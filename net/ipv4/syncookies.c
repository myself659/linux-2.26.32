/*
 *  Syncookies implementation for the Linux kernel
 *
 *  Copyright (C) 1997 Andi Kleen
 *  Based on ideas by D.J.Bernstein and Eric Schenk.
 *
 *	This program is free software; you can redistribute it and/or
 *      modify it under the terms of the GNU General Public License
 *      as published by the Free Software Foundation; either version
 *      2 of the License, or (at your option) any later version.
 */

#include <linux/tcp.h>
#include <linux/slab.h>
#include <linux/random.h>
#include <linux/cryptohash.h>
#include <linux/kernel.h>
#include <net/tcp.h>
#include <net/route.h>

/* Timestamps: lowest 9 bits store TCP options */
#define TSBITS 9
#define TSMASK (((__u32)1 << TSBITS) - 1)

extern int sysctl_tcp_syncookies;

__u32 syncookie_secret[2][16-4+SHA_DIGEST_WORDS];
EXPORT_SYMBOL(syncookie_secret);

static __init int init_syncookies(void)
{
	get_random_bytes(syncookie_secret, sizeof(syncookie_secret));
	return 0;
}
__initcall(init_syncookies);

#define COOKIEBITS 24	/* Upper bits store count */
#define COOKIEMASK (((__u32)1 << COOKIEBITS) - 1)

static DEFINE_PER_CPU(__u32 [16 + 5 + SHA_WORKSPACE_WORDS],
		      ipv4_cookie_scratch);

static u32 cookie_hash(__be32 saddr, __be32 daddr, __be16 sport, __be16 dport,
		       u32 count, int c)
{
	__u32 *tmp = __get_cpu_var(ipv4_cookie_scratch);

	memcpy(tmp + 4, syncookie_secret[c], sizeof(syncookie_secret[c]));
	tmp[0] = (__force u32)saddr;
	tmp[1] = (__force u32)daddr;
	tmp[2] = ((__force u32)sport << 16) + (__force u32)dport;
	tmp[3] = count;
	sha_transform(tmp + 16, (__u8 *)tmp, tmp + 16 + 5);

	return tmp[17];
}


/*
 * when syncookies are in effect and tcp timestamps are enabled we encode
 * tcp options in the lowest 9 bits of the timestamp value that will be
 * sent in the syn-ack.
 * Since subsequent timestamps use the normal tcp_time_stamp value, we
 * must make sure that the resulting initial timestamp is <= tcp_time_stamp.
 */
__u32 cookie_init_timestamp(struct request_sock *req)
{
	struct inet_request_sock *ireq;
	u32 ts, ts_now = tcp_time_stamp;
	u32 options = 0;

	ireq = inet_rsk(req);
	if (ireq->wscale_ok) {
		options = ireq->snd_wscale;
		options |= ireq->rcv_wscale << 4;
	}
	options |= ireq->sack_ok << 8;

	ts = ts_now & ~TSMASK;
	ts |= options;
	if (ts > ts_now) {
		ts >>= TSBITS;
		ts--;
		ts <<= TSBITS;
		ts |= options;
	}
	return ts;
}


static __u32 secure_tcp_syn_cookie(__be32 saddr, __be32 daddr, __be16 sport,
				   __be16 dport, __u32 sseq, __u32 count,
				   __u32 data)
{
	/*
	 * Compute the secure sequence number.
	 * The output should be:
	 *   HASH(sec1,saddr,sport,daddr,dport,sec1) + sseq + (count * 2^24)
	 *      + (HASH(sec2,saddr,sport,daddr,dport,count,sec2) % 2^24).
	 * Where sseq is their sequence number and count increases every
	 * minute by 1.
	 * As an extra hack, we add a small "data" value that encodes the
	 * MSS into the second hash value.
	 */

	return (cookie_hash(saddr, daddr, sport, dport, 0, 0) +
		sseq + (count << COOKIEBITS) +
		((cookie_hash(saddr, daddr, sport, dport, count, 1) + data)
		 & COOKIEMASK));
}

/*
 * This retrieves the small "data" value from the syncookie.
 * If the syncookie is bad, the data returned will be out of
 * range.  This must be checked by the caller.
 *
 * The count value used to generate the cookie must be within
 * "maxdiff" if the current (passed-in) "count".  The return value
 * is (__u32)-1 if this test fails.
 */
static __u32 check_tcp_syn_cookie(__u32 cookie, __be32 saddr, __be32 daddr,
				  __be16 sport, __be16 dport, __u32 sseq,
				  __u32 count, __u32 maxdiff)
{
	__u32 diff;

	/* Strip away the layers from the cookie */
	cookie -= cookie_hash(saddr, daddr, sport, dport, 0, 0) + sseq;

	/* Cookie is now reduced to (count * 2^24) ^ (hash % 2^24) */
	diff = (count - (cookie >> COOKIEBITS)) & ((__u32) - 1 >> COOKIEBITS);
	if (diff >= maxdiff)
		return (__u32)-1;

	return (cookie -
		cookie_hash(saddr, daddr, sport, dport, count - diff, 1))
		& COOKIEMASK;	/* Leaving the data behind */
}

/*
 * This table has to be sorted and terminated with (__u16)-1.
 * XXX generate a better table.
 * Unresolved Issues: HIPPI with a 64k MSS is not well supported.
 */
static __u16 const msstab[] = {
	64 - 1,
	256 - 1,
	512 - 1,
	536 - 1,
	1024 - 1,
	1440 - 1,
	1460 - 1,
	4312 - 1,
	(__u16)-1
};
/* The number doesn't include the -1 terminator */
#define NUM_MSS (ARRAY_SIZE(msstab) - 1)

/*
 * Generate a syncookie.  mssp points to the mss, which is returned
 * rounded down to the value encoded in the cookie.
 */
__u32 cookie_v4_init_sequence(struct sock *sk, struct sk_buff *skb, __u16 *mssp)
{
	const struct iphdr *iph = ip_hdr(skb);
	const struct tcphdr *th = tcp_hdr(skb);
	int mssind;
	const __u16 mss = *mssp;

	tcp_synq_overflow(sk);  /* 记录半连接队列溢出的最近时间 */ 

	/* XXX sort msstab[] by probability?  Binary search? */
	for (mssind = 0; mss > msstab[mssind + 1]; mssind++)
		;
	*mssp = msstab[mssind] + 1;

	NET_INC_STATS_BH(sock_net(sk), LINUX_MIB_SYNCOOKIESSENT);

	return secure_tcp_syn_cookie(iph->saddr, iph->daddr,
				     th->source, th->dest, ntohl(th->seq),
				     jiffies / (HZ * 60), mssind);  /* 计算SYN Cookie的具体值 */   
}

/*
 * This (misnamed) value is the age of syncookie which is permitted.
 * Its ideal value should be dependent on TCP_TIMEOUT_INIT and
 * sysctl_tcp_retries1. It's a rather complicated formula (exponential
 * backoff) to compute at runtime so it's currently hardcoded here.
 */
#define COUNTER_TRIES 4
/*
 * Check if a ack sequence number is a valid syncookie.
 * Return the decoded mss if it is, or 0 if not.
 */
 
 /*
cookie检查
 */
static inline int cookie_check(struct sk_buff *skb, __u32 cookie)
{
	const struct iphdr *iph = ip_hdr(skb);
	const struct tcphdr *th = tcp_hdr(skb);
	__u32 seq = ntohl(th->seq) - 1;  /* SYN的序号 */ 
	__u32 mssind = check_tcp_syn_cookie(cookie, iph->saddr, iph->daddr,
					    th->source, th->dest, seq,
					    jiffies / (HZ * 60),
					    COUNTER_TRIES);

	return mssind < NUM_MSS ? msstab[mssind] + 1 : 0;
}

static inline struct sock *get_cookie_sock(struct sock *sk, struct sk_buff *skb,
					   struct request_sock *req,
					   struct dst_entry *dst)
{
	struct inet_connection_sock *icsk = inet_csk(sk);
	struct sock *child;

	child = icsk->icsk_af_ops->syn_recv_sock(sk, skb, req, dst);
	if (child)
		inet_csk_reqsk_queue_add(sk, req, child);
	else
		reqsk_free(req);

	return child;
}


/*
 * when syncookies are in effect and tcp timestamps are enabled we stored
 * additional tcp options in the timestamp.
 * This extracts these options from the timestamp echo.
 *
 * The lowest 4 bits are for snd_wscale
 * The next 4 lsb are for rcv_wscale
 * The next lsb is for sack_ok
 */
void cookie_check_timestamp(struct tcp_options_received *tcp_opt)
{
	/* echoed timestamp, 9 lowest bits contain options */
	u32 options = tcp_opt->rcv_tsecr & TSMASK;

	tcp_opt->snd_wscale = options & 0xf;
	options >>= 4;
	tcp_opt->rcv_wscale = options & 0xf;

	tcp_opt->sack_ok = (options >> 4) & 0x1;

	if (tcp_opt->sack_ok)
		tcp_sack_reset(tcp_opt);

	if (tcp_opt->snd_wscale || tcp_opt->rcv_wscale)
		tcp_opt->wscale_ok = 1;
}
EXPORT_SYMBOL(cookie_check_timestamp);

struct sock *cookie_v4_check(struct sock *sk, struct sk_buff *skb,
			     struct ip_options *opt)
{
	struct inet_request_sock *ireq;
	struct tcp_request_sock *treq;
	struct tcp_sock *tp = tcp_sk(sk);
	const struct tcphdr *th = tcp_hdr(skb);
	__u32 cookie = ntohl(th->ack_seq) - 1;
	struct sock *ret = sk;
	struct request_sock *req;
	int mss;
	struct rtable *rt;
	__u8 rcv_wscale;
	struct tcp_options_received tcp_opt;

	if (!sysctl_tcp_syncookies || !th->ack)
		goto out;

	/* 验证cookie的合法性，必须同时符合： 
		 * 1. 最近3s内有发生半连接队列溢出。 
		 * 2. 通过cookie反算的t1和mssind是合法的。 
		 */  

	if (tcp_synq_no_recent_overflow(sk) ||
	    (mss = cookie_check(skb, cookie)) == 0) {
		NET_INC_STATS_BH(sock_net(sk), LINUX_MIB_SYNCOOKIESFAILED);
		goto out;
	}

	NET_INC_STATS_BH(sock_net(sk), LINUX_MIB_SYNCOOKIESRECV);

	/* check for timestamp cookie support */
	memset(&tcp_opt, 0, sizeof(tcp_opt));
	tcp_parse_options(skb, &tcp_opt, 0);
	
	/* 如果有使用时间戳选项，则从ACK的tsecr中提取选项信息 */  
	if (tcp_opt.saw_tstamp)
		cookie_check_timestamp(&tcp_opt);

	ret = NULL;
	/* 从缓存块中分配一个request_sock实例，指定此实例的操作函数集为tcp_request_sock_ops */ 
	req = inet_reqsk_alloc(&tcp_request_sock_ops); /* for safety */
	if (!req)
		goto out;

	ireq = inet_rsk(req);
	treq = tcp_rsk(req);
	treq->rcv_isn		= ntohl(th->seq) - 1; /* 客户端的初始序列号 */  
	treq->snt_isn		= cookie; /* 本端的初始序列号 */  
	req->mss		= mss; /* 客户端通告的MSS，通过解析cookie获得 */ 
	ireq->loc_port		= th->dest; /* 本端端口 */  
	ireq->rmt_port		= th->source; /* 客户端端口 */ 
	ireq->loc_addr		= ip_hdr(skb)->daddr; /* 本端IP */ 
	ireq->rmt_addr		= ip_hdr(skb)->saddr; /* 客户端IP */ 
	ireq->ecn_ok		= 0;   /* ECN选项，通过TS编码获得 */ 
	ireq->snd_wscale	= tcp_opt.snd_wscale; /* 客户端窗口扩大因子，通过TS编码获得 */   
	ireq->rcv_wscale	= tcp_opt.rcv_wscale;  
	ireq->sack_ok		= tcp_opt.sack_ok; /* SACK允许选项，通过TS编码获得 */ 
	ireq->wscale_ok		= tcp_opt.wscale_ok; /* 窗口扩大选项，通过TS编码获得 */  
	ireq->tstamp_ok		= tcp_opt.saw_tstamp;/* 时间戳选项，通过观察ACK段有无携带时间戳 */ 
	req->ts_recent		= tcp_opt.saw_tstamp ? tcp_opt.rcv_tsval : 0; /* 本端下个发送段的时间戳回显值 */ 

	/* We throwed the options of the initial SYN away, so we hope
	 * the ACK carries the same options again (see RFC1122 4.2.3.8)
	 * 通过ACK段，获取IP选项。 
	 */
	if (opt && opt->optlen) {
		int opt_size = sizeof(struct ip_options_rcu) + opt->optlen;

		ireq->opt = kmalloc(opt_size, GFP_ATOMIC);
		if (ireq->opt != NULL && ip_options_echo(&ireq->opt->opt, skb)) {
			kfree(ireq->opt);
			ireq->opt = NULL;
		}
	}
	   /* SELinux相关 */ 
	if (security_inet_conn_request(sk, skb, req)) {
		reqsk_free(req);
		goto out;
	}

	req->expires	= 0UL; /* SYNACK的超时时间 */  
	req->retrans	= 0; /* SYNACK的重传次数 */  

	/*
	 * We need to lookup the route here to get at the correct
	 * window size. We should better make sure that the window size
	 * hasn't changed since we received the original syn, but I see
	 * no easy way to do this.
	  * 查找路由缓存。 
	 */
	{
		struct flowi fl = { .nl_u = { .ip4_u =
					      { .daddr = ((opt && opt->srr) ?
							  opt->faddr :
							  ireq->rmt_addr),
						.saddr = ireq->loc_addr,
						.tos = RT_CONN_FLAGS(sk) } },
				    .proto = IPPROTO_TCP,
				    .flags = inet_sk_flowi_flags(sk),
				    .uli_u = { .ports =
					       { .sport = th->dest,
						 .dport = th->source } } };
		security_req_classify_flow(req, &fl);
		if (ip_route_output_key(&init_net, &rt, &fl)) {
			reqsk_free(req);
			goto out;
		}
	}

	/* Try to redo what tcp_v4_send_synack did. */
	req->window_clamp = tp->window_clamp ? :dst_metric(&rt->u.dst, RTAX_WINDOW);
	/* 获取接收窗口的初始值，窗口扩大因子和接收窗口的上限 */  
	tcp_select_initial_window(tcp_full_space(sk), req->mss,
				  &req->rcv_wnd, &req->window_clamp,
				  ireq->wscale_ok, &rcv_wscale);

	ireq->rcv_wscale  = rcv_wscale;
	
    /* 到了这里，三次握手基本完成。 
     * 接下来为新的连接创建和初始化一个传输控制块，并把它和连接请求块关联起来。 
     * 最后把该连接请求块移入全连接队列中，等待accept()。 
     */  
	ret = get_cookie_sock(sk, skb, req, &rt->u.dst);
out:	return ret;
}
