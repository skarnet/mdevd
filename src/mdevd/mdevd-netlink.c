/* ISC license. */

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <unistd.h>
#include <errno.h>
#include <signal.h>
#include <sys/socket.h>
#include <linux/netlink.h>
#include <skalibs/types.h>
#include <skalibs/allreadwrite.h>
#include <skalibs/siovec.h>
#include <skalibs/buffer.h>
#include <skalibs/sgetopt.h>
#include <skalibs/error.h>
#include <skalibs/strerr2.h>
#include <skalibs/iopause.h>
#include <skalibs/djbunix.h>
#include <skalibs/sig.h>
#include <skalibs/selfpipe.h>
#include "mdevd.h"

#define USAGE "mdevd-netlink [ -d notification-fd ] [ -v verbosity ] [ -b kbufsz ]"
#define dieusage() strerr_dieusage(100, USAGE)
#define dienomem() strerr_diefu1sys(111, "build string") ;

static unsigned int cont = 1, verbosity = 1 ;

static inline ssize_t fd_recvmsg (int fd, struct msghdr *hdr)
{
  ssize_t r ;
  do r = recvmsg(fd, hdr, MSG_DONTWAIT) ;
  while ((r == -1) && (errno == EINTR)) ;
  return r ;
}

static inline int netlink_init_stdin (unsigned int kbufsz)
{
  struct sockaddr_nl nl = { .nl_family = AF_NETLINK, .nl_pad = 0, .nl_groups = 1, .nl_pid = 0 } ;
  close(0) ;
  if (socket_internal(AF_NETLINK, SOCK_DGRAM, NETLINK_KOBJECT_UEVENT, DJBUNIX_FLAG_NB|DJBUNIX_FLAG_COE) < 0
   || bind(0, (struct sockaddr *)&nl, sizeof(struct sockaddr_nl)) < 0)
    return 0 ;

  if (setsockopt(0, SOL_SOCKET, SO_RCVBUFFORCE, &kbufsz, sizeof(unsigned int)) < 0
   && errno == EPERM
   && setsockopt(0, SOL_SOCKET, SO_RCVBUF, &kbufsz, sizeof(unsigned int)) < 0)
    return 0 ;
  return 1 ;
}

static inline void handle_signals (void)
{
  for (;;)
  {
    int c = selfpipe_read() ;
    switch (c)
    {
      case -1 : strerr_diefu1sys(111, "selfpipe_read") ;
      case 0 : return ;
      case SIGTERM :
        cont = 0 ;
        fd_close(0) ;
        break ;
      default :
        strerr_dief1x(101, "internal error: inconsistent signal state. Please submit a bug-report.") ;
    }
  }
}

static inline void handle_stdout (void)
{
  if (!buffer_flush(buffer_1) && !error_isagain(errno))
    strerr_diefu1sys(111, "flush stdout") ;
}

static inline void handle_netlink (void)
{
  struct sockaddr_nl nl;
  struct iovec v[2] ;
  struct msghdr msg =
  {
    .msg_name = &nl,
    .msg_namelen = sizeof(struct sockaddr_nl),
    .msg_iov = v,
    .msg_iovlen = 2,
    .msg_control = 0,
    .msg_controllen = 0,
    .msg_flags = 0
  } ;
  ssize_t r ;
  buffer_wpeek(buffer_1, v) ;
  siovec_trunc(v, 2, siovec_len(v, 2) - 1) ;
  r = sanitize_read(fd_recvmsg(0, &msg)) ;
  if (r < 0)
  {
    if (errno == EPIPE)
    {
      if (verbosity >= 2) strerr_warnw1x("received EOF on netlink") ;
      cont = 0 ;
      fd_close(0) ;
      return ;
    }
    else strerr_diefu1sys(111, "receive netlink message") ;
  }
  if (!r) return ;
  if (msg.msg_flags & MSG_TRUNC)
    strerr_diefu2x(111, "buffer too small for ", "netlink message") ;
  if (nl.nl_pid)
  {
    if (verbosity >= 3)
    {
      char fmt[PID_FMT] ;
      fmt[pid_fmt(fmt, nl.nl_pid)] = 0 ;
      strerr_warnw3x("netlink message", " from userspace process ", fmt) ;
    }
    return ;
  }
  buffer_wseek(buffer_1, r) ;
  buffer_putnoflush(buffer_1, "", 1) ;
}


int main (int argc, char const *const *argv, char const *const *envp)
{
  iopause_fd x[3] = { { .events = IOPAUSE_READ }, { .fd = 1 }, { .fd = 0 } } ;
  unsigned int notif = 0 ;
  PROG = "mdevd-netlink" ;
  {
    unsigned int kbufsz = 65536 ;
    subgetopt_t l = SUBGETOPT_ZERO ;
    for (;;)
    {
      int opt = subgetopt_r(argc, argv, "d:v:b:", &l) ;
      if (opt == -1) break ;
      switch (opt)
      {
        case 'd' : if (!uint0_scan(l.arg, &notif) || notif < 3) dieusage() ; break ;
        case 'v' : if (!uint0_scan(l.arg, &verbosity)) dieusage() ; break ;
        case 'b' : if (!uint0_scan(l.arg, &kbufsz)) dieusage() ; break ;
        default : dieusage() ;
      }
    }
    argc -= l.ind ; argv += l.ind ;
    if (!netlink_init_stdin(kbufsz)) strerr_diefu1sys(111, "init netlink") ;
  }

  x[0].fd = selfpipe_init() ;
  if (x[0].fd < 0) strerr_diefu1sys(111, "init selfpipe") ;
  if (selfpipe_trap(SIGTERM) < 0) strerr_diefu1sys(111, "trap SIGTERM") ;

  if (verbosity >= 2) strerr_warni1x("starting") ;
  if (notif)
  {
    fd_write(notif, "\n", 1) ;
    fd_close(notif) ;
  }

  while (cont || buffer_len(buffer_1))
  {
    int r ;
    x[1].events = buffer_len(buffer_1) ? IOPAUSE_WRITE : 0 ;
    x[2].events = buffer_available(buffer_1) >= UEVENT_MAX_SIZE + 1 ? IOPAUSE_READ : 0 ;
    r = iopause(x, 2 + cont, 0, 0) ;
    if (r < 0) strerr_diefu1sys(111, "iopause") ;
    if (!r) continue ;
    if (x[1].revents & IOPAUSE_EXCEPT) break ;
    if (x[1].revents & IOPAUSE_WRITE) handle_stdout() ;
    if (x[0].revents & (IOPAUSE_READ | IOPAUSE_EXCEPT)) handle_signals() ;
    if (cont && x[2].events & IOPAUSE_READ && x[2].revents & (IOPAUSE_READ | IOPAUSE_EXCEPT))
      handle_netlink() ;
  }
  if (verbosity >= 2) strerr_warni1x("exiting") ;
  return 0 ;
}
