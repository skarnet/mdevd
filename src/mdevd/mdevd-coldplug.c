/* ISC license. */

#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>
#include <limits.h>
#include <unistd.h>
#include <errno.h>
#include <skalibs/allreadwrite.h>
#include <skalibs/buffer.h>
#include <skalibs/sgetopt.h>
#include <skalibs/strerr2.h>
#include <skalibs/direntry.h>
#include "mdevd.h"

#define USAGE "mdevd-coldplug [ -s slashsys ]"
#define dieusage() strerr_dieusage(100, USAGE)
#define die1() strerr_diefu1sys(111, "write to stdout")

static inline void create_event (int fddir, char const *sysdev, char const *sub, char const *name)
{
  if (faccessat(fddir, "dev", R_OK, AT_EACCESS) < 0)
  {
    if (errno == ENOENT) return ;
    strerr_diefu6sys(111, "access dev in ", sysdev, "/", sub, "/", name) ;
  }
  if (buffer_put(buffer_1, "add@/", 5) < 0
   || buffer_puts(buffer_1, sub) < 0
   || buffer_put(buffer_1, "/", 1) < 0
   || buffer_puts(buffer_1, name) < 0
   || buffer_put(buffer_1, "\0ACTION=add\0DEVPATH=/dev/", sizeof("\0ACTION=add\0DEVPATH=/dev/") - 1) < 0
   || buffer_puts(buffer_1, sub) < 0
   || buffer_put(buffer_1, "/", 1) < 0
   || buffer_puts(buffer_1, name) < 0
   || buffer_put(buffer_1, "\0SUBSYSTEM=", sizeof("\0SUBSYSTEM=") - 1) < 0)
    die1() ;

  {
    char *p ;
    ssize_t r ;
    char buf[PATH_MAX] ;
    r = readlinkat(fddir, "subsystem", buf, PATH_MAX - 1) ;
    if (r < 0) strerr_diefu6sys(111, "readlink subsystem in ", sysdev, "/", sub, "/", name) ;
    buf[r] = 0 ;
    p = strrchr(buf, '/') ;
    if (p && buffer_put(buffer_1, p+1, strlen(p)) < 0) die1() ;
  }

  {
    size_t len ;
    size_t i = 0 ;
    char buf[UEVENT_MAX_SIZE] ;
    int fd = openat(fddir, "uevent", O_RDONLY) ;
    if (fd < 0)
      strerr_diefu6sys(111, "open uevent in ", sysdev, "/", sub, "/", name) ;
    len = allread(fd, buf, UEVENT_MAX_SIZE) ;
    if (!len) strerr_diefu6sys(111, "read uevent in ", sysdev, "/", sub, "/", name) ;
    close(fd) ;
    for (; i < len ; i++) if (buf[i] == '\n') buf[i] = 0 ;
    if (buffer_put(buffer_1, buf, len) < 0) die1() ;
  }

  if (buffer_put(buffer_1, "", 1) < 1) die1() ;
}

int main (int argc, char const *const *argv, char const *const *envp)
{
  char const *slashsys = "/sys" ;
  size_t slashsyslen ;
  PROG = "mdevd-coldplug" ;
  {
    subgetopt_t l = SUBGETOPT_ZERO ;
    for (;;)
    {
      int opt = subgetopt_r(argc, argv, "s:", &l) ;
      if (opt == -1) break ;
      switch (opt)
      {
        case 's' : slashsys = l.arg ; break ;
        default : dieusage() ;
      }
    }
    argc -= l.ind ; argv += l.ind ;
  }

  slashsyslen = strlen(slashsys) ;
  {
    int fdsysdev ;
    DIR *dirsysdev ;
    char sysdev[slashsyslen + 5] ;
    memcpy(sysdev, slashsys, slashsyslen) ;
    memcpy(sysdev + slashsyslen, "/dev", 5) ;
    fdsysdev = open(sysdev, O_RDONLY | O_DIRECTORY) ;
    if (fdsysdev < 0) strerr_diefu2sys(111, "open ", sysdev) ;
    dirsysdev = fdopendir(fdsysdev) ;
    if (!dirsysdev) strerr_diefu2sys(111, "fdopendir ", sysdev) ;
    for (;;)
    {
      direntry *d ;
      int fdsub ;
      DIR *dirsub ;
      errno = 0 ;
      d = readdir(dirsysdev) ;
      if (!d) break ;
      if (d->d_name[0] == '.') continue ;
      fdsub = openat(fdsysdev, d->d_name, O_RDONLY | O_DIRECTORY) ;
      if (fdsub < 0) strerr_diefu4sys(111, "open ", sysdev, "/", d->d_name) ;
      dirsub = fdopendir(fdsub) ;
      if (!dirsub) strerr_diefu4sys(111, "fdopendir ", sysdev, "/", d->d_name) ;
      for (;;)
      {
        direntry *dd ;
        int fddevice ;
        errno = 0 ;
        dd = readdir(dirsub) ;
        if (!dd) break ;
        if (dd->d_name[0] == '.') continue ;
        fddevice = openat(fdsub, dd->d_name, O_RDONLY | O_DIRECTORY) ;
        if (fddevice < 0) strerr_diefu6sys(111, "open ", sysdev, "/", d->d_name, "/", dd->d_name) ;
        create_event(fddevice, sysdev, d->d_name, dd->d_name) ;
        close(fddevice) ;
      }
      if (errno) strerr_diefu4sys(111, "readdir ", sysdev, "/", d->d_name) ;
      dir_close(dirsub) ;
      close(fdsub) ;
    }
    if (errno) strerr_diefu2sys(111, "readdir ", sysdev) ;
    dir_close(dirsysdev) ;
    close(fdsysdev) ;
  }
  if (!buffer_flush(buffer_1)) die1() ;
  return 0 ;
}
