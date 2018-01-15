/* ISC license. */

#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <skalibs/sgetopt.h>
#include <skalibs/strerr2.h>
#include <skalibs/direntry.h>

#define USAGE "mdevd-coldplug [ -s slashsys ]"
#define dieusage() strerr_dieusage(100, USAGE)

static void scan_subdir (int fdat, char const *pathat, char const *list)
{
  DIR *dir ;
  int fdlist = openat(fdat, list, O_RDONLY | O_DIRECTORY) ;
  if (fdlist < 0) strerr_diefu4sys(111, "open ", pathat, "/", list) ;
  dir = fdopendir(fdlist) ;
  if (!dir) strerr_diefu4sys(111, "fdopendir ", pathat, "/", list) ;
  for (;;)
  {
    direntry *d ;
    errno = 0 ;
    d = readdir(dir) ;
    if (!d) break ;
    if (d->d_name[0] == '.') continue ;
    {
      int fd ;
      size_t dlen = strlen(d->d_name) ;
      char fn[dlen + 8] ;
      memcpy(fn, d->d_name, dlen) ;
      memcpy(fn + dlen, "/uevent", 8) ;
      fd = openat(fdlist, fn, O_WRONLY) ;
      if (fd < 0) continue ;
      if (write(fd, "add\n", 4) < 4)
        strerr_warnwu6sys("write to ", pathat, "/", list, "/", fn) ;
      close(fd) ;
    }
  }
  if (errno) strerr_diefu4sys(111, "readdir ", pathat, "/", list) ;
  dir_close(dir) ;
}

static int scan_dir (char const *path, int add_devices)
{
  DIR *dir ;
  int fdpath = open(path, O_RDONLY | O_DIRECTORY) ;
  if (fdpath < 0) return 0 ;
  dir = fdopendir(fdpath) ;
  if (!dir) strerr_diefu2sys(111, "fdopendir ", path) ;
  for (;;)
  {
    direntry *d ;
    errno = 0 ;
    d = readdir(dir) ;
    if (!d) break ;
    if (d->d_name[0] == '.') continue ;
    if (add_devices)
    {
      size_t dlen = strlen(d->d_name) ;
      char fn[dlen + 9] ;
      memcpy(fn, d->d_name, dlen) ;
      memcpy(fn + dlen, "/devices", 9) ;
      scan_subdir(fdpath, path, fn) ;
    }
    else scan_subdir(fdpath, path, d->d_name) ;
  }
  if (errno) strerr_diefu2sys(111, "readdir ", path) ;
  dir_close(dir) ;
  return 1 ;
}


int main (int argc, char const *const *argv, char const *const *envp)
{
  char const *slashsys = "/sys" ;
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

  {
    size_t slashsyslen = strlen(slashsys) ;
    char fn[slashsyslen + 11] ;
    memcpy(fn, slashsys, slashsyslen) ;
    memcpy(fn + slashsyslen, "/subsystem", 11) ;
    if (!scan_dir(fn, 1))
    {
      memcpy(fn + slashsyslen + 1, "class", 6) ;
      if (!scan_dir(fn, 0)) strerr_diefu2sys(111, "open ", fn) ;
      memcpy(fn + slashsyslen + 1, "bus", 4) ;
      if (!scan_dir(fn, 1)) strerr_diefu2sys(111, "open ", fn) ;
    }
  }
  return 0 ;
}
