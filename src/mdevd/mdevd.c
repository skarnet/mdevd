/* ISC license. */

#include <sys/sysmacros.h>  /* makedev, major, minor */
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdint.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <limits.h>
#include <signal.h>
#include <pwd.h>
#include <grp.h>
#include <regex.h>
#include <libgen.h>  /* basename */
#include <stdio.h>  /* rename */
#include <skalibs/types.h>
#include <skalibs/allreadwrite.h>
#include <skalibs/bytestr.h>
#include <skalibs/buffer.h>
#include <skalibs/strerr2.h>
#include <skalibs/sgetopt.h>
#include <skalibs/sig.h>
#include <skalibs/selfpipe.h>
#include <skalibs/tai.h>
#include <skalibs/environ.h>
#include <skalibs/env.h>
#include <skalibs/djbunix.h>
#include <skalibs/iopause.h>
#include <skalibs/skamisc.h>
#include <skalibs/surf.h>
#include <skalibs/random.h>
#include "mdevd.h"

#define USAGE "mdevd [ -v verbosity ] [ -f conffile ] [ -n ] [ -s slashsys ] [ -d slashdev ]"
#define dieusage() strerr_dieusage(100, USAGE)

#define BUFSIZE 8192
#define UEVENT_MAX_VARS 63

#define ACTION_NONE 0x0
#define ACTION_ADD 0x1
#define ACTION_REMOVE 0x2

static int dryrun = 0 ;
static int cont = 1 ;
static pid_t pid = 0 ;
static unsigned int verbosity = 1 ;
static char const *slashsys = "/sys" ;
static char const *fwbase = "/lib/firmware" ;
static SURFSchedule surf_ctx = SURFSCHEDULE_ZERO ;
static unsigned int root_maj, root_min ;

struct envmatch_s
{
  size_t var ;
  regex_t re ;
} ;

struct majmin_s
{
  unsigned int maj ;
  unsigned int minlo ;
  unsigned int minhi ;
} ;

union devmatch_u
{
  regex_t devre ;
  struct majmin_s majmin ;
} ;

#define DEVMATCH_NOTHING 0
#define DEVMATCH_CATCHALL 1
#define DEVMATCH_DEVRE 2
#define DEVMATCH_MAJMIN 3

#define MOVEINFO_NOTHING 0
#define MOVEINFO_NOCREATE 1
#define MOVEINFO_MOVE 2
#define MOVEINFO_MOVEANDLINK 3

typedef struct scriptelem_s scriptelem, *scriptelem_ref ;
struct scriptelem_s
{
  uid_t uid ;
  gid_t gid ;
  mode_t mode ;
  size_t movepath ;
  size_t command ;
  union devmatch_u devmatch ;
  unsigned int envmatchlen : 11 ;
  unsigned int devmatchtype : 2 ;
  unsigned int movetype : 2 ;
  unsigned int cmdtype : 2 ;
  unsigned int flagcont : 1 ;
  unsigned short envmatchs ;
} ;

static scriptelem const scriptelem_catchall =
{
  .uid = 0,
  .gid = 0,
  .mode = 0660,
  .movepath = 0,
  .command = 0,
  .envmatchlen = 0,
  .devmatchtype = DEVMATCH_CATCHALL,
  .movetype = MOVEINFO_NOTHING,
  .cmdtype = ACTION_NONE,
  .flagcont = 0
} ;

struct uevent_s
{
  unsigned short len ;
  unsigned short varn ;
  unsigned short vars[UEVENT_MAX_VARS + 1] ;
  char buf[UEVENT_MAX_SIZE + PATH_MAX + 5] ;
} ;
#define UEVENT_ZERO { .len = 0, .varn = 0 }


 /* Utility functions */

static inline void script_free (scriptelem *script, unsigned short scriptlen, struct envmatch_s *envmatch, unsigned short envmatchlen)
{
  unsigned short i = 0 ;
  for (; i < scriptlen ; i++)
    if (script[i].devmatchtype == DEVMATCH_DEVRE)
      regfree(&script[i].devmatch.devre) ;
  for (i = 0 ; i < envmatchlen ; i++) regfree(&envmatch[i].re) ;
}

static void mdevd_random_init (void)
{
  char seed[160] ;
  random_makeseed(seed) ;
  surf_init(&surf_ctx, seed) ;
}

static inline void surfname (char *s, size_t n)
{
  static char const oklist[64] = "ABCDEFGHIJKLMNOPQRSTUVWXYZghijklmnopqrstuvwxyz-_0123456789abcdef" ;
  surf(&surf_ctx, s, n) ;
  while (n--) s[n] = oklist[s[n] & 63] ;
}

static inline int mkdirp (char *s)
{
  size_t n = strlen(s) ;
  size_t i = 0 ;
  for (; i < n ; i++)
  {
    if (s[i] == '/')
    {
      int r = 0 ;
      s[i] = 0 ;
      if (dryrun) strerr_warni2x("dry run: mkdir ", s) ;
      else r = mkdir(s, 0755) ;
      s[i] = '/' ;
      if (r < 0) break ;
    }
  }
  return i >= n ;
}

static int makesubdirs (char *path)
{
  if (strrchr(path, '/') && !mkdirp(path))
  {
    if (verbosity) strerr_warnwu2sys("create subdirectories for ", path) ;
    return 0 ;
  }
  return 1 ;
}


 /* mdev.conf parsing. See PARSING.txt for details. */

 /* The first pass is simple. The goal is just to compute scriptlen and envmatchlen. */

static inline unsigned char firstpass_cclass (char c)
{
  static unsigned char const classtable[65] = "08888888817881888888888888888888188438888888858888888888888288886" ;
  return (unsigned char)c < 65 ? classtable[(unsigned char)c] - '0' : 8 ;
}

static inline void script_firstpass (char *s, unsigned short *scriptlen, unsigned short *envmatchlen)
{
  static unsigned char const table[5][9] =
  {
    { 0x05, 0x00, 0x06, 0x34, 0x04, 0x01, 0x24, 0x00, 0x22 },
    { 0x06, 0x06, 0x06, 0x34, 0x06, 0x06, 0x24, 0x06, 0x22 },
    { 0x06, 0x04, 0x13, 0x02, 0x06, 0x02, 0x02, 0x06, 0x02 },
    { 0x06, 0x06, 0x06, 0x02, 0x06, 0x02, 0x02, 0x06, 0x02 },
    { 0x05, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x00, 0x04 }
  } ;
  size_t i = 0 ;
  unsigned short n = 0, m = 0 ;
  unsigned int state = 0 ;
  while (state < 5)
  {
    unsigned char what = table[state][firstpass_cclass(s[i++])] ;
    state = what & 0x07 ;
    if (what & 0x10) m++ ;
    if (what & 0x20) n++ ;
  }
  if (state == 6)
  {
    s[--i] = 0 ;
    while (i && !strchr(" \n\r\t", s[i])) i-- ;
    strerr_dief2x(2, "syntax error during first pass, after string: ", (char *)s + i) ;
  }

  *scriptlen = n ;
  *envmatchlen = m ;
}

 /* The second pass is the real, complete mdev.conf parsing. */

static inline unsigned char secondpass_cclass (char c)
{
  static unsigned char const classtable[65] = "`ppppppppagppappppppppppppppppppampdcppppplpheppnnnnnnnnookbpijpf" ;
  return (unsigned char)c < 65 ? classtable[(unsigned char)c] - '`' : 16 ;
}

static inline void script_secondpass (char *s, scriptelem *script, struct envmatch_s *envmatch)
{
  static uint32_t const table[30][17] =
  {
    { 0x0000001e, 0x00000000, 0x0000001f, 0x40000003, 0x00000001, 0x08000002, 0x20000007, 0x00000040, 0x1400000d, 0x0000001f, 0x0000001f, 0x1400000d, 0x1400000d, 0x1400000d, 0x1400000d, 0x1400000d, 0x1400000d },
    { 0x0000001e, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000040, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001 },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x40000003, 0x0000001f, 0x0000001f, 0x20000007, 0x0000001f, 0x1400000d, 0x0000001f, 0x0000001f, 0x1400000d, 0x1400000d, 0x1400000d, 0x1400000d, 0x1400000d, 0x1400000d },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x04040004, 0x0000001f, 0x04040004, 0x04040004, 0x0000001f, 0x04040004, 0x0000001f, 0x04040004, 0x04040004, 0x04040004, 0x04040004, 0x04040004, 0x04040004, 0x04040004 },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x00000004, 0x0000001f, 0x00000004, 0x00000004, 0x0000001f, 0x00000004, 0x02000005, 0x00000004, 0x00000004, 0x00000004, 0x00000004, 0x00000004, 0x00000004, 0x00000004 },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x04000006, 0x04000006, 0x0000001f, 0x04000006, 0x0000001f, 0x04000006, 0x04000006, 0x04000006, 0x04000006, 0x04000006, 0x04000006, 0x04000006 },
    { 0x0000001f, 0x03000012, 0x0000001f, 0x00000006, 0x0000001f, 0x00000006, 0x00000006, 0x0000001f, 0x00000006, 0x00000006, 0x00000006, 0x00000006, 0x00000006, 0x00000006, 0x00000006, 0x00000006, 0x00000006 },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x04000008, 0x04000008, 0x0000001f },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x02800009, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x00000008, 0x00000008, 0x0000001f },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0400000a, 0x0400000a, 0x0000001f },
    { 0x0000001f, 0x02600012, 0x0000001f, 0x0000001f, 0x0000001f, 0x0240000b, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000000a, 0x0000000a, 0x0000001f },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0400000c, 0x0400000c, 0x0000001f },
    { 0x0000001f, 0x02100012, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000000c, 0x0000000c, 0x0000001f },
    { 0x0000001f, 0x02080012, 0x0000001f, 0x0000000d, 0x0000001f, 0x0000000d, 0x0000000d, 0x0000001f, 0x0000000d, 0x0204000e, 0x0000001f, 0x0000000d, 0x0000000d, 0x0000000d, 0x0000000d, 0x0000000d, 0x0000000d },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x0400000f, 0x0000001f, 0x0400000f, 0x0400000f, 0x0000001f, 0x0400000f, 0x0400000f, 0x0400000f, 0x0400000f, 0x0400000f, 0x0400000f, 0x0400000f, 0x0400000f, 0x0400000f },
    { 0x0000001f, 0x0000001f, 0x03000010, 0x0000000f, 0x0000001f, 0x0000000f, 0x0000000f, 0x0000001f, 0x0000000f, 0x0000000f, 0x0000000f, 0x0000000f, 0x0000000f, 0x0000000f, 0x0000000f, 0x0000000f, 0x0000000f },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x04000011, 0x0000001f, 0x0400000d, 0x0400000d, 0x0000001f, 0x0400000d, 0x0000001f, 0x0000001f, 0x0400000d, 0x0400000d, 0x0400000d, 0x0400000d, 0x0400000d, 0x0400000d },
    { 0x0000001f, 0x02080012, 0x0000001f, 0x00000011, 0x0000001f, 0x00000011, 0x00000011, 0x0000001f, 0x00000011, 0x00000011, 0x00000011, 0x00000011, 0x00000011, 0x00000011, 0x00000011, 0x00000011, 0x00000011 },
    { 0x0000001f, 0x00000012, 0x0000001f, 0x0000001f, 0x0000001f, 0x04000013, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x04000013, 0x04000013, 0x04000013 },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x00000013, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x02020014, 0x0000001f, 0x0000001f, 0x00000013, 0x00000013, 0x00000013 },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x04000015, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x04000015, 0x04000015, 0x04000015 },
    { 0x0000001f, 0x02010016, 0x0000001f, 0x0000001f, 0x0000001f, 0x00000015, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x00000015, 0x00000015, 0x00000015 },
    { 0x0000001f, 0x00000016, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x04000017, 0x0000001f, 0x0000001f },
    { 0x0000001f, 0x02008018, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0200c040, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x00000017, 0x0000001f, 0x0000001f },
    { 0x0000401e, 0x00000018, 0x0000001f, 0x0000201c, 0x00004001, 0x0000001f, 0x0000101c, 0x00004040, 0x0000001f, 0x00000819, 0x00000419, 0x0000001f, 0x0000301c, 0x0000021b, 0x0000001f, 0x0000001f, 0x0000001f },
    { 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000011a, 0x0000011a, 0x0000001f, 0x0000011a, 0x0000011a, 0x0000001f, 0x0000011a, 0x0000001f, 0x0000011a, 0x0000011a, 0x0000011a, 0x0000011a },
    { 0x0000401e, 0x0200001b, 0x0000001f, 0x0000001f, 0x02004001, 0x0000001a, 0x0000001a, 0x02004040, 0x0000001a, 0x0000001a, 0x0000001f, 0x0000001a, 0x0000001f, 0x0000001a, 0x0000001a, 0x0000001a, 0x0000001a },
    { 0x0000401e, 0x0000001b, 0x0000001f, 0x0000201c, 0x00004001, 0x0000001f, 0x0000101c, 0x00004040, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000301c, 0x0000001f, 0x0000001f, 0x0000001f, 0x0000001f },
    { 0x0000001f, 0x0000009d, 0x0000001f, 0x0000009d, 0x0000001f, 0x0000009d, 0x0000009d, 0x0000001f, 0x0000009d, 0x0000009d, 0x0000009d, 0x0000009d, 0x0000009d, 0x0000009d, 0x0000009d, 0x0000009d, 0x0000009d },
    { 0x0000401e, 0x0000001d, 0x0000001d, 0x0000001d, 0x0000001d, 0x0000001d, 0x0000001d, 0x02004040, 0x0000001d, 0x0000001d, 0x0000001d, 0x0000001d, 0x0000001d, 0x0000001d, 0x0000001d, 0x0000001d, 0x0000001d }
  } ;
  size_t mark = 0 ;
  size_t col0 = 0 ;
  size_t pos = 0 ;
  unsigned int line = 0 ;
  uint32_t state = 0 ;
  unsigned short i = 0 ; /* current scriptelem index */
  unsigned short j = 0 ; /* current envmatch index */
  while (state < 0x1e)
  {
    uint32_t what = table[state][secondpass_cclass(s[pos])] ;
    state = what & 0x1f ;
    if (what & 0x40000000)
    {
      script[i].devmatchtype = DEVMATCH_NOTHING ;
      script[i].envmatchs = j ;
    }
    if (what & 0x20000000) script[i].devmatchtype = DEVMATCH_MAJMIN ;
    if (what & 0x10000000)
    {
      script[i].devmatchtype = DEVMATCH_DEVRE ;
      script[i].envmatchs = j ;
    }
    if (what & 0x08000000) script[i].flagcont = 1 ;
    if (what & 0x04000000) mark = pos ;
    if (what & 0x02000000) s[pos] = 0 ;
    if (what & 0x01000000)
    {
      int r = regcomp(&envmatch[j].re, s + mark, REG_EXTENDED) ;
      if (r)
      {
        char errbuf[256] ;
        char fmtline[UINT_FMT] ;
        fmtline[uint_fmt(fmtline, line)] = 0 ;
        regerror(r, &envmatch[j].re, errbuf, 256) ;
        strerr_dief8x(2, "syntax error during second pass: ", "line ", fmtline, ": unable to compile regular expression ", "for envmatch: ", s + mark, ": ", errbuf) ;
      }
      j++ ;
      script[i].envmatchlen++ ;
    }
    if (what & 0x00800000)
    {
      if (!uint0_scan(s + mark, &script[i].devmatch.majmin.maj))
      {
        char fmtline[UINT_FMT] ;
        fmtline[uint_fmt(fmtline, line)] = 0 ;
        strerr_dief5x(2, "syntax error during second pass: ", "line ", fmtline, ": unable to scan major from string: ", s + mark) ;
      }
    }
    if (what & 0x00400000)
    {
      if (!uint0_scan(s + mark, &script[i].devmatch.majmin.minlo))
      {
        char fmtline[UINT_FMT] ;
        fmtline[uint_fmt(fmtline, line)] = 0 ;
        strerr_dief5x(2, "syntax error during second pass: ", "line ", fmtline, ": unable to scan minor from string: ", s + mark) ;
      }
    }
    if (what & 0x00200000) script[i].devmatch.majmin.minhi = script[i].devmatch.majmin.minlo ;
    if (what & 0x00100000)
    {
      if (!uint0_scan(s + mark, &script[i].devmatch.majmin.minhi))
      {
        char fmtline[UINT_FMT] ;
        fmtline[uint_fmt(fmtline, line)] = 0 ;
        strerr_dief5x(2, "syntax error during second pass: ", "line ", fmtline, ": unable to scan minor from string: ", s + mark) ;
      }
    }
    if (what & 0x00080000)
    {
      int r = regcomp(&script[i].devmatch.devre, s + mark, REG_EXTENDED) ;
      if (r)
      {
        char errbuf[256] ;
        char fmtline[UINT_FMT] ;
        fmtline[uint_fmt(fmtline, line)] = 0 ;
        regerror(r, &envmatch[j].re, errbuf, 256) ;
        strerr_dief8x(2, "syntax error during second pass: ", "line ", fmtline, ": unable to compile regular expression ", " for devmatch: ", s + mark, ": ", errbuf) ;
      }
    }
    if (what & 0x00040000) envmatch[j].var = mark ;
    if (what & 0x00020000)
    {
      struct passwd *pw = getpwnam(s + mark) ;
      if (pw) script[i].uid = pw->pw_uid ;
      else if (!uid0_scan(s + mark, &script[i].uid))
      {
        char fmtline[UINT_FMT] ;
        fmtline[uint_fmt(fmtline, line)] = 0 ;
        strerr_dief5x(2, "syntax error during second pass: ", "line ", fmtline, ": unable to get uid from string: ", s + mark) ;
      }
    }
    if (what & 0x00010000)
    {
      struct group *gr = getgrnam(s + mark) ;
      if (gr) script[i].gid = gr->gr_gid ;
      else if (!gid0_scan(s + mark, &script[i].gid))
      {
        char fmtline[UINT_FMT] ;
        fmtline[uint_fmt(fmtline, line)] = 0 ;
        strerr_dief5x(2, "syntax error during second pass: ", "line ", fmtline, ": unable to get gid from string: ", s + mark) ;
      }
    }
    if (what & 0x00008000)
    {
      unsigned int m ;
      if (!uint0_oscan(s + mark, &m))
      {
        char fmtline[UINT_FMT] ;
        fmtline[uint_fmt(fmtline, line)] = 0 ;
        strerr_dief5x(2, "syntax error during second pass: ", "line ", fmtline, ": unable to scan mode from string: ", s + mark) ;
      }
      script[i].mode = m ;
    }
    if (what & 0x00002000) script[i].cmdtype |= ACTION_REMOVE ;
    if (what & 0x00001000) script[i].cmdtype |= ACTION_ADD ;
    if (what & 0x00000800) script[i].movetype = MOVEINFO_MOVE ;
    if (what & 0x00000400) script[i].movetype = MOVEINFO_MOVEANDLINK ;
    if (what & 0x00000200) script[i].movetype = MOVEINFO_NOCREATE ;
    if (what & 0x00000100) script[i].movepath = pos ;
    if (what & 0x00000080) script[i].command = pos ;
    if (what & 0x00000040) { line++ ; col0 = pos ; }
    if (what & 0x00004000) i++ ;
    pos++ ;
  }

  if (state == 0x1f)
  {
    char fmtline[UINT_FMT] ;
    char fmtcol[UINT_FMT] ;
    fmtline[uint_fmt(fmtline, line)] = 0 ;
    fmtcol[uint_fmt(fmtcol, pos - col0 - 1)] = 0 ;
    strerr_dief5x(2, "syntax error during second pass: ", "line ", fmtline, " column ", fmtcol) ;
  }
}


 /* Firmware management */

static inline int wait_for_loading (char const *sysdevpath, size_t sysdevpathlen)
{
  int lfd = -1 ;
  unsigned int n = 150 ;
  static tain_t const period = { .sec = TAI_ZERO, .nano = 200000000 } ;
  char loadingfn[sysdevpathlen + 9] ;
  memcpy(loadingfn, sysdevpath, sysdevpathlen) ;
  memcpy(loadingfn + sysdevpathlen, "/loading", 9) ;
  while (n--)  /* sysfs doesn't support inotify, so we have to poll -_- */
  {
    tain_t deadline ;
    lfd = open_write(loadingfn) ;
    if (lfd >= 0) break ;
    tain_add_g(&deadline, &period) ;
    deepsleepuntil_g(&deadline) ;
  }
  if (ndelay_off(lfd) < 0)
  {
    fd_close(lfd) ;
    return -1 ;
  }
  return lfd ;
}

static inline void load_firmware (char const *fw, char const *sysdevpath)
{
  size_t fwbaselen = strlen(fwbase) ;
  size_t fwlen = strlen(fw) ;
  size_t sysdevpathlen = strlen(sysdevpath) ;
  int fwfd, loadingfd ;
  char fwfn[fwbaselen + fwlen + 2] ;
  memcpy(fwfn, fwbase, fwbaselen) ;
  fwfn[fwbaselen] = '/' ;
  memcpy(fwfn + fwbaselen + 1, fw, fwlen + 1) ;
  if (dryrun)
  {
    strerr_warni5x("dry run: copy ", fwfn, " to ", sysdevpath, "/data") ;
    return ;
  }
  fwfd = open_readb(fwfn) ;
  if (fwfd < 0 && verbosity >= 2) strerr_warnwu3sys("open ", fwfn, " for reading") ;
  loadingfd = wait_for_loading(sysdevpath, sysdevpathlen) ;
  if (loadingfd < 0)
  {
    if (verbosity >= 2) strerr_warnwu3sys("open ", sysdevpath, "/loading for writing") ;
    goto errclosef ;
  }
  if (fwfd < 0) goto errclosel ;
  if (fd_write(loadingfd, "1", 1) < 1)
  {
    if (verbosity >= 2) strerr_warnwu3sys("write 1 to ", sysdevpath, "/loading") ;
    goto errclosel ;
  }
  {
    int datafd ;
    char datafn[sysdevpathlen + 6] ;
    memcpy(datafn, sysdevpath, sysdevpathlen) ;
    memcpy(datafn + sysdevpathlen, "/data", 6) ;
    datafd = open_write(datafn) ;
    if (datafd < 0)
    {
      if (verbosity >= 2) strerr_warnwu3sys("open ", datafn, " for writing") ;
      goto errload ;
    }
    if (ndelay_off(datafd) < 0)
    {
      if (verbosity >= 2) strerr_warnwu2sys("ndelay_off ", datafn) ;
      goto errload ;
    }
    if (fd_cat(fwfd, datafd) < 0)
    {
      if (verbosity >= 2) strerr_warnwu4sys("copy ", fwfn, " to ", datafn) ;
      goto errload ;
    }
    fd_close(datafd) ;
    fd_write(loadingfd, "0", 1) ;
  }
  fd_close(loadingfd) ;
  fd_close(fwfd) ;
  return ;

 errload:
  allwrite(loadingfd, "-1", 2) ;
 errclosel:
  fd_close(loadingfd) ;
 errclosef:
  if (fwfd >= 0) fd_close(fwfd) ;
}


 /* uevent management */

static char *event_getvar (struct uevent_s *event, char const *var)
{
  size_t varlen = strlen(var) ;
  unsigned short i = 1 ;
  for (; i < event->varn ; i++)
    if (!strncmp(var, event->buf + event->vars[i], varlen) && event->buf[event->vars[i] + varlen] == '=')
      break ;
  return i < event->varn ? event->buf + event->vars[i] + varlen + 1 : 0 ;
}

static inline unsigned char format_cclass (char c)
{
  static unsigned char const classtable[58] = "0333333333333333333333333333333333333133333333332222222222" ;
  return (unsigned char)c < 58 ? classtable[(unsigned char)c] - '0' : 3 ;
}

static ssize_t alias_format (char *out, size_t outmax, char const *in, char const *data, regmatch_t const *off)
{
  static unsigned char const table[2][4] = { { 0x12, 0x01, 0x10, 0x10 }, { 0x03, 0x10, 0x20, 0x03 } } ;
  size_t w = 0 ;
  unsigned int state = 0 ;
  while (state < 2)
  {
    char next = *in++ ;
    unsigned char what = table[state][format_cclass(next)] ;
    state = what & 0x03 ;
    if (what & 0x10)
    {
      if (w >= outmax) return (errno = ENAMETOOLONG, -1) ;
      if (out) out[w] = next ;
      w++ ;
    }
    if (what & 0x20)
    {
      unsigned int i = next - '0' ;
      size_t len = off[i].rm_eo - off[i].rm_so ;
      if (w + len > outmax) return -1 ;
      if (out) memcpy(out + w, data + off[i].rm_so, len) ;
      w += len ;
    }
  }
  if (state == 3) return (errno = EINVAL, -1) ;
  return w ;
}

static inline void spawn_command (char const *command, struct uevent_s const *event)
{
  char const *argv[4] = { "/bin/sh", "-c", command, 0 } ;
  size_t envlen = env_len((char const **)environ) ;
  char const *envp[envlen + event->varn + 1] ;
  if (!env_merge(envp, envlen + event->varn + 1, (char const **)environ, envlen, event->buf + event->vars[1], event->len - event->vars[1]))
  {
    if (verbosity) strerr_warnwu1sys("merge environment to spawn command") ;
    return ;
  }
  pid = child_spawn0(argv[0], argv, envp) ;
  if (!pid)
  {
    if (verbosity) strerr_warnwu1sys("spawn command") ;
  }
}

static inline int run_scriptelem (struct uevent_s *event, scriptelem const *elem, char const *storage, struct envmatch_s const *envmatch, char *devname, mode_t devtype, unsigned int action, int mmaj, int mmin)
{
  size_t devnamelen = strlen(devname) ;
  size_t nodelen = 0 ;
  char *node = event->buf + event->len + 5 ;
  regmatch_t off[10] ;
  unsigned short i = 0 ;
  for (; i < elem->envmatchlen ; i++)
  {
    char const *x = event_getvar(event, storage + envmatch[elem->envmatchs + i].var) ;
    if (!x) return 0 ;
    if (regexec(&envmatch[elem->envmatchs + i].re, x, 0, 0, 0)) return 0 ;
  }

  switch (elem->devmatchtype)
  {
    case DEVMATCH_NOTHING:
    case DEVMATCH_CATCHALL: break ;
    case DEVMATCH_MAJMIN:
      if (mmaj >= 0 && mmin >= 0 && mmaj == elem->devmatch.majmin.maj && mmin >= elem->devmatch.majmin.minlo && mmin <= elem->devmatch.majmin.minhi) break ;
      return 0 ;
    case DEVMATCH_DEVRE:
      if (!regexec(&elem->devmatch.devre, devname, 10, off, 0)
       && !off[0].rm_so && off[0].rm_eo == strlen(devname))
        break ;
      return 0 ;
  }

  switch (elem->movetype)
  {
    case MOVEINFO_NOTHING :
    case MOVEINFO_NOCREATE :
      memcpy(node, devname, devnamelen + 1) ;
      nodelen = devnamelen ;
      break ;
    case MOVEINFO_MOVE :
    case MOVEINFO_MOVEANDLINK :
    {
      ssize_t r = alias_format(node, PATH_MAX, storage + elem->movepath, devname, off) ;
      if (r <= 1)
      {
        if (verbosity) strerr_warnwu5sys("process expression \"", storage + elem->movepath, "\" with devname \"", devname, "\"") ;
        return -1 ;
      }
      if (node[r - 2] == '/')
      {
        if (r + devnamelen >= PATH_MAX)
        {
          errno = ENAMETOOLONG ;
          if (verbosity) strerr_warnwu2sys("create alias for ", devname) ;
          return -1 ;
        }
        memcpy(node + r - 1, devname, devnamelen + 1) ;
        nodelen = r + devnamelen - 1 ;
      }
      break ;
    }
  }
  if (elem->movetype != MOVEINFO_NOCREATE && action == ACTION_ADD && mmaj >= 0)
  {
    if (!makesubdirs(node)) return -1 ;
    if (dryrun)
    {
      char fmtmaj[UINT_FMT] ;
      char fmtmin[UINT_FMT] ;
      char fmtmode[UINT_OFMT] ;
      fmtmaj[uint_fmt(fmtmaj, mmaj)] = 0 ;
      fmtmin[uint_fmt(fmtmin, mmin)] = 0 ;
      fmtmode[uint_ofmt(fmtmode, elem->mode)] = 0 ;
      strerr_warni6x("dry run: mknod ", node, S_ISBLK(devtype) ? " b " : " c ", fmtmaj, " ", fmtmin) ;
      strerr_warni4x("dry run: chmod ", fmtmode, " ", node) ;
    }
    else if (mknod(node, elem->mode | devtype, makedev(mmaj, mmin)) < 0)
    {
      if (errno != EEXIST)
      {
        if (verbosity) strerr_warnwu2sys("mknod ", node) ;
        return -1 ;
      }
      if (chmod(node, elem->mode) < 0 && verbosity >= 2)
        strerr_warnwu2sys("chmod ", node) ;
    }
    if (elem->uid || elem->gid)
    {
      if (dryrun)
      {
        char fmtuid[UID_FMT] ;
        char fmtgid[GID_FMT] ;
        fmtuid[uid_fmt(fmtuid, elem->uid)] = 0 ;
        fmtgid[gid_fmt(fmtgid, elem->gid)] = 0 ;
        strerr_warni6x("dry run: chown ", fmtuid, ":", fmtgid, " ", node) ;
      }
      else if (chown(node, elem->uid, elem->gid) < 0 && verbosity >= 2)
        strerr_warnwu2sys("chown ", node) ;
    }
    if (mmaj == root_maj && mmin == root_min)
    {
      if (dryrun) strerr_warni3x("dry run: symlink ", node, " to root") ;
      else symlink(node, "root") ;
    }
    if (elem->movetype == MOVEINFO_MOVEANDLINK)
    {
      if (!makesubdirs(devname)) return -1 ;
      if (dryrun) strerr_warni4x("dry run: symlink ", node, " to ", devname) ;
      else if (symlink(node, devname) < 0)
      {
        if (errno != EEXIST)
        {
          if (verbosity)
            strerr_warnwu4sys("symlink ", node, " to ", devname) ;
          return -1 ;
        }
        else
        {
          char tmppath[devnamelen + 20] ;
          memcpy(tmppath, devname, devnamelen) ;
          memcpy(tmppath + devnamelen, ":mdevd-", 7) ;
          surfname(tmppath + devnamelen + 7, 12) ;
          tmppath[devnamelen + 19] = 0 ;
          if (symlink(node, tmppath) < 0)
          {
            if (verbosity)
              strerr_warnwu4sys("symlink ", node, " to ", tmppath) ;
          }
          else if (rename(tmppath, devname) < 0)
          {
            if (verbosity)
              strerr_warnwu4sys("rename ", tmppath, " to ", devname) ;
            unlink(tmppath) ;
          }
        }
      }
    }
  }

  if (action & elem->cmdtype)
  {
    event->vars[event->varn++] = event->len ;
    memcpy(event->buf + event->len, "MDEV=", 5) ;
    event->len += 6 + nodelen ;
    if (dryrun)
    {
      strerr_warni2x("dry run: spawn ", storage + elem->command) ;
      if (verbosity >= 2)
      {
        char buf[UEVENT_MAX_SIZE + PATH_MAX + 5] ;
        size_t j = 0 ;
        unsigned short i = 1 ;
        for (; i < event->varn ; i++)
        {
          size_t len = strlen(event->buf + event->vars[i]) ;
          memcpy(buf + j, event->buf + event->vars[i], len) ;
          buf[j+len] = ' ' ;
          j += len+1 ;
        }
        buf[j-1] = 0 ;
        strerr_warni2x("dry run: added variables: ", buf) ;
      }
    }
    else spawn_command(storage + elem->command, event) ;
  }

  if (elem->movetype != MOVEINFO_NOCREATE && action == ACTION_REMOVE && mmaj >= 0)
  {
    if (elem->movetype == MOVEINFO_MOVEANDLINK)
    {
      if (dryrun) strerr_warni2x("dry run: unlink ", devname) ;
      else unlink(devname) ;
    }
    if (dryrun) strerr_warni2x("dry run: unlink ", node) ;
    else unlink(node) ;
  }

  return !elem->flagcont ;  
}

static inline void run_script (struct uevent_s *event, scriptelem const *script, unsigned short scriptlen, char const *storage, struct envmatch_s const *envmatch, char *devname, mode_t devtype, unsigned int action, int mmaj, int mmin)
{
  unsigned short i = 0 ;
  for (; i < scriptlen ; i++)
  {
    int r ;
    r = run_scriptelem(event, script + i, storage, envmatch, devname, devtype, action, mmaj, mmin) ;
    if (r) break ;
  }
}

static inline void act_on_event (struct uevent_s *event, char *sysdevpath, size_t sysdevpathlen, unsigned int action, scriptelem const *script, unsigned short scriptlen, char const *storage, struct envmatch_s const *envmatch)
{
  ssize_t hasmajmin = 0 ;
  unsigned int mmaj, mmin ;
  mode_t devtype = S_IFCHR ;
  char *devname ;
  char const *x = event_getvar(event, "MAJOR") ;
  char buf[UEVENT_MAX_SIZE] ;
  if (action == ACTION_ADD)
  {
    if (x && uint0_scan(x, &mmaj))
    {
      x = event_getvar(event, "MINOR") ;
      if (x && uint0_scan(x, &mmin)) hasmajmin = 1 ;
    }
    if (!hasmajmin)
    {
      memcpy(sysdevpath + sysdevpathlen, "/dev", 5) ;
      hasmajmin = openreadnclose(sysdevpath, buf, UINT_FMT << 1) ;
      sysdevpath[sysdevpathlen] = 0 ;
      if (hasmajmin > 0)
      {
        size_t i = uint_scan(buf, &mmaj) ;
        if (i > 0 && buf[i] == ':')
        {
          size_t j = uint_scan(buf + i + 1, &mmin) ;
          if (j > 0 && buf[i+1+j] == '\n') ;
          else hasmajmin = 0 ;
        }
        else hasmajmin = 0 ;
      }
    }
  }

  devname = event_getvar(event, "DEVNAME") ;
  if (!devname)
  {
    ssize_t r ;
    memcpy(sysdevpath + sysdevpathlen, "/uevent", 8) ;
    r = openreadnclose(sysdevpath, buf, UEVENT_MAX_SIZE-1) ;
    sysdevpath[sysdevpathlen] = 0 ;
    if (r > 0)
    {
      buf[r] = 0 ;
      devname = strstr(buf, "\nDEVNAME=") ;
      if (devname)
      {
        devname += 9 ;
        *strchr(devname, '\n') = 0 ;
      }
    }
    if (!devname) devname = basename(sysdevpath) ;
  }
  if (strlen(devname) >= PATH_MAX - 1)
  {
    if (verbosity) strerr_warnwu2x("device name too long: ", devname) ;
    return ;
  }
  if (strstr(sysdevpath, "/block/")) devtype = S_IFBLK ;
  else
  {
    x = event_getvar(event, "SUBSYSTEM") ;
    if (x && str_start(x, "block")) devtype = S_IFBLK ;
  }
  run_script(event, script, scriptlen, storage, envmatch, devname, devtype, action, hasmajmin > 0 ? mmaj : -1, hasmajmin > 0 ? mmin : -1) ;
}

static inline void on_event (struct uevent_s *event, scriptelem const *script, unsigned short scriptlen, char const *storage, struct envmatch_s const *envmatch)
{
  unsigned int action ;
  char const *x = event_getvar(event, "ACTION") ;
  if (!x) return ;
  if (!strcmp(x, "add")) action = ACTION_ADD ;
  else if (!strcmp(x, "remove")) action = ACTION_REMOVE ;
  else return ;
  x = event_getvar(event, "DEVPATH") ;
  if (!x) return ;
  {
    size_t devpathlen = strlen(x) ;
    size_t slashsyslen = strlen(slashsys) ;
    char sysdevpath[devpathlen + slashsyslen + 2 + 7] ;
    memcpy(sysdevpath, slashsys, slashsyslen) ;
    sysdevpath[slashsyslen] = '/' ;
    memcpy(sysdevpath + slashsyslen + 1, x, devpathlen + 1) ;
    x = event_getvar(event, "FIRMWARE") ;
    if (action == ACTION_ADD || !x) act_on_event(event, sysdevpath, slashsyslen + devpathlen + 1, action, script, scriptlen, storage, envmatch) ;
    if (action == ACTION_ADD && x) load_firmware(x, sysdevpath) ;
  }
}


 /* Tying it all together */

static inline int handle_signals (void)
{
  for (;;)
  {
    int c = selfpipe_read() ;
    switch (c)
    {
      case -1 : strerr_diefu1sys(111, "selfpipe_read") ;
      case 0 : return 0 ;
      case SIGHUP : return 1 ;
      case SIGCHLD :
        if (!pid) wait_reap() ;
        else
        {
          int wstat ;
          int r = wait_pid_nohang(pid, &wstat) ;
          if (r < 0)
            if (errno != ECHILD) strerr_diefu1sys(111, "wait_pid_nohang") ;
            else break ;
          else if (!r) break ;
          pid = 0 ;
        }
        break ;
      default :
        strerr_dief1x(101, "internal error: inconsistent signal handling. Please submit a bug-report.") ;
    }
  }
}

static void handle_stdin (struct uevent_s *event, scriptelem const *script, unsigned short scriptlen, char const *storage, struct envmatch_s const *envmatch, size_t *w)
{
  while (!pid)
  {
    ssize_t r ;
    if (event->len >= UEVENT_MAX_SIZE)
      strerr_dief2x(1, "received invalid event: ", "too long") ;
    r = sanitize_read(getlnmax(buffer_0, event->buf + event->len, UEVENT_MAX_SIZE - event->len, w, '\0')) ;
    if (r < 0)
    {
      cont = 0 ;
      if (errno != EPIPE && verbosity) strerr_warnwu1sys("read from stdin") ;
      if (event->len) strerr_dief1x(1, "received incomplete event") ;
    }
    if (r <= 0) break ;
    if (*w > 1)
    {
      if (event->varn >= UEVENT_MAX_VARS)
        strerr_dief2x(1, "received invalid event: ", "too many variables") ;
      event->vars[event->varn++] = event->len ;
      event->len += *w ;
    }
    else
    {
      if (event->varn > 1) on_event(event, script, scriptlen, storage, envmatch) ;
      event->len = 0 ;
      event->varn = 0 ;
    }
    *w = 0 ;
  }
}

int main (int argc, char const *const *argv)
{
  char const *configfile = "/etc/mdev.conf" ;
  iopause_fd x[2] = { { .events = IOPAUSE_READ }, { .fd = 0 } } ;
  PROG = "mdevd" ;
  {
    char const *slashdev = "/dev" ;
    subgetopt_t l = SUBGETOPT_ZERO ;
    for (;;)
    {
      int opt = subgetopt_r(argc, argv, "nv:f:s:d:F:", &l) ;
      if (opt == -1) break ;
      switch (opt)
      {
        case 'n' : dryrun = 1 ; break ;
        case 'v' : if (!uint0_scan(l.arg, &verbosity)) dieusage() ; break ;
        case 'f' : configfile = l.arg ; break ;
        case 's' : slashsys = l.arg ; break ;
        case 'd' : slashdev = l.arg ; break ;
        case 'F' : fwbase = l.arg ; break ;
        default : dieusage() ;
      }
    }
    argc -= l.ind ; argv += l.ind ;
    if (configfile[0] != '/') strerr_dief2x(100, configfile, " is not an absolute path") ;
    if (slashsys[0] != '/') strerr_dief2x(100, slashsys, " is not an absolute path") ;
    if (slashdev[0] != '/') strerr_dief2x(100, slashdev, " is not an absolute path") ;
    if (fwbase[0] != '/') strerr_dief2x(100, fwbase, " is not an absolute path") ;
    if (chdir(slashdev) < 0) strerr_diefu2sys(111, "chdir to ", slashdev) ;
  }

  if (strlen(slashsys) >= PATH_MAX - 1) strerr_dief1x(100, "paths too long") ;
  if (!fd_sanitize()) strerr_diefu1sys(111, "sanitize standard fds") ;

  {
    struct stat st ;
    if (stat("/", &st) < 0) strerr_diefu1sys(111, "stat /") ;
    root_maj = major(st.st_dev) ;
    root_min = minor(st.st_dev) ;
  }

  if (ndelay_on(0) < 0) strerr_diefu1sys(111, "set stdin nonblocking") ;
  x[0].fd = selfpipe_init() ;
  if (x[0].fd < 0) strerr_diefu1sys(111, "init selfpipe") ;
  if (sig_ignore(SIGPIPE) < 0) strerr_diefu1sys(111, "ignore SIGPIPE") ;
  {
    sigset_t set ;
    sigemptyset(&set) ;
    sigaddset(&set, SIGCHLD) ;
    sigaddset(&set, SIGHUP) ;
    if (selfpipe_trapset(&set) < 0)
      strerr_diefu1sys(111, "trap signals") ;
  }
  mdevd_random_init() ;
  umask(0) ;

  while (cont || pid)
  {
    ssize_t len ;
    unsigned short scriptlen = 0 ;
    unsigned short envmatchlen = 0 ;
    char buf[BUFSIZE] ;
    len = openreadnclose(configfile, buf, BUFSIZE - 1) ;
    if (len < 0)
    {
      if (errno != ENOENT) strerr_diefu2sys(111, "read ", configfile) ;
      strerr_warnwu2sys("read ", configfile) ;
      len = 0 ;
    }
    buf[len++] = 0 ;
    script_firstpass(buf, &scriptlen, &envmatchlen) ;

    {
      size_t w = 0 ;
      struct uevent_s event = UEVENT_ZERO ;
      struct envmatch_s envmatch[envmatchlen ? envmatchlen : 1] ;
      scriptelem script[scriptlen + 1] ;
      memset(script, 0, scriptlen * sizeof(scriptelem)) ;
      script[scriptlen++] = scriptelem_catchall ;
      script_secondpass(buf, script, envmatch) ;
      while (cont || pid)
      {
        static tain_t const deadline = TAIN_INFINITE ;
        if (buffer_len(buffer_0)) handle_stdin(&event, script, scriptlen, buf, envmatch, &w) ;
        x[1].events = pid ? 0 : IOPAUSE_READ ;
        if (iopause_g(x, 1 + cont, &deadline) < 0) strerr_diefu1sys(111, "iopause") ;
        if (x[0].revents & IOPAUSE_READ && handle_signals()) break ;
        if (cont && !pid && x[1].revents & IOPAUSE_READ)
          handle_stdin(&event, script, scriptlen, buf, envmatch, &w) ;
      }
      script_free(script, scriptlen, envmatch, envmatchlen) ;
    }
  } 
  return 0 ;
}
