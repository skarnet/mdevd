#
# This file has been generated by tools/gen-deps.sh
#

src/mdevd/mdevd-coldplug.o src/mdevd/mdevd-coldplug.lo: src/mdevd/mdevd-coldplug.c
src/mdevd/mdevd.o src/mdevd/mdevd.lo: src/mdevd/mdevd.c src/include/mdevd/config.h

mdevd: EXTRA_LIBS := -lskarnet ${MAYBEPTHREAD_LIB}
mdevd: src/mdevd/mdevd.o ${LIBNSSS}
mdevd-coldplug: EXTRA_LIBS := -lskarnet
mdevd-coldplug: src/mdevd/mdevd-coldplug.o
