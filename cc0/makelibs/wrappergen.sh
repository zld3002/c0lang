#!/bin/sh
# TODO: make not x86 specific (will this matter?)
SUFFIX=linux
case `uname -s` in
Linux) SUFFIX=linux; ;;
FreeBSD) SUFFIX=bsd ;;
Darwin) SUFFIX=darwin ;;
CYGWIN*) SUFFIX=cygwin ;;
*) echo "Unknown OS!" ;;
esac

MACHINE=amd64
case `uname -m` in
i*86) MACHINE=x86; ;;
x86_64) MACHINE=amd64; ;;
*) echo "Unknown machine type! Assuming x86..." ;;
esac

IMGDIR=`dirname $0`
sml @SMLcmdname=$0 @SMLload=$IMGDIR/wrappergen.heap.$MACHINE-$SUFFIX "$@"
