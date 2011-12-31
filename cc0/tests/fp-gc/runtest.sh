#!/bin/sh -f
# next two lines to tie in hand-written gc
# LD_LIBRARY_PATH=./lib
# export LD_LIBRARY_PATH
# need at least -d 4096 (for GC runtime)
# experimentally, -v nnn is meansure in 1k blocks
ulimit -t 30 -d 4096 -v 20000 # between 2 and 4 MB
exec ./a.out
