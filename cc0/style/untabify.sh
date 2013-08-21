#!/bin/sh
# usage: untabify.sh [-t n] file1 [file2 ...]

if [ $# -eq 0 ]; then
    echo "usage: $0 file1 [file2 ...]"
    exit 1;
fi
if [ $1 = '-t' ]; then
    tabstop=$2
    shift 2
else 
    tabstop=8
fi
for f in $*; do
    tmpfile=$f.$$
    untabify-exec $tabstop < $f > $tmpfile
    if [ $? -eq 0 ]; then
        mv $tmpfile $f
        if [ $? -ne 0 ]; then
            echo "renaming temporary file $tmpfile failed"
            rm -f $tmpfile
            echo "$f: unchanged"
        else
            echo "$f: untabified"
        fi
    else
        rm -f $tmpfile
        echo "$f: unchanged"
    fi
done
