#!/bin/sh
# usage: untabify.sh filename

if [ $# -eq 0 ]
    then
    echo "usage: $0 file1 [file2 ...]"
    exit 1;
fi
for f in $*; do
    tmpfile=$f.$$
    untabify < $f > $tmpfile
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
