#!/bin/sh

### functions used below ###

usage () {
    echo "Usage: $0 [options] [cc0-sml options] file"
    echo ""
    echo "Options:"
    echo "  -v, --verbose   Enable verbose output"
    echo "  -h, --help      Display this information"
    echo ""
    echo "All unrecognized options are passed to cc0-sml."
}

vecho () {
    if [ -n "$verbose" ]; then
        echo "$@"
    fi
}

last_arg () {
    local filename;
    for i in "$@"; do
        filename=$i
    done
    echo "$filename"
}


### parse parameters ###

# long options are faked with an option '-' which takes a parameter
while getopts ':vh-:' opt; do
    case $opt in
        v) verbose='-v' ;;
        h) usage; exit 0 ;;
        # fake long options
        -) case $OPTARG in
            v|verbose) verbose='-v' ;;
            h|help) usage; exit 0 ;;
            *) OPTIND=$(($OPTIND-1)); break ;;
           esac ;;
        '?') OPTIND=$(($OPTIND-1)); break ;;
    esac
done
# shift away any parameters that we have processed
shift $(($OPTIND-1))


### set filenames and directory names ###

cc0dir=`dirname $0`
c0root="$cc0dir/.."

c0filename=`last_arg "$@"`
cfilename=${c0filename%.c0}.c


### run the various compilers ###

vecho "Compiling $c0filename -> $cfilename"
$cc0dir/cc0-sml $verbose "$@"

if [ $? -ne 0 ]; then
    vecho "Compilation $c0filename -> $cfilename failed"
    exit $?
fi

if [ -e $cfilename ]; then
    vecho "Compiling $cfilename -> a.out"
    gcc -O2 -I. -I$c0root/include -lgc -lQtCore -lQtGui $c0root/lib/cc0lib.c $cfilename $c0root/lib/cc0main.c $c0root/lib/libstdc0.a $c0root/lib/libc0rt.a
    if [ $? -ne 0 ]; then
        vecho "Compilation $cfilename -> a.out  failed"
        exit $?
    else
        vecho "Compiled successfully"
        exit 0
    fi
else
    exit 1
fi
