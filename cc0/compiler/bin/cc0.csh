#! /bin/csh -f
set filename=$argv[$#]
echo "Compiling $filename -> $filename:r.c"
bin/cc0-sml $*
if ($?) then
  echo "Compilation $filename -> $filename:r.c failed"
  exit 1
else
if (-e $filename:r.c) then
# gcc -m64 -I. bin/cc0lib.c $filename:r.c bin/cc0main.c >&! $filename:r.txt
    echo "Compiling $filename:r.c -> a.out"
    gcc -O2 -I. -Iinclude lib/cc0lib.c $filename:r.c lib/cc0main.c
    if ($?) then
	echo "Compilation $filename:r.c -> a.out failed"
        exit 1
    else
        echo "Compiled successfully"
	exit 0
    endif
else
    exit 1
endif
endif
