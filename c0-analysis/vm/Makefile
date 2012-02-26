CC=gcc
C0LIBDIR=$(shell pwd)/../lib
C0RUNTIMEDIR=$(shell pwd)/../runtime

# always rebuild these
.PHONY: c0vm c0vmd

c0vm: c0vm.c
	$(CC) -ftrapv -Wall -Wextra -Werror -std=c99 -pedantic -g -L$(C0LIBDIR) -L$(C0RUNTIMEDIR) -Wl,-rpath $(C0LIBDIR) -Wl,-rpath $(C0RUNTIMEDIR) -lfile -lconio -lstring -lparse -largs -lcurses -limg -lbare -o c0vm xalloc.c stacks.c readfile.c read_program.c c0vm.c c0vm_c0ffi.c c0vm_main.c

c0vmd: c0vm.c
	$(MAKE) c0vm CC='gcc -DDEBUG'
