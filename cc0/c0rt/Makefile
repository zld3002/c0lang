# RUNTIME = true
# LIBNAME = c0rt
# SOURCES = c0rt.c ../bare/cstr.c 
# DEPTH = ..
# REQUIRES = gc

# include ../lib.mk

# TODO: Make this use ../lib.mk again
libc0rt.so: c0rt.c
	gcc -g -std=c99 -fPIC -I../include  -I../../externals/gc/include -c c0rt.c -o c0rt.o
	g++  -shared -Wl,-soname,libc0rt.so -o libc0rt.so c0rt.o ../bare/cstr.o -L/home/ishan/c0-developer/cc0/lib  -lgc -lpthread -lbacktrace
