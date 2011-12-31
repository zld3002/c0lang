#include <stdlib.h>
#include <stdio.h>
#include <signal.h>
#include <limits.h>
#include <gc.h>
#include "unsafe.h"

void c0_runtime_init() {
    GC_INIT();
}

void raise_msg(int signal, const char* msg) {
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  raise(signal);
}

void c0_abort(const char *reason) {
  raise_msg(SIGABRT, reason);
}

void c0_abort_mem(const char *reason) {
  raise_msg(SIGSEGV, reason);
}

void* c0_alloc(size_t bytes) {
  void* p = GC_malloc(bytes);
  if (!p)
    c0_abort_mem("Out of memory");
  bzero(p, bytes);
  return p;
}

c0_array* c0_array_alloc(size_t elemsize, int elemcount) {
  if (elemsize == 0 || elemcount < 0)
    c0_abort_mem("Bad allocation request");
  // XXX: won't calloc check for this? Not entirely sure what we're checking
  // here...
  if (INT_MAX / elemsize < elemcount)
    c0_abort_mem("Allocation request is too large");
  c0_array* arr = c0_alloc(elemsize*elemcount);
  if (!arr)
    c0_abort_mem("Out of memory");
  return arr;
}

void* c0_array_sub(c0_array *a, int idx, size_t elemsize) {
  return ((char*)a) + idx*elemsize;
}

// String impl provided by ../bare/cstr.c
