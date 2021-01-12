#include <stdlib.h>
#include <stdio.h>
#include <signal.h>
#include <limits.h>
#include <gc.h>
#include <c0runtime.h>
#include <strings.h> // defines bzero()

void c0_runtime_init(const char* filename, const char** map, long len) {
  (void)filename; (void)map; (void)len;
  GC_INIT();
}

void c0_runtime_cleanup() {
  // nothing to do for the c0rt runtime
}

void raise_msg(int signal, const char* msg) {
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  raise(signal);
}

void c0_error(const char *msg) {
  fprintf(stderr, "Error: %s\n", msg);
  fflush(stderr);
  exit(EXIT_FAILURE);
}

void c0_abort(const char *reason) {
  raise_msg(SIGABRT, reason);
}

/* Arithmetic */

c0_int c0_idiv(c0_int x, c0_int y) { return x/y; }
c0_int c0_imod(c0_int x, c0_int y) { return x%y; }
c0_int c0_sal(c0_int x, c0_int y) { return x<<y; }
c0_int c0_sar(c0_int x, c0_int y) { return x>>y; }


/* Memory */

c0_pointer c0_alloc(size_t size) {
  void* p = GC_MALLOC(size);
  bzero(p, size);
  return p;
}

c0_array c0_array_alloc(size_t elemsize, c0_int elemcount) {
  return c0_alloc(elemsize*elemcount);
}

void* c0_array_sub(c0_array a, c0_int idx, size_t elemsize) {
  return ((char*)a) + idx*elemsize;
}

// String impl provided by ../bare/cstr.c
