#include <stdlib.h>
#include <stdio.h>
#include <signal.h>
#include "bare.h"

void c0_runtime_init() {
    // nothing to do for the bare runtime
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

void c0_abort_mem(const char *reason) {
  raise_msg(SIGSEGV, reason);
}

void* c0_array_sub(c0_array* A, int i, size_t elemsize) {
  if (A == NULL)
    c0_abort_mem("attempt to access default zero-size array");
  if (((unsigned)i) >= (unsigned)(A->count))
    c0_abort_mem("array index out of bounds");
  return (void *) (A->elems + i*A->elt_size);
}

void* c0_alloc (size_t elt_size) {
  int* p = calloc(1, elt_size);
  if (p == NULL)
    c0_abort_mem("allocation failed");
  return (void *)p;
}

c0_array* c0_array_alloc(size_t elemsize, int elemcount) {
  /* test for overflow, somehow? */
  c0_array *p;
  if (elemcount < 0)
    c0_abort_mem("array size cannot be negative");
  if (elemsize > 0 && elemcount > ((1<<30)-8)/elemsize)
    c0_abort_mem("array size too large");
  /* p = calloc(elemcount*(elemsize/4)+2, sizeof(int)); // <- BUG */
  p = calloc(1, sizeof(struct c0_array) + elemcount*elemsize);
  if (p == NULL)
    c0_abort_mem("array allocation failed");
  p->count = elemcount;               /* initialize number of elements */
  p->elt_size = elemsize;            /* store element size */
  return p;
}

int c0_array_length(c0_array* A) {
  return A ? A->count : 0;
}
