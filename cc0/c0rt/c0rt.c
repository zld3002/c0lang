#include <stdlib.h>
#include <stdio.h>
#include <signal.h>
#include <limits.h>
#include <gc.h>
#include <c0runtime.h>
#include <strings.h> // defines bzero()

void c0_runtime_init() {
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

void c0_abort_arith(const char *reason) {
  raise_msg(SIGFPE, reason);
}

c0_int c0_idiv(c0_int x, c0_int y) {
  if(y == 0) c0_abort_arith("division by 0");
  if(y == -1 && x == INT_MIN) c0_abort_arith("division causes overflow");
  return x/y;
}

c0_int c0_imod(c0_int x, c0_int y) {
  if(y == 0) c0_abort_arith("modulo by 0");
  if(y == -1 && x == INT_MIN) c0_abort_arith("modulo causes overflow");
  return x%y;  
}

c0_int c0_sal(c0_int x, c0_int y) {
  if(y < 0 || y >= 32) c0_abort_arith("shift left out-of-range");
  return x<<y;
}

c0_int c0_sar(c0_int x, c0_int y) {
  if(y < 0 || y >= 32) c0_abort_arith("shift right out-of-range");
  return x>>y;
}


/* Memory */

struct c0_array_header {
  c0_int count;
  c0_int elt_size;
  c0_char elems[];
};

void c0_abort_mem(const char *reason) {
  raise_msg(SIGSEGV, reason);
}

c0_pointer c0_alloc(size_t size) {
  if (!size)
    size = 1;

  void* p = GC_MALLOC(size);
  if (!p) c0_abort_mem("allocation failed");
  bzero(p, size);
  return p;
}

void* c0_deref(c0_pointer a){
  if (a == NULL) c0_abort_mem("attempt to dereference null pointer");
  return a;
}

c0_array c0_array_alloc(size_t elemsize, c0_int elemcount) {
  /* test for overflow, somehow? */
  if (elemcount < 0) c0_abort_mem("array size cannot be negative");
  if (elemsize > 0 && elemcount > ((1<<30)-8)/elemsize)
    c0_abort_mem("array size too large");

  c0_array p = c0_alloc(sizeof(struct c0_array_header) + elemcount*elemsize);
  p->count = elemcount;              /* initialize number of elements */
  p->elt_size = elemsize;            /* store element size */
  return p;
}

void* c0_array_sub(c0_array A, c0_int i, size_t elemsize) {
  if (A == NULL) c0_abort_mem("attempt to access default zero-size array");
  if (((unsigned)i) >= (unsigned)(A->count))
    c0_abort_mem("array index out of bounds");
  return (void *) (A->elems + i*A->elt_size);
}

c0_int c0_array_length(c0_array A) {
  return A ? A->count : 0;
}
