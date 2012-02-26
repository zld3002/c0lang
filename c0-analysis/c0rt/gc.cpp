#include "c0rt.h"
#include <gc.h>
#include <strings.h>

void* c0_alloc(size_t size) {
  if (!size)
    size = 1;

  void* mem = GC_MALLOC(size);
  if (!mem)
    c0_abort_mem("Cannot allocate memory");
  bzero(mem, size);
  return mem;
}

