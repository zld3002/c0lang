#include <c0runtime.h>
#include <gc.h>

c0_pointer c0_alloc(size_t size) {
  if (!size)
    size = 1;

  void* mem = GC_MALLOC(size);
  if (!mem) c0_abort_mem("Cannot allocate memory");
  bzero(mem, size);
  return mem;
}

