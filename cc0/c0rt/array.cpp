#include "c0rt.h"
#include <stdio.h>
#include <limits>

struct c0_array {
  c0_array(size_t length)
    : mLength(length)
  {}
  void *elem(int idx, size_t elementSize) {
    // The length of the array is the element count which was originally an int so this cast is safe.
    if (this->length() <= static_cast<size_t>(idx))
      c0_abort_mem("Out of bounds array access");
    char *base = reinterpret_cast<char*>(this+1);
    return base + elementSize*idx;
  }
  size_t length() const {
    // If we are null, then assume we are an empty array
    return this ? mLength : 0;
  }
  void *operator new (size_t request, size_t elementSize, int elementCount) {
    // zero-sized arrays are allowed -wjl, 12-22-2010
    /*
    if (elementSize == 0)
      c0_abort_mem("Non-positive element size in array allocation");
    */
    if (elementCount < 0)
      c0_abort_mem("Negative array size requested in allocation");
    if (elementCount > 0 && (std::numeric_limits<ptrdiff_t>::max() - request) / elementCount < elementSize)
      c0_abort_mem("Array dimensions too large to address - allocation will fail");
    // Cast is safe because both are non-negative and won't overflow
    size_t array_length = size_t(elementSize * elementCount);

    // size_t is unsigned and ptrdiff_t is signed so we know that this won't
    // overflow either
    // Alignment is not a concern since sizeof c0_array is larger or equal to the
    // alignment restrictions of all data types in C0
    return c0_alloc(request + array_length);
  }
  void operator delete (void *) {
    c0_abort_mem("Attempt to explicitly delete a c0_array");
  }
private:
  size_t mLength;
};

c0_array *c0_array_alloc(size_t elementSize, int elementCount) {
  return new (elementSize, elementCount) c0_array(elementCount);
}

void* c0_array_sub(c0_array *array, int idx, size_t elementSize) {
  return array->elem(idx, elementSize);
}

int c0_array_length(c0_array *array) {
  return array->length();
}
