#ifndef __C0RT_H__
#define __C0RT_H__

#define C0_HAVE_CONCRETE_RUNTIME
#include <c0runtime.h>

struct c0_array_header {
  c0_int count;
  c0_int elt_size;
  c0_char elems[];
};

// For slight speed gain, inline:
#define c0_string_fromliteral(s) (s)

#endif // __C0RT_H__

