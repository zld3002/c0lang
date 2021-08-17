#ifndef __C0RT_H__
#define __C0RT_H__

#define C0_HAVE_CONCRETE_RUNTIME
#define C0_RUNTIME_IMPLEMENTS_LENGTH
#include <c0runtime.h>

// For slight speed gain, inline:
#define c0_string_fromliteral(s) (s)

#endif // __C0RT_H__

