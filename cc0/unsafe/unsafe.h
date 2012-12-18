#ifndef __UNSAFE_H__
#define __UNSAFE_H__

#include <string.h>
#include <stdbool.h>

/* C0 runtime types */
typedef const char* c0_string;
typedef char c0_char;

// The real c0_array type is just the array elements
// but we don't have any way to express that so the
// structure remains undefined.
struct c0_array;

#undef C0_RUNTIME_IMPLEMENTS_LENGTH
#include <c0runtime.h>

// Check if we're being compiled by cc0 and provide
// these macros that inline calls to the runtime
#ifdef CC0

#undef cc0_array
#define cc0_array(ty) ty*

#undef cc0_array_sub
#define cc0_array_sub(ty, A, i) ((A)[(i)])

#undef cc0_deref
#define cc0_deref(ty, p) (*(p))

// Inline versions of most of the runtime for the generated code
#define c0_string_empty() ""
#define c0_string_length(s) strlen(s)
#define c0_string_charat(s,i) ((s)[(i)])

#define c0_string_equal(a,b) (0 == c0_string_compare(a,b))
#define c0_string_compare(a,b) strcmp(a,b)
#define c0_char_equal(a,b) ((a) == (b))
#define c0_char_compare(a,b) ((a) - (b))

#define c0_string_tocstr(s) (s)
#define c0_string_freecstr(s)

#define c0_string_fromliteral(s) s

#endif

#endif // __UNSAFE_H__

