#include <stddef.h>

typedef struct c0_array c0_array;

// Aborts execution and notifies the user of the reason
C0API void c0_abort(const char *reason);

// Allocates from the GC heap
C0API void *c0_alloc(size_t bytes);
// Allocate an array of elemsize elements of elemcount bytes per element
C0API c0_array* c0_array_alloc(size_t elemsize, int elemcount);

// Returns a pointer to the element at the given index of the given array
// Runtimes may ignore the element size
C0API void* c0_array_sub(c0_array *a, int idx, size_t elemsize);

#ifdef C0_HAVE_CONCRETE_RUNTIME
// Returns the length of the array. This is only permitted in certain C0
// programs since not all runtimes may support it.
C0API int c0_array_length(c0_array *a);
#endif

// Returns the empty string
C0API c0_string c0_string_empty();
// Returns the length of the given string
C0API int c0_string_length(c0_string s);

// Returns the character at the given index of the string. If the
// index is out of range, aborts.
C0API c0_char c0_string_charat(c0_string s, int i);

// Returns the substring composed of the characters of s beginning at
// index given by start and continuing up to but not including the
// index given by end
// If end <= start, the empty string is returned
// If end < 0 or end > the length of the string, it is treated as though
// it were equal to the length of the string.
// If start < 0 the empty string is returned.
C0API c0_string c0_string_sub(c0_string s, int a, int b);

// Returns a new string that is the result of concatenating b to a.
C0API c0_string c0_string_join(c0_string a, c0_string b);

// Constructs a c0rt_string_t from a null-terminated string
C0API c0_string c0_string_fromcstr(const char *s);

// Returns a null-terminated string from a c0_string. This string must
// be explicitly deallocated by calling c0_string_freecstr.
C0API const char *c0_string_tocstr(c0_string s);

// Frees a string returned by c0_string_tocstr
C0API void c0_string_freecstr(const char *s);

// Returns a c0_string from a string literal.
C0API c0_string c0_string_fromliteral(const char *s);

C0API bool c0_string_equal(c0_string a, c0_string b);
C0API int c0_string_compare(c0_string a, c0_string b);
C0API bool c0_char_equal(c0_char a, c0_char b);
C0API int c0_char_compare(c0_char a, c0_char b);
