#ifndef __C0RUNTIME_H__
#define __C0RUNTIME_H__
#include <stddef.h>
#ifdef __cplusplus
#define C0API extern "C"
#else
#define C0API
#endif

#ifndef C0_HAVE_CONCRETE_RUNTIME
// Generic runtime definitions for compiling libraries
#include <stdbool.h>

typedef struct c0_string_impl* c0_string;
typedef char c0_char;
#endif

typedef struct c0_array c0_array;

// Initializes the runtime
C0API void c0_runtime_init();

// Aborts execution and notifies the user of the reason
C0API void c0_abort(const char *reason);
C0API void c0_abort_mem(const char *reason);

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

// Returns the character at the given index of the string. If the index is out
// of range, aborts.
C0API c0_char c0_string_charat(c0_string s, int i);

// Returns the substring composed of the characters of s beginning at index
// given by start and continuing up to but not including the index given by end
// If end <= start, the empty string is returned
// If end < 0 or end > the length of the string, it is treated as though it
//   were equal to the length of the string.
// If start < 0 the empty string is returned.
C0API c0_string c0_string_sub(c0_string s, int a, int b);

// Returns a new string that is the result of concatenating b to a.
C0API c0_string c0_string_join(c0_string a, c0_string b);

// Constructs a c0rt_string_t from a null-terminated string
C0API c0_string c0_string_fromcstr(const char *s);

// Returns a null-terminated string from a c0_string. This string must be
// explicitly deallocated by calling c0_string_freecstr.
C0API const char *c0_string_tocstr(c0_string s);

// Frees a string returned by c0_string_tocstr
C0API void c0_string_freecstr(const char *s);

// Returns a c0_string from a string literal.
C0API c0_string c0_string_fromliteral(const char *s);

C0API bool c0_string_equal(c0_string a, c0_string b);
C0API int c0_string_compare(c0_string a, c0_string b);
C0API bool c0_char_equal(c0_char a, c0_char b);
C0API int c0_char_compare(c0_char a, c0_char b);

#if defined(__cplusplus) && !defined(C0_HAVE_CONCRETE_RUNTIME)

#ifdef QT_VERSION
#include <QString>
#endif

namespace c0 {
struct gcobject {
  void *operator new(size_t requestedSize) {
    return c0_alloc(requestedSize);
  }
  void operator delete (void *) {
    c0_abort("Illegal attempt to delete gcobject");
  }
};

class string {
public:
  string(c0_string s)
    : mFree(true),
      mStr(NULL),
      mC0Str(s)
  {}
  string(const char *s)
    : mFree(false),
      mStr(s),
      mC0Str(NULL)
  {}
  ~string() {
    if (mFree && mStr)
      c0_string_freecstr(mStr);
  }

  c0_char operator[](int idx) {
    return c0_string_charat(static_cast<c0_string>(*this), idx);
  }

  const char *cstr() {
    if (!mStr)
      mStr = c0_string_tocstr(mC0Str);
    return mStr;
  }

  operator const char *() {
    return cstr();
  }

  operator c0_string () {
    if (!mC0Str)
      mC0Str = c0_string_fromcstr(mStr);
    return mC0Str;
  }
#ifdef QT_VERSION
  QString qstr() {
    return QString(cstr());
  }
  operator QString () { return qstr(); }
#endif

private:
  bool mFree;
  const char *mStr;
  c0_string mC0Str;
};

template <typename T>
class array : public gcobject {
public:
  array()
    : mArray(NULL)
  {}
  array(int count)
    : mArray(NULL)
  {
    initialize(count);
  }
  ~array() {
    // Clear this out so that a conservative GC will collect
    mArray = NULL;
  }

  void initialize(int count) {
    mArray = c0_array_alloc(sizeof (T), count);
  }

  T& operator [](int idx) {
    return *reinterpret_cast<T*>(c0_array_sub(mArray, idx, sizeof (T)));
  }

  operator c0_array *() { return mArray; }
private:
  c0_array *mArray;
};

// Template class which tracks whether or not the object has been explicitly
// destroyed.
template <typename T>
class safe {
public:
  safe() : mValid(true) {}
  virtual ~safe() {}

  // This method must be non-virtual so that it can be invoked on NULL pointers
  void validate() {
    if (!this || !mValid)
      c0_abort("Use of invalid object");
  }

  void destroy() {
    validate();
    mValid = false;
    // Because the destructor is virtual, this will invoke the destructors of
    // the subclass (presumably is class T).
    this->~safe();
  }
private:
  bool mValid;
};

}
#endif // __cplusplus
#endif // __C0RUNTIME_H__
