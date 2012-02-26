#include <c0runtime.h>

int sizeof_bool() { return sizeof(bool); }
int sizeof_int()  { return 4; }
int sizeof_char() { return sizeof(c0_char); }
int sizeof_ptr()  { return sizeof(void *); }
