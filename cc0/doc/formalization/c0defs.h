// Defines bool, true, and false
#include <stdbool.h>

typedef const char *string;

#define alloc(ty) ((ty*)calloc(1, sizeof (ty)))
#define alloc_array(ty, size) ((ty*)calloc(size, sizeof (ty)))
