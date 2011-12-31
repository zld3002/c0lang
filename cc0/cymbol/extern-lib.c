#include <dlfcn.h>

void *lib_open(const char *path) {
  return dlopen(path, RTLD_LAZY);
}

