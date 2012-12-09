#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include "c0rt.h"

void c0_error(const char *msg) {
  fprintf(stderr, "Error: %s\n", msg);
  fflush(stderr);
  exit(EXIT_FAILURE);
}

void c0_abort(const char *reason) {
  fprintf(stderr, "%s\n", reason);
  fflush(stderr);
  abort();
}

void c0_abort_mem(const char *reason) {
  fprintf(stderr, "%s\n", reason);
  fflush(stderr);
  raise(SIGSEGV);
}
