#include <signal.h>
#include "cc0lib.h"

int _idiv (int x, int y) {
  return x/y;
}

int _imod (int x, int y) {
  return x%y;
}

int _sal (int x, int y) {
  return x << y;
}

int _sar (int x, int y) {
  return x >> y;
}

void _idiv_asn (int* px, int y) {
  *px /= y;
}

void _imod_asn (int* px, int y) {
  *px %= y;
}

void _sal_asn (int* px, int y) {
  *px <<= y;
}

void _sar_asn (int* px, int y) {
  *px >>= y;
}

void* _chk_null (void* A) {
  if (A == NULL) {
    fprintf(stderr, "attempt to dereference null pointer\n");
    fflush(stderr);
    raise(SIGSEGV);
  }
  return A;
}

