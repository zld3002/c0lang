#include <c0runtime.h>
#include <stdio.h>
#include <stdlib.h>

typedef int c0_float;

union float_or_int {
  int as_int;
  float as_float;
};

typedef union float_or_int float_or_int;

c0_float fadd(c0_float a, c0_float b) {
  float_or_int x; x.as_int = a;
  float_or_int y; y.as_int = b;
  float_or_int z; z.as_float = x.as_float + y.as_float;
  return z.as_int;
}

c0_float fsub(c0_float a, c0_float b) {
  float_or_int x; x.as_int = a;
  float_or_int y; y.as_int = b;
  float_or_int z; z.as_float = x.as_float - y.as_float;
  return z.as_int;
}

c0_float fmul(c0_float a, c0_float b) {
  float_or_int x; x.as_int = a;
  float_or_int y; y.as_int = b;
  float_or_int z; z.as_float = x.as_float * y.as_float;
  return z.as_int;
}

c0_float fdiv(c0_float a, c0_float b) {
  float_or_int x; x.as_int = a;
  float_or_int y; y.as_int = b;
  float_or_int z; z.as_float = x.as_float / y.as_float;
  return z.as_int;
}

bool fless(c0_float a, c0_float b) {
  float_or_int x; x.as_int = a;
  float_or_int y; y.as_int = b;
  return x.as_float < y.as_float;
}

c0_float itof(int a) {
  float_or_int x; x.as_float = (float)a;
  return x.as_int;
}

int ftoi(c0_float a) {
  float_or_int x; x.as_int = a;
  return (int)x.as_float;
}

int print_fpt(c0_float a) {
  float_or_int x; x.as_int = a;
  fprintf(stderr, "%g\n", x.as_float);
  return 0;
}

typedef struct dub *c0_double;

union double_or_ptr {
  struct dub *as_ptr;
  double as_double;
};

typedef union double_or_ptr double_or_ptr;

c0_double dadd(c0_double a, c0_double b) {
  double_or_ptr x; x.as_ptr = a;
  double_or_ptr y; y.as_ptr = b;
  double_or_ptr z; z.as_double = x.as_double + y.as_double;
  return z.as_ptr;
}

c0_double dsub(c0_double a, c0_double b) {
  double_or_ptr x; x.as_ptr = a;
  double_or_ptr y; y.as_ptr = b;
  double_or_ptr z; z.as_double = x.as_double - y.as_double;
  return z.as_ptr;
}

c0_double dmul(c0_double a, c0_double b) {
  double_or_ptr x; x.as_ptr = a;
  double_or_ptr y; y.as_ptr = b;
  double_or_ptr z; z.as_double = x.as_double * y.as_double;
  return z.as_ptr;
}

c0_double ddiv(c0_double a, c0_double b) {
  double_or_ptr x; x.as_ptr = a;
  double_or_ptr y; y.as_ptr = b;
  double_or_ptr z; z.as_double = x.as_double / y.as_double;
  return z.as_ptr;
}

bool dless(c0_double a, c0_double b) {
  double_or_ptr x; x.as_ptr = a;
  double_or_ptr y; y.as_ptr = b;
  return x.as_double < y.as_double;
}

c0_double itod(int a) {
  double_or_ptr x; x.as_double = (float)a;
  return x.as_ptr;
}

int dtoi(c0_double a) {
  double_or_ptr x; x.as_ptr = a;
  return (int)x.as_double;
}

int print_dub(c0_double a) {
  double_or_ptr x; x.as_ptr = a;
  fprintf(stderr, "%g\n", x.as_double);
  return 0;
}

int print_int(int n) {
  fprintf(stderr, "%d\n", n);
  return 0;
}

int print_hex(int n) {
  fprintf(stderr, "0x%08X\n", n);
  return 0;
}
