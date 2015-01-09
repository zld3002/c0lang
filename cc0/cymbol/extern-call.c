#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdint.h>

// Interpreter FFI (from c0runtime.h)
enum c0_val_kind { C0_INTEGER, C0_POINTER };

typedef struct c0_value {
  enum c0_val_kind kind; 
  union {
    uint32_t i;
    void *p;
  } payload;
} c0_value;

static inline c0_value int2val(uint32_t i) {
  c0_value v;
  v.kind = C0_INTEGER;
  v.payload.i = i;
  return v;
}

static inline uint32_t val2int(c0_value v) {
  if (v.kind != C0_INTEGER ) c0_abort("Invalid cast from c0_value to integer");
  return v.payload.i;
}

static inline c0_value ptr2val(void *p) {
  c0_value v;
  v.kind = C0_POINTER;
  v.payload.p = p;
  return v;
}

static inline void *val2ptr(c0_value v) {
  if (v.kind != C0_POINTER) c0_abort("Invalid cast from c0_value to integer");
  return v.payload.p;
}

// Functions used by ML
typedef c0_value(*native_fn)(argsbuilder);
typedef c0_value* argsbuilder;

argsbuilder args_create(int32_t argc) {
  //printf("args_create (c)\n");
  if (argc == 0) return NULL;
  return malloc(sizeof (c0_value) * (size_t) argc);
}

void args_destroy(argsbuilder builder) {
  //printf("args_destroy (c)\n");
  if (builder != NULL)
    free(builder);
}

/* Cast into the void */

void args_add_bool(argsbuilder builder, int32_t b, int32_t argn) {
  //printf("args_add_bool (c)\n");
  builder[argn] = int2val(b); }

void args_add_char(argsbuilder builder, uint8_t c, int32_t argn) {
  //printf("args_add_char (c)\n");
  builder[argn] = int2val(c); }

void args_add_int(argsbuilder builder, uint32_t i, int32_t argn) {
  //printf("args_add_int (c)\n");
  builder[argn] = int2val(i); }

void args_add_ptr(argsbuilder builder, void *ptr, int32_t argn) {
  //printf("args_add_ptr (c)\n");
  builder[argn] = ptr2val(ptr); }

/* Cast from the void */

int32_t cast_bool(c0_value* x) {
  //printf("cast_bool (c)\n");
  int32_t b = val2int(*x);
  free(x);
  return b;
} 

uint32_t cast_int(c0_value* x) {
  //printf("cast_int (c)\n");
  uint32_t i = val2int(*x);
  free(x);
  return i; }

uint8_t cast_char(c0_value* x) {
  //printf("cast_char (c)\n");
  uint8_t c = val2int(*x);
  free(x);
  return c; } 

void* cast_ptr(c0_value* x) {
  void* p = val2ptr(*x);
  free(x);
  return p; }

/* Call out to the void */

void *apply(native_fn f, argsbuilder args) {
  //printf("apply (c)\n");
  c0_value* ret = malloc(sizeof(c0_value));
  *ret = (*f)(args);
  return ret;
}




