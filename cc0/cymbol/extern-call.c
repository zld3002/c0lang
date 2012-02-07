#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdint.h>

typedef void*(*native_fn)(argsbuilder);
typedef void** argsbuilder;

argsbuilder args_create(int32_t argc) {
  //printf("args_create (c)\n");
  if (argc == 0) return NULL;
  return malloc(sizeof (void *) * (size_t) argc);
}

void args_destroy(argsbuilder builder) {
  //printf("args_destroy (c)\n");
  if (builder != NULL)
    free(builder);
}

/* Cast into the void */

void args_add_bool(argsbuilder builder, int32_t b, int32_t argn) {
  //printf("args_add_bool (c)\n");
  builder[argn] = (void *) (intptr_t) b; }

void args_add_char(argsbuilder builder, uint8_t c, int32_t argn) {
  //printf("args_add_char (c)\n");
  builder[argn] = (void *) (intptr_t) c; }

void args_add_int(argsbuilder builder, uint32_t i, int32_t argn) {
  //printf("args_add_int (c)\n");
  builder[argn] = (void *) (intptr_t) i; }

void args_add_ptr(argsbuilder builder, void *ptr, int32_t argn) {
  //printf("args_add_ptr (c)\n");
  builder[argn] = ptr; }

/* Cast from the void */

int32_t cast_bool(void* x) {
  //printf("cast_bool (c)\n");
  return (int32_t) (intptr_t) x; } 

uint32_t cast_int(void* x) {
  //printf("cast_int (c)\n");
  return (uint32_t) (intptr_t) x; }

uint8_t cast_char(void* x) {
  //printf("cast_char (c)\n");
  return (uint8_t) (intptr_t) x; } 

/* Call out to the void */

void *apply(native_fn f, argsbuilder args) {
  //printf("apply (c)\n");
  return (*f)(args);
}




