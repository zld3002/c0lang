#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdint.h>

typedef void*(*native_fn)(argsbuilder);
typedef void** argsbuilder;

argsbuilder args_create(int32_t argc) {
  if (argc == 0) return NULL;
  return malloc(sizeof (void *) * (size_t) argc);
}

void args_destroy(argsbuilder builder) {
  if (builder != NULL)
    free(builder);
}

/* Cast into the void */

void args_add_bool(argsbuilder builder, int32_t b, int32_t argn) {
  builder[argn] = (void *) (intptr_t) b; }

void args_add_char(argsbuilder builder, uint8_t c, int32_t argn) {
  builder[argn] = (void *) (intptr_t) c; }

void args_add_int(argsbuilder builder, uint32_t i, int32_t argn) {
  builder[argn] = (void *) (intptr_t) i; }

void args_add_ptr(argsbuilder builder, void *ptr, int32_t argn) {
  builder[argn] = ptr; }

/* Call, cast from the void */

int32_t call_bool(native_fn f, argsbuilder args) {
  return (int32_t) (intptr_t) (*f)(args); } 

uint32_t call_int(native_fn f, argsbuilder args) {
  return (uint32_t) (intptr_t) (*f)(args); }

uint8_t call_char(native_fn f, argsbuilder args) {
  return (uint8_t) (intptr_t) (*f)(args); } 

void *call_ptr(native_fn f, argsbuilder args) {
  return (*f)(args); }

void call_void(native_fn f, argsbuilder args) {
  (*f)(args); }




