/* 15411_c0ffi.c
 * This file automatically generated by the command 
 * 'wrappergen 15411' - editing is probably bad.
 * 
 * The call to wrappergen was likely probably by 
 * 'make libs/15411', which in turn was likely
 * invoked by 'make libs'. */

#include <inttypes.h>
#include <c0runtime.h>
#include <stdio.h>

/* Headers */

int fadd(int x, int y);
int fsub(int x, int y);
int fmul(int x, int y);
int fdiv(int x, int y);
bool fless(int x, int y);
int itof(int n);
int ftoi(int x);
void print_fpt(int x);
void print_int(int n);
void print_hex(int n);

/* Wrappers */

c0_value __c0ffi_fadd(c0_value *args) {
   //fprintf(stderr, "Calling fadd\n");
  return int2val(fadd(val2int(args[0]), val2int(args[1])));
}

c0_value __c0ffi_fsub(c0_value *args) {
   //fprintf(stderr, "Calling fsub\n");
  return int2val(fsub(val2int(args[0]), val2int(args[1])));
}

c0_value __c0ffi_fmul(c0_value *args) {
   //fprintf(stderr, "Calling fmul\n");
  return int2val(fmul(val2int(args[0]), val2int(args[1])));
}

c0_value __c0ffi_fdiv(c0_value *args) {
   //fprintf(stderr, "Calling fdiv\n");
  return int2val(fdiv(val2int(args[0]), val2int(args[1])));
}

c0_value __c0ffi_fless(c0_value *args) {
   //fprintf(stderr, "Calling fless\n");
  return int2val((c0_int)fless(val2int(args[0]), val2int(args[1])));
}

c0_value __c0ffi_itof(c0_value *args) {
   //fprintf(stderr, "Calling itof\n");
  return int2val(itof(val2int(args[0])));
}

c0_value __c0ffi_ftoi(c0_value *args) {
   //fprintf(stderr, "Calling ftoi\n");
  return int2val(ftoi(val2int(args[0])));
}

c0_value __c0ffi_print_fpt(c0_value *args) {
   //fprintf(stderr, "Calling print_fpt\n");
  print_fpt(val2int(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_print_int(c0_value *args) {
   //fprintf(stderr, "Calling print_int\n");
  print_int(val2int(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_print_hex(c0_value *args) {
   //fprintf(stderr, "Calling print_hex\n");
  print_hex(val2int(args[0]));
  return ptr2val(NULL);
}

