/* conio_c0ffi.c
 * This file automatically generated by the command 
 * 'wrappergen conio' - editing is probably bad.
 * 
 * The call to wrappergen was likely probably by 
 * 'make libs/conio', which in turn was likely
 * invoked by 'make libs'. */

#include <inttypes.h>
#include <c0runtime.h>

/* Headers */

void print(c0_string s);
void println(c0_string s);
void printint(int i);
void printbool(bool b);
void printchar(c0_char c);
void flush();
bool eof();
c0_string readline();

/* Wrappers */

void *__c0ffi_print(void **args) {
  print((c0_string) args[0]);
  return NULL;
}

void *__c0ffi_println(void **args) {
  println((c0_string) args[0]);
  return NULL;
}

void *__c0ffi_printint(void **args) {
  printint((int) (intptr_t) args[0]);
  return NULL;
}

void *__c0ffi_printbool(void **args) {
  printbool((bool) (intptr_t) args[0]);
  return NULL;
}

void *__c0ffi_printchar(void **args) {
  printchar((c0_char) (intptr_t) args[0]);
  return NULL;
}

void *__c0ffi_flush(void **args) {
  (void) args; /* suppress error */
  flush();
  return NULL;
}

void *__c0ffi_eof(void **args) {
  (void) args; /* suppress error */
  return (void *) (intptr_t) eof();
}

void *__c0ffi_readline(void **args) {
  (void) args; /* suppress error */
  return (void *) readline();
}

