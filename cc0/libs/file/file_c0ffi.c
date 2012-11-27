/* file_c0ffi.c
 * This file automatically generated by the command 
 * 'wrappergen file' - editing is probably bad.
 * 
 * The call to wrappergen was likely probably by 
 * 'make libs/file', which in turn was likely
 * invoked by 'make libs'. */

#include <inttypes.h>
#include <c0runtime.h>

/* Headers */

struct file;
typedef struct file * file_t;
file_t file_read(c0_string path);
bool file_closed(file_t f);
void file_close(file_t f);
bool file_eof(file_t f);
c0_string file_readline(file_t f);

/* Wrappers */

void *__c0ffi_file_read(void **args) {
  return (void *) file_read((c0_string) args[0]);
}

void *__c0ffi_file_closed(void **args) {
  return (void *) (intptr_t) file_closed((file_t) args[0]);
}

void *__c0ffi_file_close(void **args) {
  file_close((file_t) args[0]);
  return NULL;
}

void *__c0ffi_file_eof(void **args) {
  return (void *) (intptr_t) file_eof((file_t) args[0]);
}

void *__c0ffi_file_readline(void **args) {
  return (void *) file_readline((file_t) args[0]);
}

