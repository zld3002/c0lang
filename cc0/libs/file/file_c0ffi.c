/* file_c0ffi.c
 * This file automatically generated by the command 
 * 'wrappergen file' - editing is probably bad.
 * 
 * The call to wrappergen was likely probably by 
 * 'make libs/file', which in turn was likely
 * invoked by 'make libs'. */

#include <inttypes.h>
#include <c0runtime.h>
#include <stdio.h>

/* Headers */

struct file;
bool file_closed(struct file * f);
struct file * file_read(c0_string path);
void file_close(struct file * f);
bool file_eof(struct file * f);
c0_string file_readline(struct file * f);

/* Wrappers */

c0_value __c0ffi_file_closed(c0_value *args) {
   //fprintf(stderr, "Calling file_closed\n");
  return int2val((c0_int)file_closed((struct file *)val2ptr(args[0])));
}

c0_value __c0ffi_file_read(c0_value *args) {
   //fprintf(stderr, "Calling file_read\n");
  return ptr2val((void *)file_read((c0_string)val2ptr(args[0])));
}

c0_value __c0ffi_file_close(c0_value *args) {
   //fprintf(stderr, "Calling file_close\n");
  file_close((struct file *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_file_eof(c0_value *args) {
   //fprintf(stderr, "Calling file_eof\n");
  return int2val((c0_int)file_eof((struct file *)val2ptr(args[0])));
}

c0_value __c0ffi_file_readline(c0_value *args) {
   //fprintf(stderr, "Calling file_readline\n");
  return ptr2val((void *)file_readline((struct file *)val2ptr(args[0])));
}

