/* string_c0ffi.c
 * This file automatically generated by the command 
 * 'wrappergen string' - editing is probably bad.
 * 
 * The call to wrappergen was likely probably by 
 * 'make libs/string', which in turn was likely
 * invoked by 'make libs'. */

#include <inttypes.h>
#include <c0runtime.h>

/* Headers */

int string_length(c0_string s);
c0_char string_charat(c0_string s, int idx);
c0_string string_join(c0_string a, c0_string b);
c0_string string_sub(c0_string a, int start, int end);
bool string_equal(c0_string a, c0_string b);
int string_compare(c0_string a, c0_string b);
c0_string string_fromint(int i);
c0_string string_frombool(bool b);
c0_string string_fromchar(c0_char c);
c0_string string_tolower(c0_string s);
bool string_terminated(c0_array * A, int n);
c0_array * string_to_chararray(c0_string s);
c0_string string_from_chararray(c0_array * A);
int char_ord(c0_char c);
c0_char char_chr(int n);

/* Wrappers */

c0_value __c0ffi_string_length(c0_value *args) {
  return int2val(string_length((c0_string)val2ptr(args[0])));
}

c0_value __c0ffi_string_charat(c0_value *args) {
  return int2val((c0_int)string_charat((c0_string)val2ptr(args[0]), val2int(args[1])));
}

c0_value __c0ffi_string_join(c0_value *args) {
  return ptr2val((void *)string_join((c0_string)val2ptr(args[0]), (c0_string)val2ptr(args[1])));
}

c0_value __c0ffi_string_sub(c0_value *args) {
  return ptr2val((void *)string_sub((c0_string)val2ptr(args[0]), val2int(args[1]), val2int(args[2])));
}

c0_value __c0ffi_string_equal(c0_value *args) {
  return int2val((c0_int)string_equal((c0_string)val2ptr(args[0]), (c0_string)val2ptr(args[1])));
}

c0_value __c0ffi_string_compare(c0_value *args) {
  return int2val(string_compare((c0_string)val2ptr(args[0]), (c0_string)val2ptr(args[1])));
}

c0_value __c0ffi_string_fromint(c0_value *args) {
  return ptr2val((void *)string_fromint(val2int(args[0])));
}

c0_value __c0ffi_string_frombool(c0_value *args) {
  return ptr2val((void *)string_frombool((bool)val2int(args[0])));
}

c0_value __c0ffi_string_fromchar(c0_value *args) {
  return ptr2val((void *)string_fromchar((c0_char)val2int(args[0])));
}

c0_value __c0ffi_string_tolower(c0_value *args) {
  return ptr2val((void *)string_tolower((c0_string)val2ptr(args[0])));
}

c0_value __c0ffi_string_terminated(c0_value *args) {
  return int2val((c0_int)string_terminated((c0_array *)val2ptr(args[0]), val2int(args[1])));
}

c0_value __c0ffi_string_to_chararray(c0_value *args) {
  return ptr2val((void *)string_to_chararray((c0_string)val2ptr(args[0])));
}

c0_value __c0ffi_string_from_chararray(c0_value *args) {
  return ptr2val((void *)string_from_chararray((c0_array *)val2ptr(args[0])));
}

c0_value __c0ffi_char_ord(c0_value *args) {
  return int2val(char_ord((c0_char)val2int(args[0])));
}

c0_value __c0ffi_char_chr(c0_value *args) {
  return int2val((c0_int)char_chr(val2int(args[0])));
}

