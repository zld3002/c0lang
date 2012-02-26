/* C0VM, reading a bytecode file
 * File is ASCII coded so it can be read and edited,
 * if necessary
 */

#include <stdbool.h>
#include "file.h0"
#include "parse.h0"
#include "readfile.h"
#include "xalloc.h"
#include "contracts.h"
#include "c0vm.h"
#include <assert.h>
#include <stdlib.h>

int theint(string s) {
  int* pint = parse_int(s,16);
  if (pint == NULL) {
    fprintf(stderr, "Illegal file format: \"%s\" is not a hexadecimal integer\n", s);
    abort();
  }
  int res = *pint;
  free(pint);
  return res;
}

int read_i32(char** s, int i, int length)
{
  assert(i + 4 <= length);
  int sum = 0;
  for (int j = i; j < i+4; j++) {
    sum = (sum<<8) | theint(s[j]);
  }
  return sum;
}

int read_i16(char** s, int i, int length)
{
  assert(i + 2 <= length);
  int sum = 0;
  for (int j = i; j < i+2; j++) {
    sum = (sum<<8) | theint(s[j]);
  }
  return sum;

}

ubyte read_i8(char** s, int i, int length)
{
  assert(i + 1 <= length);
  return (ubyte) theint(s[i]);
}

struct bc0_file* read_program(string filename)
{
  string_bundle sb = read_words(filename);
  char** sb_array = string_bundle_array(sb);
  int sb_array_length = string_bundle_length(sb);

  struct bc0_file* bc0 = xmalloc(sizeof(struct bc0_file));
  int i = 0;   /* index into bc0_file byte position */

  bc0->magic = read_i32(sb_array, i, sb_array_length);
  i += 4;
  bc0->version = read_i16(sb_array, i, sb_array_length);
  i += 2;

  bc0->int_pool_count = read_i16(sb_array, i, sb_array_length);
  i += 2;

  bc0->int_pool = xcalloc(bc0->int_pool_count, sizeof(int));
  for (int j = 0; j < bc0->int_pool_count; j++) {
    bc0->int_pool[j] = read_i32(sb_array, i, sb_array_length);
    i += 4;
  }

  bc0->string_pool_count = read_i16(sb_array, i, sb_array_length);
  i += 2;
  bc0->string_pool = xcalloc(bc0->string_pool_count, sizeof(char));
  for (int j = 0; j < bc0->string_pool_count; j++) {
    bc0->string_pool[j] = (char) read_i8(sb_array, i, sb_array_length);
    i++;
  }

  bc0->function_count = read_i16(sb_array, i, sb_array_length);
  i += 2;
  bc0->function_pool = xcalloc(bc0->function_count, sizeof(struct function_info));
  for (int j = 0; j < bc0->function_count; j++) {
    bc0->function_pool[j].num_args = read_i16(sb_array, i, sb_array_length);
    i += 2;
    bc0->function_pool[j].num_vars = read_i16(sb_array, i, sb_array_length);
    i += 2;
    bc0->function_pool[j].code_length = read_i16(sb_array, i, sb_array_length);
    i += 2;
    bc0->function_pool[j].code = xcalloc(bc0->function_pool[j].code_length, sizeof(ubyte));
    for (int k = 0; k < bc0->function_pool[j].code_length; k++) {
      bc0->function_pool[j].code[k] = read_i8(sb_array, i, sb_array_length);
      i++;
    }
  }

  bc0->native_count = read_i16(sb_array, i, sb_array_length);
  i += 2;
  bc0->native_pool = xcalloc(bc0->native_count, sizeof(struct native_info));
  for (int j = 0; j < bc0->native_count; j++) {
    bc0->native_pool[j].num_args = read_i16(sb_array, i, sb_array_length);
    i += 2;
    bc0->native_pool[j].function_table_index = read_i16(sb_array, i, sb_array_length);
    i += 2;
  }

  /* free bundle and all contained strings */
  string_bundle_free(sb, free);

  return bc0;
}

void free_program(struct bc0_file *program)
{
  free(program->int_pool);
  free(program->string_pool);

  for (int j = 0; j < program->function_count; j++)
    free(program->function_pool[j].code);
  free(program->function_pool);

  free(program->native_pool);
  free(program);
}
