#include <stdio.h>
#include <c0runtime.h>
#include <assert.h>
#include "util.h"

struct file {
  FILE *handle;
};

typedef struct file* file_t;

file_t file_read(c0_string path) {
  const char* filename = c0_string_tocstr(path);
  file_t f = c0_alloc(sizeof(struct file));
  f->handle = fopen(filename, "r");
  if (!f->handle) return NULL;
  return f;
}

void file_close(file_t f) {
  assert(f != NULL);
  if (f->handle == NULL) 
    c0_abort("file_close: file already closed");
  if (EOF == fclose(f->handle)) {
    c0_abort("Could not close file");
  }
  f->handle = NULL;
  return;
}

bool file_eof(file_t f) {
  assert(f != NULL);
  if (f->handle == NULL) 
    c0_abort("file_eof: file is closed");
  if (EOF == fgetc(f->handle)) {
    return true;
  }
  fseek(f->handle, -1, SEEK_CUR);
  return false;
}

c0_string file_readline(file_t f) {
  assert(f != NULL);
  if (f->handle == NULL) 
    c0_abort("file_readline: file is closed");
  if (feof(f->handle) || file_eof(f)) {
    c0_abort("Cannot read more lines - already at end of file");
  }
  // From util.h in the conio library
  return freadline(f->handle);
}
