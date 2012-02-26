#include <stdio.h>
#include <c0runtime.h>
#include "util.h"

struct file : public c0::gcobject, public c0::safe<file> {
  FILE *handle;

  ~file() {
    fclose(handle);
  }
};

C0API file *file_read(c0_string path) {
  c0::string cpath(path);
  file *f = new file;
  f->handle = fopen(cpath, "r");
  /* could be NULL */

  if (!f->handle) {
    /* free f? */
    return NULL;
  }

  return f;
}

C0API void file_close(file *f) {
  f->destroy();
}

C0API bool file_eof(file *f) {
  f->validate();
  if (EOF == fgetc(f->handle))
    return true;
  fseek(f->handle, -1, SEEK_CUR);
  return false;
}

C0API c0_string file_readline(file *f) {
  f->validate();
  if (file_eof(f))
    c0_abort("Cannot read more lines - at end of file");
  // From util.h in the conio library
  return freadline(f->handle);
}
