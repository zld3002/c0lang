#include <stdio.h>
#include <c0runtime.h>
#include "util.h"

void print(c0_string s) {
  const char *cstr = c0_string_tocstr(s);
  printf("%s", cstr);
  c0_string_freecstr(cstr);
}

void println(c0_string s) {
  const char *cstr = c0_string_tocstr(s);
  puts(cstr);
  c0_string_freecstr(cstr);
}

void printint(int i) {
  printf("%d", i);
}

void printbool(bool b) {
  puts(b ? "true" : "false");
}

void printchar(char c) {
  putchar(c);
}

c0_string readline() {
  return freadline(stdin);
}

void error(c0_string s) {
  const char *cstr = c0_string_tocstr(s);
  c0_abort(cstr);
  /* should be unnecessary, since c0_abort will exit: */
  c0_string_freecstr(cstr);
}