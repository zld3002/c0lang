#include <string.h>
#include "bare.h"

c0_string c0_string_empty() {
  return "";
}

int c0_string_length(c0_string s) {
  return s ? strlen(s) : 0;
}

c0_char c0_string_charat(c0_string s, int i) {
  int len = c0_string_length(s);
  if (!(0 <= i && i < len)) c0_abort("c0_string_charat: index out of bounds");
  return s[i];
}

c0_string c0_string_sub(c0_string s, int a, int b) {
  if (0 > a) c0_abort("c0_string_sub: 0 > start");
  if (a > b) c0_abort("c0_string_sub: start > end");

  if (!s) {
    if (b > 0)
      c0_abort("c0_string_sub: end > length of string");
    else
      return "";
  }

  size_t len = strlen(s);
  if (b > len)
    c0_abort("c0_string_sub: end > length of string");
    /* b = len; */

  // Note, implicitly checks that a < len
  /* if (a < 0 || b <= a) */

  /* since a < b and b <= len, a <= len */
  if (a == b)
    return "";

  size_t sublen = b - a;
  char *sub = c0_alloc(sublen+1);
  *sub = '\0';
  strncat(sub, s+a, sublen);
  return sub;
}

c0_string c0_string_join(c0_string a, c0_string b) {
  if (!a)
    return b;
  if (!b)
    return a;

  char *c = c0_alloc(strlen(a) + strlen(b) + 1);
  strcpy(c, a);
  strcat(c, b);
  return c;
}

c0_string c0_string_fromcstr(const char *s) {
  return strdup(s);
}

const char *c0_string_tocstr(c0_string s) {
  return s ? s : "";
}

void c0_string_freecstr(const char *s) {
}

c0_string c0_string_fromliteral(const char *s) {
  return s;
}

bool c0_string_equal(c0_string a, c0_string b) {
  return 0 == c0_string_compare(a,b);
}

int c0_string_compare(c0_string a, c0_string b) {
  a = a ? a : "";
  b = b ? b : "";
  int res = strcmp(a,b);
  return (res < 0) ? -1 : ((res > 0) ? 1 : 0);
}

bool c0_char_equal(c0_char a, c0_char b) {
  return a == b;
}

int c0_char_compare(c0_char a, c0_char b) {
  return a - b;
}
