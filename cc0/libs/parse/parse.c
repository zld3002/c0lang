#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <limits.h>
#include <ctype.h>
#include <c0runtime.h>

bool *parse_bool(c0_string s) {
  bool *result = NULL;
  const char *cstr = c0_string_tocstr(s);
  if (0 == strcmp(cstr, "true")) {
    result = c0_alloc(sizeof(bool));
    *result = true;
  } else if (0 == strcmp(cstr, "false")) {
    result = c0_alloc(sizeof(bool));
    *result = false;
  }
  c0_string_freecstr(cstr);
  return result;
}

int *parse_int(c0_string s, int base) {
  int *result = NULL;

  if (base < 2 || base > 36) c0_abort("parse_int: invalid base");

  const char *cstr = c0_string_tocstr(s);
  errno = 0;
  char *endptr;
  long int li = strtol(cstr, &endptr, base);

  // If the upper 4 bytes are 0, then we should sign extend
  // the number
  if ((li >> 32) == 0) {
    li = (li << 32) >> 32;
  }

  if (!isspace(cstr[0]) && cstr[0] != '+' /* strtol allows leading space or +, we don't -wjl */
      && errno == 0 && li >= INT_MIN && li <= INT_MAX && endptr != cstr
      && *endptr == '\0' /* make sure whole string was valid -wjl */) {
    result = c0_alloc(sizeof(int));
    *result = li;
  }
  c0_string_freecstr(cstr);
  return result;
}

unsigned int count_tokens(const char *s) {
  unsigned int tokens = 0;

  while (true) {
    // Advance past leading whitespace
    while (isspace(*s)) {
      s++;
    }

    // Return if end of string reached
    if (*s == '\0') { 
      return tokens; 
    }

    // Advance past token
    tokens++;
    while (!isspace(*s) && *s != '\0') { 
      s++; 
    }
  }
}

int num_tokens(c0_string s) {
  const char *str = c0_string_tocstr(s);
  int i = (int)count_tokens(str);
  c0_string_freecstr(str);
  return i;
}

c0_array internal_parse_tokens(const char *s) {
  char strs[strlen(s)+1];
  strcpy(strs, s);
  char *start = strs;
  char *end = strs;

  unsigned int len = count_tokens(s);
  c0_array A = c0_array_alloc(sizeof(c0_string), len);

  // Turn the stack-allocated string copy into a series of strings
  unsigned int i;
  for (i = 0; i < len; i++) {
    // Advance past leading whitespace
    while (isspace(*start)) { start++; }

    // Advance past token;
    end = start;
    while (!isspace(*end) && *end != '\0') {
      end++;
    }

    // Record string in array
    *end = '\0';
    c0_string *arraypos = c0_array_sub(A, i, sizeof(c0_string));
    *arraypos = c0_string_fromcstr(start);
    start = end + 1;
  }
  
  return A;
}

c0_array parse_tokens(c0_string s) {
  const char *str = c0_string_tocstr(s);
  c0_array A = internal_parse_tokens(str);
  c0_string_freecstr(str);
  return A;
}

// XXX efficiency
bool int_tokens(c0_string s, int base) {
  if (base < 2 || base > 36) c0_abort("int_tokens: invalid base");

  int len = num_tokens(s);
  c0_array A = parse_tokens(s);

  int i;
  for (i = 0; i < len; i++) {
    c0_string *arraypos = c0_array_sub(A, i, sizeof(c0_string));
    if (parse_int(*arraypos, base) == NULL) return false;
  }

  return true;
}

// Does 3 passes through the string, but is significantly less
// error-prone and makes the library a lot more consistent
c0_array parse_ints(c0_string s, int base) {
  if (base < 2 || base > 36) c0_abort("parse_ints: invalid base");

  int len = num_tokens(s);
  c0_array tokens = parse_tokens(s);
  c0_array A = c0_array_alloc(sizeof(int), len);

  for (int i = 0; i < len; i++) {
    c0_string token = *(c0_string*)c0_array_sub(tokens, i, sizeof(c0_string));
    int* num = parse_int(token, base);

    if (num == NULL) {
      c0_abort("parse_ints: invalid number");
    }

    *(int*)c0_array_sub(A, i, sizeof(int)) = *num;
  }

  return A;
}
