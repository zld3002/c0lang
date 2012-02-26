#ifndef __STDC0IO_H__
#define __STDC0IO_H__

#include "apidefs.h"

// Reads the contents of filename and returns it as a string
STDC0API c0rt_string_t readfile(c0rt_string_t filename);
// Writes contents to the file given by filename, creating the file if it
// doesn't exist.
STDC0API void writefile(c0rt_string_t filename, c0rt_string_t contents);

typedef struct file* file_t;

// Opens a file for reading
STDC0API file_t file_open(c0rt_string_t path);

// Returns true if the end of the file has been reached
STDC0API bool file_eof(file_t f);

// Reads a line from a file. Once the end of the file is reached, this will
// return empty strings.
STDC0API c0rt_string_t file_readline(file_t f);

// Closes a file. Once a file is closed, subsequent operations on it are
// undefined.
STDC0API void file_close(file_t f);

// Prints the integer to stdout, formatting as a decimal
STDC0API void printint(int i);
// Prints the string to stdout
STDC0API void print(c0rt_string_t s);
// Prints the string to stdout, adding a newline
STDC0API void println(c0rt_string_t s);
// Prints a single character to stdout
STDC0API void printchar(c0rt_char ch);

// Reads a line from stdin and strips the newline
STDC0API c0rt_string_t readline();
// Consumes up to n characters from stdin
STDC0API c0rt_string_t readchars(int n);
// Reads an integer from stdin. If the user does not enter an integer, it will
// prompt until one is provided.
STDC0API int readint();

// Converts an integer into a string using the given base to format
STDC0API c0rt_string_t int_to_string(int i, int base);
// Returns true if the string can be parsed into an integer
STDC0API bool can_parse_int(c0rt_string_t s);
// If can_parse_int(s), returns the integer denoted by s, otherwise the result
// is undefined.
STDC0API int parse_int(c0rt_string_t s);

#endif // __STDC0IO_H__

