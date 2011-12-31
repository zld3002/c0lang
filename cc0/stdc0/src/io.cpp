#include <stdio.h>
#include <QTextStream>
#include "io.h"

c0rt_string_t fromQString(const QString &s) {
  QByteArray bytes = s.toAscii();
  char *cstr = new char[bytes.length()+1];
  cstr[bytes.length()] = '\0';
  strncpy(cstr, bytes.constData(), bytes.length());
  c0rt_string_t c0str = c0rt_string_fromcstr(cstr);
  delete[] cstr;
  return c0str;
}

c0rt_string_t readfile(c0rt_string_t filename) {
  FILE *f = fopen(c0rt::AutoCStr(filename), "rt");

  // XXX: error check
  QTextStream stream (f, QIODevice::ReadOnly);
  QString contents = stream.readAll();

  fclose(f);

  return fromQString(contents);
}

void writefile(c0rt_string_t filename, c0rt_string_t contents) {
  FILE *f = fopen(c0rt::AutoCStr(filename), "wt");

  // XXX: error check

  fputs(c0rt::AutoCStr(contents), f);

  fclose(f);
}

struct file : public gc {
  QTextStream stream;

  file(FILE *f, QIODevice::OpenMode mode)
    : stream (f, mode)
  {
  }
};

file_t file_open(c0rt_string_t path) {
  FILE *f = fopen(c0rt::AutoCStr(path), "rt");

  // XXX: error check

  return new file(f, QIODevice::ReadOnly);
}

bool file_eof(file_t f) {
  return f->stream.atEnd();
}

c0rt_string_t file_readline(file_t f) {
  return fromQString(f->stream.readLine());
}

void file_close(file_t f);

void printint(int i) {
  QTextStream(stdout) << i;
}

void print(c0rt_string_t s) {
  QTextStream(stdout) << c0rt::AutoCStr(s).asQString();
}

void println(c0rt_string_t s) {
  puts(c0rt::AutoCStr(s));
}

void printchar(c0rt_char ch) {
  QTextStream(stdout) << ch;
}

c0rt_string_t readline() {
  return fromQString(QTextStream (stdin).readLine());
}
c0rt_string_t readchars(int n);
int readint() {
  int i;
  QTextStream(stdin) >> i;
  return i;
}

bool can_parse_int(c0rt_string_t s);
int parse_int(c0rt_string_t s);
