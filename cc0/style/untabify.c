#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

int main (int argc, char **argv) {
  int tabstop;
  if (argc == 1) tabstop = 8;   /* default tab stop 8 */
  else tabstop = atoi(argv[1]); /* or command line argument */
  if (argc > 2 || tabstop <= 1) {
    fprintf(stderr, "usage: untabify [n] < infile > outfile\n");
    fprintf(stderr, "where 'n' is the tab stop count (default: 8)\n");
    exit(1);
  }
  int max_col = 80;
  int line = 1;
  int col = 1;
  int tabs = 0;
  bool midline = false;
  char c = getchar();
  while (c != EOF) {
    switch (c) {
    case '\n':
      if (col > max_col) {
        if (midline) fprintf(stderr, "\n");
        fprintf(stderr, "warning: line %d too long\n%d > %d characters\n",
                line, col, max_col);
        midline = false;
      }
      putchar(c); line++; col = 1;
      break;
    case '\t':
      tabs++;
      // fprintf(stderr, "."); fflush(stderr); midline = true;
      putchar(' '); col++;
      while (col % tabstop != 1) {
        putchar(' '); col++;
      }
      break;
    default: 
      putchar(c); col++;
    }
    c = getchar();
  }
  if (midline) fprintf(stderr, "\n");
  if (tabs > 0) {
    fprintf(stderr, "replaced %d tab characters\n", tabs);
    exit(0);
  } else {
    fprintf(stderr, "no tabs found\n");
    exit(1);
  }
  /* unreachable */
  return 0;
}
