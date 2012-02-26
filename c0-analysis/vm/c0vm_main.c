/* C0VM, main file
 * 15-122, Fall 2010
 * William Lovas, Tom Cortina, Frank Pfenning
 *
 * Performs some OS compatibility checks before
 * running the VM.
 */

#include "c0vm.h"
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include "c0runtime.h"

/* for the args library */
int c0_argc;
char **c0_argv;

/* fail-fast file function wrappers */
FILE *xfopen(const char *filename, const char *mode,
	     char *error) {
  FILE *f = fopen(filename, mode);
  if (f == NULL) {
    perror(error);
    exit(1);
  }
  return f;
}

void xfwrite(const void *ptr, size_t size, size_t nitems, FILE *stream,
	     char *error) {
  if (fwrite(ptr, size, nitems, stream) < nitems) {
    perror(error);
    exit(1);
  }
}

void xfclose(FILE *stream, char *error) {
  if (fclose(stream) != 0) {
    perror(error);
    exit(1);
  }
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s <bc0_file> [args...]\n", argv[0]);
    exit(1);
  }

  /* test for two's complement */
  if (~(-1) != 0) {
    fprintf(stderr, "Error: not a two's complement machine\n");
    exit(1);
  }

  /* test representation sizes */
  if (sizeof(int) != 4) {
    fprintf(stderr, "Error: sizeof(int) == %zd != 4\n", sizeof(int));
    exit(1);
  }

  if (sizeof(char) != 1) {
    fprintf(stderr, "Error: sizeof(char) == %zd != 1\n", sizeof(char));
    exit(1);
  }    

  if (sizeof(void*) != 4 && sizeof(void*) != 8) {
    fprintf(stderr, "Error: sizeof(void*) == %zd != 4 or 8\n", sizeof(void*));
    exit(1);
  }

  /* test of sign-extending shift */
  if ((int)(-1) >> 31 != -1) {
    fprintf(stderr, "Error: right shift does not sign-extend\n");
    exit(1);
  }

  /* test that casting preserves identity for a few crucial values */
  if ( INT(VAL(INT_MIN)) != INT_MIN
    || INT(VAL(INT_MAX)) != INT_MAX
    || INT(VAL(-1)) != -1
    || INT(VAL(0)) != 0
    || INT(VAL(1)) != 1 ) {
    fprintf(stderr, "Error: casting between int and void* loses information\n");
    exit(1);
  }

  /* for the args library -- skip the binary name */
  c0_argc = argc - 1;
  c0_argv = argv + 1;

  char *filename = getenv("C0_RESULT_FILE");

  /* initialize the runtime -- possibly initializing the GC */
  c0_runtime_init();

  struct bc0_file *bc0 = read_program(argv[1]);

  if (bc0->magic != (int)0xc0c0ffee) {
    fprintf(stderr, "Error: incorrect magic number, expected 0xc0c0ffee\n");
    exit(1);
  }

  int arch_wsize = 8*sizeof(void*);
  
  int arch_bit = (arch_wsize == 32) ? 0 : 1;

  if (bc0->version != ((BC0_VERSION << 1) | arch_bit)) {
    fprintf(stderr, "Error: bytecode file version %d (%d bits), c0vm version %d (%d bits)\n",
	    bc0->version >> 1, ((bc0->version & 1) == 0 || bc0->version == 1) ? 32 : 64,
	    BC0_VERSION, arch_wsize);
    exit(1);
  }

  if (filename == NULL) {
    int result = execute(bc0);
    printf("Result = %d\n", result);
  } else {
    FILE *f = xfopen(filename, "w", "Couldn't open $C0_RESULT_FILE");
    xfwrite("\0", 1, 1, f, "Couldn't write to $C0_RESULT_FILE");
    int result = execute(bc0);
    printf("Result = %d\n", result);
    xfwrite(&result, sizeof(int), 1, f, "Couldn't write to $C0_RESULT_FILE");
    xfclose(f, "Couldn't close $C0_RESULT_FILE");
  }

  free_program(bc0);
  return 0;
}
