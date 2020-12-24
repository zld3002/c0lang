#define _GNU_SOURCE

#include <stdlib.h>
#include <stdio.h>
#include <signal.h>
#include <stdnoreturn.h>
#include <assert.h>
#include <string.h> 
#include <strings.h> // bzero 
#include <limits.h>
#include <errno.h>
#include <gc.h>
#include <c0runtime.h>

#include "backtrace.h"

// Terminal color codes
#define ANSI_BOLD "\x1b[1m"
#define ANSI_BOLDRED ANSI_BOLD "\x1b[31m"
#define ANSI_BOLDBLUE ANSI_BOLD "\x1b[34m"
#define ANSI_RESET "\x1b[0m"

// Variables which can be set to "" to disable
// color printing
static const char* ansi_bold = ANSI_BOLD;
static const char* ansi_bold_red = ANSI_BOLDRED;
static const char* ansi_bold_blue = ANSI_BOLDBLUE;
static const char* ansi_reset = ANSI_RESET;

#define print_err(msg, ...) fprintf(stderr, "%sc0rt: " msg "%s" "\n", ansi_bold_red, ## __VA_ARGS__, ansi_reset)

// Environment variable names for configuration
#define C0_BACKTRACE_LIMIT_ENV "C0_BACKTRACE_LIMIT"
#define C0_MAX_ARRAYSIZE_ENV "C0_MAX_ARRAYSIZE"
#define C0_ENABLE_FANCY_OUTPUT "C0_ENABLE_FANCY_OUTPUT"

// Default backtrace print limit
static long c0_backtrace_print_limit = 20;
// Default maximum array size in bytes (includes metadata)
static long c0_max_arraysize = 1 << 30; // 1 GB

// Whether to use colors and to print backtraces or not.
// (0 = disabled, nonzero = enabled)
static long c0_enable_fancy_output = true;

static const char* prog_name = NULL;
static const char** sourcemap = NULL;
static long sourcemap_length = 0;

/**
 * Sets "out" to the environment variable "name".
 * 
 * If the environment variable does not exist, then
 * nothing happens.
 * 
 * If the environment variable is not an integer, then
 * a message is printed + program exits
 */
static void parse_env_with_default(const char* name, long* out) {
  const char* str = getenv(name);
  if (str == NULL) return;

  errno = 0;
  char* end;
  long result = strtol(str, &end, 10); 
  // None of our config options can be negative
  if (end == str || *end != '\0' || errno == ERANGE || result < 0) {
    print_err("invalid value '%s' for '%s'", str, name);
    return;
  }
  *out = result;
}

static noreturn void raise_msg(int signal, const char* msg);

#define SIG_STACK_SIZE (4 * SIGSTKSZ)
char signal_stack[SIG_STACK_SIZE] = { 0 };

void segv_handler(int signal) {
  // NULL pointer dereferences/array accesses
  // are handled by special functions, so the only
  // SIGSEGV we should ever receive is from
  // a bug in a library/runtime (hopefully unlikely)
  // or from a stack overflow (more likely)
  //
  // It's technically not safe to call raise_msg
  // inside a signal handler since it calls
  // printf and some other non-reentrant functions
  // but that's a chance I'm willing to take
  raise_msg(SIGSEGV, "recursion limit exceeded");
}

void c0_runtime_init(const char* filename, const char** source_map, long map_length) {
  GC_INIT();

  parse_env_with_default(C0_BACKTRACE_LIMIT_ENV, &c0_backtrace_print_limit);
  parse_env_with_default(C0_MAX_ARRAYSIZE_ENV, &c0_max_arraysize);
  parse_env_with_default(C0_ENABLE_FANCY_OUTPUT, &c0_enable_fancy_output);

  // Disable color printing if backtraces are disabled, in order to 
  // support environments like Autolab
  if (!c0_enable_fancy_output) {
    ansi_bold = "";
    ansi_bold_red = "";
    ansi_bold_blue = "";
    ansi_reset = "";    
  }

  // Save source map information
  prog_name = filename;
  sourcemap = source_map; 
  sourcemap_length = map_length;

  // Set up a separate stack for SIGSEGV
  // (obviously we can't reuse the main stack if a stack overflow happens)
  stack_t signal_stack_desc = {
    .ss_flags = 0,
    .ss_size = SIG_STACK_SIZE,
    .ss_sp = signal_stack
  };

  assert(sigaltstack(&signal_stack_desc, NULL) >= 0);

  struct sigaction segv_action = {
    .sa_flags = SA_ONSTACK,
    .sa_handler = segv_handler,
  };

  assert(sigfillset(&segv_action.sa_mask) >= 0);
  assert(sigaction(SIGSEGV, &segv_action, NULL) >= 0);
}

void c0_runtime_cleanup() {
  // nothing to do for the c0rt runtime
}

#define C0_EXTENSION ".c0.c"
#define C1_EXTENSION ".c1.c"
#define C0_EXTENSION_SIZE (sizeof(C0_EXTENSION) - 1)

// Check if a file is the generated .c0.c or .c1.c file
static bool from_user_program(const char* filename) {
  size_t n = strlen(filename);

  const char* extension_start = filename + n - C0_EXTENSION_SIZE;
  return strcmp(extension_start, C0_EXTENSION) == 0
      || strcmp(extension_start, C1_EXTENSION) == 0;
}

#define C0_FUNC_MANGLE_PREFIX "_c0_"
#define C0_FUNC_MANGLE_PREFIX_SIZE (sizeof(C0_FUNC_MANGLE_PREFIX) - 1)

// "Demangle" a C0 function name
static const char* demangle(const char* funcname) {
  size_t n = strlen(funcname);

  if (n < C0_FUNC_MANGLE_PREFIX_SIZE) {
    // Technically shouldn't happen, but better to just print out the
    // fault name instead of crashing
    return funcname;
  }

  return funcname + C0_FUNC_MANGLE_PREFIX_SIZE;
}

/**
 * Called by libbacktrace for every stack frame.
 * 
 * @param backtrace_count The number of frames counted so far
 * @param pc %rip 
 * 
 * @returns -1 to stop backtrace, 0 to continue
 */
int backtrace_callback(
  int* backtrace_count, uintptr_t pc, 
  const char* filename, int lineno, const char* function) 
{
  if (*backtrace_count > c0_backtrace_print_limit) {
    print_err("stoppping after %ld entries", c0_backtrace_print_limit);
    print_err("adjust C0_BACKTRACE_LIMIT to increase this limit");
    return -1;
  }

  if (filename == NULL || !from_user_program(filename)) {
    // Frame is not from the C0 program.
    // Could be from the runtime, a library function,
    // or the C runtime.
    // Skip it
    return 0;
  }

  if (lineno >= sourcemap_length) {
    // This shouldn't happen
    printf(" at %s (%s: %d)", function, filename, lineno);
    return 0;
  }

  const char* c0_location = sourcemap[lineno];
  if (c0_location == NULL) c0_location = "<unknown location>";

  printf(" at %s (%s)\n", demangle(function), c0_location);
  
  (*backtrace_count)++;

  return 0;
}

void backtrace_error_handler(void* data, const char* msg, int errnum) {
  (void)data;
  (void)errnum;

  print_err("couldn't print backtrace: %s", msg);
}

void c0_print_callstack() {
  struct backtrace_state* state = 
    backtrace_create_state(
      prog_name, // Executable name to load symbols from
      false, // Disable multithreading support
      backtrace_error_handler, 
      NULL); // data parameter to error callback

  assert(state != NULL);

  // Keep track of the number of backtrace entries printed
  int num_printed = 0;
  backtrace_full(
    state,  
    0, // Number of stack frames to skip
    (backtrace_full_callback)backtrace_callback, backtrace_error_handler, 
    &num_printed); // first parameter to callbacks
}

noreturn void c0_abort_mem(const char* msg);

static void reset_sigsegv_handler(void) {
  struct sigaction default_action = {
    .sa_flags = 0,
    .sa_handler = SIG_DFL
  };

  assert(sigemptyset(&default_action.sa_mask) >= 0);
  assert(sigaction(SIGSEGV, &default_action, NULL) >= 0);
}

static noreturn void raise_msg(int signal, const char* msg) {
  fflush(stdout);

  reset_sigsegv_handler();
  print_err("%s", msg);
  c0_print_callstack();
  fflush(stderr);

  raise(signal);
  exit(EXIT_FAILURE); 
}

noreturn void c0_error(const char *msg) {
  fflush(stdout);
  
  fprintf(stderr, "Error: %s\n", msg);
  fflush(stderr);
  exit(EXIT_FAILURE);
}

noreturn void c0_abort(const char *reason) {
  raise_msg(SIGABRT, reason);
}


/* Arithmetic */

noreturn void c0_abort_arith(const char *reason) {
  raise_msg(SIGFPE, reason);
}

c0_int c0_idiv(c0_int x, c0_int y) {
  if(y == 0) c0_abort_arith("division by 0");
  if(y == -1 && x == INT_MIN) c0_abort_arith("division causes overflow");
  return x / y;
}

c0_int c0_imod(c0_int x, c0_int y) {
  if(y == 0) c0_abort_arith("modulo by 0");
  if(y == -1 && x == INT_MIN) c0_abort_arith("modulo causes overflow");
  return x % y;  
}

c0_int c0_sal(c0_int x, c0_int y) {
  if(y < 0 || y >= 32) c0_abort_arith("shift left out-of-range");
  return x << y;
}

c0_int c0_sar(c0_int x, c0_int y) {
  if(y < 0 || y >= 32) c0_abort_arith("shift right out-of-range");
  return x >> y;
}


/* Memory */

/* Arrays are represented as EITHER a null pointer or an array with
 * three fields: count, elt_size, and elems.  Elems is a void pointer
 * pointing to the array data.
 * 
 * In fact, this pointer always actually points one past the end of
 * the struct:        _
 *                  / \
 * |---------------/---v------...
 * |    |    |    *   |       ...
 * |--------------------------...
 *
 * It would be incorrect for an implementation to rely on this
 * behavior. */

struct c0_array_header {
  c0_int count;
  c0_int elt_size;
  void* elems;
};

noreturn void c0_abort_mem(const char *reason) {
  raise_msg(SIGSEGV, reason);
}

c0_pointer c0_alloc(size_t size) {
  if (!size)
    size = 1;

  void* p = GC_MALLOC(size);
  if (!p) c0_abort_mem("allocation failed");
  bzero(p, size);
  return p;
}

void* c0_deref(c0_pointer a){
  if (a == NULL) c0_abort_mem("attempt to dereference null pointer");
  return a;
}

c0_array c0_array_alloc(size_t elemsize, c0_int elemcount) {
  /* test for overflow, somehow? */
  if (elemcount < 0) c0_abort_mem("array size cannot be negative");
  // Max array size is 1 gigabyte (including metadata)
  if (elemsize > 0 && elemcount > (c0_max_arraysize - 8) / elemsize)
    c0_abort_mem("array size too large (change $" C0_MAX_ARRAYSIZE_ENV " to adjust)");

  c0_array p = c0_alloc(sizeof(struct c0_array_header) + elemcount*elemsize);
  p->count = elemcount;              /* initialize number of elements */
  p->elt_size = elemsize;            /* store element size */
  p->elems = (void*)(p + 1);         /* initalize pointer to memory immediately
                                        following the struct */
  return p;
}

void* c0_array_sub(c0_array A, c0_int i, size_t elemsize) {
  if (A == NULL) c0_abort_mem("attempt to access default zero-size array");
  if (((unsigned)i) >= (unsigned)(A->count))
    c0_abort_mem("array index out of bounds");
  return (void *) (((char*)A->elems) + i*A->elt_size);
}

c0_int c0_array_length(c0_array A) {
  return A ? A->count : 0;
}

struct c0_tagged_struct {
  char* tyrep;
  void* ptr;
};

c0_tagged_ptr c0_tag_ptr(char* tyrep, c0_pointer a) {
  if (a == NULL)
    return NULL;
  else {
    c0_tagged_ptr p = GC_MALLOC(sizeof(struct c0_tagged_struct));
    if (!p) c0_abort_mem("allocation failed");
    p->tyrep = tyrep;
    p->ptr = a;
    return p;
  }
}

void* c0_untag_ptr(char* tyrep, c0_tagged_ptr p) {
  if (p == NULL)
    return NULL;
  else if (strcmp(tyrep, p->tyrep) == 0)
    return p->ptr;
  else {
    c0_abort_mem("untagging pointer failed");
  }
}

/* we don't compare tags since pointers with different
 * tags cannot be equal anyway */
c0_bool c0_tagged_eq(c0_tagged_ptr p, c0_tagged_ptr q) {
  void* raw_p = (p == NULL) ? p : p->ptr;
  void* raw_q = (q == NULL) ? q : q->ptr;
  return raw_p == raw_q;
}

c0_bool c0_hastag(char* tyrep, c0_tagged_ptr p) {
  if (p == NULL)
    return true;
  else
    return strcmp(tyrep, p->tyrep) == 0;
}
