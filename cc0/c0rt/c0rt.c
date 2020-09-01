#include <stdlib.h>
#include <stdio.h>
#include <signal.h>
#include <stdnoreturn.h>
#include <string.h> 
#include <strings.h> // bzero 
#include <limits.h>
#include <errno.h>
#include <gc.h>
#include <c0runtime.h>

// Terminal color codes
#define ANSI_BOLD "\x1b[1m"
#define ANSI_BOLDRED ANSI_BOLD "\x1b[31m"
#define ANSI_BOLDBLUE ANSI_BOLD "\x1b[34m"
#define ANSI_RESET "\x1b[0m"

#define print_err(msg, ...) fprintf(stderr, ANSI_BOLDRED "c0rt: " msg ANSI_RESET "\n", ## __VA_ARGS__)

// Environment variable names for configuration
#define C0_BACKTRACE_LIMIT_ENV "C0_BACKTRACE_LIMIT"
#define C0_STACK_LIMIT_ENV "C0_STACK_LIMIT"
#define C0_MAX_ARRAYSIZE_ENV "C0_MAX_ARRAYSIZE"
#define C0_ENABLE_BACKTRACE "C0_ENABLE_BACKTRACE"

// Default backtrace print limit
static long c0_backtrace_print_limit = 50;
// Default max callstack depth 
static long c0_stacksize_limit = 0x15122;
// Default maximum array size in bytes (includes metadata)
static long c0_max_arraysize = 1 << 30; // 1 GB

// Whether to print backtraces or not.
// (0 = disabled, nonzero = enabled)
static long c0_enable_backtrace = true;

// Modifies out if parse succeeeds, leaves unchanged otherwise and prints a message
// name is the name of the environment variable
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

void c0_runtime_init() {
  GC_INIT();

  parse_env_with_default(C0_BACKTRACE_LIMIT_ENV, &c0_backtrace_print_limit);
  parse_env_with_default(C0_STACK_LIMIT_ENV, &c0_stacksize_limit);
  parse_env_with_default(C0_MAX_ARRAYSIZE_ENV, &c0_max_arraysize);
  parse_env_with_default(C0_ENABLE_BACKTRACE, &c0_enable_backtrace);
}

void c0_runtime_cleanup() {
  // nothing to do for the c0rt runtime
}

struct c0_stack_info {
  const char* funcname;
  long repeat_count;
};

static struct c0_stack_info* c0_backtrace_stack = NULL;
// Next available index in the array 
// or could be equal to limit, then the array will
// resize on the next push_callstack call.
static long c0_backtrace_size = 0; 
static long c0_backtrace_limit = 0;

// Total recursion depth (independent of c0_backtrace size)
static long c0_stack_size = 0;

void c0_print_callstack() {
  // If contracts are not turned on, then calls to c0_push/pop_callstack 
  // are not generated. So this function shouldn't run
  if (c0_backtrace_size == 0) return;
  // If backtraces are disabled, don't run as well
  if (!c0_enable_backtrace) return;

  print_err("in a function called from:");
  for (long i = 0; i < c0_backtrace_print_limit && i < c0_backtrace_size; i++) {
    const struct c0_stack_info* current = &c0_backtrace_stack[c0_backtrace_size - i - 1];

    int func_length = strchr(current->funcname, '(') - current->funcname;

    fprintf(stderr, 
      "          " ANSI_BOLDBLUE "%.*s" ANSI_RESET "%s", 
      func_length, current->funcname, current->funcname + func_length);

    if (current->repeat_count > 1) {
      fprintf(stderr, " (repeated %ld times)\n", current->repeat_count);
    }
    else {
      fprintf(stderr, "\n");
    }
  }

  if (c0_backtrace_print_limit < c0_backtrace_size) {
    fprintf(stderr, "          (...)\n");
    fprintf(stderr, "          backtrace truncated at %ld entries\n", c0_backtrace_print_limit);
    fprintf(stderr, "          change $" C0_BACKTRACE_LIMIT_ENV " to increase the number of entries shown\n");
  }
}

noreturn void c0_abort_mem(const char* msg);

void c0_push_callstack(c0_string c0_funcname) {
  c0_stack_size++;

  const char* funcname = c0_string_tocstr(c0_funcname);

  if (c0_stack_size > c0_stacksize_limit) {
    print_err("Maximum callstack size exceeded (is %ld, change $" C0_STACK_LIMIT_ENV " to adjust)", c0_stacksize_limit);
    c0_print_callstack();
    raise(SIGSEGV);
  }

  if (c0_backtrace_size == c0_backtrace_limit) {
    c0_backtrace_limit++;
    c0_backtrace_limit *= 2;

    c0_backtrace_stack = GC_REALLOC(c0_backtrace_stack, c0_backtrace_limit * sizeof(struct c0_stack_info));
    if (!c0_backtrace_stack) c0_abort_mem("allocation failure");
  }

  // Performance: Technically we would only have to compare the strings
  // until the first space (since function names can't have spaces).
  // The rest of the string is location info
  if (c0_backtrace_size == 0 || strcmp(c0_backtrace_stack[c0_backtrace_size - 1].funcname, funcname) != 0) {  
    // Stack is empty or this is a different function
    c0_backtrace_stack[c0_backtrace_size] = (struct c0_stack_info){ 
      .funcname = funcname, 
      .repeat_count = 1 
    };
    c0_backtrace_size++;
  }
  else {
    // Stack is nonempty and this is the same function, so we just need to increment the count
    c0_backtrace_stack[c0_backtrace_size - 1].repeat_count++;
  }
}

void c0_pop_callstack() {
  c0_stack_size--;
  if (c0_backtrace_stack == NULL || c0_backtrace_size == 0) return;

  struct c0_stack_info* top = &c0_backtrace_stack[c0_backtrace_size - 1];

  if (top->repeat_count > 1) top->repeat_count--;
  else { 
    c0_string_freecstr(c0_backtrace_stack[c0_backtrace_size - 1].funcname);
    c0_backtrace_size--;
  }
}

static noreturn void raise_msg(int signal, const char* msg) {
  print_err("%s", msg);
  c0_print_callstack();
  fflush(stderr);

  raise(signal);
  __builtin_unreachable(); 
}

noreturn void c0_error(const char *msg) {
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
