/* C0VM sample implementation
 * 15-122, Fall 2010
 * William Lovas
 */

#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <signal.h>

#include "xalloc.h"
#include "contracts.h"
#include "stacks.h"

#include "bare.h"
#include "c0vm.h"
#include "c0vm_c0ffi.h"


/* call stack frames */
typedef struct frame * frame;
struct frame {
    c0_value *V;  /* local variables */
    stack S;      /* operand stack */
    ubyte *P;     /* function body and last program counter */
    int pc;       /* return address */
};


void c0vm_raise(bool b, char *err, int sig) {
    if (!b) {
        fprintf(stderr, "Exception: %s\n", err);
        raise(sig);
    }
}

/* two-byte (signed) offset and (unsigned) index calculations */
/* some casts are redundant due to the "integer promotions" and the
   "usual arithmetic conversions", but they're left explicit for clarity */

int offset(ubyte c1, ubyte c2) {
  return ((int) (byte) c1 << 8) | (int) c2;
}

unsigned index(ubyte c1, ubyte c2) {
  return ((unsigned) c1 << 8) | (unsigned) c2;
}

/* arithmetic operations */
unsigned int arithop(ubyte op, unsigned int x, unsigned int y) {
    switch (op) {
        case IDIV:
            c0vm_raise(y != 0, "Division by zero", SIGFPE);
            c0vm_raise(!(x == (unsigned int) INT_MIN && y == (unsigned int) -1),
                       "INT_MIN div -1", SIGFPE);
            return (int)x / (int)y;

        case IREM:
            c0vm_raise(y != 0, "Remainder by zero", SIGFPE);
            c0vm_raise(!(x == (unsigned int) INT_MIN && y == (unsigned int) -1),
                       "INT_MIN rem -1", SIGFPE);
            return (int)x % (int)y;

        case IADD: return x + y;
        case ISUB: return x - y;
        case IMUL: return x * y;

        case IAND: return x & y;
        case IOR:  return x | y;
        case IXOR: return x ^ y;

        case ISHL: return (x << (y & 0x1f));
        /* implementation-defined: implemented by sign-extension in GCC */
        case ISHR: return ((signed int) x >> (y & 0x1f));
    }

    fprintf(stderr, "invalid arithmetic opcode: %x\n", op);
    abort();
}

/* comparisons */
bool intcomp(ubyte op, int x, int y) {
  switch (op) {
  case IF_CMPEQ: return x == y;
  case IF_CMPNE: return x != y;
  case IF_ICMPLT: return x < y;
  case IF_ICMPGE: return x >= y;
  case IF_ICMPGT: return x > y;
  case IF_ICMPLE: return x <= y;
  }

  fprintf(stderr, "invalid conditional branch opcode: %x\n", op);
  abort();
}

bool valcomp(ubyte op, c0_value v1, c0_value v2) {
  switch (op) {
  case IF_CMPEQ: return v1 == v2;
  case IF_CMPNE: return v1 != v2;
  }
  
  fprintf(stderr, "invalid conditional branch opcode: %x\n", op);
  abort();
}

int execute(struct bc0_file *bc0) {
    /* initial callStack is empty */
    stack callStack = stack_new();
    /* initial program is the "main" function, function 0 (which must exist) */
    assert(bc0->function_count > 0);
    struct function_info* main_fn = &bc0->function_pool[0];
    /* initial variables are all zero, stack is empty */
    c0_value *V = xcalloc(main_fn->num_vars, sizeof(c0_value));
    stack S = stack_new();
    ubyte *P = main_fn->code;
    int pc = 0;

    while (true) {

#ifdef DEBUG
      printf("Executing pc %d opcode %x  --- Operand stack size: %d\n", pc, P[pc], stack_size(S));
#endif

      switch (P[pc]) {
	/* arithmetic */
      case IADD:
      case ISUB:
      case IMUL:
      case IDIV:
      case IREM:
      case IAND:
      case IOR:
      case IXOR:
      case ISHL:
      case ISHR: {
	/* cast to unsigned so we can do reliably defined arithmetic */
	unsigned int y = (unsigned int) INT(pop(S));
	unsigned int x = (unsigned int) INT(pop(S));
	push(S, VAL((int) arithop(P[pc], x, y)));
	pc++;
	break;
      }

      /* stack operations */
      case DUP: {
	c0_value v = pop(S);
	push(S, v);
	push(S, v);
	pc++;
	break;
      }

      case POP: {
	pop(S);
	pc++;
	break;
      }

      case SWAP: {
	c0_value v2 = pop(S);
	c0_value v1 = pop(S);
	push(S, v2);
	push(S, v1);
	pc++;
	break;
      }

      /* memory allocation */
      case NEW: {
	ubyte sz = P[pc+1];
	void *a = xcalloc(1, sz);
	push(S, a);
	pc += 2;
	break;
      }

      case NEWARRAY: {
	ubyte sz = P[pc+1];
	int n = INT(pop(S));
	c0vm_raise(n >= 0, "Alloc negative array", SIGSEGV);
	/* flexible struct c0_array has fields for count and size */
	struct c0_array *a = xcalloc(1, sizeof(struct c0_array) + n*sz);
	a->count = n;
	a->elt_size = sz;
	push(S, (void*)a);
	pc += 2;
	break;
      }

      case ARRAYLENGTH: {
	struct c0_array *a = (struct c0_array *) pop(S);
	ASSERT(a != NULL);
	push(S, VAL(a->count));
	pc++;
	break;
      }

      /* memory access */
      case AADDF: {
	ubyte f = P[pc+1];
	byte *a = (byte *) pop(S);
	c0vm_raise(a != NULL, "NULL pointer dereference", SIGSEGV);
	push(S, (void*)(a+f));
	pc += 2;
	break;
      }

      case AADDS: {
	int i = INT(pop(S));
	struct c0_array *a = (struct c0_array *) pop(S);
	c0vm_raise(a != NULL, "NULL pointer dereference", SIGSEGV);
	c0vm_raise(0 <= i && i < a->count,
		   "Array index out of bounds", SIGSEGV);
	push(S, (void*)(a->elems + a->elt_size*i));
	pc++;
	break;
      }

      case IMLOAD : {
	int *a = (int *) pop(S);
	c0vm_raise(a != NULL, "NULL pointer dereference", SIGSEGV);
	push(S, VAL(*a));
	pc++;
	break;
      }

      case AMLOAD: {
	c0_value *a = (c0_value *) pop(S);
	c0vm_raise(a != NULL, "NULL pointer dereference", SIGSEGV);
	push(S, *a);
	pc++;
	break;
      }

      case IMSTORE: {
	int x = INT(pop(S));
	int *a = (int *) pop(S);
	c0vm_raise(a != NULL, "NULL pointer dereference", SIGSEGV);
	*a = x;
	pc++;
	break;
      }

      case AMSTORE: {
	c0_value v = pop(S);
	c0_value *a = (c0_value *) pop(S);
	c0vm_raise(a != NULL, "NULL pointer dereference", SIGSEGV);
	*a = v;
	pc++;
	break;
      }

      case CMLOAD: {
	byte *a = (byte *) pop(S);
	c0vm_raise(a != NULL, "NULL pointer dereference", SIGSEGV);
	assert(*a >= 0); /* XXX necessary? */
	push(S, VAL(*a));
	pc++;
	break;
      }

      case CMSTORE: {
	byte b = INT(pop(S)) & 0x7f;
	byte *a = (byte *) pop(S);
	c0vm_raise(a != NULL, "NULL pointer dereference", SIGSEGV);
	*a = b;
	pc++;
	break;
      }

      /* local variables */
      case VLOAD: {
	int i = P[pc+1];
	push(S, V[i]);
	pc += 2;
	break;
      }

      case VSTORE: {
	int i = P[pc+1];
	c0_value v = pop(S);
	V[i] = v;
	pc += 2;
	break;
      }

      /* constants */
      case ACONST_NULL: {
	push(S, NULL);
	pc++;
	break;
      }

      case BIPUSH: {
	byte b = P[pc+1];
	push(S, VAL(b));
	pc += 2;
	break;
      }

      case ILDC: {
	ubyte c1 = P[pc+1];
	ubyte c2 = P[pc+2];
	int x = bc0->int_pool[index(c1, c2)];
	push(S, VAL(x));
	pc += 3;
	break;
      }

      case ALDC: {
	ubyte c1 = P[pc+1];
	ubyte c2 = P[pc+2];
	char *a = &bc0->string_pool[index(c1, c2)];
	push(S, a);
	pc += 3;
	break;
      }

      /* control flow */
      case NOP: {
	pc++;
	break;
      }

      case IF_CMPEQ:
      case IF_CMPNE: {
	ubyte o1 = P[pc+1];
	ubyte o2 = P[pc+2];
	c0_value v2 = pop(S);
	c0_value v1 = pop(S);
	if (valcomp(P[pc], v1, v2))
	  pc += offset(o1, o2);
	else
	  pc += 3;
	break;
      }

      case IF_ICMPLT:
      case IF_ICMPGE:
      case IF_ICMPGT:
      case IF_ICMPLE: {
	ubyte o1 = P[pc+1];
	ubyte o2 = P[pc+2];
	int y = INT(pop(S));
	int x = INT(pop(S));
	if (intcomp(P[pc], x, y))
	  pc += offset(o1, o2);
	else
	  pc += 3;
	break;
      }

      case GOTO: {
	ubyte o1 = P[pc+1];
	ubyte o2 = P[pc+2];
	pc += offset(o1, o2);
	break;
      }

      /* function calls and returns */
      case INVOKENATIVE: {
	ubyte c1 = P[pc+1];
	ubyte c2 = P[pc+2];
	struct native_info ni = bc0->native_pool[index(c1, c2)];
	c0_value *args = xcalloc(ni.num_args, sizeof(c0_value));
	for (int i = ni.num_args - 1; i >= 0; i--) args[i] = pop(S);
	native_fn g = native_function_table[ni.function_table_index];
#ifdef DEBUG
	printf("native_pool index: %d\n", index(c1, c2));
	ASSERT(g != NULL);
	printf("about to run function pointer: 0x%08x\n", (int) g);
	printf("function has %d args\n", ni.num_args);
#endif
	c0_value v = g(args);
	free(args);
	push(S, v);
	pc += 3;
	break;
      }

      case INVOKESTATIC: {
	ubyte c1 = P[pc+1];
	ubyte c2 = P[pc+2];
	struct function_info fi = bc0->function_pool[index(c1, c2)];
	/* 1. build a stack frame containing current code pointer,
	 *    current pc, current locals, and current operand stack.
	 *    push this stack frame onto the call stack.
	 * 2. allocate a new locals array of size fi.num_vars.
	 * 3. pop fi.num_args words off the stack and put them into
	 *    the new locals array.
	 * 4. create a new, empty operand stack.
	 * 5. load the new code into the program array.
	 * 6. set the program counter to 0.
	 */
	frame F = xmalloc(sizeof(struct frame));
	F->V = V;
	F->S = S;
	F->P = P;
	F->pc = pc+3;   /* return address is one after <c1,c2> */
	push(callStack, F);

	V = xcalloc(fi.num_vars, sizeof(c0_value));
	for (int i = fi.num_args - 1; i >= 0; i--) V[i] = pop(S);
	S = stack_new();
	P = fi.code;
	pc = 0;

	break;
      }

      case RETURN: {
	/* 1. pop return value off the operand stack.  (assert empty.)
	 * 2. free the current local variables array and operand stack.
	 * 3. if callStack is empty, return that value.  (as an int?)
	 * 4. pop a frame off the callstack.
	 * 5. restore V, S, P, and pc from the stack frame.
	 * 6. free the stack frame.
	 * 7. push the return value onto the operand stack.
	 */
	c0_value v = pop(S);
	assert(stack_empty(S));

	free(V);
	stack_free(S, NULL);

	if (stack_empty(callStack)) {
	  stack_free(callStack, NULL);
	  return INT(v);
	}

	frame F = pop(callStack);
	V = F->V;
	S = F->S;
	P = F->P;
	pc = F->pc;

	free(F);

	push(S, v);
	break;
      }

      default:
	fprintf(stderr, "invalid opcode: %x\n", P[pc]);
	abort();
      }
    }

    assert(false);
}
