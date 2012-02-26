/* C0VM structs, function signatures, and opcodes
 * 15-122, Fall 2010
 * William Lovas & Tom Cortina
 */

#ifndef _C0VM_H_
#define _C0VM_H_

#include <inttypes.h>

/* Version info in file is (BC0_VERSION << 1) | arch_bit
 * where arch_bit = 1 (64 bits), or arch_bit = 0 (32 bits) */
#define BC0_VERSION 1

typedef signed char byte;
typedef unsigned char ubyte;

/* type of arbitrary c0_values -- variables, operands, etc. */
typedef void * c0_value;

/* VAL(x) converts int x to generic C0 value */
/* x can also be of other integral type */
/* Assumes sizeof(intptr_t) >= sizeof(int) */
#define VAL(x) ((c0_value) (intptr_t) (x))

/* INT(p) converts generic C0 value v to int */
/* Assumes that sizeof(intptr_t) >= sizeof(int) */
#define INT(v) ((int) (intptr_t) (v))

/*** .bc0 file format, including function info and native info ***/

struct bc0_file {
    int magic;
    int version;

    /* integer and string constant pools */
    int int_pool_count;
    int *int_pool;

    /* string pool stores all strings consecutively with NUL terminators */
    int string_pool_count;
    char *string_pool;

    /* bytecode and native function tables */
    int function_count;
    struct function_info *function_pool;
    int native_count;
    struct native_info *native_pool;
};

struct function_info {
    int num_args;
    int num_vars;
    int code_length;
    ubyte *code;
};

struct native_info {
    int num_args;
    int function_table_index;
};


/*** interface functions ***/

struct bc0_file *read_program(char *filename);
void free_program(struct bc0_file *program);

int execute(struct bc0_file *bc0);

/*** instruction opcodes ***/

/* arithmetic operations */
#define IADD        0x60
#define IAND        0x7E
#define IDIV        0x6C
#define IMUL        0x68
#define IOR         0x80
#define IREM        0x70
#define ISHL        0x78
#define ISHR        0x7A
#define ISUB        0x64
#define IXOR        0x82

/* stack operations */
#define DUP         0x59
#define POP         0x57
#define SWAP        0x5F

/* memory allocation */
#define NEWARRAY    0xBC
#define ARRAYLENGTH 0xBE
#define NEW         0xBB

/* memory access */
#define AADDF       0x62
#define AADDS       0x63
#define IMLOAD      0x2E
#define AMLOAD      0x2F
#define IMSTORE     0x4E
#define AMSTORE     0x4F
#define CMLOAD      0x34
#define CMSTORE     0x55

/* local variables */
#define VLOAD       0x15
#define VSTORE      0x36

/* constants */
#define ACONST_NULL 0x01
#define BIPUSH      0x10
#define ILDC        0x13
#define ALDC        0x14

/* control flow */
#define NOP         0x00
#define IF_CMPEQ    0x9F
#define IF_CMPNE    0xA0
#define IF_ICMPLT   0xA1
#define IF_ICMPGE   0xA2
#define IF_ICMPGT   0xA3
#define IF_ICMPLE   0xA4
#define GOTO        0xA7

/* function calls and returns */
#define INVOKESTATIC    0xB8
#define INVOKENATIVE    0xB7
#define RETURN          0xB0

#endif /* _C0VM_H_ */
