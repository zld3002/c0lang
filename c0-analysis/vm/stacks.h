/* Interface for stacks
 * 15-122 Principles of Imperative Computation, Fall 2010
 * Frank Pfenning
 */

#include <stdbool.h>

#ifndef _STACKS_H
#define _STACKS_H

typedef struct stack* stack;
bool stack_empty(stack S);	/* O(1) */
stack stack_new();		/* O(1) */
void push(stack S, void* e);	/* O(1) */
void* pop(stack S);		/* O(1) */
int stack_size(stack S);        /* O(1) */
void stack_free(stack S, void (*data_free)(void* e));   /* O(n) */

#endif
