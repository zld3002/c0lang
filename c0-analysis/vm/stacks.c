/* Stacks
 * 15-122 Principles of Imperative Computation, Spring 2011
 * Frank Pfenning
 */

#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include "xalloc.h"
#include "contracts.h"
#include "stacks.h"

/* Linked lists */

typedef struct list* list;
struct list {
  void* data;			/* generic data */
  list next;
};

/* is_segment(start, end) will diverge if list is circular! */
bool is_segment(list start, list end)
{ list p = start;
  while (p != end) {
    if (p == NULL) return false;
    p = p->next;
  }
  return true;
}

/* segement_free(start, end, data_free) will free the list
 * segment from start to end, excluding end.  It also applies
 * the data_free function to every stored element
 */
void segment_free(list start, list end, void (*data_free)(void* e))
{
  REQUIRES(is_segment(start, end));
  list p = start;
  while (p != end) {
    ASSERT(p != NULL);
    list tmp = p;
    p = p->next;
    if (data_free != NULL && tmp->data != NULL)
      (*data_free)(tmp->data);
    free(tmp);
  }
  return;
}


/* Stacks */ 

struct stack {
  list top;
  list bottom;
  int size;
};

bool is_stack (stack S) {
  if (S == NULL) return false;
  if (S->top == NULL || S->bottom == NULL) return false;
  if (!is_segment(S->top, S->bottom)) return false;
  return true;
}

bool stack_empty(stack S) {
  REQUIRES(is_stack(S));
  return S->top == S->bottom;
}

stack stack_new() {
  REQUIRES(true);		/* no precondition */
  stack S = xmalloc(sizeof(struct stack));
  list l = xmalloc(sizeof(struct list));
  S->top = l;
  S->bottom = l;
  S->size = 0;
  ENSURES(is_stack(S) && stack_empty(S));
  return S;
}

void stack_free(stack S, void (*data_free)(void* e))
{ REQUIRES(is_stack(S));
  segment_free(S->top, S->bottom, data_free);
  free(S->bottom);
  free(S);
  return;
}

void push(stack S, void* e)
{
  REQUIRES(is_stack(S));
  list first = xmalloc(sizeof(struct list));
  first->data = e;
  first->next = S->top;
  S->top = first;
  S->size++;
  ENSURES(is_stack(S) && !stack_empty(S));
}

void* pop(stack S) {
  REQUIRES(is_stack(S) && !stack_empty(S));
  assert(S != NULL && !stack_empty(S)); /* check this routinely */
  void* e = S->top->data;	/* save old stack element to return */
  list q = S->top;		/* save old list node to free */
  S->top = S->top->next;
  S->size--;
  free(q);			/* free old list node */
  ENSURES(is_stack(S));
  return e;			/* return old stack element */
}

int stack_size(stack S)
{ REQUIRES(is_stack(S));
  return S->size;
}
