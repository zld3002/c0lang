#include <stddef.h>

struct list {
  int data;
  struct list *next;
}

int length(struct list *p) {
  int l = 0;
  while (p) {
    l++;
    p = p->next;
  }
  return l;
}

