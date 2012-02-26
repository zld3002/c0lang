struct Box {
  // 0 for int, 1 for pointer
  int tag;
  union U {
    int i;
    int *p;
  } value;
};

int *f(Box *b, int *p) {
  b->tag = 1;
  b->value.p = p;
  return p;
}

int main () {
  Box b;
  b.tag = 0;
  b.value.i = 0;

  int *s = f(&b, &b.value.i);

  // Can now get a pointer to arbitrary memory
  *s = 40;

  return 0;
}
