int foo(int x) {
  x += 2;
  return x;
}

int bar(int y) {
  int x = y*2;
  int z = foo(x);
  /* x is still y*2 no matter what foo does. */
  return z+x;
}

