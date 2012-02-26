union Box {
  int Int;
  int* Ptr;
};

void SomeComputation(Box &b);

int main () {
  Box b = Int (0);
  Box *pb = &b;

  SomeComputation(&b);

  switch (b) {
  case Int i:
    *pb = Pointer(malloc(sizeof(int)));
    return i;
  case Pointer p:
    *pb = Int(0);
    return *p;
  }
}
