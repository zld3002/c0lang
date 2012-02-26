int* x = alloc(int);
// Reads the value from the heap at the address stored in x.
int y = *x;
// Writes the value 9 to the heap at the address stored in x.
*x = 9;
y = 2
// y = 2, *x = 9

