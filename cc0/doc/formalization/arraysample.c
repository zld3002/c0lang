int[] x = alloc_array(int, 4);
x[0] = 9;
x[1] = 3;
x[2] = x[0] + x[1];
/* Runtime errors: */
x[4] += 9;
int[] x = alloc_array(int, -1);
