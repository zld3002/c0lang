//test segfault

int main()
{
    int n = readint();
    int i = readint();
    int[] a = alloc_array(int, n);
    a[i] = n;
    return n;
}
