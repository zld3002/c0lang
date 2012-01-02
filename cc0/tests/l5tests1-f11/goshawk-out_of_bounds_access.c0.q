//test segfault

int main()
{
    int n = readint();
    int i = readint();
    int[] a = alloc_array(int, n);
    return a[i];
}
