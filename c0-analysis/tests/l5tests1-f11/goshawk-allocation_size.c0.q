//test segfault

int main()
{
    int size = readint();
    int[] a = alloc_array(int, size);
    return size;
}
