//test segfault

int main()
{
    int[] *a = alloc(int[]);
    int all = readint();
    if (all != 13) 
        *a = alloc_array(int, 10);
    return (*a)[0];
}
