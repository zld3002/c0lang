//test segfault

int main()
{
    int[] *a = alloc(int[]);
    int all = readint();
    if (all != 14) 
        *a = alloc_array(int, 10);
    (*a)[0] = all;
    return all;
}
