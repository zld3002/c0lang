//test segfault

int main()
{
    int all = readint();
    int *p;
    if (all != 0)
        p = alloc(int);
    else
        p = NULL;

    return *p;
}
