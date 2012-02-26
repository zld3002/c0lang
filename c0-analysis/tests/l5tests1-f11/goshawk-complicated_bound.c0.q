//test segfault

int main()
{
    int sum = 0;
    while (!eof()) {
        sum += readint();
    }

    int[] a = alloc_array(int, sum);
    return a[sum];
}
