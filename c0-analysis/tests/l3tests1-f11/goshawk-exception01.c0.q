//test segfault
// read off the end of a file

int main()
{
    while(!eof()) {
        int c = readchar();
        //Tranlsate upper case to lower case
        if (c >= 97 && c <= 122) {
            c -= 32;
        }
        printchar(c);
    }

    readchar();

    return 0;
}
