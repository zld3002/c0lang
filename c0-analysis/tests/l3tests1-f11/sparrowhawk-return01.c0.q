//test return 17

//uses helper functions to add two integers in input file

int ascii2int(int x)
{
	return x - 0x30;
}

int main()
{
	int x = ascii2int(readchar());
	int y = ascii2int(readchar());

	return (x + y);
}
