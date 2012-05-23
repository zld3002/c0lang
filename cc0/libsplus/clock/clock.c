#include <time.h>

int millisecs()
{
	clock_t t;
	
	t = clock();
	/* CLOCK_PER_SEC = 10^6 per UNIX Spec (see clock(3)) */
	return (int)(t / (CLOCKS_PER_SEC / 1000)); 
}

int now()
{
    return (int)time(NULL);
}