//test return -1206908864

int main () {
    int c = readint();
    int * j = alloc(int);
    int i=0;
    for (i = 0; i < c ; i ++) {
    	*j += 1 * i + (*j) + c + 0 + (*j) + i + c + 0;
	*j *= 1;
    }
    
    return (*j) + i;
}
