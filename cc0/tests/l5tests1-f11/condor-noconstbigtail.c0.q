//test return 705082705

int fact0(int i, int accum) {
    int j = 0;
    int k = 0;
    int n = 1*i+accum;
    int l = 1;
    if (i<-1) j+k*l+fact0(10,accum);
    return i<=0 ? accum : l*fact0(i-1,(j*k*l)+l*accum+i);
}

int fact(int i) {
    return fact0(i,1);
}

int main () {
    int c = readint();
    return fact(c);
}
