//test div-by-zero
//99 bottles of beer on the wall,
//except that it goes down to MIN_INT because
//input is negative

int bottles(int n) {
  if(n == 0)
    return 0;

  printint(n);
  printchar(32);
  printchar(98);
  printchar(111);
  printchar(116);
  printchar(116);
  printchar(108);
  printchar(101);
  printchar(115);
  printchar(32);
  printchar(111);
  printchar(102);
  printchar(32);
  printchar(98);
  printchar(101);
  printchar(101);
  printchar(114);
  printchar(32);
  printchar(111);
  printchar(110);
  printchar(32);
  printchar(116);
  printchar(104);
  printchar(101);
  printchar(32);
  printchar(119);
  printchar(97);
  printchar(108);
  printchar(108);
  printchar(44);
  printchar(10);
  printint(n);
  printchar(32);
  printchar(98);
  printchar(111);
  printchar(116);
  printchar(116);
  printchar(108);
  printchar(101);
  printchar(115);
  printchar(32);
  printchar(111);
  printchar(102);
  printchar(32);
  printchar(98);
  printchar(101);
  printchar(101);
  printchar(114);
  printchar(33);
  printchar(10);
  printchar(84);
  printchar(97);
  printchar(107);
  printchar(101);
  printchar(32);
  printchar(111);
  printchar(110);
  printchar(101);
  printchar(32);
  printchar(100);
  printchar(111);
  printchar(119);
  printchar(110);
  printchar(44);
  printchar(32);
  printchar(112);
  printchar(97);
  printchar(115);
  printchar(115);
  printchar(32);
  printchar(105);
  printchar(116);
  printchar(32);
  printchar(97);
  printchar(114);
  printchar(111);
  printchar(117);
  printchar(110);
  printchar(100);
  printchar(44);
  printchar(10);
  printint(n-1);
  printchar(32);
  printchar(98);
  printchar(111);
  printchar(116);
  printchar(116);
  printchar(108);
  printchar(101);
  printchar(115);
  printchar(32);
  printchar(111);
  printchar(102);
  printchar(32);
  printchar(98);
  printchar(101);
  printchar(101);
  printchar(114);
  printchar(32);
  printchar(111);
  printchar(110);
  printchar(32);
  printchar(116);
  printchar(104);
  printchar(101);
  printchar(32);
  printchar(119);
  printchar(97);
  printchar(108);
  printchar(108);
  printchar(46);
  printchar(10);
  printchar(10);
  return bottles(n-1);
}

int main() {
  int n = readint();
  return bottles(n);
}
