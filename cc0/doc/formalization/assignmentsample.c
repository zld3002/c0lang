int x;
{
  bool y;
  /* Error: x has not been assigned */
  y = x > 0;
  /* Error: y has not been assigned */
  y = !y;
}
/* Error: y is not in scope */
x = y > 0 ? 3 : 4;
int y;
y = x+2;

