//test return 0

//mult(arr) returns an array arr' such that
//arr'[i] = the product of all elements in 
//arr except arr[i], but it achieves this 
//in linear time and WITHOUT division
int print_array(int[] a, int len);

int[] mult(int[] arr, int length)
{
  int[] forward = alloc_array(int,length);
  int[] backward = alloc_array(int,length);

  int k = length-1;
  for(int i = 0; i < length; i++)
  {
      if(i == 0)
        forward[i] = arr[i];
      else
        forward[i] = forward[i-1]*arr[i];
      

      if(k == length-1)
        backward[k] = arr[k];
      else
        backward[k] = backward[k+1] * arr[k];
      k--;
  }

  for(int i = 0; i < length; i++)
  {
    if(i == length-1)
      arr[i] = forward[i-1];
    else if(i == 0)
      arr[i] = backward[i+1];
    else
      arr[i] = forward[i-1] * backward[i+1];
  }
  
  print_array(forward,length);
  printchar(0xa);
  print_array(backward,length);
  printchar(0xa);
  return arr;
}

int print_array(int[] arr,int len)
{
  for(int i = 0; i < len;i++)
  {
    printint(arr[i]);
    printchar(0x20);
  }
  printchar(0xa);
  return 0;
}

int main()
{
  int n = 8;
  int[] a = alloc_array(int,n);
  a[0] = 5;
  a[1] = 5;
  a[2] = 9;
  a[3] = 6;
  a[4] = 8;
  a[5] = 3;
  a[6] = 8;
  a[7] = 2;
  
  print_array(mult(a,n),n);
  return 0;
}
