int main ()
{
  /* Intializes random number generator */
  int len = 50;
  int myArray[len];
   for (int j = 0; j < len; j++)
    {
      myArray[j] = 1;
    }

  int res = 0;
  int i = 0;

  while (i < len-1)
    {
      res = res + myArray[i] ;
      i = i + 1;
    }
  return 0;
}
