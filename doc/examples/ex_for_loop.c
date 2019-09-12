extern int __VERIFIER_nondet_int(void);

int SIZE;

int main()
{
    SIZE = __VERIFIER_nondet_int();
    int i = 0;
    int  res =0;
    if (0 <= SIZE)
    {        
        int a[SIZE];
   
        for (     int j=0;j < 10;    j = j+1)        {
            a[j]=__VERIFIER_nondet_int();
            res = res + a[j];
        
        }
    }
    else{
        ;
    }
    return 0;
}
