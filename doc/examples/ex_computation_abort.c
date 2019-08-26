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
       while( i <= SIZE){
            if(i != 0){			
				a[i]=__VERIFIER_nondet_int();
				res = res + a[i];
			}else{
				;
			}
			i = i+1;
		}
		
    }
    else{
        ;
    }
    return 0;
}
