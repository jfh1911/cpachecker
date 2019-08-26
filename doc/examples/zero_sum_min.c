extern int __VERIFIER_nondet_int(void);

int SIZE;

int main()
{
	SIZE = __VERIFIER_nondet_int();
	if (1 <= SIZE)
	{
		int i = 0;
		int a[SIZE];
		
		while (i < SIZE - 1)		{
			a[i]=1;
			i = i++;

		}
		if (!(i < SIZE))		{
		ERROR:
			return 1;
		}
	}
	return 0;
}
