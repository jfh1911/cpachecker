
extern int __VERIFIER_nondet_int(void);
void *malloc(unsigned int size);

int SIZE;

const int MAX = 100000;

int main()
{
	__VERIFIER_error();
	SIZE = __VERIFIER_nondet_int();

	if (SIZE > 1 && SIZE < MAX)
	{
		int SIZE_Minus_ONE = SIZE - 1;
		int i = 0;
		int *a = malloc(sizeof(long) * SIZE);
		int sum = 0;

		for (int j = 0; j < SIZE; j++)
		{
			a[j] = 1;
		}

		while (i < SIZE -1)
		{
			sum = sum + a[i];
			int temp = i + 1;
			i = i++;
		}
		
		if( ! (i  < SIZE)){
			ERROR: return 1;
		}
	}
	return 0;
}
