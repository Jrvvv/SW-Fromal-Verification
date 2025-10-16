// Simple ariphmetic function verification example

/*@
requires 6000 >= n >= 0;
ensures \result == n * (n + 1) / 2;
*/
int foo(int n)
{
	int i = 0;
	int s = 0;
	/*@
	loop invariant s == i * (i - 1) / 2;
	loop invariant 1 <= i <= n + 1;
	loop variant n - i;
	*/
	for (i = 1; i <= n; i++) {
		s += i;
	}
	return s;
}
