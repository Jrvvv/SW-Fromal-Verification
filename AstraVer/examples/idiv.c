// Integer divide example

/*@ // Pre-condition
@ requires a >= 0 && b > 0;
@ requires \valid(r);
@ // Modified memory block
@ assigns *r;
@ // Post-condition
@ // ensures \let q = \result; a == q * b + *r;
@ // ensures 0 <= *r < b;
@ // Аналогичное :
@ ensures a == b * \result + *r && 0 <= *r < b;
@*/

int idiv(int a, int b, int *r)
{
	int q = 0;
	int p = a;
	/*@ loop invariant (a == b * q + p) && (0 <= p <= a);
	  @ loop assigns q, p;
	  @ loop variant p; // is 0 be default (lowest edge)
	  @*/
	while (p >= b) {
		q++;
		p -= b;
	}
	/*@ assert (a == q * b + p) && (0 <= p < b); */
	*r = p;

	return q;
}
