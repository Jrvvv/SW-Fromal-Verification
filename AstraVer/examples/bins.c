// Binary sort verification example

// long *a -- sorted(!!) array
// int n -- array lengt
// long v -- searched value

/*@
predicate Sorted(long *a, integer n) =
  \forall integer i, j;
    0 <= i <= j < n ==> a[i] <= a[j];
*/

/*@
// PRE
requires \valid(a+(0..n-1));
requires n >= 0;
requires Sorted(a, n);

// POST
ensures -1 <= \result < n;
ensures \result >= 0
  ==> a[\result] == v;
ensures \result == -1
  ==> \forall integer k; 0 <= k < n ==> a[k] != v;

// !!! To say array is not modified !!!
assigns \nothing;
*/

int bins(long *a, int n, long v)
{
  int u;
  int l = 0;

  u = n -1;
  /*@
  loop invariant \forall integer k; 0 <= k < l ==> a[k] < v;
  loop invariant \forall integer k; u < k < n ==> v < a[k];
  loop invariant 0 <= l <= n;
  loop invariant -1 <= u < n;

  loop variant n - l + u;
  */
  while (l <= u) {
    int m = (u + l) / 2;
    //@ assert 0 <= m < n;
    if (a[m] < v) {
      //@ assert \forall integer k; 0 <= k <= m ==> a[k] < v;
      //@ assert \forall integer k; 0 <= k <= m ==> a[k] <= a[m];
      l = m + 1;
    } else if (a[m] > v) {
      //@ assert \forall integer k; 0 <= k <= m ==> v < a[k];
      //@ assert \forall integer k; 0 <= k <= m ==> a[m] <= a[k];
      u = m - 1;
    } else {
      return m;
    }
  }

  return -1;
}
