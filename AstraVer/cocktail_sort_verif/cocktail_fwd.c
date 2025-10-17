/*@
predicate sorted{L}(int* a, integer beg, integer end) =
    \forall integer i, j; beg <= i <= j < end ==> a[i] <= a[j];

predicate swap_in_array{L1,L2}(int* a, integer b, integer e, integer i, integer j) =
    b <= i < e && b <= j < e &&
    \at(a[i], L1) == \at(a[j], L2) &&
    \at(a[j], L1) == \at(a[i], L2) &&
    \forall integer k; b <= k < e && k != j && k != i ==>
    \at(a[k], L1) == \at(a[k], L2);

inductive permutation{L1,L2}(int* a, integer b, integer e){
    case reflexive{L1}:
        \forall int* a, integer b,e ; permutation{L1,L1}(a, b, e);
    case swap{L1,L2}:
        \forall int* a, integer b,e,i,j ;
            swap_in_array{L1,L2}(a,b,e,i,j) ==> permutation{L1,L2}(a, b, e);
    case transitive{L1,L2,L3}:
        \forall int* a, integer b,e ;
            permutation{L1,L2}(a, b, e) && permutation{L2,L3}(a, b, e) ==>
            permutation{L1,L3}(a, b, e);
  }
*/

/*@
requires n >= 0;
requires \valid(arr + (0 .. n-1));
assigns arr[0 .. n-1];
ensures sorted(arr, 0, n);
ensures permutation{Pre, Post}(arr, 0, n);
*/
void cocktail_fwd(int *arr, int n) {
    int swapped = 1;
    int start = 0;
    int end = n - 1;

    /*@
    loop invariant 0 <= start <= end+1 <= n;
    loop invariant permutation{Pre, Here}(arr, 0, n);
    loop invariant sorted(arr, 0, start);
    loop invariant sorted(arr, end+1, n);
    loop invariant \forall integer i, j; 0 <= i < start && start <= j < n ==> arr[i] <= arr[j];
    loop invariant \forall integer i, j; 0 <= i <= end && end < j < n ==> arr[i] <= arr[j];
    loop invariant swapped >= 0;
    loop assigns arr[0 .. n-1], start, end, swapped;
    loop variant end - start;
    */
    while (swapped > 0) {
        int i, tmp;

        //@ ghost fwd_begin: ;
        swapped = 0;

        /*@
        loop invariant start <= i <= end;
        loop invariant permutation{Pre, Here}(arr, 0, n);
        loop invariant swapped >= 0;
        loop invariant \forall integer j; start <= j < i ==> arr[j] <= arr[j+1];
        loop invariant sorted(arr, 0, start);
        loop invariant sorted(arr, end+1, n);
        loop assigns i, swapped, arr[start .. end];
        loop variant end - i;
        */
        for (i = start; i < end; ++i) {
            if (arr[i] > arr[i + 1]) {
                //@ ghost swap_begin: ;
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
                //@ assert swap_in_array{swap_begin, Here}(arr, 0, n, i, i+1);
                //@ assert permutation{Pre, Here}(arr, 0, n);
            }
        }

        if (!swapped)
            break;
        --end;

        //@ ghost bwd_begin: ;
        swapped = 0;
        /*@
        loop invariant start-1 <= i <= end;
        loop invariant permutation{Pre, Here}(arr, 0, n);
        loop invariant swapped >= 0;
        loop invariant \forall integer j; i < j < end ==> arr[j] <= arr[j+1];
        loop invariant sorted(arr, 0, start);
        loop invariant sorted(arr, end+1, n);
        loop assigns i, swapped, arr[start .. end];
        loop variant i - start + 1;
        */
        for (i = end - 1; i >= start; --i) {
            if (arr[i] > arr[i + 1]) {
                //@ ghost swap_begin2: ;
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
                //@ assert swap_in_array{swap_begin2, Here}(arr, 0, n, i, i+1);
                //@ assert permutation{Pre, Here}(arr, 0, n);
            }
        }
        ++start;
    }
}
