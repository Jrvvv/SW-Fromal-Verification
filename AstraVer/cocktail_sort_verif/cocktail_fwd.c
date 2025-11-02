/*
* Parameters:
* 1) Timeout: 30 s (the longest proving duration is 26.99 s)
* 2) Memory: 6000Mb
* 3) Num of processes: 6
* 4) CVC4 version: 1.8
* 5) Alt-Ergo version: 2.6.2
*
* Algorithm:
* 1) Run proving for safety and lemas with CVC4
* 2) Split behaviours twice
* 3) Run proving for behaviours with CVC4
* 4) Run proving for behaviours with Alt-Ergo
*/

/*@
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

lemma transitive_permutation{L1, L2, L3}:
    \forall int* a, integer beg, integer end ;
    permutation{L1, L2}(a, beg, end) ==>
    permutation{L2, L3}(a, beg, end) ==>
    permutation{L1, L3}(a, beg, end);
*/

/*@
predicate last_is_sorted(int *a, integer first, integer last) =
    \forall integer k;
    first <= k <= last ==> a[k] <= a[last];

predicate first_is_sorted(int *a, integer first, integer last) =
    \forall integer k;
    first <= k <= last ==> a[first] <= a[k];
  
predicate sorted(int *a, integer first, integer last) =
\forall integer k;
    first < k < last ==> a[k-1] <= a[k];
*/

/*@
lemma sorted_concat:
\forall int *a, integer s1, e1, s2, e2;
    s2 < e1 && sorted(a, s1, e1) && sorted (a, s2, e2) ==> sorted(a, s1, e2);
*/

/*@
requires n > 0;
requires \valid(arr + (0..n-1));
assigns arr[0..n-1];
ensures sorted(arr, 0, n);
ensures permutation{Pre, Post}(arr, 0, n);
*/
void cocktail_fwd(int *arr, int n) {
    int swapped = 1;
    int start = 0;
    int end = n - 1;

    /*@
    loop assigns start, end, swapped, arr[0..n-1];

    loop invariant swapped ==> 0 <= start <= end <= n-1;
    loop invariant n >= swapped >= 0;

    loop invariant start > 0 ==> first_is_sorted(arr, start-1, end);
    loop invariant end < n-1 ==> last_is_sorted(arr, start, end+1);

    loop invariant sorted(arr, 0, start+1);
    loop invariant sorted(arr, end, n);
    loop invariant !swapped ==> sorted(arr, start, end+1);

    loop invariant permutation{Pre, Here}(arr, 0, n);

    loop variant end - start;
    */
    while (swapped > 0) {
        int i, tmp;

        swapped = 0;

        /*@
        loop assigns i, tmp, swapped, arr[0..end];

        loop invariant 0 <= start <= i <= end <= n-1;
        loop invariant i >= swapped >= 0;

        loop invariant last_is_sorted(arr, start, i);
        loop invariant start > 0 ==> first_is_sorted(arr, start-1, end);
        loop invariant end < n-1 ==> last_is_sorted(arr, start, end+1);

        loop invariant sorted(arr, end+1, n);
        loop invariant sorted(arr, 0, start);

        loop invariant \at(swapped, Here) != \at(swapped, LoopEntry) ==> start < end;
        loop invariant \at(swapped, Here) == \at(swapped, LoopEntry) ==> sorted(arr, start, i+1);

        loop invariant permutation{Pre, Here}(arr, 0, n);

        loop variant end - i;
        */
        for (i = start; i < end; ++i) {
            if (arr[i] > arr[i + 1]) {
                //@ ghost swap_begin1: ;
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
                //@ assert \at(arr[i], LoopCurrent) == \at(arr[i+1], Here);
                //@ assert swap_in_array{swap_begin1, Here}(arr, 0, n, i, i+1);
                //@ assert permutation{swap_begin1, Here}(arr, 0, n);
            }
            /*@ assert \at(swapped, LoopEntry) == \at(swapped, Here) ==>
                        arr[i] <= arr[i+1];
            */
        }

        //@ assert sorted(arr, end, n);
        //@ assert sorted(arr, 0, start+1);

        if (!swapped)
          //@ assert sorted(arr, start, end+1);
          break;

        //@ assert last_is_sorted(arr, start, end);
        //@ assert start < end;

        --end;

        swapped = 0;

        //@ assert end > start-1;

        /*@ 
        loop assigns i, tmp, swapped, arr[start..end];

        loop invariant 0 <= start <= i+1 <= end < n-1;
        loop invariant end - i >= swapped >= 0;

        loop invariant first_is_sorted(arr, i+1, end);
        loop invariant start > 0 ==> first_is_sorted(arr, start-1, end);
        loop invariant end < n-1 ==> last_is_sorted(arr, start, end+1); 

        loop invariant sorted(arr, 0, start);
        loop invariant sorted(arr, end+1, n);

        loop invariant \at(swapped, Here) != \at(swapped, LoopEntry) ==> start < end;
        loop invariant \at(swapped, Here) == \at(swapped, LoopEntry) ==> sorted(arr, i+1, end+1);

        loop invariant permutation{Pre, Here}(arr, 0, n);

        loop variant i - start;
        */
        for (i = end - 1; i >= start; --i) {
            if (arr[i] > arr[i + 1]) {
                //@ ghost swap_begin2: ;
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
                //@ assert \at(arr[i], LoopCurrent) == \at(arr[i+1], Here);
                //@ assert swap_in_array{swap_begin2, Here}(arr, 0, n, i, i+1);
                //@ assert permutation{swap_begin2, Here}(arr, 0, n);
            }
            /*@ assert \at(swapped, LoopEntry) == \at(swapped, Here) ==>
                        arr[i] <= arr[i+1];
            */
        }

        //@ assert first_is_sorted(arr, start, end);
        //@ assert sorted(arr, 0, start+1);
        //@ assert sorted(arr, end, n);

        ++start;

        //@ assert sorted(arr, 0, start+1);
        //@ assert first_is_sorted(arr, start-1, end) ==> arr[start-1] <= arr[start];
    }
}