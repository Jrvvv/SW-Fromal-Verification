// 1. Run
// 2. Split All
// 3. Run
// 4. Split All
// 5. Run
// 6. Run the last not proven assert
// Timeout: 30 sec
// Mem: 5 GB

/*@ predicate PredMin(int* a, integer start, integer n) =
        (\forall integer i, j;
                0 <= i < start <= j <= n ==> a[i] <= a[j]);
*/

/*@ predicate PredMax(int* a, integer end, integer n) =
        (\forall integer i, j;
                0 <= i <= end < j <= n ==> a[i] <= a[j]);
*/


/*@
predicate sorted{L}(int* a, integer beg, integer end) =
    \forall integer i, j; beg <= i <= j < end ==> a[i] <= a[j];

 predicate all_smaller_than_the_last (int* a, integer start_index, integer end_index) =
   \forall integer k1;
    start_index <= k1 < end_index ==> a[k1] <= a[end_index];

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
lemma sorted_concat:
    \forall int* a, integer x, y, z;
    0 <= x <= y <= z &&
    sorted(a, x, y) && sorted(a, y, z) && a[y-1] <= a[y] ==> sorted(a, x, z);

lemma sorted_triple_concat:
    \forall int* a, integer b1, b2, b3, b4;
    0 <= b1 <= b2 <= b3 <= b4 &&
    sorted(a, b1, b4) &&
    sorted(a, b1, b2) &&
    sorted(a, b3, b4) &&
    a[b2-1] <= a[b2] &&
    a[b3-1] <= a[b3] ==> sorted(a, b2, b3);
*/

/*@
requires 1 < n <= 2147483647;
requires \valid(arr + (0 .. n-1));
assigns arr[0 .. n-1];
ensures sorted{Here}(arr, 0, n);
ensures permutation{Pre, Post}(arr, 0, n);
*/
void cocktail_fwd(int *arr, int n) {
    //@ ghost int first_swap_fw_i = 0;
    //@ ghost int first_swap_bw_i = 0;
    int swapped = 1;
    int start = 0;
    int end = n - 1;

    /*@
    loop assigns arr[0 .. n-1], start, end, swapped;

    loop invariant 0 <= start <= end+1 <= n;
    loop invariant 0 <= swapped <= n-1;

    loop invariant sorted(arr, 0, start);
    loop invariant sorted(arr, end+1, n);

        loop invariant \forall integer i;
                (start != 0 && 0 <= i <= end) ==> arr[i] <= arr[end + 1];

        loop invariant \forall integer i;
                (start != 0 && start <= i < n) ==> arr[start - 1] <= arr[i];

        loop invariant end + 1 < n ==> \forall integer i; 
                0 <= i <= end ==> arr[i] <= arr[end + 1];

        loop invariant start == 0 || 
            \forall integer j; start <= j < n ==> arr[start-1] <= arr[j];

        loop invariant \forall integer k; start <= k <= n ==> 
            (start == 0 || arr[start-1] <= arr[k]);

    loop invariant swapped == 0 ==> sorted(arr, 0, n);

    loop invariant (swapped == 0) && (start <= end) ==> sorted(arr, start, end+1);

    loop invariant permutation{Pre, Here}(arr, 0, n);

    loop variant end - start + 1;

    */
    while (swapped > 0) {
        int i, tmp;
        //@ ghost fwd_begin: ;
        swapped = 0;
        //@ ghost first_swap_fw_i = 0;
        //@ ghost first_swap_bw_i = 0;

        /*@
        loop assigns i, swapped, arr[start .. end];
        loop invariant 0 <= start <= i <= end <= n-1 || (i == start && start > end);
        loop invariant 0 <= swapped <= i - start;

        loop invariant end + 1 < n ==> \forall integer i; 
                0 <= i <= end ==> arr[i] <= arr[end + 1];

        loop invariant start == 0 || 
            \forall integer j; start <= j < n ==> arr[start-1] <= arr[j];

        //loop invariant sorted(arr, 0, start);
        //loop invariant sorted(arr, end+1, n);

        loop invariant permutation{Pre, Here}(arr, 0, n);

        loop variant end - i;
        */
        for (i = start; i < end; ++i) {
            //@ ghost fwd_entry: ;
            if (arr[i] > arr[i + 1]) {
                //@ ghost swap_begin1: ;
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
                //@ ghost first_swap_fw_i = (swapped == 1) ? i : first_swap_fw_i;
                //@ assert swap_in_array{swap_begin1, Here}(arr, 0, n, i, i+1);
                //@ assert permutation{swap_begin1, Here}(arr, 0, n);
            }
            /*@ assert \at(swapped, fwd_entry) == \at(swapped, Here) ==>
                        arr[i] <= arr[i+1];
            */
        }

        //@ assert sorted(arr, 0, start);
        //@ assert sorted(arr, end+1, n);
        // assert swapped == 0 ==> sorted(arr, start, end+1);


        if (!swapped)
            //@ assert swapped == 0;
            //@ assert swapped == 0 ==> sorted(arr, 0, n);
            //@ assert sorted(arr, 0, start);
            //@ assert sorted(arr, start, end+1);
            //@ assert sorted(arr, end+1, n);
            //@ assert sorted(arr, 0, n);
            break;
        --end;

        //@ ghost bwd_begin: ;
        swapped = 0;

        /*@
        loop assigns i, swapped, arr[start .. end];
        loop invariant start-1 <= i <= end-1;
        loop invariant 0 <= swapped <= end - 1 - i;

        loop invariant start == 0 || 
            \forall integer j; start <= j < n ==> arr[start-1] <= arr[j];

        loop invariant \forall integer k; start <= k <= i ==> 
            (start == 0 || arr[start-1] <= arr[k]);

        loop invariant permutation{Pre, Here}(arr, 0, n);

        loop variant i - start + 1;
        */
        
        for (i = end - 1; i >= start; --i) {
            //@ ghost bwd_entry: ;
            if (arr[i] > arr[i + 1]) {
                //@ ghost swap_begin2: ;
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
                //@ ghost first_swap_bw_i = (swapped == 1) ? i : first_swap_bw_i;
                //@ assert swap_in_array{swap_begin2, Here}(arr, 0, n, i, i+1);
                //@ assert permutation{swap_begin2, Here}(arr, 0, n);
            }
            /*@ assert \at(swapped, bwd_entry) == \at(swapped, Here) ==>
                        arr[i] <= arr[i+1];
            */
        }

        //@ assert \forall integer i; start <= i <= end ==> (start == 0 || arr[start-1] <= arr[i]);

        //@ assert sorted(arr, 0, start);
        //@ assert sorted(arr, end+1, n);
        //@ assert swapped == 0 ==> sorted(arr, start, end+1);

        ++start;

    }

}
