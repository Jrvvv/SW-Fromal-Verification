/*@ predicate BubleInvMin(int* a, integer start, integer end, integer i) =
(\forall integer k;
      i < k <= end ==> (
        ( (i >= start) &&
          ( (a[i]   <= a[i+1] ==> a[k] >= a[i]) &&
            (a[i+1] <= a[i]   ==> a[k] >= a[i+1]) ) )
        ||
        ( (i == start-1) && (a[k] >= a[i+1]) )
      )
    );
*/



/*@ predicate PredMax(int* a, integer end, integer n) =
        (\forall integer i, j;
                0 <= i <= end < j <= n ==> a[i] <= a[j]);
*/

/*@ predicate PredMaxExpanded(int* a, integer start, integer end, integer n) =
        (\forall integer i, j;
                0 <= start <= i <= end < j <= n ==> a[i] <= a[j]);
*/




/*@ predicate BubleInvMax(int* a, integer start, integer end, integer i) =
(\forall integer k;
      start <= k < i ==> (
        ( (i < end) &&
          ( (a[i]   >= a[i+1] ==> a[k] <= a[i]) &&
            (a[i+1] >= a[i]   ==> a[k] <= a[i+1]) ) )
        ||
        ( (i == end) && (a[k] <= a[i]) )
      )
    );
*/

/*@ predicate BubleAssertMax(int* a, integer start, integer end) =
      (\forall integer k; start <= k <= end ==> a[k] <= a[end]);
*/


/*@ predicate Sorted(int* a, integer start, integer end) =
(\forall integer i, j;
          start <= i <= j <= end ==> a[i] <= a[j]);

@*/


/*@ predicate SuffixDominates(int* a, integer start, integer end, integer n) =
      \forall integer k,t; end < k <= n-1 ==> start <= t <= end ==> a[k] >= a[t];
*/




/*@ predicate BubleAssertMin(int* a, integer start, integer end) =
      (\forall integer k; start <= k <= end ==> a[k] >= a[start]);
*/

/*@ predicate PredMin(int* a, integer start, integer n) =
        (\forall integer i, j;
                0 <= i < start <= j <= n ==> a[i] <= a[j]);
*/


/*@ predicate PredStartElement(int* a, integer start, integer n) =
        (\forall integer i;
                0 <= i < start <= n ==> a[i] <= a[start]);
*/






/*@ requires \valid(arr + (0..n-1));
    requires n > 0;

    assigns arr[0 .. n-1];

    ensures Sorted(arr, 0, n-1);
@*/
void cocktail_back(int *arr, int n) {
    int swapped = 1;
    int start = 0;
    int end = n - 1;
    //@ assert start <= end;


    //@ assert PredMin(arr, start, n-1);

    //@ assert PredMaxExpanded(arr, start, end, n-1);

    //@ assert 0 <= start <= end;

    //@ assert Sorted(arr, 0, start);

    /*@
      loop assigns arr[0 .. n-1], swapped, start, end;
      loop invariant PredMin(arr, start, n-1);
      loop invariant Sorted(arr, 0, start);
      loop invariant Sorted(arr, end, n-1);
      loop invariant PredMax(arr, end, n-1);
      loop invariant (0 <= start <= end <= n-1) || (((end - start) == -1) && (swapped == 0));
      loop invariant swapped >= 0;
      loop invariant (swapped == 0) ==> Sorted(arr, 0, n-1);
      loop variant end;
      @*/
    while (swapped > 0) {
        //@ assert Sorted(arr, 0, start);
        //@ assert Sorted(arr, end, n-1);
        //@ assert PredMaxExpanded(arr, start, end, n-1);
        //@ assert swapped > 0;
        //@ assert (swapped == 0) ==> Sorted(arr, 0, n-1);
        //@ assert start <= end;
        //@ assert PredMin(arr, start, n-1);
        //@ assert PredMax(arr, end, n-1);
        int i, tmp;
        swapped = 0;
        /*@
            loop assigns arr[start .. end], i, tmp, swapped;
            loop invariant BubleInvMin(arr,start, end, i);
            loop invariant PredMaxExpanded(arr, start, end, n-1);
            loop invariant end - 1 >= i >= start-1;
            loop invariant (swapped == 0) ==> Sorted(arr, i+1, end);
            loop invariant swapped >= 0;
            loop invariant Sorted(arr, 0, start);
            loop invariant Sorted(arr, end, n-1);
            loop invariant 0 <= swapped <= end - 1 - i;
            loop invariant 0 <= start <= end;
            loop invariant PredMin(arr, start, n-1);
            loop variant i;
        @*/
        for (i = end - 1; i >= start; --i) {
            //@ assert Sorted(arr, end, n-1);
            //@ assert Sorted(arr, 0, start);
            //@ assert PredMaxExpanded(arr, start, end, n-1);
            //@ assert PredMin(arr, start, n-1);
            //@ assert BubleInvMin(arr,start, end, i);
            //@ assert start <= i + 1 <= end;
            if (arr[i] > arr[i + 1]) {
                //@ assert PredMin(arr, start, n-1);
                //@ assert PredStartElement(arr, start, n-1);
                //@ assert Sorted(arr, 0, start);
                //@ assert PredMaxExpanded(arr, start, end, n-1);
                //@ assert i >= start;
                tmp = arr[i];
                //@ assert PredStartElement(arr, start, n-1);
                //@ assert Sorted(arr, 0, start);
                //@ assert PredMin(arr, start, n-1);
                //@ assert PredMaxExpanded(arr, start, end, n-1);
                //@ assert (end - 1 >= i >= start-1);
                arr[i] = arr[i + 1];
                //@ assert PredStartElement(arr, start, n-1);
                //@ assert PredMin(arr, start, n-1);
                //@ assert PredMaxExpanded(arr, start, end, n-1);
                //@ assert i >= start;
                arr[i + 1] = tmp;
                //@ assert PredMin(arr, start, n-1);
                //@ assert PredMaxExpanded(arr, start, end, n-1);
                //@ assert i >= start;
                //@ assert Sorted(arr, 0, start);
                ++swapped;
                //@ assert PredMin(arr, start, n-1);
                //@ assert (swapped != 0);
                //@ assert PredMaxExpanded(arr, start, end, n-1);
                //@ assert Sorted(arr, 0, start);
                //@ assert BubleInvMin(arr,start, end, i);
                //@ assert Sorted(arr, end, n-1);
            }
            //@ assert Sorted(arr, end, n-1);
            //@ assert Sorted(arr, 0, start);
            //@ assert PredMaxExpanded(arr, start, end, n-1);
            //@ assert PredMin(arr, start, n-1);
            //@ assert i >= start;
            //@ assert BubleInvMin(arr,start, end, i-1);
            //@ assert (swapped == 0) ==> Sorted(arr, i+1, end);
        }
        //@ assert Sorted(arr, end, n-1);
        //@ assert Sorted(arr, 0, start);
        //@ assert start <= end;
        //@ assert PredMaxExpanded(arr, start, end, n-1);
        //@ assert swapped == 0 ==> Sorted(arr, start, end);
        //@ assert BubleAssertMin(arr, start, end);
        //@ assert PredMin(arr, start, n-1);
        //@ assert PredMax(arr, end, n-1);
        //@ assert PredMin(arr, start+1, n-1);

        //@ assert swapped == 0 && Sorted(arr, 0, start) ==> Sorted(arr, 0, end);
        if (!swapped)
            //@ assert Sorted(arr, 0, end);
            //@ assert start <= end;
            //@ assert swapped == 0 ==> Sorted(arr, start, end);
            break;
        ++start;

        //@ assert PredMin(arr, start, n-1);
        //@ assert PredMax(arr, end, n-1);

        //@ assert start <= end;

        //@ assert Sorted(arr, 0, start);
        //@ assert Sorted(arr, end, n-1);

        swapped = 0;

        /*@
            loop assigns arr[start .. end], i, tmp, swapped;
            loop invariant BubleInvMax(arr,start, end, i)  &&  end >= i >= start;
            loop invariant PredMin(arr, start, n-1);
            loop invariant Sorted(arr, 0, start);
            loop invariant Sorted(arr, end, n-1);
            loop invariant PredMax(arr, end, n-1);
            loop invariant (swapped == 0) ==> Sorted(arr, start, i);
            loop invariant swapped >= 0;
            loop invariant 0 <= swapped <= i - start;
            loop variant end - i + 1;
        @*/


        for (i = start; i < end; ++i) {
            //@ assert PredMax(arr, end, n-1);
            //@ assert Sorted(arr, 0, start);
            //@ assert Sorted(arr, end, n-1);
            //@ assert (end >= i >= start);
            //@ assert BubleInvMax(arr,start, end, i);
            if (arr[i] > arr[i + 1]) {
                //@ assert Sorted(arr, end, n-1);
                //@ assert PredMax(arr, end, n-1);
                tmp = arr[i];
                //@ assert (end >= i >= start);
                arr[i] = arr[i + 1];
                //@ assert PredMax(arr, end, n-1);
                arr[i + 1] = tmp;
                //@ assert PredMax(arr, end, n-1);

                ++swapped;
                //@ assert (swapped != 0);
                //@ assert Sorted(arr, 0, start);
                //@ assert Sorted(arr, end, n-1);
            }
            //@ assert PredMax(arr, end, n-1);
            //@ assert BubleInvMax(arr,start, end, i+1);
            //@ assert (swapped == 0) ==> Sorted(arr, start, i);
            //@ assert Sorted(arr, end, n-1);
        }
        //@ assert swapped >= 0;
        //@ assert Sorted(arr, end, n-1);
        //@ assert Sorted(arr, 0, start);
        //@ assert (swapped == 0) ==> Sorted(arr, start, end);
        //@ assert Sorted(arr, 0, start) && Sorted(arr, start, end) &&  Sorted(arr, end, n-1) ==> Sorted(arr, 0, n-1);

        //@ assert (swapped == 0) ==> Sorted(arr, start, end) ==> Sorted(arr, 0, start) && Sorted(arr, start, end) &&  Sorted(arr, end, n-1) ==>Sorted(arr, 0, n-1);

        //@ assert swapped < 0 ==> Sorted(arr, 0, n-1);
        //@ assert (start <= end);
        //@ assert (start == end) ==> (swapped == 0);
        //@ assert BubleAssertMax(arr,start, end);
        //@ assert PredMax(arr, end, n-1);

        //@ assert PredMax(arr, end-1, n-1);

        --end;
        //@ assert (swapped == 0) ==> Sorted(arr, 0, n-1);
        //@ assert swapped <= 0 ==> Sorted(arr, 0, n-1);
        //@ assert (start <= end) || (((end - start) == -1) && (swapped == 0)) ;

    }
    //@ assert swapped <= 0;
    //@ assert Sorted(arr, end, n-1);
    //@ assert Sorted(arr, 0, start);
    //@ assert Sorted(arr, 0, n-1);
}