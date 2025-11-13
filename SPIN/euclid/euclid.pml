proctype euclid(int a, b) {
  int x = a, y = b;
  do
  :: x < y -> y = y - x;
  :: x > y -> x = x - y;
  :: else -> break;
  od

  printf("GCD(%d, %d) = %d\n", a, b, x);

}

init {
  run euclid(17*9, 17*5);
}