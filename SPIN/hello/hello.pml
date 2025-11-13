#define N (5)

active [N] proctype main() {
  printf("Hello, world %d\n", _pid);
}

init {
  run main();
}
