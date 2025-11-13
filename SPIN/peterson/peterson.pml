bool flag[2] = 0;
byte turn = 0;

active [2] proctype p() {
  byte i = _pid;
  assert (i == 0 || i == 1);

  //Non-Critical Section
  NCS:
  printf("NCS %d\n", i);

  SET:
  flag[i] = 1;
  turn = i;

  TST:
  !(flag[1 - i] == 1 && turn == i);

  // Critical Section
  CRS:
  printf("CRS %d\n", i);

  RST:
  flag[i] = 0;

  if
  :: goto NCS;
  :: skip;
  fi
}

ltl mutex {
  [](!(p[0]@CRS && p[1]@CRS)) && [](p[0]@SET -> <>(p[0]@CRS)) && [](p[1]@SET -> <>(p[1]@CRS))
}

// spin -run peterson.pml
// !!! trail file to check error
// spin -t peterson.pml
// ./pan -a
// ./pan -a -p