#define DISKS_NUM (5)
#define RODS_NUM  (3)

typedef Rod {
  byte stack[DISKS_NUM];
  byte count;
}

Rod rods[RODS_NUM];

#define TOP(idx) rods[idx].stack[rods[idx].count - 1]
#define IS_EMPTY(idx) (rods[idx].count == 0)


inline is_valid(i, j) {
  !IS_EMPTY(i) && (!IS_EMPTY(j) || TOP(j) > TOP(i));
}

inline move(i, j) {
  atomic {
    rods[j].count++;
    TOP(j) = TOP(i);
    rods[i].count--;
  }
}

proctype hanoi() {
  do
  :: is_valid(0, 1) -> atomic { printf("0 -> 1"); move(0, 1) };
  :: is_valid(0, 2) -> atomic { printf("0 -> 2"); move(0, 2) };
  :: is_valid(1, 0) -> atomic { printf("1 -> 0"); move(1, 0) };
  :: is_valid(1, 2) -> atomic { printf("1 -> 2"); move(1, 2) };
  :: is_valid(2, 0) -> atomic { printf("2 -> 0"); move(2, 1) };
  :: is_valid(2, 1) -> atomic { printf("2 -> 1"); move(2, 0) };
  od
}

ltl {
  !<>(rods[2].count == DISKS_NUM);
}

init {
  int i;
  int end = DISKS_NUM-1;

  for (i: 0..end) {
    rods[0].stack[i] = DISKS_NUM - i;
  }

  rods[0].count = DISKS_NUM;
  rods[1].count = 0;
  rods[2].count = 0;

  run hanoi();
}