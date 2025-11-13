bool boat = 1; // Boat is on the left shore

int m_l = 3;
int c_l = 3;

#define UNSAFE ((m_l && (c_l > m_l)) || ((3-m_l) && ((3-c_l) > (3-m_l))))
#define SAFE !UNSAFE

inline move_one_kind(x, n) {
  atomic {
    x = (boat -> x - n : x + n);
    boat = !boat;
  }
}

inline move_both() {
  atomic {
    m_l = (boat -> m_l - 1 : m_l + 1);
    c_l = (boat -> c_l - 1 : c_l + 1);
    boat = !boat;
  }
}

inline can_move_one(x, n) {
  (boat -> (x >= n) : ((3-x) >= n)) && (n > 0) && (n <= 2)
}

inline can_move_both() {
  (boat -> (m_l >= 1 && c_l >= 1) : ((3-m_l) >= 1 && (3-c_l) >= 1))
}

inline debug() {
  printf("Missionaries: %d %d\n", m_l, 3 - m_l);
  printf("Cannibals: %d %d\n", c_l, 3 - c_l);
}

active proctype main() {
  do
  :: can_move_both() -> move_both(); printf("Move both\n"); debug();
  :: can_move_one(m_l, 1) -> move_one_kind(m_l, 1); printf("Move 1 Missionary\n"); debug();
  :: can_move_one(m_l, 2) -> move_one_kind(m_l, 2); printf("Move 2 Missionaries\n"); debug();
  :: can_move_one(c_l, 1) -> move_one_kind(c_l, 1); printf("Move 1 Cannibal\n"); debug();
  :: can_move_one(c_l, 2) -> move_one_kind(c_l, 2); printf("Move 2 Cannibals\n"); debug();
  od
}

ltl {
  !(SAFE U (m_l == 0 && c_l == 0))
}
