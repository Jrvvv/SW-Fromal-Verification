// Is on other coast
bit boat = 0;
bit wolf = 0;
bit goat = 0;
bit cabb = 0;

#define UNSAFE ((cabb == goat && boat != cabb) || (goat == wolf && boat != goat))

#define SAFE (!UNSAFE)

active proctype man() {
  do
  :: true         -> atomic { printf("alone\n"); boat = 1 - boat };
  :: wolf == boat -> atomic { printf("wolf\n"); boat = 1 - boat; wolf = boat };
  :: goat == boat -> atomic { printf("goat\n"); boat = 1 - boat; goat = boat };
  :: cabb == boat -> atomic { printf("cabb\n"); boat = 1 - boat; cabb = boat };
  od

}

ltl {
  !(SAFE U (boat && wolf && cabb && goat))
}
