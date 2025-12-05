// Положение объектов: 0 = левый берег, 1 = правый берег
bit boat = 0;
bit father = 0;
bit son1 = 0;
bit son2 = 0;

active proctype main() {
    do
    :: // Отец плывет один (вес 200 = грузоподъемность)
       boat == father ->
           atomic {
               father = 1 - father;
               boat = 1 - boat;
               printf("Отец переплывает один\n");
           }

    :: // Сын1 плывет один (вес 100) - только если отец на том же берегу
       boat == son1 ->
           atomic {
               son1 = 1 - son1;
               boat = 1 - boat;
               printf("Сын1 переплывает один\n");
           }

    :: // Сын2 плывет один (вес 100) - только если отец на том же берегу
       boat == son2 ->
           atomic {
               son2 = 1 - son2;
               boat = 1 - boat;
               printf("Сын2 переплывает один\n");
           }

    :: // Оба сына плывут (вес 100+100=200 = грузоподъемность)
       boat == son1 && boat == son2 ->
           atomic {
               son1 = 1 - son1;
               son2 = 1 - son2;
               boat = 1 - boat;
               printf("Оба сына переплывают вместе\n");
           }
    od
}

// Спецификация LTL: проверяем, что трое НЕ могут оказаться на другом берегу
ltl goal {
    !(true U (father == 1 && son1 == 1 && son2 == 1))
}