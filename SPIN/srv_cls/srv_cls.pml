#define N 3
#define CAP 1

chan server_c = [CAP] of {
    byte /* msg */,
    byte /* client id */
};

chan client_c[N] = [0] of {
    byte /* response */
};

active proctype Server() {
    byte msg;
    byte client;

    do
    :: server_c?msg,client ->
        // assert(client < N);
        printf("Sending to %d\n", client);
        client_c[client]!((msg + 1) % N);
    od
}

proctype Client(byte id) {
    byte msg = 0;

    do
    ::true ->
        Send: skip;
        server_c!msg,id;
        printf("Client %d waiting\n", id);
        client_c[id]?msg;
        Recv: skip;
        // msg = (msg + 1) % N;
    od
}

active proctype watchdog() {
    do
    :: timeout -> assert(false);
    od
}

init {
    int i = 0;
    for (i: 0 .. N-1) {
        run Client(i);
    }
}

ltl {
    [](Client[5]@Send -> <>(Client[5]@Recv))
}