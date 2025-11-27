#define BUFFER_SIZE 3
#define INVALID_SEQ 255
#define INVALID_MSG 255

// data channel
chan d = [1] of {
    byte /* data */,
    bool /* error */,
    byte /* seq */
};

// acknowledgement channel
chan a = [1] of {
    bool /* error */,
    byte /* seq */
};

byte send_msg = 0;
byte send_seq = 0;

byte recv_msg = INVALID_MSG;
byte send_ack = INVALID_SEQ;

active proctype P() {
    bool error;
    byte recv_seq;

    do
    :: d!send_msg,0,send_seq ->
       Send: printf("P: send: %d", send_msg);
    :: a?error,recv_seq ->
        if
        :: error
        :: !error && recv_seq == send_seq ->
            send_seq = 1 - send_seq;
            send_msg = (send_msg + 1) % BUFFER_SIZE;
        :: else
        fi
    od
}

active proctype Q() {
    byte error;
    byte recv_seq;

    do
    :: send_ack != INVALID_SEQ -> a!0,send_ack
    :: d?recv_msg,error,recv_seq -> Recv:
        if
        :: !error ->
            RecvOk: printf("Recv: %d", recv_msg);
            send_ack = recv_seq;
        :: else
        fi
    od
}

active proctype d_media() {
    do
    :: true -> Loss:
        printf("D loss\n");
        d?_,_,_;
    :: true -> Corruption:
        atomic {
            printf("D corruption\n");
            d?_,0,_;
            d!INVALID_MSG,1,INVALID_SEQ;
        };
    :: true -> Normal:
        atomic {
            printf("D normal\n");
            d?<_,0,_>;
            empty(d);
        };
    od
}

active proctype a_media() {
    do
    :: true -> Loss:
        printf("A loss\n");
        a?_,_;
    :: true -> Corruption:
        atomic {
            printf("A corruption\n");
            a?0,_;
            a!1,INVALID_SEQ;
        };
    :: true -> Normal:
        atomic {
            printf("A normal\n");
            a?<0,_>;
            empty(a);
        };
    od
}

active proctype watcdog() {
    do
    :: timeout -> assert(false)
    od
}

#define LINK_ALIVE(c) []<>(c##_media@Normal)

ltl {
    (LINK_ALIVE(d) && LINK_ALIVE(a)) ->
        []((P@Send & <>(Q@Recv))-> <>(Q@Recv && (recv_msg == send_msg)))
}