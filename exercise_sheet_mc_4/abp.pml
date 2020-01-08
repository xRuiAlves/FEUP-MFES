mtype = { msg0, msg1, ack0, ack1 }
chan sender = [1] of { mtype }
chan receiver = [1] of { mtype }

active proctype Sender() {
    do
    :: if
       :: receiver?msg0;
       :: skip
       fi;
       do
       :: sender?ack0 -> break
       :: sender?ack1
       :: timeout ->
send0:     if
           :: receiver!msg0;
           :: skip
           fi;
       od;
    :: if
       :: receiver?msg1;
       :: skip
       fi;
       do
       :: sender?ack1 -> break
       :: sender?ack0
       :: timeout ->
send1:    if
          :: receiver!msg1;
          :: skip
          fi;
        od;
    od
}

active proctype Receiver() {
    do
    :: do
       :: receiver?msg0 -> sender!ack0; break
       :: receiver?msg1 -> sender!ack1
       od;
       do
       :: receiver?msg1 -> sender!ack1; break
       :: receiver?msg0 -> sender!ack0
       od
    od
}

#define smsg0 (receiver?[msg0])
#define smsg1 (receiver?[msg1])
#define rmsg0 (sender?[ack0])
#define rmsg1 (sender?[ack1])
#define send0 Sender@send0
#define send1 Sender@send1
#define send (send0 || send1)

ltl P00 { [](smsg0 -> <>smsg1) }
ltl P01 { [](smsg1 -> <>smsg0) }

ltl P10 { []<>smsg0 -> []<>rmsg0 }
ltl P11 { []<>smsg1 -> []<>rmsg1 }

ltl P20 { [](send0 -> <>rmsg0) }
ltl P21 { [](send1 -> <>rmsg1) }