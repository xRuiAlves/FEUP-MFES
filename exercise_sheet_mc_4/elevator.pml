//floor indicates which floor the elevator is
byte floor=1;

//doorisopen[i]==1 if the door of floor i is open
bit doorisopen[3];

// rendezvous between the cabin and the floor door:byte is the floor number and
// bit is 1 if the door is open, and 0 if it is closed
chan openclosedoor=[0] of {byte,bit};

//waits for elevator to allow door open in floor i
//opens the door (bit 1)
//closes the door (bit 0)
//sends message to elevator
proctype door(byte i) {
    do ::
        printf("XX - Door %d awaiting to open\n", i);
        openclosedoor?eval(i),1;
        printf("XX - Door %d OPENING!\n", i);
        doorisopen[i-1]=1;
        doorisopen[i-1]=0;
        openclosedoor!i,0;
    od
}

//cabin goes up or down or stays or floor door opens and closes
proctype elevator() {
    do
        :: (floor!=3)-> 
            printf("Going UP from floor %d to %d\n", floor, floor + 1);
            moveup: floor++;
        :: (floor!=1)-> 
            printf("Going DOWN from floor %d to %d\n", floor, floor - 1);
            movedown: floor--;
        :: 
            printf("Going for DOOR OPENING in floor %d\n", floor);
            openclosedoor!floor,1;
            openclosedoor?eval(floor),0
    od
}

init {
    atomic {
        run door(1);
        run door(2);
        run door(3);
        run elevator();
    }
}

#define open1 doorisopen[0]
#define closed1 !open1
#define open2 doorisopen[1]
#define closed2 !open2
#define open3 doorisopen[2]
#define closed3 !open3
#define open (open1 || open2 || open3)
#define floor1 (floor == 1) 
#define floor2 (floor == 2)
#define floor3 (floor == 3)

ltl R1 { [](open1 -> <> closed1) }
ltl R2 { []((!floor1 -> !open1) && (!floor2 -> !open2) && (!floor3 -> !open3))}
ltl R3 { [](open -> (!elevator@movedown && elevator@moveup)) }
ltl R4 { <>open }
ltl R5 { []<>(!floor1)}