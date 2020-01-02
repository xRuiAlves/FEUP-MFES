bool b1 = 0;
bool b2 = 0;
bool c1 = 0;
bool c2 = 0;
int x = 0;

#define w1 (b1 == 1 && c1 == 0)
#define w2 (b2 == 1 && c2 == 0)

proctype P1() {
    do ::
        true -> skip; 
        atomic {
            b1 = 1;
            x = 2;
        };
        if 
            :: (x == 1 || b2 == 0) -> c1 = 1;
        fi;
        atomic {
            b1 = 0;
            c1 = 0;
        }
    od;
}

proctype P2() {
    do ::
        true -> skip; 
        atomic {
            b2 = 1;
            x = 1;
        };
        if 
            :: (x == 2 || b2 == 0) -> c2 = 1;
        fi;
        atomic {
            b2 = 0;
            c2 = 0;
        }
    od;
}

init {
    atomic {
        run P1();
        run P2();
    }
}

ltl R1 { [](!(c1 && c2)) }
ltl R2 { ([]<>c1) && ([]<>c2) }
ltl R3 { []((w1 -> <>c1) && (w2 -> <>c2)) }
ltl R4 { (([]<>w1) -> ([]<>c1)) && (([]<>w2) -> ([]<>c2)) }