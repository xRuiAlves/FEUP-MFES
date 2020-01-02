mtype = { green, yellow, red };
mtype light[2] = {red, red}
int turn = 0;

active [2] proctype P() {
    bit my_id = _pid;
    bit other_id = 1 - my_id;
    do
        :: (turn == my_id && light[my_id] == red) -> light[my_id] = green;
        :: (turn == my_id && light[my_id] == green) -> light[my_id] = yellow;
        :: (turn == my_id && light[my_id] == yellow) -> 
            light[my_id] = red;
            turn = other_id;
    od
}

ltl P0 { [](!(light[0] == green && light[1] == green)) }
ltl P1 { ([]<>(light[0] == green)) && ([]<>(light[1] == green)) }