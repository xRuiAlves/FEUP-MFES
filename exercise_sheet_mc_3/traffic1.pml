mtype = { red, green, yellow };
mtype light = red;

#define g (light==green)
#define y (light==yellow)
#define r (light==red)

active proctype TrafficLight(){
	do
	:: 	if
			:: light == red -> light = green
			:: light == green -> light = yellow
			:: light == yellow -> light = red
		fi
		
		printf("light %e\n", light);
	od
}

ltl P0 { []<>g }
ltl P1 { [](g || y || r) }
ltl P2 { [](y -> <>r) }