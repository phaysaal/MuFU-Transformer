%HES

G x =v x<=0 \/ DEvenI x \/ Even x.
Even x =μ   x=0 \/ (x>0 /\ Odd (x-1)).
Odd x =μ  Even (x-1).
DEvenI x =v x<>0 /\ (x<=0 \/ DOddI (x-1))  /\ (x>=0 \/ DOddI (x+1)).
DOddI x =v (x>=0 \/ DEvenI (x+1)) /\ (x>=0 \/ DEvenI (x+1)).

/*
Div6 x -> Even x

Nat x -> Int x

(x>=0 \/ DDivsix (x+6)) /\ 
*/