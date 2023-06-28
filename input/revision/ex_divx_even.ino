%HES

G x =μ DDivsixI x \/ EvenI x.
EvenI x =μ x=0 \/ (x>0 /\ EvenI (x-2)) \/ (x<0 /\ EvenI (x+2)).
OddI  x =μ (x>0 /\ EvenI (x-1)) \/ (x<0 /\ EvenI (x+1)).
DDivsixI x =v x<>0 /\ (x<=0 \/ DDivsixI (x-6)) /\ (x>=0 \/ DDivsixI (x+6)).
