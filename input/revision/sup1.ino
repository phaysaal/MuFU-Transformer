%HES

A x y =μ DG x y \/ F x y.
F x y =μ (x=0 /\ x=y) \/ (x>0 /\ x<10 /\ F (x-1) (y-1)) \/ (x > 9 /\ F (x-1) (y-1)).
G x y =μ (x=0 /\ x=y) \/ (x>0 /\ G (x-1) (y-1)).
DG x y =μ (x<>0 \/ x<>y) /\ (x<=0 \/ DG (x-1) (y-1)).


/*
//(x=0 /\ y=x+x) \/ (x<0 /\ Abs2 (x+1) (y+1)) \/ (x>0 /\ Abs2 (x-1) (y+1)).
(x=0 /\ r=y+z) \/ (x>0 /\ z=0 /\ S(x-1,y+1,0,r)) \/ exists r1 r2(x>0 /\ z>0 /\ S(x-1, r1, r2+y, r) /\ S(x,y,z-1,r1) /\ S(x,y,z,r2))
*/