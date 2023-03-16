%HES
X x y =μ DPlus x x y \/ Even y.
Plus x y z =μ (x=0 /\ y=z) \/ (x>0 /\ Plus (x-1) y (z-1)) \/ (x<0 /\ Plus (x+1) y (z+1)).
DPlus x y z =v (x<>0 \/ y<>z) /\ (x<=0 \/ DPlus (x-1) y (z-1)) \/ (x>=0 \/ DPlus (x+1) y (z+1)).
Even x =μ x=0 \/ (x>0 /\ Even (x-2)) \/ (x<0 /\ Even (x+2)).
DEven x =v x<>0 /\ (x<=0 \/ DEven (x-2)) /\ (x>=0 \/ DEven (x+2)).

/*
Plus x x y -> Even y 
DPlus x x y \/ Even y
Fails
*/