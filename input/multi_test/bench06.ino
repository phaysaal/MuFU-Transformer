%HES
X x y =μ DEven x \/ DPlus x 1 y \/ DEven y.
Plus x y z =μ (x=0 /\ y=z) \/ (x>0 /\ Plus (x-1) y (z-1)) \/ (x<0 /\ Plus (x+1) y (z+1)).
DPlus x y z =v (x<>0 \/ y<>z) /\ (x<=0 \/ DPlus (x-1) y (z-1)) \/ (x>=0 \/ DPlus (x+1) y (z+1)).
Even x =μ x=0 \/ (x>0 /\ Even (x-2)) \/ (x<0 /\ Even (x+2)).
DEven x =v x<>0 /\ (x<=0 \/ DEven (x-2)) /\ (x>=0 \/ DEven (x+2)).

/*
Even x /\ Plus x 1 y -> DEven y 
DEven x \/ DPlus x 1 y \/ DEven y
Fails
*/