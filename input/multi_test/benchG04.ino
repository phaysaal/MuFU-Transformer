%HES
X x y z =μ Even z \/ DPlus x y z \/ DEven x \/ DEven y.
Plus x y z =μ (x=0 /\ y=z) \/ (x>0 /\ Plus (x-1) y (z-1)) \/ (x<0 /\ Plus (x+1) y (z+1)).
DPlus x y z =v (x<>0 \/ y<>z) /\ (x<=0 \/ DPlus (x-1) y (z-1)) \/ (x>=0 \/ DPlus (x+1) y (z+1)).
Even x =μ x=0 \/ (x>0 /\ DEven (x-1)) \/ (x<0 /\ Even (x+2)).
DEven x =v x<>0 /\ (x<=0 \/ Even (x-1)) /\ (x>=0 \/ DEven (x+2)).

/*
Fails to fold
*/