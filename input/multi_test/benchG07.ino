%HES
X x =μ DEven x \/ Even x.
Even x =μ x=0 \/ (x>0 /\ DEven (x-1)) \/ (x<0 /\ DEven (x+1)).
DEven x =v x<>0 /\ (x<=0 \/ Even (x-1)) /\ (x>=0 \/ Even (x+1)).

/*
Even x /\ Plus x 1 y -> DEven y 
DEven x \/ DPlus x 1 y \/ DEven y
Fails
*/