%HES

G =μ ∀ x.DEvenI x \/ Even x.
DEvenI x =μ x<>0 /\ (x<=0 \/ DOddI (x-1)) /\ (x>=0 \/ DOddI (x+1)).
DOddI  x =μ (x<=0 \/ DEvenI (x-1)) /\ (x>=0 \/ DEvenI (x+1)).
Even x =μ x=0 \/ Even (x-2).

