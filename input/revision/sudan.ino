%HES

G m n r =v DAck1 m n r \/ Ack3 m n (r-1).
S x y z r =μ (x=0 /\ r=y+z) \/ (x>0 /\ z=0 /\ S (x-1) (y+1) 0 r) \/ ∃ r1 r2.(x>0 /\ z>0 /\ S (x-1) r1 (r2+y) r /\ S x y (z-1) r1 /\ S x y z r2).



/*
(x=0 /\ r=y+z) \/ (x>0 /\ z=0 /\ S(x-1,y+1,0,r)) \/ exists r1 r2(x>0 /\ z>0 /\ S(x-1, r1, r2+y, r) /\ S(x,y,z-1,r1) /\ S(x,y,z,r2))
*/