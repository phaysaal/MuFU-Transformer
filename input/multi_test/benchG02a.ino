%HES
X x y =μ LE x y \/ NLE x y.
LE x y =μ x=0 \/ (y=0 /\ y>(x-1)) \/ (y<>0 /\ LE (x-1) (y-1)) \/ (y<0 /\ LE (x+1) (y+1)).
NLE x y =v x<>0 /\ (y<>0 \/ y<=(x-1)) /\ (y=0 \/ NLE (x-1) (y-1)) /\ (y>=0 \/ NLE (x+1) (y+1)).
