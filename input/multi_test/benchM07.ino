%HES
G x y r =μ DPlus x y r \/ Minus r x y.
Plus x y z =μ (x=0 /\ y=z) \/ (x>0 /\ Plus (x-1) y (z-1)) \/ (x<0 /\ Plus (x+1) y (z+1)).
DPlus x y z =μ (x<>0 \/ y<>z) /\ (0<=x \/ DPlus (x-1) y (z-1)) /\ (0<=x \/ DPlus (x+1) y (z+1)).
Minus x y z =μ (x=y /\ z=0) \/ (x>y /\ Minus (x-1) y (z-1)) \/ (x<y /\ Minus x (y-1) (z+1)).


/*
	The earliest solution does not work here since the particular disjunct is unsatisfiable.
	The result:
	((Plus{(z,-1,z),(y,0,y),(x,-1,x)}Plus:0)^{m3}.(Plus{(z,1,z),(y,0,y),(x,1,x)}Plus:1)^{m4},(Minus{(z,-1,z),(y,0,y),(x,-1,x)}Minus:0)^{m7}.(Minus{(z,1,z),(y,-1,y),(x,0,x)}Minus:1)^{m8})

	m4: 1
m1: 1
m3: 1
m5: 1
m6: 0
x: 0
x': 0
y: 0
y': 0
r: 0
r': 0
m7: 0
m2: 2
m8: 0

Unfolded goal: ((((x=0 /\ y=r) \/ ((x>0 /\ (((x+(-1))=0 /\ y=(r+(-1))) \/ (((x+(-1))>0 /\ Plus (x+(-2)) y (r+(-2))) \/ ((x+(-1))<0 /\ Plus x y r)))) \/ (x<0 /\ Plus (x+1) y (r+1)))) /\ Minus r x y))

(x>0 /\ (x+(-1))<0 /\ Plus x y r) is unsat
*/
