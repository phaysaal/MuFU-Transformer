%HES

/* Y =μ ∀ a.∀ b.∀ c.∀ d.(a>=b \/ b>=c) \/ X a b c \/ Z a b c. */
Y a b c =μ (a>=b \/ b>=c) \/ X a b c \/ Z a b c.
X a b c =μ (a<b /\ X a (b-1) c) \/ (b<c /\ X a b (c-1)) \/ (a=b /\ a=c).
Z a b c =μ Z a (b-1) c /\ Z a b (c-1).