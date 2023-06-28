%HES

Y =μ ∀ a.∀ b.∀ c.∀ d.X a b c d \/ Z a b c d.
/* Y a b c d =μ X a b c d \/ Z a b c d. */
X a b c d =μ (a<b /\ X a (b-1) c d) \/ (b<c /\ X a b (c-1) d) \/ (d=a+b+c).
Z a b c d =μ (a<b /\ b<c /\ Z a (b-1) (c-1) d) \/ (a<b /\ Z a (b-1) c d