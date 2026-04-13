import Mathlib.FieldTheory.IsAlgClosed.Basic

variable (n : ℕ) (k : Type u) [Field k]

#synth AddCommMonoid (Fin n → k)
#synth Module k (Fin n → k)

abbrev V := (Fin n → k)
-- attribute [reducible] V
-- #check V
-- #synth AddCommMonoid (V (n := n) (k := k))
-- #synth Module k (V (n := n) (k := k))
#synth Module k (V n k)
