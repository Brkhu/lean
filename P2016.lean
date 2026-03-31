import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Minpoly.Basic

open scoped Rat

abbrev S : Set ℝ := { α |
  ∀ n : ℕ, n > 0 → ∀ (G₁ G₂ G₃ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel G₃.Adj], (G₁ ⊔ G₂ ⊔ G₃).minDegree ≥ α * n →
      ∃ v₁ v₂ v₃, ∀ w, G₁.Reachable w v₁ ∨ G₂.Reachable w v₂ ∨ G₃.Reachable w v₃ }

def answer : List ℚ := [1, -7 /. 8]
theorem P₂₀₁₆ : ∃ min, IsLeast S min ∧ (minpoly ℚ min).coeffList = answer := by sorry
