import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.EuclideanDomain.Defs

variable {F K : Type _} [Field F] [Field K] [Algebra F K]

open Polynomial

theorem minpoly_from_monic_irreducible (f : F[X]) (hm : Monic f) (hi : Irreducible f)
    {x : K} (hx : aeval x f = 0) : minpoly F x = f := by
  have hf_ne_one : f ≠ 1 := by
    intro hf_one
    simp only [hf_one, map_one, one_ne_zero] at hx
  let Q := minpoly F x
  have hQ_ne_one : Q ≠ 1 := minpoly.ne_one F x
  have hQ_monic : Q.Monic := minpoly.monic ⟨f, hm, hx⟩
  have hQ_dvd : Q ∣ f := minpoly.dvd F x hx
  obtain ⟨R, hR⟩ := hQ_dvd
  have hR_monic : R.Monic := by
    apply (Monic.def).mpr
    have hf_lc_1 : f.leadingCoeff = 1 := Monic.leadingCoeff hm
    rw [hR, Polynomial.leadingCoeff_monic_mul hQ_monic] at hf_lc_1
    exact hf_lc_1
  have h_iff := (Polynomial.irreducible_of_monic hm hf_ne_one).mp
  have hQR_eq_1 : Q = 1 ∨ R = 1 := h_iff hi Q R hQ_monic hR_monic hR.symm
  have hR_eq_1 : R = 1 := by
    simp only [hQ_ne_one, false_or] at hQR_eq_1
    exact hQR_eq_1
  rw [hR_eq_1, mul_one] at hR
  exact hR.symm
