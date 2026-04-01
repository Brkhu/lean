-- import Brkhu.P6011.YTheta

-- set_option linter.style.emptyLine false

-- open NumberField


-- for discr and resultants of polynomials
import Mathlib.RingTheory.Polynomial.Resultant.Basic
-- for irreducible_iff_roots_eq_zero_of_degree_le_three
import Mathlib.Algebra.Polynomial.SpecificDegree
-- for Gauss's lemma
import Mathlib.RingTheory.Polynomial.GaussLemma

import Mathlib.NumberTheory.NumberField.Discriminant.Defs

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown


open Polynomial


variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

#check PowerSeries.invUnitsSub
#check PowerSeries.coeff_invUnitsSub

noncomputable def power_base (x : B) (n : ℕ) : Fin n → B := fun k => x ^ k.val

theorem power_base_apply (x : B) (n : ℕ) (k : Fin n) : power_base x n k = x ^ k.val :=
  rfl

noncomputable def hankel_matrix (x : B) (n : ℕ) := Matrix.of
  fun (i j : Fin n) ↦ (Algebra.trace A B) (x ^ (i.val + j.val))

theorem hankel_matrix_apply (x : B) (n : ℕ) (i j : Fin n) :
  hankel_matrix x n i j = (Algebra.trace A B) (x ^ (i.val + j.val)) := rfl

theorem power_base_trace_matrix (x : B) (n : ℕ) :
    Algebra.traceMatrix A (power_base x n) = hankel_matrix x n := by
  ext i j
  dsimp only [Algebra.traceMatrix_apply, hankel_matrix_apply, power_base_apply,
    Algebra.traceForm_apply, Matrix.of_apply]
  congr
  rw [← pow_add]

theorem power_base_discr_eq_minpoly_discr (x : B) (f : A[X]) (hf_monic : Monic f)
    (hf_root : aeval x f = 0) :
    Algebra.discr A (power_base x f.natDegree)
    = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  dsimp [Algebra.discr]
  rw [power_base_trace_matrix]

  -- rw [← pow_add x _ _]
  -- rw [power_base_def x f.natDegree (i : Fin f.natDegree)]

  sorry


-- def sylvester (f g : R[X]) (m n : ℕ) : Matrix (Fin (m + n)) (Fin (m + n)) R :=
--   .of fun i j ↦ j.addCases
--     (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + n) then g.coeff (i - j₁) else 0)
--     (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + m) then f.coeff (i - j₁) else 0)

-- b0       a0
-- b1 b0    a1 a0
-- bn b1 b0 am a1 a0
--    bn b1    am a1
--       bn       am

-- a0    a1
-- a1 a0 2a2     a1
-- .. a1 ..      2a2
-- an .. na(n-1) ..
--    an         na(n-1)

-- f xf ... x^{n-2}f f' xf' ... x^{n-1}f'

-- a0    b0
-- a1 a0 b1 b0
-- a2 a1 b2 b1 b0
-- a3 a2    b2 b1
--    a3       b2
