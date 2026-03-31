import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Minpoly.Basic


import Mathlib.Algebra.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.Rat
import Mathlib.Tactic.LinearCombination'
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.Divisors

open scoped Rat
open Polynomial

noncomputable def theta : ℝ := (2 * Real.pi / 9).cos
noncomputable def P : ℚ[X] := X^3 - C (3/4) * X + C (1/8)


lemma nonzero_P : P ≠ 0 := by
  intro h
  have coeff_zero : P.coeff 3 = 0 := by rw [h, coeff_zero]
  simp only [P] at coeff_zero
  norm_num at coeff_zero

lemma nonone_P : P ≠ 1 := by
  intro h
  have coeff_one : P.coeff 3 = 0 := by rw [h, coeff_one, if_neg (by norm_num)]
  simp only [P] at coeff_one
  norm_num at coeff_one

lemma degree_P : P.degree = 3 := by
  have hdegPleq3 : P.degree ≤ 3 := by
    let M1 : ℚ[X] := monomial 3 1
    let M2 : ℚ[X] := monomial 1 (-3/4)
    let M3 : ℚ[X] := monomial 0 (1/8)

    have hdegM1 : M1.degree ≤ 3 := by
      exact degree_monomial_le 3 1
    have hdegM2 : M2.degree ≤ 1 := by
      exact degree_monomial_le 1 (-3/4)
    have hdegM3 : M3.degree ≤ 0 := by
      exact degree_monomial_le 0 (1/8)

    let P1 : ℚ[X] := M2 + M3
    have hdegP1 : P1.degree ≤ 1 := by
      apply degree_add_le_of_le hdegM2 hdegM3

    have hP : P = M1 + P1 := by
      have hP1 : P1 = M2 + M3 := by
        simp only [P1, M2, M3, ← C_mul_X_pow_eq_monomial]
      simp only [P, M1, M2, M3, hP1, ← C_mul_X_pow_eq_monomial]
      norm_num
      ring
    rw [hP]
    apply degree_add_le_of_le hdegM1 hdegP1

  have hcoeff3_nonzero : P.coeff 3 ≠ 0 := by
    simp only [P]
    norm_num
  exact degree_eq_of_le_of_coeff_ne_zero hdegPleq3 hcoeff3_nonzero

lemma natdegree_P : P.natDegree = 3 := by
  apply (degree_eq_iff_natDegree_eq nonzero_P).mp
  exact degree_P

lemma eval_theta_zero : aeval theta P = 0 := by

  have cos_cube (x : ℝ) : Real.cos x ^ 3 = (Real.cos (3 * x) + 3 * Real.cos x) / 4 := by
    simp only [Real.cos_three_mul, sub_add_cancel, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_div_cancel_left₀]

  have cos_2_pi_div_three : Real.cos (Real.pi * (2 / 3)) = -1 / 2 := by
    have eq : Real.pi * (2 / 3) = Real.pi - Real.pi / 3 := by
      calc Real.pi * (2 / 3)
        _ = Real.pi - Real.pi / 3 := by ring
    rw [eq, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num

  simp only [theta, P, one_div, map_add, aeval_sub, map_pow, aeval_X, cos_cube, map_mul, aeval_C,
    map_div₀, eq_ratCast, Rat.cast_ofNat, map_inv₀]
  ring_nf
  rw [cos_2_pi_div_three]
  norm_num



lemma irreducible_P : Irreducible P := by
  have hdeg_geq2 : 2 ≤ P.natDegree := by
    rw [natdegree_P]
    norm_num
  have hdeg_leq3 : P.natDegree ≤ 3 := by
    rw [natdegree_P]
  apply (irreducible_iff_roots_eq_zero_of_degree_le_three hdeg_geq2 hdeg_leq3).mpr
  by_contra hroots
  have hnonempty : ∃ a, a ∈ P.roots := by
    exact Multiset.exists_mem_of_ne_zero hroots
  obtain ⟨r, hr⟩ := hnonempty
  have haeval_r_zero : aeval r P = 0 := by
    exact (mem_roots_iff_aeval_eq_zero nonzero_P).mp hr

  let num : ℤ := r.num
  let den : ℕ := r.den
  have hcoprime_num_den : IsCoprime num den := by
    exact Rat.isCoprime_num_den r
  have haeval_num_den_zero : num ^ 3 * 8 - num * den ^ 2 * 6 + den ^ 3 = 0 := by
    simp only [num, den]

    have haeval_r_zero' := by exact haeval_r_zero
    rw [← Rat.num_div_den r] at haeval_r_zero'
    simp only [P, one_div, coe_aeval_eq_eval, eval_add, eval_sub, eval_pow, eval_X, eval_mul,
      eval_C] at haeval_r_zero'
    have h := by
      exact Mathlib.Tactic.LinearCombination'.pf_mul_c haeval_r_zero' (8 * ↑r.den ^ 3)
    ring_nf at h
    field_simp at h
    rw [neg_add_eq_sub, mul_sub, ← mul_assoc, ← pow_succ', ← mul_assoc] at h
    norm_num at h
    norm_cast at h

  -- let num : ℤ := r.num
  -- let den : ℤ := r.den
  -- let fnum : ℤ := IsFractionRing.num ℤ r
  -- let fden : ℤ := IsFractionRing.den ℤ r

  -- have hassoc := by
  --   exact Rat.associated_num_den r


  have hnum : num = 1 ∨ num = -1 := by
    have hnum_div_den3 : num ∣ den ^ 3 := by
      have hnum_div : num ∣ 0 := by exact dvd_zero num
      rw [← haeval_num_den_zero] at hnum_div
      have hnum_div_8num3 : num ∣ num ^ 3 * 8 := by
        apply dvd_mul_of_dvd_left
        exact dvd_pow_self num (by norm_num)
      have hnum_div_8num3_6numden2 : num ∣ num ^ 3 * 8 - num * den ^ 2 * 6 := by
        apply (dvd_sub_right hnum_div_8num3).mp
        simp only [sub_sub_cancel]
        apply dvd_mul_of_dvd_left
        apply dvd_mul_of_dvd_left
        exact dvd_refl num
      apply (dvd_add_right hnum_div_8num3_6numden2).mp
      exact hnum_div

    have hnum_unit : IsUnit num := by
      have hcoprime_num_den3 : IsCoprime num (den ^ 3) := by
        exact IsCoprime.pow_right hcoprime_num_den
      exact IsCoprime.isUnit_of_dvd hcoprime_num_den3 hnum_div_den3

    exact Int.isUnit_eq_one_or hnum_unit

  have hden : den ∈ ({1, 2, 4, 8} : Finset ℕ) := by
    let denZ : ℤ := den
    have hden_div_8num3 : denZ ∣ num ^ 3 * 8 := by
      have hden_div : denZ ∣ 0 := by exact dvd_zero denZ
      rw [← haeval_num_den_zero] at hden_div
      have hden_div_den3 : denZ ∣ den ^ 3 := by
        exact dvd_pow_self denZ (by norm_num)
      have hden_div_6numden2 : denZ ∣ num * den ^ 2 * 6 := by
        apply dvd_mul_of_dvd_left
        apply dvd_mul_of_dvd_right
        exact dvd_pow_self denZ (by norm_num)

      apply (dvd_sub_left hden_div_6numden2).mp
      apply (dvd_add_left hden_div_den3).mp

      exact hden_div

    have hden_div_8 : denZ ∣ 8 := by
      have hcoprime_den_num3 : IsCoprime denZ (num ^ 3) := by
        exact IsCoprime.pow_right hcoprime_num_den.symm
      exact IsCoprime.dvd_of_dvd_mul_left hcoprime_den_num3 hden_div_8num3

    simp only [denZ] at hden_div_8
    norm_cast at hden_div_8

    have hdivisors_of_8 : Nat.divisors 8 = {1, 2, 4, 8} := by
      rfl
    rw [← hdivisors_of_8]
    apply Nat.mem_divisors.mpr
    constructor
    · exact hden_div_8
    · norm_num

  have hden' : den = 1 ∨ den = 2 ∨ den = 4 ∨ den = 8 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hden
    exact hden

  cases hnum with
  | inl hnum_eq_one =>
    rw [hnum_eq_one] at haeval_num_den_zero
    norm_num at haeval_num_den_zero
    cases hden' with
    | inl hden_eq_one =>
      rw [hden_eq_one] at haeval_num_den_zero
      norm_num at haeval_num_den_zero
    | inr hden_cases =>
      cases hden_cases with
      | inl hden_eq_two =>
        rw [hden_eq_two] at haeval_num_den_zero
        norm_num at haeval_num_den_zero
      | inr hden_cases' =>
        cases hden_cases' with
        | inl hden_eq_four =>
          rw [hden_eq_four] at haeval_num_den_zero
          norm_num at haeval_num_den_zero
        | inr hden_eq_eight =>
          rw [hden_eq_eight] at haeval_num_den_zero
          norm_num at haeval_num_den_zero

  | inr hnum_eq_neg_one =>
    rw [hnum_eq_neg_one] at haeval_num_den_zero
    norm_num at haeval_num_den_zero
    cases hden' with
    | inl hden_eq_one =>
      rw [hden_eq_one] at haeval_num_den_zero
      norm_num at haeval_num_den_zero
    | inr hden_cases =>
      cases hden_cases with
      | inl hden_eq_two =>
        rw [hden_eq_two] at haeval_num_den_zero
        norm_num at haeval_num_den_zero
      | inr hden_cases' =>
        cases hden_cases' with
        | inl hden_eq_four =>
          rw [hden_eq_four] at haeval_num_den_zero
          norm_num at haeval_num_den_zero
        | inr hden_eq_eight =>
          rw [hden_eq_eight] at haeval_num_den_zero
          norm_num at haeval_num_den_zero



def answer : List ℚ := [1, 0, -3 /. 4, 1 /. 8]
theorem P₂ : (minpoly ℚ theta).coeffList = answer := by
  have h1 : minpoly ℚ theta = P := by
    have hP_monic : P.Monic := by
      apply (Monic.def).mpr
      simp only [← coeff_natDegree, natdegree_P]
      simp only [P]
      norm_num

    let Q := minpoly ℚ theta
    have hQ_nonone : Q ≠ 1 := by
      intro h
      have htheta_zero : aeval theta Q = 0 := by
        exact minpoly.aeval ℚ theta
      simp only [h] at htheta_zero
      norm_num at htheta_zero
    have hQ_monic : Q.Monic := by
      have htheta_integral : IsIntegral ℚ theta := by
        apply isAlgebraic_iff_isIntegral.mp

        have h1' : P.natDegree ≠ 0 := by
          rw [natdegree_P]
          norm_num
        have h2' : P.leadingCoeff ∈ nonZeroDivisors ℚ := by
          rw [Monic.leadingCoeff hP_monic]
          norm_num
        have h3' : IsAlgebraic ℚ ((aeval theta) P) := by
          rw [eval_theta_zero]
          apply isAlgebraic_iff_isIntegral.mpr
          exact isIntegral_zero

        exact IsAlgebraic.of_aeval P h1' h2' h3'
      exact minpoly.monic htheta_integral

    have hQ_divides_P : Q ∣ P := by
      apply minpoly.dvd ℚ theta eval_theta_zero
    obtain ⟨R, hR⟩ := hQ_divides_P
    have hR_monic : R.Monic := by
      apply (Monic.def).mpr
      have hP_lc_1 : P.leadingCoeff = 1 := by
        rw [Monic.leadingCoeff hP_monic]
      rw [hR, Polynomial.leadingCoeff_monic_mul hQ_monic] at hP_lc_1
      exact hP_lc_1

    have h_iff := (Polynomial.irreducible_of_monic hP_monic nonone_P).mp
    have hQR_eq_1 : Q = 1 ∨ R = 1 := by
      specialize h_iff irreducible_P Q R hQ_monic hR_monic hR.symm
      exact h_iff
    have hR_eq_1 : R = 1 := by
      cases hQR_eq_1 with
      | inl hQ_eq_one =>
        exfalso
        rw [hQ_eq_one] at hQ_nonone
        exact hQ_nonone rfl
      | inr hR_eq_one =>
        exact hR_eq_one

    rw [hR_eq_1, mul_one] at hR
    exact hR.symm
  have h2 : P.coeffList = answer := by
    unfold coeffList
    rw [degree_P]
    change[P.coeff 3, P.coeff 2, P.coeff 1, P.coeff 0] = answer
    unfold P answer
    simp only [one_div, coeff_add, coeff_sub, coeff_X_pow, ↓reduceIte, coeff_mul_X, coeff_C_succ,
      sub_zero, add_zero, Nat.reduceEqDiff, sub_self, OfNat.one_ne_ofNat, coeff_C, zero_sub,
      OfNat.zero_ne_ofNat, mul_coeff_zero, coeff_X, one_ne_zero, mul_zero, zero_add, Int.reduceNeg,
      List.cons.injEq, and_true, true_and]
    constructor
    · rw [← Rat.intCast_div_eq_divInt]
      simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat]
      norm_num
    · rw [← Rat.intCast_div_eq_divInt]
      simp only [Int.cast_ofNat]
      norm_num


  rw [h1]
  exact h2
