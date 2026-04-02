import Mathlib.RingTheory.Polynomial.Resultant.Basic
-- for irreducible_iff_roots_eq_zero_of_degree_le_three
import Mathlib.Algebra.Polynomial.SpecificDegree
-- for dvd
import Mathlib.Algebra.Divisibility.Basic
-- for Gauss's lemma
import Mathlib.RingTheory.Polynomial.GaussLemma
-- for degree 3
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

import Brkhu.P6011.Defs

set_option linter.style.emptyLine false

open Polynomial


noncomputable abbrev f : ℤ[X] := X^3 + X^2 + C 5 * X - 1
noncomputable abbrev f_rat : ℚ[X] := f.map (algebraMap ℤ ℚ)

lemma hf_C : f = C 1 * X^3 + C 1 * X^2 + C 5 * X + C (-1) := by
  dsimp only [f]
  norm_num
  rfl


lemma hf_natDeg : natDegree f = 3 := by
  rw [hf_C, natDegree_cubic (by norm_num : (1 : ℤ) ≠ 0)]

lemma hf_monic : Monic f := by
  apply (Monic.def).mpr
  rw [hf_C, leadingCoeff_cubic (by norm_num : (1 : ℤ) ≠ 0)]

lemma hf_deg : degree f = 3 := by
  rw [hf_C, degree_cubic (by norm_num : (1 : ℤ) ≠ 0)]

lemma hf_nonzero : f ≠ 0 := by
  apply Polynomial.zero_le_degree_iff.mp
  simp [hf_deg]


lemma hf_rat_natDeg : natDegree f_rat = 3 := by
  rw [natDegree_map_eq_iff.mpr]
  · exact hf_natDeg
  · left
    rw [Polynomial.Monic.leadingCoeff]
    · rw [Algebra.algebraMap_eq_smul_one]
      norm_num
    · exact hf_monic

lemma hf_rat_monic : Monic f_rat := by
  apply (Monic.def).mpr
  simp only [← coeff_natDegree, hf_rat_natDeg]
  simp only [f_rat]
  norm_num
  simp [coeff_X, coeff_one]

lemma hf_rat_deg : degree f_rat = 3 := by
  rw [degree_eq_natDegree]
  · norm_cast
    exact hf_rat_natDeg
  · exact @Polynomial.Monic.ne_zero_of_ne ℚ _ (by norm_num : (0 : ℚ) ≠ 1) f_rat hf_rat_monic

lemma hf_rat_nonzero : f_rat ≠ 0 := by
  apply Polynomial.zero_le_degree_iff.mp
  rw [hf_rat_deg]
  norm_num


lemma hf_rat_irreducible : Irreducible f_rat := by
  have hdeg_rat_geq2 : 2 ≤ f_rat.natDegree := by
    rw [hf_rat_natDeg]
    norm_num
  have hdeg_rat_leq3 : f_rat.natDegree ≤ 3 := by
    rw [hf_rat_natDeg]
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg_rat_geq2 hdeg_rat_leq3]
  apply Multiset.eq_zero_of_forall_notMem
  intro r hr

  let num : ℤ := r.num
  let den : ℕ := r.den
  have hcoprime_num_den : IsCoprime num den := by
    exact Rat.isCoprime_num_den r

  have haeval_num_den_zero : num ^ 3 + num ^ 2 * den + num * den ^ 2 * 5 - den ^ 3 = 0 := by
    simp only [num, den]
    have haeval_r_zero : aeval r f_rat = 0 := by
      apply (Polynomial.mem_roots_iff_aeval_eq_zero hf_rat_nonzero).mp hr
    rw [← Rat.num_div_den r] at haeval_r_zero
    simp[f_rat] at haeval_r_zero
    field_simp at haeval_r_zero
    norm_cast at haeval_r_zero
    simp only [mul_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← pow_three, ← mul_assoc,
      mul_zero, CharP.cast_eq_zero] at haeval_r_zero
    rw [← pow_two] at haeval_r_zero
    exact haeval_r_zero



  have hnum : num = 1 ∨ num = -1 := by
    have hnum_dvd_den_3 : num ∣ den ^ 3 := by
      have hnum_div : num ∣ 0 := by exact dvd_zero num
      rw [← haeval_num_den_zero] at hnum_div
      apply @dvd_sub ℤ _ num (num ^ 3 + num ^ 2 * ↑den + num * ↑den ^ 2 * 5) at hnum_div
      · norm_num at hnum_div
        exact hnum_div
      · apply @dvd_add ℤ _ _ _ num (num ^ 3 + num ^ 2 * ↑den)
        · apply @dvd_add ℤ _ _ _ num (num ^ 3)
          · exact dvd_pow_self num (by norm_num : 3 ≠ 0)
          · rw [pow_two, mul_assoc]
            exact @dvd_mul_right ℤ _ num (num * den)
        · rw [mul_assoc]
          exact @dvd_mul_right ℤ _ num (↑den ^ 2 * 5)

    have hnum_unit : IsUnit num := by
      have hcoprime_num_den3 : IsCoprime num (den ^ 3) := by
        exact IsCoprime.pow_right hcoprime_num_den
      exact IsCoprime.isUnit_of_dvd hcoprime_num_den3 hnum_dvd_den_3

    exact Int.isUnit_eq_one_or hnum_unit

  have hden : den = 1 := by
    let denZ : ℤ := den
    have hden_dvd_num_3 : denZ ∣ num ^ 3 := by
      have hden_div : denZ ∣ 0 := by exact dvd_zero denZ
      rw [← haeval_num_den_zero] at hden_div
      apply @dvd_add ℤ _ _ _ denZ (den ^ 3) at hden_div
      · norm_num at hden_div
        apply @dvd_sub ℤ _ denZ (num * ↑den ^ 2 * 5) at hden_div
        · apply dvd_sub_comm.mp at hden_div
          norm_num at hden_div
          apply @dvd_sub ℤ _ denZ (num ^ 2 * ↑den) at hden_div
          · apply dvd_sub_comm.mp at hden_div
            norm_num at hden_div
            exact hden_div
          · exact @dvd_mul_left ℤ _ denZ (num ^ 2)
        · rw [mul_assoc, ← mul_comm 5, ← mul_assoc, pow_two, ← mul_assoc]
          exact @dvd_mul_left ℤ _ denZ (num * 5 * den)
      · exact dvd_pow_self denZ (by norm_num : 3 ≠ 0)

    have hden_unit : IsUnit denZ := by
      have hcoprime_den_num3 : IsCoprime denZ (num ^ 3) := by
        exact IsCoprime.pow_right hcoprime_num_den.symm
      exact IsCoprime.isUnit_of_dvd hcoprime_den_num3 hden_dvd_num_3

    apply Int.isUnit_eq_one_or at hden_unit
    cases hden_unit with
    | inl hden_one =>
      dsimp only [denZ] at hden_one
      norm_cast at hden_one
    | inr hden_neg_one =>
      dsimp only [denZ] at hden_neg_one
      norm_cast at hden_neg_one

  cases hnum with
  | inl hnum_one =>
    rw [hnum_one, hden] at haeval_num_den_zero
    norm_num at haeval_num_den_zero
  | inr hnum_neg_one =>
    rw [hnum_neg_one, hden] at haeval_num_den_zero
    norm_num at haeval_num_den_zero

lemma hf_irreducible : Irreducible f := by
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast _).mpr
  · exact hf_rat_irreducible
  · exact Polynomial.Monic.isPrimitive hf_monic


lemma hf_root : aeval y f = 0 := by
  simp only [aeval_sub, map_add, map_pow, aeval_X, map_mul, map_one,
    f]
  rw [aeval_C y 5]
  simp only [eq_intCast, Int.cast_ofNat]

  rw [(by ring : (5 : F) = 1 + 1 + 1 + 1 + 1)]
  apply F.mk_eq_zero.mpr

  simp only [SubmonoidClass.mk_pow, AddMemClass.mk_add_mk, AddMemClass.coe_add,
    MulMemClass.coe_mul, OneMemClass.coe_one, y]

  ring_nf

  have h1 : θ ^ 4 = θ * 28 := by
    rw [pow_succ', theta3_eq_28]
  have h2 : θ ^ 5 = θ ^ 2 * 28 := by
    rw [pow_add θ 2 3, theta3_eq_28]
  have h3 : θ ^ 6 = 784 := by
    rw [pow_add θ 3 3, theta3_eq_28]
    norm_num

  rw [theta3_eq_28, h1, h2, h3]
  ring_nf

lemma hf_rat_root : aeval y f_rat = 0 := by
  dsimp only [f_rat]
  rw [Polynomial.aeval_map_algebraMap]
  exact hf_root


lemma hf_discr : discr f = -588 := by
  rw [discr_of_degree_eq_three]
  · simp [f, coeff_X, coeff_one]
  · apply (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 3)).mpr
    exact hf_natDeg
