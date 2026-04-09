import Mathlib.RingTheory.Polynomial.Resultant.Basic
-- for irreducible_iff_roots_eq_zero_of_degree_le_three
import Mathlib.Algebra.Polynomial.SpecificDegree
-- for dvd
import Mathlib.Algebra.Divisibility.Basic
-- for Gauss's lemma
import Mathlib.RingTheory.Polynomial.GaussLemma
-- for degree 3
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
-- for rational root
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.Rat

import brkhu.MinPoly
import brkhu.P6011.Defs

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
  have haeval_r_zero : aeval r f = 0 := by
    have h_rat_aeval_r_zero : aeval r f_rat = 0 := by
      apply (Polynomial.mem_roots_iff_aeval_eq_zero hf_rat_nonzero).mp hr
    dsimp only [f_rat] at h_rat_aeval_r_zero
    rw [Polynomial.aeval_map_algebraMap ℚ] at h_rat_aeval_r_zero
    exact h_rat_aeval_r_zero
  have hsubst_r : r ^ 3 + r ^ 2 + 5 * r - 1 = 0 := by
    have h := haeval_r_zero
    simp only [f, eq_intCast, Int.cast_ofNat, aeval_sub, map_add, map_pow, aeval_X, map_mul,
      map_one] at h
    rw [(by simp : (5 : ℤ[X]) = C 5)] at h
    simp only [aeval_C] at h
    exact h


  have hnum : r.num.natAbs = 1 := by
    have hfrac_num_dvd_1 := num_dvd_of_is_root haeval_r_zero
    norm_num at hfrac_num_dvd_1
    have h_frac_num_abs_1 := (Int.isUnit_iff_natAbs_eq).mp (isUnit_of_dvd_one hfrac_num_dvd_1)
    rw [← (Int.associated_iff_natAbs).mp (Rat.isFractionRingNum r)]
    exact h_frac_num_abs_1

  have hden : r.den = 1 := by
    have hfrac_den_dvd_1 := den_dvd_of_is_root haeval_r_zero
    rw [(Monic.def).mp hf_monic] at hfrac_den_dvd_1
    have h_frac_den_abs_1 := (Int.isUnit_iff_natAbs_eq).mp (isUnit_of_dvd_one hfrac_den_dvd_1)
    rw [Rat.isFractionRingDen r] at h_frac_den_abs_1
    exact h_frac_den_abs_1

  apply Int.isUnit_iff_natAbs_eq.mpr at hnum
  apply Int.isUnit_iff.mp at hnum
  cases hnum with
  | inl hnum_one =>
    have hr_one : r = 1 := by
      rw [← Rat.num_div_den r, hnum_one, hden]
      norm_num
    rw [hr_one] at hsubst_r
    norm_num at hsubst_r
  | inr hnum_neg_one =>
    have hr_neg_one : r = -1 := by
      rw [← Rat.num_div_den r, hnum_neg_one, hden]
      norm_num
    rw [hr_neg_one] at hsubst_r
    norm_num at hsubst_r

lemma hf_irreducible : Irreducible f := by
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (Monic.isPrimitive hf_monic)).mpr
  exact hf_rat_irreducible


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


theorem hf_discr : discr f = -588 := by
  rw [discr_of_degree_eq_three]
  · simp [f, coeff_X, coeff_one]
  · apply (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 3)).mpr
    exact hf_natDeg

theorem hf_rat_minpoly : minpoly ℚ y = f_rat := by
  exact minpoly_from_monic_irreducible f_rat hf_rat_monic hf_rat_irreducible hf_rat_root
