import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Nat.Prime.Int

import Brkhu.P6011.Defs

set_option linter.style.emptyLine false

open scoped IntermediateField
open Polynomial Prime

lemma minpoly_theta : minpoly ℚ θ = X ^ 3 - 28 := by
  let f : ℚ[X] := X ^ 3 - C 28
  have h_root : aeval θ f = 0 := by
    simp only [aeval_sub, map_pow, aeval_X, aeval_C, eq_ratCast, Rat.cast_ofNat, f]
    rw [theta3_eq_28]
    norm_num
  have h_natdeg : f.natDegree = 3 := by
    exact natDegree_X_pow_sub_C
  have h_monic : Monic f := by
    simp only [f]
    exact monic_X_pow_sub_C 28 (by norm_num : 3 ≠ 0)
  have h_irreducible : Irreducible f := by
    have h1 : 2 ≤ f.natDegree := by simp [h_natdeg]
    have h2 : f.natDegree ≤ 3 := by simp [h_natdeg]
    apply (irreducible_iff_roots_eq_zero_of_degree_le_three h1 h2).mpr
    by_contra hroots
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hroots

    have haeval_r_zero : aeval r f = 0 := by
      have h := Monic.ne_zero_of_polynomial_ne h_monic (by norm_num : (0 : ℚ[X]) ≠ 1)
      exact (mem_roots_iff_aeval_eq_zero h).mp hr

    let num : ℤ := r.num
    let den : ℕ := r.den
    have hcoprime_num_den : IsCoprime num den := by
      exact Rat.isCoprime_num_den r
    have haeval_num_den : num ^ 3 = den ^ 3 * 28 := by
      simp only [num, den]
      have h := by exact haeval_r_zero
      rw [← Rat.num_div_den r] at h
      simp [f] at h
      field_simp at h
      norm_num at h
      norm_cast at h
      rw [sub_eq_zero] at h
      exact h
    -- let num_nn : ℕ := num.natAbs
    -- have h_nonneg : num = num_nn := by
    --   sorry
    have h2_dvd_num : 2 ∣ num := by
      have h := haeval_num_den
      rw [(by norm_num : (28 : ℤ) = 14 * 2), ← mul_assoc] at h
      apply (dvd_pow_iff_dvd ((Int.prime_ofNat_iff).mpr Nat.prime_two) (by norm_num : 3 ≠ 0)).mp
      rw [h]
      exact dvd_mul_left _ _
    have h2_dvd_den : (2 : ℤ) ∣ den := by
      obtain ⟨k, hk⟩ := dvd_def.mp h2_dvd_num
      rw [hk, mul_pow, mul_comm] at haeval_num_den
      rw [pow_three 2, ← mul_assoc] at haeval_num_den
      rw [(by norm_num : (28 : ℤ) = 7 * (2 * 2)), ← mul_assoc _ _ (2 * 2)] at haeval_num_den
      apply mul_right_cancel₀ (by norm_num) at haeval_num_den
      have h : den ^ 3 = (k ^ 3 - den ^ 3 * 3) * 2 := by
        rw [sub_mul, eq_sub_iff_add_eq, mul_assoc, ← mul_one_add]
        norm_num
        exact haeval_num_den.symm
      -- rw [← mul_assoc] at h
      apply (dvd_pow_iff_dvd ((Int.prime_ofNat_iff).mpr Nat.prime_two) (by norm_num : 3 ≠ 0)).mp
      rw [h]
      exact dvd_mul_left _ _

    have h := IsCoprime.isUnit_of_dvd' hcoprime_num_den h2_dvd_num h2_dvd_den
    apply Int.isUnit_eq_one_or at h
    norm_num at h



  have h_min : ∀ (q : ℚ[X]), q.Monic → (aeval θ) q = 0 → f.degree ≤ q.degree := by
    intros q h_q_monic h_q_root
    let r := EuclideanDomain.gcd f q
    have h_root_gcd : aeval θ r = 0 := by
      apply root_gcd_iff_root_left_right.mpr
      constructor
      · exact h_root
      · exact h_q_root
    have h_div : r ∣ f := EuclideanDomain.gcd_dvd_left f q
    have h_div' : r ∣ q := EuclideanDomain.gcd_dvd_right f q
    obtain ⟨s, hs⟩ := dvd_def.mp h_div
    have h := h_irreducible
    rw [hs] at h
    apply of_irreducible_mul at h
    rcases h with h | h
    · obtain ⟨u, ⟨h1, h2⟩⟩ := isUnit_iff.mp h
      simp [← h2] at h_root_gcd
      have h' := IsUnit.ne_zero h1
      simp [h_root_gcd] at h'
    · have h_assoc : Associated f r := by
        rw [hs]
        exact associated_mul_unit_left r s h
      have h_degree : f.degree = r.degree := degree_eq_degree_of_associated h_assoc
      have h' := Monic.ne_zero_of_polynomial_ne h_q_monic (by norm_num : (0 : ℚ[X]) ≠ 1)
      have h'' := degree_le_of_dvd h_div' h'
      rw [← h_degree] at h''
      exact h''


  subst f
  exact (minpoly.unique ℚ θ h_monic h_root h_min).symm
