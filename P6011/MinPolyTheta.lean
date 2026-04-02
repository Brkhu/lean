import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.Padics.PadicVal.Basic

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
    apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_three).mpr
    intro r hr
    have hr_nonzero : r ≠ 0 := by
      intro hr_zero
      simp [hr_zero] at hr
    apply_fun padicValRat 2 at hr
    rw [padicValRat.pow hr_nonzero] at hr
    norm_cast at hr
    rw [(by norm_num : 28 = 2 ^ 2 * 7 ^ 1)] at hr
    let _inst_prime_7 : Fact (Nat.Prime 7) := Fact.mk Nat.prime_seven
    rw [padicValNat_mul_pow_left 2 1 (by norm_num : 2 ≠ 7)] at hr
    omega


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

theorem rank_F_eq_three : Module.finrank ℚ F = 3 := by
  dsimp only [F]
  rw [IntermediateField.adjoin.finrank theta_isIntegralQ]
  rw [minpoly_theta]
  exact Polynomial.natDegree_X_pow_sub_C
