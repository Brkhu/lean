import Brkhu.P6011.Defs
import Brkhu.P6011.MinPolyTheta
import Brkhu.P6011.MinPolyY
import Brkhu.P6011.YTheta
import Brkhu.P6011.Ramification
import Brkhu.P6011.PBDiscEqMPDisc


set_option linter.style.emptyLine false

open scoped IntermediateField
open Polynomial NumberField


theorem Algebra2 : ∃ (_ : NumberField F), NumberField.discr F = -588 := by
  use instNumberFieldF

  obtain ⟨m, hm⟩ := h_discr_rel

  have h_m_not_div_2 : ¬ (2 ∣ m) := by
    intro h2
    have h4 : 4 ∣ m ^ 2 := pow_dvd_pow_of_dvd h2 2
    have h_588_not_div_8 : ¬ (8 ∣ f.discr) := by
      rw [hf_discr]
      norm_num
    have h_2_not_div_discr : ¬ (2 ∣ NumberField.discr F) := by
      intro h_2_div
      have h_8_div : 8 ∣ (m ^ 2 * NumberField.discr F) := mul_dvd_mul h4 h_2_div
      rw [← hm] at h_8_div
      exact h_588_not_div_8 h_8_div
    exact h_2_not_div_discr h_ramify_2

  have h_m_not_div_7 : ¬ (7 ∣ m) := by
    intro h7
    have h49 : 49 ∣ m ^ 2 := pow_dvd_pow_of_dvd h7 2
    have h_588_not_div_343 : ¬ (343 ∣ f.discr) := by
      rw[hf_discr]
      norm_num
    have h_7_not_div_discr : ¬ (7 ∣ NumberField.discr F) := by
      intro h_7_div
      have h_343_div : 343 ∣ (m ^ 2 * NumberField.discr F) := mul_dvd_mul h49 h_7_div
      rw [← hm] at h_343_div
      exact h_588_not_div_343 h_343_div
    exact h_7_not_div_discr h_ramify_7

  have h_m_sq_eq_one : m ^ 2 = 1 := by
    rw [hf_discr] at hm
    have h_dvd := dvd_mul_right (m^2) (NumberField.discr F)
    rw [← hm] at h_dvd
    apply dvd_neg.mp at h_dvd

    have h_dvd_42 : m ∣ 2 * (3 * 7) := by
      apply (fun x ↦ dvd_mul_of_dvd_left x 3) at h_dvd
      rw [(by norm_num : (588 : ℤ) * 3 = (42) ^ 2)] at h_dvd
      exact (IsIntegrallyClosed.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp h_dvd

    have h := h_dvd_42
    apply Prime.left_dvd_or_dvd_right_of_dvd_mul ((Int.prime_ofNat_iff).mpr Nat.prime_two) at h
    simp only [h_m_not_div_2, false_or, mul_comm (3 : ℤ) 7] at h

    apply Prime.left_dvd_or_dvd_right_of_dvd_mul ((Int.prime_ofNat_iff).mpr Nat.prime_seven) at h
    simp only [h_m_not_div_7, false_or] at h

    apply Int.natAbs_dvd_natAbs.mpr at h
    simp only [Int.reduceAbs] at h
    apply Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three at h
    have h3 : m.natAbs ≠ 3 := by
      by_contra h3'
      apply_fun (·^2) at h3'
      zify at h3'
      simp only [sq_abs, Int.reducePow] at h3'
      rw [h3'] at h_dvd
      norm_num at h_dvd
    simp only [h3, or_false] at h
    apply_fun (·^2) at h
    zify at h
    simp only [sq_abs, Int.reducePow] at h
    exact h

  have h_discr_eq : NumberField.discr F = f.discr := by
    calc NumberField.discr F
      _ = 1 * NumberField.discr F := by ring
      _ = m ^ 2 * NumberField.discr F := by rw[h_m_sq_eq_one]
      _ = f.discr := hm.symm

  rw [h_discr_eq, hf_discr]
