import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

open scoped IntermediateField
open Polynomial NumberField

set_option linter.style.emptyLine false

noncomputable abbrev θ : ℝ := 28 ^ (3⁻¹ : ℝ)
noncomputable abbrev F := ℚ⟮θ⟯

lemma theta3_eq_28 : θ ^ 3 = 28 := by
  simp only [θ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · norm_num

lemma theta_isIntegral : IsIntegral ℤ θ := by
  let P : ℤ[X] := X ^ 3 + C (-28)
  have h1 : Monic P := by
    simp only [P]
    exact Polynomial.monic_X_pow_add_C (-28) (by norm_num : 3 ≠ 0)
  have h2 : aeval θ P = 0 := by
    simp only [aeval_add, map_pow, aeval_X, aeval_C, P]
    rw [theta3_eq_28]
    norm_num
  exact ⟨P, h1, h2⟩

lemma theta_isIntegralQ : IsIntegral ℚ θ := by
  let P : ℚ[X] := X ^ 3 + C (-28)
  have h1 : Monic P := by
    simp only [P]
    exact Polynomial.monic_X_pow_add_C (-28) (by norm_num : 3 ≠ 0)
  have h2 : aeval θ P = 0 := by
    simp only [aeval_add, map_pow, aeval_X, aeval_C, P]
    rw [theta3_eq_28]
    norm_num
  exact ⟨P, h1, h2⟩


lemma theta_isAlgebraic : IsAlgebraic ℤ θ := by
  apply IsIntegral.isAlgebraic
  exact theta_isIntegral

lemma theta_isAlgebraicQ : IsAlgebraic ℚ θ := by
  apply IsIntegral.isAlgebraic
  exact theta_isIntegralQ

lemma theta_is_in_F : θ ∈ F := by
  apply F.adjoin_simple_le_iff.mp
  simp

noncomputable abbrev θF : F := ⟨θ, theta_is_in_F⟩

lemma hthetaF_in_OF : θF ∈ integralClosure ℤ ↥F := by
  apply (mem_integralClosure_iff ℤ F).mpr
  let P : ℤ[X] := X ^ 3 + C (-28)
  have h1 : Monic P := by
    simp only [P]
    exact Polynomial.monic_X_pow_add_C (-28) (by norm_num : 3 ≠ 0)
  have h2 : aeval θF P = 0 := by
    simp only [aeval_add, map_pow, aeval_X, aeval_C, P]
    have h : θF ^ 3 = 28 := by
      apply SetLike.coe_eq_coe.mp
      exact theta3_eq_28
    rw [h]
    norm_num
  exact ⟨P, h1, h2⟩

noncomputable abbrev θO : 𝓞 F := ⟨θF, hthetaF_in_OF⟩


instance instFiniteDimensionalF : FiniteDimensional ℚ F := by
  dsimp only [F]
  exact IntermediateField.adjoin.finiteDimensional theta_isIntegralQ

instance instNumberFieldF : NumberField F where
  -- NumberField 定义上要求是特征为 0 的有限维 ℚ-代数

  -- 1. 特征为 0: F 作为 ℝ 的子域，Lean 可以自动推导出 CharZero，所以留给 inferInstance 即可
  -- (如果在某些老版本报错，可以显式写出 toCharZero := inferInstance)

  -- 2. 有限维: 填入我们在步骤 2 中构造的实例
  to_finiteDimensional := instFiniteDimensionalF


lemma h_alpha_mem : θ^2 / 2 ∈ F := by
  apply F.div_mem
  · rw [pow_two]
    apply F.mul_mem
    · exact theta_is_in_F
    · exact theta_is_in_F
  · exact F.natCast_mem 2
noncomputable abbrev α : F := ⟨θ^2 / 2, h_alpha_mem⟩

lemma hy_mem : (α.val - θ - 1) / 3 ∈ F := by
  apply F.div_mem
  · apply F.sub_mem
    · apply F.sub_mem
      · exact α.2
      · exact theta_is_in_F
    · exact F.one_mem
  · exact F.natCast_mem 3
noncomputable abbrev y : F := ⟨(α.val - θ - 1) / 3, hy_mem⟩
