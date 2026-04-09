import brkhu.P6011.Defs
import brkhu.P6011.MinPolyTheta
import brkhu.P6011.MinPolyY


set_option linter.style.emptyLine false

open scoped IntermediateField
open Polynomial NumberField

-- noncomputable abbrev O := 𝓞 F


lemma y_integral : IsIntegral ℤ y := ⟨f, hf_monic, hf_root⟩
lemma y_integral' : IsIntegral ℚ y := ⟨f_rat, hf_rat_monic, hf_rat_root⟩
noncomputable abbrev yO : 𝓞 F := ⟨y, y_integral⟩
lemma f_yO_root : aeval yO f = 0 := by
  apply NumberField.RingOfIntegers.coe_eq_zero_iff.mp
  rw [← Polynomial.aeval_algebraMap_apply F yO f]
  have h := hf_root
  norm_cast

lemma yO_integral : IsIntegral ℤ yO := ⟨f, hf_monic, f_yO_root⟩


lemma y_by_thetaF : y = (θF ^ 2 / 2 - θF - 1) / 3 := by
  apply SetLike.coe_eq_coe.mp
  rw [div_eq_mul_inv, div_eq_mul_inv, sub_eq_add_neg, sub_eq_add_neg]
  rw [IntermediateField.coe_mul, IntermediateField.coe_add, IntermediateField.coe_add]
  rw [IntermediateField.coe_mul, IntermediateField.coe_pow,
    IntermediateField.coe_inv, IntermediateField.coe_inv,
    IntermediateField.coe_neg, IntermediateField.coe_neg]
  rw [(by norm_num : (2 : F) = 1 + 1), (by norm_num : (3 : F) = 1 + 1 + 1)]
  rw [IntermediateField.coe_add, IntermediateField.coe_add, IntermediateField.coe_one]
  dsimp only [y, θF]
  push_cast
  ring_nf

lemma thetaF_by_y : θF = y ^ 2 + 3 := by
  dsimp only [θF]
  rw [(by ring : (3 : F) = 1 + 1 + 1)]
  simp [← SetLike.coe_eq_coe]
  field_simp
  ring_nf
  have h : θ ^ 4 = θ * 28 := by
    rw [pow_succ', theta3_eq_28]
  rw [theta3_eq_28, h]
  ring_nf

theorem y_gen_top : ℚ⟮y⟯ = ⊤ := by
  apply top_le_iff.mp
  intro x hx_in_top

  have hthetaF_in_Q_y : θF ∈ ℚ⟮y⟯ := by
    have hy_in_Q_y : y ∈ ℚ⟮y⟯ := by
      apply ℚ⟮y⟯.adjoin_simple_le_iff.mp
      simp
    rw [thetaF_by_y]
    apply ℚ⟮y⟯.add_mem
    · rw [pow_two]
      apply ℚ⟮y⟯.mul_mem
      · exact hy_in_Q_y
      · exact hy_in_Q_y
    · exact ℚ⟮y⟯.natCast_mem 3

  have hy_in_Q_thetaF : y ∈ ℚ⟮θF⟯ := by
    have hθF_in_Q_θF : θF ∈ ℚ⟮θF⟯ := by
      apply ℚ⟮θF⟯.adjoin_simple_le_iff.mp
      simp
    rw [y_by_thetaF]
    apply div_mem
    · rw [pow_two]
      apply sub_mem
      · apply sub_mem
        · apply div_mem
          · apply mul_mem
            · exact hθF_in_Q_θF
            · exact hθF_in_Q_θF
          · exact ℚ⟮θF⟯.natCast_mem 2
        · exact hθF_in_Q_θF
      · exact ℚ⟮θF⟯.one_mem
    · exact ℚ⟮θF⟯.natCast_mem 3

  have hQ_thetaF_eq_Q_y : ℚ⟮θF⟯ = ℚ⟮y⟯ := by
    apply le_antisymm_iff.mpr
    constructor
    · apply IntermediateField.adjoin_simple_le_iff.mpr
      exact hthetaF_in_Q_y
    · apply IntermediateField.adjoin_simple_le_iff.mpr
      exact hy_in_Q_thetaF

  rw [← hQ_thetaF_eq_Q_y]

  apply (IntermediateField.mem_lift x).mp
  -- rw [IntermediateField.lift_adjoin_simple ℚ F θF]
  -- simp
  have h : @IntermediateField.adjoin ℚ Rat.instField (↥F) F.toField F.algebra' {θF} =
    @IntermediateField.adjoin ℚ Rat.instField (↥F) F.toField DivisionRing.toRatAlgebra {θF} := by
    rfl
  rw [← h, IntermediateField.lift_adjoin_simple ℚ F θF]
  simp
