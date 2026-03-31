import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.NumberField.Discriminant.Defs


import Mathlib.Tactic.Qify -- for qify
import Mathlib.RingTheory.Adjoin.PowerBasis -- for adjoin power basis
import Mathlib.RingTheory.IsAdjoinRoot -- for IsAdjoinRootMonic.basis
-- for ramification
import Mathlib.NumberTheory.RamificationInertia.Unramified
-- for prime ideals in ℤ
import Mathlib.RingTheory.Ideal.NatInt
-- for Polynomial.discr
import Mathlib.RingTheory.Polynomial.Resultant.Basic

-- import Brkhu.P6011.Defs
-- import Brkhu.P6011.MinPolyTheta
-- import Brkhu.P6011.MinPolyY
-- import Brkhu.P6011.Ramification


set_option linter.style.emptyLine false

open scoped IntermediateField
open Polynomial NumberField

-- Defs
noncomputable abbrev θ : ℝ := 28 ^ (3⁻¹ : ℝ)
noncomputable abbrev F := ℚ⟮θ⟯
lemma theta3_eq_28 : θ ^ 3 = 28 := by sorry
lemma theta_isIntegralQ : IsIntegral ℚ θ := by sorry
instance instFiniteDimensionalF : FiniteDimensional ℚ F := by
  dsimp only [F]
  exact IntermediateField.adjoin.finiteDimensional theta_isIntegralQ
instance instNumberFieldF : NumberField F where
  to_finiteDimensional := instFiniteDimensionalF
lemma h_alpha_mem : θ^2 / 2 ∈ F := by sorry
noncomputable abbrev α : F := ⟨θ^2 / 2, h_alpha_mem⟩
lemma hy_mem : (α.val - θ - 1) / 3 ∈ F := by sorry
noncomputable abbrev y : F := ⟨(α.val - θ - 1) / 3, hy_mem⟩
lemma theta_is_in_F : θ ∈ F := by sorry
noncomputable abbrev θF : F := ⟨θ, theta_is_in_F⟩


-- MinPolyY
noncomputable abbrev f : ℤ[X] := X^3 + X^2 + C 5 * X - 1
noncomputable abbrev f_rat : ℚ[X] := f.map (algebraMap ℤ ℚ)
lemma hf_monic : Monic f := by sorry
lemma hf_rat_monic : Monic f_rat := by sorry
lemma hf_root : aeval y f = 0 := by sorry
lemma hf_rat_root : aeval y f_rat = 0 := by sorry
lemma hf_deg : degree f = 3 := by sorry
lemma hf_natDeg : natDegree f = 3 := by sorry
lemma hf_nonzero : f ≠ 0 := by sorry
lemma hf_irreducible : Irreducible f := by sorry
lemma hf_discr : Polynomial.discr f = -588 := by sorry


-- Ramification
lemma h_ramify_2 : 2 ∣ NumberField.discr F := by sorry
lemma h_ramify_7 : 7 ∣ NumberField.discr F := by sorry


-- MinPolyTheta
lemma rank_F_eq_three : Module.finrank ℚ F = 3 := by sorry


theorem Algebra2 : ∃ (_ : NumberField F), NumberField.discr F = -588 := by
  -- 1. 提供存在性证明所需的 NumberField 实例
  use instNumberFieldF

  -- 2. 发现判别式的平方因子，构造初步的代数整数 α = θ^2 / 2
  -- h_alpha_mem : θ^2 / 2 ∈ F
  -- α : F := ⟨θ^2 / 2, h_alpha_mem⟩

  -- 3. 为了除掉判别式中隐藏的 3^3 因子，扩大整数环构造 y = (α - θ - 1) / 3
  -- hy_mem : (α.val - θ - 1) / 3 ∈ F
  -- y : F := ⟨(α.val - θ - 1) / 3, hy_mem⟩

  -- 4. 提出 y 的极小多项式 f(X) = X^3 + X^2 + 5X - 1
  -- f : ℤ[X] := X^3 + X^2 + C 5 * X - 1
  -- f_rat : ℚ[X] := f.map (algebraMap ℤ ℚ)

  -- 证明 y 是多项式 f 的根，结合 f 为首一多项式，得出 y 确实是代数整数
  -- hf_root : aeval y f = 0
  -- hf_rat_root : aeval y f_rat = 0

  have hy_integral : IsIntegral ℤ y := ⟨f, hf_monic, hf_root⟩
  have hy_integral' : IsIntegral ℚ y := ⟨f_rat, hf_rat_monic, hf_rat_root⟩
  let yO : 𝓞 F := ⟨y, hy_integral⟩
  have hf_yO_root : aeval yO f = 0 := by
    apply NumberField.RingOfIntegers.coe_eq_zero_iff.mp
    rw [← Polynomial.aeval_algebraMap_apply F yO f]
    have h := hf_root
    norm_cast

  have hyO_integral : IsIntegral ℤ yO := ⟨f, hf_monic, hf_yO_root⟩

  -- 验证 y 生成整个代数数域 F

  have hy_by_thetaF : y = (θF ^ 2 / 2 - θF - 1) / 3 := by
    apply SetLike.coe_eq_coe.mp
    rw [div_eq_mul_inv, div_eq_mul_inv, sub_eq_add_neg, sub_eq_add_neg]
    rw [IntermediateField.coe_mul, IntermediateField.coe_add, IntermediateField.coe_add]
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow]
    rw [IntermediateField.coe_inv, IntermediateField.coe_inv]
    rw [IntermediateField.coe_neg, IntermediateField.coe_neg]
    rw [(by norm_num : (2 : F) = 1 + 1), (by norm_num : (3 : F) = 1 + 1 + 1)]
    rw [IntermediateField.coe_add, IntermediateField.coe_add, IntermediateField.coe_one]
    dsimp only [y, θF]
    push_cast
    ring_nf

  have hthetaF_by_y : θF = y ^ 2 + 3 := by
    dsimp only [θF]
    rw [(by ring : (3 : F) = 1 + 1 + 1)]
    simp [← SetLike.coe_eq_coe]
    field_simp
    ring_nf
    have h : θ ^ 4 = θ * 28 := by
      rw [pow_succ', theta3_eq_28]
    rw [theta3_eq_28, h]
    ring_nf

  have hy_gen_top : ℚ⟮y⟯ = ⊤ := by
    apply top_le_iff.mp
    intro x hx_in_top

    have hthetaF_in_Q_y : θF ∈ ℚ⟮y⟯ := by
      have hy_in_Q_y : y ∈ ℚ⟮y⟯ := by
        apply ℚ⟮y⟯.adjoin_simple_le_iff.mp
        simp
      rw [hthetaF_by_y]
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
      rw [hy_by_thetaF]
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
      @IntermediateField.adjoin ℚ Rat.instField (↥F) F.toField DivisionRing.toRatAlgebra {θF} := by rfl
    rw [← h, IntermediateField.lift_adjoin_simple ℚ F θF]
    simp

  -- 5. 计算多项式 f 的判别式 Δ(f) = -588
  -- hf_discr : discr f = -588

  -- 6. 利用判别式关系与分歧定理
  -- 多项式 f 的判别式等于 ℤ[y] 的判别式，且与数域 F 的判别式相差一个平方因子 m^2
  have h_discr_rel : ∃ (m : ℤ), f.discr = m ^ 2 * NumberField.discr F := by

    have h_maximal_order' : Algebra.adjoin ℤ {yO} = ⊤ := by
      apply Algebra.eq_top_iff.mpr
      intro x

      sorry


    let b := NumberField.RingOfIntegers.basis F

    -- 问题是我也不知道该用 ℚ 上的还是 ℤ 上的 basis 来计算 discr


    -- 大概明白了, 翻到了这么个定理:
    -- Cubic.discr_eq_prod_three_roots
    -- 说的是三次多项式的 discr 就是三个根的 pairwise difference 的积的平方, 乘以一个固定的符号
    -- 那我就应该用
    -- Algebra.discr_powerBasis_eq_prod
    -- 但这个定理的参数 K, L 都要是域, 所以确实应该用 ℚ 上的



    -- let pb := IntermediateField.adjoin.powerBasis hy_integral'
    -- let b := integralBasis ℚ⟮y⟯


    #check Algebra.discr_of_matrix_mulVec

    #check b.toMatrix_map_vecMul

    #check rank_eq_card_basis b
    -- #check Module.finrank_eq_card_finset_basis b
    #check NumberField.RingOfIntegers.rank F
    #check IntermediateField.adjoin.finrank theta_isIntegralQ
    #check rank_F_eq_three
    #check Fintype.card_eq

    have hO_rank : Module.finrank ℤ (𝓞 F) = 3 := by
      rw [NumberField.RingOfIntegers.rank F, rank_F_eq_three]

    let b := Module.finBasis ℤ (𝓞 F)
    rw [hO_rank] at b
    rw [← NumberField.discr_eq_discr F b]


    -- let pb := PowerBasis.ofAdjoinEqTop' hyO_integral h_maximal_order'
    let pb : Fin 3 → 𝓞 F := fun n => yO ^ n.val


    sorry

  obtain ⟨m, hm⟩ := h_discr_rel

  -- 证明 2 和 7 在 F 中分歧，从而由 Dedekind 判别式定理推导：素数整除数域的判别式
  -- h_ramify_2 : 2 ∣ NumberField.discr F
  -- h_ramify_7 : 7 ∣ NumberField.discr F

  -- 7. 通过平方因子耗尽（Exponent counting）证明指数 m 不能被 2 和 7 整除
  have h_m_not_div_2 : ¬ (2 ∣ m) := by
    intro h2
    -- 如果 2 整除 m，那么 4 整除 m^2
    have h4 : 4 ∣ m ^ 2 := pow_dvd_pow_of_dvd h2 2

    -- 代入判别式方程：-588 = m^2 * Δ_F
    -- 我们可以用 norm_num 直接验证 -588 中 2 的幂次恰好为 2 (即 8 不整除 -588)
    have h_588_not_div_8 : ¬ (8 ∣ f.discr) := by
      rw [hf_discr]
      norm_num

    -- 若 m^2 贡献了所有的 4，且 Δ_F 又被 2 整除，则乘积必定被 8 整除
    have h_2_not_div_discr : ¬ (2 ∣ NumberField.discr F) := by
      intro h_2_div
      -- 4 ∣ m^2 且 2 ∣ Δ_F => 8 ∣ m^2 * Δ_F
      have h_8_div : 8 ∣ (m ^ 2 * NumberField.discr F) := mul_dvd_mul h4 h_2_div
      rw [← hm] at h_8_div
      exact h_588_not_div_8 h_8_div

    -- 这与我们在第 6 步证明的 2 ∣ Δ_F (h_ramify_2) 矛盾！
    exact h_2_not_div_discr h_ramify_2

  have h_m_not_div_7 : ¬ (7 ∣ m) := by
    intro h7
    -- 如果 7 整除 m，那么 49 整除 m^2
    have h49 : 49 ∣ m ^ 2 := pow_dvd_pow_of_dvd h7 2

    -- -588 中 7 的幂次恰好为 2 (即 343 = 7^3 不整除 -588)
    have h_588_not_div_343 : ¬ (343 ∣ f.discr) := by
      rw[hf_discr]
      norm_num

    -- 若 m^2 贡献了所有的 49，Δ_F 中就不能再含有 7
    have h_7_not_div_discr : ¬ (7 ∣ NumberField.discr F) := by
      intro h_7_div
      -- 49 ∣ m^2 且 7 ∣ Δ_F => 343 ∣ m^2 * Δ_F
      have h_343_div : 343 ∣ (m ^ 2 * NumberField.discr F) := mul_dvd_mul h49 h_7_div
      rw [← hm] at h_343_div
      exact h_588_not_div_343 h_343_div

    -- 这与 h_ramify_7 矛盾！
    exact h_7_not_div_discr h_ramify_7

  -- 8. 锁定指数并得出最终结论
  -- 既然 m^2 必须整除 -588，且 m 不能被 2 和 7 整除
  -- 而 -588 = - 2^2 * 3 * 7^2 中，剩余的素因子 3 只出现了 1 次（无法提供平方因子）
  -- 故 m 只能是 1 或 -1
  have h_m_sq_eq_one : m ^ 2 = 1 := by
    -- 留作 sorry：通过算术基本定理证明 m^2 ∣ -588 且 gcd(m, 14)=1 推导得出
    sorry

  -- 将 m^2 = 1 代回判别式关系，即得数域判别式等于多项式判别式
  have h_discr_eq : NumberField.discr F = f.discr := by
    calc NumberField.discr F
      _ = 1 * NumberField.discr F := by ring
      _ = m ^ 2 * NumberField.discr F := by rw[h_m_sq_eq_one]
      _ = f.discr := hm.symm

  -- 代入具体的数值，证明结束
  rw [h_discr_eq, hf_discr]
