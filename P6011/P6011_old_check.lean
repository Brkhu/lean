import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.NumberField.Discriminant.Defs


import Mathlib.Tactic.Qify -- for qify
import Mathlib.RingTheory.Adjoin.PowerBasis -- for adjoin power basis
import Mathlib.RingTheory.IsAdjoinRoot -- for IsAdjoinRootMonic.basis
-- for ramification
import Mathlib.NumberTheory.RamificationInertia.Unramified
-- for prime ideals in ℤ
import Mathlib.RingTheory.Ideal.NatInt

import Brkhu.P6011.Defs
import Brkhu.P6011.MinPolyY


set_option linter.style.emptyLine false

open scoped IntermediateField
open Polynomial NumberField


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
  -- have hy_gen : ℚ⟮y⟯ = F := by
  -- #check IntermediateField.restrict
  -- #check IntermediateField.restrict (le_rfl : F ≤ F)

  let θF : F := ⟨θ, theta_is_in_F⟩
  have hy_by_thetaF : y = (θF ^ 2 / 2 - θF - 1) / 3 := by
    apply SetLike.coe_eq_coe.mp
    rw [div_eq_mul_inv, div_eq_mul_inv, sub_eq_add_neg, sub_eq_add_neg]
    rw [IntermediateField.coe_mul, IntermediateField.coe_add, IntermediateField.coe_add]
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow]
    rw [IntermediateField.coe_inv, IntermediateField.coe_inv, IntermediateField.coe_neg, IntermediateField.coe_neg]
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

  have hthetaF_in_OF : θF ∈ integralClosure ℤ ↥F := by
    apply (mem_integralClosure_iff ℤ F).mpr
    let P : ℤ[X] := X ^ 3 + C (-28)
    have h1 : Monic P := by
      simp only [P]
      exact Polynomial.monic_X_pow_add_C (-28) (by norm_num : 3 ≠ 0)
    have h2 : aeval θF P = 0 := by
      -- apply F.mk_eq_zero.mpr
      simp only [aeval_add, map_pow, aeval_X, aeval_C, P]
      have h : θF ^ 3 = 28 := by
        apply SetLike.coe_eq_coe.mp
        exact theta3_eq_28
      rw [h]
      norm_num
    exact ⟨P, h1, h2⟩

  let θO : 𝓞 F := ⟨θF, hthetaF_in_OF⟩

  have hy_gen_top : ℚ⟮y⟯ = ⊤ := by
    -- apply eq_top_iff.mpr
    -- have (⊤ : Subfield F) ≃+* F := by
    --   sorry

    -- #check @Subfield.topEquiv F _
    -- #check @divisionRingOfFiniteDimensional ℚ F _ _ _ _ instFiniteDimensionalF
    -- #check @IntermediateField.adjoin_root_eq_top ℚ _ (X ^ 3 - 28 : ℚ[X])
    -- #check IntermediateField.toSubfield_inj.mp

    -- #check @Subfield.topEquiv F _
    -- #check IntermediateField.finrank_eq_one_iff_eq_top.mp
    -- #check IntermediateField.adjoin_root_eq_top
    -- #check IntermediateField.toSubfield_inj
    -- apply IntermediateField.ext_iff.mpr
    -- intro x
    -- constructor
    -- · simp
    -- · intro hx_in_top
    --   sorry

    apply top_le_iff.mp
    intro x hx_in_top
    -- simp [F] at x

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
      -- rw [algebraMap_int_eq, eq_intCast, Int.cast_ofNat]
      -- exact hthetaF_in_Q_y
      apply le_antisymm_iff.mpr
      constructor
      · apply IntermediateField.adjoin_simple_le_iff.mpr
        exact hthetaF_in_Q_y
      · apply IntermediateField.adjoin_simple_le_iff.mpr
        exact hy_in_Q_thetaF

    rw [← hQ_thetaF_eq_Q_y]

    -- #check @IntermediateField.mem_top ℚ _ F _ _ θF
    -- #check x.mem
    -- #check x.val
    -- #check x.property
    -- #check x.val_inj
    -- #check IntermediateField.mem_mk ℚ⟮θF⟯.toSubsemiring

    -- #check IntermediateField.lift_adjoin ℚ F {y}
    -- #check (IntermediateField.lift_inj ℚ⟮θF⟯ ℚ⟮y⟯).mpr hQ_thetaF_eq_Q_y
    -- #check IntermediateField.mem_lift x

    -- rw [(IntermediateField.lift_inj ℚ⟮θF⟯ ℚ⟮y⟯).mpr hQ_thetaF_eq_Q_y]

    -- rw [htheta_by_y] at x

    apply (IntermediateField.mem_lift x).mp
    rw [IntermediateField.lift_adjoin_simple]
    simp



  -- 5. 计算多项式 f 的判别式 Δ(f) = -588
  -- hf_discr : discr f = -588

  -- 6. 利用分歧证明极大性
  -- f 的判别式为 -588 = - 2^2 * 3 * 7^2
  -- 我们知道域的判别式与多项式判别式满足关系 Δ(f) = [𝓞_F : ℤ[y]]^2 * Δ_F
  -- 故只需检验素数 p=2 和 p=7 的平方是否能从 -588 中被提取作为环扩指数：

  -- 通过 (2) 分歧说明 p = 2 整除 Δ_F：
  -- let P2 : Ideal ℤ := Ideal.span {2}
  -- have h_ramify_2 : ¬ IsUnramifiedAt ℤ (𝓞 F) _ _ _ P2 P2_prime := sorry

  -- 通过 (7) 分歧说明 p = 7 整除 Δ_F：
  -- have h_ramify_7 : ¬ ∃ (k : ℤ), f.discr = (7 * k)^2 * NumberField.discr F := sorry

  -- 结合以上两点，-588 中不存在使得指数大于 1 的平方因子。
  -- 也就是说 ℤ[y] 已经是极大阶，即 𝓞_F = ℤ[y]
  have h_maximal_order : 𝓞 F = Algebra.adjoin ℤ { (⟨y, hy_integral⟩ : 𝓞 F) } := by
    sorry


  -- 7. 因为 𝓞_F = ℤ[y] 是极大极大阶，数域 F 的判别式等于多项式 f 的判别式
  have h_discr_eq : NumberField.discr F = f.discr := by

    -- 第一种思路: 去到 ℚ 上工作

    -- #check @IntermediateField.topEquiv ℚ _ F _ _
    have h := @IntermediateField.topEquiv ℚ _ F _ _
    -- #check NumberField.discr_eq_discr_of_algEquiv F h.symm
    rw [NumberField.discr_eq_discr_of_algEquiv F h.symm, ← hy_gen_top]

    qify
    rw [NumberField.coe_discr]

    let pb := IntermediateField.adjoin.powerBasis hy_integral'
    let b := integralBasis ℚ⟮y⟯

    -- #check Algebra.discr_powerBasis_eq_norm ℚ pb
    -- #check Algebra.adjoin.powerBasis
    -- #check Algebra.adjoin.powerBasis hy_integral
    -- #check IsAdjoinRootMonic.basis
    -- #check @PowerBasis.ofAdjoinEqTop' ℤ (𝓞 F) _ _ _ _ _ _ _ yO hyO_integral
    -- #check Algebra.discr
    have h1 : ∀ i j, IsIntegral ℤ (Module.Basis.toMatrix b pb.basis i j) := by sorry
    have h2 : ∀ i j, IsIntegral ℤ (Module.Basis.toMatrix pb.basis b i j) := by sorry
    -- #check @Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral (Module.Free.ChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯)) (Fin pb.dim) ℚ⟮y⟯ _ _ _ _ _ _ b pb.basis h1 h2
    -- #check IntermediateField.adjoin.powerBasis hy_integral

    rw [Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral ℚ⟮y⟯ h1 h2]



    sorry

  have h_discr_eq' : NumberField.discr F = f.discr := by

    -- 第二种思路: 保持在 ℤ 上工作, 即手动构造一个 ℤ-basis b : Module.Basis ι ℤ (𝓞 F), 作为参数把 F 的 discr 转化成 ℤ 上这个 basis 的 discr

    -- 也就是这样:
    -- let b : Module.Basis (Fin 3) ℤ (𝓞 F) := sorry
    -- rw [← NumberField.discr_eq_discr F b]

    -- 我大概需要一个 b : Module.Basis ι ℤ (𝓞 F), 我希望它能是 1,y,y^2, 或者说 power basis

    have h_maximal_order' : Algebra.adjoin ℤ {yO} = ⊤ := by
      apply Algebra.eq_top_iff.mpr
      intro x

      sorry

    let pb := PowerBasis.ofAdjoinEqTop' hyO_integral h_maximal_order'
    rw [← NumberField.discr_eq_discr F pb.basis]

    -- 问题是我也不知道该用 ℚ 上的还是 ℤ 上的 basis 来计算 discr


    -- 大概明白了, 翻到了这么个定理:
    -- Cubic.discr_eq_prod_three_roots
    -- 说的是三次多项式的 discr 就是三个根的 pairwise difference 的积的平方, 乘以一个固定的符号
    -- 那我就应该用
    -- Algebra.discr_powerBasis_eq_prod
    -- 但这个定理的参数 K, L 都要是域, 所以确实应该用 ℚ 上的

    #check @Algebra.discr_powerBasis_eq_prod
    -- Algebra.discr_powerBasis_eq_prod.{u, v, z} (K : Type u) {L : Type v} (E : Type z) [Field K] [Field L] [Field E]
    -- [Algebra K L] [Algebra K E] [Module.Finite K L] [IsAlgClosed E] (pb : PowerBasis K L) (e : Fin pb.dim ≃ (L →ₐ[K] E))
    -- [Algebra.IsSeparable K L] :
    -- (algebraMap K E) (Algebra.discr K ⇑pb.basis) = ∏ i, ∏ j ∈ Finset.Ioi i, ((e j) pb.gen - (e i) pb.gen) ^ 2




    -- Algebra.discr (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    -- [Fintype ι] (b : ι → B) := (traceMatrix A b).det
    -- 所以我还要构造一个 (b : ι → B)
    -- 怎么会吃这种东西呢, 太奇怪了, 是指标集吗?


    #check NumberField.coe_discr F
    --   NumberField.coe_discr.{u_1} (K : Type u_1) [Field K] [NumberField K] :
    -- ↑(NumberField.discr K) = Algebra.discr ℚ ⇑(integralBasis K)


    let pb := IntermediateField.adjoin.powerBasis hy_integral'
    -- rw [hy_gen_top] at pb
    #check pb.basis
    let b := integralBasis ℚ⟮y⟯

    sorry


  -- 8. 结合上述两条结论，代入 f 的判别式数值结束证明
  rw [h_discr_eq, hf_discr]
