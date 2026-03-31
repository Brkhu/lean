import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.NumberField.Discriminant.Defs


-- for ramification
import Mathlib.NumberTheory.RamificationInertia.Unramified
-- for prime ideals in ℤ
import Mathlib.RingTheory.Ideal.NatInt

import Brkhu.P6011.Defs
import Brkhu.P6011.MinPolyTheta
import Brkhu.P6011.MinPolyY
import Brkhu.P6011.Ramification
import Brkhu.P6011.PBDiscEqMPDisc


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

  -- 证明 y 是多项式 f 的根，结合 f 为首一多项式，得出 y 确实是代数整数
  -- hf_root : aeval y f = 0
  -- hy_integral : IsIntegral ℤ y

  -- yO : 𝓞 F := ⟨y, hy_integral⟩

  -- hf_yO_root : aeval yO f = 0
  -- hyO_integral : IsIntegral ℤ yO

  -- 验证 y 生成整个代数数域 F
  -- y_gen_top : ℚ⟮y⟯ = ⊤


  -- 5. 计算多项式 f 的判别式 Δ(f) = -588
  -- hf_discr : discr f = -588

  -- 6. 利用判别式关系与分歧定理
  -- 多项式 f 的判别式等于 ℤ[y] 的判别式，且与数域 F 的判别式相差一个平方因子 m^2
  have h_discr_rel : ∃ (m : ℤ), f.discr = m ^ 2 * NumberField.discr F := by


    -- let b := NumberField.RingOfIntegers.basis F
    -- rw [← NumberField.discr_eq_discr F b]

    -- 问题是我也不知道该用 ℚ 上的还是 ℤ 上的 basis 来计算 discr


    -- 大概明白了, 翻到了这么个定理:
    -- Cubic.discr_eq_prod_three_roots
    -- 说的是三次多项式的 discr 就是三个根的 pairwise difference 的积的平方, 乘以一个固定的符号
    -- 那我就应该用
    -- Algebra.discr_powerBasis_eq_prod
    -- 但这个定理的参数 K, L 都要是域, 所以确实应该用 ℚ 上的



    -- let pb := IntermediateField.adjoin.powerBasis hy_integral'
    -- let b := integralBasis ℚ⟮y⟯


    -- #check Algebra.discr_of_matrix_mulVec

    -- #check b.toMatrix_map_vecMul

    -- #check rank_eq_card_basis b
    -- #check Module.finrank_eq_card_finset_basis b
    -- #check NumberField.RingOfIntegers.rank F
    -- #check IntermediateField.adjoin.finrank theta_isIntegralQ
    -- #check rank_F_eq_three
    -- #check Fintype.card_eq

    have hO_rank : Module.finrank ℤ O = 3 := by
      rw [NumberField.RingOfIntegers.rank F, rank_F_eq_three]

    let b := Module.finBasis ℤ O
    rw [hO_rank] at b

    rw [← NumberField.discr_eq_discr F b]


    have h := Algebra.discr_of_matrix_vecMul b (b.toMatrix pb)
    rw [b.toMatrix_map_vecMul] at h

    use (b.toMatrix pb).det
    rw [discr_powbase_eq_discr_minpoly]
    exact h

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
    -- #check Int.natAbs_sq
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

  -- 将 m^2 = 1 代回判别式关系，即得数域判别式等于多项式判别式
  have h_discr_eq : NumberField.discr F = f.discr := by
    calc NumberField.discr F
      _ = 1 * NumberField.discr F := by ring
      _ = m ^ 2 * NumberField.discr F := by rw[h_m_sq_eq_one]
      _ = f.discr := hm.symm

  -- 代入具体的数值，证明结束
  rw [h_discr_eq, hf_discr]
