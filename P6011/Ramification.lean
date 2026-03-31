-- for ramification
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.NumberField.Discriminant.Different
-- for ramification index
import Mathlib.NumberTheory.RamificationInertia.Galois
-- for prime ideals in ℤ
import Mathlib.RingTheory.Ideal.NatInt
-- for Kummer-Dedekind criteria
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind


import Brkhu.P6011.Defs
import Brkhu.P6011.MinPolyTheta
-- import Brkhu.P6011.MinPolyY


set_option linter.style.emptyLine false

open NumberField Ideal

noncomputable abbrev O := 𝓞 F

noncomputable abbrev p2 : Ideal ℤ := span {2}
noncomputable abbrev p7 : Ideal ℤ := span {7}
noncomputable abbrev P2 : Ideal O := span {2}
noncomputable abbrev P7 : Ideal O := span {7}
noncomputable abbrev Ptheta : Ideal O := span {θO}

lemma p2_prime : IsPrime p2 := by
  apply Ideal.isPrime_int_iff.mpr
  right
  use 2
  constructor
  · exact Nat.prime_two
  · dsimp [P2]

lemma p7_prime : IsPrime p7 := by
  apply Ideal.isPrime_int_iff.mpr
  right
  use 7
  constructor
  · exact Nat.prime_seven
  · dsimp [P7]


lemma p2_map_to_P2 : map (algebraMap ℤ O) p2 = P2 := by
  dsimp only [p2, P2]
  rw [Ideal.map_span (algebraMap ℤ O) {2}]
  simp [algebraMap_int_eq O]

lemma p7_map_to_P7 : map (algebraMap ℤ O) p7 = P7 := by
  dsimp only [p7, P7]
  rw [Ideal.map_span (algebraMap ℤ O) {7}]
  simp [algebraMap_int_eq O]



-- #check map_span (algebraMap ℤ O) {2}

lemma thetaO_cube : θO ^ 3 = 28 := by
  apply RingOfIntegers.eq_iff.mp
  simp only [map_pow, θO]
  rw [RingOfIntegers.map_mk]
  apply SetLike.coe_eq_coe.mp
  exact theta3_eq_28


lemma Ptheta3_eq_P22_P7 : Ptheta ^ 3 = P2 ^ 2 * P7 := by
  rw [span_singleton_pow, span_singleton_pow, span_singleton_mul_span_singleton]
  rw [thetaO_cube]
  norm_num

lemma coprime_P2_P7 : IsCoprime P2 P7 := by
  apply (isCoprime_span_singleton_iff 2 7).mpr
  use -3
  use 1
  norm_num

lemma hthetaO_neq_zero : ¬ θO = 0 := by
  apply NumberField.RingOfIntegers.coe_eq_zero_iff.ne.mp
  apply (@SetLike.coe_eq_coe).not.mp
  simp


theorem h_ramify_2 : 2 ∣ NumberField.discr F := by
  -- 核心思想：θ^3 = 28 = 2^2 * 7，说明 2 在 𝓞 F 中的分歧指数为 3
  -- have h_theta_cube : (⟨θF, sorry⟩ : O) ^ 3 = 28 := sorry
  -- 设 p_2 为整除 2 的素理想，对其取赋值 v_{p_2}
  -- 3 * v_{p_2}(θ) = 2 * e_2 + 0 => 3 ∣ 2 * e_2 => 3 ∣ e_2

  have : p2.IsPrime := p2_prime

  -- #check @nonempty_primesOver ℤ _ O _ _ _ _ _ _ p2 p2_prime

  obtain ⟨P2', hP2'⟩ := nonempty_primesOver (R := ℤ) (S := O) p2

  have hP2'_prime : Prime P2' := by
    exact prime_of_mem_primesOver (by norm_num : p2 ≠ ⊥) hP2'
  have : P2'.IsPrime := primesOver.isPrime p2 ⟨P2', hP2'⟩
  have : p2.IsMaximal := IsPrime.isMaximal p2_prime (by simp)
  have : P2'.LiesOver p2 := primesOver.liesOver p2 ⟨P2', hP2'⟩

  have h_P2'_dvd_P2 : P2' ∣ P2 := by
    rw [← p2_map_to_P2]

    have h1 := IsPrime.ne_top' (I := P2')
    have h2 := primesOver.liesOver p2 ⟨P2', hP2'⟩
    exact (liesOver_iff_dvd_map (p := p2) (P := P2') h1).mp h2

  have h_multiplicity_P2'_p2_geq_3 : multiplicity P2' P2 ≥ 3 := by

    let a : ℕ := multiplicity P2' Ptheta
    let b : ℕ := multiplicity P2' P2
    let c : ℕ := multiplicity P2' P7

    have h_mult_rel : 3 * a = 2 * b + c := by
      rw [(by ring_nf : 3 * a = a + a + a), (by ring_nf : 2 * b = b + b)]
      dsimp only [a, b, c]
      rw [← multiplicity_mul, ← multiplicity_mul, ← multiplicity_mul, ← multiplicity_mul]
      · rw [← pow_three', ← pow_two]
        rw [Ptheta3_eq_P22_P7]
      · exact hP2'_prime
      · exact FiniteMultiplicity.of_prime_left hP2'_prime (by simp : P2 * P2 * P7 ≠ 0)
      · exact hP2'_prime
      · exact FiniteMultiplicity.of_prime_left hP2'_prime (by simp : P2 * P2 ≠ 0)
      · exact hP2'_prime
      · exact FiniteMultiplicity.of_prime_left hP2'_prime (by
          simp only [Submodule.zero_eq_bot, ne_eq, mul_eq_bot, span_singleton_eq_bot, or_self]
          exact hthetaO_neq_zero
          : Ptheta * Ptheta * Ptheta ≠ 0)
      · exact hP2'_prime
      · exact FiniteMultiplicity.of_prime_left hP2'_prime (by
          simp only [Submodule.zero_eq_bot, ne_eq, mul_eq_bot, span_singleton_eq_bot, or_self]
          exact hthetaO_neq_zero
          : Ptheta * Ptheta ≠ 0)

    have h_c_zero : c = 0 := by

      dsimp only [c]
      apply multiplicity_eq_zero.mpr
      by_contra h_P2'_dvd_P7

      have h_P2'_dvd_gcd : P2' ∣ gcd P2 P7 := by
        apply (dvd_gcd_iff P2' P2 P7).mpr
        constructor
        · exact h_P2'_dvd_P2
        · exact h_P2'_dvd_P7

      rw [isCoprime_iff_gcd.mp coprime_P2_P7] at h_P2'_dvd_gcd
      simp only [one_eq_top] at h_P2'_dvd_gcd

      have h := IsPrime.ne_top (isPrime_of_prime hP2'_prime)

      rw [top_le_iff.mp (dvd_iff_le.mp h_P2'_dvd_gcd)] at h
      exact h rfl

    rw [h_c_zero] at h_mult_rel
    norm_num at h_mult_rel

    have h_3_mid_b : 3 ∣ b := by
      have h : b = 3 * (b - a) := by
        rw [Nat.mul_sub 3 b a, h_mult_rel, ← Nat.sub_mul 3 2 b]
        norm_num
      rw [h]
      exact dvd_mul_right 3 (b - a)


    have h_b_geq_3 : b ≥ 3 := by
      have h_b_neq_0 : b ≠ 0 := by
        dsimp only [b]
        exact multiplicity_ne_zero.mpr h_P2'_dvd_P2

      apply Nat.le_of_dvd (Nat.pos_of_ne_zero h_b_neq_0) h_3_mid_b

    dsimp only [b] at h_b_geq_3
    exact h_b_geq_3


  have h_P2'_ramification_index_3 : ramificationIdx p2 P2' = 3 := by

    apply Nat.eq_iff_le_and_ge.mpr
    constructor
    · have : P2'.IsPrime := primesOver.isPrime p2 ⟨P2', hP2'⟩
      have h := ramificationIdx_le_finrank (R := ℤ) (S := O) ℚ F (p := p2) P2'
      rw [rank_F_eq_three] at h
      exact h

    · rw [IsDedekindDomain.ramificationIdx_eq_multiplicity]
      · rw [← p2_map_to_P2] at h_multiplicity_P2'_p2_geq_3
        exact h_multiplicity_P2'_p2_geq_3
      · rw [p2_map_to_P2]
        simp
      · exact primesOver.isPrime p2 ⟨P2', hP2'⟩

  have h_2_ramified : ¬ Algebra.IsUnramifiedAt ℤ (A := O) P2' := by
    -- apply Algebra.isRamifiedAt_of_ramificationIdxIn_eq_one
    -- have h_ramify_2 : Ideal.ramificationIdxIn P2' O = 3 := by
    --   sorry
    -- rw [h_ramify_2]
    -- norm_num
    have : P2'.IsPrime := primesOver.isPrime p2 ⟨P2', hP2'⟩
    have h : P2' ≠ ⊥ := by
      have h1 : p2 ≠ ⊥ := by
        dsimp only [p2]
        apply span_singleton_eq_bot.not.mpr
        simp
      exact ne_bot_of_liesOver_of_ne_bot h1 P2'
    apply (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h).not.mpr
    -- simp only [Submodule.zero_eq_bot, ne_eq, mul_eq_bot, span_singleton_eq_bot, or_self]
    --       exact hthetaO_neq_zero
    rw [over_def P2' p2] at h_P2'_ramification_index_3
    rw [h_P2'_ramification_index_3]
    simp

  apply dvd_differentIdeal_iff.mpr at h_2_ramified
  apply Ideal.dvd_iff_le.mp at h_2_ramified
  apply (mem_of_le_of_mem · (NumberField.discr_mem_differentIdeal F O)) at h_2_ramified
  -- have h_2_ramified := mem_of_le_of_mem h_2_ramified (NumberField.discr_mem_differentIdeal F O)
  apply (mem_of_liesOver P2' p2 (discr F)).mpr at h_2_ramified
  dsimp only [p2] at h_2_ramified
  exact mem_span_singleton.mp h_2_ramified

theorem h_ramify_7 : 7 ∣ NumberField.discr F := by

  have : p7.IsPrime := p7_prime

  obtain ⟨P7', hP7'⟩ := nonempty_primesOver (R := ℤ) (S := O) p7

  have hP7'_prime : Prime P7' := by
    exact prime_of_mem_primesOver (by norm_num : p7 ≠ ⊥) hP7'
  have : P7'.IsPrime := primesOver.isPrime p7 ⟨P7', hP7'⟩
  have : p7.IsMaximal := IsPrime.isMaximal p7_prime (by simp)
  have : P7'.LiesOver p7 := primesOver.liesOver p7 ⟨P7', hP7'⟩

  have h_P7'_dvd_P7 : P7' ∣ P7 := by
    rw [← p7_map_to_P7]

    have h1 := IsPrime.ne_top' (I := P7')
    have h2 := primesOver.liesOver p7 ⟨P7', hP7'⟩
    exact (liesOver_iff_dvd_map (p := p7) (P := P7') h1).mp h2

  have h_multiplicity_P7'_p7_geq_3 : multiplicity P7' P7 ≥ 3 := by

    let a : ℕ := multiplicity P7' Ptheta
    let b : ℕ := multiplicity P7' P2
    let c : ℕ := multiplicity P7' P7

    have h_mult_rel : 3 * a = 2 * b + c := by
      rw [(by ring_nf : 3 * a = a + a + a), (by ring_nf : 2 * b = b + b)]
      dsimp only [a, b, c]
      rw [← multiplicity_mul, ← multiplicity_mul, ← multiplicity_mul, ← multiplicity_mul]
      · rw [← pow_three', ← pow_two]
        rw [Ptheta3_eq_P22_P7]
      · exact hP7'_prime
      · exact FiniteMultiplicity.of_prime_left hP7'_prime (by simp : P2 * P2 * P7 ≠ 0)
      · exact hP7'_prime
      · exact FiniteMultiplicity.of_prime_left hP7'_prime (by simp : P2 * P2 ≠ 0)
      · exact hP7'_prime
      · exact FiniteMultiplicity.of_prime_left hP7'_prime (by
          simp only [Submodule.zero_eq_bot, ne_eq, mul_eq_bot, span_singleton_eq_bot, or_self]
          exact hthetaO_neq_zero
          : Ptheta * Ptheta * Ptheta ≠ 0)
      · exact hP7'_prime
      · exact FiniteMultiplicity.of_prime_left hP7'_prime (by
          simp only [Submodule.zero_eq_bot, ne_eq, mul_eq_bot, span_singleton_eq_bot, or_self]
          exact hthetaO_neq_zero
          : Ptheta * Ptheta ≠ 0)

    have h_b_zero : b = 0 := by

      dsimp only [b]
      apply multiplicity_eq_zero.mpr
      by_contra h_P7'_dvd_P2

      have h_P7'_dvd_gcd : P7' ∣ gcd P2 P7 := by
        apply (dvd_gcd_iff P7' P2 P7).mpr
        constructor
        · exact h_P7'_dvd_P2
        · exact h_P7'_dvd_P7

      rw [isCoprime_iff_gcd.mp coprime_P2_P7] at h_P7'_dvd_gcd
      simp only [one_eq_top] at h_P7'_dvd_gcd

      have h := IsPrime.ne_top (isPrime_of_prime hP7'_prime)

      rw [top_le_iff.mp (dvd_iff_le.mp h_P7'_dvd_gcd)] at h
      exact h rfl

    rw [h_b_zero] at h_mult_rel
    norm_num at h_mult_rel

    have h_3_mid_c : 3 ∣ c := by
      rw [← h_mult_rel]
      exact dvd_mul_right 3 a


    have h_c_geq_3 : c ≥ 3 := by
      have h_c_neq_0 : c ≠ 0 := by
        dsimp only [c]
        exact multiplicity_ne_zero.mpr h_P7'_dvd_P7

      apply Nat.le_of_dvd (Nat.pos_of_ne_zero h_c_neq_0) h_3_mid_c

    dsimp only [c] at h_c_geq_3
    exact h_c_geq_3


  have h_P7'_ramification_index_3 : ramificationIdx p7 P7' = 3 := by

    apply Nat.eq_iff_le_and_ge.mpr
    constructor
    · have : P7'.IsPrime := primesOver.isPrime p7 ⟨P7', hP7'⟩
      have h := ramificationIdx_le_finrank (R := ℤ) (S := O) ℚ F (p := p7) P7'
      rw [rank_F_eq_three] at h
      exact h

    · rw [IsDedekindDomain.ramificationIdx_eq_multiplicity]
      · rw [← p7_map_to_P7] at h_multiplicity_P7'_p7_geq_3
        exact h_multiplicity_P7'_p7_geq_3
      · rw [p7_map_to_P7]
        simp
      · exact primesOver.isPrime p7 ⟨P7', hP7'⟩

  have h_7_ramified : ¬ Algebra.IsUnramifiedAt ℤ (A := O) P7' := by
    have : P7'.IsPrime := primesOver.isPrime p7 ⟨P7', hP7'⟩
    have h : P7' ≠ ⊥ := by
      have h1 : p7 ≠ ⊥ := by
        dsimp only [p7]
        apply span_singleton_eq_bot.not.mpr
        simp
      exact ne_bot_of_liesOver_of_ne_bot h1 P7'
    apply (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h).not.mpr

    rw [over_def P7' p7] at h_P7'_ramification_index_3
    rw [h_P7'_ramification_index_3]
    simp

  apply dvd_differentIdeal_iff.mpr at h_7_ramified
  apply Ideal.dvd_iff_le.mp at h_7_ramified
  apply (mem_of_le_of_mem · (NumberField.discr_mem_differentIdeal F O)) at h_7_ramified
  apply (mem_of_liesOver P7' p7 (discr F)).mpr at h_7_ramified
  dsimp only [p7] at h_7_ramified
  exact mem_span_singleton.mp h_7_ramified
