-- for discr and resultants of polynomials
import Mathlib.RingTheory.Polynomial.Resultant.Basic
-- for qify
import Mathlib.Tactic.Qify
-- for rational integral over Z
import Mathlib.NumberTheory.Niven
-- for ring of integer as range
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

import Mathlib.NumberTheory.NumberField.Discriminant.Defs

-- for cubic
import Mathlib.Algebra.CubicDiscriminant

import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Multiset.MapFold


import Brkhu.P6011.Defs
import Brkhu.P6011.MinPolyTheta
import Brkhu.P6011.MinPolyY
import Brkhu.P6011.YTheta


set_option linter.style.emptyLine false

open scoped IntermediateField
open Polynomial NumberField


variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]



noncomputable abbrev b := NumberField.integralBasis ℚ⟮y⟯
noncomputable abbrev pb := IntermediateField.adjoin.powerBasis y_integral'

lemma h_pb_gen_y : pb.gen = y := by rfl

lemma discr_powbasis_f : f.discr = Algebra.discr ℚ pb.basis := by
  have h' := resultant_deriv (f := f) (by rw [hf_deg]; norm_num)
  rw [hf_natDeg, (Monic.def).mp hf_monic] at h'
  simp only [Nat.add_one_sub_one, Int.reduceNeg, Nat.reduceMul, Nat.reduceDiv, Int.reducePow,
    mul_one, neg_mul, one_mul] at h'
  rw [Int.eq_neg_comm] at h'

  rw [h']
  -- simp

  have h := Algebra.discr_powerBasis_eq_prod _ (AlgebraicClosure ℚ⟮y⟯) pb
  -- rw [h]
  simp at h

  -- have h' : (algebraMap ℚ (AlgebraicClosure ↥ℚ⟮y⟯)) (Algebra.discr ℚ ⇑pb.basis) =
  -- rw [h _]
  #check IntermediateField.algHomAdjoinIntegralEquiv _ (K := AlgebraicClosure ℚ) y_integral'

  #check IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen

  #check Cubic.discr_eq_prod_three_roots

  #check resultant_deriv (f := f) (by rw [hf_deg]; norm_num)

  #check resultant_map_map f f.derivative f.natDegree f.derivative.natDegree (algebraMap ℤ ℚ)


  have h_to_rat : (f.resultant (derivative f) 3 2) =
      f_rat.resultant f_rat.derivative 3
      2 := by
    rw [derivative_map]
    rw [resultant_map_map f f.derivative 3 2 (algebraMap ℤ ℚ)]
    rfl
  simp only [Int.cast_neg, IntermediateField.adjoin.powerBasis_dim]
  rw [h_to_rat]
  rw [neg_eq_iff_eq_neg]

  let f_split : ℂ[X] := f_rat.map (algebraMap ℚ ℂ)
  have h_f_split_deg : f_split.degree = 3 := by
    dsimp only [f_split]
    rw [Polynomial.degree_map f_rat (algebraMap ℚ ℂ), hf_rat_deg]
  have h_f_split_natDeg : f_split.natDegree = 3 := by
    dsimp only [f_split]
    rw [Polynomial.natDegree_map (algebraMap ℚ ℂ), hf_rat_natDeg]
  have h_f_split_monic : Monic f_split := by
    apply (Monic.def).mpr
    dsimp only [f_split]
    rw [Polynomial.leadingCoeff_map (algebraMap ℚ ℂ), hf_rat_monic]
    simp
  have h_f_split_splits : Splits f_split := by
    exact IsAlgClosed.splits f_split
  have h_f_split_nonzero : f_split ≠ 0 := by
    exact Polynomial.Monic.ne_zero_of_ne (by norm_num) h_f_split_monic
  have h_f_split_root_nodup : Multiset.Nodup f_split.roots := by
    apply nodup_roots
    have h_f_rat_separable : Separable f_rat := by
      exact Irreducible.separable hf_rat_irreducible
    dsimp only [f_split]
    exact Separable.map h_f_rat_separable

  have h_to_split : algebraMap ℚ ℂ (f_rat.resultant (derivative f_rat) 3 2) =
      f_split.resultant f_split.derivative 3
      2 := by
    dsimp only [f_split]
    rw [← resultant_map_map f_rat f_rat.derivative 3 2 (algebraMap ℚ ℂ)]
    rw [derivative_map f_rat]

  -- #check Algebra.discr_powerBasis_eq_prod ℚ (AlgebraicClosure ℚ⟮y⟯) pb
  have h_Qybar_inj : Function.Injective (algebraMap ℚ ℂ) := by
    sorry
  #check Subfield.subtype_injective (K := AlgebraicClosure ℚ)
  apply h_Qybar_inj
  -- have h : Field.toSemifield.toCommSemiring = Rat.commSemiring := rfl
  -- rw [← h]
  -- simp

  rw [h_to_split]


  #check Irreducible.separable

  -- simp only [Int.cast_neg, IntermediateField.adjoin.powerBasis_dim]
  -- rw [h'']


  #check resultant_map_map f_rat f_rat.derivative f_rat.natDegree f_rat.derivative.natDegree (algebraMap ℚ ℂ)

  -- have hf'_natDeg_leq : f_split.derivative.natDegree ≤ 2 := by
  --   have h_leq := Polynomial.natDegree_derivative_le f_split
  --   rw [h_f_split_natDeg, (by norm_num : 3 - 1 = 2)] at h_leq
  --   exact h_leq

  have h_to_prod := resultant_eq_prod_eval f_split f_split.derivative (f_split.natDegree - 1)
      (Polynomial.natDegree_derivative_le f_split) h_f_split_splits
  rw [h_f_split_natDeg, h_f_split_monic] at h_to_prod
  norm_num at h_to_prod

  rw [h_to_prod]

  -- #check Polynomial.Splits.eval_root_derivative
  -- rw [Polynomial.Splits.eval_root_derivative]

  have h_to_double_prod : (Multiset.map (fun x ↦ eval x (derivative f_split)) f_split.roots).prod =
      (Multiset.map (fun x ↦ (Multiset.map (fun x_1 ↦ x - x_1) (f_split.roots.erase x)).prod)
      f_split.roots).prod := by
    congr 1
    -- #check map_congr
    have h_eval_deriv : ∀ x ∈ f_split.roots, eval x (derivative f_split) = (Multiset.map
        (fun x_1 ↦ x - x_1) (f_split.roots.erase x)).prod := by
      intro _ hx
      exact Polynomial.Splits.eval_root_derivative h_f_split_splits h_f_split_monic hx
    exact Multiset.map_congr (by rfl) h_eval_deriv


  rw [h_to_double_prod]



  -- #check Polynomial.Splits.degree_eq_card_roots h_f_split_splits h_f_split_nonzero
  -- #check Fintype.card_eq (α := Fin)
  -- #check Fintype.card_fin

  -- let index : Fin 3 ≃ f_split.roots := by
  --   have h_root_card := Polynomial.Splits.degree_eq_card_roots h_f_split_splits h_f_split_nonzero
  --   rw [h_f_split_deg] at h_root_card
  --   norm_cast at h_root_card
  --   apply Fintype.equivOfCardEq
  --   rw [Multiset.card_coe, Fintype.card_fin, h_root_card]

  -- #check index.toFun
  -- #check index.symm.toFun
  -- -- #check

  -- #check finprod_comp index.toFun
  #check Finset.prod_multiset_map_count
  #check Finset.prod_mk
  #check Finset.prod_mk f_split.roots h_f_split_root_nodup



  #check Multiset.map_map

  #check Multiset.toFinset_eq
  #check Multiset.toFinset_eq h_f_split_root_nodup


  -- rw [← Finset.prod_mk f_split.roots h_f_split_root_nodup]
  -- rw [Multiset.toFinset_eq h_f_split_root_nodup]



  -- have h_to_fin_double_prod : (Multiset.map (fun x ↦ (Multiset.map (fun x_1 ↦ x - x_1)
  --     (f_split.roots.erase x)).prod) f_split.roots).prod = 1 := by
    -- congr 1
    -- -- #check map_congr
    -- have h_eval_deriv : ∀ x ∈ f_split.roots, eval x (derivative f_split) = (Multiset.map
    --     (fun x_1 ↦ x - x_1) (f_split.roots.erase x)).prod := by
    --   intro _ hx
    --   exact Polynomial.Splits.eval_root_derivative h_f_split_splits h_f_split_monic hx
    -- exact Multiset.map_congr (by rfl) h_eval_deriv

    -- sorry

  have h_to_fin_double_prod : (Multiset.map (fun x ↦ (Multiset.map (fun x_1 ↦ x - x_1)
      (f_split.roots.erase x)).prod) f_split.roots).prod
      = ∏ x : f_split.roots.toFinset, ∏ x_1 ∈ f_split.roots.toFinset.erase x, (x - x_1) := by

    rw [← Finset.prod_mk f_split.roots h_f_split_root_nodup]
    rw [Multiset.toFinset_eq h_f_split_root_nodup]

    rw [← Finset.prod_coe_sort]
    -- rw [← Finset.prod_coe_sort f_split.roots.toFinset]

    rw [Fintype.prod_congr]
    intro x
    have h_nodup_erase : (f_split.roots.erase x).Nodup := by
      apply h_f_split_root_nodup.erase
    rw [← Finset.prod_mk (f_split.roots.erase x) h_nodup_erase]
    rw [Multiset.toFinset_eq h_nodup_erase]

    have h_erase_eq_erase : (f_split.roots.erase x).toFinset = f_split.roots.toFinset.erase x := by
      apply Finset.mk.congr_simp
      rw [(Multiset.dedup_eq_self).mpr h_nodup_erase]
      simp only [Multiset.toFinset_val]
      rw [(Multiset.dedup_eq_self).mpr h_f_split_root_nodup]
    rw [h_erase_eq_erase]

  rw [h_to_fin_double_prod]


  let index : Fin 3 ≃ f_split.roots.toFinset := by
    have h_root_card := Polynomial.Splits.degree_eq_card_roots h_f_split_splits h_f_split_nonzero
    rw [h_f_split_deg] at h_root_card
    norm_cast at h_root_card
    apply Fintype.equivOfCardEq
    -- #check Multiset.toFinset_card_of_nodup h_f_split_root_nodup
    simp only [Fintype.card_fin, Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def,
      Fintype.card_coe, Multiset.toFinset_card_of_nodup h_f_split_root_nodup]
    rw [h_root_card]

  #check index.toFun
  #check index.symm.toFun
  -- #check

  #check finprod_comp index.toFun

  #check finprod_comp


  -- let sub_fun : ℂ × ℂ → ℂ := fun p ↦ if p.1 = p.2 then 1 else p.1 - p.2

  have h_to_fin_prod : ∏ x : f_split.roots.toFinset, ∏ x_1 ∈ f_split.roots.toFinset.erase x,
      (x - x_1) =
      ∏ x : Fin 3, ∏ x_1 ∈ (Finset.univ : Finset (Fin 3)).erase x, ((index x : ℂ) - index x_1) := by
    -- rw [Finset.prod_equiv index]
    let index_map_f : Fin 3 → ℂ := (fun x ↦ ∏ x_1 ∈ (Finset.univ : Finset (Fin 3)).erase x,
        ((index x : ℂ) - index x_1))
    let index_map_g : f_split.roots.toFinset → ℂ := (fun (ix : f_split.roots.toFinset) ↦
        ∏ x_1 ∈ f_split.roots.toFinset.erase ix, (ix - x_1))
    have h_index_map : ∀ (x : Fin 3), index_map_f x = index_map_g (index x) := by
      intro x
      dsimp [index_map_f, index_map_g]

      -- rw [← Finset.prod_coe_sort]
      -- rw [← Finset.prod_coe_sort (f_split.roots.toFinset.erase (index x))]

      #check Finset.prod_bij
      -- let index_map := fun y hy => (index y : ℂ)
      #check Finset.prod_bij (fun y _ => (index y : ℂ)) _

      -- rw [Finset.prod_bij (fun y _ => (index y : ℂ))]
      -- goal 1 : ∀ a ∈ Finset.univ.erase x, ↑(index a) ∈ f_split.roots.toFinset.erase ↑(index x)
      -- · intro a ha
      --   rw [Finset.map_erase index.toEmbedding]

      -- rw [Fintype.prod_equiv]
      sorry
    rw [Fintype.prod_equiv index _ _ h_index_map]

  #check Finset.prod_equiv index _ _
  #check Finset.prod_map Finset.univ index.toEmbedding
  #check Fintype.prod_equiv index

  #check Set.Iio_union_Ioi
  #check Set.Iio_union_Ioi (α := Fin 3)
  #check Finset.compl_singleton

  have h_to_ioi_prod : ∏ x : Fin 3, ∏ x_1 ∈ (Finset.univ : Finset (Fin 3)).erase x,
      ((index x : ℂ) - index x_1)
      = - ∏ x : Fin 3, ∏ x_1 ∈ Finset.Ioi x, ((index x : ℂ) - index x_1) ^ 2 := by


    sorry


  --   sorry

  sorry

lemma discr_powbasis_integralbasis : ∃ (m : ℤ), Algebra.discr ℚ pb.basis = m ^ 2 * discr F := by

  have h := IntermediateField.topEquiv (F := ℚ) (E := F)

  rw [NumberField.discr_eq_discr_of_algEquiv F h.symm, ← y_gen_top]

  rw [NumberField.coe_discr]

  let pb' := pb.basis ∘ ⇑(pb.basis.indexEquiv b).symm

  have h1 := Algebra.discr_of_matrix_vecMul b (b.toMatrix pb')

  have hint : ∀ i j, b.toMatrix pb' i j ∈ Set.range (Int.cast (R := ℚ)) := by
    intro i j
    rw [Module.Basis.toMatrix_apply]
    have h_algmap_intcast : algebraMap ℤ ℚ = Int.cast (R := ℚ) := by rfl
    rw [← h_algmap_intcast]

    have h_pb' : pb' j ∈ Submodule.span ℤ (Set.range b) := by
      apply (NumberField.mem_span_integralBasis ℚ⟮y⟯).mpr
      have h_pb : ∀ (n : Fin pb.dim), pb.basis n ∈ (algebraMap (𝓞 ℚ⟮y⟯) ℚ⟮y⟯).range := by
        intro n
        rw [pb.basis_eq_pow n]
        have h_pow_integral : IsIntegral ℤ (pb.gen ^ n.val) := by
          apply IsIntegral.pow
          apply IntermediateField.coe_isIntegral_iff.mp
          exact y_integral
        apply RingHom.mem_range.mpr
        use ⟨pb.gen ^ n.val, h_pow_integral⟩
        simp
      exact h_pb ((pb.basis.indexEquiv b).symm j)

    exact (Module.Basis.mem_span_iff_repr_mem ℤ b (pb' j)).mp h_pb' i

  let M := b.toMatrix pb'

  choose f hf using hint
  let MZ : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯))
      (Module.Free.ChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯)) ℤ := Matrix.of f
  have h_rep : M = MZ.map (Int.cast (R := ℚ)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, M, MZ]
    exact (hf i j).symm
  use MZ.det
  rw [Int.cast_det]
  rw [← h_rep]

  rw [← Algebra.discr_of_matrix_vecMul b (b.toMatrix pb')]

  rw [Module.Basis.toMatrix_map_vecMul b pb']

  have h : Algebra.discr ℚ pb.basis = Algebra.discr ℚ pb' := by
    dsimp only [pb']
    have h' := Algebra.discr_reindex ℚ pb.basis (pb.basis.indexEquiv b)
    exact h'.symm
  exact h

theorem h_discr_rel : ∃ (m : ℤ), f.discr = m ^ 2 * NumberField.discr F := by
  qify
  rw [discr_powbasis_f]
  exact discr_powbasis_integralbasis
