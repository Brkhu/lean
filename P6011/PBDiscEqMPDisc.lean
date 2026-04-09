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
open Polynomial NumberField Finset


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

  -- let index : Fin f_split.natDegree ≃ f_split.roots := by
  --   have h_root_card := Polynomial.Splits.degree_eq_card_roots h_f_split_splits h_f_split_nonzero
  --   rw [h_f_split_deg] at h_root_card
  --   norm_cast at h_root_card
  --   apply Fintype.equivOfCardEq
  --   rw [Multiset.card_coe, Fintype.card_fin, h_root_card]

  -- #check index.toFun
  -- #check index.symm.toFun
  -- -- #check

  -- #check finprod_comp index.toFun
  #check prod_multiset_map_count
  #check prod_mk
  #check prod_mk f_split.roots h_f_split_root_nodup



  #check Multiset.map_map

  #check Multiset.toFinset_eq
  #check Multiset.toFinset_eq h_f_split_root_nodup


  -- rw [← prod_mk f_split.roots h_f_split_root_nodup]
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

    rw [← prod_mk f_split.roots h_f_split_root_nodup]
    rw [Multiset.toFinset_eq h_f_split_root_nodup]

    rw [← prod_coe_sort]
    -- rw [← prod_coe_sort f_split.roots.toFinset]

    rw [Fintype.prod_congr]
    intro x
    have h_nodup_erase : (f_split.roots.erase x).Nodup := by
      apply h_f_split_root_nodup.erase
    rw [← prod_mk (f_split.roots.erase x) h_nodup_erase]
    rw [Multiset.toFinset_eq h_nodup_erase]

    have h_erase_eq_erase : (f_split.roots.erase x).toFinset = f_split.roots.toFinset.erase x := by
      apply Finset.mk.congr_simp
      rw [(Multiset.dedup_eq_self).mpr h_nodup_erase]
      simp only [Multiset.toFinset_val]
      rw [(Multiset.dedup_eq_self).mpr h_f_split_root_nodup]
    rw [h_erase_eq_erase]

  rw [h_to_fin_double_prod]




  let index : Fin (minpoly ℚ y).natDegree ≃ f_split.roots.toFinset := by
    have h_root_card := Polynomial.Splits.degree_eq_card_roots h_f_split_splits h_f_split_nonzero
    rw [h_f_split_deg] at h_root_card
    norm_cast at h_root_card
    apply Fintype.equivOfCardEq
    -- #check Multiset.toFinset_card_of_nodup h_f_split_root_nodup
    simp only [Fintype.card_fin, Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def,
      Fintype.card_coe, Multiset.toFinset_card_of_nodup h_f_split_root_nodup]
    rw [← h_root_card]
    rw [hf_rat_minpoly]
    exact hf_rat_natDeg

  #check index.toFun
  #check index.symm.toFun
  -- #check

  #check finprod_comp index.toFun

  #check finprod_comp


  -- let sub_fun : ℂ × ℂ → ℂ := fun p ↦ if p.1 = p.2 then 1 else p.1 - p.2

  have h_to_fin_prod : ∏ x : f_split.roots.toFinset, ∏ x_1 ∈ f_split.roots.toFinset.erase x,
      (x - x_1) =
      ∏ x : Fin (minpoly ℚ y).natDegree, ∏ x_1 ∈ (univ : Finset (Fin (minpoly ℚ y).natDegree)).erase x, ((index x : ℂ) - index x_1) := by
    -- rw [prod_equiv index]
    let index_map_f : Fin (minpoly ℚ y).natDegree → ℂ := (fun x ↦ ∏ x_1 ∈ (univ : Finset (Fin (minpoly ℚ y).natDegree)).erase x,
        ((index x : ℂ) - index x_1))
    let index_map_g : f_split.roots.toFinset → ℂ := (fun (ix : f_split.roots.toFinset) ↦
        ∏ x_1 ∈ f_split.roots.toFinset.erase ix, (ix - x_1))
    have h_index_map : ∀ (x : Fin (minpoly ℚ y).natDegree), index_map_f x = index_map_g (index x) := by
      intro x
      dsimp [index_map_f, index_map_g]

      -- rw [← prod_coe_sort]
      -- rw [← prod_coe_sort (f_split.roots.toFinset.erase (index x))]

      #check prod_bij
      -- let index_map := fun y hy => (index y : ℂ)
      #check prod_bij (fun y _ => (index y : ℂ)) _

      -- rw [prod_bij (fun y _ => (index y : ℂ))]
      -- goal 1 : ∀ a ∈ univ.erase x, ↑(index a) ∈ f_split.roots.toFinset.erase ↑(index x)
      -- · intro a ha
        -- rw [map_erase index.toEmbedding]

      -- rw [Fintype.prod_equiv]

      -- #check prod_nbij (s := univ.erase x) (t := f_split.roots.toFinset.erase (index x)) index
      #check prod_image

      let index_C : Fin (minpoly ℚ y).natDegree → ℂ := fun s ↦ (index s).val
      have h_index_inj' : Set.InjOn index_C (univ.erase x) := by
        intro i hi j hj hij
        apply index.injective
        ext
        exact hij

      have h_index_image : image index_C (univ.erase x) = f_split.roots.toFinset.erase
          (index x) := by
        apply Finset.ext
        intro x_1
        simp only [mem_image, mem_erase, mem_univ, and_true, index_C]
        constructor
        · intro h1
          obtain ⟨a, ha, hai⟩ := h1
          constructor
          · rw [← hai]
            norm_cast
            exact index.injective.ne ha
          · rw [← hai]
            simp
        · intro h2
          obtain ⟨hxi, hx⟩ := h2
          use index.symm ⟨x_1, hx⟩
          constructor
          · symm
            apply index.apply_eq_iff_eq_symm_apply.ne.mp
            apply Subtype.ext_iff.ne.mpr
            rw [Subtype.coe_mk x_1 hx]
            exact hxi.symm
          · rw [index.apply_symm_apply]

      rw [← h_index_image]
      rw [prod_image h_index_inj']

      -- sorry
    rw [Fintype.prod_equiv index _ _ h_index_map]

  rw [h_to_fin_prod]


  #check prod_equiv index _ _
  #check prod_map univ index.toEmbedding
  #check Fintype.prod_equiv index

  #check Set.Iio_union_Ioi
  #check Set.Iio_union_Ioi (α := Fin (minpoly ℚ y).natDegree)
  #check compl_singleton

  have h_to_ioi_iio_prod : ∏ x : Fin (minpoly ℚ y).natDegree, ∏ x_1 ∈ (univ : Finset (Fin (minpoly ℚ y).natDegree)).erase x,
      ((index x : ℂ) - index x_1)
      = (∏ x : Fin (minpoly ℚ y).natDegree, ∏ x_1 ∈ Ioi x, ((index x : ℂ) - index x_1)) *
      ∏ x : Fin (minpoly ℚ y).natDegree, ∏ x_1 ∈ Iio x, ((index x : ℂ) - index x_1) := by

    rw [← prod_mul_distrib]

    rw [Fintype.prod_congr]
    intro x
    have h_erase_eq_ioi_cup_iio : univ.erase x = Ioi x ∪ Iio x := by
      apply Finset.ext
      intro x_1
      simp only [mem_erase, mem_univ, and_true, mem_union, mem_Ioi,
        mem_Iio]
      exact lt_or_gt_iff_ne'.symm
    have h_ioi_iio_disjoint : Disjoint (Ioi x) (Iio x) := by
      exact disjoint_Ioi_Iio x

    rw [h_erase_eq_ioi_cup_iio]

    #check prod_union
    #check prod_union h_ioi_iio_disjoint

    rw [prod_union h_ioi_iio_disjoint]


  rw [h_to_ioi_iio_prod]


  have h_to_ioi_prod : (∏ x, ∏ x_1 ∈ Ioi x, ((index x : ℂ) - index x_1)) *
      ∏ x, ∏ x_1 ∈ Iio x, ((index x : ℂ) - index x_1)
      = - ∏ x : Fin (minpoly ℚ y).natDegree, ∏ x_1 ∈ Ioi x, ((index x_1 : ℂ) - index x) ^ 2 := by

    have h_iio_to_with : ∏ x, ∏ x_1 ∈ Iio x, ((index x : ℂ) - index x_1) =
        ∏ x, ∏ x_1 with x_1 < x, ((index x : ℂ) - index x_1) := by
      rw [Fintype.prod_congr]
      intro x

      -- #check prod_subtype_eq_prod_filter
      -- rw [← prod_subtype_eq_prod_filter]

      have h_iio_eq_filter : (univ : Finset (Fin (minpoly ℚ y).natDegree)).filter (fun x_1 ↦ x_1 < x) =
          Iio x := by
        apply Finset.ext
        intro x_1
        simp only [mem_filter, mem_univ, true_and, mem_Iio]

      rw [← h_iio_eq_filter]

    #check Filter.prod_comm
    #check prod_comm

    have h_iio_to_ioi : ∏ x, ∏ x_1 ∈ Iio x, ((index x : ℂ) - index x_1) =
        - ∏ x, ∏ x_1 ∈ Ioi x, ((index x : ℂ) - index x_1) := by

      have h_iio_iff_ioi : ∀ (x : Fin (minpoly ℚ y).natDegree) (x_1 : Fin (minpoly ℚ y).natDegree), x ∈ univ ∧ x_1 ∈ Iio x ↔
          x ∈ Ioi x_1 ∧ x_1 ∈ univ := by
        intro x x_1
        simp only [mem_univ, true_and, mem_Iio, and_true, mem_Ioi]

      #check prod_comm' (s := (univ : Finset (Fin (minpoly ℚ y).natDegree))) (t := Iio) (t' := (univ : Finset (Fin (minpoly ℚ y).natDegree))) (s' := Ioi) h_iio_iff_ioi

      rw [prod_comm' (s := (univ : Finset (Fin (minpoly ℚ y).natDegree))) (t := Iio)
          (t' := (univ : Finset (Fin (minpoly ℚ y).natDegree))) (s' := Ioi) h_iio_iff_ioi]

      -- #check Fin.card_Ioi
      #check Nat.geomSum_eq

      calc
        ∏ y, ∏ x ∈ Ioi y, ((index x : ℂ) - index y)
        = ∏ y, ∏ x ∈ Ioi y, (-1) * ((index y : ℂ) - index x) := by simp
        _ = ∏ y, ((∏ x ∈ Ioi y, (-1)) * ∏ x ∈ Ioi y, ((index y : ℂ) - index x)) := by
          rw [Fintype.prod_congr]
          intro y
          rw [← prod_mul_distrib]
        _ = (∏ y, ∏ x ∈ Ioi y, (-1)) * ∏ y, ∏ x ∈ Ioi y, ((index y : ℂ) - index x) := by
          rw [← prod_mul_distrib]
        _ = (∏ y : Fin (minpoly ℚ y).natDegree, (-1) ^ (2 - y.val)) * ∏ y, ∏ x ∈ Ioi y, ((index y : ℂ) - index x) := by
          rw [Fintype.prod_congr]
          intro y
          rw [prod_const]
          rw [Fin.card_Ioi]
          congr
          rw [hf_rat_minpoly]
          rw [hf_rat_natDeg]
        _ = (-1) ^ (∑ y : Fin (minpoly ℚ y).natDegree, (2 - y.val)) * ∏ y, ∏ x ∈ Ioi y, ((index y : ℂ) - index x) := by
          rw [prod_pow_eq_pow_sum]
        -- _ = (-1) ^ (∑ y ∈ range 3, (2 - y)) * ∏ x, ∏ x_1 ∈ Ioi x, (↑(index x) - ↑(index x_1)) := by
        --   rw [Fin.sum_univ_eq_sum_range]
        -- _ = (-1) ^ (∑ y ∈ range 3, 2 - ∑ y ∈ range 3, y) * ∏ x, ∏ x_1 ∈ Ioi x, (↑(index x) - ↑(index x_1)) := by
        _ = (-1) ^ (∑ y : Fin 3, (2 - y.val)) * ∏ y, ∏ x ∈ Ioi y, ((index y : ℂ) - index x) := by
          rw [← Fin.sum_congr' _ (by rw [hf_rat_minpoly, hf_rat_natDeg] : 3 = (minpoly ℚ y).natDegree)]
          simp
        _ = - ∏ y, ∏ x ∈ Ioi y, ((index y : ℂ) - index x) := by
          rw [Fin.sum_univ_three]
          norm_num

    -- #check Fin.card_Ioi

      -- rw [mem_Iio]

      -- sorry

    rw [h_iio_to_ioi, mul_neg, ← prod_mul_distrib]
    congr
    ext x
    rw [← prod_mul_distrib]
    congr
    ext x_1
    ring_nf

  rw [h_to_ioi_prod]

  simp only [eq_ratCast, Rat.cast_neg, neg_inj]





  --   sorry
  -- have h_roots_aroots : f_split.roots.toFinset ≃ { x // x ∈ (minpoly ℚ y).aroots ℂ } := by
  --   rw [hf_rat_minpoly]
  --   have h_rat_aroots : f_rat.aroots ℂ = f_split.roots := by
  --     rw [aroots_def]
  --   rw [h_rat_aroots]
  --   simp
  --   rfl



  -- have h_roots_aroots_multiset : f_split.roots = (minpoly ℚ y).aroots ℂ := by
  --   rw [aroots_def]
  --   rw [hf_rat_minpoly]
  -- have h_roots_aroots : f_split.roots.toFinset = ((minpoly ℚ y).aroots ℂ).toFinset := by
  --   congr

  -- let roots_finset_aroots_finset : f_split.roots.toFinset ≃ { x // x ∈ ((minpoly ℚ y).aroots ℂ).toFinset } :=
  --   Equiv.subtypeEquivRight (Finset.ext_iff.mp h_roots_aroots)
  -- let aroots_finset_aroots : { x // x ∈ ((minpoly ℚ y).aroots ℂ).toFinset } ≃ { x // x ∈ (minpoly ℚ y).aroots ℂ } :=
  --   Equiv.subtypeEquivRight (by intro x ; exact Multiset.mem_toFinset : ∀ (x : ℂ), x ∈ ((minpoly ℚ y).aroots ℂ).toFinset ↔ x ∈ (minpoly ℚ y).aroots ℂ)

  have h_roots_iff_aroots : ∀ (x : ℂ), x ∈ f_split.roots.toFinset ↔ x ∈ (minpoly ℚ y).aroots ℂ := by
    intro x
    rw [Multiset.mem_toFinset]
    rw [aroots_def]
    rw [hf_rat_minpoly]
  let roots_aroots : f_split.roots.toFinset ≃ { x // x ∈ (minpoly ℚ y).aroots ℂ } := Equiv.subtypeEquivRight h_roots_iff_aroots

  #check Equiv.subtypeEquivRight
  #check Equiv.subtypeEquivRight_apply

  #check Set.Finite.subtypeEquivToFinset
  #check Multiset.mem_toFinset

  let index' : Fin (minpoly ℚ y).natDegree ≃ { x // x ∈ (minpoly ℚ y).aroots ℂ } := index.trans roots_aroots
  let embed_roots : (ℚ⟮y⟯ →ₐ[ℚ] ℂ) ≃ { x // x ∈ (minpoly ℚ y).aroots ℂ } :=
    IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := ℂ) y_integral'
  let index'' : Fin (minpoly ℚ y).natDegree ≃ (ℚ⟮y⟯ →ₐ[ℚ] ℂ) := index'.trans embed_roots.symm

  -- rw [← hf_rat_natDeg] at index''
  -- rw [← hf_rat_minpoly] at index''

  -- #check h index''

  -- let embed : Fin (minpoly ℚ y).natDegree ≃ (F →ₐ[ℚ] ℂ) :=

  let y' := IntermediateField.AdjoinSimple.gen ℚ y

  have h_to_index'' : ∏ x, ∏ x_1 ∈ Ioi x, ((index x_1 : ℂ) - index x) ^ 2 =
      ∏ x, ∏ x_1 ∈ Ioi x, ((index'' x_1) y' - (index'' x) y') ^ 2 := by
    rw [Fintype.prod_congr]
    intro x_1
    rw [← Finset.prod_coe_sort (Ioi x_1)]
    rw [← Finset.prod_coe_sort (Ioi x_1)]
    rw [Fintype.prod_congr]
    intro x
    have h_index_index'' : ∀ x, index x = (index'' x) y' := by
      intro x
      dsimp only [index'']
      rw [Equiv.trans_apply]
      dsimp only [embed_roots, y']
      erw [IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen]
      dsimp only [index']
      rw [Equiv.trans_apply]
      rw [Equiv.subtypeEquivRight_apply]
    rw [h_index_index'', h_index_index'']



  -- rw [h index'']

  #check Equiv.trans_apply index roots_aroots


  #check IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := ℂ) y_integral'

  #check IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ (K := ℂ) y_integral'

  rw [h_to_index'']
  -- rw [← hf_rat_natDeg] at index''
  -- rw [← hf_rat_minpoly] at index''
  symm

  have h := Algebra.discr_powerBasis_eq_prod ℚ ℂ pb
  -- rw [h]
  simp only [IntermediateField.adjoin.powerBasis_dim, eq_ratCast,
    IntermediateField.adjoin.powerBasis_gen] at h
  -- rw [hf_rat_minpoly] at h

  erw [h index'']
  dsimp only [index'', y']
  rfl


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
