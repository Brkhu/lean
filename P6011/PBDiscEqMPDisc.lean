import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.Qify
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

import Mathlib.NumberTheory.NumberField.Discriminant.Defs


import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Multiset.MapFold


import brkhu.P6011.Defs
import brkhu.P6011.MinPolyTheta
import brkhu.P6011.MinPolyY
import brkhu.P6011.YTheta


set_option linter.style.emptyLine false

open scoped IntermediateField
open Polynomial NumberField Finset


variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]


noncomputable abbrev b := NumberField.integralBasis ℚ⟮y⟯
noncomputable abbrev pb := IntermediateField.adjoin.powerBasis y_integral'


lemma discr_powbasis_f : f.discr = Algebra.discr ℚ pb.basis := by
  have h_to_resultant := resultant_deriv (f := f) (by rw [hf_deg]; norm_num)
  rw [hf_natDeg, (Monic.def).mp hf_monic] at h_to_resultant
  simp only [Nat.add_one_sub_one, Int.reduceNeg, Nat.reduceMul, Nat.reduceDiv, Int.reducePow,
    mul_one, neg_mul, one_mul] at h_to_resultant
  rw [Int.eq_neg_comm] at h_to_resultant

  rw [h_to_resultant]

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
  have h_f_split_root_nodup : Multiset.Nodup f_split.roots := by
    apply nodup_roots
    have h_f_rat_separable : Separable f_rat := by
      exact Irreducible.separable hf_rat_irreducible
    dsimp only [f_split]
    exact Separable.map h_f_rat_separable


  have h_Qybar_inj : Function.Injective (algebraMap ℚ ℂ) := by
    exact Rat.cast_injective

  apply h_Qybar_inj


  have h_to_split : algebraMap ℚ ℂ (f_rat.resultant (derivative f_rat) 3 2) =
      f_split.resultant f_split.derivative 3
      2 := by
    dsimp only [f_split]
    rw [← resultant_map_map f_rat f_rat.derivative 3 2 (algebraMap ℚ ℂ)]
    rw [derivative_map f_rat]

  rw [h_to_split]


  have h_to_prod := resultant_eq_prod_eval f_split f_split.derivative (f_split.natDegree - 1)
      (Polynomial.natDegree_derivative_le f_split) h_f_split_splits
  rw [h_f_split_natDeg, h_f_split_monic] at h_to_prod
  norm_num at h_to_prod

  rw [h_to_prod]


  have h_to_double_prod : (Multiset.map (fun x ↦ eval x (derivative f_split)) f_split.roots).prod =
      (Multiset.map (fun x ↦ (Multiset.map (fun x_1 ↦ x - x_1) (f_split.roots.erase x)).prod)
      f_split.roots).prod := by
    congr 1
    have h_eval_deriv : ∀ x ∈ f_split.roots, eval x (derivative f_split) = (Multiset.map
        (fun x_1 ↦ x - x_1) (f_split.roots.erase x)).prod := by
      intro _ hx
      exact Polynomial.Splits.eval_root_derivative h_f_split_splits h_f_split_monic hx
    exact Multiset.map_congr (by rfl) h_eval_deriv

  rw [h_to_double_prod]


  have h_to_fin_double_prod : (Multiset.map (fun x ↦ (Multiset.map (fun x_1 ↦ x - x_1)
      (f_split.roots.erase x)).prod) f_split.roots).prod
      = ∏ x : f_split.roots.toFinset, ∏ x_1 ∈ f_split.roots.toFinset.erase x, (x - x_1) := by
    rw [← prod_mk f_split.roots h_f_split_root_nodup]
    rw [Multiset.toFinset_eq h_f_split_root_nodup]

    rw [← prod_coe_sort]
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
    apply Fintype.equivOfCardEq
    simp only [Fintype.card_fin, Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def,
      Fintype.card_coe, Multiset.toFinset_card_of_nodup h_f_split_root_nodup]
    have h_root_card := Splits.natDegree_eq_card_roots h_f_split_splits
    rw [← h_root_card]
    rw [hf_rat_minpoly, h_f_split_natDeg]
    exact hf_rat_natDeg


  have h_to_fin_prod : ∏ x : f_split.roots.toFinset, ∏ x_1 ∈ f_split.roots.toFinset.erase x,
      (x - x_1) =
      ∏ x : Fin (minpoly ℚ y).natDegree, ∏ x_1 ∈ (univ : Finset
      (Fin (minpoly ℚ y).natDegree)).erase x, ((index x : ℂ) - index x_1) := by
    let index_map_f : Fin (minpoly ℚ y).natDegree → ℂ := (fun x ↦ ∏ x_1 ∈ (univ : Finset (Fin
        (minpoly ℚ y).natDegree)).erase x, ((index x : ℂ) - index x_1))
    let index_map_g : f_split.roots.toFinset → ℂ := (fun (ix : f_split.roots.toFinset) ↦
        ∏ x_1 ∈ f_split.roots.toFinset.erase ix, (ix - x_1))
    have h_index_map : ∀ (x : Fin (minpoly ℚ y).natDegree), index_map_f x = index_map_g (index x)
        := by
      intro x
      dsimp [index_map_f, index_map_g]

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

    rw [Fintype.prod_equiv index _ _ h_index_map]

  rw [h_to_fin_prod]


  have h_to_ioi_iio_prod : ∏ x : Fin (minpoly ℚ y).natDegree, ∏ x_1 ∈ (univ : Finset (Fin (minpoly
      ℚ y).natDegree)).erase x, ((index x : ℂ) - index x_1)
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
    rw [prod_union h_ioi_iio_disjoint]

  rw [h_to_ioi_iio_prod]


  have h_to_ioi_prod : (∏ x, ∏ x_1 ∈ Ioi x, ((index x : ℂ) - index x_1)) *
      ∏ x, ∏ x_1 ∈ Iio x, ((index x : ℂ) - index x_1)
      = - ∏ x : Fin (minpoly ℚ y).natDegree, ∏ x_1 ∈ Ioi x, ((index x_1 : ℂ) - index x) ^ 2 := by

    have h_iio_to_with : ∏ x, ∏ x_1 ∈ Iio x, ((index x : ℂ) - index x_1) =
        ∏ x, ∏ x_1 with x_1 < x, ((index x : ℂ) - index x_1) := by
      rw [Fintype.prod_congr]
      intro x

      have h_iio_eq_filter : (univ : Finset (Fin (minpoly ℚ y).natDegree)).filter
          (fun x_1 ↦ x_1 < x) = Iio x := by
        apply Finset.ext
        intro x_1
        simp only [mem_filter, mem_univ, true_and, mem_Iio]
      rw [← h_iio_eq_filter]

    have h_iio_to_ioi : ∏ x, ∏ x_1 ∈ Iio x, ((index x : ℂ) - index x_1) =
        - ∏ x, ∏ x_1 ∈ Ioi x, ((index x : ℂ) - index x_1) := by

      have h_iio_iff_ioi : ∀ (x : Fin (minpoly ℚ y).natDegree) (x_1 : Fin (minpoly ℚ y).natDegree),
          x ∈ univ ∧ x_1 ∈ Iio x ↔ x ∈ Ioi x_1 ∧ x_1 ∈ univ := by
        intro x x_1
        simp only [mem_univ, true_and, mem_Iio, and_true, mem_Ioi]

      rw [prod_comm' (s := (univ : Finset (Fin (minpoly ℚ y).natDegree))) (t := Iio)
          (t' := (univ : Finset (Fin (minpoly ℚ y).natDegree))) (s' := Ioi) h_iio_iff_ioi]

      calc
        ∏ y, ∏ x ∈ Ioi y, ((index x : ℂ) - index y)
        = ∏ y, ∏ x ∈ Ioi y, (-1) * ((index y : ℂ) - index x) := by simp
        _ = ∏ y, ((∏ x ∈ Ioi y, (-1)) * ∏ x ∈ Ioi y, ((index y : ℂ) - index x)) := by
          rw [Fintype.prod_congr]
          intro y
          rw [← prod_mul_distrib]
        _ = (∏ y, ∏ x ∈ Ioi y, (-1)) * ∏ y, ∏ x ∈ Ioi y, ((index y : ℂ) - index x) := by
          rw [← prod_mul_distrib]
        _ = (∏ y : Fin (minpoly ℚ y).natDegree, (-1) ^ (2 - y.val)) * ∏ y, ∏ x ∈ Ioi y,
            ((index y : ℂ) - index x) := by
          rw [Fintype.prod_congr]
          intro y
          rw [prod_const, Fin.card_Ioi]
          congr
          rw [hf_rat_minpoly, hf_rat_natDeg]
        _ = (-1) ^ (∑ y : Fin (minpoly ℚ y).natDegree, (2 - y.val)) * ∏ y, ∏ x ∈ Ioi y,
            ((index y : ℂ) - index x) := by
          rw [prod_pow_eq_pow_sum]
        _ = (-1) ^ (∑ y : Fin 3, (2 - y.val)) * ∏ y, ∏ x ∈ Ioi y, ((index y : ℂ) - index x) := by
          rw [← Fin.sum_congr' _ (by rw [hf_rat_minpoly, hf_rat_natDeg] : 3 =
            (minpoly ℚ y).natDegree)]
          simp only [Fin.val_cast]
        _ = - ∏ y, ∏ x ∈ Ioi y, ((index y : ℂ) - index x) := by
          rw [Fin.sum_univ_three]
          norm_num

    rw [h_iio_to_ioi, mul_neg, ← prod_mul_distrib]
    congr
    ext x
    rw [← prod_mul_distrib]
    congr
    ext x_1
    ring_nf

  rw [h_to_ioi_prod]

  simp only [eq_ratCast, Rat.cast_neg, neg_inj]


  have h_roots_iff_aroots : ∀ (x : ℂ), x ∈ f_split.roots.toFinset ↔ x ∈ (minpoly ℚ y).aroots ℂ := by
    intro x
    rw [Multiset.mem_toFinset]
    rw [aroots_def]
    rw [hf_rat_minpoly]
  let roots_aroots : f_split.roots.toFinset ≃ { x // x ∈ (minpoly ℚ y).aroots ℂ } :=
    Equiv.subtypeEquivRight h_roots_iff_aroots
  let index' : Fin (minpoly ℚ y).natDegree ≃ { x // x ∈ (minpoly ℚ y).aroots ℂ } :=
    index.trans roots_aroots
  let embed_roots : (ℚ⟮y⟯ →ₐ[ℚ] ℂ) ≃ { x // x ∈ (minpoly ℚ y).aroots ℂ } :=
    IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := ℂ) y_integral'
  let index'' : Fin (minpoly ℚ y).natDegree ≃ (ℚ⟮y⟯ →ₐ[ℚ] ℂ) := index'.trans embed_roots.symm


  let y' := IntermediateField.AdjoinSimple.gen ℚ y

  have h_to_index'' : ∏ x, ∏ x_1 ∈ Ioi x, ((index x_1 : ℂ) - index x) ^ 2 =
      ∏ x, ∏ x_1 ∈ Ioi x, ((index'' x_1) y' - (index'' x) y') ^ 2 := by
    rw [Fintype.prod_congr]
    intro x
    rw [← Finset.prod_coe_sort (Ioi x), ← Finset.prod_coe_sort (Ioi x), Fintype.prod_congr]
    intro x_1
    have h_index_index'' : ∀ a, index a = (index'' a) y' := by
      intro a
      dsimp only [index'']
      rw [Equiv.trans_apply]
      dsimp only [embed_roots, y']
      erw [IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen]
      dsimp only [index']
      rw [Equiv.trans_apply]
      rw [Equiv.subtypeEquivRight_apply]
    rw [h_index_index'', h_index_index'']

  rw [h_to_index'']


  have h := Algebra.discr_powerBasis_eq_prod ℚ ℂ pb
  simp only [IntermediateField.adjoin.powerBasis_dim, eq_ratCast,
    IntermediateField.adjoin.powerBasis_gen] at h

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
