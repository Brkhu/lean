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

  let f_split : (AlgebraicClosure ℚ)[X] := f_rat.map (algebraMap ℚ (AlgebraicClosure ℚ))
  have h_f_split_natDeg : f_split.natDegree = 3 := by
    dsimp only [f_split]
    rw [Polynomial.natDegree_map (algebraMap ℚ (AlgebraicClosure ℚ)), hf_rat_natDeg]
  have h_f_split_monic : Monic f_split := by
    apply (Monic.def).mpr
    dsimp only [f_split]
    rw [Polynomial.leadingCoeff_map (algebraMap ℚ (AlgebraicClosure ℚ)), hf_rat_monic]
    simp

  have h_to_split : algebraMap ℚ (AlgebraicClosure ℚ) (f_rat.resultant (derivative f_rat) 3 2) =
      f_split.resultant f_split.derivative 3
      2 := by
    dsimp only [f_split]
    rw [← resultant_map_map f_rat f_rat.derivative 3 2 (algebraMap ℚ (AlgebraicClosure ℚ))]
    rw [derivative_map f_rat]

  -- #check Algebra.discr_powerBasis_eq_prod ℚ (AlgebraicClosure ℚ⟮y⟯) pb
  have h_Qybar_inj : Function.Injective (algebraMap ℚ (AlgebraicClosure ℚ)) := by
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


  #check resultant_map_map f_rat f_rat.derivative f_rat.natDegree f_rat.derivative.natDegree (algebraMap ℚ (AlgebraicClosure ℚ))

  have hf'_natDeg_leq : f_split.derivative.natDegree ≤ 2 := by
    have h_leq := Polynomial.natDegree_derivative_le f_split
    rw [h_f_split_natDeg, (by norm_num : 3 - 1 = 2)] at h_leq
    exact h_leq

  have h_to_prod := resultant_eq_prod_eval f_split f_split.derivative (f_split.natDegree - 1)
      (Polynomial.natDegree_derivative_le f_split) (IsAlgClosed.splits f_split)
  rw [h_f_split_natDeg, h_f_split_monic] at h_to_prod
  norm_num at h_to_prod

  rw [h_to_prod]

  #check Polynomial.Splits.eval_root_derivative
  -- rw [Polynomial.Splits.eval_root_derivative]



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
