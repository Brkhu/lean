-- for discr and resultants of polynomials
import Mathlib.RingTheory.Polynomial.Resultant.Basic
-- for qify
import Mathlib.Tactic.Qify
-- for rational integral over Z
import Mathlib.NumberTheory.Niven
-- for ring of integer as range
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

import Mathlib.NumberTheory.NumberField.Discriminant.Defs


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

lemma discr_powbasis_f : f.discr = Algebra.discr ℚ pb.basis := by

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
          have h_gen_y : pb.gen = y := by rfl
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
