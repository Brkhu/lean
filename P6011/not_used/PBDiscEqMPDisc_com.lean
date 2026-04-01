-- import Brkhu.P6011.YTheta

-- set_option linter.style.emptyLine false

-- open NumberField


-- for discr and resultants of polynomials
import Mathlib.RingTheory.Polynomial.Resultant.Basic
-- for irreducible_iff_roots_eq_zero_of_degree_le_three
import Mathlib.Algebra.Polynomial.SpecificDegree
-- for Gauss's lemma
import Mathlib.RingTheory.Polynomial.GaussLemma
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


-- noncomputable def power_base (x : B) (n : ℕ) : Fin n → B := fun k => x ^ k.val

noncomputable abbrev b := NumberField.integralBasis ℚ⟮y⟯
noncomputable abbrev pb := IntermediateField.adjoin.powerBasis y_integral'

lemma discr_powbasis_f : f.discr = Algebra.discr ℚ pb.basis := by
  sorry

lemma discr_powbasis_integralbasis : ∃ (m : ℤ), Algebra.discr ℚ pb.basis = m ^ 2 * discr F := by
  -- 第一种思路: 去到 ℚ 上工作

  -- #check @IntermediateField.topEquiv ℚ _ F _ _
  have h := IntermediateField.topEquiv (F := ℚ) (E := F)
  -- #check NumberField.discr_eq_discr_of_algEquiv F h.symm
  rw [NumberField.discr_eq_discr_of_algEquiv F h.symm, ← y_gen_top]


  rw [NumberField.coe_discr]



  -- #check b.toMatrix pb.basis
  -- #check b.reindex (b.indexEquiv pb.basis)

  -- let b' := b.reindex (b.indexEquiv pb.basis)
  -- let pb' := pb.basis.reindex (pb.basis.indexEquiv b)
  let pb' := pb.basis ∘ ⇑(pb.basis.indexEquiv b).symm

  -- #check Algebra.discr_powerBasis_eq_norm ℚ pb
  -- #check Algebra.adjoin.powerBasis
  -- #check Algebra.adjoin.powerBasis hy_integral
  -- #check IsAdjoinRootMonic.basis
  -- #check @PowerBasis.ofAdjoinEqTop' ℤ (𝓞 F) _ _ _ _ _ _ _ yO hyO_integral
  -- #check Algebra.discr
  -- #check @Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral (Module.Free.ChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯)) (Fin pb.dim) ℚ⟮y⟯ _ _ _ _ _ _ b pb.basis h1 h2
  -- #check IntermediateField.adjoin.powerBasis hy_integral

  -- rw [Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral ℚ⟮y⟯ h1 h2]

  #check b.indexEquiv pb.basis

  #check Algebra.discr_of_matrix_vecMul b (b.toMatrix pb')
  have h1 := Algebra.discr_of_matrix_vecMul b (b.toMatrix pb')

  -- have hint : ∀ i j, IsIntegral ℤ (b.toMatrix pb' i j) := by
  --   sorry
  -- let M := b.toMatrix pb'
  -- have hdetint := IsIntegral.det hint
  -- obtain ⟨m, hm⟩ := (IsIntegral.exists_int_iff_exists_rat hdetint).mp (by simp)
  -- use m
  -- rw [← hm]

  have hint : ∀ i j, b.toMatrix pb' i j ∈ Set.range (Int.cast (R := ℚ)) := by
    intro i j
    #check Module.Basis.toMatrix_apply
    rw [Module.Basis.toMatrix_apply]
    #check algebraMap_int_eq ℚ
    have h_algmap_intcast : algebraMap ℤ ℚ = Int.cast (R := ℚ) := by rfl
    rw [← h_algmap_intcast]
    #check (Module.Basis.mem_span_iff_repr_mem ℤ b (pb' j)).mp
    -- apply (mem_span_integralBasis F).mpr
    have h_pb' : pb' j ∈ Submodule.span ℤ (Set.range b) := by
      apply (NumberField.mem_span_integralBasis ℚ⟮y⟯).mpr
      have h_pb : ∀ (n : Fin pb.dim), pb.basis n ∈ (algebraMap (𝓞 ℚ⟮y⟯) ℚ⟮y⟯).range := by
        intro n
        rw [pb.basis_eq_pow n]
        have h_pow_integral : IsIntegral ℤ (pb.gen ^ n.val) := by
          apply IsIntegral.pow
          -- exact pb.isIntegral_gen
          -- exact PowerBasis.isIntegral_gen pb
          -- apply (IntermediateField.isIntegral_iff (K := ℚ) (L := F) (S := ℚ⟮y⟯)).mpr
          apply IntermediateField.coe_isIntegral_iff.mp
          have h_gen_y : pb.gen = y := by rfl
          exact y_integral
        apply RingHom.mem_range.mpr
        use ⟨pb.gen ^ n.val, h_pow_integral⟩
        simp
      exact h_pb ((pb.basis.indexEquiv b).symm j)

    exact (Module.Basis.mem_span_iff_repr_mem ℤ b (pb' j)).mp h_pb' i
    -- #check Module.Basis.mem_span_iff_repr_mem ℤ b
    -- sorry
  let M := b.toMatrix pb'
  -- #check AlgHom.mapMatrix_apply (algebraMap ℤ ℚ)
  -- #check Matrix.map_algebraMap ℤ
  #check Matrix.map_apply (f := algebraMap ℤ ℚ)
  #check Matrix.map_apply (f := Int.cast (R := ℚ))
  -- have hdetint := IsIntegral.det hint
  -- have hrep : ∃ (M' : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯)) (Module.Free.ChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯)) ℤ), M = M'.map (Int.cast (R := ℚ)) := by
  choose f hf using hint
  let MZ : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯)) (Module.Free.ChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯)) ℤ := Matrix.of f
  have h_rep : M = MZ.map (Int.cast (R := ℚ)) := by
    ext i j
    simp [Matrix.map_apply, M, MZ]
    exact (hf i j).symm
  #check Set.mapsTo_range_iff
  use MZ.det
  #check Int.cast
  rw [Int.cast_det]
  -- rw [Matrix.map_apply]
  rw [← h_rep]

  rw [← Algebra.discr_of_matrix_vecMul b (b.toMatrix pb')]

  rw [Module.Basis.toMatrix_map_vecMul b pb']

  have h : Algebra.discr ℚ pb.basis = Algebra.discr ℚ pb' := by
    dsimp only [pb']
    have h' := Algebra.discr_reindex ℚ pb.basis (pb.basis.indexEquiv b)
    exact h'.symm
  exact h
  -- have h3 := Algebra.discr_reindex ℚ pb.basis (pb.basis.indexEquiv b)
  -- have h3 : @Algebra.discr (Fin (minpoly ℚ y).natDegree) (instDecidableEqFin pb.dim) ℚ (↥ℚ⟮y⟯) Field.toEuclideanDomain.toCommRing Field.toEuclideanDomain.toCommRing ℚ⟮y⟯.algebra' (Fin.fintype (minpoly ℚ y).natDegree) ⇑pb.basis = @Algebra.discr (Fin pb.dim) (instDecidableEqFin pb.dim) ℚ (↥ℚ⟮y⟯) Field.toEuclideanDomain.toCommRing Field.toEuclideanDomain.toCommRing ℚ⟮y⟯.algebra' (Fin.fintype pb.dim) ⇑pb.basis := by rfl

  -- have h3 : @Algebra.discr (Module.Free.ChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯)) (Module.Free.instDecidableEqChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯)) ℚ (↥ℚ⟮y⟯) Rat.commRing Field.toEuclideanDomain.toCommRing DivisionRing.toRatAlgebra (Module.Free.ChooseBasisIndex.fintype ℤ (𝓞 ↥ℚ⟮y⟯)) (⇑pb.basis ∘ ⇑(pb.basis.indexEquiv b).symm) = @Algebra.discr (Module.Free.ChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯)) (Module.Free.instDecidableEqChooseBasisIndex ℤ (𝓞 ↥ℚ⟮y⟯)) ℚ (↥ℚ⟮y⟯) Field.toEuclideanDomain.toCommRing Field.toEuclideanDomain.toCommRing ℚ⟮y⟯.algebra' (Module.Free.ChooseBasisIndex.fintype ℤ (𝓞 ↥ℚ⟮y⟯)) (⇑pb.basis ∘ ⇑(pb.basis.indexEquiv b).symm) := by rfl

  -- rw [h3]
  -- rw [(by sorry : (minpoly ℚ y).natDegree = pb.dim)] at h3

  -- congr 2



  -- have hO_rank : Module.finrank ℤ (𝓞 F) = 3 := by
  --   rw [NumberField.RingOfIntegers.rank F, rank_F_eq_three]

  -- let b := Module.finBasis ℤ (𝓞 F)
  -- rw [hO_rank] at b

  -- rw [← NumberField.discr_eq_discr F b]

  -- let pb : Fin 3 → 𝓞 F := power_base yO 3
  -- have discr_powbase_eq_discr_minpoly : f.discr = Algebra.discr ℤ pb := by
  --   dsimp [pb]
  --   rw [← hf_natDeg]
  --   exact (power_base_discr_eq_minpoly_discr yO f hf_monic f_yO_root).symm

  -- let pb : Fin 3 → 𝓞 F := power_base yO 3
  -- have discr_powbase_eq_discr_minpoly : f.discr = Algebra.discr ℤ pb := by
  --   dsimp [pb]
  --   rw [← hf_natDeg]
  --   exact (power_base_discr_eq_minpoly_discr yO f hf_monic f_yO_root).symm

  -- have h := Algebra.discr_of_matrix_vecMul b (b.toMatrix pb)
  -- rw [b.toMatrix_map_vecMul] at h

  -- use (b.toMatrix pb).det
  -- rw [discr_powbase_eq_discr_minpoly]
  -- exact h



theorem h_discr_rel : ∃ (m : ℤ), f.discr = m ^ 2 * NumberField.discr F := by
  sorry
