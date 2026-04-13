import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

open Matrix

set_option linter.style.emptyLine false

variable {n : ℕ} {k : Type u} [Field k]

-- def is_eigenvector (T : Matrix (Fin n) (Fin n) k) (a : k) (v : Fin n → k) : Prop :=
--   T.mulVec v = a • v

lemma has_eigenvalue [IsAlgClosed k] (T : Matrix (Fin n) (Fin n) k) (hn : n ≠ 0) :
    ∃ a : k, T.charpoly.IsRoot a := by
  have h_deg : T.charpoly.degree ≠ 0 := by
    simp [charpoly_degree_eq_dim, hn]
  exact IsAlgClosed.exists_root T.charpoly h_deg

lemma has_eigenvector (T : Matrix (Fin n) (Fin n) k) (a : k) (ha : T.charpoly.IsRoot a) :
    ∃ v : Fin n → k, v ≠ 0 ∧ (T.mulVec v = a • v) := by
  rw [Polynomial.IsRoot.def, eval_charpoly] at ha
  apply exists_mulVec_eq_zero_iff.mpr at ha
  obtain ⟨v, hv1, hv2⟩ := ha
  simp [sub_mulVec, sub_eq_zero] at hv2
  exact ⟨v, hv1, hv2.symm⟩

lemma has_vectoreigen (T : Matrix (Fin n) (Fin n) k) (a : k) (ha : T.charpoly.IsRoot a) :
    ∃ w : Fin n → k, w ≠ 0 ∧ (T.vecMul w = a • w) := by
  rw [Polynomial.IsRoot.def, eval_charpoly] at ha
  apply exists_vecMul_eq_zero_iff.mpr at ha
  obtain ⟨w, hw1, hw2⟩ := ha
  simp [vecMul_sub, sub_eq_zero] at hw2
  exact ⟨w, hw1, hw2.symm⟩

-- lemma common_eigenvector {T U : Matrix (Fin n) (Fin n) k} (h : (T * U - U * T).rank = 1) :
--   ∃ v : Fin n → k, v ≠ 0 ∧ is_eigenvector T v ∧ is_eigenvector U v := by

--   sorry

lemma rank_one_nonempty (A : Matrix (Fin n) (Fin n) k) (h : A.rank = 1) : n ≠ 0 := by
  intro hn
  have : IsEmpty (Fin n) := by
    rw [hn]
    exact Fin.isEmpty
  have h_unit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simp only [Matrix.det_isEmpty, isUnit_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true]
  rw [Matrix.rank_of_isUnit A h_unit] at h
  simp only [hn, Fintype.card_eq_zero, zero_ne_one] at h

lemma rank_one_as_mul_vec (A : Matrix (Fin n) (Fin n) k) (h : A.rank ≤ 1) (hn : n ≠ 0) :
  ∃ v w : Fin n → k, A = vecMulVec v w := by
  by_cases h_zero : A = 0
  · use 0, 0
    simp [h_zero]
  · apply ext_iff.not.mpr at h_zero
    simp only [zero_apply, not_forall] at h_zero
    obtain ⟨i, j, hij⟩ := h_zero
    rw [← ne_eq] at hij
    -- use A.col j, (A.row i) / A i j
    use (fun i => A i j), (fun j' => A i j' / A i j)
    ext i' j'
    rw [vecMulVec_apply]
    field_simp
    -- have h_sub_le :
    -- #check rank_transpose
    by_cases hi : i' = i
    · rw [hi, mul_comm]
    rw [← ne_eq] at hi
    by_cases hj : j' = j
    · rw [hj, mul_comm]
    rw [← ne_eq] at hj

    -- let r : ({i, i'} : Set (Fin n)) → Fin n := fun x ↦ x.1
    -- let c : ({j, j'} : Set (Fin n)) → Fin n := fun x ↦ x.1

    let r : Fin 2 → Fin n := fun x => if x = 0 then i else i'
    let c : Fin 2 → Fin n := fun x => if x = 0 then j else j'

    let A_sub := A.submatrix r c
    have h_sub_le : A_sub.rank ≤ 1 := by
      -- #check rank_submatrix_le
      rw [← cRank_toNat_eq_rank]
      #check Cardinal.toNat_ofNat 2
      #check Cardinal.toNat_le_toNat (d := 2) _ (by simp)
      have h_sub_c_le := cRank_submatrix_le A r c
      apply Cardinal.toNat_le_toNat at h_sub_c_le


      sorry
    have h_sub_degenerate : ¬ IsUnit A_sub := by
      intro h_unit
      rw [rank_of_isUnit A_sub h_unit] at h_sub_le
      simp at h_sub_le
    apply (isUnit_iff_isUnit_det A_sub).not.mp at h_sub_degenerate
    apply isUnit_iff_ne_zero.not.mp at h_sub_degenerate
    rw [ne_eq, not_not, det_fin_two] at h_sub_degenerate
    dsimp [A_sub, r, c] at h_sub_degenerate
    rw [← sub_eq_zero, mul_comm (A i' j'), mul_comm (A i' j)]
    exact h_sub_degenerate


lemma at_least_one_side_eigenspace_preserved {T U : Matrix (Fin n) (Fin n) k}
    (h : T * U - U * T = vecMulVec x y) (a : k) :
    ∀ v w : Fin n → k, (T *ᵥ v = a • v) → (w ᵥ* T = a • w) →
    (T *ᵥ (U *ᵥ v) = a • U *ᵥ v ∨ (w ᵥ* U) ᵥ* T = a • (w ᵥ* U)) := by

  intro v w hv hw

  have hvw := h

  apply_fun (fun x ↦ w ᵥ* x) at hvw
  apply_fun (fun x ↦ x ⬝ᵥ v) at hvw

  rw [vecMul_sub, ← vecMul_vecMul, ← vecMul_vecMul] at hvw
  rw [sub_dotProduct, ← dotProduct_mulVec (w ᵥ* U)] at hvw
  rw [hv, hw, smul_vecMul, smul_dotProduct, dotProduct_smul, sub_self] at hvw

  rw [vecMul_vecMulVec, smul_dotProduct] at hvw

  rw [smul_eq_mul] at hvw
  symm at hvw
  rw [mul_eq_zero] at hvw

  cases hvw with
  | inl hw_perp =>
    apply_fun (fun x ↦ w ᵥ* x) at h
    rw [vecMul_sub, ← vecMul_vecMul, ← vecMul_vecMul] at h
    rw [hw, smul_vecMul, vecMul_vecMulVec, hw_perp, zero_smul] at h
    apply eq_of_sub_eq_zero at h
    right
    exact h.symm
  | inr hv_perp =>
    apply_fun (fun x ↦ x *ᵥ v) at h
    rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec] at h
    rw [hv, mulVec_smul, vecMulVec_mulVec, hv_perp, MulOpposite.op_zero, zero_smul] at h
    apply eq_of_sub_eq_zero at h
    left
    exact h




theorem P₆₀₈₉' [IsAlgClosed k] {T U : Matrix (Fin n) (Fin n) k} (h : (T * U - U * T).rank ≤ 1) (hn : n ≠ 0) :
  ∃ β : (Matrix (Fin n) (Fin n) k)ˣ, (β * T * β⁻¹).BlockTriangular id ∧ (β * U * β⁻¹).BlockTriangular id := by

  -- let V := T * U - U * T


  obtain ⟨a, ha⟩ := has_eigenvalue T hn
  obtain ⟨v, hv1, hv2⟩ := has_eigenvector T a ha
  obtain ⟨w, hw1, hw2⟩ := has_vectoreigen T a ha
  obtain ⟨x, y, hxy⟩ := rank_one_as_mul_vec (T * U - U * T) h hn
  -- apply_fun (fun x ↦ x *ᵥ v) at hvw
  -- apply_fun (fun x ↦ w ⬝ᵥ x) at hvw

  -- -- #check toBilin'_apply'

  -- rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec] at hvw
  -- rw [dotProduct_sub, dotProduct_mulVec] at hvw
  -- rw [hv2, hw2, smul_dotProduct, mulVec_smul, dotProduct_smul, sub_self] at hvw

  -- rw [vecMulVec_mulVec] at hvw







  sorry

theorem P₆₀₈₉ [IsAlgClosed k] {T U : Matrix (Fin n) (Fin n) k} (h : (T * U - U * T).rank = 1) :
  ∃ β : (Matrix (Fin n) (Fin n) k)ˣ, (β * T * β⁻¹).BlockTriangular id ∧ (β * U * β⁻¹).BlockTriangular id := by
  apply P₆₀₈₉'
  · exact le_of_eq h
  · exact rank_one_nonempty (T * U - U * T) h
