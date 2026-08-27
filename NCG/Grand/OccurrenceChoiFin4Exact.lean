/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OccurrenceChoiSource
import NCG.Grand.SMBridgeAndMarkedDirac
import NCG.Grand.CanonicalPrefixPurificationUniqueness

/-!
# The concrete two-way occurrence Choi source on `M₄(ℂ)`

This instantiates the generic Choi algebra at the manuscript's actual occurrence map
`Φ_occ = Φ_{L←R} + Φ_{R←L}` by combining the two Kraus families into a sum index.
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder

namespace NCG

abbrev OccurrenceIndex (l r : Type*) := Sum l r

def occurrenceKraus {l r : Type*}
    (VLR : l → Matrix (Fin 4) (Fin 4) ℂ)
    (VRL : r → Matrix (Fin 4) (Fin 4) ℂ) :
    OccurrenceIndex l r → Matrix (Fin 4) (Fin 4) ℂ
  | Sum.inl a => VLR a
  | Sum.inr a => VRL a

/-- The concrete completely-positive occurrence map, with both support directions included. -/
noncomputable def occurrenceMap {l r : Type*} [Fintype l] [Fintype r]
    (VLR : l → Matrix (Fin 4) (Fin 4) ℂ)
    (VRL : r → Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun X := ∑ a, occurrenceKraus VLR VRL a * X * (occurrenceKraus VLR VRL a)ᴴ
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- The matrix-unit Choi operator of the concrete two-way occurrence map. -/
noncomputable def occurrenceChoi {l r : Type*} [Fintype l] [Fintype r]
    (VLR : l → Matrix (Fin 4) (Fin 4) ℂ)
    (VRL : r → Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    Matrix.single i j (1 : ℂ) ⊗ₖ occurrenceMap VLR VRL (Matrix.single i j (1 : ℂ))

set_option maxHeartbeats 1000000 in
/-- The concrete `J_occ` is the explicit Kraus-vector Gram and is positive semidefinite. -/
theorem occurrenceChoi_eq_dyadSum_and_posSemidef
    {l r : Type*} [Fintype l] [Fintype r]
    (VLR : l → Matrix (Fin 4) (Fin 4) ℂ)
    (VRL : r → Matrix (Fin 4) (Fin 4) ℂ) :
    occurrenceChoi VLR VRL =
        ∑ a, Matrix.vecMulVec
          (fun p : Fin 4 × Fin 4 ↦ occurrenceKraus VLR VRL a p.2 p.1)
          (star fun p : Fin 4 × Fin 4 ↦ occurrenceKraus VLR VRL a p.2 p.1)
      ∧ (occurrenceChoi VLR VRL).PosSemidef := by
  change
    ((∑ i : Fin 4, ∑ j : Fin 4,
        Matrix.single i j (1 : ℂ) ⊗ₖ
          (∑ a, occurrenceKraus VLR VRL a * Matrix.single i j (1 : ℂ) *
            (occurrenceKraus VLR VRL a)ᴴ)) =
      ∑ a, Matrix.vecMulVec
        (fun p : Fin 4 × Fin 4 => occurrenceKraus VLR VRL a p.2 p.1)
        (star fun p : Fin 4 × Fin 4 => occurrenceKraus VLR VRL a p.2 p.1)) ∧
      (∑ i : Fin 4, ∑ j : Fin 4,
        Matrix.single i j (1 : ℂ) ⊗ₖ
          (∑ a, occurrenceKraus VLR VRL a * Matrix.single i j (1 : ℂ) *
            (occurrenceKraus VLR VRL a)ᴴ)).PosSemidef
  have hentry : ∀ (V : Matrix (Fin 4) (Fin 4) ℂ)
      (p q : Fin 4 × Fin 4),
      ∑ i : Fin 4, ∑ j : Fin 4,
          Matrix.single i j (1 : ℂ) p.1 q.1 *
            (V * Matrix.single i j (1 : ℂ) * Vᴴ) p.2 q.2 =
        V p.2 p.1 * star (V q.2 q.1) := by
    intro V p q
    rw [Finset.sum_eq_single p.1]
    · rw [Finset.sum_eq_single q.1]
      · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, one_mul]
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single q.1]
        · rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single p.1]
          · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
              mul_one, Matrix.conjTranspose_apply]
          · intro a _ ha
            rw [Matrix.single_apply,
              if_neg (fun h => ha h.1.symm), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
        · intro a _ ha
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_zero fun b _ => ?_, zero_mul]
          rw [Matrix.single_apply,
            if_neg (fun h => ha h.2.symm), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro a _ ha
        rw [Matrix.single_apply, if_neg (fun h => ha h.2), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Matrix.single_apply, if_neg (fun h => ha h.1), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have heq :
      (∑ i : Fin 4, ∑ j : Fin 4,
        Matrix.single i j (1 : ℂ) ⊗ₖ
          (∑ a, occurrenceKraus VLR VRL a * Matrix.single i j (1 : ℂ) *
            (occurrenceKraus VLR VRL a)ᴴ)) =
      ∑ a, Matrix.vecMulVec
        (fun p : Fin 4 × Fin 4 => occurrenceKraus VLR VRL a p.2 p.1)
        (star fun p : Fin 4 × Fin 4 => occurrenceKraus VLR VRL a p.2 p.1) := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Finset.mul_sum]
    exact Eq.trans
      (Eq.trans
        (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
        Finset.sum_comm)
      (Finset.sum_congr rfl fun a _ =>
        hentry (occurrenceKraus VLR VRL a) p q)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact Finset.sum_induction _ _
    (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun a _ => Matrix.posSemidef_vecMulVec_self_star _)
/-- `Γ_occ = √J_occ` is the canonical positive square factor. -/
theorem occurrenceChoi_sqrt_canonical
    {l r : Type*} [Fintype l] [Fintype r]
    (VLR : l → Matrix (Fin 4) (Fin 4) ℂ)
    (VRL : r → Matrix (Fin 4) (Fin 4) ℂ) :
    (CFC.sqrt (occurrenceChoi VLR VRL))ᴴ * CFC.sqrt (occurrenceChoi VLR VRL)
        = occurrenceChoi VLR VRL
      ∧ (CFC.sqrt (occurrenceChoi VLR VRL)).PosSemidef
      ∧ ∀ Γ : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ,
          Γ.PosSemidef → Γ * Γ = occurrenceChoi VLR VRL →
          Γ = CFC.sqrt (occurrenceChoi VLR VRL) := by
  exact (occurrence_choi_source (d := Fin 4)).2.1 _
    (occurrenceChoi_eq_dyadSum_and_posSemidef VLR VRL).2

/-- The minimal occurrence carrier is exactly `supp J_occ`, expressed by equality of kernels. -/
theorem occurrenceChoi_sqrt_support
    {l r : Type*} [Fintype l] [Fintype r]
    (VLR : l → Matrix (Fin 4) (Fin 4) ℂ)
    (VRL : r → Matrix (Fin 4) (Fin 4) ℂ) :
    ∀ x : (Fin 4 × Fin 4) → ℂ,
      CFC.sqrt (occurrenceChoi VLR VRL) *ᵥ x = 0 ↔
      occurrenceChoi VLR VRL *ᵥ x = 0 :=
  occurrence_choi_minimal_support _
    (occurrenceChoi_eq_dyadSum_and_posSemidef VLR VRL).2

/-- Every other factor of `J_occ` is related to the square-root memory by the unique
source-fixing inner-product-preserving equivalence. -/
theorem occurrenceChoi_factor_unique_sourceUnitary
    {l r h : Type*} [Fintype l] [Fintype r] [Fintype h]
    (VLR : l → Matrix (Fin 4) (Fin 4) ℂ)
    (VRL : r → Matrix (Fin 4) (Fin 4) ℂ)
    (T : Matrix h (Fin 4 × Fin 4) ℂ)
    (hT : Tᴴ * T = occurrenceChoi VLR VRL) :
    ∃! U : CanonicalPrefixMemory (occurrenceChoi VLR VRL) ≃ₗ[ℂ]
        LinearMap.range T.mulVecLin,
      (∀ u : (Fin 4 × Fin 4) → ℂ,
        U ((canonicalPrefixFactor (occurrenceChoi VLR VRL)).mulVecLin.rangeRestrict u)
          = T.mulVecLin.rangeRestrict u)
      ∧ (∀ x y : CanonicalPrefixMemory (occurrenceChoi VLR VRL),
        star (x : (Fin 4 × Fin 4) → ℂ) ⬝ᵥ (y : (Fin 4 × Fin 4) → ℂ)
          = star (U x : h → ℂ) ⬝ᵥ (U y : h → ℂ)) := by
  exact canonicalPrefixPurification_unique _
    (occurrenceChoi_eq_dyadSum_and_posSemidef VLR VRL).2 T hT

/-- Any sixteen-element Hermitian Hilbert--Schmidt orthonormal basis reconstructs the concrete
two-way occurrence Choi operator. -/
theorem occurrenceChoi_sixteenOutput_reconstruction
    {l r : Type*} [Fintype l] [Fintype r]
    (VLR : l → Matrix (Fin 4) (Fin 4) ℂ)
    (VRL : r → Matrix (Fin 4) (Fin 4) ℂ)
    (F : Fin 16 → Matrix (Fin 4) (Fin 4) ℂ)
    (hcomplete : ∀ i j k q : Fin 4, ∑ a, F a i j * F a k q =
      if i = q ∧ j = k then 1 else 0) :
    ∑ a, (F a)ᵀ ⊗ₖ occurrenceMap VLR VRL (F a) = occurrenceChoi VLR VRL := by
  calc
    ∑ a, (F a)ᵀ ⊗ₖ occurrenceMap VLR VRL (F a) =
        ∑ i : Fin 4, ∑ j : Fin 4,
          (Matrix.single i j (1 : ℂ))ᵀ ⊗ₖ
            occurrenceMap VLR VRL (Matrix.single j i (1 : ℂ)) :=
      (occurrence_choi_source (d := Fin 4)).2.2 F
        (occurrenceMap VLR VRL) hcomplete
    _ = occurrenceChoi VLR VRL := by
      rw [occurrenceChoi]
      simp only [Matrix.transpose_single]
      rw [Finset.sum_comm]

end NCG
