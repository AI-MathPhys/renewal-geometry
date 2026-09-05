/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteBlockDiagonalPositivity
import NCG.Grand.FiniteIsotypicPacketDecomposition
import NCG.Grand.IsotypicLeastEigenvalueFrameFloor

/-!
# Geometry of a finite isotypic positive packet

This file assembles the blockwise Schur formula with exact direct-sum range
and positive-definiteness criteria.
-/

open Matrix
open scoped ComplexOrder Kronecker

namespace NCG
namespace FiniteIsotypicPacketGeometry

variable {L : Type} [Fintype L] [DecidableEq L]
variable (I M : L → Type)
variable [∀ l, Fintype (I l)] [∀ l, DecidableEq (I l)]
variable [∀ l, Nonempty (I l)]
variable [∀ l, Fintype (M l)] [∀ l, DecidableEq (M l)]

/-- The normalized Schur block attached to one irreducible label. -/
noncomputable def normalizedIsotypicBlock
    (B : ∀ l, Matrix (M l) (M l) ℂ) (l : L) :
    Matrix (I l × M l) (I l × M l) ℂ :=
  ((Fintype.card (I l) : ℂ)⁻¹ • (1 : Matrix (I l) (I l) ℂ)) ⊗ₖ B l

/-- The full normalized isotypic packet is positive definite exactly when
every multiplicity packet is positive definite. -/
theorem normalized_isotypic_packet_posDef_iff
    (B : ∀ l, Matrix (M l) (M l) ℂ) :
    (Matrix.blockDiagonal' (normalizedIsotypicBlock I M B)).PosDef ↔
      ∀ l, (B l).PosDef := by
  rw [NCG.FiniteBlockDiagonal.posDef_blockDiagonal'_iff]
  exact forall_congr' fun l =>
    NCG.IsotypicPartialTrace.invDimension_one_kronecker_posDef_iff (B l)

/-- Exact direct-sum range formula.  On each irreducible coordinate, the
multiplicity slice lies in the range of the corresponding packet `B l`. -/
theorem range_normalized_isotypic_packet
    (B : ∀ l, Matrix (M l) (M l) ℂ) :
    Set.range (fun x : (Σ l, I l × M l) → ℂ =>
      Matrix.blockDiagonal' (normalizedIsotypicBlock I M B) *ᵥ x) =
      {x | ∀ l i,
        NCG.IsotypicPartialTrace.multiplicitySlice
          (NCG.FiniteBlockDiagonal.slice (fun l => I l × M l) x l) i ∈
            LinearMap.range (B l).mulVecLin} := by
  rw [NCG.FiniteBlockDiagonal.range_blockDiagonal'_mulVec]
  ext x
  constructor
  · intro hx l
    rcases hx l with ⟨z, hz⟩
    have hlocal :
        NCG.FiniteBlockDiagonal.slice (fun l => I l × M l) x l ∈
          Set.range (fun y : I l × M l → ℂ =>
            normalizedIsotypicBlock I M B l *ᵥ y) := by
      refine ⟨z, ?_⟩
      exact hz
    change NCG.FiniteBlockDiagonal.slice (fun l => I l × M l) x l ∈
      Set.range (fun y : I l × M l → ℂ =>
        (((Fintype.card (I l) : ℂ)⁻¹ • (1 : Matrix (I l) (I l) ℂ)) ⊗ₖ
          B l) *ᵥ y) at hlocal
    rw [NCG.IsotypicPartialTrace.range_invDimension_one_kronecker_mulVec]
      at hlocal
    exact hlocal
  · intro hx l
    have hlocal :
        NCG.FiniteBlockDiagonal.slice (fun l => I l × M l) x l ∈
          {y | ∀ i,
            NCG.IsotypicPartialTrace.multiplicitySlice y i ∈
              LinearMap.range (B l).mulVecLin} := hx l
    change NCG.FiniteBlockDiagonal.slice (fun l => I l × M l) x l ∈
      {y | ∀ i, NCG.IsotypicPartialTrace.multiplicitySlice y i ∈
        LinearMap.range (B l).mulVecLin} at hlocal
    rw [← NCG.IsotypicPartialTrace.range_invDimension_one_kronecker_mulVec]
      at hlocal
    rcases hlocal with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    exact hz

/-- A covariant operator with pairwise inequivalent irreducible blocks is
positive definite exactly when all of its multiplicity partial traces are. -/
theorem covariant_packet_posDef_iff_partialTraces
    {G : Type} [Group G]
    (ρ : ∀ l, G →* Matrix (I l) (I l) ℂ)
    [∀ l, CategoryTheory.Simple
      (FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation (ρ l)))]
    (hpair : ∀ {l k : L}, l ≠ k → IsEmpty
      (FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation (ρ k)) ≅
        FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation (ρ l))))
    (F : Matrix (Σ l, I l × M l) (Σ l, I l × M l) ℂ)
    (hglobal : ∀ g,
      F * Matrix.blockDiagonal' (fun l =>
        ρ l g ⊗ₖ (1 : Matrix (M l) (M l) ℂ)) =
      Matrix.blockDiagonal' (fun l =>
        ρ l g ⊗ₖ (1 : Matrix (M l) (M l) ℂ)) * F) :
    F.PosDef ↔ ∀ l,
      (NCG.FiniteIsotypicPacketDecomposition.familyMultiplicityPartialTrace
        I M F l).PosDef := by
  let B := fun l =>
    NCG.FiniteIsotypicPacketDecomposition.familyMultiplicityPartialTrace I M F l
  have hformula : F = Matrix.blockDiagonal' (normalizedIsotypicBlock I M B) :=
    NCG.FiniteIsotypicPacketDecomposition.finite_isotypic_decomposition_of_global_covariance
      I M ρ hpair F hglobal
  constructor
  · intro hF
    apply (normalized_isotypic_packet_posDef_iff I M B).mp
    rwa [← hformula]
  · intro hB
    rw [hformula]
    exact (normalized_isotypic_packet_posDef_iff I M B).mpr hB

section ExactFiniteFloor

variable [Nonempty L]

/-- The minimum of a real-valued family over a nonempty finite type. -/
noncomputable def finiteMinimum (c : L → ℝ) : ℝ :=
  (Finset.univ.image c).min' (Finset.univ_nonempty.image c)

theorem finiteMinimum_mem (c : L → ℝ) :
    ∃ l, finiteMinimum c = c l := by
  have hmem := Finset.min'_mem (Finset.univ.image c)
    (Finset.univ_nonempty.image c)
  rcases Finset.mem_image.mp hmem with ⟨l, _, hl⟩
  exact ⟨l, hl.symm⟩

theorem finiteMinimum_le (c : L → ℝ) (l : L) : finiteMinimum c ≤ c l := by
  exact Finset.min'_le (Finset.univ.image c) (c l)
    (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩)

theorem finiteMinimum_pos {c : L → ℝ} (hc : ∀ l, 0 < c l) :
    0 < finiteMinimum c := by
  obtain ⟨l, hl⟩ := finiteMinimum_mem c
  rw [hl]
  exact hc l

/-- Exact finite direct-sum frame floor.  Each `lam l` is the actual least
eigenvalue of `B l`, and the global constant is precisely the finite minimum
of `lam l / dim(I l)`. -/
theorem exact_finite_isotypic_frame_floor
    (n : L → ℕ) (hn : ∀ l, 0 < n l)
    (B : ∀ l, Matrix (Fin (n l)) (Fin (n l)) ℂ)
    (hB : ∀ l, (B l).PosDef) :
    ∃ lam : L → ℝ,
      (∀ l, 0 < lam l
        ∧ (∃ i : Fin (n l), lam l = (hB l).1.eigenvalues i)
        ∧ (∀ i : Fin (n l), lam l ≤ (hB l).1.eigenvalues i))
      ∧ 0 < finiteMinimum (fun l => lam l / Fintype.card (I l))
      ∧ (Matrix.blockDiagonal'
          (normalizedIsotypicBlock I (fun l => Fin (n l)) B) -
        ((finiteMinimum (fun l => lam l / Fintype.card (I l)) : ℝ) : ℂ) •
          (1 : Matrix (Σ l, I l × Fin (n l))
            (Σ l, I l × Fin (n l)) ℂ)).PosSemidef := by
  classical
  have hlocal : ∀ l, ∃ a : ℝ, 0 < a
      ∧ (∃ i : Fin (n l), a = (hB l).1.eigenvalues i)
      ∧ (∀ i : Fin (n l), a ≤ (hB l).1.eigenvalues i)
      ∧ (normalizedIsotypicBlock I (fun l => Fin (n l)) B l -
        ((a / Fintype.card (I l) : ℝ) : ℂ) •
          (1 : Matrix (I l × Fin (n l)) (I l × Fin (n l)) ℂ)).PosSemidef := by
    intro l
    simpa [normalizedIsotypicBlock] using
      (NCG.IsotypicLeastEigenvalueFrameFloor.exact_isotypic_frame_floor
        (I := I l) (hn l) (B l) (hB l))
  choose lam hlam hactual hleast hfloor using hlocal
  refine ⟨lam, fun l => ⟨hlam l, hactual l, hleast l⟩, ?_, ?_⟩
  · apply finiteMinimum_pos
    intro l
    exact div_pos (hlam l) (by exact_mod_cast Fintype.card_pos)
  · let c : ℝ := finiteMinimum (fun l => lam l / Fintype.card (I l))
    have hc_le : ∀ l, c ≤ lam l / Fintype.card (I l) :=
      fun l => finiteMinimum_le _ l
    have hblocks : ∀ l,
        (normalizedIsotypicBlock I (fun l => Fin (n l)) B l -
          (c : ℂ) • (1 : Matrix (I l × Fin (n l))
            (I l × Fin (n l)) ℂ)).PosSemidef := by
      intro l
      let cl : ℝ := lam l / Fintype.card (I l)
      have hcoeffR : 0 ≤ cl - c := sub_nonneg.mpr (hc_le l)
      have hcoeffC : (0 : ℂ) ≤ ((cl - c : ℝ) : ℂ) := by
        rw [Complex.zero_le_real]
        exact hcoeffR
      have hadd := (hfloor l).add
        ((Matrix.PosSemidef.one :
          (1 : Matrix (I l × Fin (n l)) (I l × Fin (n l)) ℂ).PosSemidef).smul
            hcoeffC)
      have heq :
          normalizedIsotypicBlock I (fun l => Fin (n l)) B l -
              (c : ℂ) • (1 : Matrix (I l × Fin (n l))
                (I l × Fin (n l)) ℂ) =
            (normalizedIsotypicBlock I (fun l => Fin (n l)) B l -
              (cl : ℂ) • (1 : Matrix (I l × Fin (n l))
                (I l × Fin (n l)) ℂ)) +
              ((cl - c : ℝ) : ℂ) •
                (1 : Matrix (I l × Fin (n l))
                  (I l × Fin (n l)) ℂ) := by
        ext p q
        by_cases hpq : p = q
        · subst q
          simp [cl]
        · simp [Matrix.one_apply, hpq]
      rw [heq]
      exact hadd
    have hdiag : (Matrix.blockDiagonal' (fun l =>
        normalizedIsotypicBlock I (fun l => Fin (n l)) B l -
          (c : ℂ) • (1 : Matrix (I l × Fin (n l))
            (I l × Fin (n l)) ℂ))).PosSemidef :=
      (NCG.FiniteBlockDiagonal.posSemidef_blockDiagonal'_iff
        (fun l => I l × Fin (n l)) _).mpr hblocks
    have heq :
        Matrix.blockDiagonal'
            (normalizedIsotypicBlock I (fun l => Fin (n l)) B) -
          (c : ℂ) • (1 : Matrix (Σ l, I l × Fin (n l))
            (Σ l, I l × Fin (n l)) ℂ) =
        Matrix.blockDiagonal' (fun l =>
          normalizedIsotypicBlock I (fun l => Fin (n l)) B l -
            (c : ℂ) • (1 : Matrix (I l × Fin (n l))
              (I l × Fin (n l)) ℂ)) := by
      have hscalar :
          Matrix.blockDiagonal'
              ((c : ℂ) • (1 : ∀ l,
                Matrix (I l × Fin (n l)) (I l × Fin (n l)) ℂ)) =
            (c : ℂ) • (1 : Matrix (Σ l, I l × Fin (n l))
              (Σ l, I l × Fin (n l)) ℂ) := by
        rw [Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_one]
      calc
        _ = Matrix.blockDiagonal'
              (normalizedIsotypicBlock I (fun l => Fin (n l)) B) -
            Matrix.blockDiagonal'
              ((c : ℂ) • (1 : ∀ l,
                Matrix (I l × Fin (n l)) (I l × Fin (n l)) ℂ)) := by
              rw [hscalar]
        _ = Matrix.blockDiagonal'
              (normalizedIsotypicBlock I (fun l => Fin (n l)) B -
                (c : ℂ) • (1 : ∀ l,
                  Matrix (I l × Fin (n l)) (I l × Fin (n l)) ℂ)) :=
              (Matrix.blockDiagonal'_sub _ _).symm
        _ = _ := rfl
    change (Matrix.blockDiagonal'
          (normalizedIsotypicBlock I (fun l => Fin (n l)) B) -
        (c : ℂ) • (1 : Matrix (Σ l, I l × Fin (n l))
          (Σ l, I l × Fin (n l)) ℂ)).PosSemidef
    rw [heq]
    exact hdiag

end ExactFiniteFloor

end FiniteIsotypicPacketGeometry
end NCG
