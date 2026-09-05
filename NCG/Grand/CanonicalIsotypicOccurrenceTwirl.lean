/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMEdgewisePositivePacketExhaustion
import NCG.Grand.FiniteSchurOrthogonality

/-!
# Canonical isotypic occurrence twirl

Same-block Schur orthogonality for the finite Peter--Weyl blocks derives the
isotypic occurrence formula `d⁻¹ I ⊗ Tr_V(J)`.  This removes the Schur formula
as an assumption in the canonical protected-block realization and feeds its
positive multiplicity matrix directly into packet exhaustion.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder Kronecker MatrixOrder

namespace NCG
namespace CanonicalIsotypicOccurrenceTwirl

open FinitePeterWeyl

variable {G : Type*} [Group G] [Fintype G]

/-- Protected irreducible block acting trivially on its multiplicity space. -/
def isotypicBlockRep (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (M : Type*) [Fintype M] [DecidableEq M] (g : G) :
    Matrix (Fin (D.dimension i) × M) (Fin (D.dimension i) × M) ℂ :=
  normalizedBlockMatrix D i g ⊗ₖ (1 : Matrix M M ℂ)

theorem isotypicBlockRep_mul (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (M : Type*) [Fintype M] [DecidableEq M]
    (g h : G) :
    isotypicBlockRep D i M (g * h) =
      isotypicBlockRep D i M g * isotypicBlockRep D i M h := by
  rw [isotypicBlockRep, isotypicBlockRep, isotypicBlockRep,
    normalizedBlockMatrix_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Partial trace over the protected irreducible carrier. -/
def multiplicityTrace (D : MatrixBlockDecomposition G) (i : Fin D.count)
    {M : Type*} [Fintype M]
    (J : Matrix (Fin (D.dimension i) × M)
      (Fin (D.dimension i) × M) ℂ) : Matrix M M ℂ :=
  fun m n => ∑ a : Fin (D.dimension i), J (a, m) (a, n)

private theorem isotypicBlockRep_mul_entry
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    {M : Type*} [Fintype M] [DecidableEq M]
    (J : Matrix (Fin (D.dimension i) × M)
      (Fin (D.dimension i) × M) ℂ)
    (g : G) (a d : Fin (D.dimension i)) (m n : M) :
    (isotypicBlockRep D i M g * J) (a, m) (d, n) =
      ∑ b : Fin (D.dimension i),
        normalizedBlockMatrix D i g a b * J (b, m) (d, n) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single m]
  · change normalizedBlockMatrix D i g a b * (1 : Matrix M M ℂ) m m *
        J (b, m) (d, n) = _
    simp
  · intro k _ hkm
    change normalizedBlockMatrix D i g a b * (1 : Matrix M M ℂ) m k *
        J (b, k) (d, n) = 0
    simp [hkm.symm]
  · intro habs
    exact absurd (Finset.mem_univ m) habs

private theorem conjugated_entry
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    {M : Type*} [Fintype M] [DecidableEq M]
    (J : Matrix (Fin (D.dimension i) × M)
      (Fin (D.dimension i) × M) ℂ)
    (g : G) (a c : Fin (D.dimension i)) (m n : M) :
    (isotypicBlockRep D i M g * J *
      (isotypicBlockRep D i M g)ᴴ) (a, m) (c, n) =
      ∑ b : Fin (D.dimension i), ∑ d : Fin (D.dimension i),
        normalizedBlockMatrix D i g a b * J (b, m) (d, n) *
          star (normalizedBlockMatrix D i g c d) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  calc
    _ = ∑ d : Fin (D.dimension i),
        (isotypicBlockRep D i M g * J) (a, m) (d, n) *
          star (normalizedBlockMatrix D i g c d) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_eq_single n]
      · change (isotypicBlockRep D i M g * J) (a, m) (d, n) *
            star (normalizedBlockMatrix D i g c d *
              (1 : Matrix M M ℂ) n n) = _
        simp
      · intro k _ hkn
        change (isotypicBlockRep D i M g * J) (a, m) (d, k) *
            star (normalizedBlockMatrix D i g c d *
              (1 : Matrix M M ℂ) n k) = 0
        simp [hkn.symm]
      · intro habs
        exact absurd (Finset.mem_univ n) habs
    _ = _ := by
      simp_rw [isotypicBlockRep_mul_entry D i J, Finset.sum_mul]
      rw [Finset.sum_comm]

/-- The finite Peter--Weyl block twirl is exactly `d⁻¹ I` tensored with the
multiplicity partial trace of the packet. -/
theorem occurrenceOrbitAverage_isotypicBlockRep
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    {M : Type*} [Fintype M] [DecidableEq M]
    (J : Matrix (Fin (D.dimension i) × M)
      (Fin (D.dimension i) × M) ℂ) :
    occurrenceOrbitAverage (isotypicBlockRep D i M) J =
      ((D.dimension i : ℂ))⁻¹ •
        (1 : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ) ⊗ₖ
          multiplicityTrace D i J := by
  have hG : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hd : (D.dimension i : ℂ) ≠ 0 := by
    exact_mod_cast (D.dimension_neZero i).out
  ext ⟨a, m⟩ ⟨c, n⟩
  rw [occurrenceOrbitAverage, Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [conjugated_entry D i J]
  rw [Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [multiplicityTrace]
  have hreorder :
      (∑ g : G, ∑ b : Fin (D.dimension i), ∑ d : Fin (D.dimension i),
        normalizedBlockMatrix D i g a b * J (b, m) (d, n) *
          star (normalizedBlockMatrix D i g c d)) =
      ∑ b : Fin (D.dimension i), ∑ d : Fin (D.dimension i),
        J (b, m) (d, n) *
          (∑ g : G, normalizedBlockMatrix D i g a b *
            star (normalizedBlockMatrix D i g c d)) := by
    calc
      _ = ∑ b : Fin (D.dimension i), ∑ g : G,
          ∑ d : Fin (D.dimension i),
            normalizedBlockMatrix D i g a b * J (b, m) (d, n) *
              star (normalizedBlockMatrix D i g c d) := Finset.sum_comm
      _ = ∑ b : Fin (D.dimension i), ∑ d : Fin (D.dimension i),
          ∑ g : G, normalizedBlockMatrix D i g a b * J (b, m) (d, n) *
            star (normalizedBlockMatrix D i g c d) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro d hdmem
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g hg
          ring
  rw [hreorder]
  have horth : ∀ b d,
      ∑ g : G, normalizedBlockMatrix D i g a b *
          star (normalizedBlockMatrix D i g c d) =
        ((Fintype.card G : ℂ) / D.dimension i) *
          (if a = c ∧ b = d then 1 else 0) := by
    intro b d
    simpa [mul_comm, eq_comm] using
      normalizedBlockMatrix_same_orthogonality D i c d a b
  simp_rw [horth]
  by_cases hac : a = c
  · subst c
    simp only [true_and, if_pos, if_true]
    have hdiag :
        (∑ b : Fin (D.dimension i), ∑ d : Fin (D.dimension i),
          J (b, m) (d, n) *
            (((Fintype.card G : ℂ) / D.dimension i) *
              (if b = d then 1 else 0))) =
          ((Fintype.card G : ℂ) / D.dimension i) *
            ∑ b : Fin (D.dimension i), J (b, m) (b, n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_eq_single b]
      · simp
        ring
      · intro d _ hdb
        simp [hdb, Ne.symm hdb]
      · intro habs
        exact absurd (Finset.mem_univ b) habs
    rw [hdiag]
    simp only [smul_eq_mul]
    field_simp [hG, hd]
  · simp [hac]

/-- Positive multiplicity partial trace now yields exhaustion without any
assumed Schur identity. -/
theorem canonical_isotypic_occurrence_exhaustion
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    {M : Type*} [Fintype M] [DecidableEq M]
    (J : Matrix (Fin (D.dimension i) × M)
      (Fin (D.dimension i) × M) ℂ)
    (hJ : J.PosSemidef) (hB : (multiplicityTrace D i J).PosDef) :
    (occurrenceOrbitAverage (isotypicBlockRep D i M) J).PosDef ∧
      (∀ x : Fin (D.dimension i) × M → ℂ, x ≠ 0 →
        ∃ g : G, J *ᵥ ((isotypicBlockRep D i M g)ᴴ *ᵥ x) ≠ 0) ∧
      selectedPacketSupport
        (occurrenceOrbitAverage (isotypicBlockRep D i M) J) = 1 ∧
      admissibleExtraOddResidual
        (occurrenceOrbitAverage (isotypicBlockRep D i M) J) = 0 := by
  letI : Nonempty (Fin (D.dimension i)) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (D.dimension_neZero i).out)
  have hsector := occurrence_isotypic_sector_exhaustion
    (isotypicBlockRep D i M) (isotypicBlockRep_mul D i M)
    J hJ (multiplicityTrace D i J) hB
    (by simpa using occurrenceOrbitAverage_isotypicBlockRep D i J)
  obtain ⟨hpos, hex⟩ := hsector
  obtain ⟨hsupp, hres⟩ := selectedPacketSupport_eq_one_of_posDef hpos
  exact ⟨hpos, hex, hsupp, hres⟩

end CanonicalIsotypicOccurrenceTwirl
end NCG
