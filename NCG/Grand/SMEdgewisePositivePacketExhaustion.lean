/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMPositivePacketOrbit
import Mathlib.Analysis.Matrix.Order

/-!
# Edgewise positive-packet exhaustion

This file proves the finite isotypic exhaustion theorem used by
`thm:SM-edgewise-positive-packet-exhaustion`.  On every protected typed/reality
block, the controlled occurrence average is assumed to have the Schur form
`d⁻¹ I ⊗ B`.  Strict positivity of the multiplicity matrix `B` then makes the
whole isotypic average positive definite.  The exact orbit kernel theorem turns
that statement into controlled-span exhaustion.  Blockwise exhaustion is the
orthogonal direct-sum statement, so the selected support is the complete odd
support and its admissible-extra residual is zero.
-/

open Matrix Finset
open scoped ComplexOrder Kronecker MatrixOrder

namespace NCG

set_option maxHeartbeats 800000

/-- The finite controlled occurrence average on one protected isotypic block. -/
noncomputable def occurrenceOrbitAverage {G n : Type*} [Fintype G]
    [Fintype n] [DecidableEq n]
    (ρ : G → Matrix n n ℂ) (J : Matrix n n ℂ) : Matrix n n ℂ :=
  ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, ρ g * J * (ρ g)ᴴ

/-- The selected support of an invertible finite packet.  In the positive
definite branch this is the orthogonal support, namely the identity. -/
noncomputable def selectedPacketSupport {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : Matrix n n ℂ :=
  A * A⁻¹

/-- The admissible odd part missed by the selected occurrence support. -/
noncomputable def admissibleExtraOddResidual {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n ℂ) : Matrix n n ℂ :=
  1 - selectedPacketSupport A

/-- A positive-definite packet has complete selected support and zero residual. -/
theorem selectedPacketSupport_eq_one_of_posDef {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosDef) :
    selectedPacketSupport A = 1 ∧ admissibleExtraOddResidual A = 0 := by
  letI := hA.isUnit.invertible
  have hs : selectedPacketSupport A = 1 := by
    simpa [selectedPacketSupport] using Matrix.mul_inv_of_invertible A
  exact ⟨hs, by simp [admissibleExtraOddResidual, hs]⟩

/-- Strict positivity of the multiplicity partial trace makes the complete
isotypic Schur block `d⁻¹ I ⊗ B` positive definite. -/
theorem occurrence_isotypic_block_posDef
    {V M : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype M] [DecidableEq M]
    (B : Matrix M M ℂ) (hB : B.PosDef) :
    (((Fintype.card V : ℂ))⁻¹ • (1 : Matrix V V ℂ) ⊗ₖ B).PosDef := by
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hscale : (0 : ℂ) < ((Fintype.card V : ℂ))⁻¹ := by
    rw [show (Fintype.card V : ℂ) = ((Fintype.card V : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_inv, Complex.zero_lt_real]
    positivity
  have hI : (((Fintype.card V : ℂ))⁻¹ •
      (1 : Matrix V V ℂ)).PosDef :=
    Matrix.PosDef.smul (Matrix.PosDef.one : (1 : Matrix V V ℂ).PosDef) hscale
  simpa only [Matrix.smul_kronecker] using hI.kronecker hB

/-- Exact single-sector implication: the Schur multiplicity formula and
`B ≻ 0` imply both positivity of the occurrence average and orbit exhaustion. -/
theorem occurrence_isotypic_sector_exhaustion
    {G V M : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype M] [DecidableEq M]
    (ρ : G → Matrix (V × M) (V × M) ℂ)
    (hρmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (J : Matrix (V × M) (V × M) ℂ) (hJ : J.PosSemidef)
    (B : Matrix M M ℂ) (hB : B.PosDef)
    (hSchur : occurrenceOrbitAverage ρ J =
      ((Fintype.card V : ℂ))⁻¹ • (1 : Matrix V V ℂ) ⊗ₖ B) :
    (occurrenceOrbitAverage ρ J).PosDef ∧
      (∀ x : V × M → ℂ, x ≠ 0 →
        ∃ g : G, J *ᵥ ((ρ g)ᴴ *ᵥ x) ≠ 0) := by
  have havg : (occurrenceOrbitAverage ρ J).PosDef := by
    rw [hSchur]
    exact occurrence_isotypic_block_posDef B hB
  refine ⟨havg, ?_⟩
  have horbit := sm_positive_packet_orbit ρ hρmul J hJ
  exact horbit.2.2.2.mpr (by simpa [occurrenceOrbitAverage] using havg)

/-- For a positive occurrence packet, positive trace is exactly nonzero direct
occurrence mass.  Thus a zero-mass packet is an absent direct slot. -/
theorem occurrence_mass_positive_iff {n : Type*} [Fintype n]
    [DecidableEq n] {J : Matrix n n ℂ} (hJ : J.PosSemidef) :
    0 < J.trace ↔ J ≠ 0 := by
  constructor
  · intro hpos hzero
    subst J
    simpa using hpos
  · intro hne
    have htrace : J.trace ≠ 0 := by
      intro hz
      exact hne (hJ.trace_eq_zero_iff.mp hz)
    exact lt_of_le_of_ne hJ.trace_nonneg htrace.symm

/-- `thm:SM-edgewise-positive-packet-exhaustion`.

The index `s` packages the protected pair `(η, λ)`.  The conclusions are:
every isotypic average is positive definite; every nonzero vector is detected
by a controlled occurrence; every selected support is the full admissible odd
support and the extra residual is zero; and nonzero direct occurrence is
equivalent to strictly positive packet mass. -/
theorem sm_edgewise_positive_packet_exhaustion
    {S : Type*} [Fintype S]
    (G V M : S → Type*)
    [∀ s, Group (G s)] [∀ s, Fintype (G s)]
    [∀ s, Fintype (V s)] [∀ s, DecidableEq (V s)] [∀ s, Nonempty (V s)]
    [∀ s, Fintype (M s)] [∀ s, DecidableEq (M s)]
    (ρ : ∀ s, G s → Matrix (V s × M s) (V s × M s) ℂ)
    (hρmul : ∀ s g h, ρ s (g * h) = ρ s g * ρ s h)
    (J : ∀ s, Matrix (V s × M s) (V s × M s) ℂ)
    (hJ : ∀ s, (J s).PosSemidef)
    (B : ∀ s, Matrix (M s) (M s) ℂ)
    (hB : ∀ s, (B s).PosDef)
    (hSchur : ∀ s, occurrenceOrbitAverage (ρ s) (J s) =
      ((Fintype.card (V s) : ℂ))⁻¹ • (1 : Matrix (V s) (V s) ℂ) ⊗ₖ B s) :
    (∀ s, (occurrenceOrbitAverage (ρ s) (J s)).PosDef) ∧
    (∀ s x, x ≠ 0 → ∃ g : G s, J s *ᵥ ((ρ s g)ᴴ *ᵥ x) ≠ 0) ∧
    (∀ s, selectedPacketSupport (occurrenceOrbitAverage (ρ s) (J s)) = 1 ∧
      admissibleExtraOddResidual (occurrenceOrbitAverage (ρ s) (J s)) = 0) ∧
    (∀ s, 0 < (J s).trace ↔ J s ≠ 0) := by
  have hsector : ∀ s,
      (occurrenceOrbitAverage (ρ s) (J s)).PosDef ∧
      (∀ x : V s × M s → ℂ, x ≠ 0 →
        ∃ g : G s, J s *ᵥ ((ρ s g)ᴴ *ᵥ x) ≠ 0) := fun s =>
    occurrence_isotypic_sector_exhaustion (ρ s) (hρmul s)
      (J s) (hJ s) (B s) (hB s) (hSchur s)
  refine ⟨fun s => (hsector s).1, fun s => (hsector s).2, ?_, ?_⟩
  · intro s
    exact selectedPacketSupport_eq_one_of_posDef (hsector s).1
  · intro s
    exact occurrence_mass_positive_iff (hJ s)

end NCG
