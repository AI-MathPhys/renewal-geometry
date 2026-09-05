/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual

/-!
# Exact upstream germ packet and rerun rule

Finite encoding of the five rows (G1)--(G5) in
`cor:GT-NCG-germ-handoff`.  The appended source synthesis is required to
contain both the old bank and the complete mixed germ panel.  The terminal
prefix short is then the genuine Moore--Penrose orthogonal residual, positive
semidefinite, and vanishes exactly when every target row factors through the
augmented source range.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace ExactUpstreamGermPacketHandoff

/-- The finite data rows demanded by (G1)--(G5).  The matrices use one common
active carrier and source gauge. -/
structure GermPanel (h q : ℕ) where
  identityRow : Matrix (Fin h) (Fin q) ℂ
  forwardRow : Fin 2 → Matrix (Fin h) (Fin q) ℂ
  reverseRow : Fin 2 → Matrix (Fin h) (Fin q) ℂ
  duration : Fin 2 → ℝ
  adjacentDuration : Fin 2 → ℝ
  mixedSourceBank : Matrix (Fin h) (Fin q) ℂ
  hamiltonianResidual : Matrix (Fin q) (Fin q) ℂ
  reversalResidual : Matrix (Fin q) (Fin q) ℂ
  sourceCoreResidual : Matrix (Fin q) (Fin q) ℂ
  heldOutResidual : Matrix (Fin q) (Fin q) ℂ
  germCoefficient : Matrix (Fin h) (Fin h) ℂ
  deterministicCoefficient : Matrix (Fin h) (Fin h) ℂ
  commutantAnchor : Matrix (Fin h) (Fin h) ℂ

/-- Exact population conditions for the five germ rows: two nested positive
times with transported calibration, all structural residuals zero, and the
coefficient incidence modulo the declared commutant anchor. -/
def GermPanel.Populated {h q : ℕ} (P : GermPanel h q) : Prop :=
  0 < P.duration 0 ∧ P.duration 0 < P.duration 1 ∧
  (∀ i, P.adjacentDuration i = P.duration i) ∧
  P.hamiltonianResidual = 0 ∧ P.reversalResidual = 0 ∧
  P.sourceCoreResidual = 0 ∧ P.heldOutResidual = 0 ∧
  P.germCoefficient = P.deterministicCoefficient + P.commutantAnchor

/-- An augmented synthesis obtained after adjoining the polar innovations of
the panel.  The factorization fields say exactly that the old and new panel
rows lie in its source range. -/
structure AugmentedSource (h e q ep : ℕ) where
  oldSource : Matrix (Fin h) (Fin e) ℂ
  panelSource : Matrix (Fin h) (Fin q) ℂ
  synthesis : Matrix (Fin h) (Fin ep) ℂ
  oldFactor : Matrix (Fin ep) (Fin e) ℂ
  panelFactor : Matrix (Fin ep) (Fin q) ℂ
  old_eq : oldSource = synthesis * oldFactor
  panel_eq : panelSource = synthesis * panelFactor

/-- Orthogonal innovation of the terminal target against the augmented
source range. -/
noncomputable def germInnovation {h ep b : ℕ}
    (Splus : Matrix (Fin h) (Fin ep) ℂ)
    (B : Matrix (Fin h) (Fin b) ℂ) : Matrix (Fin h) (Fin b) ℂ :=
  (1 - sourceRangeProjection Splus) * B

/-- The displayed prefix short is exactly the manuscript expression
`B*(I-P_S)B`, in source-Gram orientation. -/
theorem terminalShort_eq_display {h ep b : ℕ}
    (Splus : Matrix (Fin h) (Fin ep) ℂ)
    (B : Matrix (Fin h) (Fin b) ℂ) :
    sourceSchurResidual Splus B =
      Bᴴ * (1 - sourceRangeProjection Splus) * B :=
  sourceSchurResidual_eq_orthogonalResidual Splus B

/-- The terminal prefix short is positive semidefinite. -/
theorem terminalShort_posSemidef {h ep b : ℕ}
    (Splus : Matrix (Fin h) (Fin ep) ℂ)
    (B : Matrix (Fin h) (Fin b) ℂ) :
    (sourceSchurResidual Splus B).PosSemidef :=
  sourceSchurResidual_posSemidef Splus B

/-- Exact rerun rule: closure of the prefix is equivalent to factorization of
the complete target bank through the augmented source synthesis. -/
theorem terminalShort_eq_zero_iff_target_factors {h ep b : ℕ}
    (Splus : Matrix (Fin h) (Fin ep) ℂ)
    (B : Matrix (Fin h) (Fin b) ℂ) :
    sourceSchurResidual Splus B = 0 ↔
      ∃ T : Matrix (Fin ep) (Fin b) ℂ, B = Splus * T :=
  sourceSchurResidual_eq_zero_iff_rangeIncluded Splus B

/-- Complete finite handoff theorem.  Once (G1)--(G5) are populated on one
carrier and the polar-augmented synthesis contains the old and panel rows,
the audit may pass the terminal prefix exactly on the zero-short branch; this
is equivalently the source-range closure of the complete target bank. -/
theorem exact_upstream_germ_packet_and_rerun_rule
    {h e q ep b : ℕ}
    (P : GermPanel h q) (A : AugmentedSource h e q ep)
    (B1 : Matrix (Fin h) (Fin b) ℂ)
    (hpop : P.Populated)
    (hpanel : P.mixedSourceBank = A.panelSource) :
    P.Populated ∧ P.mixedSourceBank = A.panelSource ∧
    SourceRangeIncluded A.oldSource A.synthesis ∧
    SourceRangeIncluded P.mixedSourceBank A.synthesis ∧
    (sourceSchurResidual A.synthesis B1).PosSemidef ∧
    (sourceSchurResidual A.synthesis B1 = 0 ↔
      ∃ T : Matrix (Fin ep) (Fin b) ℂ, B1 = A.synthesis * T) := by
  refine ⟨hpop, hpanel, ⟨A.oldFactor, A.old_eq⟩, ?_,
    terminalShort_posSemidef A.synthesis B1,
    terminalShort_eq_zero_iff_target_factors A.synthesis B1⟩
  exact ⟨A.panelFactor, hpanel.trans A.panel_eq⟩

end ExactUpstreamGermPacketHandoff
end NCG
