/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.StandardModel.CliffordTwirlMatterAudit
import RenewalGeometry.StandardModel.OneDoubletOddTangentClassification

open NCG
/-!
# Clifford occurrence test and odd provenance completeness

Covers `def:clifford-matter`, `prop:clifford-occurrence` and the unlabelled
definition "Odd provenance completeness" (ledger key
`definition:odd-provenance-completeness`) of the spacetime/gauge duality
manuscript.

* `cliffordProbability_eq_paper`: the Clifford matter margin in the
  manuscript's normalisation
  `p_Cl = (2 dim H)⁻¹ ∑_{μ=0}^{3} ‖P₋ σ_μ P₊‖²_HS`
  (`eq:clifford-matter`), unfolding
  `CliffordTwirlMatterAudit.cliffordProbability`.
* `cliffordProbability_nonneg`: `p_Cl ≥ 0` for any grading and axes.
* `clifford_occurrence_test`: on the represented carrier `ℂ⁴ ⊗ M` with the
  faithful Clifford axes `γ_μ ⊗ 1`, `p_Cl > 0` exactly when some axis changes
  the protected grading `J`, and on the branch `p_Cl = 0` the grading commutes
  with every axis (reduces the external Clifford action), `J = 1 ⊗ B` with
  `B` a Hermitian involution of the multiplicity factor, and the Clifford
  commutant is exactly the normal multiplicity commutant `1 ⊗ M_m(ℂ)`.
* `OddProvenanceComplete`: the odd provenance completeness predicate
  (vanishing odd provenance defect), with
  `oddProvenanceComplete_iff_rangeIncluded` recording the manuscript's
  "equivalently" clause.
-/

open Matrix Kronecker
open scoped ComplexOrder

namespace RenewalGeometry

namespace CliffordTwirlMatterAudit

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- **`def:clifford-matter`** in the manuscript's normalisation:
`p_Cl = (2 dim H)⁻¹ ∑_μ ‖P₋ σ_μ P₊‖²_HS`. -/
theorem cliffordProbability_eq_paper (J : Block n) (σ : Fin 4 → Block n) :
    cliffordProbability J σ =
      (2 * (Fintype.card n : ℂ))⁻¹ * ∑ μ, axisOccurrence J (σ μ) := by
  unfold cliffordProbability axisProbability
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [mul_inv]
  ring

/-- The Clifford matter margin is nonnegative. -/
theorem cliffordProbability_nonneg (J : Block n) (σ : Fin 4 → Block n) :
    (0 : ℂ) ≤ cliffordProbability J σ := by
  rw [cliffordProbability_eq_paper]
  refine mul_nonneg ?_ (Finset.sum_nonneg fun μ _ => axisOccurrence_nonnegative J (σ μ))
  have h : (2 * (Fintype.card n : ℂ))⁻¹ = (((2 * (Fintype.card n : ℝ))⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h]
  exact Complex.zero_le_real.mpr (by positivity)

section ConcreteCarrier

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- **`prop:clifford-occurrence`** (Clifford occurrence test) on the
represented carrier `ℂ⁴ ⊗ M` with the faithful axes `γ_μ ⊗ 1`.  For a
Hermitian involutive grading `J`: `p_Cl > 0` exactly when at least one
represented Clifford axis changes the grading; and if `p_Cl = 0` the grading
commutes with every axis, is carried by the multiplicity factor
(`J = 1 ⊗ B` with `B` a Hermitian involution), and the residual (commutant)
of the Clifford action is exactly the normal multiplicity commutant
`1 ⊗ M_m(ℂ)`. -/
theorem clifford_occurrence_test (J : Block (CliffordCarrier m))
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    (0 < cliffordProbability J representedAxis ↔
      ∃ μ, J * representedAxis μ ≠ representedAxis μ * J) ∧
    (cliffordProbability J representedAxis = 0 →
      (∀ μ, J * representedAxis μ = representedAxis μ * J) ∧
      (∃ B : Block m, J = (1 : Block SMST4) ⊗ₖ B ∧ Bᴴ = B ∧ B * B = 1) ∧
      (∀ X : Block (CliffordCarrier m),
        (∀ μ, X * representedAxis μ = representedAxis μ * X) ↔
          ∃ B : Block m, X = (1 : Block SMST4) ⊗ₖ B)) := by
  have hzero := cliffordProbability_eq_zero_iff_commutes J hJH hJ2
  refine ⟨?_, fun hp => ⟨hzero.mp hp, (noMatter_branch J hJH hJ2).mp hp,
    fun X => representedAxis_commutant_iff X⟩⟩
  have hnonneg := cliffordProbability_nonneg J (representedAxis (m := m))
  constructor
  · intro hpos
    by_contra μall
    have hall : ∀ μ, J * representedAxis μ = representedAxis μ * J := by
      intro μ
      by_contra hμ
      exact μall ⟨μ, hμ⟩
    exact (ne_of_gt hpos) (hzero.mpr hall)
  · intro hex
    refine lt_of_le_of_ne hnonneg fun h0 => ?_
    obtain ⟨μ, hμ⟩ := hex
    exact hμ (hzero.mp h0.symm μ)

end ConcreteCarrier

end

end CliffordTwirlMatterAudit

/-- **Odd provenance completeness** (unlabelled definition following
`eq:finite-dirac`): the branch is odd-provenance complete when the odd
provenance defect — the trace of the source Schur residual of the complete
grading-odd coefficient block against the selected finite-Dirac block —
vanishes, i.e. the orthogonal odd innovation Gram is zero. -/
def OddProvenanceComplete {h e k : ℕ}
    (selected : Matrix (Fin h) (Fin e) ℂ)
    (complete : Matrix (Fin h) (Fin k) ℂ) : Prop :=
  oddProvenanceDefect selected complete = 0

/-- The manuscript's "equivalently" clause: odd provenance completeness holds
exactly when every future-visible grading-odd action (complete coefficient)
lies in the represented range of the finite Dirac block (selected). -/
theorem oddProvenanceComplete_iff_rangeIncluded {h e k : ℕ}
    (selected : Matrix (Fin h) (Fin e) ℂ)
    (complete : Matrix (Fin h) (Fin k) ℂ) :
    OddProvenanceComplete selected complete ↔ SourceRangeIncluded complete selected :=
  oddProvenanceDefect_eq_zero_iff_rangeIncluded selected complete

end RenewalGeometry
