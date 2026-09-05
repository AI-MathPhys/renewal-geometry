/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.IsotypicPartialTraceFormula
import NCG.Upstream.PrimitiveWeight

/-!
# Exact least-eigenvalue frame floor for an isotypic packet

For a positive-definite multiplicity packet `B`, this file selects its actual
least eigenvalue and proves the sharp normalized Loewner floor
`(lambda_min / dim V) I` for `dim(V)⁻¹ I ⊗ B`.
-/

open Matrix
open NCG.Upstream.PrimitiveWeight
open scoped ComplexOrder Kronecker

namespace NCG
namespace IsotypicLeastEigenvalueFrameFloor

variable {I : Type} {n : ℕ}
variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- A positive-definite finite Hermitian matrix has an actual positive least
eigenvalue, and subtracting that eigenvalue leaves a PSD matrix. -/
theorem posDef_leastEigenvalue_shift
    (hn : 0 < n) (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosDef) :
    ∃ lam : ℝ, 0 < lam
      ∧ (∃ i : Fin n, lam = hB.1.eigenvalues i)
      ∧ (∀ i : Fin n, lam ≤ hB.1.eigenvalues i)
      ∧ (B - (lam : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i0, _, hi0⟩ :=
    Finset.exists_min_image Finset.univ hB.1.eigenvalues hne
  let lam : ℝ := hB.1.eigenvalues i0
  have hlam : 0 < lam := hB.eigenvalues_pos i0
  have heig : ∃ i : Fin n, lam = hB.1.eigenvalues i := ⟨i0, rfl⟩
  have hleast : ∀ i : Fin n, lam ≤ hB.1.eigenvalues i := by
    intro i
    exact hi0 i (Finset.mem_univ i)
  have hshift : (B - (lam : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    have heq : B - (lam : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
        hB.1.cfc fun x => x - lam := by
      have hsub := Upstream.PrimitiveWeight.cfc_sub hB.1 id (fun _ => lam)
      rw [Upstream.PrimitiveWeight.cfc_id',
        Upstream.PrimitiveWeight.cfc_const] at hsub
      exact hsub
    rw [heq]
    exact cfc_posSemidef hB.1 (fun i => sub_nonneg.mpr (hleast i))
  exact ⟨lam, hlam, heig, hleast, hshift⟩

/-- The actual least multiplicity eigenvalue gives the exact normalized
isotypic frame floor `lambda_min / dim(V)`. -/
theorem exact_isotypic_frame_floor
    (hn : 0 < n) (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosDef) :
    ∃ lam : ℝ, 0 < lam
      ∧ (∃ i : Fin n, lam = hB.1.eigenvalues i)
      ∧ (∀ i : Fin n, lam ≤ hB.1.eigenvalues i)
      ∧ (((((Fintype.card I : ℂ)⁻¹) • (1 : Matrix I I ℂ)) ⊗ₖ B) -
          ((lam / Fintype.card I : ℝ) : ℂ) •
            (1 : Matrix (I × Fin n) (I × Fin n) ℂ)).PosSemidef := by
  obtain ⟨lam, hlam, heig, hleast, hshift⟩ :=
    posDef_leastEigenvalue_shift hn B hB
  exact ⟨lam, hlam, heig, hleast,
    NCG.IsotypicPartialTrace.multiplicity_floor_transfers_to_isotypic
      B lam hlam.le hshift⟩

/-- Frame-floor form for an operator already identified with its exact Schur
partial-trace block. -/
theorem exact_frame_floor_of_partialTrace_formula
    (hn : 0 < n) (F : Matrix (I × Fin n) (I × Fin n) ℂ)
    (hformula :
      F = ((Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) ⊗ₖ
        NCG.IsotypicPartialTrace.multiplicityPartialTrace F)
    (hB : (NCG.IsotypicPartialTrace.multiplicityPartialTrace F).PosDef) :
    ∃ lam : ℝ, 0 < lam
      ∧ (∃ i : Fin n,
          lam = hB.1.eigenvalues i)
      ∧ (∀ i : Fin n, lam ≤ hB.1.eigenvalues i)
      ∧ (F - ((lam / Fintype.card I : ℝ) : ℂ) •
          (1 : Matrix (I × Fin n) (I × Fin n) ℂ)).PosSemidef := by
  obtain ⟨lam, hlam, heig, hleast, hfloor⟩ :=
    exact_isotypic_frame_floor
      (I := I) hn (NCG.IsotypicPartialTrace.multiplicityPartialTrace F) hB
  refine ⟨lam, hlam, heig, hleast, ?_⟩
  rw [hformula]
  exact hfloor

end IsotypicLeastEigenvalueFrameFloor
end NCG
