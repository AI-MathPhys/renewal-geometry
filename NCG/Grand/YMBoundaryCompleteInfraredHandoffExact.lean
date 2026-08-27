/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTBoundaryShort
import NCG.Grand.YMNSHodgeShort

/-!
# Boundary-complete Yang--Mills infrared handoff

Assembly of the two-scale Feshbach floor with the exact relaxed boundary
short.  It records directly that a nonnegative boundary relaxation term cannot
consume the infrared/ultraviolet floor.
-/

open Matrix

namespace NCG
namespace YMBoundaryCompleteInfraredHandoffExact

/-- The boundary-complete infrared action. -/
def boundaryCompleteIRAction {b m : Type} [Fintype b] [Fintype m]
    (S : Matrix m m ℂ) (E : Matrix b m ℂ) (W : Matrix b b ℂ) :
    Matrix m m ℂ :=
  S + Eᴴ * W * E

/-- Exact boundary-complete handoff: the Woodbury inverse gives the advertised
action, the naive discrepancy is the positive-dispersion term, and the
two-scale floor survives addition of every nonnegative boundary relaxation
cost. -/
theorem ym_boundary_complete_infrared_handoff
    {T b m : Type} [Fintype T] [Fintype b] [Fintype m]
    [DecidableEq T] [DecidableEq b]
    (C : Matrix T T ℂ) (DT : Matrix b T ℂ)
    [Invertible C] [Invertible (C + DTᴴ * DT)]
    (S : Matrix m m ℂ) (E : Matrix b m ℂ)
    (K W : Matrix b b ℂ)
    (hK : K = DT * C⁻¹ * DTᴴ)
    (hW : W = 1 - DT * ((C + DTᴴ * DT)⁻¹ * DTᴴ)) :
    (((1 : Matrix b b ℂ) + K) * W = 1 ∧
      W * ((1 : Matrix b b ℂ) + K) = 1) ∧
    (boundaryCompleteIRAction S E W = S + Eᴴ * W * E) ∧
    (Eᴴ * E - Eᴴ * (W * E) = Eᴴ * (K * (W * E))) ∧
    (∀ full s c nx nz ntot δ γ β boundary boundaryComplete : ℝ,
      0 < δ → 0 < γ → 0 ≤ β → 0 ≤ nx → 0 ≤ nz →
      full = s + c → δ * nx ≤ s → γ * nz ≤ c →
      ntot ≤ (1 + 2 * β ^ 2) * nx + 2 * nz →
      0 ≤ boundary → boundaryComplete = full + boundary →
      min (δ / (1 + 2 * β ^ 2)) (γ / 2) * ntot ≤
        boundaryComplete) := by
  obtain ⟨_, hleft, hright⟩ := gt_boundary_complete_short C DT
  rw [← hK, ← hW] at hleft hright
  refine ⟨⟨hleft, hright⟩, rfl,
    (gt_boundary_relaxation_dispersion K W E hleft hright).1, ?_⟩
  intro full s c nx nz ntot δ γ β boundary boundaryComplete
    hδ hγ hβ hnx hnz hfull hs hc hdom hboundary hcomplete
  have hfloor := ym_two_scale_feshbach.1 full s c nx nz ntot δ γ β
    hδ hγ hβ hnx hnz hfull hs hc hdom
  rw [hcomplete]
  linarith

end YMBoundaryCompleteInfraredHandoffExact
end NCG
