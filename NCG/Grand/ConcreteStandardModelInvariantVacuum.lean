/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMYMColourRestrictionExact

/-!
# Concrete invariant vacuum for the finite Standard-Model action

This file supplies CA.7--CA.8 for the actual finite field record and local
densities.  Both gauge-link banks are the identity, the Higgs field is the
constant normalized vector `vH • h₀`, and the fermion field is zero.
-/

open Matrix
open scoped BigOperators

namespace NCG
namespace StandardModelInvariantVacuum

open ColourRestriction

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
variable (s t : E → V)

/-- CA.7: the literal invariant internal vacuum. -/
def invariantVacuum (vH : ℝ) (h₀ : Fin 2 → ℂ) : SMField V E :=
  embed vH h₀ (fun _ => 1)

@[simp] theorem invariantVacuum_linkC (vH : ℝ) (h₀ : Fin 2 → ℂ) (e : E) :
    (invariantVacuum (V := V) (E := E) vH h₀).linkC e = 1 := rfl

@[simp] theorem invariantVacuum_linkW (vH : ℝ) (h₀ : Fin 2 → ℂ) (e : E) :
    (invariantVacuum (V := V) (E := E) vH h₀).linkW e = 1 := rfl

@[simp] theorem invariantVacuum_higgs (vH : ℝ) (h₀ : Fin 2 → ℂ) (v : V) :
    (invariantVacuum (V := V) (E := E) vH h₀).higgs v =
      fun i => (vH : ℂ) * h₀ i := rfl

@[simp] theorem invariantVacuum_psi (vH : ℝ) (h₀ : Fin 2 → ℂ) (v : V) :
    (invariantVacuum (V := V) (E := E) vH h₀).psi v = 0 := rfl

/-- Every colour plaquette is flat at the invariant vacuum. -/
theorem curvC_invariantVacuum (P : Plaquette V E) (vH : ℝ)
    (h₀ : Fin 2 → ℂ) :
    curvC P (invariantVacuum vH h₀) = 0 := by
  simp [curvC, invariantVacuum, embed]

/-- Every weak plaquette is flat at the invariant vacuum. -/
theorem curvW_invariantVacuum (P : Plaquette V E) (vH : ℝ)
    (h₀ : Fin 2 → ℂ) :
    curvW P (invariantVacuum vH h₀) = 0 := by
  simp [curvW, invariantVacuum, embed]

/-- The complete gauge density vanishes plaquette by plaquette. -/
theorem faceDensity_invariantVacuum (g₃ g₂ : ℝ)
    (plaq : F → Plaquette V E) (vH : ℝ) (h₀ : Fin 2 → ℂ) (p : F) :
    faceDensity g₃ g₂ plaq p (invariantVacuum vH h₀) = 0 := by
  simp [faceDensity, curvC_invariantVacuum, curvW_invariantVacuum,
    hsNormSq_zero]

/-- The transported-Higgs density vanishes edge by edge. -/
theorem edgeDensity_invariantVacuum (vH : ℝ) (h₀ : Fin 2 → ℂ) (e : E) :
    edgeDensity s t e (invariantVacuum vH h₀) = 0 := by
  simpa [invariantVacuum] using
    (edge_embed s t vH h₀ (fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℂ)) e)

/-- The radial Higgs density vanishes vertex by vertex when `h₀` is normalized. -/
theorem siteDensity_invariantVacuum (lam vH : ℝ) (h₀ : Fin 2 → ℂ)
    (hnorm : ∑ i, Complex.normSq (h₀ i) = 1) (v : V) :
    siteDensity lam vH v (invariantVacuum (E := E) vH h₀) = 0 := by
  simpa [invariantVacuum] using
    (site_embed lam vH h₀ hnorm
      (fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℂ)) v)

/-- The fermion density vanishes vertex by vertex because the vacuum fermion
field is zero. -/
theorem fermionDensity_invariantVacuum (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (vH : ℝ) (h₀ : Fin 2 → ℂ) (v : V) :
    fermionDensity Y v (invariantVacuum (E := E) vH h₀) = 0 := by
  simpa [invariantVacuum] using
    (fermion_embed Y vH h₀
      (fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℂ)) v)

/-- The signed regulated Standard-Model action vanishes at the concrete
invariant vacuum. -/
theorem regulatedAction_invariantVacuum
    (g₃ g₂ lam vH : ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (plaq : F → Plaquette V E) (h₀ : Fin 2 → ℂ)
    (hnorm : ∑ i, Complex.normSq (h₀ i) = 1) :
    regulatedStandardModelAction (faceDensity g₃ g₂ plaq) (edgeDensity s t)
      (siteDensity lam vH) (fermionDensity Y) (invariantVacuum vH h₀) = 0 := by
  exact regulatedStandardModelAction_vacuum _ _ _ _ _
    (faceDensity_invariantVacuum g₃ g₂ plaq vH h₀)
    (edgeDensity_invariantVacuum s t vH h₀)
    (siteDensity_invariantVacuum (E := E) lam vH h₀ hnorm)
    (fermionDensity_invariantVacuum (E := E) Y vH h₀)

/-- A positive operational cost made from the same four local density banks.
The signed fermion pairing is squared, and the remaining signed coefficients
are clipped at zero, so positivity is unconditional. -/
noncomputable def regulatedStandardModelPositiveCost
    (g₃ g₂ lam vH : ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (plaq : F → Plaquette V E) (Φ : SMField V E) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ p, max (faceDensity g₃ g₂ plaq p Φ) 0 +
    (2 : ℝ)⁻¹ * ∑ e, max (edgeDensity s t e Φ) 0 +
    ∑ v, max (siteDensity lam vH v Φ) 0 +
    ∑ v, (fermionDensity Y v Φ) ^ 2

theorem regulatedStandardModelPositiveCost_nonnegative
    (g₃ g₂ lam vH : ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (plaq : F → Plaquette V E) (Φ : SMField V E) :
    0 ≤ regulatedStandardModelPositiveCost s t g₃ g₂ lam vH Y plaq Φ := by
  unfold regulatedStandardModelPositiveCost
  positivity

/-- The positive operational cost also vanishes at the same concrete vacuum. -/
theorem positiveCost_invariantVacuum
    (g₃ g₂ lam vH : ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (plaq : F → Plaquette V E) (h₀ : Fin 2 → ℂ)
    (hnorm : ∑ i, Complex.normSq (h₀ i) = 1) :
    regulatedStandardModelPositiveCost s t g₃ g₂ lam vH Y plaq
      (invariantVacuum vH h₀) = 0 := by
  simp [regulatedStandardModelPositiveCost,
    faceDensity_invariantVacuum g₃ g₂ plaq vH h₀,
    edgeDensity_invariantVacuum s t vH h₀,
    siteDensity_invariantVacuum (E := E) lam vH h₀ hnorm,
    fermionDensity_invariantVacuum (E := E) Y vH h₀]

/-- Concrete CA.7--CA.8 zero packet for both the signed action and positive
operational cost, including all four pointwise local-density witnesses. -/
theorem invariantVacuum_zero_packet
    (g₃ g₂ lam vH : ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (plaq : F → Plaquette V E) (h₀ : Fin 2 → ℂ)
    (hnorm : ∑ i, Complex.normSq (h₀ i) = 1) :
    (∀ p : F, faceDensity g₃ g₂ plaq p (invariantVacuum vH h₀) = 0) ∧
    (∀ e : E, edgeDensity s t e (invariantVacuum vH h₀) = 0) ∧
    (∀ v : V, siteDensity lam vH v (invariantVacuum (E := E) vH h₀) = 0) ∧
    (∀ v : V, fermionDensity Y v (invariantVacuum (E := E) vH h₀) = 0) ∧
    regulatedStandardModelAction (faceDensity g₃ g₂ plaq) (edgeDensity s t)
      (siteDensity lam vH) (fermionDensity Y) (invariantVacuum vH h₀) = 0 ∧
    regulatedStandardModelPositiveCost s t g₃ g₂ lam vH Y plaq
      (invariantVacuum vH h₀) = 0 := by
  exact ⟨faceDensity_invariantVacuum g₃ g₂ plaq vH h₀,
    edgeDensity_invariantVacuum s t vH h₀,
    siteDensity_invariantVacuum (E := E) lam vH h₀ hnorm,
    fermionDensity_invariantVacuum (E := E) Y vH h₀,
    regulatedAction_invariantVacuum s t g₃ g₂ lam vH Y plaq h₀ hnorm,
    positiveCost_invariantVacuum s t g₃ g₂ lam vH Y plaq h₀ hnorm⟩

end StandardModelInvariantVacuum
end NCG
