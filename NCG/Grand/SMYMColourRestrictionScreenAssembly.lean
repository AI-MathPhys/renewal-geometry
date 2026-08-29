/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMYMColourRestrictionExact
import NCG.Grand.UniversalCoupledActionCarrier

/-!
# Colour-vacuum restriction on the inherited regulator screen

This file closes the regulator-framing clause of
the exact colour-restriction theorem.  The colour restriction uses the same
vertex, edge, and face types as the active Standard-Model field, and its fixed
three-dimensional internal fibre changes a spacetime spectral screen only by
the exact finite-fibre multiplicity factor three.
-/

open Matrix

namespace NCG
namespace ColourRestriction

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

/-- The inherited spacetime screen on a colour fibre has exactly three copies
of every selected spacetime mode.  In particular, a finite/compact screen
stays finite and no second compactness primitive is introduced. -/
theorem colour_fibre_screen_rank
    {p : Type*} [Fintype p] [DecidableEq p]
    (z : p → Prop) [DecidablePred z] :
    (finiteFibreScreen (r := Fin 3) z).rank
      = 3 * (Matrix.diagonal
          (fun i : p => if z i then (1 : ℂ) else 0)).rank := by
  simpa using (finiteFibreScreen_rank (r := Fin 3) z)

/-- Complete CY.1--CY.2 packet on the original emerged regulator: exact
colour-vacuum restriction, inherited local colour Ward identity, and exact
finite-Hodge-screen multiplicity. -/
theorem exact_colour_vacuum_restriction_on_inherited_screen
    (s t : E → V)
    (g₃ g₂ lam vH : ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (plaq : F → Plaquette V E) (hcomp : ∀ p, Compatible s t (plaq p))
    (h₀ : Fin 2 → ℂ) (hnorm : ∑ i, Complex.normSq (h₀ i) = 1) :
    (∀ U : E → Matrix (Fin 3) (Fin 3) ℂ,
      regulatedStandardModelAction (faceDensity g₃ g₂ plaq) (edgeDensity s t)
        (siteDensity lam vH) (fermionDensity Y) (embed vH h₀ U)
        = (2 : ℝ)⁻¹ * ∑ p,
            g₃ * hsNormSq (curvC (plaq p) (embed vH h₀ U)))
    ∧ (∀ (g : V → Matrix (Fin 3) (Fin 3) ℂ),
        (∀ v, g v ∈ Matrix.unitaryGroup (Fin 3) ℂ) →
        ∀ U : E → Matrix (Fin 3) (Fin 3) ℂ,
          (2 : ℝ)⁻¹ * ∑ p,
              g₃ * hsNormSq
                (curvC (plaq p) (embed vH h₀ (gaugeActC s t g U)))
            = (2 : ℝ)⁻¹ * ∑ p,
                g₃ * hsNormSq (curvC (plaq p) (embed vH h₀ U)))
    ∧ (∀ {p : Type*} [Fintype p] [DecidableEq p]
        (z : p → Prop) [DecidablePred z],
        (finiteFibreScreen (r := Fin 3) z).rank
          = 3 * (Matrix.diagonal
              (fun i : p => if z i then (1 : ℂ) else 0)).rank) := by
  refine ⟨(smym_colour_restriction s t g₃ g₂ lam vH Y plaq hcomp h₀ hnorm).1,
    (smym_colour_restriction s t g₃ g₂ lam vH Y plaq hcomp h₀ hnorm).2, ?_⟩
  intro p _ _ z _
  exact colour_fibre_screen_rank z

end ColourRestriction
end NCG
