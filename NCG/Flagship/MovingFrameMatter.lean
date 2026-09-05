/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact moving-frame matter bracket
  (`thm:moving-frame-matter-master`, flagship manuscript)

The provable algebra of the matter self-bracket:

* `matter_bracket_antisymmetric`: the boxed edge form
  `Σ_e (N_xM_y - M_xN_y)𝔡_e` is antisymmetric in `(N, M)` — the
  bracket shape;
* `symmetric_terms_cancel`: local-potential cross terms carry
  the symmetric factor `N_xM_x` and cancel exactly in the
  antisymmetrization;
* `species_amplitude_one`: positivity of the species-current
  Gram forces every positive relative amplitude to one —
  `λ > 0` with `λ² = 1` (the Gram identifies the `λ²`-weighted
  representation with the unweighted one) gives `λ = 1`;
* `cross_bracket_cancel`: endpoint-local dependence on the
  canonical metric register makes the antisymmetrized
  gravity–matter cross bracket vanish — equal mixed factors
  cancel under antisymmetrization.

Rendering disclosed: the per-edge kinetic–gradient commutator
computation producing `𝔡_e` (the anticommutator combination of
the two endpoint kinetic terms) and the conductance
second-moment limit to the continuum diffeomorphism constraint
are the manuscript's model layer.
-/

namespace NCG

/-- The boxed edge form is antisymmetric in the two lapses. -/
theorem matter_bracket_antisymmetric {E : Type*}
    (edges : Finset E) (Nx Ny Mx My d : E → ℝ) :
    ∑ e ∈ edges, (Nx e * My e - Mx e * Ny e) * d e
      = -∑ e ∈ edges, (Mx e * Ny e - Nx e * My e) * d e := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- Symmetric local-potential cross terms cancel exactly in the
antisymmetrization. -/
theorem symmetric_terms_cancel {E : Type*} (edges : Finset E)
    (Nx Mx f : E → ℝ) :
    ∑ e ∈ edges, (Nx e * Mx e - Mx e * Nx e) * f e = 0 := by
  refine Finset.sum_eq_zero fun e _ => ?_
  ring

/-- Positive relative amplitudes with unit-normalized species
Gram equal one: `λ > 0`, `λ² = 1 ⟹ λ = 1`. -/
theorem species_amplitude_one (lam : ℝ) (hpos : 0 < lam)
    (hsq : lam ^ 2 = 1) : lam = 1 := by
  nlinarith

/-- Endpoint-local metric dependence: equal mixed factors cancel
under antisymmetrization — the gravity–matter cross bracket
vanishes exactly. -/
theorem cross_bracket_cancel {E : Type*} (edges : Finset E)
    (lapse grav matter : E → ℝ) :
    ∑ e ∈ edges, (lapse e * (grav e * matter e)
      - lapse e * (grav e * matter e)) = 0 := by
  simp

end NCG
