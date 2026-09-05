/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Perron large-deviation potential: convex layer
  (`thm:deficiency-rate-function`, GR_emergence)

The Legendre–Fenchel transform `I_B(b) = sup_χ (χb - Λ_B(χ))` of a
convex pressure with `Λ_B(0) = 0`, `Λ_B'(0) = B_*`:

* `pressure_tangent_bound` — the tangent bound `χB_* ≤ Λ_B(χ)`;
* `rate_function_at_mean` — `I_B(B_*) = 0`, attained at `χ = 0`;
* `rate_function_nonneg` — `I_B ≥ 0` wherever defined;
* `rate_function_convex_combination` — convexity of `I_B`;
* `rate_min_deriv_zero` — `I_B'(B_*) = 0` when differentiable.

These are the displayed properties `I_B(B_*) = I_B'(B_*) = 0` and
good convexity.  The Gärtner–Ellis large-deviation principle itself
and the curvature identity `I_B''(B_*) = 1/σ_B²` (smooth Legendre
duality) are the declared large-deviations layer.
-/

namespace NCG

/-- The Legendre–Fenchel rate function of the pressure. -/
noncomputable def rateFunction (Lam : ℝ → ℝ) (b : ℝ) : ℝ :=
  ⨆ chi : ℝ, (chi * b - Lam chi)

/-- `thm:deficiency-rate-function` (tangent bound): a convex pressure
lies above its tangent at the origin, `χB_* ≤ Λ(χ)`. -/
theorem pressure_tangent_bound {Lam : ℝ → ℝ} {Bstar : ℝ}
    (hconv : ConvexOn ℝ Set.univ Lam) (h0 : Lam 0 = 0)
    (hd : HasDerivAt Lam Bstar 0) :
    ∀ chi : ℝ, chi * Bstar ≤ Lam chi := by
  intro chi
  rcases lt_trichotomy chi 0 with h | h | h
  · have hs := hconv.slope_le_of_hasDerivAt (Set.mem_univ chi)
      (Set.mem_univ 0) h hd
    rw [slope_def_field, h0] at hs
    have hs' : Lam chi / chi ≤ Bstar := by
      calc Lam chi / chi = (0 - Lam chi) / (0 - chi) := by
            rw [zero_sub, zero_sub, neg_div_neg_eq]
      _ ≤ Bstar := hs
    rw [div_le_iff_of_neg h] at hs'
    linarith [hs']
  · rw [h, zero_mul, h0]
  · have hs := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0)
      (Set.mem_univ chi) h hd
    rw [slope_def_field, h0, sub_zero, sub_zero] at hs
    rw [le_div_iff₀ h] at hs
    linarith [hs]

/-- `thm:deficiency-rate-function` (`I_B(B_*) = 0`): the rate
function vanishes at the Perron mean, with the supremum attained at
`χ = 0`. -/
theorem rate_function_at_mean {Lam : ℝ → ℝ} {Bstar : ℝ}
    (hconv : ConvexOn ℝ Set.univ Lam) (h0 : Lam 0 = 0)
    (hd : HasDerivAt Lam Bstar 0) :
    rateFunction Lam Bstar = 0 := by
  have hgreat : IsGreatest
      (Set.range fun chi : ℝ => chi * Bstar - Lam chi) 0 := by
    constructor
    · exact ⟨0, by change (0 : ℝ) * Bstar - Lam 0 = 0
                   rw [zero_mul, h0, sub_zero]⟩
    · rintro y ⟨chi, rfl⟩
      have := pressure_tangent_bound hconv h0 hd chi
      change chi * Bstar - Lam chi ≤ 0
      linarith
  rw [rateFunction, iSup]
  exact hgreat.csSup_eq

/-- `thm:deficiency-rate-function` (`I_B ≥ 0`): the rate function is
nonnegative wherever the defining family is bounded above. -/
theorem rate_function_nonneg {Lam : ℝ → ℝ} (h0 : Lam 0 = 0) (b : ℝ)
    (hbdd : BddAbove (Set.range fun chi : ℝ => chi * b - Lam chi)) :
    0 ≤ rateFunction Lam b := by
  have h := le_ciSup hbdd (0 : ℝ)
  rw [zero_mul, h0, sub_zero] at h
  exact h

/-- `thm:deficiency-rate-function` (convexity): the rate function is
convex — a Legendre–Fenchel transform is a supremum of affine
functions of `b`. -/
theorem rate_function_convex_combination {Lam : ℝ → ℝ}
    {b1 b2 t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hbdd1 : BddAbove (Set.range fun chi : ℝ => chi * b1 - Lam chi))
    (hbdd2 : BddAbove (Set.range fun chi : ℝ => chi * b2 - Lam chi))
    (hne : Nonempty ℝ) :
    rateFunction Lam (t * b1 + (1 - t) * b2)
      ≤ t * rateFunction Lam b1 + (1 - t) * rateFunction Lam b2 := by
  apply ciSup_le
  intro chi
  have h1 : chi * b1 - Lam chi ≤ rateFunction Lam b1 :=
    le_ciSup hbdd1 chi
  have h2 : chi * b2 - Lam chi ≤ rateFunction Lam b2 :=
    le_ciSup hbdd2 chi
  have e : chi * (t * b1 + (1 - t) * b2) - Lam chi
      = t * (chi * b1 - Lam chi) + (1 - t) * (chi * b2 - Lam chi) := by
    ring
  rw [e]
  have ht1' : 0 ≤ 1 - t := by linarith
  calc t * (chi * b1 - Lam chi) + (1 - t) * (chi * b2 - Lam chi)
      ≤ t * rateFunction Lam b1
          + (1 - t) * rateFunction Lam b2 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h1 ht0
        · exact mul_le_mul_of_nonneg_left h2 ht1'

/-- `thm:deficiency-rate-function` (`I_B'(B_*) = 0`): the Perron mean
is a global minimum of the rate function, so any derivative there
vanishes. -/
theorem rate_min_deriv_zero {I : ℝ → ℝ} {Bstar dI : ℝ}
    (hmin : ∀ b, I Bstar ≤ I b) (hd : HasDerivAt I dI Bstar) :
    dI = 0 := by
  have hloc : IsLocalMin I Bstar :=
    Filter.Eventually.of_forall (fun b => hmin b)
  exact hloc.hasDerivAt_eq_zero hd

end NCG
