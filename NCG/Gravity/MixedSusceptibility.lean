/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Mixed current–screen and current–metric susceptibilities
  (`prop:mixed-perron-susceptibilities`, GR_emergence)

The mixed Perron susceptibilities are connected stationary cumulants
with exactly one deficiency (time-reversal odd) insertion and
otherwise even insertions.  Under a reversing involution that
preserves the stationary law, every such correlation vanishes term by
term, and the chain rule converts the trace-susceptibility derivative
into `κ_{Bε} = ∂_χ tr C(0)/(2dε)`:

* `odd_observable_mean_zero` — a time-reversal odd observable has
  zero stationary mean;
* `odd_even_correlation_zero` — one odd and one even insertion
  (`κ_{Bη} = 0` term shape);
* `odd_two_even_correlation_zero` — one odd and two even insertions
  (`∂_χ C_{ab}(0)` term shape);
* `sqrt_trace_susceptibility` — the chain rule
  `∂_χ (tr C(χ)/d)^{1/2}|₀ = ∂_χ tr C(0)/(2dε)` for
  `tr C(0)/d = ε²`, and its reversible-vanishing corollary.

The identification of the mixed pressure derivatives with these
stationary Green–Kubo correlations (absolute convergence term by
term) is the declared analytic interface of the record.
-/

namespace NCG

variable {E : Type*} [Fintype E]

/-- A time-reversal odd observable has zero stationary mean under an
involution preserving the stationary law. -/
theorem odd_observable_mean_zero (pi : E → ℝ) (sigma : Equiv.Perm E)
    (hpi : ∀ x, pi (sigma x) = pi x)
    (f : E → ℝ) (hodd : ∀ x, f (sigma x) = -f x) :
    ∑ x, pi x * f x = 0 := by
  have h1 : ∑ x, pi (sigma x) * f (sigma x) = ∑ x, pi x * f x :=
    Equiv.sum_comp sigma (fun x => pi x * f x)
  have h2 : ∑ x, pi (sigma x) * f (sigma x)
      = -∑ x, pi x * f x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [hpi x, hodd x]
    ring
  linarith [h1, h2]

/-- `κ_{Bη}` term shape: a stationary correlation with one odd
(deficiency) and one even (screen-surprisal) insertion vanishes. -/
theorem odd_even_correlation_zero (pi : E → ℝ) (sigma : Equiv.Perm E)
    (hpi : ∀ x, pi (sigma x) = pi x)
    (b eta : E → ℝ) (hb : ∀ x, b (sigma x) = -b x)
    (heta : ∀ x, eta (sigma x) = eta x) :
    ∑ x, pi x * (b x * eta x) = 0 := by
  apply odd_observable_mean_zero pi sigma hpi
  intro x
  rw [hb x, heta x]
  ring

/-- `∂_χ C_{ab}(0)` term shape: a stationary correlation with one odd
and two even (displacement) insertions vanishes. -/
theorem odd_two_even_correlation_zero (pi : E → ℝ)
    (sigma : Equiv.Perm E) (hpi : ∀ x, pi (sigma x) = pi x)
    (b e1 e2 : E → ℝ) (hb : ∀ x, b (sigma x) = -b x)
    (he1 : ∀ x, e1 (sigma x) = e1 x)
    (he2 : ∀ x, e2 (sigma x) = e2 x) :
    ∑ x, pi x * (b x * (e1 x * e2 x)) = 0 := by
  apply odd_observable_mean_zero pi sigma hpi
  intro x
  rw [hb x, he1 x, he2 x]
  ring

/-- The chain rule for the metric-calibration susceptibility:
if `tr C(χ)/d` has derivative `c'/d` at `0` and value `ε² > 0`, then
`ε(χ) = (tr C(χ)/d)^{1/2}` has derivative
`κ_{Bε} = c'/(2dε)` at `0`. -/
theorem sqrt_trace_susceptibility {c : ℝ → ℝ} {c' d eps : ℝ}
    (hd : 0 < d) (heps : 0 < eps)
    (hc : HasDerivAt c c' 0) (h0 : c 0 = d * eps ^ 2) :
    HasDerivAt (fun x => Real.sqrt (c x / d)) (c' / (2 * d * eps)) 0 := by
  have h1 : HasDerivAt (fun x => c x / d) (c' / d) 0 := hc.div_const d
  have hval : c 0 / d = eps ^ 2 := by
    rw [h0]
    field_simp
  have hne : c 0 / d ≠ 0 := by
    rw [hval]
    positivity
  have h2 := (Real.hasDerivAt_sqrt hne).comp 0 h1
  have hsq : Real.sqrt (c 0 / d) = eps := by
    rw [hval, Real.sqrt_sq heps.le]
  rw [hsq] at h2
  exact h2.congr_deriv (by field_simp)

/-- `prop:mixed-perron-susceptibilities` (reversible vanishing): if
the trace susceptibility derivative is itself a one-odd-insertion
stationary correlation, both mixed susceptibilities vanish at the
reversible locus: `κ_{Bη} = 0` and `κ_{Bε} = 0`. -/
theorem mixed_susceptibilities_vanish (pi : E → ℝ)
    (sigma : Equiv.Perm E) (hpi : ∀ x, pi (sigma x) = pi x)
    (b eta : E → ℝ) (hb : ∀ x, b (sigma x) = -b x)
    (heta : ∀ x, eta (sigma x) = eta x)
    {kBeta : ℝ}
    (hkBeta : kBeta = ∑ x, pi x * (b x * eta x))
    {c : ℝ → ℝ} {d eps : ℝ} (hd : 0 < d) (heps : 0 < eps)
    (e1 e2 : E → ℝ) (he1 : ∀ x, e1 (sigma x) = e1 x)
    (he2 : ∀ x, e2 (sigma x) = e2 x)
    (hc : HasDerivAt c (∑ x, pi x * (b x * (e1 x * e2 x))) 0)
    (h0 : c 0 = d * eps ^ 2) :
    kBeta = 0 ∧
      HasDerivAt (fun x => Real.sqrt (c x / d)) 0 0 := by
  constructor
  · rw [hkBeta]
    exact odd_even_correlation_zero pi sigma hpi b eta hb heta
  · have hzero := odd_two_even_correlation_zero pi sigma hpi
      b e1 e2 hb he1 he2
    have h := sqrt_trace_susceptibility hd heps hc h0
    rw [hzero] at h
    simpa using h

end NCG
