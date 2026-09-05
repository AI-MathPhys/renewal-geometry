/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Lipschitz semiprime profile and the atomic–continuous split
  (`thm:v003-profile-lipschitz`, `thm:v003-atomic-continuous`,
   arithmetic manuscript)

Finite-carrier rendering:

* `profile_lipschitz`: the boxed interval bound
  `μ_x⁽²⁾([u,v]) ≪ (v-u) + 1/L` — with the dimension-two sieve
  bound per factor `r` (`hper`, the displayed Assumption
  `ass:v003-two-form-sieve`) and the Mertens sum
  `Σ_{r ∈ window} log r/r ≤ C_M((v-u)L + 1)` (`hmert`, the
  displayed classical input over the window
  `e^{uL} < r ≤ e^{vL}`), the normalized measure of `[u,v]` is
  `≤ C_x·C_M·((v-u) + 1/L)`;
* `atomic_continuous_split`: the boxed decomposition
  `ν = τδ₀ + μ♯` at finite scale — the carrier mass splits
  exactly into the prime-target atom `τ` and the semiprime
  profile mass, and the rough-carrier lower bound transfers to
  the sum `τ + μ♯-mass ≥ M`.

Rendering disclosed: the weak-* subsequential limit statements
(absolute continuity of every limit of `μ_x⁽²⁾`, `L^∞` density,
support convergence into `[1/12, 3/7]`) are the manuscript's
compactness bookkeeping on top of the uniform interval bound
proved here; the sieve constant and Mertens window sum are the
displayed classical inputs.
-/

namespace NCG

/-- `thm:v003-profile-lipschitz`, boxed interval bound in finite
form: sieve bound per factor + Mertens window sum give
`μ_x⁽²⁾([u,v]) ≤ C_x C_M ((v-u) + 1/L)`. -/
theorem profile_lipschitz (R : Finset ℕ) (contrib : ℕ → ℝ)
    (Cx CM L u v x : ℝ) (hL : 0 < L) (hx : 0 < x)
    (hCx : 0 ≤ Cx)
    (hper : ∀ r ∈ R,
      contrib r ≤ Cx * x * (Real.log r / r) / L ^ 2)
    (hmert : ∑ r ∈ R, Real.log r / r ≤ CM * ((v - u) * L + 1)) :
    L / x * ∑ r ∈ R, contrib r
      ≤ Cx * CM * ((v - u) + 1 / L) := by
  have h1 : ∑ r ∈ R, contrib r
      ≤ Cx * x / L ^ 2 * ∑ r ∈ R, Real.log r / r := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    calc contrib r ≤ Cx * x * (Real.log r / r) / L ^ 2 :=
        hper r hr
      _ = Cx * x / L ^ 2 * (Real.log r / r) := by ring
  have h2 : Cx * x / L ^ 2 * ∑ r ∈ R, Real.log r / r
      ≤ Cx * x / L ^ 2 * (CM * ((v - u) * L + 1)) := by
    have hnn : (0:ℝ) ≤ Cx * x / L ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hmert hnn
  have h3 : L / x * ∑ r ∈ R, contrib r
      ≤ L / x * (Cx * x / L ^ 2 * (CM * ((v - u) * L + 1))) := by
    have hnn : (0:ℝ) ≤ L / x := by positivity
    exact mul_le_mul_of_nonneg_left (le_trans h1 h2) hnn
  refine le_trans h3 (le_of_eq ?_)
  field_simp

/-- `thm:v003-atomic-continuous`, finite-scale decomposition: the
carrier mass splits exactly into the prime atom `τ` and the
semiprime profile mass, and the carrier lower bound transfers to
the sum. -/
theorem atomic_continuous_split (S : Finset ℕ) (w : ℕ → ℝ)
    (isPrimeTarget : ℕ → Prop) [DecidablePred isPrimeTarget]
    (M : ℝ) (hlb : M ≤ ∑ p ∈ S, w p) :
    M ≤ (∑ p ∈ S.filter isPrimeTarget, w p)
        + ∑ p ∈ S.filter (fun p => ¬ isPrimeTarget p), w p := by
  rw [Finset.sum_filter_add_sum_filter_not]
  exact hlb

end NCG
