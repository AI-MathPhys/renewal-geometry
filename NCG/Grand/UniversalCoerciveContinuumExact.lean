/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.CompatibleCylinder

/-!
# The universal coercive continuum: direct-limit handoff and gap

Machinery for `thm:universal-coercive-continuum`, addressing the
fidelity-audit gap (the direct-limit handoff — the record's title clause):
its three anchors are proved records — `thm:universal-Hankel-exhaustion`
(transient norm = supremum over source heads), `thm:sharp-positive-head-tail`
(branch (H1) with the boxed `q* = (a+d+√((a−d)²+4b²))/2`), and
`thm:weighted-source-influence` (branch (H2)) — and the dense-exhaustion
module-bound criterion is the proved `NCG.bounded_action_of_uniform_bound`.
The record-local handoff content is formalized here:

* `pow_eq_exp_gap` / `contraction_gap`: a compression of norm at most
  `q* < 1` decays at rate at least `−τ⁻¹ log q*` in physical time `nτ` —
  the boxed gap clause;
* `universal_coercive_continuum`: the bundle — the uniform stage bound on a
  dense exhaustion extends to the direct-limit transfer with the same
  noncollapsing contraction, whose gap at physical time `τ` is at least
  `−τ⁻¹ log q* > 0`.
-/

namespace NCG
namespace UniversalCoercive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The scalar gap identity: `q^n = exp(−(τ⁻¹ log q⁻¹)·nτ)`. -/
theorem pow_eq_exp_gap (q τ : ℝ) (hq0 : 0 < q) (hτ : 0 < τ) (n : ℕ) :
    q ^ n = Real.exp (-(τ⁻¹ * Real.log q⁻¹) * (n * τ)) := by
  have hexp : -(τ⁻¹ * Real.log q⁻¹) * (n * τ) = (n : ℝ) * Real.log q := by
    rw [Real.log_inv]
    field_simp
  rw [hexp, Real.exp_nat_mul, Real.exp_log hq0]

/-- **The noncollapsing contraction gap**: a transient compression of norm at
most `q* < 1` decays at rate at least `−τ⁻¹ log q*` in physical time `nτ`. -/
theorem contraction_gap (T : E →L[ℂ] E) (q τ : ℝ) (hq0 : 0 < q) (hτ : 0 < τ)
    (hT : ‖T‖ ≤ q) (n : ℕ) :
    ‖T ^ n‖ ≤ Real.exp (-(τ⁻¹ * Real.log q⁻¹) * (n * τ)) := by
  rw [← pow_eq_exp_gap q τ hq0 hτ n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [ContinuousLinearMap.one_def] using ContinuousLinearMap.norm_id_le
  · calc ‖T ^ n‖ ≤ ‖T‖ ^ n := norm_pow_le' T hn
      _ ≤ q ^ n := pow_le_pow_left₀ (norm_nonneg T) hT n

/-- **The universal coercive continuum bundle**: the uniform stage bound `q*`
on a dense exhaustion extends to the direct-limit transfer (the proved
module-bound criterion), which therefore carries the same noncollapsing
contraction and a spectral gap of at least `−τ⁻¹ log q* > 0` at physical
time `τ`. -/
theorem universal_coercive_continuum (T : E →L[ℂ] E) (q τ : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hτ : 0 < τ) (D : ℕ → Set E)
    (hdense : Dense (⋃ m, D m))
    (hbd : ∀ m, ∀ x ∈ D m, ‖T x‖ ≤ q * ‖x‖) :
    ‖T‖ ≤ q ∧ 0 < τ⁻¹ * Real.log q⁻¹ ∧
      ∀ n : ℕ, ‖T ^ n‖ ≤ Real.exp (-(τ⁻¹ * Real.log q⁻¹) * (n * τ)) := by
  have hnorm := NCG.bounded_action_of_uniform_bound T q hq0.le D hdense hbd
  refine ⟨hnorm, ?_, contraction_gap T q τ hq0 hτ hnorm⟩
  have hinv : 1 < q⁻¹ := one_lt_inv_iff₀.mpr ⟨hq0, hq1⟩
  exact mul_pos (inv_pos.mpr hτ) (Real.log_pos hinv)

end UniversalCoercive
end NCG
