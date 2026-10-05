/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.TransportGaugeVariation
import RenewalGeometry.Algebra.SeriesLogChart

/-!
# First variations of the comparison stencils (covariant differences and log plaquettes)

Generic infrastructure for the proof of `prop:mesh-consistency` (Einstein–Standard-Model
action-closure manuscript, "These expansions also hold after one field or metric variation …
differentiate the transport equation itself").  It extends `GaugeTheory/TransportGaugeVariation`
(variations of transports along *affine* lines `A + t a` of connections) in three directions.

* **Non-affine families of connections** (`hasDerivAt_backwardLink_of_sq`,
  `hasDerivAt_forwardLink_of_sq`): if `Ω_t = Ω_0 + t α + O(t²)` uniformly, the links of `Ω_t` are
  differentiable at `t = 0` with the derivative of the affine line (transport stability,
  `norm_transport_sub_transport_le`).  This covers the metric variation of the spin connection,
  which is not affine in the coframe.
* **The covariant difference stencils after one variation**:
  - `centredDiff` (`eq:spin-difference`, `(2h)⁻¹(𝒰(x)Ψ(x+he) - 𝒰(x-he)⁻¹Ψ(x-he))`):
    `hasDerivAt_centredDiff` and `norm_centredDiff_variation_sub_le`
    (`δ∇^hΨ = αΨ + ∂η + Ω η + O(h)`);
  - `fwdDiff` (the Higgs link `h⁻¹(U(x)H(x+he) - H(x))` of `eq:lattice-comparison`):
    `hasDerivAt_fwdDiff` and `norm_fwdDiff_variation_sub_le` (`δK^h = aH + ∂η + Aη + O(h)`).
* **The log plaquette after one gauge variation** (`hasFDerivAt_logOneAdd`,
  `norm_fderiv_logOneAdd_sub_le`, `logPlaquette_variation`): the series logarithm has the termwise
  derivative and `‖D log(1+z)[w] - w‖ ≤ 2‖z‖‖w‖` for `‖z‖ ≤ 1/2`, so
  `δF^h = h⁻² D log(U_{μν} - 1)[δU_{μν}] = dF + O(h)`.
-/

open Set Filter Topology Asymptotics
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.TransportStencilVariation

open PathOrderedExp TransportPlaquetteConsistency TransportGaugeVariation TrivSqZeroExt

/-! ### Functions with a quadratic remainder -/

/-- A function vanishing to second order at `0` has derivative `0` there. -/
theorem hasDerivAt_zero_of_sq_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {C τ : ℝ} (hτ : 0 < τ) (hf0 : f 0 = 0) (hf : ∀ t : ℝ, |t| ≤ τ → ‖f t‖ ≤ C * t ^ 2) :
    HasDerivAt f 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, hf0, sub_zero, smul_zero]
  have hO : (fun t : ℝ => f t) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hτ] with t ht
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
    exact hf t ht.le
  exact hO.trans_isLittleO (isLittleO_pow_id (by norm_num))

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two transports along the same edge whose coefficients differ by `δ` differ by
`δ h e^{2Kh}` at the end of the edge. -/
theorem norm_transport_end_sub_le {w₁ w₂ : ℝ → 𝔸} {h K δ : ℝ} (hh : 0 ≤ h)
    (hK : ∀ s ∈ Icc 0 h, ‖w₁ s‖ ≤ K) (hK' : ∀ s ∈ Icc 0 h, ‖w₂ s‖ ≤ K)
    (hδ : ∀ s ∈ Icc 0 h, ‖w₁ s - w₂ s‖ ≤ δ) {U V : ℝ → 𝔸} (hU : IsTransport w₁ 0 h U)
    (hV : IsTransport w₂ 0 h V) (hU0 : U 0 = 1) (hV0 : V 0 = 1) :
    ‖U h - V h‖ ≤ δ * h * Real.exp (2 * K * h) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hh⟩)
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 ⟨le_rfl, hh⟩)
  have := norm_transport_sub_transport_le hK hK' hδ hU hV (by rw [hU0, hV0]) h ⟨hh, le_rfl⟩
  rw [hU0, norm_one, one_mul, sub_zero] at this
  refine this.trans ((gronwallBound_zero_le hK0 (by positivity) hh).trans (le_of_eq ?_))
  rw [mul_assoc δ, mul_comm (Real.exp (K * h)) h, ← mul_assoc, mul_assoc (δ * h),
    ← Real.exp_add]
  ring_nf

/-- **Links of a non-affine family of connections** (backward links): if
`‖Ω_t - (Ω_0 + t α)‖ ≤ C t²` uniformly for `|t| ≤ τ`, the backward link of `Ω_t` is
differentiable at `t = 0`, with the derivative of the affine line `Ω_0 + t α`, the `ε`-part of
the backward link of the dual connection `Ω_0 + εα`. -/
theorem hasDerivAt_backwardLink_of_sq {Ω : ℝ → E → 𝔸} {α : E → 𝔸} {K Ka Cq τ : ℝ} (hτ : 0 < τ)
    (hΩc : ∀ t : ℝ, |t| ≤ τ → Continuous (Ω t)) (hαc : Continuous α)
    (hK : ∀ t : ℝ, |t| ≤ τ → ∀ y, ‖Ω t y‖ ≤ K) (hKa : ∀ y, ‖α y‖ ≤ Ka)
    (hq : ∀ t : ℝ, |t| ≤ τ → ∀ y, ‖Ω t y - (Ω 0 y + t • α y)‖ ≤ Cq * t ^ 2)
    (e x : E) {h : ℝ} (hh : 0 ≤ h) :
    HasDerivAt (fun t => backwardLink (Ω t) e x h)
      (backwardLink (fun y => dual (Ω 0 y) (α y)) e x h).snd 0 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by simp [hτ.le]) x)
  have hKa0 : 0 ≤ Ka := (norm_nonneg _).trans (hKa x)
  have hL := (hasDerivAt_backwardLink (hΩc 0 (by simp [hτ.le])) hαc (hK 0 (by simp [hτ.le])) hKa e x hh).2
  set L : ℝ → 𝔸 := fun t => backwardLink (Ω 0 + t • α) e x h
  have hsq : ∀ t : ℝ, |t| ≤ τ →
      ‖backwardLink (Ω t) e x h - L t‖ ≤ (Cq * h * Real.exp (2 * (K + τ * Ka) * h)) * t ^ 2 := by
    intro t ht
    have hc1 : Continuous (Ω t) := hΩc t ht
    have hc2 : Continuous (Ω 0 + t • α) := (hΩc 0 (by simp [hτ.le])).add (hαc.const_smul t)
    have hb1 : ∀ y, ‖Ω t y‖ ≤ K + τ * Ka := fun y => (hK t ht y).trans (by nlinarith)
    have hb2 : ∀ y, ‖(Ω 0 + t • α) y‖ ≤ K + τ * Ka := fun y =>
      (norm_line_le (hK 0 (by simp [hτ.le])) hKa t y).trans (by nlinarith [abs_nonneg t, ht])
    obtain ⟨U, hU0, hU, hUe⟩ := exists_backwardLink hc1 hb1 e x hh
    obtain ⟨V, hV0, hV, hVe⟩ := exists_backwardLink hc2 hb2 e x hh
    rw [hUe]
    show ‖U h - backwardLink (Ω 0 + t • α) e x h‖ ≤ _
    rw [hVe]
    have := norm_transport_end_sub_le (K := K + τ * Ka) (δ := Cq * t ^ 2) hh
      (fun s _ => by rw [norm_neg]; exact hb1 _) (fun s _ => by rw [norm_neg]; exact hb2 _)
      (fun s _ => by
        rw [neg_sub_neg, norm_sub_rev]
        have := hq t ht (x + (h - s) • e)
        simpa [Pi.add_apply, Pi.smul_apply] using this) hU hV hU0 hV0
    refine this.trans (le_of_eq ?_)
    ring
  have hg : HasDerivAt (fun t => backwardLink (Ω t) e x h - L t) 0 0 :=
    hasDerivAt_zero_of_sq_le hτ (by simp [L]) hsq
  have := hL.add hg
  simp only [add_zero] at this
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp [L]

/-- **Links of a non-affine family of connections** (forward links). -/
theorem hasDerivAt_forwardLink_of_sq {Ω : ℝ → E → 𝔸} {α : E → 𝔸} {K Ka Cq τ : ℝ} (hτ : 0 < τ)
    (hΩc : ∀ t : ℝ, |t| ≤ τ → Continuous (Ω t)) (hαc : Continuous α)
    (hK : ∀ t : ℝ, |t| ≤ τ → ∀ y, ‖Ω t y‖ ≤ K) (hKa : ∀ y, ‖α y‖ ≤ Ka)
    (hq : ∀ t : ℝ, |t| ≤ τ → ∀ y, ‖Ω t y - (Ω 0 y + t • α y)‖ ≤ Cq * t ^ 2)
    (e x : E) {h : ℝ} (hh : 0 ≤ h) :
    HasDerivAt (fun t => forwardLink (Ω t) e x h)
      (forwardLink (fun y => dual (Ω 0 y) (α y)) e x h).snd 0 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by simp [hτ.le]) x)
  have hKa0 : 0 ≤ Ka := (norm_nonneg _).trans (hKa x)
  have hL := (hasDerivAt_forwardLink (hΩc 0 (by simp [hτ.le])) hαc (hK 0 (by simp [hτ.le])) hKa e x hh).2
  set L : ℝ → 𝔸 := fun t => forwardLink (Ω 0 + t • α) e x h
  have hsq : ∀ t : ℝ, |t| ≤ τ →
      ‖forwardLink (Ω t) e x h - L t‖ ≤ (Cq * h * Real.exp (2 * (K + τ * Ka) * h)) * t ^ 2 := by
    intro t ht
    have hc1 : Continuous (Ω t) := hΩc t ht
    have hc2 : Continuous (Ω 0 + t • α) := (hΩc 0 (by simp [hτ.le])).add (hαc.const_smul t)
    have hb1 : ∀ y, ‖Ω t y‖ ≤ K + τ * Ka := fun y => (hK t ht y).trans (by nlinarith)
    have hb2 : ∀ y, ‖(Ω 0 + t • α) y‖ ≤ K + τ * Ka := fun y =>
      (norm_line_le (hK 0 (by simp [hτ.le])) hKa t y).trans (by nlinarith [abs_nonneg t, ht])
    obtain ⟨U, hU0, hU, hUe⟩ := exists_forwardLink hc1 hb1 e x hh
    obtain ⟨V, hV0, hV, hVe⟩ := exists_forwardLink hc2 hb2 e x hh
    rw [hUe]
    show ‖U h - forwardLink (Ω 0 + t • α) e x h‖ ≤ _
    rw [hVe]
    have := norm_transport_end_sub_le (K := K + τ * Ka) (δ := Cq * t ^ 2) hh
      (fun s _ => hb1 _) (fun s _ => hb2 _)
      (fun s _ => by
        have := hq t ht (x + s • e)
        simpa [Pi.add_apply, Pi.smul_apply] using this) hU hV hU0 hV0
    refine this.trans (le_of_eq ?_)
    ring
  have hg : HasDerivAt (fun t => forwardLink (Ω t) e x h - L t) 0 0 :=
    hasDerivAt_zero_of_sq_le hτ (by simp [L]) hsq
  have := hL.add hg
  simp only [add_zero] at this
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp [L]

/-- **The forward edge expansion after one variation**:
`‖δP_{x+he←x}[a] + h a(x)‖ ≤ ((K + K_a)² e^{K + K_a} + Λ + Λ_a) h²`. -/
theorem norm_snd_forwardLink_add_le {A a : E → 𝔸} {K Ka Λ Λa : ℝ} (hΛ : 0 ≤ Λ) (hΛa : 0 ≤ Λa)
    (hA : ∀ y z, ‖A y - A z‖ ≤ Λ * ‖y - z‖) (ha : ∀ y z, ‖a y - a z‖ ≤ Λa * ‖y - z‖)
    (hK : ∀ y, ‖A y‖ ≤ K) (hKa : ∀ y, ‖a y‖ ≤ Ka) {e : E} (he : ‖e‖ ≤ 1) (x : E) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ‖(forwardLink (fun y => dual (A y) (a y)) e x h).snd + h • a x‖ ≤
      ((K + Ka) ^ 2 * Real.exp (K + Ka) + (Λ + Λa)) * h ^ 2 := by
  have hb := norm_forwardLink_sub_le (A := fun y => dual (A y) (a y)) (K := K + Ka)
    (Λ := Λ + Λa) (by positivity) (fun y z => by
      rw [dual_sub, norm_dual, add_mul]; exact add_le_add (hA y z) (ha y z))
    (fun y => by rw [norm_dual]; exact add_le_add (hK y) (hKa y)) he x hh hh1
  refine le_trans ?_ hb
  have e1 : (forwardLink (fun y => dual (A y) (a y)) e x h).snd + h • a x =
      (forwardLink (fun y => dual (A y) (a y)) e x h - (1 - h • dual (A x) (a x))).snd := by
    simp
  rw [e1]
  exact norm_snd_le _

/-! ### The covariant difference stencils -/

section Stencils

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]

/-- **The centred covariant difference** (`eq:spin-difference`):
`(2h)⁻¹(𝒰(x)Ψ(x+he) - 𝒰(x-he)⁻¹Ψ(x-he))`, `𝒰` the backward link of the connection `A`. -/
def centredDiff (A : E → F →L[ℝ] F) (Ψ : E → F) (e x : E) (h : ℝ) : F :=
  (2 * h)⁻¹ • (backwardLink A e x h (Ψ (x + h • e)) -
    Ring.inverse (backwardLink A e (x - h • e) h) (Ψ (x - h • e)))

/-- **The forward covariant difference** (the Higgs link of `eq:lattice-comparison`):
`h⁻¹(U(x)H(x+he) - H(x))`. -/
def fwdDiff (A : E → F →L[ℝ] F) (H : E → F) (e x : E) (h : ℝ) : F :=
  h⁻¹ • (backwardLink A e x h (H (x + h • e)) - H x)

theorem centredDiff_eq {A : E → F →L[ℝ] F} (hA : Continuous A) {K : ℝ} (hK : ∀ y, ‖A y‖ ≤ K)
    (Ψ : E → F) (e x : E) {h : ℝ} (hh : 0 ≤ h) :
    centredDiff A Ψ e x h = (2 * h)⁻¹ • (backwardLink A e x h (Ψ (x + h • e)) -
      forwardLink A e (x - h • e) h (Ψ (x - h • e))) := by
  rw [centredDiff, ring_inverse_backwardLink hA hK e (x - h • e) hh]

/-- **Derivative of the centred difference** along a (non-affine) family of connections `Ω_t`
with `Ω_t = Ω_0 + tα + O(t²)` and the line `Ψ + tη` of fields. -/
theorem hasDerivAt_centredDiff {Ω : ℝ → E → F →L[ℝ] F} {α : E → F →L[ℝ] F} {K Ka Cq τ : ℝ}
    (hτ : 0 < τ)
    (hΩc : ∀ t : ℝ, |t| ≤ τ → Continuous (Ω t)) (hαc : Continuous α)
    (hK : ∀ t : ℝ, |t| ≤ τ → ∀ y, ‖Ω t y‖ ≤ K) (hKa : ∀ y, ‖α y‖ ≤ Ka)
    (hq : ∀ t : ℝ, |t| ≤ τ → ∀ y, ‖Ω t y - (Ω 0 y + t • α y)‖ ≤ Cq * t ^ 2)
    (Ψ η : E → F) (e x : E) {h : ℝ} (hh : 0 ≤ h) :
    HasDerivAt (fun t => centredDiff (Ω t) (Ψ + t • η) e x h)
      ((2 * h)⁻¹ • ((backwardLink (fun y => dual (Ω 0 y) (α y)) e x h).snd (Ψ (x + h • e)) +
          backwardLink (Ω 0) e x h (η (x + h • e)) -
        ((forwardLink (fun y => dual (Ω 0 y) (α y)) e (x - h • e) h).snd (Ψ (x - h • e)) +
          forwardLink (Ω 0) e (x - h • e) h (η (x - h • e))))) 0 := by
  have hB := hasDerivAt_backwardLink_of_sq hτ hΩc hαc hK hKa hq e x hh
  have hF := hasDerivAt_forwardLink_of_sq hτ hΩc hαc hK hKa hq e (x - h • e) hh
  have hl1 : HasDerivAt (fun t : ℝ => (Ψ + t • η) (x + h • e)) (η (x + h • e)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η (x + h • e))).const_add (Ψ (x + h • e))
  have hl2 : HasDerivAt (fun t : ℝ => (Ψ + t • η) (x - h • e)) (η (x - h • e)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η (x - h • e))).const_add (Ψ (x - h • e))
  have h1 := hB.clm_apply hl1
  have h2 := hF.clm_apply hl2
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), centredDiff (Ω t) (Ψ + t • η) e x h =
      (2 * h)⁻¹ • (backwardLink (Ω t) e x h ((Ψ + t • η) (x + h • e)) -
        forwardLink (Ω t) e (x - h • e) h ((Ψ + t • η) (x - h • e))) := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hτ] with t ht
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
    exact centredDiff_eq (hΩc t ht) (hK t ht) _ e x hh
  refine ((h1.sub h2).const_smul (2 * h)⁻¹).congr_of_eventuallyEq hev |>.congr_deriv ?_
  simp only [zero_smul, add_zero]

/-- **The centred difference after one variation** (`δ∇^hΨ = αΨ + ∇η + O(h)`): with `Ω_0`
bounded by `K` and `Λ`-Lipschitz, `α` bounded by `K_a` and `Λ_a`-Lipschitz, `Ψ` bounded by `B`
and `L_Ψ`-Lipschitz, and `η` with `L_η`-Lipschitz derivative and bounded by `B_η`,
`‖δ - (α(x)Ψ(x) + η'(x)e + Ω_0(x)η(x))‖ ≤ C h`. -/
theorem norm_centredDiff_variation_sub_le {A a : E → F →L[ℝ] F} {Ψ η : E → F}
    {η' : E → E →L[ℝ] F} {K Ka Λ Λa B LΨ Lη Bη : ℝ} (hΛ : 0 ≤ Λ) (hΛa : 0 ≤ Λa)
    (hA : ∀ y z, ‖A y - A z‖ ≤ Λ * ‖y - z‖) (ha : ∀ y z, ‖a y - a z‖ ≤ Λa * ‖y - z‖)
    (hK : ∀ y, ‖A y‖ ≤ K) (hKa : ∀ y, ‖a y‖ ≤ Ka) (hB : ∀ y, ‖Ψ y‖ ≤ B)
    (hΨL : ∀ y z, ‖Ψ y - Ψ z‖ ≤ LΨ * ‖y - z‖) (hLΨ : 0 ≤ LΨ) (hη : ∀ y, HasFDerivAt η (η' y) y)
    (hηL : ∀ y z, ‖η' y - η' z‖ ≤ Lη * ‖y - z‖) (hLη : 0 ≤ Lη) (hBη : ∀ y, ‖η y‖ ≤ Bη)
    {e : E} (he : ‖e‖ ≤ 1) (x : E) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ‖(2 * h)⁻¹ • ((backwardLink (fun y => dual (A y) (a y)) e x h).snd (Ψ (x + h • e)) +
          backwardLink A e x h (η (x + h • e)) -
        ((forwardLink (fun y => dual (A y) (a y)) e (x - h • e) h).snd (Ψ (x - h • e)) +
          forwardLink A e (x - h • e) h (η (x - h • e)))) -
      (a x (Ψ x) + (η' x e + A x (η x)))‖ ≤
      (((K ^ 2 * Real.exp K + 2 * Λ) * Bη + Lη + K * Lη) +
        (((K + Ka) ^ 2 * Real.exp (K + Ka) + (Λ + Λa)) * B + Ka * LΨ + Λa * B)) * h := by
  have hc : Continuous A := continuous_of_norm_sub_le hΛ hA
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  have hKa0 : 0 ≤ Ka := (norm_nonneg _).trans (hKa x)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
  set δB := (backwardLink (fun y => dual (A y) (a y)) e x h).snd
  set δF := (forwardLink (fun y => dual (A y) (a y)) e (x - h • e) h).snd
  -- the `η`-part is the centred difference of `η`
  have hcd := norm_spinDifference_sub_covDeriv_le hΛ hA hK hη hηL hLη hBη he x hh hh1
  rw [ring_inverse_backwardLink hc hK e (x - h • e) hh.le] at hcd
  -- the variation part
  have hδB := norm_snd_backwardLink_sub_le hΛ hΛa hA ha hK hKa he x hh.le hh1
  have hδF := norm_snd_forwardLink_add_le hΛ hΛa hA ha hK hKa he (x - h • e) hh.le hh1
  set c := ((K + Ka) ^ 2 * Real.exp (K + Ka) + (Λ + Λa))
  have hc0 : 0 ≤ c := by positivity
  have hhe : ‖h • e‖ ≤ h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]; exact mul_le_of_le_one_right hh.le he
  have e1 : (2 * h)⁻¹ • (δB (Ψ (x + h • e)) + backwardLink A e x h (η (x + h • e)) -
        (δF (Ψ (x - h • e)) + forwardLink A e (x - h • e) h (η (x - h • e)))) -
      (a x (Ψ x) + (η' x e + A x (η x))) =
      ((2 * h)⁻¹ • (backwardLink A e x h (η (x + h • e)) -
          forwardLink A e (x - h • e) h (η (x - h • e))) - (η' x e + A x (η x))) +
      ((2 * h)⁻¹ • ((δB - h • a x) (Ψ (x + h • e)) - (δF + h • a (x - h • e)) (Ψ (x - h • e))) +
        ((1 / 2 : ℝ) • (a x (Ψ (x + h • e) - Ψ x)) +
          (1 / 2 : ℝ) • ((a (x - h • e) - a x) (Ψ (x - h • e)) + a x (Ψ (x - h • e) - Ψ x)))) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, map_sub, smul_sub, smul_add, smul_smul]
    have h2 : (2 * h)⁻¹ * h = 1 / 2 := by field_simp
    rw [h2]
    module
  rw [e1]
  refine (norm_add_le _ _).trans ?_
  have t2 : ‖(2 * h)⁻¹ • ((δB - h • a x) (Ψ (x + h • e)) - (δF + h • a (x - h • e))
      (Ψ (x - h • e)))‖ ≤ c * B * h := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * h)]
    have a1 : ‖(δB - h • a x) (Ψ (x + h • e))‖ ≤ c * h ^ 2 * B :=
      ((δB - h • a x).le_opNorm _).trans (mul_le_mul hδB (hB _) (norm_nonneg _) (by positivity))
    have a2 : ‖(δF + h • a (x - h • e)) (Ψ (x - h • e))‖ ≤ c * h ^ 2 * B :=
      ((δF + h • a (x - h • e)).le_opNorm _).trans
        (mul_le_mul hδF (hB _) (norm_nonneg _) (by positivity))
    calc (2 * h)⁻¹ * ‖(δB - h • a x) (Ψ (x + h • e)) - (δF + h • a (x - h • e)) (Ψ (x - h • e))‖
        ≤ (2 * h)⁻¹ * (c * h ^ 2 * B + c * h ^ 2 * B) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add a1 a2)) (by positivity)
      _ = c * B * h := by field_simp; ring
  have t3 : ‖(1 / 2 : ℝ) • (a x (Ψ (x + h • e) - Ψ x)) +
      (1 / 2 : ℝ) • ((a (x - h • e) - a x) (Ψ (x - h • e)) + a x (Ψ (x - h • e) - Ψ x))‖ ≤
      (Ka * LΨ + Λa * B) * h := by
    have b1 : ‖a x (Ψ (x + h • e) - Ψ x)‖ ≤ Ka * (LΨ * h) := by
      refine ((a x).le_opNorm _).trans (mul_le_mul (hKa x) ?_ (norm_nonneg _) hKa0)
      refine (hΨL _ _).trans ?_
      rw [add_sub_cancel_left]
      exact mul_le_mul_of_nonneg_left hhe hLΨ
    have b2 : ‖a x (Ψ (x - h • e) - Ψ x)‖ ≤ Ka * (LΨ * h) := by
      refine ((a x).le_opNorm _).trans (mul_le_mul (hKa x) ?_ (norm_nonneg _) hKa0)
      refine (hΨL _ _).trans ?_
      rw [sub_sub_cancel_left, norm_neg]
      exact mul_le_mul_of_nonneg_left hhe hLΨ
    have b3 : ‖(a (x - h • e) - a x) (Ψ (x - h • e))‖ ≤ Λa * h * B := by
      refine ((a (x - h • e) - a x).le_opNorm _).trans (mul_le_mul ?_ (hB _) (norm_nonneg _)
        (by positivity))
      refine (ha _ _).trans ?_
      rw [sub_sub_cancel_left, norm_neg]
      exact mul_le_mul_of_nonneg_left hhe hΛa
    calc _ ≤ ‖(1 / 2 : ℝ) • (a x (Ψ (x + h • e) - Ψ x))‖ +
          ‖(1 / 2 : ℝ) • ((a (x - h • e) - a x) (Ψ (x - h • e)) + a x (Ψ (x - h • e) - Ψ x))‖ :=
          norm_add_le _ _
      _ ≤ (1 / 2) * (Ka * (LΨ * h)) + (1 / 2) * (Λa * h * B + Ka * (LΨ * h)) := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          gcongr
          exact (norm_add_le _ _).trans (add_le_add b3 b2)
      _ ≤ (Ka * LΨ + Λa * B) * h := by nlinarith [mul_nonneg hΛa (mul_nonneg hh.le hB0)]
  calc _ ≤ ((K ^ 2 * Real.exp K + 2 * Λ) * Bη + Lη + K * Lη) * h +
        (c * B * h + (Ka * LΨ + Λa * B) * h) := add_le_add hcd ((norm_add_le _ _).trans
          (add_le_add t2 t3))
    _ = _ := by ring

/-- **Derivative of the forward difference** along `A + t a` and `H + t η`. -/
theorem hasDerivAt_fwdDiff {A a : E → F →L[ℝ] F} (hA : Continuous A) (ha : Continuous a)
    {K Ka : ℝ} (hK : ∀ y, ‖A y‖ ≤ K) (hKa : ∀ y, ‖a y‖ ≤ Ka) (H η : E → F) (e x : E) {h : ℝ}
    (hh : 0 ≤ h) :
    HasDerivAt (fun t : ℝ => fwdDiff (A + t • a) (H + t • η) e x h)
      (h⁻¹ • (backwardLink (fun y => dual (A y) (a y)) e x h).snd (H (x + h • e)) +
        fwdDiff A η e x h) 0 := by
  have hU := (hasDerivAt_backwardLink hA ha hK hKa e x hh).2
  have hl1 : HasDerivAt (fun t : ℝ => (H + t • η) (x + h • e)) (η (x + h • e)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η (x + h • e))).const_add (H (x + h • e))
  have hl2 : HasDerivAt (fun t : ℝ => (H + t • η) x) (η x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η x)).const_add (H x)
  have := ((hU.clm_apply hl1).sub hl2).const_smul h⁻¹
  refine this.congr_deriv ?_
  have h0 : backwardLink (A + (0 : ℝ) • a) e x h = backwardLink A e x h := by simp
  rw [h0, fwdDiff]
  simp only [smul_sub, smul_add, zero_smul, add_zero]
  abel

/-- **The forward difference after one variation** (`δK^h = aH + ∂η + Aη + O(h)`). -/
theorem norm_fwdDiff_variation_sub_le {A a : E → F →L[ℝ] F} {H η : E → F}
    {η' : E → E →L[ℝ] F} {K Ka Λ Λa B L₁ Lη Bη : ℝ} (hΛ : 0 ≤ Λ) (hΛa : 0 ≤ Λa)
    (hA : ∀ y z, ‖A y - A z‖ ≤ Λ * ‖y - z‖) (ha : ∀ y z, ‖a y - a z‖ ≤ Λa * ‖y - z‖)
    (hK : ∀ y, ‖A y‖ ≤ K) (hKa : ∀ y, ‖a y‖ ≤ Ka) (hB : ∀ y, ‖H y‖ ≤ B)
    (hη : ∀ y, HasFDerivAt η (η' y) y) (hηL : ∀ y z, ‖η' y - η' z‖ ≤ Lη * ‖y - z‖)
    (hLη : 0 ≤ Lη) (hBη : ∀ y, ‖η y‖ ≤ Bη) {e : E} (he : ‖e‖ ≤ 1) (x : E) {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) (hL : ‖H (x + h • e) - H x‖ ≤ L₁ * h) :
    ‖(h⁻¹ • (backwardLink (fun y => dual (A y) (a y)) e x h).snd (H (x + h • e)) +
        fwdDiff A η e x h) - (a x (H x) + (η' x e + A x (η x)))‖ ≤
      ((((K + Ka) ^ 2 * Real.exp (K + Ka) + (Λ + Λa)) * B + Ka * L₁) +
        ((K ^ 2 * Real.exp K + Λ) * Bη + Lη + K * (‖η' x e‖ + Lη))) * h := by
  have h1 := norm_higgsLink_gauge_variation_sub_le hΛ hΛa hA ha hK hKa hB he x hh hh1 hL
  have h2 := norm_higgsLink_sub_covDeriv_le hΛ hA hK hη hηL hLη hBη he x hh hh1
  have e1 : (h⁻¹ • (backwardLink (fun y => dual (A y) (a y)) e x h).snd (H (x + h • e)) +
        fwdDiff A η e x h) - (a x (H x) + (η' x e + A x (η x))) =
      (h⁻¹ • (backwardLink (fun y => dual (A y) (a y)) e x h).snd (H (x + h • e)) - a x (H x)) +
        (h⁻¹ • (backwardLink A e x h (η (x + h • e)) - η x) - (η' x e + A x (η x))) := by
    rw [fwdDiff]; abel
  rw [e1, add_mul]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

end Stencils

/-! ### The log plaquette after one gauge variation -/

section LogPlaquette

open ShiftedPlaquette Metric

variable {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [NormOneClass 𝔅] [CompleteSpace 𝔅]

/-- Derivatives of powers in a normed algebra: `‖D(x^m)(z)[w]‖ ≤ m ‖z‖^{m-1} ‖w‖`. -/
theorem exists_hasFDerivAt_pow (m : ℕ) (z : 𝔅) : ∃ D : 𝔅 →L[ℝ] 𝔅,
    HasFDerivAt (fun x : 𝔅 => x ^ m) D z ∧ ∀ w, ‖D w‖ ≤ m * ‖z‖ ^ (m - 1) * ‖w‖ := by
  induction m with
  | zero => exact ⟨0, by simpa using hasFDerivAt_const (1 : 𝔅) z, fun w => by simp⟩
  | succ m ih =>
      obtain ⟨D, hD, hb⟩ := ih
      have h := (hasFDerivAt_id z).mul' hD
      refine ⟨_, h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_), fun w => ?_⟩
      · show x ^ (m + 1) = x * x ^ m
        rw [pow_succ']
      · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply, smul_eq_mul, id]
        rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        refine (norm_add_le _ _).trans ?_
        have h1 : ‖z * D w‖ ≤ ‖z‖ * (m * ‖z‖ ^ (m - 1) * ‖w‖) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hb w) (norm_nonneg _))
        have h2 : ‖w * z ^ m‖ ≤ ‖w‖ * ‖z‖ ^ m :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_pow_le _ _) (norm_nonneg _))
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          have hDw : D w = 0 := norm_le_zero_iff.mp (by simpa using hb w)
          simp [hDw]
        · have e : ‖z‖ * ‖z‖ ^ (m - 1) = ‖z‖ ^ m := by
            rw [← pow_succ']; congr 1; omega
          have h1' : ‖z * D w‖ ≤ m * ‖z‖ ^ m * ‖w‖ := h1.trans (le_of_eq (by rw [← e]; ring))
          simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
          nlinarith [h1', h2]

theorem norm_fderiv_pow_apply_le (m : ℕ) (z w : 𝔅) :
    ‖fderiv ℝ (fun x : 𝔅 => x ^ m) z w‖ ≤ m * ‖z‖ ^ (m - 1) * ‖w‖ := by
  obtain ⟨D, hD, hb⟩ := exists_hasFDerivAt_pow m z
  rw [hD.fderiv]; exact hb w

theorem norm_fderiv_pow_le (m : ℕ) (z : 𝔅) :
    ‖fderiv ℝ (fun x : 𝔅 => x ^ m) z‖ ≤ m * ‖z‖ ^ (m - 1) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => norm_fderiv_pow_apply_le m z w

theorem abs_logQuotientCoeff_le (n : ℕ) : |logQuotientCoeff n| = 1 / ((n : ℝ) + 1) := by
  have := norm_logQuotientCoeff n
  rwa [Real.norm_eq_abs] at this

/-- **The derivative of the series logarithm is the termwise derivative.** -/
theorem hasFDerivAt_logOneAdd {z : 𝔅} (hz : ‖z‖ < 1) :
    HasFDerivAt logOneAdd
      (∑' n : ℕ, logQuotientCoeff n • fderiv ℝ (fun x : 𝔅 => x ^ (n + 1)) z) z := by
  set q := (1 + ‖z‖) / 2
  have hq1 : q < 1 := by simp only [q]; linarith
  have hzq : ‖z‖ < q := by simp only [q]; linarith
  have hq0 : 0 ≤ q := by simp only [q]; linarith [norm_nonneg z]
  have hu : Summable fun n : ℕ => q ^ n := summable_geometric_of_lt_one hq0 hq1
  have hdiff : ∀ (n : ℕ) (x : 𝔅), x ∈ ball (0 : 𝔅) q →
      HasFDerivAt (fun x : 𝔅 => logQuotientCoeff n • x ^ (n + 1))
        (logQuotientCoeff n • fderiv ℝ (fun x : 𝔅 => x ^ (n + 1)) x) x := by
    intro n x _
    obtain ⟨D, hD, -⟩ := exists_hasFDerivAt_pow (n + 1) x
    rw [hD.fderiv]
    exact hD.const_smul (logQuotientCoeff n)
  have hbd : ∀ (n : ℕ) (x : 𝔅), x ∈ ball (0 : 𝔅) q →
      ‖logQuotientCoeff n • fderiv ℝ (fun x : 𝔅 => x ^ (n + 1)) x‖ ≤ q ^ n := by
    intro n x hx
    rw [mem_ball_zero_iff] at hx
    rw [norm_smul, Real.norm_eq_abs, abs_logQuotientCoeff_le]
    have := norm_fderiv_pow_le (n + 1) x
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at this
    calc 1 / ((n : ℝ) + 1) * ‖fderiv ℝ (fun x : 𝔅 => x ^ (n + 1)) x‖
        ≤ 1 / ((n : ℝ) + 1) * (((n : ℝ) + 1) * ‖x‖ ^ n) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ‖x‖ ^ n := by field_simp
      _ ≤ q ^ n := pow_le_pow_left₀ (norm_nonneg _) hx.le n
  have hT := hasFDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball (0 : 𝔅) q).isPreconnected
    hdiff hbd (mem_ball_self (by linarith [norm_nonneg z]) : (0 : 𝔅) ∈ ball 0 q)
    (by simp) (mem_ball_zero_iff.mpr hzq)
  refine hT.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzq)] with y hy
  rw [mem_ball_zero_iff] at hy
  exact (SeriesLogChart.hasSum_logOneAdd (by linarith)).tsum_eq.symm

/-- **Derivative of the series logarithm near `0`**: `‖D log(1+z)[w] - w‖ ≤ 2 ‖z‖ ‖w‖` for
`‖z‖ ≤ 1/2`. -/
theorem norm_fderiv_logOneAdd_sub_le {z : 𝔅} (hz : ‖z‖ ≤ 1 / 2) (w : 𝔅) :
    ‖fderiv ℝ logOneAdd z w - w‖ ≤ 2 * ‖z‖ * ‖w‖ := by
  have hz1 : ‖z‖ < 1 := by linarith
  set r := ‖z‖
  have hr0 : 0 ≤ r := norm_nonneg z
  -- the termwise derivative applied to `w`
  set g : ℕ → 𝔅 := fun n => logQuotientCoeff n • fderiv ℝ (fun x : 𝔅 => x ^ (n + 1)) z w
  have hgb : ∀ n, ‖g n‖ ≤ r ^ n * ‖w‖ := by
    intro n
    simp only [g]
    rw [norm_smul, Real.norm_eq_abs, abs_logQuotientCoeff_le]
    have := norm_fderiv_pow_apply_le (n + 1) z w
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at this
    calc 1 / ((n : ℝ) + 1) * ‖fderiv ℝ (fun x : 𝔅 => x ^ (n + 1)) z w‖
        ≤ 1 / ((n : ℝ) + 1) * (((n : ℝ) + 1) * r ^ n * ‖w‖) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = r ^ n * ‖w‖ := by field_simp
  have hsumL : Summable fun n : ℕ => logQuotientCoeff n • fderiv ℝ (fun x : 𝔅 => x ^ (n + 1)) z := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one hr0 hz1) fun n => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_logQuotientCoeff_le]
    have := norm_fderiv_pow_le (n + 1) z
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at this
    calc 1 / ((n : ℝ) + 1) * ‖fderiv ℝ (fun x : 𝔅 => x ^ (n + 1)) z‖
        ≤ 1 / ((n : ℝ) + 1) * (((n : ℝ) + 1) * r ^ n) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = r ^ n := by field_simp
  have happ : fderiv ℝ logOneAdd z w = ∑' n, g n := by
    rw [(hasFDerivAt_logOneAdd hz1).fderiv]
    exact (ContinuousLinearMap.apply ℝ 𝔅 w).map_tsum hsumL
  have hgs : Summable g :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hz1).mul_right ‖w‖) hgb
  have hg0 : g 0 = w := by
    simp only [g, zero_add, pow_one]
    have hc : logQuotientCoeff 0 = 1 := by simp [logQuotientCoeff]
    have : fderiv ℝ (fun x : 𝔅 => x) z = ContinuousLinearMap.id ℝ 𝔅 := fderiv_id'
    rw [hc, this, one_smul, ContinuousLinearMap.id_apply]
  rw [happ, hgs.tsum_eq_zero_add, hg0, add_sub_cancel_left]
  have hb : ∀ n, ‖g (n + 1)‖ ≤ (r * ‖w‖) * r ^ n := fun n =>
    (hgb (n + 1)).trans (le_of_eq (by ring))
  have hgeo : HasSum (fun n : ℕ => (r * ‖w‖) * r ^ n) ((r * ‖w‖) * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hz1).mul_left _
  refine (tsum_of_norm_bounded hgeo hb).trans ?_
  have : (1 - r)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc r * ‖w‖ * (1 - r)⁻¹ ≤ r * ‖w‖ * 2 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * r * ‖w‖ := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The logarithmic field strength after one gauge variation** (proof of
`prop:mesh-consistency`): for connection components `A_μ, A_ν` and variations `a_μ, a_ν` with the
bounds of `norm_snd_linkPlaquette_sub_le`, and `h` in the identity chart, the field strength
`F^h = h⁻² log U_{μν}` along `A + t a` is differentiable at `t = 0` with derivative
`h⁻² D log(U_{μν} - 1)[δU_{μν}]`, which differs from the curvature variation
`dF = ∂_μa_ν - ∂_νa_μ + [A_μ,a_ν] + [a_μ,A_ν]` by `O(h)`. -/
theorem logPlaquette_variation {Aμ Aν aμ aν : E → 𝔅} {Aμ' Aν' aμ' aν' : E → E →L[ℝ] 𝔅}
    {K Ka D Da L La : ℝ} (hAμ : ∀ y, HasFDerivAt Aμ (Aμ' y) y)
    (hAν : ∀ y, HasFDerivAt Aν (Aν' y) y) (haμ : ∀ y, HasFDerivAt aμ (aμ' y) y)
    (haν : ∀ y, HasFDerivAt aν (aν' y) y)
    (hKμ : ∀ y, ‖Aμ y‖ ≤ K) (hKν : ∀ y, ‖Aν y‖ ≤ K) (hKaμ : ∀ y, ‖aμ y‖ ≤ Ka)
    (hKaν : ∀ y, ‖aν y‖ ≤ Ka) (hDμ : ∀ y, ‖Aμ' y‖ ≤ D) (hDν : ∀ y, ‖Aν' y‖ ≤ D)
    (hDaμ : ∀ y, ‖aμ' y‖ ≤ Da) (hDaν : ∀ y, ‖aν' y‖ ≤ Da)
    (hLμ : ∀ y z, ‖Aμ' y - Aμ' z‖ ≤ L * ‖y - z‖) (hLν : ∀ y z, ‖Aν' y - Aν' z‖ ≤ L * ‖y - z‖)
    (hLaμ : ∀ y z, ‖aμ' y - aμ' z‖ ≤ La * ‖y - z‖) (hLaν : ∀ y z, ‖aν' y - aν' z‖ ≤ La * ‖y - z‖)
    {eμ eν : E} (heμ : ‖eμ‖ ≤ 1) (heν : ‖eν‖ ≤ 1) (hL : 0 ≤ L) (hLa : 0 ≤ La) (x : E) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hsmall : (plaquetteConst (max K D) K (4 * L) + (2 * D + 2 * K ^ 2)) * h ^ 2 ≤ 1 / 8) :
    HasDerivAt (fun t : ℝ => (h ^ 2)⁻¹ •
        logOneAdd (linkPlaquette (Aμ + t • aμ) (Aν + t • aν) eμ eν x h - 1))
      ((h ^ 2)⁻¹ • fderiv ℝ logOneAdd (linkPlaquette Aμ Aν eμ eν x h - 1)
        (linkPlaquette (fun y => dual (Aμ y) (aμ y)) (fun y => dual (Aν y) (aν y)) eμ eν x h).snd)
      0 ∧
    ‖(h ^ 2)⁻¹ • fderiv ℝ logOneAdd (linkPlaquette Aμ Aν eμ eν x h - 1)
        (linkPlaquette (fun y => dual (Aμ y) (aμ y)) (fun y => dual (Aν y) (aν y)) eμ eν x h).snd -
      (aν' x eμ - aμ' x eν + (Aμ x * aν x + aμ x * Aν x - Aν x * aμ x - aν x * Aμ x))‖ ≤
      (4 * (plaquetteConst (max K D) K (4 * L) + (2 * D + 2 * K ^ 2)) *
          ((2 * Da + 4 * K * Ka) + plaquetteConst (max (K + Ka) (D + Da)) (K + Ka) (4 * (L + La))) +
        plaquetteConst (max (K + Ka) (D + Da)) (K + Ka) (4 * (L + La))) * h := by
  have hcμ : Continuous Aμ := continuous_iff_continuousAt.2 fun y => (hAμ y).continuousAt
  have hcν : Continuous Aν := continuous_iff_continuousAt.2 fun y => (hAν y).continuousAt
  have hcaμ : Continuous aμ := continuous_iff_continuousAt.2 fun y => (haμ y).continuousAt
  have hcaν : Continuous aν := continuous_iff_continuousAt.2 fun y => (haν y).continuousAt
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hKμ x)
  have hKa0 : 0 ≤ Ka := (norm_nonneg _).trans (hKaμ x)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hDμ x)
  have hDa0 : 0 ≤ Da := (norm_nonneg _).trans (hDaμ x)
  set P := linkPlaquette Aμ Aν eμ eν x h
  set dP := (linkPlaquette (fun y => dual (Aμ y) (aμ y)) (fun y => dual (Aν y) (aν y))
    eμ eν x h).snd
  set Fc := Aν' x eμ - Aμ' x eν + (Aμ x * Aν x - Aν x * Aμ x)
  set dF := aν' x eμ - aμ' x eν + (Aμ x * aν x + aμ x * Aν x - Aν x * aμ x - aν x * Aμ x)
  set Cp := plaquetteConst (max K D) K (4 * L)
  set Cd := plaquetteConst (max (K + Ka) (D + Da)) (K + Ka) (4 * (L + La))
  have hP : ‖P - (1 + h ^ 2 • Fc)‖ ≤ Cp * h ^ 3 :=
    norm_linkPlaquette_sub_curvature_le hAμ hAν hKμ hKν hDμ hDν hLμ hLν heμ heν hL x hh.le hh1
  have hdP := norm_snd_linkPlaquette_sub_le hAμ hAν haμ haν hKμ hKν hKaμ hKaν hDμ hDν hDaμ hDaν
    hLμ hLν hLaμ hLaν heμ heν hL hLa x hh.le hh1
  have hCp : 0 ≤ Cp := by
    have : 0 ≤ Cp * h ^ 3 := (norm_nonneg _).trans hP
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hCd : 0 ≤ Cd := by
    have : 0 ≤ Cd * h ^ 3 := (norm_nonneg _).trans hdP
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hN : ∀ {T : E →L[ℝ] 𝔅} {e : E} {c : ℝ}, ‖T‖ ≤ c → ‖e‖ ≤ 1 → ‖T e‖ ≤ c :=
    fun {T} {e} {c} hT he =>
      (T.le_opNorm e).trans ((mul_le_mul hT he (norm_nonneg _) ((norm_nonneg _).trans hT)).trans
        (by rw [mul_one]))
  have m : ∀ (p q : 𝔅) (cp cq : ℝ), ‖p‖ ≤ cp → ‖q‖ ≤ cq → ‖p * q‖ ≤ cp * cq :=
    fun p q cp cq hp hq =>
      (norm_mul_le _ _).trans (mul_le_mul hp hq (norm_nonneg _) ((norm_nonneg _).trans hp))
  have hFc : ‖Fc‖ ≤ 2 * D + 2 * K ^ 2 := by
    have a1 := hN (hDν x) heμ
    have a2 := hN (hDμ x) heν
    have b1 := m _ _ _ _ (hKμ x) (hKν x)
    have b2 := m _ _ _ _ (hKν x) (hKμ x)
    calc ‖Fc‖ ≤ ‖Aν' x eμ‖ + ‖Aμ' x eν‖ + (‖Aμ x * Aν x‖ + ‖Aν x * Aμ x‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))
      _ ≤ 2 * D + 2 * K ^ 2 := by nlinarith
  have hdF : ‖dF‖ ≤ 2 * Da + 4 * K * Ka := by
    have a1 := hN (hDaν x) heμ
    have a2 := hN (hDaμ x) heν
    have b1 := m _ _ _ _ (hKμ x) (hKaν x)
    have b2 := m _ _ _ _ (hKaμ x) (hKν x)
    have b3 := m _ _ _ _ (hKν x) (hKaμ x)
    have b4 := m _ _ _ _ (hKaν x) (hKμ x)
    calc ‖dF‖ ≤ ‖aν' x eμ‖ + ‖aμ' x eν‖ + (‖Aμ x * aν x‖ + ‖aμ x * Aν x‖ + ‖Aν x * aμ x‖ +
          ‖aν x * Aμ x‖) := by
          refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
            (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ 2 * Da + 4 * K * Ka := by nlinarith
  -- `‖P - 1‖ ≤ (Cp + cFc) h²`
  have hP1 : ‖P - 1‖ ≤ (Cp + (2 * D + 2 * K ^ 2)) * h ^ 2 := by
    have e : P - 1 = (P - (1 + h ^ 2 • Fc)) + h ^ 2 • Fc := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have : h ^ 3 ≤ h ^ 2 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left this hCp, hP, mul_le_mul_of_nonneg_left hFc (sq_nonneg h)]
  have hdPb : ‖dP‖ ≤ ((2 * Da + 4 * K * Ka) + Cd) * h ^ 2 := by
    have e : dP = (dP - h ^ 2 • dF) + h ^ 2 • dF := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have : h ^ 3 ≤ h ^ 2 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left this hCd, hdP, mul_le_mul_of_nonneg_left hdF (sq_nonneg h)]
  have hP18 : ‖P - 1‖ ≤ 1 / 8 := hP1.trans hsmall
  refine ⟨?_, ?_⟩
  · -- differentiability
    have hlog : DifferentiableAt ℝ logOneAdd (P - 1) :=
      (SeriesLogChart.analyticAt_logOneAdd (by linarith)).differentiableAt
    have hpl := hasDerivAt_linkPlaquette hcμ hcν hcaμ hcaν hKμ hKν hKaμ hKaν eμ eν x hh.le
    have hz : linkPlaquette (Aμ + (0 : ℝ) • aμ) (Aν + (0 : ℝ) • aν) eμ eν x h = P := by
      simp [P]
    have hpl' : HasDerivAt (fun t : ℝ => linkPlaquette (Aμ + t • aμ) (Aν + t • aν) eμ eν x h - 1)
        dP 0 := hpl.sub_const 1
    have hcomp := hlog.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hpl' (by rw [hz])
    exact hcomp.const_smul (h ^ 2)⁻¹
  · have hL1 : ‖fderiv ℝ logOneAdd (P - 1) dP - dP‖ ≤ 4 * ‖P - 1‖ * ‖dP‖ :=
      (norm_fderiv_logOneAdd_sub_le (hP18.trans (by norm_num)) dP).trans
        (by nlinarith [norm_nonneg (P - 1), norm_nonneg dP])
    have e : (h ^ 2)⁻¹ • fderiv ℝ logOneAdd (P - 1) dP - dF =
        (h ^ 2)⁻¹ • (fderiv ℝ logOneAdd (P - 1) dP - dP) + (h ^ 2)⁻¹ • (dP - h ^ 2 • dF) := by
      rw [smul_sub (h ^ 2)⁻¹ dP, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
      rw [smul_sub]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
    have t1 : (h ^ 2)⁻¹ * ‖fderiv ℝ logOneAdd (P - 1) dP - dP‖ ≤
        4 * (Cp + (2 * D + 2 * K ^ 2)) * ((2 * Da + 4 * K * Ka) + Cd) * h ^ 2 := by
      calc (h ^ 2)⁻¹ * ‖fderiv ℝ logOneAdd (P - 1) dP - dP‖ ≤ (h ^ 2)⁻¹ * (4 * ‖P - 1‖ * ‖dP‖) :=
            mul_le_mul_of_nonneg_left hL1 (by positivity)
        _ ≤ (h ^ 2)⁻¹ * (4 * ((Cp + (2 * D + 2 * K ^ 2)) * h ^ 2) *
              (((2 * Da + 4 * K * Ka) + Cd) * h ^ 2)) := by
            gcongr
        _ = 4 * (Cp + (2 * D + 2 * K ^ 2)) * ((2 * Da + 4 * K * Ka) + Cd) * h ^ 2 := by
            field_simp
    have t2 : (h ^ 2)⁻¹ * ‖dP - h ^ 2 • dF‖ ≤ Cd * h := by
      calc (h ^ 2)⁻¹ * ‖dP - h ^ 2 • dF‖ ≤ (h ^ 2)⁻¹ * (Cd * h ^ 3) :=
            mul_le_mul_of_nonneg_left hdP (by positivity)
        _ = Cd * h := by field_simp
    have hh2' : h ^ 2 ≤ h := by nlinarith
    have hA0 : 0 ≤ 4 * (Cp + (2 * D + 2 * K ^ 2)) * ((2 * Da + 4 * K * Ka) + Cd) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hh2' hA0]

end LogPlaquette

end RenewalGeometry.TransportStencilVariation
