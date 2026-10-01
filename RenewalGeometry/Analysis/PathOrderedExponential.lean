/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Path-ordered exponentials (product integrals) of a connection along a segment
(infrastructure for `thm:supp-finite-defects`, `eq:supp-exact-link`; emergent-spacetime
manuscript)

Let `𝔸` be a complete normed `ℝ`-algebra with `‖1‖ = 1` (e.g. real matrices with an operator
norm).  For a connection coefficient `ω : ℝ → 𝔸`, continuous on `[a,b]`, the exact parallel
transport (path-ordered exponential) `U(t) = 𝒫 exp(−∫_a^t ω)` is the solution of
`U' = −ω U`, `U(a) = U₀` (`IsTransport`).

* `exists_transport`: existence on segments with `K (b − a) ≤ 1/2`, `‖ω‖ ≤ K` (Picard–Lindelöf;
  this covers the exact links of a mesh of size `h ≤ 1/(2K)`).
* `transport_unique`: uniqueness (Grönwall).
* `IsTransport.mul_const`, `transport_concat`: right multiplication and **multiplicativity**
  `U_{[a,c]}(t) = U_{[b,c]}(t) U_{[a,c]}(b)` on `[b,c]` (the composition law of exact links).
* `norm_transport_le`, `norm_transport_sub_initial_le`, `norm_transport_sub_le_lipschitz`:
  `‖U(t)‖ ≤ ‖U₀‖ e^{K(t−a)}`, `‖U(t) − U₀‖ ≤ ‖U₀‖ (e^{K(t−a)} − 1)`, and the Lipschitz bound
  `‖U(t) − U(s)‖ ≤ K ‖U₀‖ e^{K(b−a)} |t − s|`.
* `norm_transport_sub_transport_le`: Lipschitz dependence on the connection,
  `‖U(t) − Ũ(t)‖ ≤ gronwallBound 0 K (δ ‖U₀‖ e^{K(b−a)}) (t − a)` when `‖ω − ω̃‖ ≤ δ`.
* `transport_integral_eq`: the integral equation `U(t) = U₀ − ∫_a^t ω U`.
* `norm_transport_sub_dyson_two_le`: **second-order consistency** (Dyson expansion): for
  `U₀ = 1`, `‖U(t) − (1 − ∫_a^t ω + ∫_a^t ω(s) ∫_a^s ω)‖ ≤ K³ (t − a)³ e^{K(t−a)}`.
* `isTransport_const_exp`, `transport_const_eq_exp`: for a constant connection `ω ≡ X` the exact
  link is `exp(−(t−a)X)`; `norm_exp_neg_smul_sub_quadratic_le`: the resulting second-order
  Taylor bound `‖exp(−hX) − (1 − hX + h²X²/2)‖ ≤ ‖X‖³h³e^{‖X‖h}`.

Scope: existence is proved on segments of length `≤ 1/(2K)` (enough for the links of a mesh of
size `h → 0`); gluing to arbitrary length, the midpoint-exponential comparison
`U(a+h) = exp(−h ω(a+h/2)) + O(h³)` and the nonabelian Stokes/BCH expansion of face holonomies
are not formalised here.
-/

namespace RenewalGeometry.PathOrderedExp

open Set intervalIntegral MeasureTheory
open scoped NNReal Topology Interval

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- `U` is a parallel transport of the connection `ω` along `[a,b]`: `U' = −ω U` within
`[a,b]` (the initial value `U a` is left free). -/
def IsTransport (ω : ℝ → 𝔸) (a b : ℝ) (U : ℝ → 𝔸) : Prop :=
  ∀ t ∈ Icc a b, HasDerivWithinAt U (-(ω t * U t)) (Icc a b) t

theorem IsTransport.continuousOn {ω : ℝ → 𝔸} {a b : ℝ} {U : ℝ → 𝔸} (hU : IsTransport ω a b U) :
    ContinuousOn U (Icc a b) := fun t ht => (hU t ht).continuousWithinAt

theorem IsTransport.hasDerivWithinAt_Ici {ω : ℝ → 𝔸} {a b : ℝ} {U : ℝ → 𝔸}
    (hU : IsTransport ω a b U) {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt U (-(ω t * U t)) (Ici t) t := by
  have hmem : Icc a b ∈ 𝓝[≥] t :=
    Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  exact (hU t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin hmem

theorem IsTransport.mono {ω : ℝ → 𝔸} {a b a' b' : ℝ} {U : ℝ → 𝔸} (hU : IsTransport ω a b U)
    (ha : a ≤ a') (hb : b' ≤ b) : IsTransport ω a' b' U := fun t ht =>
  (hU t ⟨ha.trans ht.1, ht.2.trans hb⟩).mono (Icc_subset_Icc ha hb)

/-- Right multiplication by a constant preserves transports. -/
theorem IsTransport.mul_const {ω : ℝ → 𝔸} {a b : ℝ} {U : ℝ → 𝔸} (hU : IsTransport ω a b U)
    (C : 𝔸) : IsTransport ω a b (fun t => U t * C) := fun t ht => by
  have := (hU t ht).mul_const C
  rwa [neg_mul, mul_assoc] at this

/-- The linear field `x ↦ −ω x` is `‖ω‖`-Lipschitz. -/
theorem dist_neg_mul_le (w x y : 𝔸) {K : ℝ} (hw : ‖w‖ ≤ K) :
    dist (-(w * x)) (-(w * y)) ≤ K * dist x y := by
  have h : -(w * x) - -(w * y) = w * (y - x) := by noncomm_ring
  rw [dist_eq_norm, dist_eq_norm, h, norm_sub_rev x y]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hw (norm_nonneg _))

/-! ### Existence and uniqueness -/

/-- **Existence of the exact link** on a short segment: if `ω` is continuous on `[a,b]`,
`‖ω‖ ≤ K` there and `K (b − a) ≤ 1/2`, then for every initial value `U₀` there is a transport
`U` with `U a = U₀`. -/
theorem exists_transport {ω : ℝ → 𝔸} {a b K : ℝ} (hab : a ≤ b)
    (hω : ContinuousOn ω (Icc a b)) (hK : ∀ t ∈ Icc a b, ‖ω t‖ ≤ K)
    (hshort : K * (b - a) ≤ 1 / 2) (U₀ : 𝔸) :
    ∃ U : ℝ → 𝔸, U a = U₀ ∧ IsTransport ω a b U := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK a (left_mem_Icc.2 hab))
  set ρ : ℝ≥0 := (‖U₀‖ + 1).toNNReal
  set L : ℝ≥0 := (K * (2 * ‖U₀‖ + 1)).toNNReal
  set Kn : ℝ≥0 := K.toNNReal
  have hρ : (ρ : ℝ) = ‖U₀‖ + 1 := Real.coe_toNNReal _ (by positivity)
  have hL : (L : ℝ) = K * (2 * ‖U₀‖ + 1) := Real.coe_toNNReal _ (by positivity)
  have hKn : (Kn : ℝ) = K := Real.coe_toNNReal _ hK0
  let t₀ : Icc a b := ⟨a, left_mem_Icc.2 hab⟩
  have hPL : IsPicardLindelof (fun t x => -(ω t * x)) t₀ U₀ ρ 0 L Kn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
      rw [hKn]
      exact dist_neg_mul_le _ _ _ (hK t ht)
    · intro x _
      exact (hω.mul continuousOn_const).neg
    · intro t ht x hx
      rw [norm_neg]
      have hx' : ‖x‖ ≤ 2 * ‖U₀‖ + 1 := by
        have := norm_le_of_mem_closedBall hx
        rw [hρ] at this
        linarith
      rw [hL]
      calc ‖ω t * x‖ ≤ ‖ω t‖ * ‖x‖ := norm_mul_le _ _
        _ ≤ K * (2 * ‖U₀‖ + 1) := mul_le_mul (hK t ht) hx' (norm_nonneg _) hK0
    · rw [hL, hρ, NNReal.coe_zero, sub_zero]
      simp only [t₀, sub_self]
      rw [max_eq_left (by linarith)]
      nlinarith [norm_nonneg U₀]
  obtain ⟨U, hU0, hU⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (Metric.mem_closedBall_self le_rfl)
  exact ⟨U, hU0, fun t ht => hU t ht⟩

/-- **Uniqueness** of transports with a common initial value. -/
theorem transport_unique {ω : ℝ → 𝔸} {a b K : ℝ} (hK : ∀ t ∈ Icc a b, ‖ω t‖ ≤ K)
    {U V : ℝ → 𝔸} (hU : IsTransport ω a b U) (hV : IsTransport ω a b V) (h : U a = V a) :
    EqOn U V (Icc a b) := by
  have hK0 : ∀ t ∈ Ico a b, 0 ≤ K := fun t ht =>
    le_trans (norm_nonneg _) (hK t (Ico_subset_Icc_self ht))
  by_cases hab : a < b
  · have hK0' : 0 ≤ K := hK0 a ⟨le_rfl, hab⟩
    refine ODE_solution_unique_of_mem_Icc_right (v := fun t x => -(ω t * x))
      (s := fun _ => univ) (K := K.toNNReal) ?_ hU.continuousOn
      (fun t ht => hU.hasDerivWithinAt_Ici ht) (fun _ _ => mem_univ _) hV.continuousOn
      (fun t ht => hV.hasDerivWithinAt_Ici ht) (fun _ _ => mem_univ _) h
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
    rw [Real.coe_toNNReal _ hK0']
    exact dist_neg_mul_le _ _ _ (hK t (Ico_subset_Icc_self ht))
  · intro t ht
    have : t = a := le_antisymm (ht.2.trans (not_lt.1 hab)) ht.1
    rw [this, h]

/-- **Multiplicativity of exact links**: if `U` is the transport on `[a,c]` and `V` the
transport on `[b,c]` with `V b = 1`, then `U t = V t · U b` on `[b,c]`; in particular
`U_{a→c} = U_{b→c} U_{a→b}`. -/
theorem transport_concat {ω : ℝ → 𝔸} {a b c K : ℝ} (hab : a ≤ b) (_hbc : b ≤ c)
    (hK : ∀ t ∈ Icc a c, ‖ω t‖ ≤ K) {U V : ℝ → 𝔸} (hU : IsTransport ω a c U)
    (hV : IsTransport ω b c V) (hV1 : V b = 1) :
    ∀ t ∈ Icc b c, U t = V t * U b := by
  have hU' : IsTransport ω b c U := hU.mono hab le_rfl
  have hW : IsTransport ω b c (fun t => V t * U b) := hV.mul_const (U b)
  exact transport_unique (fun t ht => hK t ⟨hab.trans ht.1, ht.2⟩) hU' hW
    (by simp [hV1])

/-! ### Grönwall bounds -/

/-- `‖U(t)‖ ≤ ‖U(a)‖ e^{K(t−a)}`. -/
theorem norm_transport_le {ω : ℝ → 𝔸} {a b K : ℝ} (hK : ∀ t ∈ Icc a b, ‖ω t‖ ≤ K)
    {U : ℝ → 𝔸} (hU : IsTransport ω a b U) :
    ∀ t ∈ Icc a b, ‖U t‖ ≤ ‖U a‖ * Real.exp (K * (t - a)) := by
  intro t ht
  have := norm_le_gronwallBound_of_norm_deriv_right_le (f := U) (δ := ‖U a‖) (K := K) (ε := 0)
    hU.continuousOn (fun s hs => hU.hasDerivWithinAt_Ici hs) le_rfl
    (fun s hs => by
      rw [norm_neg, add_zero]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (hK s (Ico_subset_Icc_self hs)) (norm_nonneg _))) t ht
  rwa [gronwallBound_ε0] at this

/-- `‖U(t) − U(a)‖ ≤ ‖U(a)‖ (e^{K(t−a)} − 1)`. -/
theorem norm_transport_sub_initial_le {ω : ℝ → 𝔸} {a b K : ℝ}
    (hK : ∀ t ∈ Icc a b, ‖ω t‖ ≤ K) {U : ℝ → 𝔸} (hU : IsTransport ω a b U) :
    ∀ t ∈ Icc a b, ‖U t - U a‖ ≤ ‖U a‖ * (Real.exp (K * (t - a)) - 1) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK a (left_mem_Icc.2 hab))
  have hD : ∀ s ∈ Ico a b, HasDerivWithinAt (fun s => U s - U a) (-(ω s * U s)) (Ici s) s :=
    fun s hs => (hU.hasDerivWithinAt_Ici hs).sub_const (U a)
  have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => U s - U a) (δ := 0)
    (K := K) (ε := K * ‖U a‖) (hU.continuousOn.sub continuousOn_const) hD (by simp)
    (fun s hs => by
      have hs' := hK s (Ico_subset_Icc_self hs)
      rw [norm_neg]
      calc ‖ω s * U s‖ ≤ ‖ω s‖ * ‖U s‖ := norm_mul_le _ _
        _ ≤ K * ‖U s‖ := mul_le_mul_of_nonneg_right hs' (norm_nonneg _)
        _ = K * ‖(U s - U a) + U a‖ := by rw [sub_add_cancel]
        _ ≤ K * (‖U s - U a‖ + ‖U a‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hK0
        _ = K * ‖U s - U a‖ + K * ‖U a‖ := by ring) t ht
  refine this.trans (le_of_eq ?_)
  rcases eq_or_lt_of_le hK0 with hK0 | hKpos
  · subst hK0; simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hKpos.ne']
    field_simp
    ring

/-- **Lipschitz bound in time**: `‖U(t) − U(s)‖ ≤ K ‖U(a)‖ e^{K(b−a)} |t − s|` on `[a,b]`. -/
theorem norm_transport_sub_le_lipschitz {ω : ℝ → 𝔸} {a b K : ℝ}
    (hK : ∀ t ∈ Icc a b, ‖ω t‖ ≤ K) {U : ℝ → 𝔸} (hU : IsTransport ω a b U) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖U t - U s‖ ≤ K * ‖U a‖ * Real.exp (K * (b - a)) * |t - s| := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK a (left_mem_Icc.2 hab))
  have hbound : ∀ x ∈ Icc a b, ‖-(ω x * U x)‖ ≤ K * ‖U a‖ * Real.exp (K * (b - a)) := by
    intro x hx
    rw [norm_neg]
    calc ‖ω x * U x‖ ≤ ‖ω x‖ * ‖U x‖ := norm_mul_le _ _
      _ ≤ K * (‖U a‖ * Real.exp (K * (b - a))) := by
          refine mul_le_mul (hK x hx) ((norm_transport_le hK hU x hx).trans ?_) (norm_nonneg _) hK0
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left (by linarith [hx.2]) hK0)) (norm_nonneg _)
      _ = K * ‖U a‖ * Real.exp (K * (b - a)) := by ring
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => hU x hx) hbound
    (convex_Icc a b) hs ht
  rwa [Real.norm_eq_abs] at this

/-- **Lipschitz dependence on the connection**: transports of `ω`, `ω̃` (both bounded by `K`)
from the same initial value `U₀`, with `‖ω − ω̃‖ ≤ δ` on `[a,b]`, satisfy
`‖U(t) − Ũ(t)‖ ≤ gronwallBound 0 K (δ ‖U₀‖ e^{K(b−a)}) (t − a)`. -/
theorem norm_transport_sub_transport_le {ω ω' : ℝ → 𝔸} {a b K δ : ℝ}
    (hK : ∀ t ∈ Icc a b, ‖ω t‖ ≤ K) (hK' : ∀ t ∈ Icc a b, ‖ω' t‖ ≤ K)
    (hδ : ∀ t ∈ Icc a b, ‖ω t - ω' t‖ ≤ δ) {U V : ℝ → 𝔸} (hU : IsTransport ω a b U)
    (hV : IsTransport ω' a b V) (h0 : U a = V a) :
    ∀ t ∈ Icc a b, ‖U t - V t‖ ≤ gronwallBound 0 K (δ * (‖U a‖ * Real.exp (K * (b - a)))) (t - a) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK a (left_mem_Icc.2 hab))
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hδ a (left_mem_Icc.2 hab))
  refine norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => U s - V s)
    (hU.continuousOn.sub hV.continuousOn)
    (fun s hs => (hU.hasDerivWithinAt_Ici hs).sub (hV.hasDerivWithinAt_Ici hs)) (by simp [h0])
    (fun s hs => ?_) t ht
  have hs' := Ico_subset_Icc_self hs
  have hVs : ‖V s‖ ≤ ‖U a‖ * Real.exp (K * (b - a)) := by
    refine (norm_transport_le hK' hV s hs').trans ?_
    rw [← h0]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (by linarith [hs'.2]) hK0)) (norm_nonneg _)
  have heq : -(ω s * U s) - -(ω' s * V s) = -(ω s * (U s - V s)) - (ω s - ω' s) * V s := by
    noncomm_ring
  rw [heq]
  calc ‖-(ω s * (U s - V s)) - (ω s - ω' s) * V s‖
      ≤ ‖ω s * (U s - V s)‖ + ‖(ω s - ω' s) * V s‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
    _ ≤ K * ‖U s - V s‖ + δ * (‖U a‖ * Real.exp (K * (b - a))) := by
        gcongr
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hK s hs') (norm_nonneg _))
        · exact (norm_mul_le _ _).trans (mul_le_mul (hδ s hs') hVs (norm_nonneg _) hδ0)

/-! ### Integral equation and second-order (Dyson) consistency -/

theorem IsTransport.hasDerivWithinAt_Ioi {ω : ℝ → 𝔸} {a b : ℝ} {U : ℝ → 𝔸}
    (hU : IsTransport ω a b U) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivWithinAt U (-(ω x * U x)) (Ioi x) x :=
  (hU x (Ioo_subset_Icc_self hx)).mono_of_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2))

/-- **Integral equation** `U(t) = U(a) − ∫_a^t ω U`. -/
theorem transport_integral_eq {ω : ℝ → 𝔸} {a b : ℝ} (hω : ContinuousOn ω (Icc a b))
    {U : ℝ → 𝔸} (hU : IsTransport ω a b U) {t : ℝ} (ht : t ∈ Icc a b) :
    U t = U a - ∫ s in a..t, ω s * U s := by
  have hcont : ContinuousOn (fun s => -(ω s * U s)) (Icc a t) :=
    ((hω.mul hU.continuousOn).neg).mono (Icc_subset_Icc_right ht.2)
  have h := integral_eq_sub_of_hasDeriv_right_of_le ht.1
    (hU.continuousOn.mono (Icc_subset_Icc_right ht.2))
    (fun x hx => hU.hasDerivWithinAt_Ioi ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩)
    (by rw [← uIcc_of_le ht.1] at hcont; exact hcont.intervalIntegrable)
  rw [intervalIntegral.integral_neg] at h
  calc U t = U a + (U t - U a) := by abel
    _ = U a - ∫ s in a..t, ω s * U s := by rw [← h]; abel

theorem exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h1 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.add_one_le_exp (-x), Real.exp_pos x]

/-- First-order remainder: for `U(a) = 1`,
`‖U(s) − 1 + ∫_a^s ω‖ ≤ K² (s − a)² e^{K(s−a)}`. -/
theorem norm_transport_sub_dyson_one_le {ω : ℝ → 𝔸} {a b K : ℝ}
    (hω : ContinuousOn ω (Icc a b)) (hK : ∀ t ∈ Icc a b, ‖ω t‖ ≤ K) {U : ℝ → 𝔸}
    (hU : IsTransport ω a b U) (h1 : U a = 1) {s : ℝ} (hs : s ∈ Icc a b) :
    ‖U s - 1 + ∫ r in a..s, ω r‖ ≤ K ^ 2 * (s - a) ^ 2 * Real.exp (K * (s - a)) := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK a (left_mem_Icc.2 hab))
  have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
  have hωi : IntervalIntegrable ω volume a s := by
    have := hω.mono hsub; rw [← uIcc_of_le hs.1] at this; exact this.intervalIntegrable
  have hωUi : IntervalIntegrable (fun r => ω r * U r) volume a s := by
    have := (hω.mul hU.continuousOn).mono hsub; rw [← uIcc_of_le hs.1] at this
    exact this.intervalIntegrable
  have heq : U s - 1 + ∫ r in a..s, ω r = -∫ r in a..s, ω r * (U r - 1) := by
    rw [transport_integral_eq hω hU hs, h1]
    have : ∫ r in a..s, ω r * (U r - 1) = (∫ r in a..s, ω r * U r) - ∫ r in a..s, ω r := by
      rw [← intervalIntegral.integral_sub hωUi hωi]
      congr 1; funext r; rw [mul_sub, mul_one]
    rw [this]; abel
  rw [heq, norm_neg]
  have hbound : ∀ r ∈ Ι a s, ‖ω r * (U r - 1)‖ ≤ K * (Real.exp (K * (s - a)) - 1) := by
    intro r hr
    rw [uIoc_of_le hs.1] at hr
    have hr' : r ∈ Icc a b := ⟨hr.1.le, hr.2.trans hs.2⟩
    have hU1 := norm_transport_sub_initial_le hK hU r hr'
    rw [h1, norm_one, one_mul] at hU1
    calc ‖ω r * (U r - 1)‖ ≤ ‖ω r‖ * ‖U r - 1‖ := norm_mul_le _ _
      _ ≤ K * (Real.exp (K * (s - a)) - 1) := by
          refine mul_le_mul (hK r hr') (hU1.trans ?_) (norm_nonneg _) hK0
          have : K * (r - a) ≤ K * (s - a) := mul_le_mul_of_nonneg_left (by linarith [hr.2]) hK0
          linarith [Real.exp_le_exp.2 this]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s - a)] at this
  refine this.trans ?_
  have hx := exp_sub_one_le_mul_exp (K * (s - a))
  have hsa : 0 ≤ s - a := by linarith [hs.1]
  calc K * (Real.exp (K * (s - a)) - 1) * (s - a)
      ≤ K * (K * (s - a) * Real.exp (K * (s - a))) * (s - a) := by gcongr
    _ = K ^ 2 * (s - a) ^ 2 * Real.exp (K * (s - a)) := by ring

/-- **Second-order consistency of the exact link (Dyson expansion)**: for the transport with
`U(a) = 1` of a connection continuous on `[a,b]` with `‖ω‖ ≤ K`,
`‖U(t) − (1 − ∫_a^t ω + ∫_a^t ω(s) ∫_a^s ω(r) dr ds)‖ ≤ K³ (t − a)³ e^{K(t−a)}`. -/
theorem norm_transport_sub_dyson_two_le {ω : ℝ → 𝔸} {a b K : ℝ}
    (hω : ContinuousOn ω (Icc a b)) (hK : ∀ t ∈ Icc a b, ‖ω t‖ ≤ K) {U : ℝ → 𝔸}
    (hU : IsTransport ω a b U) (h1 : U a = 1) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖U t - (1 - (∫ s in a..t, ω s) + ∫ s in a..t, ω s * ∫ r in a..s, ω r)‖
      ≤ K ^ 3 * (t - a) ^ 3 * Real.exp (K * (t - a)) := by
  have hab : a ≤ b := ht.1.trans ht.2
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK a (left_mem_Icc.2 hab))
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  set A : ℝ → 𝔸 := fun s => ∫ r in a..s, ω r with hA
  have hAc : ContinuousOn A (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := a) (b := b)
      (f := ω) (by rw [uIcc_of_le hab]; exact hω.integrableOn_Icc)
    rwa [uIcc_of_le hab] at this
  set R : ℝ → 𝔸 := fun s => U s - 1 + A s with hR
  have hRc : ContinuousOn R (Icc a b) := (hU.continuousOn.sub continuousOn_const).add hAc
  have hint : ∀ {g : ℝ → 𝔸}, ContinuousOn g (Icc a b) → IntervalIntegrable g volume a t := by
    intro g hg
    have := hg.mono hsub; rw [← uIcc_of_le ht.1] at this; exact this.intervalIntegrable
  have hI3 : IntervalIntegrable ω volume a t := hint hω
  have hI4 : IntervalIntegrable (fun s => ω s * A s) volume a t :=
    hint (g := fun s => ω s * A s) (hω.mul hAc)
  have hI2 : IntervalIntegrable (fun s => ω s * R s) volume a t :=
    hint (g := fun s => ω s * R s) (hω.mul hRc)
  have e1 : ∫ s in a..t, (ω s - ω s * A s + ω s * R s)
      = (∫ s in a..t, ω s) - (∫ s in a..t, ω s * A s) + ∫ s in a..t, ω s * R s := by
    rw [intervalIntegral.integral_add (hI3.sub hI4) hI2, intervalIntegral.integral_sub hI3 hI4]
  have hsplit : ∫ s in a..t, ω s * U s
      = (∫ s in a..t, ω s) - (∫ s in a..t, ω s * A s) + ∫ s in a..t, ω s * R s := by
    rw [← e1]
    congr 1; funext s
    simp only [hR]
    noncomm_ring
  have heq : U t - (1 - (∫ s in a..t, ω s) + ∫ s in a..t, ω s * A s)
      = -∫ s in a..t, ω s * R s := by
    rw [transport_integral_eq hω hU ht, h1, hsplit]; abel
  rw [heq, norm_neg]
  have hbound : ∀ s ∈ Ι a t, ‖ω s * R s‖ ≤ K * (K ^ 2 * (t - a) ^ 2 * Real.exp (K * (t - a))) := by
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2.trans ht.2⟩
    have hR1 := norm_transport_sub_dyson_one_le hω hK hU h1 hs'
    have hsa : 0 ≤ s - a := by linarith [hs.1]
    calc ‖ω s * R s‖ ≤ ‖ω s‖ * ‖R s‖ := norm_mul_le _ _
      _ ≤ K * (K ^ 2 * (t - a) ^ 2 * Real.exp (K * (t - a))) := by
          refine mul_le_mul (hK s hs') (hR1.trans ?_) (norm_nonneg _) hK0
          have h2 : (s - a) ^ 2 ≤ (t - a) ^ 2 := pow_le_pow_left₀ hsa (by linarith [hs.2]) 2
          have h3 : Real.exp (K * (s - a)) ≤ Real.exp (K * (t - a)) :=
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hK0)
          gcongr
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - a)] at this
  refine this.trans (le_of_eq ?_)
  ring

/-! ### Constant connections: the exact link is an exponential -/

/-- For a constant connection `ω ≡ X` the transport from `1` is `t ↦ exp(−(t−a) X)`. -/
theorem isTransport_const_exp (X : 𝔸) (a b : ℝ) :
    IsTransport (fun _ => X) a b (fun t => NormedSpace.exp ((t - a) • (-X))) := by
  intro t _
  have h := HasDerivAt.scomp t (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-X) (t - a))
    ((hasDerivAt_id' t).sub_const a)
  have e : (1 : ℝ) • (-X * NormedSpace.exp ((t - a) • -X))
      = -(X * NormedSpace.exp ((t - a) • (-X))) := by rw [one_smul, neg_mul]
  rw [e] at h
  exact h.hasDerivWithinAt

/-- **Exact link of a constant connection**: any transport of `ω ≡ X` on `[a,b]` with
`U(a) = 1` equals `exp(−(t−a)X)`. -/
theorem transport_const_eq_exp {X : 𝔸} {a b : ℝ} {U : ℝ → 𝔸}
    (hU : IsTransport (fun _ => X) a b U) (h1 : U a = 1) :
    ∀ t ∈ Icc a b, U t = NormedSpace.exp ((t - a) • (-X)) :=
  transport_unique (K := ‖X‖) (fun _ _ => le_rfl) hU (isTransport_const_exp X a b)
    (by simp [h1])

/-- Second-order Taylor bound for the algebra exponential, obtained from the Dyson expansion:
`‖exp(−hX) − (1 − hX + (h²/2) X²)‖ ≤ ‖X‖³ h³ e^{‖X‖h}` for `h ≥ 0`. -/
theorem norm_exp_neg_smul_sub_quadratic_le (X : 𝔸) {h : ℝ} (hh : 0 ≤ h) :
    ‖NormedSpace.exp (h • (-X)) - (1 - h • X + (h ^ 2 / 2) • (X * X))‖
      ≤ ‖X‖ ^ 3 * h ^ 3 * Real.exp (‖X‖ * h) := by
  have hT := isTransport_const_exp X 0 h
  have hmem : h ∈ Icc (0 : ℝ) h := ⟨hh, le_rfl⟩
  have := norm_transport_sub_dyson_two_le (ω := fun _ => X) (K := ‖X‖) continuousOn_const
    (fun _ _ => le_rfl) hT (by simp) hmem
  simp only [sub_zero] at this
  have e1 : ∫ s in (0 : ℝ)..h, X = h • X := by simp
  have e2 : ∫ s in (0 : ℝ)..h, X * ∫ r in (0 : ℝ)..s, X = (h ^ 2 / 2) • (X * X) := by
    have : (fun s : ℝ => X * ∫ r in (0 : ℝ)..s, X) = fun s => s • (X * X) := by
      funext s; simp
    rw [this, intervalIntegral.integral_smul_const, integral_id]
    congr 1; ring
  rwa [e1, e2] at this


section MatrixInstance

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Non-vacuity: the hypotheses are met by real `4 × 4` matrices with the `L∞` operator norm
(the frame-bundle algebra of the Cartan regulator); e.g. the flat connection `ω = 0` has an
exact link on `[0,1]`, and every exact link of a continuous connection with `‖ω‖ ≤ K` exists
on segments of length `≤ 1/(2K)`. -/
example : ∃ U : ℝ → Matrix (Fin 4) (Fin 4) ℝ, U 0 = 1 ∧
    IsTransport (fun _ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) 0 1 U := by
  have : CompleteSpace (Matrix (Fin 4) (Fin 4) ℝ) := FiniteDimensional.complete ℝ _
  exact exists_transport (K := 0) zero_le_one continuousOn_const (fun _ _ => by simp)
    (by norm_num) 1

end MatrixInstance

end RenewalGeometry.PathOrderedExp
