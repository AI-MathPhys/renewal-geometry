/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.PathOrderedExponential
import RenewalGeometry.Analysis.CovariantCellQuadrature
import RenewalGeometry.DiscreteAnalysis.ShiftedPlaquetteLogarithmUniformExact

/-!
# Transport links, plaquettes and covariant differences of a smooth connection
  (pointwise expansions of `prop:mesh-consistency`)

Einstein–Standard-Model action-closure manuscript, "Concrete reconstruction and smooth
first-variation consistency", `eq:lattice-comparison`, `eq:spin-difference` and the proof of
`prop:mesh-consistency`: "The integral equation for parallel transport and Taylor expansion along
an edge give `U_μ(x) = I + hA_μ(x) + O(h²)`.  Multiplying the four edge expansions cancels the
terms linear in `h` and leaves `U_{μν}(x) = I + h²𝔽_{A,μν}(x) + O(h³)` … `F^h = 𝔽_A + O(h)`.
Covariant Taylor expansion similarly gives `K^h = D_AH + O(h)` and `∇^hΨ = ∇^{e,A}Ψ + O(h)`."

Setting: a complete normed real algebra `𝔸` with `‖1‖ = 1` (the represented gauge/spin–gauge
algebra), transports `U' = -ωU`, `U(0) = 1` of `PathOrderedExp.IsTransport`.  For a connection
`A` with components `A_μ`, the *backward* transport `U_μ(x)` from `x + h e_μ` to `x` is the
transport along the reversed edge, with coefficient `t ↦ -A_μ(x + (h - t) e_μ)`; its inverse is
the forward transport with coefficient `t ↦ A_μ(x + t e_μ)` (`reverse_transport_mul`).

* `norm_transport_sub_linear_le`: first-order edge expansion `U(h) = 1 - hZ + O(h²)` when
  `ω = Z + O(h)` on the edge.
* `norm_transport_sub_quadratic_le`: **second-order edge expansion**
  `U(h) = 1 - hZ + (h²/2)(Z² - W) + O(h³)` when `ω(t) = Z + tW + O(h²)` (Dyson expansion of
  `PathOrderedExp` plus explicit integration of the Taylor polynomial).
* `reverse_transport_mul`, `transport_mul_reverse`: the reversed-edge transport is the
  two-sided inverse of the forward transport.
* `norm_mul_quadratic_sub_le`: products of second-order expansions
  (`(1 + hA + h²B)(1 + hA' + h²B') = 1 + h(A + A') + h²(B + B' + AA') + O(h³)`).
* `norm_plaquette_sub_curvature_le` (**the four-edge plaquette**): for the four edges of the
  `(μ,ν)` plaquette with coefficient expansions
  `A_μ(x + u) = X + Dₓ A_μ u + O(|u|²)`, `A_ν(x + u) = Y + Dₓ A_ν u + O(|u|²)`,
  `‖U_μ(x) U_ν(x + he_μ) U_μ(x + he_ν)⁻¹ U_ν(x)⁻¹ - (1 + h² 𝔽_{μν})‖ ≤ C h³`,
  `𝔽_{μν} = ∂_μA_ν - ∂_νA_μ + [A_μ, A_ν]`.
* `norm_logOneAdd_sub_le` and `norm_logPlaquette_sub_curvature_le`: with the analytic logarithm
  near the identity, `F^h = h⁻² log U_{μν} = 𝔽 + O(h)`.
* `norm_covariantForwardDifference_sub_le` (**Higgs links** `K^h = h⁻¹(U_μ(x)H(x+he_μ) - H(x))
  = D_μH + O(h)`) and `norm_covariantCentredDifference_sub_le` (**spinor transport**,
  `eq:spin-difference`: `(𝒰_μ(x)Ψ(x+he_μ) - 𝒰_μ(x-he_μ)⁻¹Ψ(x-he_μ))/(2h) = ∇_μΨ + O(h)`).

All constants are explicit in the sup bound `K` of the connection, the Taylor constants of the
fields and the edge mesh `h ≤ 1`.
-/

open Set intervalIntegral MeasureTheory

noncomputable section

namespace RenewalGeometry.TransportPlaquetteConsistency

open PathOrderedExp

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ### Edge expansions -/

/-- **First-order edge expansion**: if `‖ω‖ ≤ K` and `‖ω t - Z‖ ≤ m` on `[0,h]`, the transport
with `U(0) = 1` satisfies `‖U(h) - (1 - hZ)‖ ≤ (K² e^{Kh}) h² + m h`. -/
theorem norm_transport_sub_linear_le {ω : ℝ → 𝔸} {h K m : ℝ} (hh : 0 ≤ h)
    (hω : ContinuousOn ω (Icc 0 h)) (hK : ∀ t ∈ Icc 0 h, ‖ω t‖ ≤ K) {Z : 𝔸}
    (hZ : ∀ t ∈ Icc 0 h, ‖ω t - Z‖ ≤ m) {U : ℝ → 𝔸} (hU : IsTransport ω 0 h U) (h1 : U 0 = 1) :
    ‖U h - (1 - h • Z)‖ ≤ K ^ 2 * Real.exp (K * h) * h ^ 2 + m * h := by
  have hD := norm_transport_sub_dyson_one_le hω hK hU h1 ⟨hh, le_rfl⟩
  simp only [sub_zero] at hD
  have hint : IntervalIntegrable ω volume 0 h := by
    have := hω; rw [← uIcc_of_le hh] at this; exact this.intervalIntegrable
  have hI : ‖(∫ r in (0 : ℝ)..h, ω r) - h • Z‖ ≤ m * h := by
    have e : (∫ r in (0 : ℝ)..h, ω r) - h • Z = ∫ r in (0 : ℝ)..h, (ω r - Z) := by
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
        intervalIntegral.integral_const, sub_zero]
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
      (C := m) (f := fun r => ω r - Z) (fun r hr => by
        rw [uIoc_of_le hh] at hr; exact hZ r ⟨hr.1.le, hr.2⟩)
    rwa [sub_zero, abs_of_nonneg hh] at this
  have e : U h - (1 - h • Z) = (U h - 1 + ∫ r in (0 : ℝ)..h, ω r) -
      ((∫ r in (0 : ℝ)..h, ω r) - h • Z) := by abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  nlinarith [hD, hI]

/-- **Second-order edge expansion** (Dyson expansion plus integration of the Taylor polynomial of
the coefficient): if `‖ω‖ ≤ K` on `[0,h]` and `‖ω t - (Z + tW)‖ ≤ M h²` there, then
`‖U(h) - (1 - hZ + (h²/2)(Z² - W))‖ ≤ (K³ e^{Kh} + M + (K + ‖Z‖)(‖W‖ + Mh)) h³`. -/
theorem norm_transport_sub_quadratic_le {ω : ℝ → 𝔸} {h K M : ℝ} (hh : 0 ≤ h)
    (hω : ContinuousOn ω (Icc 0 h)) (hK : ∀ t ∈ Icc 0 h, ‖ω t‖ ≤ K) {Z W : 𝔸}
    (hZW : ∀ t ∈ Icc 0 h, ‖ω t - (Z + t • W)‖ ≤ M * h ^ 2) {U : ℝ → 𝔸}
    (hU : IsTransport ω 0 h U) (h1 : U 0 = 1) :
    ‖U h - (1 - h • Z + (h ^ 2 / 2) • (Z * Z - W))‖ ≤
      (K ^ 3 * Real.exp (K * h) + M + (K + ‖Z‖) * (‖W‖ + M * h)) * h ^ 3 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hh⟩)
  have hM0 : 0 ≤ M * h ^ 2 := (norm_nonneg _).trans (hZW 0 ⟨le_rfl, hh⟩)
  have hD := norm_transport_sub_dyson_two_le hω hK hU h1 ⟨hh, le_rfl⟩
  simp only [sub_zero] at hD
  set A : ℝ → 𝔸 := fun s => ∫ r in (0 : ℝ)..s, ω r with hA
  have hint : ∀ {g : ℝ → 𝔸}, ContinuousOn g (Icc 0 h) → ∀ s ∈ Icc 0 h,
      IntervalIntegrable g volume 0 s := by
    intro g hg s hs
    have := hg.mono (Icc_subset_Icc_right hs.2); rw [← uIcc_of_le hs.1] at this
    exact this.intervalIntegrable
  have hAc : ContinuousOn A (Icc 0 h) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := h)
      (f := ω) (by rw [uIcc_of_le hh]; exact hω.integrableOn_Icc)
    rwa [uIcc_of_le hh] at this
  -- the difference `ω - Z` is `O(h)` on the edge
  have hδ : ∀ t ∈ Icc 0 h, ‖ω t - Z‖ ≤ h * (‖W‖ + M * h) := by
    intro t ht
    have e : ω t - Z = (ω t - (Z + t • W)) + t • W := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have : t * ‖W‖ ≤ h * ‖W‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    nlinarith [hZW t ht]
  -- first Dyson term
  have hI1 : ‖A h - (h • Z + (h ^ 2 / 2) • W)‖ ≤ M * h ^ 3 := by
    have hpoly : ∫ r in (0 : ℝ)..h, (Z + r • W) = h • Z + (h ^ 2 / 2) • W := by
      rw [intervalIntegral.integral_add (f := fun _ => Z) (g := fun r : ℝ => r • W)
        intervalIntegrable_const
        ((by fun_prop : Continuous fun r : ℝ => r • W).intervalIntegrable _ _),
        intervalIntegral.integral_const, intervalIntegral.integral_smul_const, integral_id]
      simp only [sub_zero]
      congr 1; congr 1; ring
    have e : A h - (h • Z + (h ^ 2 / 2) • W) = ∫ r in (0 : ℝ)..h, (ω r - (Z + r • W)) := by
      rw [← hpoly, intervalIntegral.integral_sub (g := fun r : ℝ => Z + r • W)
        (hint hω h ⟨hh, le_rfl⟩)
        ((by fun_prop : Continuous fun r : ℝ => Z + r • W).intervalIntegrable _ _)]
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
      (C := M * h ^ 2) (f := fun r => ω r - (Z + r • W)) (fun r hr => by
        rw [uIoc_of_le hh] at hr; exact hZW r ⟨hr.1.le, hr.2⟩)
    rw [sub_zero, abs_of_nonneg hh] at this
    exact this.trans (le_of_eq (by ring))
  -- second Dyson term
  have hI2 : ‖(∫ s in (0 : ℝ)..h, ω s * A s) - (h ^ 2 / 2) • (Z * Z)‖ ≤
      (K + ‖Z‖) * (‖W‖ + M * h) * h ^ 3 := by
    have hpoly : ∫ s in (0 : ℝ)..h, s • (Z * Z) = (h ^ 2 / 2) • (Z * Z) := by
      rw [intervalIntegral.integral_smul_const, integral_id]; congr 1; ring
    have hc : ContinuousOn (fun s => ω s * A s) (Icc 0 h) := hω.mul hAc
    have e : (∫ s in (0 : ℝ)..h, ω s * A s) - (h ^ 2 / 2) • (Z * Z) =
        ∫ s in (0 : ℝ)..h, (ω s * A s - s • (Z * Z)) := by
      rw [← hpoly, intervalIntegral.integral_sub (g := fun s : ℝ => s • (Z * Z))
        (hint hc h ⟨hh, le_rfl⟩)
        ((by fun_prop : Continuous fun s : ℝ => s • (Z * Z)).intervalIntegrable _ _)]
    rw [e]
    have hpt : ∀ s ∈ Icc 0 h, ‖ω s * A s - s • (Z * Z)‖ ≤ (K + ‖Z‖) * (‖W‖ + M * h) * h ^ 2 := by
      intro s hs
      have hAs : ‖A s‖ ≤ K * h := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s) (C := K)
          (f := ω) (fun r hr => by
            rw [uIoc_of_le hs.1] at hr; exact hK r ⟨hr.1.le, hr.2.trans hs.2⟩)
        rw [sub_zero, abs_of_nonneg hs.1] at this
        exact this.trans (mul_le_mul_of_nonneg_left hs.2 hK0)
      have hAZ : ‖A s - s • Z‖ ≤ h * (‖W‖ + M * h) * h := by
        have e : A s - s • Z = ∫ r in (0 : ℝ)..s, (ω r - Z) := by
          rw [intervalIntegral.integral_sub (hint hω s hs) intervalIntegrable_const,
            intervalIntegral.integral_const, sub_zero]
        rw [e]
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s)
          (C := h * (‖W‖ + M * h)) (f := fun r => ω r - Z) (fun r hr => by
            rw [uIoc_of_le hs.1] at hr; exact hδ r ⟨hr.1.le, hr.2.trans hs.2⟩)
        rw [sub_zero, abs_of_nonneg hs.1] at this
        exact this.trans (mul_le_mul_of_nonneg_left hs.2 (by
          have := hδ 0 ⟨le_rfl, hh⟩; exact (norm_nonneg _).trans this))
      have e : ω s * A s - s • (Z * Z) = (ω s - Z) * A s + Z * (A s - s • Z) := by
        rw [mul_sub, mul_smul_comm, sub_mul]; abel
      rw [e]
      have hδs := hδ s hs
      have hδ0 : 0 ≤ h * (‖W‖ + M * h) := (norm_nonneg _).trans hδs
      calc ‖(ω s - Z) * A s + Z * (A s - s • Z)‖
          ≤ ‖ω s - Z‖ * ‖A s‖ + ‖Z‖ * ‖A s - s • Z‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ (h * (‖W‖ + M * h)) * (K * h) + ‖Z‖ * (h * (‖W‖ + M * h) * h) := by
            gcongr
        _ = (K + ‖Z‖) * (‖W‖ + M * h) * h ^ 2 := by ring
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
      (C := (K + ‖Z‖) * (‖W‖ + M * h) * h ^ 2) (f := fun s => ω s * A s - s • (Z * Z))
      (fun r hr => by rw [uIoc_of_le hh] at hr; exact hpt r ⟨hr.1.le, hr.2⟩)
    rw [sub_zero, abs_of_nonneg hh] at this
    exact this.trans (le_of_eq (by ring))
  have e : U h - (1 - h • Z + (h ^ 2 / 2) • (Z * Z - W)) =
      (U h - (1 - A h + ∫ s in (0 : ℝ)..h, ω s * A s)) - (A h - (h • Z + (h ^ 2 / 2) • W)) +
        ((∫ s in (0 : ℝ)..h, ω s * A s) - (h ^ 2 / 2) • (Z * Z)) := by
    rw [smul_sub]; abel
  rw [e]
  have hD' : ‖U h - (1 - A h + ∫ s in (0 : ℝ)..h, ω s * A s)‖ ≤
      K ^ 3 * h ^ 3 * Real.exp (K * h) := hD
  calc _ ≤ ‖U h - (1 - A h + ∫ s in (0 : ℝ)..h, ω s * A s)‖ +
          ‖A h - (h • Z + (h ^ 2 / 2) • W)‖ +
          ‖(∫ s in (0 : ℝ)..h, ω s * A s) - (h ^ 2 / 2) • (Z * Z)‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ K ^ 3 * h ^ 3 * Real.exp (K * h) + M * h ^ 3 + (K + ‖Z‖) * (‖W‖ + M * h) * h ^ 3 := by
        gcongr
    _ = _ := by ring

/-! ### Reversed edges: backward transports are inverse to forward transports -/

/-- The transport of the reversed edge (coefficient `t ↦ -ω(h - t)`) is a left inverse of the
forward transport: `R(h) P(h) = 1`. -/
theorem reverse_transport_mul {ω : ℝ → 𝔸} {h K : ℝ} (hh : 0 ≤ h)
    (hK : ∀ t ∈ Icc 0 h, ‖ω t‖ ≤ K) {P R : ℝ → 𝔸} (hP : IsTransport ω 0 h P) (hP0 : P 0 = 1)
    (hR : IsTransport (fun t => -ω (h - t)) 0 h R) (hR0 : R 0 = 1) : R h * P h = 1 := by
  have hmaps : MapsTo (fun t : ℝ => h - t) (Icc 0 h) (Icc 0 h) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hf : IsTransport (fun t => -ω (h - t)) 0 h (fun t => R t * P h - P (h - t)) := by
    intro t ht
    have h1 := (hR t ht).mul_const (P h)
    have h2 : HasDerivWithinAt (fun t => P (h - t)) ((-1 : ℝ) • (-(ω (h - t) * P (h - t))))
        (Icc 0 h) t :=
      (hP (h - t) (hmaps ht)).scomp t ((hasDerivWithinAt_id t _).const_sub h) hmaps
    refine (h1.sub h2).congr_deriv ?_
    simp only [neg_one_smul, neg_neg, neg_mul, mul_sub, mul_assoc]
    abel
  have hz : IsTransport (fun t => -ω (h - t)) 0 h (fun _ => (0 : 𝔸)) := fun t _ => by
    simpa using hasDerivWithinAt_const t (Icc 0 h) (0 : 𝔸)
  have huniq := transport_unique (K := K) (fun t ht => by
      rw [norm_neg]; exact hK _ (hmaps ht)) hf hz (by simp [hR0])
    ⟨hh, le_rfl⟩
  simp only [sub_self, hP0] at huniq
  exact sub_eq_zero.1 huniq

/-- The forward transport is a left inverse of the reversed-edge transport: `P(h) R(h) = 1`. -/
theorem transport_mul_reverse {ω : ℝ → 𝔸} {h K : ℝ} (hh : 0 ≤ h)
    (hK : ∀ t ∈ Icc 0 h, ‖ω t‖ ≤ K) {P R : ℝ → 𝔸} (hP : IsTransport ω 0 h P) (hP0 : P 0 = 1)
    (hR : IsTransport (fun t => -ω (h - t)) 0 h R) (hR0 : R 0 = 1) : P h * R h = 1 := by
  have hmaps : MapsTo (fun t : ℝ => h - t) (Icc 0 h) (Icc 0 h) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hg : IsTransport ω 0 h (fun t => P t * R h - R (h - t)) := by
    intro t ht
    have h1 := (hP t ht).mul_const (R h)
    have h2 : HasDerivWithinAt (fun t => R (h - t))
        ((-1 : ℝ) • (-(-ω (h - (h - t)) * R (h - t)))) (Icc 0 h) t :=
      (hR (h - t) (hmaps ht)).scomp t ((hasDerivWithinAt_id t _).const_sub h) hmaps
    refine (h1.sub h2).congr_deriv ?_
    simp only [sub_sub_cancel, neg_one_smul, neg_neg, neg_mul, mul_sub, mul_assoc]
    abel
  have hz : IsTransport ω 0 h (fun _ => (0 : 𝔸)) := fun t _ => by
    simpa using hasDerivWithinAt_const t (Icc 0 h) (0 : 𝔸)
  have huniq := transport_unique hK hg hz (by simp [hP0]) ⟨hh, le_rfl⟩
  simp only [sub_self, hR0] at huniq
  exact sub_eq_zero.1 huniq

/-- The reversed-edge transport is the inverse of the forward transport in `𝔸`. -/
theorem ring_inverse_reverse_transport {ω : ℝ → 𝔸} {h K : ℝ} (hh : 0 ≤ h)
    (hK : ∀ t ∈ Icc 0 h, ‖ω t‖ ≤ K) {P R : ℝ → 𝔸} (hP : IsTransport ω 0 h P) (hP0 : P 0 = 1)
    (hR : IsTransport (fun t => -ω (h - t)) 0 h R) (hR0 : R 0 = 1) : Ring.inverse (R h) = P h := by
  let u : 𝔸ˣ := ⟨R h, P h, reverse_transport_mul hh hK hP hP0 hR hR0,
    transport_mul_reverse hh hK hP hP0 hR hR0⟩
  exact Ring.inverse_unit u

/-! ### Products of second-order expansions -/

omit [CompleteSpace 𝔸] in
/-- **Product of two second-order expansions**: if `‖u - (1 + hA + h²B)‖ ≤ E h³` and
`‖u' - (1 + hA' + h²B')‖ ≤ E' h³` with `‖A‖, ‖A'‖ ≤ α`, `‖B‖, ‖B'‖ ≤ β`, `0 ≤ h ≤ 1`, then
`‖uu' - (1 + h(A + A') + h²(B + B' + AA'))‖ ≤ ((1 + α + β)(E + E') + EE' + 2αβ + β²) h³`. -/
theorem norm_mul_quadratic_sub_le {u u' A A' B B' : 𝔸} {h E E' α β : ℝ} (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1) (hE : 0 ≤ E) (hu : ‖u - (1 + h • A + h ^ 2 • B)‖ ≤ E * h ^ 3)
    (hu' : ‖u' - (1 + h • A' + h ^ 2 • B')‖ ≤ E' * h ^ 3) (hA : ‖A‖ ≤ α) (hA' : ‖A'‖ ≤ α)
    (hB : ‖B‖ ≤ β) (hB' : ‖B'‖ ≤ β) :
    ‖u * u' - (1 + h • (A + A') + h ^ 2 • (B + B' + A * A'))‖ ≤
      ((1 + α + β) * (E + E') + E * E' + 2 * α * β + β ^ 2) * h ^ 3 := by
  have hα : 0 ≤ α := (norm_nonneg _).trans hA
  have hβ : 0 ≤ β := (norm_nonneg _).trans hB
  set p := 1 + h • A + h ^ 2 • B
  set p' := 1 + h • A' + h ^ 2 • B'
  have hh2 : h ^ 2 ≤ 1 := pow_le_one₀ hh0 hh1
  have hp : ‖p‖ ≤ 1 + α + β := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_one, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hh0,
      abs_of_nonneg (by positivity)]
    have := mul_le_mul hh1 hA (norm_nonneg _) zero_le_one
    have := mul_le_mul hh2 hB (norm_nonneg _) zero_le_one
    linarith
  have hp' : ‖p'‖ ≤ 1 + α + β := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_one, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hh0,
      abs_of_nonneg (by positivity)]
    have := mul_le_mul hh1 hA' (norm_nonneg _) zero_le_one
    have := mul_le_mul hh2 hB' (norm_nonneg _) zero_le_one
    linarith
  have hpp : p * p' - (1 + h • (A + A') + h ^ 2 • (B + B' + A * A')) =
      h ^ 3 • (A * B' + B * A') + h ^ 4 • (B * B') := by
    simp only [p, p', add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      smul_add]
    module
  have e : u * u' - (1 + h • (A + A') + h ^ 2 • (B + B' + A * A')) =
      (h ^ 3 • (A * B' + B * A') + h ^ 4 • (B * B')) + p * (u' - p') + (u - p) * p' +
        (u - p) * (u' - p') := by
    rw [← hpp]; noncomm_ring
  rw [e]
  have h3 : 0 ≤ h ^ 3 := by positivity
  have h43 : h ^ 4 ≤ h ^ 3 := pow_le_pow_of_le_one hh0 hh1 (by norm_num)
  have h63 : h ^ 3 * h ^ 3 ≤ h ^ 3 := by
    have : h ^ 3 ≤ 1 := pow_le_one₀ hh0 hh1
    nlinarith
  have t1 : ‖h ^ 3 • (A * B' + B * A') + h ^ 4 • (B * B')‖ ≤ (2 * α * β + β ^ 2) * h ^ 3 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3,
      abs_of_nonneg (by positivity)]
    have hAB : ‖A * B' + B * A'‖ ≤ 2 * α * β := by
      refine (norm_add_le _ _).trans ?_
      have := (norm_mul_le A B').trans (mul_le_mul hA hB' (norm_nonneg _) hα)
      have := (norm_mul_le B A').trans (mul_le_mul hB hA' (norm_nonneg _) hβ)
      linarith
    have hBB : ‖B * B'‖ ≤ β ^ 2 := by
      have := (norm_mul_le B B').trans (mul_le_mul hB hB' (norm_nonneg _) hβ)
      nlinarith
    have : h ^ 4 * ‖B * B'‖ ≤ h ^ 3 * β ^ 2 :=
      mul_le_mul h43 hBB (norm_nonneg _) h3
    nlinarith [mul_le_mul_of_nonneg_left hAB h3]
  have t2 : ‖p * (u' - p')‖ ≤ (1 + α + β) * (E' * h ^ 3) :=
    (norm_mul_le _ _).trans (mul_le_mul hp hu' (norm_nonneg _) (by linarith))
  have t3 : ‖(u - p) * p'‖ ≤ (E * h ^ 3) * (1 + α + β) :=
    (norm_mul_le _ _).trans (mul_le_mul hu hp' (norm_nonneg _) (by positivity))
  have t4 : ‖(u - p) * (u' - p')‖ ≤ E * E' * h ^ 3 := by
    refine (norm_mul_le _ _).trans ((mul_le_mul hu hu' (norm_nonneg _) (by positivity)).trans ?_)
    have hE' : 0 ≤ E' * h ^ 3 := (norm_nonneg _).trans hu'
    calc E * h ^ 3 * (E' * h ^ 3) = E * (E' * h ^ 3) * h ^ 3 := by ring
      _ ≤ E * (E' * h ^ 3) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hh0 hh1) (mul_nonneg hE hE')
      _ = E * E' * h ^ 3 := by ring
  calc _ ≤ ‖h ^ 3 • (A * B' + B * A') + h ^ 4 • (B * B')‖ + ‖p * (u' - p')‖ +
        ‖(u - p) * p'‖ + ‖(u - p) * (u' - p')‖ :=
        (norm_add_le _ _).trans (add_le_add_left ((norm_add_le _ _).trans
          (add_le_add_left (norm_add_le _ _) _)) _) |>.trans (le_of_eq (by ring))
    _ ≤ (2 * α * β + β ^ 2) * h ^ 3 + (1 + α + β) * (E' * h ^ 3) +
        (E * h ^ 3) * (1 + α + β) + E * E' * h ^ 3 := by gcongr
    _ = _ := by ring

/-- **Second-order edge expansion with an `h`-dependent base value**: if the coefficient is
`ω(t) = Z₀ + hZ₁ + tW + O(h²)` on the edge, the transport is
`U(h) = 1 + h(-Z₀) + h²(-Z₁ + (Z₀² - W)/2) + O(h³)`, with explicit constant. -/
theorem norm_transport_sub_edgeExpansion_le {ω : ℝ → 𝔸} {h K M : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hω : ContinuousOn ω (Icc 0 h)) (hK : ∀ t ∈ Icc 0 h, ‖ω t‖ ≤ K) (hM : 0 ≤ M) {Z₀ Z₁ W : 𝔸}
    (hZW : ∀ t ∈ Icc 0 h, ‖ω t - (Z₀ + h • Z₁ + t • W)‖ ≤ M * h ^ 2) {U : ℝ → 𝔸}
    (hU : IsTransport ω 0 h U) (h1 : U 0 = 1) :
    ‖U h - (1 + h • (-Z₀) + h ^ 2 • (-Z₁ + (1 / 2 : ℝ) • (Z₀ * Z₀ - W)))‖ ≤
      (K ^ 3 * Real.exp K + M + (K + ‖Z₀‖ + ‖Z₁‖) * (‖W‖ + M) + ‖Z₀‖ * ‖Z₁‖ + ‖Z₁‖ ^ 2) *
        h ^ 3 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hh⟩)
  have hq := norm_transport_sub_quadratic_le hh hω hK (Z := Z₀ + h • Z₁) (W := W)
    (fun t ht => by simpa [add_assoc] using hZW t ht) hU h1
  have hid : (1 - h • (Z₀ + h • Z₁) + (h ^ 2 / 2) • ((Z₀ + h • Z₁) * (Z₀ + h • Z₁) - W)) -
      (1 + h • (-Z₀) + h ^ 2 • (-Z₁ + (1 / 2 : ℝ) • (Z₀ * Z₀ - W))) =
      (h ^ 3 / 2) • (Z₀ * Z₁ + Z₁ * Z₀) + (h ^ 4 / 2) • (Z₁ * Z₁) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_neg]
    module
  have hZ : ‖Z₀ + h • Z₁‖ ≤ ‖Z₀‖ + ‖Z₁‖ := by
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    exact mul_le_of_le_one_left (norm_nonneg _) hh1
  have hexp : Real.exp (K * h) ≤ Real.exp K :=
    Real.exp_le_exp.2 (mul_le_of_le_one_right hK0 hh1)
  have e : U h - (1 + h • (-Z₀) + h ^ 2 • (-Z₁ + (1 / 2 : ℝ) • (Z₀ * Z₀ - W))) =
      (U h - (1 - h • (Z₀ + h • Z₁) + (h ^ 2 / 2) • ((Z₀ + h • Z₁) * (Z₀ + h • Z₁) - W))) +
        ((h ^ 3 / 2) • (Z₀ * Z₁ + Z₁ * Z₀) + (h ^ 4 / 2) • (Z₁ * Z₁)) := by
    rw [← hid]; abel
  rw [e]
  have h3 : 0 ≤ h ^ 3 := by positivity
  have h43 : h ^ 4 ≤ h ^ 3 := pow_le_pow_of_le_one hh (hh1) (by norm_num)
  have hrest : ‖(h ^ 3 / 2) • (Z₀ * Z₁ + Z₁ * Z₀) + (h ^ 4 / 2) • (Z₁ * Z₁)‖ ≤
      (‖Z₀‖ * ‖Z₁‖ + ‖Z₁‖ ^ 2) * h ^ 3 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    have a1 : ‖Z₀ * Z₁ + Z₁ * Z₀‖ ≤ 2 * (‖Z₀‖ * ‖Z₁‖) := by
      refine (norm_add_le _ _).trans ?_
      have := norm_mul_le Z₀ Z₁; have := norm_mul_le Z₁ Z₀; nlinarith
    have a2 : ‖Z₁ * Z₁‖ ≤ ‖Z₁‖ ^ 2 := by have := norm_mul_le Z₁ Z₁; nlinarith
    have b1 : h ^ 3 / 2 * ‖Z₀ * Z₁ + Z₁ * Z₀‖ ≤ h ^ 3 * (‖Z₀‖ * ‖Z₁‖) := by nlinarith
    have b2 : h ^ 4 / 2 * ‖Z₁ * Z₁‖ ≤ h ^ 3 * ‖Z₁‖ ^ 2 := by
      have := mul_le_mul h43 a2 (norm_nonneg _) h3
      nlinarith [norm_nonneg (Z₁ * Z₁)]
    nlinarith
  refine (norm_add_le _ _).trans ?_
  have hq' : ‖U h - (1 - h • (Z₀ + h • Z₁) + (h ^ 2 / 2) •
      ((Z₀ + h • Z₁) * (Z₀ + h • Z₁) - W))‖ ≤
      (K ^ 3 * Real.exp K + M + (K + ‖Z₀‖ + ‖Z₁‖) * (‖W‖ + M)) * h ^ 3 := by
    refine hq.trans (mul_le_mul_of_nonneg_right ?_ h3)
    have : ‖W‖ + M * h ≤ ‖W‖ + M := by nlinarith
    have c1 : K ^ 3 * Real.exp (K * h) ≤ K ^ 3 * Real.exp K :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    have c2 : (K + ‖Z₀ + h • Z₁‖) * (‖W‖ + M * h) ≤ (K + ‖Z₀‖ + ‖Z₁‖) * (‖W‖ + M) :=
      mul_le_mul (by linarith) this (by positivity) (by positivity)
    linarith
  nlinarith [hq', hrest]

/-! ### The four-edge plaquette -/

/-- The edge constant `K³e^K + M + (K + 3N)(N + M) + 6N²`. -/
def edgeConst (N K M : ℝ) : ℝ := K ^ 3 * Real.exp K + M + (K + 3 * N) * (N + M) + 6 * N ^ 2

/-- Bound `3N + N²` for the second-order edge coefficients. -/
def edgeBeta (N : ℝ) : ℝ := 3 * N + N ^ 2

/-- The constant of `norm_mul_quadratic_sub_le`. -/
def prodConst (α β E E' : ℝ) : ℝ := (1 + α + β) * (E + E') + E * E' + 2 * α * β + β ^ 2

/-- **The explicit plaquette constant** (depends only on the coefficient bound `K`, the Taylor
constant `M` and the jet bound `N`). -/
def plaquetteConst (N K M : ℝ) : ℝ :=
  prodConst (3 * N) (3 * edgeBeta N + 3 * N ^ 2)
    (prodConst (2 * N) (2 * edgeBeta N + N ^ 2)
      (prodConst N (edgeBeta N) (edgeConst N K M) (edgeConst N K M)) (edgeConst N K M))
    (edgeConst N K M)

theorem prodConst_nonneg {α β E E' : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hE : 0 ≤ E) (hE' : 0 ≤ E') :
    0 ≤ prodConst α β E E' := by
  unfold prodConst; positivity

theorem edgeConst_nonneg {N K M : ℝ} (hN : 0 ≤ N) (hK : 0 ≤ K) (hM : 0 ≤ M) :
    0 ≤ edgeConst N K M := by
  unfold edgeConst; positivity

/-- One edge in the normal form `1 + h a + h² b + O(h³)` used for the plaquette. -/
theorem edge_normalForm {ω : ℝ → 𝔸} {h K M N : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hω : ContinuousOn ω (Icc 0 h)) (hK : ∀ t ∈ Icc 0 h, ‖ω t‖ ≤ K) (hM : 0 ≤ M) {Z₀ Z₁ W : 𝔸}
    (hZ₀ : ‖Z₀‖ ≤ N) (hZ₁ : ‖Z₁‖ ≤ 2 * N) (hW : ‖W‖ ≤ N)
    (hZW : ∀ t ∈ Icc 0 h, ‖ω t - (Z₀ + h • Z₁ + t • W)‖ ≤ M * h ^ 2) {U : ℝ → 𝔸}
    (hU : IsTransport ω 0 h U) (h1 : U 0 = 1) :
    ‖U h - (1 + h • (-Z₀) + h ^ 2 • (-Z₁ + (1 / 2 : ℝ) • (Z₀ * Z₀ - W)))‖ ≤
      edgeConst N K M * h ^ 3 ∧ ‖-Z₀‖ ≤ N ∧
      ‖-Z₁ + (1 / 2 : ℝ) • (Z₀ * Z₀ - W)‖ ≤ edgeBeta N := by
  have hN : 0 ≤ N := (norm_nonneg _).trans hZ₀
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hh⟩)
  refine ⟨(norm_transport_sub_edgeExpansion_le hh hh1 hω hK hM hZW hU h1).trans
    (mul_le_mul_of_nonneg_right ?_ (by positivity)), by rwa [norm_neg], ?_⟩
  · unfold edgeConst
    have : (K + ‖Z₀‖ + ‖Z₁‖) * (‖W‖ + M) ≤ (K + 3 * N) * (N + M) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have : ‖Z₀‖ * ‖Z₁‖ ≤ N * (2 * N) := mul_le_mul hZ₀ hZ₁ (norm_nonneg _) hN
    have : ‖Z₁‖ ^ 2 ≤ (2 * N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hZ₁ 2
    nlinarith
  · unfold edgeBeta
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have : ‖Z₀ * Z₀ - W‖ ≤ N ^ 2 + N := by
      refine (norm_sub_le _ _).trans ?_
      have := (norm_mul_le Z₀ Z₀).trans (mul_le_mul hZ₀ hZ₀ (norm_nonneg _) hN)
      nlinarith
    nlinarith

omit [CompleteSpace 𝔸] in
/-- **Products of four second-order expansions** with explicit constant. -/
theorem norm_prod4_sub_le {u₁ u₂ u₃ u₄ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : 𝔸} {h N E β : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1) (hN : 0 ≤ N) (hE : 0 ≤ E) (hβ : 0 ≤ β)
    (e₁ : ‖u₁ - (1 + h • a₁ + h ^ 2 • b₁)‖ ≤ E * h ^ 3)
    (e₂ : ‖u₂ - (1 + h • a₂ + h ^ 2 • b₂)‖ ≤ E * h ^ 3)
    (e₃ : ‖u₃ - (1 + h • a₃ + h ^ 2 • b₃)‖ ≤ E * h ^ 3)
    (e₄ : ‖u₄ - (1 + h • a₄ + h ^ 2 • b₄)‖ ≤ E * h ^ 3)
    (ha₁ : ‖a₁‖ ≤ N) (ha₂ : ‖a₂‖ ≤ N) (ha₃ : ‖a₃‖ ≤ N) (ha₄ : ‖a₄‖ ≤ N)
    (hb₁ : ‖b₁‖ ≤ β) (hb₂ : ‖b₂‖ ≤ β) (hb₃ : ‖b₃‖ ≤ β) (hb₄ : ‖b₄‖ ≤ β) :
    ‖u₁ * u₂ * u₃ * u₄ - (1 + h • (a₁ + a₂ + a₃ + a₄) +
        h ^ 2 • (b₁ + b₂ + a₁ * a₂ + b₃ + (a₁ + a₂) * a₃ + b₄ + (a₁ + a₂ + a₃) * a₄))‖ ≤
      prodConst (3 * N) (3 * β + 3 * N ^ 2)
        (prodConst (2 * N) (2 * β + N ^ 2) (prodConst N β E E) E) E * h ^ 3 := by
  have s12 := norm_mul_quadratic_sub_le hh hh1 hE e₁ e₂ ha₁ ha₂ hb₁ hb₂
  have hA12 : ‖a₁ + a₂‖ ≤ 2 * N := (norm_add_le _ _).trans (by linarith)
  have hB12 : ‖b₁ + b₂ + a₁ * a₂‖ ≤ 2 * β + N ^ 2 := by
    have := (norm_mul_le a₁ a₂).trans (mul_le_mul ha₁ ha₂ (norm_nonneg _) hN)
    have := norm_add_le (b₁ + b₂) (a₁ * a₂)
    have := norm_add_le b₁ b₂
    nlinarith
  have s123 := norm_mul_quadratic_sub_le (α := 2 * N) (β := 2 * β + N ^ 2) hh hh1
    (prodConst_nonneg hN hβ hE hE) s12 e₃ hA12 (ha₃.trans (by linarith)) hB12
    (hb₃.trans (by nlinarith))
  have hA123 : ‖a₁ + a₂ + a₃‖ ≤ 3 * N := (norm_add_le _ _).trans (by linarith)
  have hB123 : ‖b₁ + b₂ + a₁ * a₂ + b₃ + (a₁ + a₂) * a₃‖ ≤ 3 * β + 3 * N ^ 2 := by
    have := (norm_mul_le (a₁ + a₂) a₃).trans (mul_le_mul hA12 ha₃ (norm_nonneg _) (by linarith))
    have := norm_add_le (b₁ + b₂ + a₁ * a₂ + b₃) ((a₁ + a₂) * a₃)
    have := norm_add_le (b₁ + b₂ + a₁ * a₂) b₃
    nlinarith
  have s1234 := norm_mul_quadratic_sub_le (α := 3 * N) (β := 3 * β + 3 * N ^ 2) hh hh1
    (prodConst_nonneg (by linarith) (by positivity) (prodConst_nonneg hN hβ hE hE) hE) s123 e₄
    hA123 (ha₄.trans (by linarith)) hB123 (hb₄.trans (by nlinarith))
  exact s1234

/-- **The four-edge plaquette of a smooth connection** (`eq:lattice-comparison`, proof of
`prop:mesh-consistency`: `U_{μν}(x) = I + h² 𝔽_{A,μν}(x) + O(h³)`).  Let `X = A_μ(x)`,
`Y = A_ν(x)`, `p = ∂_μA_μ(x)`, `q = ∂_νA_ν(x)`, `r = ∂_μA_ν(x)`, `s = ∂_νA_μ(x)` (all of norm
`≤ N`), and let the four edges of the plaquette carry the coefficients
* `ω₁(t) = -A_μ(x + (h - t)e_μ)` (backward transport `U_μ(x)`),
* `ω₂(t) = -A_ν(x + he_μ + (h - t)e_ν)` (backward transport `U_ν(x + he_μ)`),
* `ω₃(t) = A_μ(x + he_ν + te_μ)` (forward transport `= U_μ(x + he_ν)⁻¹`),
* `ω₄(t) = A_ν(x + te_ν)` (forward transport `= U_ν(x)⁻¹`),
expressed through their first-order Taylor polynomials with remainder `≤ Mh²` and sup bound
`K`.  Then the ordered product of the four exact transports satisfies
`‖U₁(h)U₂(h)U₃(h)U₄(h) - (1 + h²(r - s + [X,Y]))‖ ≤ plaquetteConst N K M · h³`. -/
theorem norm_plaquette_sub_curvature_le {X Y p q r s : 𝔸} {N K M h : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1) (hM : 0 ≤ M) (hX : ‖X‖ ≤ N) (hY : ‖Y‖ ≤ N) (hp : ‖p‖ ≤ N) (hq : ‖q‖ ≤ N)
    (hr : ‖r‖ ≤ N) (hs : ‖s‖ ≤ N) {ω₁ ω₂ ω₃ ω₄ U₁ U₂ U₃ U₄ : ℝ → 𝔸}
    (hc₁ : ContinuousOn ω₁ (Icc 0 h)) (hc₂ : ContinuousOn ω₂ (Icc 0 h))
    (hc₃ : ContinuousOn ω₃ (Icc 0 h)) (hc₄ : ContinuousOn ω₄ (Icc 0 h))
    (hK₁ : ∀ t ∈ Icc 0 h, ‖ω₁ t‖ ≤ K) (hK₂ : ∀ t ∈ Icc 0 h, ‖ω₂ t‖ ≤ K)
    (hK₃ : ∀ t ∈ Icc 0 h, ‖ω₃ t‖ ≤ K) (hK₄ : ∀ t ∈ Icc 0 h, ‖ω₄ t‖ ≤ K)
    (hT₁ : ∀ t ∈ Icc 0 h, ‖ω₁ t - (-X + h • (-p) + t • p)‖ ≤ M * h ^ 2)
    (hT₂ : ∀ t ∈ Icc 0 h, ‖ω₂ t - (-Y + h • (-(r + q)) + t • q)‖ ≤ M * h ^ 2)
    (hT₃ : ∀ t ∈ Icc 0 h, ‖ω₃ t - (X + h • s + t • p)‖ ≤ M * h ^ 2)
    (hT₄ : ∀ t ∈ Icc 0 h, ‖ω₄ t - (Y + h • (0 : 𝔸) + t • q)‖ ≤ M * h ^ 2)
    (hU₁ : IsTransport ω₁ 0 h U₁) (hU₂ : IsTransport ω₂ 0 h U₂) (hU₃ : IsTransport ω₃ 0 h U₃)
    (hU₄ : IsTransport ω₄ 0 h U₄) (h₁ : U₁ 0 = 1) (h₂ : U₂ 0 = 1) (h₃ : U₃ 0 = 1)
    (h₄ : U₄ 0 = 1) :
    ‖U₁ h * U₂ h * U₃ h * U₄ h - (1 + h ^ 2 • (r - s + (X * Y - Y * X)))‖ ≤
      plaquetteConst N K M * h ^ 3 := by
  have hN : 0 ≤ N := (norm_nonneg _).trans hX
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK₁ 0 ⟨le_rfl, hh⟩)
  have hrq : ‖-(r + q)‖ ≤ 2 * N := by rw [norm_neg]; linarith [norm_add_le r q]
  have hs2 : ‖s‖ ≤ 2 * N := by linarith
  have hp2 : ‖-p‖ ≤ 2 * N := by rw [norm_neg]; linarith
  have h02 : ‖(0 : 𝔸)‖ ≤ 2 * N := by rw [norm_zero]; linarith
  obtain ⟨e₁, a₁, b₁⟩ := edge_normalForm hh hh1 hc₁ hK₁ hM (by rwa [norm_neg]) hp2 hp hT₁ hU₁ h₁
  obtain ⟨e₂, a₂, b₂⟩ := edge_normalForm hh hh1 hc₂ hK₂ hM (by rwa [norm_neg]) hrq hq hT₂ hU₂ h₂
  obtain ⟨e₃, a₃, b₃⟩ := edge_normalForm hh hh1 hc₃ hK₃ hM hX hs2 hp hT₃ hU₃ h₃
  obtain ⟨e₄, a₄, b₄⟩ := edge_normalForm hh hh1 hc₄ hK₄ hM hY h02 hq hT₄ hU₄ h₄
  have hβ : 0 ≤ edgeBeta N := by unfold edgeBeta; positivity
  have key := norm_prod4_sub_le hh hh1 hN (edgeConst_nonneg hN hK0 hM) hβ e₁ e₂ e₃ e₄
    a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄
  have hA : -(-X) + -(-Y) + -X + -Y = (0 : 𝔸) := by simp only [neg_neg]; abel
  have hB : (-(-p) + (1 / 2 : ℝ) • (-X * -X - p)) + (-(-(r + q)) + (1 / 2 : ℝ) • (-Y * -Y - q)) +
      -(-X) * -(-Y) + (-s + (1 / 2 : ℝ) • (X * X - p)) + (-(-X) + -(-Y)) * -X +
      (-(0 : 𝔸) + (1 / 2 : ℝ) • (Y * Y - q)) + (-(-X) + -(-Y) + -X) * -Y =
      r - s + (X * Y - Y * X) := by
    simp only [add_mul, mul_neg, neg_mul, neg_neg, smul_sub, neg_zero]
    module
  rw [hA, hB, smul_zero, add_zero] at key
  exact key

/-! ### The logarithmic plaquette `F^h = h⁻² log U_{μν}` -/

open ShiftedPlaquette in
/-- The analytic logarithm near the identity is `z + O(‖z‖²)`:
`‖log(1 + z) - z‖ ≤ ‖z‖²/(1 - ‖z‖)` for `‖z‖ < 1` (`log(1+z) = z L(z)`, `L` the series of
`ShiftedPlaquette`, whose inverse property `exp (log (1 + z)) = 1 + z` is
`ShiftedPlaquette.exp_logOneAdd`). -/
theorem norm_logOneAdd_sub_le {z : 𝔸} (hz : ‖z‖ < 1) :
    ‖logOneAdd z - z‖ ≤ ‖z‖ ^ 2 / (1 - ‖z‖) := by
  have hs := hasSum_logQuotient hz
  have hs1 : HasSum (fun n => logQuotientCoeff (n + 1) • z ^ (n + 1)) (logQuotient z - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hs
    simpa [logQuotientCoeff] using this
  have hg : HasSum (fun n : ℕ => ‖z‖ * ‖z‖ ^ n) (‖z‖ * (1 - ‖z‖)⁻¹) :=
    (hasSum_geometric_of_lt_one (norm_nonneg z) hz).mul_left ‖z‖
  have hb : ‖logQuotient z - 1‖ ≤ ‖z‖ * (1 - ‖z‖)⁻¹ := by
    refine hs1.norm_le_of_bounded hg fun n => ?_
    rw [norm_smul, norm_logQuotientCoeff]
    have h1 : 1 / ((↑(n + 1) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; push_cast; linarith
    calc 1 / ((↑(n + 1) : ℝ) + 1) * ‖z ^ (n + 1)‖ ≤ 1 * ‖z ^ (n + 1)‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ ‖z‖ ^ (n + 1) := by rw [one_mul]; exact norm_pow_le z (n + 1)
      _ = ‖z‖ * ‖z‖ ^ n := by ring
  have e : logOneAdd z - z = z * (logQuotient z - 1) := by
    rw [logOneAdd, mul_sub, mul_one]
  rw [e]
  refine (norm_mul_le _ _).trans ?_
  calc ‖z‖ * ‖logQuotient z - 1‖ ≤ ‖z‖ * (‖z‖ * (1 - ‖z‖)⁻¹) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖z‖ ^ 2 / (1 - ‖z‖) := by ring

open ShiftedPlaquette in
/-- **`F^h = 𝔽 + O(h)`**: if a plaquette product `Pq` satisfies `‖Pq - (1 + h²𝔽)‖ ≤ C h³` with
`‖𝔽‖ ≤ N₂`, `0 < h ≤ 1` and `(N₂ + C) h² ≤ 1/2` (the uniform identity chart), then the logarithmic
plaquette `F^h = h⁻² log Pq` (analytic branch) satisfies `‖F^h - 𝔽‖ ≤ (C + 2(N₂ + C)²) h`. -/
theorem norm_logPlaquette_sub_curvature_le {Pq F : 𝔸} {h C N₂ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hF : ‖F‖ ≤ N₂) (hPq : ‖Pq - (1 + h ^ 2 • F)‖ ≤ C * h ^ 3)
    (hsmall : (N₂ + C) * h ^ 2 ≤ 1 / 2) :
    ‖(h ^ 2)⁻¹ • logOneAdd (Pq - 1) - F‖ ≤ (C + 2 * (N₂ + C) ^ 2) * h := by
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans hPq
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hN₂ : 0 ≤ N₂ := (norm_nonneg _).trans hF
  set z := Pq - 1
  have hz : ‖z‖ ≤ (N₂ + C) * h ^ 2 := by
    have e : z = (Pq - (1 + h ^ 2 • F)) + h ^ 2 • F := by simp only [z]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : C * h ^ 3 ≤ C * h ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hh.le hh1 (by norm_num)) hC
    nlinarith [mul_le_mul_of_nonneg_left hF (sq_nonneg h)]
  have hz1 : ‖z‖ < 1 := by linarith
  have hlog := norm_logOneAdd_sub_le hz1
  have hlog' : ‖logOneAdd z - z‖ ≤ 2 * ((N₂ + C) * h ^ 2) ^ 2 := by
    refine hlog.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : ‖z‖ ^ 2 ≤ ((N₂ + C) * h ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    nlinarith
  have hh2 : (0 : ℝ) < h ^ 2 := by positivity
  have e : (h ^ 2)⁻¹ • logOneAdd z - F =
      (h ^ 2)⁻¹ • ((logOneAdd z - z) + (Pq - (1 + h ^ 2 • F))) := by
    simp only [z, smul_add, smul_sub, smul_smul, inv_mul_cancel₀ hh2.ne', one_smul]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hh2)]
  have hsum : ‖(logOneAdd z - z) + (Pq - (1 + h ^ 2 • F))‖ ≤
      2 * ((N₂ + C) * h ^ 2) ^ 2 + C * h ^ 3 :=
    (norm_add_le _ _).trans (add_le_add hlog' hPq)
  rw [inv_mul_le_iff₀ hh2]
  have : h ^ 4 ≤ h ^ 3 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg (N₂ + C))]

/-! ### Covariant differences: Higgs links and spinor transport -/

section Differences

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Covariant forward difference** (`K^h_μ = h⁻¹(U_μ(x)H(x+he_μ) - H(x)) = D_μH + O(h)`): if
the link satisfies `‖U - (1 + hX)‖ ≤ E h²` and the field `‖H₁ - H₀ - hH'‖ ≤ L h²`, `‖H₁‖ ≤ B`,
then `‖h⁻¹(U H₁ - H₀) - (H' + X H₀)‖ ≤ (E B + L + ‖X‖(‖H'‖ + L)) h` for `0 < h ≤ 1`. -/
theorem norm_covariantForwardDifference_sub_le {U X : F →L[ℝ] F} {H₀ H₁ H' : F}
    {h E L B : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hU : ‖U - (1 + h • X)‖ ≤ E * h ^ 2)
    (hH : ‖H₁ - H₀ - h • H'‖ ≤ L * h ^ 2) (hB : ‖H₁‖ ≤ B) :
    ‖h⁻¹ • (U H₁ - H₀) - (H' + X H₀)‖ ≤ (E * B + L + ‖X‖ * (‖H'‖ + L)) * h := by
  have hL : 0 ≤ L := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hH) (by positivity)
  have e : h⁻¹ • (U H₁ - H₀) - (H' + X H₀) =
      h⁻¹ • ((U - (1 + h • X)) H₁) + h⁻¹ • (H₁ - H₀ - h • H') + X (H₁ - H₀) := by
    simp only [sub_apply, add_apply,
      one_apply_eq_self, smul_apply, map_sub, smul_sub,
      smul_add, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
    abel
  rw [e]
  have h1 : ‖h⁻¹ • ((U - (1 + h • X)) H₁)‖ ≤ E * B * h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hh), inv_mul_le_iff₀ hh]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have hE : 0 ≤ E * h ^ 2 := (norm_nonneg _).trans hU
    calc ‖U - (1 + h • X)‖ * ‖H₁‖ ≤ E * h ^ 2 * B := mul_le_mul hU hB (norm_nonneg _) hE
      _ = h * (E * B * h) := by ring
  have h2 : ‖h⁻¹ • (H₁ - H₀ - h • H')‖ ≤ L * h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hh), inv_mul_le_iff₀ hh]
    exact hH.trans (le_of_eq (by ring))
  have h3 : ‖X (H₁ - H₀)‖ ≤ ‖X‖ * (‖H'‖ + L) * h := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have : ‖H₁ - H₀‖ ≤ (‖H'‖ + L) * h := by
      have e2 : H₁ - H₀ = (H₁ - H₀ - h • H') + h • H' := by abel
      rw [e2]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      have : L * h ^ 2 ≤ L * h := mul_le_mul_of_nonneg_left (by nlinarith) hL
      nlinarith
    calc ‖X‖ * ‖H₁ - H₀‖ ≤ ‖X‖ * ((‖H'‖ + L) * h) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖X‖ * (‖H'‖ + L) * h := by ring
  calc _ ≤ ‖h⁻¹ • ((U - (1 + h • X)) H₁)‖ + ‖h⁻¹ • (H₁ - H₀ - h • H')‖ + ‖X (H₁ - H₀)‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ E * B * h + L * h + ‖X‖ * (‖H'‖ + L) * h := by gcongr
    _ = _ := by ring

/-- **Centred covariant spinor difference** (`eq:spin-difference`):
`(𝒰_μ(x)Ψ(x+he_μ) - 𝒰_μ(x-he_μ)⁻¹Ψ(x-he_μ))/(2h) = ∇_μΨ + O(h)`.  If the backward link
`‖Up - (1 + hX)‖ ≤ E h²`, the inverse of the previous backward link `‖Um - (1 - hX)‖ ≤ E h²`, and
`‖Ψp - Ψ₀ - hΨ'‖ ≤ L h²`, `‖Ψm - Ψ₀ + hΨ'‖ ≤ L h²`, `‖Ψ±‖ ≤ B`, then
`‖(2h)⁻¹(UpΨp - UmΨm) - (Ψ' + XΨ₀)‖ ≤ (E B + L + ‖X‖ L) h`. -/
theorem norm_covariantCentredDifference_sub_le {Up Um X : F →L[ℝ] F} {Ψ₀ Ψp Ψm Ψ' : F}
    {h E L B : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hUp : ‖Up - (1 + h • X)‖ ≤ E * h ^ 2)
    (hUm : ‖Um - (1 - h • X)‖ ≤ E * h ^ 2) (hΨp : ‖Ψp - Ψ₀ - h • Ψ'‖ ≤ L * h ^ 2)
    (hΨm : ‖Ψm - Ψ₀ + h • Ψ'‖ ≤ L * h ^ 2) (hBp : ‖Ψp‖ ≤ B) (hBm : ‖Ψm‖ ≤ B) :
    ‖(2 * h)⁻¹ • (Up Ψp - Um Ψm) - (Ψ' + X Ψ₀)‖ ≤ (E * B + L + ‖X‖ * L) * h := by
  have hE : 0 ≤ E * h ^ 2 := (norm_nonneg _).trans hUp
  have h2 : (0 : ℝ) < 2 * h := by positivity
  have e : (2 * h)⁻¹ • (Up Ψp - Um Ψm) - (Ψ' + X Ψ₀) =
      (2 * h)⁻¹ • ((Up - (1 + h • X)) Ψp - (Um - (1 - h • X)) Ψm +
        ((Ψp - Ψ₀ - h • Ψ') - (Ψm - Ψ₀ + h • Ψ')) +
        h • X ((Ψp - Ψ₀ - h • Ψ') + (Ψm - Ψ₀ + h • Ψ'))) := by
    have : (2 * h)⁻¹ • ((2 * h) • (Ψ' + X Ψ₀)) = Ψ' + X Ψ₀ := by
      rw [smul_smul, inv_mul_cancel₀ h2.ne', one_smul]
    rw [← this, ← smul_sub]
    congr 1
    simp only [sub_apply, add_apply,
      one_apply_eq_self, smul_apply, map_sub, map_add,
      map_smul, smul_add, smul_sub, two_mul, add_smul]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 h2), inv_mul_le_iff₀ h2]
  have t1 : ‖(Up - (1 + h • X)) Ψp‖ ≤ E * h ^ 2 * B :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hUp hBp (norm_nonneg _) hE)
  have t2 : ‖(Um - (1 - h • X)) Ψm‖ ≤ E * h ^ 2 * B :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hUm hBm (norm_nonneg _) hE)
  have t3 : ‖(Ψp - Ψ₀ - h • Ψ') - (Ψm - Ψ₀ + h • Ψ')‖ ≤ 2 * (L * h ^ 2) :=
    (norm_sub_le _ _).trans (by linarith)
  have t4 : ‖h • X ((Ψp - Ψ₀ - h • Ψ') + (Ψm - Ψ₀ + h • Ψ'))‖ ≤ h * (‖X‖ * (2 * (L * h ^ 2))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    refine mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans ?_) hh.le
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _)
  have hL : 0 ≤ L * h ^ 2 := (norm_nonneg _).trans hΨp
  calc _ ≤ ‖(Up - (1 + h • X)) Ψp‖ + ‖(Um - (1 - h • X)) Ψm‖ +
        ‖(Ψp - Ψ₀ - h • Ψ') - (Ψm - Ψ₀ + h • Ψ')‖ +
        ‖h • X ((Ψp - Ψ₀ - h • Ψ') + (Ψm - Ψ₀ + h • Ψ'))‖ :=
        (norm_add_le _ _).trans (add_le_add_left ((norm_add_le _ _).trans
          (add_le_add_left (norm_sub_le _ _) _)) _) |>.trans (le_of_eq (by ring))
    _ ≤ E * h ^ 2 * B + E * h ^ 2 * B + 2 * (L * h ^ 2) + h * (‖X‖ * (2 * (L * h ^ 2))) := by
        gcongr
    _ = 2 * h * ((E * B + L + ‖X‖ * L * h) * h) := by ring
    _ ≤ 2 * h * ((E * B + L + ‖X‖ * L) * h) := by
        have hL0 : 0 ≤ L := nonneg_of_mul_nonneg_left hL (by positivity)
        have : ‖X‖ * L * h ≤ ‖X‖ * L := mul_le_of_le_one_right (by positivity) hh1
        gcongr

end Differences

/-! ### Links of a smooth connection on a normed space -/

section Concrete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **First-order Taylor bound** for a map with `L`-Lipschitz derivative:
`‖f(x + u) - f(x) - f'(x)u‖ ≤ L ‖u‖²`. -/
theorem norm_sub_sub_fderiv_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} {f' : E → E →L[ℝ] G} {L : ℝ} (hf : ∀ y, HasFDerivAt f (f' y) y)
    (hL : ∀ y z, ‖f' y - f' z‖ ≤ L * ‖y - z‖) (x u : E) :
    ‖f (x + u) - f x - f' x u‖ ≤ L * ‖u‖ ^ 2 := by
  have hL0 : 0 ≤ L ∨ u = 0 := by
    by_cases hu : u = 0
    · exact Or.inr hu
    · left
      have := (norm_nonneg _).trans (hL (x + u) x)
      rw [add_sub_cancel_left] at this
      exact nonneg_of_mul_nonneg_left this (norm_pos_iff.2 hu)
  rcases hL0 with hL0 | hu
  swap
  · subst hu; simp
  set g : E → G := fun y => f y - f' x (y - x)
  have hg : ∀ y ∈ Metric.closedBall x ‖u‖, HasFDerivWithinAt g (f' y - f' x)
      (Metric.closedBall x ‖u‖) y := by
    intro y _
    have h2 : HasFDerivAt (fun y => f' x (y - x)) (f' x) y :=
      ((f' x).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)).congr_fderiv
        (ContinuousLinearMap.comp_id _)
    exact ((hf y).sub h2).hasFDerivWithinAt
  have hbd : ∀ y ∈ Metric.closedBall x ‖u‖, ‖f' y - f' x‖ ≤ L * ‖u‖ := fun y hy =>
    (hL y x).trans (mul_le_mul_of_nonneg_left (by rwa [Metric.mem_closedBall, dist_eq_norm] at hy)
      hL0)
  have := (convex_closedBall x ‖u‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbd
    (Metric.mem_closedBall_self (norm_nonneg u))
    (by rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left])
  simp only [g, add_sub_cancel_left, sub_self, map_zero, sub_zero] at this
  calc ‖f (x + u) - f x - f' x u‖ = ‖f (x + u) - f' x u - f x‖ := by congr 1; abel
    _ ≤ L * ‖u‖ * ‖u‖ := this
    _ = L * ‖u‖ ^ 2 := by ring

open Classical in
/-- **The backward link** `U(x) = P_{x ← x + he}`: the transport, along the reversed edge, of the
coefficient `t ↦ -A(x + (h - t)e)` (`eq:lattice-comparison`, "backward parallel transport from
`x + he_μ` to `x`"), evaluated at `t = h`. -/
def backwardLink (A : E → 𝔸) (e x : E) (h : ℝ) : 𝔸 :=
  if hex : ∃ U : ℝ → 𝔸, U 0 = 1 ∧ IsTransport (fun t => -A (x + (h - t) • e)) 0 h U then
    hex.choose h
  else 1

open Classical in
/-- **The forward link** `P_{x + he ← x}`: the transport of `t ↦ A(x + te)` at `t = h`. -/
def forwardLink (A : E → 𝔸) (e x : E) (h : ℝ) : 𝔸 :=
  if hex : ∃ U : ℝ → 𝔸, U 0 = 1 ∧ IsTransport (fun t => A (x + t • e)) 0 h U then
    hex.choose h
  else 1

theorem exists_backwardLink {A : E → 𝔸} (hA : Continuous A) {K : ℝ} (hK : ∀ y, ‖A y‖ ≤ K)
    (e x : E) {h : ℝ} (hh : 0 ≤ h) :
    ∃ U : ℝ → 𝔸, U 0 = 1 ∧ IsTransport (fun t => -A (x + (h - t) • e)) 0 h U ∧
      backwardLink A e x h = U h := by
  have hex : ∃ U : ℝ → 𝔸, U 0 = 1 ∧ IsTransport (fun t => -A (x + (h - t) • e)) 0 h U :=
    CovariantQuadrature.exists_transport_of_le hh (by fun_prop) (fun t _ => by
      rw [norm_neg]; exact hK _) 1
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  rw [backwardLink, dite_eq_left hex]

theorem exists_forwardLink {A : E → 𝔸} (hA : Continuous A) {K : ℝ} (hK : ∀ y, ‖A y‖ ≤ K)
    (e x : E) {h : ℝ} (hh : 0 ≤ h) :
    ∃ U : ℝ → 𝔸, U 0 = 1 ∧ IsTransport (fun t => A (x + t • e)) 0 h U ∧
      forwardLink A e x h = U h := by
  have hex : ∃ U : ℝ → 𝔸, U 0 = 1 ∧ IsTransport (fun t => A (x + t • e)) 0 h U :=
    CovariantQuadrature.exists_transport_of_le hh (by fun_prop) (fun t _ => hK _) 1
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  rw [forwardLink, dite_eq_left hex]

/-- The inverse of the backward link is the forward link: `U_μ(x)⁻¹ = P_{x+he_μ ← x}`. -/
theorem ring_inverse_backwardLink {A : E → 𝔸} (hA : Continuous A) {K : ℝ}
    (hK : ∀ y, ‖A y‖ ≤ K) (e x : E) {h : ℝ} (hh : 0 ≤ h) :
    Ring.inverse (backwardLink A e x h) = forwardLink A e x h := by
  obtain ⟨R, hR0, hR, hRe⟩ := exists_backwardLink hA hK e x hh
  obtain ⟨P, hP0, hP, hPe⟩ := exists_forwardLink hA hK e x hh
  rw [hRe, hPe]
  exact ring_inverse_reverse_transport (K := K) hh (fun t _ => hK _) hP hP0
    (by simpa using hR) hR0

/-- **The plaquette of a smooth connection** (`eq:lattice-comparison`):
for `A_μ, A_ν` bounded by `K` with derivatives bounded by `D` and `L`-Lipschitz, unit-bounded
directions `e_μ, e_ν` and `0 ≤ h ≤ 1`,
`‖U_μ(x)U_ν(x+he_μ)U_μ(x+he_ν)⁻¹U_ν(x)⁻¹ - (1 + h²𝔽_{μν}(x))‖ ≤ C h³` with
`𝔽_{μν} = ∂_μA_ν - ∂_νA_μ + [A_μ, A_ν]` and `C = plaquetteConst (max K D) K (4L)`. -/
theorem norm_linkPlaquette_sub_curvature_le {Aμ Aν : E → 𝔸} {Aμ' Aν' : E → E →L[ℝ] 𝔸}
    {K D L : ℝ} (hAμ : ∀ y, HasFDerivAt Aμ (Aμ' y) y) (hAν : ∀ y, HasFDerivAt Aν (Aν' y) y)
    (hKμ : ∀ y, ‖Aμ y‖ ≤ K) (hKν : ∀ y, ‖Aν y‖ ≤ K) (hDμ : ∀ y, ‖Aμ' y‖ ≤ D)
    (hDν : ∀ y, ‖Aν' y‖ ≤ D) (hLμ : ∀ y z, ‖Aμ' y - Aμ' z‖ ≤ L * ‖y - z‖)
    (hLν : ∀ y z, ‖Aν' y - Aν' z‖ ≤ L * ‖y - z‖) {eμ eν : E} (heμ : ‖eμ‖ ≤ 1)
    (heν : ‖eν‖ ≤ 1) (hL : 0 ≤ L) (x : E) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ‖backwardLink Aμ eμ x h * backwardLink Aν eν (x + h • eμ) h *
        Ring.inverse (backwardLink Aμ eμ (x + h • eν) h) *
        Ring.inverse (backwardLink Aν eν x h) -
      (1 + h ^ 2 • (Aν' x eμ - Aμ' x eν + (Aμ x * Aν x - Aν x * Aμ x)))‖ ≤
      plaquetteConst (max K D) K (4 * L) * h ^ 3 := by
  have hcμ : Continuous Aμ := continuous_iff_continuousAt.2 fun y => (hAμ y).continuousAt
  have hcν : Continuous Aν := continuous_iff_continuousAt.2 fun y => (hAν y).continuousAt
  rw [ring_inverse_backwardLink hcμ hKμ eμ (x + h • eν) hh,
    ring_inverse_backwardLink hcν hKν eν x hh]
  obtain ⟨U₁, h₁, hU₁, e₁⟩ := exists_backwardLink hcμ hKμ eμ x hh
  obtain ⟨U₂, h₂, hU₂, e₂⟩ := exists_backwardLink hcν hKν eν (x + h • eμ) hh
  obtain ⟨U₃, h₃, hU₃, e₃⟩ := exists_forwardLink hcμ hKμ eμ (x + h • eν) hh
  obtain ⟨U₄, h₄, hU₄, e₄⟩ := exists_forwardLink hcν hKν eν x hh
  rw [e₁, e₂, e₃, e₄]
  have hN : ∀ {T : E →L[ℝ] 𝔸} {e : E}, ‖T‖ ≤ D → ‖e‖ ≤ 1 → ‖T e‖ ≤ max K D := fun {T} {e} hT he =>
    (T.le_opNorm e).trans ((mul_le_mul hT he (norm_nonneg _) ((norm_nonneg _).trans hT)).trans
      (by rw [mul_one]; exact le_max_right _ _))
  have hTay : ∀ {f : E → 𝔸} {f' : E → E →L[ℝ] 𝔸}, (∀ y, HasFDerivAt f (f' y) y) →
      (∀ y z, ‖f' y - f' z‖ ≤ L * ‖y - z‖) → ∀ u : E, ‖u‖ ≤ 2 * h →
      ‖f (x + u) - f x - f' x u‖ ≤ 4 * L * h ^ 2 := fun hf hfL u hu =>
    (norm_sub_sub_fderiv_le hf hfL x u).trans (by
      have : ‖u‖ ^ 2 ≤ (2 * h) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
      nlinarith)
  have hu1 : ∀ {a b : ℝ} {e e' : E}, 0 ≤ a → a ≤ h → 0 ≤ b → b ≤ h → ‖e‖ ≤ 1 → ‖e'‖ ≤ 1 →
      ‖a • e + b • e'‖ ≤ 2 * h := fun {a b e e'} ha ha' hb hb' he he' => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
      abs_of_nonneg hb]
    nlinarith [norm_nonneg e, norm_nonneg e']
  refine norm_plaquette_sub_curvature_le (N := max K D) (K := K) (M := 4 * L) hh hh1
    (by positivity) ((hKμ x).trans (le_max_left _ _)) ((hKν x).trans (le_max_left _ _))
    (hN (hDμ x) heμ) (hN (hDν x) heν) (hN (hDν x) heμ) (hN (hDμ x) heν)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun t _ => by rw [norm_neg]; exact hKμ _) (fun t _ => by rw [norm_neg]; exact hKν _)
    (fun t _ => hKμ _) (fun t _ => hKν _) ?_ ?_ ?_ ?_ hU₁ hU₂ hU₃ hU₄ h₁ h₂ h₃ h₄
  · intro t ht
    have := hTay hAμ hLμ ((h - t) • eμ + (0 : ℝ) • eν)
      (hu1 (by linarith [ht.2]) (by linarith [ht.1]) le_rfl hh heμ heν)
    simp only [zero_smul, add_zero, map_smul] at this
    calc ‖-Aμ (x + (h - t) • eμ) - (-Aμ x + h • -Aμ' x eμ + t • Aμ' x eμ)‖
        = ‖Aμ (x + (h - t) • eμ) - Aμ x - (h - t) • Aμ' x eμ‖ := by
          rw [← norm_neg]; congr 1; module
      _ ≤ 4 * L * h ^ 2 := this
  · intro t ht
    have := hTay hAν hLν (h • eμ + (h - t) • eν)
      (hu1 hh le_rfl (by linarith [ht.2]) (by linarith [ht.1]) heμ heν)
    simp only [map_add, map_smul] at this
    calc ‖-Aν (x + h • eμ + (h - t) • eν) -
          (-Aν x + h • -(Aν' x eμ + Aν' x eν) + t • Aν' x eν)‖
        = ‖Aν (x + (h • eμ + (h - t) • eν)) - Aν x - (h • Aν' x eμ + (h - t) • Aν' x eν)‖ := by
          rw [← norm_neg, add_assoc]; congr 1; module
      _ ≤ 4 * L * h ^ 2 := this
  · intro t ht
    have := hTay hAμ hLμ (h • eν + t • eμ) (hu1 hh le_rfl ht.1 ht.2 heν heμ)
    simp only [map_add, map_smul] at this
    calc ‖Aμ (x + h • eν + t • eμ) - (Aμ x + h • Aμ' x eν + t • Aμ' x eμ)‖
        = ‖Aμ (x + (h • eν + t • eμ)) - Aμ x - (h • Aμ' x eν + t • Aμ' x eμ)‖ := by
          rw [add_assoc]; congr 1; module
      _ ≤ 4 * L * h ^ 2 := this
  · intro t ht
    have := hTay hAν hLν (t • eν + (0 : ℝ) • eμ) (hu1 ht.1 ht.2 le_rfl hh heν heμ)
    simp only [zero_smul, add_zero, map_smul] at this
    calc ‖Aν (x + t • eν) - (Aν x + h • (0 : 𝔸) + t • Aν' x eν)‖
        = ‖Aν (x + t • eν) - Aν x - t • Aν' x eν‖ := by
          rw [smul_zero, add_zero]; congr 1; module
      _ ≤ 4 * L * h ^ 2 := this

omit [NormedSpace ℝ E] in
/-- A Lipschitz map (constant `Λ ≥ 0`, stated with norms) is continuous. -/
theorem continuous_of_norm_sub_le {G : Type*} [NormedAddCommGroup G] {A : E → G} {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hA : ∀ y z, ‖A y - A z‖ ≤ Λ * ‖y - z‖) : Continuous A :=
  (LipschitzWith.of_dist_le_mul (K := Λ.toNNReal) fun y z => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hΛ]; exact hA y z).continuous

/-- First-order expansion of the backward link `U(x) = 1 + hA(x) + O(h²)` for a bounded
`Λ`-Lipschitz connection component (proof of `prop:mesh-consistency`). -/
theorem norm_backwardLink_sub_le {A : E → 𝔸} {K Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hA : ∀ y z, ‖A y - A z‖ ≤ Λ * ‖y - z‖)
    (hK : ∀ y, ‖A y‖ ≤ K) {e : E} (he : ‖e‖ ≤ 1) (x : E) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ‖backwardLink A e x h - (1 + h • A x)‖ ≤ (K ^ 2 * Real.exp K + Λ) * h ^ 2 := by
  have hc : Continuous A := continuous_of_norm_sub_le hΛ hA
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  obtain ⟨U, h1, hU, hUe⟩ := exists_backwardLink hc hK e x hh
  rw [hUe]
  have hlin := norm_transport_sub_linear_le (ω := fun t => -A (x + (h - t) • e)) (K := K)
    (m := Λ * h) (Z := -A x) hh (by fun_prop) (fun t _ => by rw [norm_neg]; exact hK _)
    (fun t ht => by
      rw [neg_sub_neg, norm_sub_rev]
      refine (hA _ _).trans ?_
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      refine mul_le_mul_of_nonneg_left ?_ hΛ
      nlinarith [ht.1, ht.2, norm_nonneg e]) hU h1
  rw [smul_neg, sub_neg_eq_add] at hlin
  refine hlin.trans ?_
  have : Real.exp (K * h) ≤ Real.exp K := Real.exp_le_exp.2 (mul_le_of_le_one_right hK0 hh1)
  have : K ^ 2 * Real.exp (K * h) * h ^ 2 ≤ K ^ 2 * Real.exp K * h ^ 2 := by gcongr
  nlinarith

/-- First-order expansion of the forward link `P_{x+he←x} = 1 - hA(x) + O(h²)` (the inverse of the
backward link, `ring_inverse_backwardLink`). -/
theorem norm_forwardLink_sub_le {A : E → 𝔸} {K Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hA : ∀ y z, ‖A y - A z‖ ≤ Λ * ‖y - z‖)
    (hK : ∀ y, ‖A y‖ ≤ K) {e : E} (he : ‖e‖ ≤ 1) (x : E) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ‖forwardLink A e x h - (1 - h • A x)‖ ≤ (K ^ 2 * Real.exp K + Λ) * h ^ 2 := by
  have hc : Continuous A := continuous_of_norm_sub_le hΛ hA
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  obtain ⟨U, h1, hU, hUe⟩ := exists_forwardLink hc hK e x hh
  rw [hUe]
  have hlin := norm_transport_sub_linear_le (ω := fun t => A (x + t • e)) (K := K)
    (m := Λ * h) (Z := A x) hh (by fun_prop) (fun t _ => hK _)
    (fun t ht => by
      refine (hA _ _).trans ?_
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      refine mul_le_mul_of_nonneg_left ?_ hΛ
      nlinarith [ht.1, ht.2, norm_nonneg e]) hU h1
  refine hlin.trans ?_
  have : Real.exp (K * h) ≤ Real.exp K := Real.exp_le_exp.2 (mul_le_of_le_one_right hK0 hh1)
  have : K ^ 2 * Real.exp (K * h) * h ^ 2 ≤ K ^ 2 * Real.exp K * h ^ 2 := by gcongr
  nlinarith

end Concrete

/-! ### Concrete consistency of `F^h`, `K^h` and the spinor difference -/

section ConcreteSectors

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open ShiftedPlaquette in
/-- **`F^h_{μν} = 𝔽_{μν} + O(h)` for the transport plaquette of a smooth connection**
(`eq:lattice-comparison`, proof of `prop:mesh-consistency`): with the hypotheses of
`norm_linkPlaquette_sub_curvature_le`, `0 < h ≤ 1` and the identity-chart smallness
`(2D + 2K² + C) h² ≤ 1/2` (`C = plaquetteConst (max K D) K (4L)`),
`‖h⁻² log(U_μ(x)U_ν(x+he_μ)U_μ(x+he_ν)⁻¹U_ν(x)⁻¹) - 𝔽_{μν}(x)‖ ≤ (C + 2(2D + 2K² + C)²) h`. -/
theorem norm_linkLogPlaquette_sub_curvature_le {Aμ Aν : E → 𝔸} {Aμ' Aν' : E → E →L[ℝ] 𝔸}
    {K D L : ℝ} (hAμ : ∀ y, HasFDerivAt Aμ (Aμ' y) y) (hAν : ∀ y, HasFDerivAt Aν (Aν' y) y)
    (hKμ : ∀ y, ‖Aμ y‖ ≤ K) (hKν : ∀ y, ‖Aν y‖ ≤ K) (hDμ : ∀ y, ‖Aμ' y‖ ≤ D)
    (hDν : ∀ y, ‖Aν' y‖ ≤ D) (hLμ : ∀ y z, ‖Aμ' y - Aμ' z‖ ≤ L * ‖y - z‖)
    (hLν : ∀ y z, ‖Aν' y - Aν' z‖ ≤ L * ‖y - z‖) {eμ eν : E} (heμ : ‖eμ‖ ≤ 1)
    (heν : ‖eν‖ ≤ 1) (hL : 0 ≤ L) (x : E) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hsmall : (2 * D + 2 * K ^ 2 + plaquetteConst (max K D) K (4 * L)) * h ^ 2 ≤ 1 / 2) :
    ‖(h ^ 2)⁻¹ • logOneAdd (backwardLink Aμ eμ x h * backwardLink Aν eν (x + h • eμ) h *
        Ring.inverse (backwardLink Aμ eμ (x + h • eν) h) *
        Ring.inverse (backwardLink Aν eν x h) - 1) -
      (Aν' x eμ - Aμ' x eν + (Aμ x * Aν x - Aν x * Aμ x))‖ ≤
      (plaquetteConst (max K D) K (4 * L) +
        2 * (2 * D + 2 * K ^ 2 + plaquetteConst (max K D) K (4 * L)) ^ 2) * h := by
  have hP := norm_linkPlaquette_sub_curvature_le hAμ hAν hKμ hKν hDμ hDν hLμ hLν heμ heν hL x
    hh.le hh1
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hKμ x)
  have hF : ‖Aν' x eμ - Aμ' x eν + (Aμ x * Aν x - Aν x * Aμ x)‖ ≤ 2 * D + 2 * K ^ 2 := by
    have a1 : ‖Aν' x eμ‖ ≤ D := ((Aν' x).le_opNorm _).trans
      ((mul_le_mul (hDν x) heμ (norm_nonneg _) ((norm_nonneg _).trans (hDν x))).trans
        (by rw [mul_one]))
    have a2 : ‖Aμ' x eν‖ ≤ D := ((Aμ' x).le_opNorm _).trans
      ((mul_le_mul (hDμ x) heν (norm_nonneg _) ((norm_nonneg _).trans (hDμ x))).trans
        (by rw [mul_one]))
    have a3 : ‖Aμ x * Aν x‖ ≤ K ^ 2 :=
      (norm_mul_le _ _).trans ((mul_le_mul (hKμ x) (hKν x) (norm_nonneg _) hK0).trans
        (le_of_eq (by ring)))
    have a4 : ‖Aν x * Aμ x‖ ≤ K ^ 2 :=
      (norm_mul_le _ _).trans ((mul_le_mul (hKν x) (hKμ x) (norm_nonneg _) hK0).trans
        (le_of_eq (by ring)))
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le (Aν' x eμ) (Aμ' x eν)
    have := norm_sub_le (Aμ x * Aν x) (Aν x * Aμ x)
    linarith
  exact norm_logPlaquette_sub_curvature_le hh hh1 hF hP hsmall

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]

/-- **Higgs links** (`eq:lattice-comparison`, `K^h_μ = h⁻¹(U_μ(x)H(x+he_μ) - H(x)) = D_μH + O(h)`):
for a represented connection component `A : E → End F` (bounded by `K`, `Λ`-Lipschitz) and a
Higgs field `H` with `L`-Lipschitz derivative and `‖H‖ ≤ B`,
`‖h⁻¹(U(x)H(x+he) - H(x)) - (dH(x)e + A(x)H(x))‖ ≤ ((K²e^K + Λ)B + L + K(‖dH(x)e‖ + L)) h`. -/
theorem norm_higgsLink_sub_covDeriv_le {A : E → F →L[ℝ] F} {H : E → F} {H' : E → E →L[ℝ] F}
    {K Λ L B : ℝ} (hΛ : 0 ≤ Λ) (hA : ∀ y z, ‖A y - A z‖ ≤ Λ * ‖y - z‖) (hK : ∀ y, ‖A y‖ ≤ K)
    (hH : ∀ y, HasFDerivAt H (H' y) y) (hHL : ∀ y z, ‖H' y - H' z‖ ≤ L * ‖y - z‖)
    (hL : 0 ≤ L) (hB : ∀ y, ‖H y‖ ≤ B) {e : E} (he : ‖e‖ ≤ 1) (x : E) {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) :
    ‖h⁻¹ • (backwardLink A e x h (H (x + h • e)) - H x) - (H' x e + A x (H x))‖ ≤
      ((K ^ 2 * Real.exp K + Λ) * B + L + K * (‖H' x e‖ + L)) * h := by
  have hU := norm_backwardLink_sub_le hΛ hA hK he x hh.le hh1
  have hT : ‖H (x + h • e) - H x - h • H' x e‖ ≤ L * h ^ 2 := by
    have := norm_sub_sub_fderiv_le hH hHL x (h • e)
    rw [map_smul] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hL)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh, mul_pow]
    nlinarith [norm_nonneg e, pow_le_one₀ (norm_nonneg e) he (n := 2)]
  have := norm_covariantForwardDifference_sub_le hh hh1 hU hT (hB _)
  refine this.trans (mul_le_mul_of_nonneg_right ?_ hh.le)
  have : ‖A x‖ * (‖H' x e‖ + L) ≤ K * (‖H' x e‖ + L) :=
    mul_le_mul_of_nonneg_right (hK x) (by positivity)
  linarith

/-- **Spinor transport** (`eq:spin-difference`): the centred covariant difference
`(2h)⁻¹(𝒰(x)Ψ(x+he) - 𝒰(x-he)⁻¹Ψ(x-he))` of a spinor field with `L`-Lipschitz derivative
(`‖Ψ‖ ≤ B`) along a bounded `Λ`-Lipschitz spin–gauge connection component `A` differs from
`∇Ψ = dΨ(x)e + A(x)Ψ(x)` by at most `((K²e^K + 2Λ)B + L + K L) h`. -/
theorem norm_spinDifference_sub_covDeriv_le {A : E → F →L[ℝ] F} {Ψ : E → F}
    {Ψ' : E → E →L[ℝ] F} {K Λ L B : ℝ} (hΛ : 0 ≤ Λ) (hA : ∀ y z, ‖A y - A z‖ ≤ Λ * ‖y - z‖)
    (hK : ∀ y, ‖A y‖ ≤ K) (hΨ : ∀ y, HasFDerivAt Ψ (Ψ' y) y)
    (hΨL : ∀ y z, ‖Ψ' y - Ψ' z‖ ≤ L * ‖y - z‖) (hL : 0 ≤ L) (hB : ∀ y, ‖Ψ y‖ ≤ B) {e : E}
    (he : ‖e‖ ≤ 1) (x : E) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ‖(2 * h)⁻¹ • (backwardLink A e x h (Ψ (x + h • e)) -
        Ring.inverse (backwardLink A e (x - h • e) h) (Ψ (x - h • e))) - (Ψ' x e + A x (Ψ x))‖ ≤
      ((K ^ 2 * Real.exp K + 2 * Λ) * B + L + K * L) * h := by
  have hc : Continuous A := continuous_of_norm_sub_le hΛ hA
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  rw [ring_inverse_backwardLink hc hK e (x - h • e) hh.le]
  have hUp := norm_backwardLink_sub_le hΛ hA hK he x hh.le hh1
  have hUm0 := norm_forwardLink_sub_le hΛ hA hK he (x - h • e) hh.le hh1
  have hUm : ‖forwardLink A e (x - h • e) h - (1 - h • A x)‖ ≤
      (K ^ 2 * Real.exp K + 2 * Λ) * h ^ 2 := by
    have e1 : forwardLink A e (x - h • e) h - (1 - h • A x) =
        (forwardLink A e (x - h • e) h - (1 - h • A (x - h • e))) -
          h • (A (x - h • e) - A x) := by
      rw [smul_sub]; abel
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    have : ‖h • (A (x - h • e) - A x)‖ ≤ Λ * h ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      refine (mul_le_mul_of_nonneg_left (hA _ _) hh.le).trans ?_
      rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      nlinarith [norm_nonneg e, mul_le_mul_of_nonneg_left he (mul_nonneg hΛ hh.le)]
    nlinarith
  have hUp' : ‖backwardLink A e x h - (1 + h • A x)‖ ≤ (K ^ 2 * Real.exp K + 2 * Λ) * h ^ 2 :=
    hUp.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hTp : ‖Ψ (x + h • e) - Ψ x - h • Ψ' x e‖ ≤ L * h ^ 2 := by
    have := norm_sub_sub_fderiv_le hΨ hΨL x (h • e)
    rw [map_smul] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hL)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh, mul_pow]
    nlinarith [norm_nonneg e, pow_le_one₀ (norm_nonneg e) he (n := 2)]
  have hTm : ‖Ψ (x - h • e) - Ψ x + h • Ψ' x e‖ ≤ L * h ^ 2 := by
    have := norm_sub_sub_fderiv_le hΨ hΨL x (-(h • e))
    rw [map_neg, map_smul, ← sub_eq_add_neg, sub_neg_eq_add] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hL)
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh, mul_pow]
    nlinarith [norm_nonneg e, pow_le_one₀ (norm_nonneg e) he (n := 2)]
  have := norm_covariantCentredDifference_sub_le hh hh1 hUp' hUm hTp hTm (hB _) (hB _)
  refine this.trans (mul_le_mul_of_nonneg_right ?_ hh.le)
  have : ‖A x‖ * L ≤ K * L := mul_le_mul_of_nonneg_right (hK x) hL
  linarith

end ConcreteSectors

end RenewalGeometry.TransportPlaquetteConsistency
