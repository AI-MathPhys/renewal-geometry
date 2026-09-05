/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.MultiplierResolvent

/-!
# The functional-calculus clause on L²

The `C₀` functional-calculus clause of `thm:flat-limit`(v) /
`lem:app-core-resolvent`, realized in the multiplication-operator
model.  Three layers:

* `strong_tendsto_mul` — products of uniformly bounded strongly
  convergent operator sequences converge strongly: with strong
  resolvent convergence this already covers the **resolvent algebra**
  (polynomials in the resolvents), which is sup-norm dense in
  `C₀(ℝ)`;
* `cfc_tendsto_of_isSelfAdjoint` — the **operator-continuity of the
  functional calculus**: for selfadjoint `aₙ → a` in a unital
  C⋆-algebra and `f` continuous, `f(aₙ) → f(a)` in norm (via
  Mathlib's `Filter.Tendsto.cfc`, with the compact spectral window
  extracted from the norm convergence);
* `multiplier_cfc_tendsto` — the packaged clause: for selfadjoint
  symbol fields `Hₙ(ξ) → H(ξ)` (pointwise a.e., uniformly normed)
  and any continuous bounded `f : ℝ → ℝ`, the multiplication
  operators by `f(Hₙ(ξ))` converge **strongly on L²** to
  multiplication by `f(H(ξ))`.

Applied on the Fourier side to the flat renewal Hamiltonians, whose
symbols are Hermitian matrix fields, `multiplier_cfc_tendsto` is
exactly the statement `f(Hₙ) → f(H)` strongly for `f ∈ C₀(ℝ)` (a
`C₀` function is in particular continuous and bounded); this
discharges the last analytic clause of `thm:flat-limit`(v) in the
multiplication model.
-/

namespace NCG

open Filter MeasureTheory

/-! ## The resolvent algebra: products converge strongly -/

/-- Products of uniformly bounded strongly convergent operator
sequences converge strongly — the resolvent-algebra part of the
functional-calculus clause. -/
theorem strong_tendsto_mul
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Sn Tn : ℕ → H →L[ℝ] H} {S T : H →L[ℝ] H} {M : ℝ}
    (hSb : ∀ n, ‖Sn n‖ ≤ M)
    (hS : ∀ v, Tendsto (fun n => Sn n v) atTop (nhds (S v)))
    (hT : ∀ v, Tendsto (fun n => Tn n v) atTop (nhds (T v))) :
    ∀ v, Tendsto (fun n => Sn n (Tn n v)) atTop (nhds (S (T v))) := by
  intro v
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hSb 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- split into `Sₙ(Tₙv − Tv)` and `(Sₙ − S)(Tv)`
  have h1 := hT v
  rw [Metric.tendsto_atTop] at h1
  obtain ⟨N₁, hN₁⟩ := h1 (ε / (2 * (M + 1))) (by positivity)
  have h2 := hS (T v)
  rw [Metric.tendsto_atTop] at h2
  obtain ⟨N₂, hN₂⟩ := h2 (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ := hN₁ n (le_trans (le_max_left _ _) hn)
  have hn₂ := hN₂ n (le_trans (le_max_right _ _) hn)
  rw [dist_eq_norm] at hn₁ hn₂ ⊢
  have hsplit : Sn n (Tn n v) - S (T v)
      = Sn n (Tn n v - T v) + (Sn n (T v) - S (T v)) := by
    rw [map_sub]
    abel
  rw [hsplit]
  have hb1 : ‖Sn n (Tn n v - T v)‖ ≤ M * ‖Tn n v - T v‖ :=
    le_trans ((Sn n).le_opNorm _)
      (mul_le_mul_of_nonneg_right (hSb n) (norm_nonneg _))
  calc ‖Sn n (Tn n v - T v) + (Sn n (T v) - S (T v))‖
      ≤ ‖Sn n (Tn n v - T v)‖ + ‖Sn n (T v) - S (T v)‖ :=
        norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
        have hb2 : ‖Sn n (Tn n v - T v)‖
            ≤ (M + 1) * ‖Tn n v - T v‖ :=
          le_trans hb1 (by nlinarith [norm_nonneg (Tn n v - T v)])
        have hb3 : (M + 1) * ‖Tn n v - T v‖
            < (M + 1) * (ε / (2 * (M + 1))) :=
          mul_lt_mul_of_pos_left hn₁ (by positivity)
        have hb4 : (M + 1) * (ε / (2 * (M + 1))) = ε / 2 := by
          field_simp
        have := add_lt_add_of_le_of_lt
          (le_trans hb2 hb3.le) hn₂
        linarith [hb2, hb3, hb4, hn₂]
    _ = ε := by ring

/-! ## Operator-continuity of the functional calculus -/

/-- **`f(aₙ) → f(a)` for selfadjoint convergent sequences** — the
functional-calculus continuity clause, with the compact spectral
window `closedBall 0 (‖a‖ + 1)` extracted from norm convergence. -/
theorem cfc_tendsto_of_isSelfAdjoint
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
    [NormOneClass A] [CompleteSpace A] [ContinuousStar A]
    [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {an : ℕ → A} {a : A}
    (hsan : ∀ n, IsSelfAdjoint (an n)) (hsa : IsSelfAdjoint a)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hconv : Tendsto an atTop (nhds a)) :
    Tendsto (fun n => cfc f (an n)) atTop (nhds (cfc f a)) := by
  set R : ℝ := ‖a‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  -- eventually the spectra live in the closed ball of radius `R`
  have hnorm : ∀ᶠ n in atTop, ‖an n‖ < R := by
    have h1 : Tendsto (fun n => ‖an n‖) atTop (nhds ‖a‖) :=
      hconv.norm
    have h2 : ‖a‖ < R := by rw [hR]; linarith
    exact h1.eventually_lt_const h2
  have hspec : ∀ᶠ n in atTop,
      spectrum ℝ (an n) ⊆ Metric.closedBall (0:ℝ) R := by
    filter_upwards [hnorm] with n hn
    exact subset_trans (spectrum.subset_closedBall_norm (an n))
      (Metric.closedBall_subset_closedBall hn.le)
  have hspec₀ : spectrum ℝ a ⊆ Metric.closedBall (0:ℝ) R :=
    subset_trans (spectrum.subset_closedBall_norm a)
      (Metric.closedBall_subset_closedBall (by rw [hR]; linarith))
  exact hconv.cfc (isCompact_closedBall 0 R) f hspec
    (Filter.Eventually.of_forall hsan) hspec₀ hsa hf.continuousOn

/-! ## The packaged `C₀` clause on L² -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

/-- **The functional-calculus clause on L²**
(`thm:flat-limit`(v) realized): for selfadjoint symbol fields
converging pointwise a.e. with a uniform norm bound, and any
continuous globally bounded `f : ℝ → ℝ` (in particular any
`f ∈ C₀(ℝ)`), the multiplication operators by `f(Hₙ(·))` converge
strongly on L² to multiplication by `f(H(·))`:
`‖(f(Hₙ) − f(H)) u‖_{L²} → 0` for every `u ∈ L²`. -/
theorem multiplier_cfc_tendsto
    {Hn : ℕ → X → E →L[ℂ] E} {Hsym : X → E →L[ℂ] E} {u : X → E}
    {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : Continuous f) (hfb : ∀ t, ‖f t‖ ≤ c)
    (hsan : ∀ n, ∀ᵐ x ∂μ, IsSelfAdjoint (Hn n x))
    (hsa : ∀ᵐ x ∂μ, IsSelfAdjoint (Hsym x))
    (hmeasn : ∀ n, AEStronglyMeasurable
      (fun x => cfc f (Hn n x)) μ)
    (hmeas : AEStronglyMeasurable (fun x => cfc f (Hsym x)) μ)
    (hu : MemLp u 2 μ)
    (hconv : ∀ᵐ x ∂μ,
      Tendsto (fun n => Hn n x) atTop (nhds (Hsym x))) :
    Tendsto (fun n => eLpNorm (fun x =>
        (cfc f (Hn n x)) (u x) - (cfc f (Hsym x)) (u x)) 2 μ)
      atTop (nhds 0) := by
  -- uniform bound from `norm_cfc_le`
  have hbn : ∀ n, ∀ᵐ x ∂μ, ‖cfc f (Hn n x)‖ ≤ c := by
    intro n
    filter_upwards [hsan n] with x hx
    exact norm_cfc_le hc fun t _ => hfb t
  have hb : ∀ᵐ x ∂μ, ‖cfc f (Hsym x)‖ ≤ c := by
    filter_upwards [hsa] with x hx
    exact norm_cfc_le hc fun t _ => hfb t
  -- pointwise a.e. convergence from the cfc continuity
  have hptwise : ∀ᵐ x ∂μ, Tendsto
      (fun n => (cfc f (Hn n x)) (u x)) atTop
      (nhds ((cfc f (Hsym x)) (u x))) := by
    have hall : ∀ᵐ x ∂μ, (∀ n, IsSelfAdjoint (Hn n x)) := by
      rw [MeasureTheory.ae_all_iff]
      exact hsan
    filter_upwards [hall, hsa, hconv] with x hxn hx hcx
    have h1 : Tendsto (fun n => cfc f (Hn n x)) atTop
        (nhds (cfc f (Hsym x))) :=
      cfc_tendsto_of_isSelfAdjoint hxn hx f hf hcx
    exact ((ContinuousLinearMap.apply ℂ E
      (u x)).continuous.tendsto (cfc f (Hsym x))).comp h1
  exact multiplier_tendsto_eLpNorm hc hmeasn hmeas hbn hb hu
    hptwise

end NCG
