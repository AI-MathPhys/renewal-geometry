/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMMainLimit

/-!
# Localized variational closure on one compact subslab (towards `thm:regular-branch`)

`thm:regular-branch` of the Einstein–Standard-Model action-closure manuscript is local to one
compact subslab `Q = I × Σ`: the conclusion is convergence in the strong packet *on `Q`* and the
classical Einstein–Standard-Model equations *there*.  The library's `closure_along`
(`EinsteinSMMainLimit.lean`) assumes reduced convergence on every slab chart and concludes on all
test regions.  This file provides the local form.

* `FirstVariationsConvergeOn`, `IsDistributionalSolutionOn`, `SatisfiesEinsteinSMOn`: the
  conclusions of `thm:main-limit` for the test regions whose time support lies in `(t₀, t₁)`, with
  the limit functionals computed on the slab chart `(t₀, t₁) × (0,1)³`;
* **`closure_on_slab`**: reduced convergence on the single slab chart `(t₀, t₁) × (0,1)³` along a
  subsequence, first-variation consistency, physical stationarity and continuity of the Yukawa map
  give the three local conclusions;
* `closure_on_slab_of_strong`: the same from strong-packet convergence on the slab chart (with the
  coframe chart condition and compact banks), through `StrongPacketOn.toReduced`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-- **Local convergence of the first variations** on the slab `(t₀, t₁)`: for every test region
`K` with time support in `(t₀, t₁)`, `D𝒮_{θ_h}(z_h) → D𝒮_θ(z)` in the dual norm of `𝒱_K^r`, the
limit functional computed on the slab chart `(t₀, t₁) × (0,1)³`. -/
def FirstVariationsConvergeOn (t₀ t₁ : ℝ) (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) (r : ℕ)
    (fields : ℕ → SmoothFields T FC.left) (bank : ℕ → CoefficientBank Ysec)
    (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec) : Prop :=
  ∀ K : CylRegion T, (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ ε > (0 : ℝ), ∀ᶠ k in atTop,
    ∀ v : CrTest FC.left r K,
      |(firstVariation T FC (bank k) .gravity (fields k).z v.val +
          firstVariation T FC (bank k) .standardModel (fields k).z v.val) -
        (gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
          smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v)| ≤ ε * ‖v‖

/-- **Local `eq:main-stationary`** on the slab `(t₀, t₁)`. -/
def IsDistributionalSolutionOn (t₀ t₁ : ℝ) (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    (r : ℕ) (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec) : Prop :=
  ∀ K : CylRegion T, (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest FC.left r K,
    gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
      smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v = 0

/-- **Local `eq:Einstein-SM`** on the slab `(t₀, t₁)`. -/
def SatisfiesEinsteinSMOn (t₀ t₁ : ℝ) (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) (r : ℕ)
    (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec) : Prop :=
  ∀ K : CylRegion T, (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest FC.left r K,
    einsteinDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v =
      θ₀.kappa * stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v

variable {FC}

theorem IsDistributionalSolutionOn.einstein {t₀ t₁ : ℝ} {h0 : 0 < t₀} {h01 : t₀ < t₁}
    {h1 : t₁ < T} {r : ℕ} {L : LimitFields FC.C} {θ₀ : CoefficientBank Ysec}
    (h : IsDistributionalSolutionOn FC t₀ t₁ h0 h01 h1 r L θ₀) :
    SatisfiesEinsteinSMOn FC t₀ t₁ h0 h01 h1 r L θ₀ := by
  intro K hK v
  have h' := h K hK (metricTest FC v)
  simp only [einsteinDistribution, stressDistribution]
  rw [show gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L (metricTest FC v) =
    -smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L (metricTest FC v) by linarith]
  ring

/-- **Localized closure** (the closure step of `thm:regular-branch` on one subslab): if along
`σ → ∞` the reconstructed fields converge in the reduced topology on the single slab chart
`(t₀, t₁) × (0,1)³`, the regulator is first-variation consistent and physically stationary, and
the Yukawa map is continuous in the bank, then on every test region with time support in
`(t₀, t₁)` the first variations converge, the limit solves all Euler equations and
`eq:Einstein-SM` holds there. -/
theorem closure_on_slab (reg : RegulatorSequence T FC) {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop)
    {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {L : LimitFields FC.C} {θ₀ : CoefficientBank Ysec}
    (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (σ k))
      (fun k => reg.bank (σ k)) L θ₀)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) :
    FirstVariationsConvergeOn FC t₀ t₁ h0 h01 h1 reg.r0 (fun k => reg.fields (σ k))
        (fun k => reg.bank (σ k)) L θ₀ ∧
      IsDistributionalSolutionOn FC t₀ t₁ h0 h01 h1 reg.r0 L θ₀ ∧
      SatisfiesEinsteinSMOn FC t₀ t₁ h0 h01 h1 reg.r0 L θ₀ := by
  have hr : 1 ≤ reg.r0 := le_trans (by norm_num) reg.four_le_r0
  have hdual : FirstVariationsConvergeOn FC t₀ t₁ h0 h01 h1 reg.r0 (fun k => reg.fields (σ k))
      (fun k => reg.bank (σ k)) L θ₀ := by
    intro K hK ε hε
    obtain ⟨hyL, hy0⟩ := hyuk _ _ hRC.bank_tendsto
    exact actionVariation_dual_tendsto FC h0 h01 h1 hK hr hRC hyL hy0 hε
  have heuler : IsDistributionalSolutionOn FC t₀ t₁ h0 h01 h1 reg.r0 L θ₀ := by
    intro K hK
    refine eq_zero_of_unit_of_homogeneous FC (fun v => gravLimitVariation FC θ₀
      (slabChart t₀ t₁ h0 h01 h1) L v + smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v)
      (fun c v => by
        simp only [gravLimitVariation_smul, smLimitVariation_smul]; ring) ?_
    intro v hv
    exact limit_eq_zero_of_defects reg hσ K hcons hstat _ (hdual K hK) v hv
  exact ⟨hdual, heuler, heuler.einstein⟩

/-- **Localized closure from a local strong packet**: strong-packet convergence on the single slab
chart (with the coframe chart condition and banks in a compact physical set) along a strictly
increasing subsequence gives the local conclusions. -/
theorem closure_on_slab_of_strong (reg : RegulatorSequence T FC) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    (hch : CoframeChartCondition (slabChart t₀ t₁ h0 h01 h1) reg.fields)
    (hbank : ∃ P, IsCompactBankSet P ∧ ∀ n, reg.bank n ∈ P)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) {L : LimitFields FC.C} {θ₀ : CoefficientBank Ysec}
    (hSP : StrongPacketOn (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (σ k)) L)
    (hθ : BankTendsto (fun k => reg.bank (σ k)) θ₀) :
    FirstVariationsConvergeOn FC t₀ t₁ h0 h01 h1 reg.r0 (fun k => reg.fields (σ k))
        (fun k => reg.bank (σ k)) L θ₀ ∧
      IsDistributionalSolutionOn FC t₀ t₁ h0 h01 h1 reg.r0 L θ₀ ∧
      SatisfiesEinsteinSMOn FC t₀ t₁ h0 h01 h1 reg.r0 L θ₀ := by
  obtain ⟨P, hP, hθP⟩ := hbank
  obtain ⟨Ke, hKe, hKn⟩ := hch
  refine closure_on_slab reg hσ.tendsto_atTop h0 h01 h1 ?_ hcons hstat hyuk
  exact hSP.toReduced ⟨Ke, hKe, fun k => hKn _⟩ ⟨P, hP, fun k => hθP _⟩ hθ

end EinsteinSM
end RenewalGeometry
