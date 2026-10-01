/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Dependence of the acceleration defect on preparation jets
  (`prop:supp-finite-acc-invariance`, `eq:supp-finite-acc-total-response`,
  conditional on `eq:supp-finite-acc-initial-verdict`; emergent-spacetime manuscript)

The initial-data expression of the two-row acceleration defect
(`eq:supp-finite-acc-initial-verdict`, a consequence of
`thm:supp-exact-initial-gate` / `thm:supp-finite-acc-coefficients`) is
`Δ_g = p_g {C_red Df(0) κ + C_red s₀ + Dg(0) b}`; it is encoded as
`FiniteAccInvariance.initialVerdict`.  The paper's proof of
`prop:supp-finite-acc-invariance` is "apply the initial verdict to the two
families and differentiate it".  Here the initial verdict is a hypothesis
(`hverdict`), since `thm:supp-exact-initial-gate` is not formalized; given
it:

* `same_tuple_same_defect`: two families with the same determining tuple
  `(κ, b, s₀, Df(0), Dg(0), C_red, p_g)` have the same `Δ_g` (and hence a higher
  target jet that preserves the tuple cannot remove a nonzero defect);
* `total_response`: for a differentiable family of preparations
  `d ↦ (κ(d), s₀(d), b(d))` with the four maps fixed,
  `D_d Δ_g [ḋ] = p_g {C_red Df(0) D_dκ[ḋ] + C_red D_d s₀[ḋ] + Dg(0) D_d b[ḋ]}`
  (`eq:supp-finite-acc-total-response`);
* `source_derivative_not_certificate`: a nonzero derivative of the source `s₀`
  alone does not force a nonzero derivative of `Δ_g`.
-/

namespace RenewalGeometry
namespace FiniteAccInvariance

variable {Vk Vx Vz Vb Vg D : Type*}
  [NormedAddCommGroup Vk] [NormedSpace ℝ Vk] [NormedAddCommGroup Vx] [NormedSpace ℝ Vx]
  [NormedAddCommGroup Vz] [NormedSpace ℝ Vz] [NormedAddCommGroup Vb] [NormedSpace ℝ Vb]
  [NormedAddCommGroup Vg] [NormedSpace ℝ Vg] [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The initial-data value of the two-row acceleration defect
`Δ_g = p_g {C_red Df(0) κ + C_red s₀ + Dg(0) b}`
(`eq:supp-finite-acc-initial-verdict`). -/
def initialVerdict (pg : Vz →L[ℝ] Vg) (Cred : Vx →L[ℝ] Vz) (Df0 : Vk →L[ℝ] Vx)
    (Dg0 : Vb →L[ℝ] Vz) (κ : Vk) (s0 : Vx) (b : Vb) : Vg :=
  pg (Cred (Df0 κ) + Cred s0 + Dg0 b)

/-- First clause of `prop:supp-finite-acc-invariance` (conditional on the initial
verdict): two exact initialized families whose defects obey the initial verdict
and which share the determining tuple have the same `Δ_g`. -/
theorem same_tuple_same_defect (pg : Vz →L[ℝ] Vg) (Cred : Vx →L[ℝ] Vz)
    (Df0 : Vk →L[ℝ] Vx) (Dg0 : Vb →L[ℝ] Vz) (κ : Vk) (s0 : Vx) (b : Vb)
    (Δ₁ Δ₂ : Vg) (h₁ : Δ₁ = initialVerdict pg Cred Df0 Dg0 κ s0 b)
    (h₂ : Δ₂ = initialVerdict pg Cred Df0 Dg0 κ s0 b) : Δ₁ = Δ₂ := h₁.trans h₂.symm

/-- `eq:supp-finite-acc-total-response` (conditional on the initial verdict):
for a family of preparations `d ↦ (κ(d), s₀(d), b(d))` differentiable at `d₀`,
with `Df(0), Dg(0), C_red, p_g` fixed, whose defect obeys the initial verdict
near `d₀`, the defect is differentiable at `d₀` with
`D_dΔ_g = p_g ∘ (C_red ∘ Df(0) ∘ D_dκ + C_red ∘ D_d s₀ + Dg(0) ∘ D_d b)`. -/
theorem total_response (pg : Vz →L[ℝ] Vg) (Cred : Vx →L[ℝ] Vz) (Df0 : Vk →L[ℝ] Vx)
    (Dg0 : Vb →L[ℝ] Vz) (κ : D → Vk) (s0 : D → Vx) (b : D → Vb) (Δ : D → Vg)
    (κ' : D →L[ℝ] Vk) (s0' : D →L[ℝ] Vx) (b' : D →L[ℝ] Vb) {d₀ : D}
    (hκ : HasFDerivAt κ κ' d₀) (hs : HasFDerivAt s0 s0' d₀) (hb : HasFDerivAt b b' d₀)
    (hverdict : ∀ᶠ d in nhds d₀, Δ d = initialVerdict pg Cred Df0 Dg0 (κ d) (s0 d) (b d)) :
    HasFDerivAt Δ (pg.comp ((Cred.comp Df0).comp κ' + Cred.comp s0' + Dg0.comp b')) d₀ := by
  have hin : HasFDerivAt (fun d => Cred (Df0 (κ d)) + Cred (s0 d) + Dg0 (b d))
      ((Cred.comp Df0).comp κ' + Cred.comp s0' + Dg0.comp b') d₀ :=
    (((Cred.comp Df0).hasFDerivAt.comp d₀ hκ).add (Cred.hasFDerivAt.comp d₀ hs)).add
      (Dg0.hasFDerivAt.comp d₀ hb)
  have hout := pg.hasFDerivAt.comp d₀ hin
  refine hout.congr_of_eventuallyEq ?_
  filter_upwards [hverdict] with d hd
  simp [hd, initialVerdict, Function.comp]

/-- Last clause of `prop:supp-finite-acc-invariance`: a nonzero derivative of the
acceleration source alone is not a certificate for the derivative of the
complete defect.  Scalar instance: `p_g = C_red = Df(0) = id`, `Dg(0) = 0`,
`κ(d) = -d`, `s₀(d) = d`, `b ≡ 0`; then `D s₀ ≠ 0` but `D Δ_g = 0`. -/
theorem source_derivative_not_certificate :
    ∃ (pg Cred Df0 : ℝ →L[ℝ] ℝ) (Dg0 : ℝ →L[ℝ] ℝ) (κ' s0' b' : ℝ →L[ℝ] ℝ),
      s0' ≠ 0 ∧ pg.comp ((Cred.comp Df0).comp κ' + Cred.comp s0' + Dg0.comp b') = 0 := by
  refine ⟨ContinuousLinearMap.id ℝ ℝ, ContinuousLinearMap.id ℝ ℝ,
    ContinuousLinearMap.id ℝ ℝ, 0, -ContinuousLinearMap.id ℝ ℝ,
    ContinuousLinearMap.id ℝ ℝ, 0, ?_, ?_⟩
  · intro h
    have := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) h
    simp at this
  · ext; simp

end FiniteAccInvariance
end RenewalGeometry
