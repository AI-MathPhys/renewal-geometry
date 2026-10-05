/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeDensityAnalytic
import RenewalGeometry.Analysis.AnalyticCompositionGevrey

/-!
# Analytic growth of the low-frequency physical residuals (`thm:native-source`)

Einstein–Standard-Model action-closure manuscript, proof of `thm:native-source`: "By Bernstein
estimates the low-frequency field changes by at most a fixed constant times `K|Im x|` in a complex
spatial strip.  Taking its width `a/K` with `a` small relative to the declared field-value and
inverse-metric margins preserves the analytic branches of every algebraic coefficient …  Thus the
bosonic and Dirac source amplitudes in this strip are bounded by `CK²` and `CK`."

We prove the real-variable content of this step: the physical residual rows of the low-frequency
comparison head `z^lo = 𝓘_h^trig P_{≤K} u_h` have derivatives of analytic growth along every
direction,
`‖Dᵖ𝓡_B(z^lo)(x)(v, …, v)‖ ≤ C K² p! (R K)ᵖ`, `‖Dᵖ𝓡_D(z^lo)(x)(v, …, v)‖ ≤ C K p! (R K)ᵖ`
(`‖v‖ ≤ 1`), with `C`, `R` depending only on the chart, the amplitude bound and the coefficient
bank.  This is what the strip bound is used for (the Fourier decay of `lem:log-source-upgrade`,
see `GevreyFourier`).

## Structure

* `PhiB`, `PhiD`: the Euler rows as **analytic** functions of the second-order jet:
  `E_ν(Y)(z) = Φ_B(J¹Y(z), ∂J¹Y(z))` (`eulerOp_eq_PhiB`) and the Dirac first-order operator
  `= Φ_D(J¹Y(z), (Y(z), ∂Y(z)))` (`foOp_eq_PhiD`); `Φ_B`, `Φ_D` are real-analytic on the chart
  (`analyticAt_PhiB`, `analyticAt_PhiD`) because the density is (`NativeAnalytic`).
* `GamB`, `GamD`: the jet curves; their derivatives are bounded geometrically by the derivatives
  of the rescaled low head (Bernstein, `resc_reconLow_bound`).
* **`native_low_gevrey`**: the analytic growth bounds above.
-/

open Finset Filter Topology Metric Set NormedSpace
open scoped ContDiff Nat

namespace RenewalGeometry.NativeLowSource

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency NativeTail
open ContEulerBounds (JS jetP jetQ eulerOp foOp inlJ slotJ inrP)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Generic: Euler-type operators as analytic functions of the second-order jet -/

section Generic

variable {V Θ S : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Θ]
  [NormedSpace ℝ Θ] [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The bilinear evaluation `(L, x) ↦ L x` preserves analyticity. -/
theorem analyticAt_apply_comp {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : X → E →L[ℝ] F} {g : X → E} {x : X} (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun x => f x (g x)) x := by
  have hb := (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (f x, g x)
  exact AnalyticAt.comp (g := fun p : (E →L[ℝ] F) × E => ContinuousLinearMap.id ℝ (E →L[ℝ] F) p.1 p.2)
    (f := fun x => (f x, g x)) hb (hf.prod hg)

/-- The Euler-row map `Φ_E(q, v) = G(q) ∘ ι_w - Σ_μ (DG(q) v_μ) ∘ ι_{p_μ}`. -/
def phiE (G : Θ × JS V → (JS V →L[ℝ] ℝ)) (p : (Θ × JS V) × (Fin 4 → Θ × JS V)) : V →L[ℝ] ℝ :=
  (G p.1).comp (inlJ V) - ∑ μ, (fderiv ℝ G p.1 (p.2 μ)).comp (slotJ V μ)

/-- The first-order map `Φ_F(q, (w, v)) = G₁(q) - Σ_μ Dℓ_μ(w) v_μ`. -/
def phiF (G₁ : Θ × JS V → (S →L[ℝ] ℝ)) (ℓ : Fin 4 → Θ × V → (S →L[ℝ] ℝ))
    (p : (Θ × JS V) × ((Θ × V) × (Fin 4 → Θ × V))) : S →L[ℝ] ℝ :=
  G₁ p.1 - ∑ μ, fderiv ℝ (ℓ μ) p.2.1 (p.2.2 μ)

/-- The second-order jet curve of the Euler rows. -/
def gamE (θ : Θ) (Y : R4 → V) (z : R4) : (Θ × JS V) × (Fin 4 → Θ × JS V) :=
  (jetP θ Y z, fun μ => fderiv ℝ (jetP θ Y) z (evec μ))

/-- The jet curve of the first-order rows. -/
def gamF (θ : Θ) (Y : R4 → V) (z : R4) : (Θ × JS V) × ((Θ × V) × (Fin 4 → Θ × V)) :=
  (jetP θ Y z, (jetQ θ Y z, fun μ => fderiv ℝ (jetQ θ Y) z (evec μ)))

theorem analyticAt_phiE {G : Θ × JS V → (JS V →L[ℝ] ℝ)} {U : Set (Θ × JS V)} (hU : IsOpen U)
    (hG : AnalyticOnNhd ℝ G U) {p : (Θ × JS V) × (Fin 4 → Θ × JS V)} (hp : p.1 ∈ U) :
    AnalyticAt ℝ (phiE G) p := by
  have hG1 : AnalyticAt ℝ (fun p : (Θ × JS V) × (Fin 4 → Θ × JS V) => G p.1) p :=
    AnalyticAt.comp (g := G) (f := fun p : (Θ × JS V) × (Fin 4 → Θ × JS V) => p.1)
      (hG _ hp) analyticAt_fst
  have hdG : AnalyticAt ℝ (fun p : (Θ × JS V) × (Fin 4 → Θ × JS V) => fderiv ℝ G p.1) p :=
    AnalyticAt.comp (g := fderiv ℝ G) (f := fun p : (Θ × JS V) × (Fin 4 → Θ × JS V) => p.1)
      ((hG.fderiv_of_isOpen hU) _ hp) analyticAt_fst
  have hv : ∀ μ, AnalyticAt ℝ (fun p : (Θ × JS V) × (Fin 4 → Θ × JS V) => p.2 μ) p := fun μ =>
    ((ContinuousLinearMap.proj μ : (Fin 4 → Θ × JS V) →L[ℝ] Θ × JS V).comp
      (ContinuousLinearMap.snd ℝ (Θ × JS V) (Fin 4 → Θ × JS V))).analyticAt p
  have h1 : AnalyticAt ℝ (fun p : (Θ × JS V) × (Fin 4 → Θ × JS V) => (G p.1).comp (inlJ V)) p :=
    (ContEulerBounds.preL (inlJ V)).analyticAt _ |>.comp hG1
  have h2 : ∀ μ, AnalyticAt ℝ (fun p : (Θ × JS V) × (Fin 4 → Θ × JS V) =>
      (fderiv ℝ G p.1 (p.2 μ)).comp (slotJ V μ)) p := fun μ =>
    (ContEulerBounds.preL (slotJ V μ)).analyticAt _ |>.comp (analyticAt_apply_comp hdG (hv μ))
  unfold phiE
  exact h1.sub (Finset.analyticAt_fun_sum _ fun μ _ => h2 μ)

theorem analyticAt_phiF {G₁ : Θ × JS V → (S →L[ℝ] ℝ)} {ℓ : Fin 4 → Θ × V → (S →L[ℝ] ℝ)}
    {U₁ : Set (Θ × JS V)} {U₀ : Set (Θ × V)} (hU₀ : IsOpen U₀) (hG₁ : AnalyticOnNhd ℝ G₁ U₁)
    (hℓ : ∀ μ, AnalyticOnNhd ℝ (ℓ μ) U₀) {p : (Θ × JS V) × ((Θ × V) × (Fin 4 → Θ × V))}
    (hp1 : p.1 ∈ U₁) (hp2 : p.2.1 ∈ U₀) : AnalyticAt ℝ (phiF G₁ ℓ) p := by
  have hG : AnalyticAt ℝ (fun p : (Θ × JS V) × ((Θ × V) × (Fin 4 → Θ × V)) => G₁ p.1) p :=
    AnalyticAt.comp (g := G₁) (f := fun p : (Θ × JS V) × ((Θ × V) × (Fin 4 → Θ × V)) => p.1)
      (hG₁ _ hp1) analyticAt_fst
  have hdl : ∀ μ, AnalyticAt ℝ (fun p : (Θ × JS V) × ((Θ × V) × (Fin 4 → Θ × V)) =>
      fderiv ℝ (ℓ μ) p.2.1) p := fun μ =>
    AnalyticAt.comp (g := fderiv ℝ (ℓ μ))
      (f := fun p : (Θ × JS V) × ((Θ × V) × (Fin 4 → Θ × V)) => p.2.1)
      (((hℓ μ).fderiv_of_isOpen hU₀) _ hp2)
      (((ContinuousLinearMap.fst ℝ (Θ × V) (Fin 4 → Θ × V)).comp
        (ContinuousLinearMap.snd ℝ (Θ × JS V) ((Θ × V) × (Fin 4 → Θ × V)))).analyticAt p)
  have hv : ∀ μ, AnalyticAt ℝ (fun p : (Θ × JS V) × ((Θ × V) × (Fin 4 → Θ × V)) => p.2.2 μ) p :=
    fun μ => ((ContinuousLinearMap.proj μ : (Fin 4 → Θ × V) →L[ℝ] Θ × V).comp
      ((ContinuousLinearMap.snd ℝ (Θ × V) (Fin 4 → Θ × V)).comp
        (ContinuousLinearMap.snd ℝ (Θ × JS V) ((Θ × V) × (Fin 4 → Θ × V))))).analyticAt p
  unfold phiF
  exact hG.sub (Finset.analyticAt_fun_sum _ fun μ _ => analyticAt_apply_comp (hdl μ) (hv μ))

/-- **The Euler operator through `Φ_E`**: `E_θ(Y)(z) = Φ_E(Γ_E(z))`. -/
theorem eulerOp_eq_phiE {G : Θ × JS V → (JS V →L[ℝ] ℝ)} {θ : Θ} {Y : R4 → V}
    (hY : ContDiff ℝ ∞ Y) {z : R4} (hG : DifferentiableAt ℝ G (jetP θ Y z)) :
    eulerOp G θ Y z = phiE G (gamE θ Y z) := by
  have hJ : ContDiff ℝ ∞ (jetP θ Y) := ContEulerBounds.contDiff_jetP_infty θ hY
  rw [ContEulerBounds.eulerOp_slot, phiE, gamE]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hJd : DifferentiableAt ℝ (jetP θ Y) z := hJ.differentiable (by simp) z
  have hin : HasFDerivAt (fun z' => G (jetP θ Y z'))
      ((fderiv ℝ G (jetP θ Y z)).comp (fderiv ℝ (jetP θ Y) z)) z :=
    hG.hasFDerivAt.comp z hJd.hasFDerivAt
  have hcomp : HasFDerivAt (fun z' => (ContEulerBounds.preL (slotJ V μ)) (G (jetP θ Y z')))
      ((ContEulerBounds.preL (slotJ V μ)).comp ((fderiv ℝ G (jetP θ Y z)).comp
        (fderiv ℝ (jetP θ Y) z))) z :=
    (ContEulerBounds.preL (slotJ V μ)).hasFDerivAt.comp z hin
  have e : (fun z' => (G (jetP θ Y z')).comp (slotJ V μ)) =
      fun z' => (ContEulerBounds.preL (slotJ V μ)) (G (jetP θ Y z')) := by
    funext z'; rfl
  rw [e, hcomp.fderiv]
  rfl

/-- **The first-order operator through `Φ_F`**: `foOp(Y)(z) = Φ_F(Γ_F(z))`. -/
theorem foOp_eq_phiF {G₁ : Θ × JS V → (S →L[ℝ] ℝ)} {ℓ : Fin 4 → Θ × V → (S →L[ℝ] ℝ)}
    {θ : Θ} {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) {z : R4}
    (hℓ : ∀ μ, DifferentiableAt ℝ (ℓ μ) (jetQ θ Y z)) :
    foOp G₁ ℓ θ Y z = phiF G₁ ℓ (gamF θ Y z) := by
  have hQ : ContDiff ℝ ∞ (jetQ θ Y) := ContEulerBounds.contDiff_jetQ_infty θ hY
  unfold ContEulerBounds.foOp phiF gamF
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hQd : DifferentiableAt ℝ (jetQ θ Y) z := hQ.differentiable (by simp) z
  have hcomp := ((hℓ μ).hasFDerivAt.comp z hQd.hasFDerivAt).fderiv
  rw [show (fun z' => ℓ μ (jetQ θ Y z')) = ℓ μ ∘ jetQ θ Y from rfl, hcomp]
  rfl

end Generic

/-! ### Derivative bounds and analyticity of the jet curves -/

section CurveBounds

variable {E F₁ F₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F₁]
  [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

theorem norm_iteratedFDeriv_prodMk_le {f : E → F₁} {g : E → F₂} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (m : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ m (fun z => (f z, g z)) z‖ ≤
      ‖iteratedFDeriv ℝ m f z‖ + ‖iteratedFDeriv ℝ m g z‖ := by
  have e : (fun z => (f z, g z)) = (fun z => ContinuousLinearMap.inl ℝ F₁ F₂ (f z)) +
      (fun z => ContinuousLinearMap.inr ℝ F₁ F₂ (g z)) := by
    funext z; simp
  have h1 : ContDiff ℝ ∞ (fun z => ContinuousLinearMap.inl ℝ F₁ F₂ (f z)) :=
    (ContinuousLinearMap.inl ℝ F₁ F₂).contDiff.comp hf
  have h2 : ContDiff ℝ ∞ (fun z => ContinuousLinearMap.inr ℝ F₁ F₂ (g z)) :=
    (ContinuousLinearMap.inr ℝ F₁ F₂).contDiff.comp hg
  have hm : ((m : ℕ) : WithTop ℕ∞) ≤ ∞ := ContEulerBounds.natCast_le_infty m
  rw [e, iteratedFDeriv_add_apply (h1.of_le hm).contDiffAt (h2.of_le hm).contDiffAt]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine ((ContinuousLinearMap.inl ℝ F₁ F₂).norm_iteratedFDeriv_comp_left
      (hf.of_le hm).contDiffAt le_rfl).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      fun x => by simp)
  · refine ((ContinuousLinearMap.inr ℝ F₁ F₂).norm_iteratedFDeriv_comp_left
      (hg.of_le hm).contDiffAt le_rfl).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      fun x => by simp)

theorem norm_iteratedFDeriv_pi4_le {c : Fin 4 → E → F₁} (hc : ∀ μ, ContDiff ℝ ∞ (c μ)) (m : ℕ)
    (z : E) : ‖iteratedFDeriv ℝ m (fun z => fun μ => c μ z) z‖ ≤
      ∑ μ, ‖iteratedFDeriv ℝ m (c μ) z‖ := by
  have e : (fun z => fun μ => c μ z) = fun z => ∑ μ,
      ContinuousLinearMap.single ℝ (fun _ : Fin 4 => F₁) μ (c μ z) := by
    funext z
    rw [← Finset.univ_sum_single (fun μ => c μ z)]
    simp
  have hm : ((m : ℕ) : WithTop ℕ∞) ≤ ∞ := ContEulerBounds.natCast_le_infty m
  have hs : ∀ μ, ContDiff ℝ m (fun z => ContinuousLinearMap.single ℝ (fun _ : Fin 4 => F₁) μ
      (c μ z)) := fun μ =>
    ((ContinuousLinearMap.single ℝ (fun _ : Fin 4 => F₁) μ).contDiff.comp (hc μ)).of_le hm
  rw [e, iteratedFDeriv_sum (fun μ _ => hs μ), Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
  refine ((ContinuousLinearMap.single ℝ (fun _ : Fin 4 => F₁) μ).norm_iteratedFDeriv_comp_left
    ((hc μ).of_le hm).contDiffAt le_rfl).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    fun x => by simp [Pi.norm_single])

end CurveBounds

section CurveGeneric

variable {V Θ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Θ]
  [NormedSpace ℝ Θ]

theorem contDiff_fderiv_apply_infty {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ f z v) :=
  (ContinuousLinearMap.apply ℝ F v).contDiff.comp (hf.fderiv_right (by simp))

/-- `‖D^m Γ_E(z)‖ ≤ ‖D^m J¹Y(z)‖ + 4 ‖D^{m+1} J¹Y(z)‖` for `m ≥ 1`. -/
theorem norm_iteratedFDeriv_gamE_le {θ : Θ} {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) {m : ℕ}
    (hm : m ≠ 0) (z : R4) :
    ‖iteratedFDeriv ℝ m (gamE θ Y) z‖ ≤
      ‖iteratedFDeriv ℝ m (jet1 Y) z‖ + 4 * ‖iteratedFDeriv ℝ (m + 1) (jet1 Y) z‖ := by
  have hJ : ContDiff ℝ ∞ (jetP θ Y) := ContEulerBounds.contDiff_jetP_infty θ hY
  have hdJ : ∀ μ, ContDiff ℝ ∞ (fun z => fderiv ℝ (jetP θ Y) z (evec μ)) := fun μ =>
    contDiff_fderiv_apply_infty hJ (evec μ)
  have hpi : ContDiff ℝ ∞ (fun z => fun μ => fderiv ℝ (jetP θ Y) z (evec μ)) :=
    contDiff_pi.mpr hdJ
  refine (norm_iteratedFDeriv_prodMk_le hJ hpi m z).trans (add_le_add ?_ ?_)
  · exact ContEulerBounds.norm_iteratedFDeriv_jetP_le hm θ
      (hY.of_le (ContEulerBounds.natCast_le_infty _)) z
  · refine (norm_iteratedFDeriv_pi4_le hdJ m z).trans ?_
    have hb : ∀ μ, ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ (jetP θ Y) z (evec μ)) z‖ ≤
        ‖iteratedFDeriv ℝ (m + 1) (jet1 Y) z‖ := by
      intro μ
      refine (ContEulerBounds.norm_iteratedFDeriv_fderiv_apply_le
        (hJ.of_le (ContEulerBounds.natCast_le_infty _)) (evec μ) z).trans ?_
      rw [norm_evec, mul_one]
      exact ContEulerBounds.norm_iteratedFDeriv_jetP_le (Nat.succ_ne_zero m) θ
        (hY.of_le (ContEulerBounds.natCast_le_infty _)) z
    calc ∑ μ : Fin 4, ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ (jetP θ Y) z (evec μ)) z‖
        ≤ ∑ _μ : Fin 4, ‖iteratedFDeriv ℝ (m + 1) (jet1 Y) z‖ := Finset.sum_le_sum fun μ _ => hb μ
      _ = 4 * ‖iteratedFDeriv ℝ (m + 1) (jet1 Y) z‖ := by simp

/-- `‖D^m Γ_F(z)‖ ≤ ‖D^m J¹Y(z)‖ + ‖D^m Y(z)‖ + 4 ‖D^{m+1} Y(z)‖` for `m ≥ 1`. -/
theorem norm_iteratedFDeriv_gamF_le {θ : Θ} {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) {m : ℕ}
    (hm : m ≠ 0) (z : R4) :
    ‖iteratedFDeriv ℝ m (gamF θ Y) z‖ ≤ ‖iteratedFDeriv ℝ m (jet1 Y) z‖ +
      (‖iteratedFDeriv ℝ m Y z‖ + 4 * ‖iteratedFDeriv ℝ (m + 1) Y z‖) := by
  have hJ : ContDiff ℝ ∞ (jetP θ Y) := ContEulerBounds.contDiff_jetP_infty θ hY
  have hQ : ContDiff ℝ ∞ (jetQ θ Y) := ContEulerBounds.contDiff_jetQ_infty θ hY
  have hdQ : ∀ μ, ContDiff ℝ ∞ (fun z => fderiv ℝ (jetQ θ Y) z (evec μ)) := fun μ =>
    contDiff_fderiv_apply_infty hQ (evec μ)
  have hpi : ContDiff ℝ ∞ (fun z => fun μ => fderiv ℝ (jetQ θ Y) z (evec μ)) :=
    contDiff_pi.mpr hdQ
  have hQpi : ContDiff ℝ ∞ (fun z => (jetQ θ Y z, fun μ => fderiv ℝ (jetQ θ Y) z (evec μ))) :=
    hQ.prodMk hpi
  refine (norm_iteratedFDeriv_prodMk_le hJ hQpi m z).trans (add_le_add ?_ ?_)
  · exact ContEulerBounds.norm_iteratedFDeriv_jetP_le hm θ
      (hY.of_le (ContEulerBounds.natCast_le_infty _)) z
  refine (norm_iteratedFDeriv_prodMk_le hQ hpi m z).trans (add_le_add ?_ ?_)
  · exact ContEulerBounds.norm_iteratedFDeriv_jetQ_le hm θ
      (hY.of_le (ContEulerBounds.natCast_le_infty _)) z
  · refine (norm_iteratedFDeriv_pi4_le hdQ m z).trans ?_
    have hb : ∀ μ, ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ (jetQ θ Y) z (evec μ)) z‖ ≤
        ‖iteratedFDeriv ℝ (m + 1) Y z‖ := by
      intro μ
      refine (ContEulerBounds.norm_iteratedFDeriv_fderiv_apply_le
        (hQ.of_le (ContEulerBounds.natCast_le_infty _)) (evec μ) z).trans ?_
      rw [norm_evec, mul_one]
      exact ContEulerBounds.norm_iteratedFDeriv_jetQ_le (Nat.succ_ne_zero m) θ
        (hY.of_le (ContEulerBounds.natCast_le_infty _)) z
    calc ∑ μ : Fin 4, ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ (jetQ θ Y) z (evec μ)) z‖
        ≤ ∑ _μ : Fin 4, ‖iteratedFDeriv ℝ (m + 1) Y z‖ := Finset.sum_le_sum fun μ _ => hb μ
      _ = 4 * ‖iteratedFDeriv ℝ (m + 1) Y z‖ := by simp

theorem analyticOnNhd_fderiv_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : AnalyticOnNhd ℝ f univ) (v : E) :
    AnalyticOnNhd ℝ (fun z => fderiv ℝ f z v) univ := fun z _ =>
  (ContinuousLinearMap.apply ℝ F v).analyticAt _ |>.comp
    ((hf.fderiv_of_isOpen isOpen_univ) z (mem_univ z))

theorem analyticOnNhd_jet1 {Y : R4 → V} (hY : AnalyticOnNhd ℝ Y univ) :
    AnalyticOnNhd ℝ (jet1 Y) univ := fun z _ => by
  have h2 : AnalyticAt ℝ (fun z => fun μ => fderiv ℝ Y z (evec μ)) z :=
    analyticAt_pi_iff.mpr fun μ => analyticOnNhd_fderiv_apply hY (evec μ) z (mem_univ z)
  exact (hY z (mem_univ z)).prod h2

theorem analyticOnNhd_jetP (θ : Θ) {Y : R4 → V} (hY : AnalyticOnNhd ℝ Y univ) :
    AnalyticOnNhd ℝ (jetP θ Y) univ := fun z _ =>
  analyticAt_const.prod (analyticOnNhd_jet1 hY z (mem_univ z))

theorem analyticOnNhd_jetQ (θ : Θ) {Y : R4 → V} (hY : AnalyticOnNhd ℝ Y univ) :
    AnalyticOnNhd ℝ (jetQ θ Y) univ := fun z _ =>
  analyticAt_const.prod (hY z (mem_univ z))

theorem analyticOnNhd_gamE (θ : Θ) {Y : R4 → V} (hY : AnalyticOnNhd ℝ Y univ) :
    AnalyticOnNhd ℝ (gamE θ Y) univ := fun z _ =>
  (analyticOnNhd_jetP θ hY z (mem_univ z)).prod (analyticAt_pi_iff.mpr fun μ =>
    analyticOnNhd_fderiv_apply (analyticOnNhd_jetP θ hY) (evec μ) z (mem_univ z))

theorem analyticOnNhd_gamF (θ : Θ) {Y : R4 → V} (hY : AnalyticOnNhd ℝ Y univ) :
    AnalyticOnNhd ℝ (gamF θ Y) univ := fun z _ =>
  (analyticOnNhd_jetP θ hY z (mem_univ z)).prod ((analyticOnNhd_jetQ θ hY z (mem_univ z)).prod
    (analyticAt_pi_iff.mpr fun μ =>
      analyticOnNhd_fderiv_apply (analyticOnNhd_jetQ θ hY) (evec μ) z (mem_univ z)))

end CurveGeneric

/-! ### Trigonometric polynomials are entire -/

theorem analyticOnNhd_tp {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : Finset (Fin d → ℤ)) (c : VecTrig.Coef d V) : AnalyticOnNhd ℝ (VecTrig.tp S c) univ := by
  intro x _
  unfold VecTrig.tp
  refine Finset.analyticAt_fun_sum _ fun ℓ _ => ?_
  have hp : AnalyticAt ℝ (fun x => VecTrig.phase ℓ x) x := by
    rw [VecTrig.phase_eq_phaseL]; exact (VecTrig.phaseL ℓ).analyticAt x
  have hc : AnalyticAt ℝ (fun x => Real.cos (VecTrig.phase ℓ x)) x :=
    AnalyticAt.comp (g := Real.cos) Real.analyticAt_cos hp
  have hs : AnalyticAt ℝ (fun x => Real.sin (VecTrig.phase ℓ x)) x :=
    AnalyticAt.comp (g := Real.sin) Real.analyticAt_sin hp
  exact (hc.smul analyticAt_const).add (hs.smul analyticAt_const)

/-! ### A linear map commutes with one-variable derivatives -/

theorem norm_iteratedDeriv_smul_clm_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (c : ℝ) (L : F →L[ℝ] G) {f : ℝ → F} {s : ℝ}
    {p : ℕ} (hf : ContDiffAt ℝ p f s) :
    ‖iteratedDeriv p (fun t => c • L (f t)) s‖ ≤ |c| * ‖L‖ * ‖iteratedDeriv p f s‖ := by
  have e : (fun t => c • L (f t)) = ⇑(c • L) ∘ f := by funext t; simp
  rw [e, iteratedDeriv_eq_iteratedFDeriv, (c • L).iteratedFDeriv_comp_left hf le_rfl,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    iteratedDeriv_eq_iteratedFDeriv]
  refine ((c • L).le_opNorm _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]

theorem contDiff_gamE {V Θ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] {θ : Θ} {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (gamE θ Y) := by
  have hJ : ContDiff ℝ ∞ (jetP θ Y) := ContEulerBounds.contDiff_jetP_infty θ hY
  exact hJ.prodMk (contDiff_pi.mpr fun μ => contDiff_fderiv_apply_infty hJ (evec μ))

theorem contDiff_gamF {V Θ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] {θ : Θ} {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (gamF θ Y) := by
  have hJ : ContDiff ℝ ∞ (jetP θ Y) := ContEulerBounds.contDiff_jetP_infty θ hY
  have hQ : ContDiff ℝ ∞ (jetQ θ Y) := ContEulerBounds.contDiff_jetQ_infty θ hY
  exact hJ.prodMk (hQ.prodMk (contDiff_pi.mpr fun μ => contDiff_fderiv_apply_infty hQ (evec μ)))

/-- Derivative of the curve `s ↦ Γ(ξ + s w)` bounded through `D^mΓ`. -/
theorem norm_iteratedDeriv_line_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Γ : E → F} (hΓ : ContDiff ℝ ∞ Γ) (ξ w : E) (m : ℕ) :
    ‖iteratedDeriv m (fun s : ℝ => Γ (ξ + s • w)) 0‖ ≤ ‖iteratedFDeriv ℝ m Γ ξ‖ * ‖w‖ ^ m := by
  rw [AnalyticGevrey.iteratedDeriv_line hΓ ξ w m 0, zero_smul, add_zero]
  refine ((iteratedFDeriv ℝ m Γ ξ).le_opNorm _).trans ?_
  simp

/-! ### The native residual rows of the low-frequency head -/

section Native

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

local notation "FJ" => JS (Field 𝔄 𝓗 𝓢)
local notation "FF" => Field 𝔄 𝓗 𝓢

theorem analyticOnNhd_resc_reconLow {n : ℕ} [NeZero n] (u : (Fin 4 → ZMod n) → FF) (K : ℝ) :
    AnalyticOnNhd ℝ (resc K (TrigInterp.reconLow n K u)) univ := fun ξ _ => by
  have h1 : AnalyticAt ℝ (fun ξ : R4 => K⁻¹ • ξ) ξ :=
    ((K⁻¹ • ContinuousLinearMap.id ℝ R4).analyticAt ξ).congr
      (Filter.Eventually.of_forall fun _ => by simp)
  exact AnalyticAt.comp (g := TrigInterp.reconLow n K u) (f := fun ξ : R4 => K⁻¹ • ξ)
    (analyticOnNhd_tp _ _ _ (mem_univ _)) h1

theorem analyticOnNhd_Gd' : AnalyticOnNhd ℝ (Gd D) chartU := fun _ hq =>
  NativeAnalytic.analyticAt_Gd D hq

theorem analyticOnNhd_G1D : AnalyticOnNhd ℝ (G1D D) chartU := fun _ hq =>
  NativeAnalytic.analyticAt_G1D D hq

theorem analyticOnNhd_ellD' (μ : Fin 4) : AnalyticOnNhd ℝ (ellD D μ) chartW := fun _ hr =>
  NativeAnalytic.analyticAt_ellD D μ hr

theorem rb_line {K : ℝ} (hK0 : 0 < K) {Y : R4 → FF} (hY : ContDiff ℝ ∞ Y)
    (hch : ∀ ξ, ((K⁻¹, jet1 (resc K Y) ξ) : ℝ × FJ) ∈ chartU) (x v : R4) :
    (fun s : ℝ => RB D Y (x + s • v)) =
      fun s => (K ^ 2) • ContEulerBounds.preL (ιB (𝓢 := 𝓢))
        (phiE (Gd D) (gamE K⁻¹ (resc K Y) (K • x + s • (K • v)))) := by
  have hYt : ContDiff ℝ ∞ (resc K Y) := hY.comp (contDiff_const_smul K⁻¹)
  funext s
  rw [RB_fun_scale D hK0.ne' Y hch]
  beta_reduce
  rw [eulerOp_eq_phiE hYt ((NativeAnalytic.analyticAt_Gd D (hch _)).differentiableAt),
    smul_add, smul_comm K s v]

theorem rd_line {K : ℝ} (hK0 : 0 < K) {Y : R4 → FF} (hY : ContDiff ℝ ∞ Y)
    (hch : ∀ ξ, ((K⁻¹, jet1 (resc K Y) ξ) : ℝ × FJ) ∈ chartU) (x v : R4) :
    (fun s : ℝ => RD D Y (x + s • v)) =
      fun s => K • ContinuousLinearMap.id ℝ (ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ)
        (phiF (G1D D) (fun μ => ellD D μ) (gamF K⁻¹ (resc K Y) (K • x + s • (K • v)))) := by
  have hYt : ContDiff ℝ ∞ (resc K Y) := hY.comp (contDiff_const_smul K⁻¹)
  funext s
  rw [RD_fun_scale D hK0 Y hY hch]
  beta_reduce
  rw [foOp_eq_phiF hYt (fun μ =>
      (NativeAnalytic.analyticAt_ellD D μ (hch _)).differentiableAt), smul_add, smul_comm K s v]

theorem gamE_low_mem {n : ℕ} [NeZero n] (u : (Fin 4 → ZMod n) → FF) {K : ℝ} (hK : 1 ≤ K)
    {Ke : Set Mat} {A : ℝ} (hKe : ∀ x, (TrigInterp.reconLow n K u x).1 ∈ Ke)
    (hA : ∀ y, ‖TrigInterp.reconLow n K u y‖ ≤ A) (ξ : R4) :
    gamE K⁻¹ (resc K (TrigInterp.reconLow n K u)) ξ ∈
      jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A (240 * A) ×ˢ
        closedBall (0 : Fin 4 → ℝ × FJ) (5 * 240 ^ 2 * A) := by
  have hYt : ContDiff ℝ ∞ (resc K (TrigInterp.reconLow n K u)) :=
    (contDiff_reconLow u K).comp (contDiff_const_smul K⁻¹)
  refine ⟨jetP_resc_low_mem u hK hKe hA ξ, ?_⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]
  intro μ
  have h1 := ContEulerBounds.norm_iteratedFDeriv_fderiv_apply_le (n := 0)
    ((ContEulerBounds.contDiff_jetP_infty K⁻¹ hYt).of_le (ContEulerBounds.natCast_le_infty _))
    (evec μ) ξ
  rw [norm_iteratedFDeriv_zero, norm_evec, mul_one] at h1
  have h2 := ContEulerBounds.norm_iteratedFDeriv_jetP_le (n := 1) one_ne_zero K⁻¹
    (hYt.of_le (ContEulerBounds.natCast_le_infty _)) ξ
  have h3 := jet1_resc_low_bound u hK hA 1 ξ
  have e : (5 : ℝ) * 240 ^ (1 + 1) * A = 5 * 240 ^ 2 * A := by norm_num
  rw [e] at h3
  exact h1.trans (h2.trans h3)

theorem gamF_low_mem {n : ℕ} [NeZero n] (u : (Fin 4 → ZMod n) → FF) {K : ℝ} (hK : 1 ≤ K)
    {Ke : Set Mat} {A : ℝ} (hKe : ∀ x, (TrigInterp.reconLow n K u x).1 ∈ Ke)
    (hA : ∀ y, ‖TrigInterp.reconLow n K u y‖ ≤ A) (ξ : R4) :
    gamF K⁻¹ (resc K (TrigInterp.reconLow n K u)) ξ ∈
      jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A (240 * A) ×ˢ
        (valSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A ×ˢ closedBall (0 : Fin 4 → ℝ × FF) (240 * A)) := by
  have hYt : ContDiff ℝ ∞ (resc K (TrigInterp.reconLow n K u)) :=
    (contDiff_reconLow u K).comp (contDiff_const_smul K⁻¹)
  refine ⟨jetP_resc_low_mem u hK hKe hA ξ, jetQ_resc_low_mem u hK hKe hA ξ, ?_⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]
  intro μ
  have h1 := ContEulerBounds.norm_iteratedFDeriv_fderiv_apply_le (n := 0)
    ((ContEulerBounds.contDiff_jetQ_infty K⁻¹ hYt).of_le (ContEulerBounds.natCast_le_infty _))
    (evec μ) ξ
  rw [norm_iteratedFDeriv_zero, norm_evec, mul_one] at h1
  have h2 := ContEulerBounds.norm_iteratedFDeriv_jetQ_le (n := 1) one_ne_zero K⁻¹
    (hYt.of_le (ContEulerBounds.natCast_le_infty _)) ξ
  have h3 := resc_reconLow_bound u hK hA 1 ξ
  rw [pow_one] at h3
  exact h1.trans (h2.trans h3)

theorem gamE_low_deriv {n : ℕ} [NeZero n] (u : (Fin 4 → ZMod n) → FF) {K : ℝ} (hK : 1 ≤ K)
    {A : ℝ} (hA : ∀ y, ‖TrigInterp.reconLow n K u y‖ ≤ A) (ξ w : R4) {m : ℕ} (hm : 1 ≤ m) :
    ‖iteratedDeriv m (fun s : ℝ => gamE K⁻¹ (resc K (TrigInterp.reconLow n K u)) (ξ + s • w)) 0‖ ≤
      25 * 240 ^ 2 * A * (240 * ‖w‖) ^ m := by
  have hYt : ContDiff ℝ ∞ (resc K (TrigInterp.reconLow n K u)) :=
    (contDiff_reconLow u K).comp (contDiff_const_smul K⁻¹)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  refine (norm_iteratedDeriv_line_le (contDiff_gamE (θ := K⁻¹) hYt) ξ w m).trans ?_
  have h1 := norm_iteratedFDeriv_gamE_le (θ := K⁻¹) hYt (m := m) (by omega) ξ
  have h2 := jet1_resc_low_bound u hK hA m ξ
  have h3 := jet1_resc_low_bound u hK hA (m + 1) ξ
  have hP : (0 : ℝ) ≤ 240 ^ m := by positivity
  have hc : 5 * 240 ^ (m + 1) * A + 4 * (5 * 240 ^ (m + 1 + 1) * A) ≤
      25 * 240 ^ 2 * A * 240 ^ m := by
    have e1 : (240 : ℝ) ^ (m + 1) = 240 * 240 ^ m := by ring
    have e2 : (240 : ℝ) ^ (m + 1 + 1) = 240 ^ 2 * 240 ^ m := by ring
    rw [e1, e2]; nlinarith
  calc ‖iteratedFDeriv ℝ m (gamE K⁻¹ (resc K (TrigInterp.reconLow n K u))) ξ‖ * ‖w‖ ^ m
      ≤ (25 * 240 ^ 2 * A * 240 ^ m) * ‖w‖ ^ m := by
        gcongr
        exact h1.trans (by linarith)
    _ = 25 * 240 ^ 2 * A * (240 * ‖w‖) ^ m := by rw [mul_pow]; ring

theorem gamF_low_deriv {n : ℕ} [NeZero n] (u : (Fin 4 → ZMod n) → FF) {K : ℝ} (hK : 1 ≤ K)
    {A : ℝ} (hA : ∀ y, ‖TrigInterp.reconLow n K u y‖ ≤ A) (ξ w : R4) {m : ℕ} (hm : 1 ≤ m) :
    ‖iteratedDeriv m (fun s : ℝ => gamF K⁻¹ (resc K (TrigInterp.reconLow n K u)) (ξ + s • w)) 0‖ ≤
      25 * 240 ^ 2 * A * (240 * ‖w‖) ^ m := by
  have hYt : ContDiff ℝ ∞ (resc K (TrigInterp.reconLow n K u)) :=
    (contDiff_reconLow u K).comp (contDiff_const_smul K⁻¹)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  refine (norm_iteratedDeriv_line_le (contDiff_gamF (θ := K⁻¹) hYt) ξ w m).trans ?_
  have h1 := norm_iteratedFDeriv_gamF_le (θ := K⁻¹) hYt (m := m) (by omega) ξ
  have h2 := jet1_resc_low_bound u hK hA m ξ
  have h3 := resc_reconLow_bound u hK hA m ξ
  have h4 := resc_reconLow_bound u hK hA (m + 1) ξ
  have hP : (0 : ℝ) ≤ 240 ^ m := by positivity
  have hc : 5 * 240 ^ (m + 1) * A + (240 ^ m * A + 4 * (240 ^ (m + 1) * A)) ≤
      25 * 240 ^ 2 * A * 240 ^ m := by
    have e1 : (240 : ℝ) ^ (m + 1) = 240 * 240 ^ m := by ring
    rw [e1]; nlinarith
  calc ‖iteratedFDeriv ℝ m (gamF K⁻¹ (resc K (TrigInterp.reconLow n K u))) ξ‖ * ‖w‖ ^ m
      ≤ (25 * 240 ^ 2 * A * 240 ^ m) * ‖w‖ ^ m := by
        gcongr
        exact h1.trans (by linarith)
    _ = 25 * 240 ^ 2 * A * (240 * ‖w‖) ^ m := by rw [mul_pow]; ring


theorem analyticAt_PhiDir {p : (ℝ × FJ) × ((ℝ × FF) × (Fin 4 → ℝ × FF))} (hp1 : p.1 ∈ chartU)
    (hp2 : p.2.1 ∈ chartW) : AnalyticAt ℝ (phiF (G1D D) (fun μ => ellD D μ)) p :=
  analyticAt_phiF (V := FF) (Θ := ℝ) (S := 𝓢 × CoSpinor 𝓢) isOpen_chartW
      (analyticOnNhd_G1D D) (fun μ => analyticOnNhd_ellD' D μ) hp1 hp2

theorem exists_gevrey_PhiDir {S : Set ((ℝ × FJ) × ((ℝ × FF) × (Fin 4 → ℝ × FF)))}
    (hS : IsCompact S) (hSU : ∀ y ∈ S, y.1 ∈ chartU ∧ y.2.1 ∈ chartW) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ (γ : ℝ → (ℝ × FJ) × ((ℝ × FF) × (Fin 4 → ℝ × FF))) (s₀ : ℝ),
      AnalyticAt ℝ γ s₀ → γ s₀ ∈ S →
      ∀ B c : ℝ, 0 ≤ B → 0 ≤ c → (∀ m, 1 ≤ m → ‖iteratedDeriv m γ s₀‖ ≤ B * c ^ m) →
        ∀ n, ‖iteratedDeriv n (phiF (G1D D) (fun μ => ellD D μ) ∘ γ) s₀‖ ≤
          n ! * (C * (2 * c * max 1 (B / r)) ^ n) := by
  have : CompleteSpace (ℝ × FF) := inferInstance
  have : CompleteSpace (Fin 4 → ℝ × FF) := inferInstance
  have : CompleteSpace ((ℝ × FF) × (Fin 4 → ℝ × FF)) := inferInstance
  have : CompleteSpace (ℝ × FJ) := inferInstance
  have : CompleteSpace ((ℝ × FJ) × ((ℝ × FF) × (Fin 4 → ℝ × FF))) := inferInstance
  have : CompleteSpace (ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ) := inferInstance
  exact AnalyticGevrey.exists_gevrey_comp (E := (ℝ × FJ) × ((ℝ × FF) × (Fin 4 → ℝ × FF)))
    (F := ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ) (Φ := phiF (G1D D) (fun μ => ellD D μ)) hS
    (fun y hy => analyticAt_PhiDir D (hSU y hy).1 (hSU y hy).2)

theorem exists_gevrey_PhiBos {S : Set ((ℝ × FJ) × (Fin 4 → ℝ × FJ))}
    (hS : IsCompact S) (hSU : ∀ y ∈ S, y.1 ∈ chartU) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ (γ : ℝ → (ℝ × FJ) × (Fin 4 → ℝ × FJ)) (s₀ : ℝ),
      AnalyticAt ℝ γ s₀ → γ s₀ ∈ S →
      ∀ B c : ℝ, 0 ≤ B → 0 ≤ c → (∀ m, 1 ≤ m → ‖iteratedDeriv m γ s₀‖ ≤ B * c ^ m) →
        ∀ n, ‖iteratedDeriv n (phiE (Gd D) ∘ γ) s₀‖ ≤
          n ! * (C * (2 * c * max 1 (B / r)) ^ n) := by
  have : CompleteSpace (ℝ × FJ) := inferInstance
  have : CompleteSpace (Fin 4 → ℝ × FJ) := inferInstance
  have : CompleteSpace ((ℝ × FJ) × (Fin 4 → ℝ × FJ)) := inferInstance
  have : CompleteSpace (ContEulerBounds.CovV FF) := inferInstance
  exact AnalyticGevrey.exists_gevrey_comp (E := (ℝ × FJ) × (Fin 4 → ℝ × FJ))
    (F := ContEulerBounds.CovV FF) (Φ := phiE (Gd D)) hS
    (fun y hy => analyticAt_phiE (V := FF) (Θ := ℝ) isOpen_chartU (analyticOnNhd_Gd' D) (hSU y hy))


theorem iteratedDeriv_line_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f) (x v : E) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => f (x + t • v)) 0 = iteratedFDeriv ℝ n f x (fun _ => v) := by
  rw [AnalyticGevrey.iteratedDeriv_line hf x v n 0, zero_smul, add_zero]

/-- **Analytic growth of the low-frequency residual rows** (`thm:native-source`, strip step,
real-variable form).  For a compact coframe chart `K_e ⊂ {det e > 0}` and an amplitude bound `A`
there are `C ≥ 0`, `R > 0` (depending only on the chart, `A` and the coefficient bank) such that
for every record `u_h`, every `K ≥ 1` with low head `z^lo = 𝓘_h^trig P_{≤K}u_h` in the chart and
`|z^lo| ≤ A`, every point `x`, direction `‖v‖ ≤ 1` and order `p`,
`‖Dᵖ𝓡_B(z^lo)(x)(v, …, v)‖ ≤ C K² p! (RK)ᵖ` and `‖Dᵖ𝓡_D(z^lo)(x)(v, …, v)‖ ≤ C K p! (RK)ᵖ`:
the bosonic and Dirac source amplitudes `CK²`, `CK` with analytic radius `∼ 1/K`. -/
theorem native_low_gevrey {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A : ℝ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ ∀ (n : ℕ) [NeZero n] (u : (Fin 4 → ZMod n) → FF) (K : ℝ),
      1 ≤ K → (∀ x, (TrigInterp.reconLow n K u x).1 ∈ Ke) →
      (∀ x, ‖TrigInterp.reconLow n K u x‖ ≤ A) →
      ∀ (x v : R4), ‖v‖ ≤ 1 → ∀ p : ℕ,
        ‖iteratedFDeriv ℝ p (RB D (TrigInterp.reconLow n K u)) x (fun _ => v)‖ ≤
            C * K ^ 2 * (p ! * (R * K) ^ p) ∧
        ‖iteratedFDeriv ℝ p (RD D (TrigInterp.reconLow n K u)) x (fun _ => v)‖ ≤
            C * K * (p ! * (R * K) ^ p) := by
  obtain ⟨A', hA'0, hAA'⟩ : ∃ A' : ℝ, 0 ≤ A' ∧ A ≤ A' :=
    ⟨max A 0, le_max_right _ _, le_max_left _ _⟩
  have hB0 : (0 : ℝ) ≤ 25 * 240 ^ 2 * A' := by positivity
  have hSB : IsCompact (jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A' (240 * A') ×ˢ
      closedBall (0 : Fin 4 → ℝ × FJ) (5 * 240 ^ 2 * A')) :=
    (isCompact_jetSet hKe _ _).prod (isCompact_closedBall _ _)
  have hSD : IsCompact (jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A' (240 * A') ×ˢ
      (valSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A' ×ˢ closedBall (0 : Fin 4 → ℝ × FF) (240 * A'))) :=
    (isCompact_jetSet hKe _ _).prod ((isCompact_valSet hKe _).prod (isCompact_closedBall _ _))
  obtain ⟨C₁, r₁, hC₁, hr₁, hG₁⟩ := exists_gevrey_PhiBos D hSB
    (fun y hy => jetSet_subset hdet _ _ hy.1)
  obtain ⟨C₂, r₂, hC₂, hr₂, hG₂⟩ := exists_gevrey_PhiDir D hSD
    (fun y hy => ⟨jetSet_subset hdet _ _ hy.1, valSet_subset hdet _ hy.2.1⟩)
  obtain ⟨M, hM1, hM₁, hM₂⟩ : ∃ M : ℝ, 1 ≤ M ∧ max 1 (25 * 240 ^ 2 * A' / r₁) ≤ M ∧
      max 1 (25 * 240 ^ 2 * A' / r₂) ≤ M :=
    ⟨max (max 1 (25 * 240 ^ 2 * A' / r₁)) (max 1 (25 * 240 ^ 2 * A' / r₂)),
      (le_max_left _ _).trans (le_max_left _ _), le_max_left _ _, le_max_right _ _⟩
  have hCC : 0 ≤ max C₁ C₂ := hC₁.trans (le_max_left _ _)
  refine ⟨max C₁ C₂, 2 * 240 * M, hCC, by positivity, ?_⟩
  intro n _ u K hK hKe' hA x v hv p
  have hK0 : 0 < K := by linarith
  have hA'' : ∀ y, ‖TrigInterp.reconLow n K u y‖ ≤ A' := fun y => (hA y).trans hAA'
  have hY : ContDiff ℝ ∞ (TrigInterp.reconLow n K u) := contDiff_reconLow u K
  have hYa : AnalyticOnNhd ℝ (resc K (TrigInterp.reconLow n K u)) univ :=
    analyticOnNhd_resc_reconLow u K
  have hch : ∀ ξ, ((K⁻¹, jet1 (resc K (TrigInterp.reconLow n K u)) ξ) : ℝ × FJ) ∈ chartU :=
    fun ξ => jetSet_subset hdet _ _ (jetP_resc_low_mem u hK hKe' hA'' ξ)
  have hKv : ‖K • v‖ ≤ K := by
    rw [norm_smul, Real.norm_of_nonneg hK0.le]
    exact mul_le_of_le_one_right hK0.le hv
  have hscal : ∀ (C r : ℝ), 0 ≤ C → max 1 (25 * 240 ^ 2 * A' / r) ≤ M → C ≤ max C₁ C₂ →
      C * (2 * (240 * ‖K • v‖) * max 1 (25 * 240 ^ 2 * A' / r)) ^ p ≤
        max C₁ C₂ * (2 * 240 * M * K) ^ p := by
    intro C r hC hr hCm
    have h1 : 2 * (240 * ‖K • v‖) * max 1 (25 * 240 ^ 2 * A' / r) ≤ 2 * 240 * M * K := by
      calc 2 * (240 * ‖K • v‖) * max 1 (25 * 240 ^ 2 * A' / r) ≤ 2 * (240 * K) * M := by
            gcongr
        _ = 2 * 240 * M * K := by ring
    exact mul_le_mul hCm (pow_le_pow_left₀ (by positivity) h1 p) (by positivity) hCC
  constructor
  · have hRB : ContDiff ℝ ∞ (RB D (TrigInterp.reconLow n K u)) := contDiff_RB D hK0 hY hch
    rw [← iteratedDeriv_line_zero hRB x v p, rb_line D hK0 hY hch x v]
    have hγa : AnalyticAt ℝ (fun s : ℝ =>
        gamE K⁻¹ (resc K (TrigInterp.reconLow n K u)) (K • x + s • (K • v))) 0 :=
      AnalyticGevrey.analyticAt_line (analyticOnNhd_gamE K⁻¹ hYa _ (mem_univ _))
    have hγS := gamE_low_mem u hK hKe' hA'' (K • x + (0 : ℝ) • (K • v))
    have hG := hG₁ _ 0 hγa hγS _ _ hB0 (by positivity)
      (fun m hm => gamE_low_deriv u hK hA'' (K • x) (K • v) hm) p
    have hcd : ContDiffAt ℝ p (phiE (Gd D) ∘ fun s : ℝ =>
        gamE K⁻¹ (resc K (TrigInterp.reconLow n K u)) (K • x + s • (K • v))) 0 :=
      (AnalyticAt.comp (g := phiE (Gd D)) (f := fun s : ℝ =>
        gamE K⁻¹ (resc K (TrigInterp.reconLow n K u)) (K • x + s • (K • v)))
        (analyticAt_phiE (V := FF) (Θ := ℝ) isOpen_chartU (analyticOnNhd_Gd' D)
        (jetSet_subset hdet _ _ hγS.1)) hγa).contDiffAt
    refine (norm_iteratedDeriv_smul_clm_le _ _ hcd).trans ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ K ^ 2)]
    calc K ^ 2 * ‖ContEulerBounds.preL (ιB (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))‖ *
          ‖iteratedDeriv p (phiE (Gd D) ∘ fun s : ℝ =>
            gamE K⁻¹ (resc K (TrigInterp.reconLow n K u)) (K • x + s • (K • v))) 0‖
        ≤ K ^ 2 * 1 * (p ! * (C₁ * (2 * (240 * ‖K • v‖) *
            max 1 (25 * 240 ^ 2 * A' / r₁)) ^ p)) := by
          gcongr
          exact norm_preL_ιB_le
      _ ≤ K ^ 2 * 1 * (p ! * (max C₁ C₂ * (2 * 240 * M * K) ^ p)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (hscal C₁ r₁ hC₁ hM₁ (le_max_left _ _)) (Nat.cast_nonneg _)) (by positivity)
      _ = max C₁ C₂ * K ^ 2 * (p ! * (2 * 240 * M * K) ^ p) := by ring
  · have hRD : ContDiff ℝ ∞ (RD D (TrigInterp.reconLow n K u)) := contDiff_RD D hK0 hY hch
    rw [← iteratedDeriv_line_zero hRD x v p, rd_line D hK0 hY hch x v]
    have hγa : AnalyticAt ℝ (fun s : ℝ =>
        gamF K⁻¹ (resc K (TrigInterp.reconLow n K u)) (K • x + s • (K • v))) 0 :=
      AnalyticGevrey.analyticAt_line (analyticOnNhd_gamF K⁻¹ hYa _ (mem_univ _))
    have hγS := gamF_low_mem u hK hKe' hA'' (K • x + (0 : ℝ) • (K • v))
    have hG := hG₂ _ 0 hγa hγS _ _ hB0 (by positivity)
      (fun m hm => gamF_low_deriv u hK hA'' (K • x) (K • v) hm) p
    have hcd : ContDiffAt ℝ p (phiF (G1D D) (fun μ => ellD D μ) ∘ fun s : ℝ =>
        gamF K⁻¹ (resc K (TrigInterp.reconLow n K u)) (K • x + s • (K • v))) 0 :=
      (AnalyticAt.comp (g := phiF (G1D D) (fun μ => ellD D μ)) (f := fun s : ℝ =>
        gamF K⁻¹ (resc K (TrigInterp.reconLow n K u)) (K • x + s • (K • v)))
        (analyticAt_PhiDir D (jetSet_subset hdet _ _ hγS.1)
        (valSet_subset hdet _ hγS.2.1)) hγa).contDiffAt
    refine (norm_iteratedDeriv_smul_clm_le _ _ hcd).trans ?_
    rw [abs_of_nonneg hK0.le]
    calc K * ‖ContinuousLinearMap.id ℝ (ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ)‖ *
          ‖iteratedDeriv p (phiF (G1D D) (fun μ => ellD D μ) ∘ fun s : ℝ =>
            gamF K⁻¹ (resc K (TrigInterp.reconLow n K u)) (K • x + s • (K • v))) 0‖
        ≤ K * 1 * (p ! * (C₂ * (2 * (240 * ‖K • v‖) *
            max 1 (25 * 240 ^ 2 * A' / r₂)) ^ p)) := by
          gcongr
          exact norm_id_NCLM_le
      _ ≤ K * 1 * (p ! * (max C₁ C₂ * (2 * 240 * M * K) ^ p)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (hscal C₂ r₂ hC₂ hM₂ (le_max_right _ _)) (Nat.cast_nonneg _)) (by positivity)
      _ = max C₁ C₂ * K * (p ! * (2 * 240 * M * K) ^ p) := by ring

end Native

end

end RenewalGeometry.NativeLowSource
