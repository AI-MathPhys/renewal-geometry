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

end Native

end

end RenewalGeometry.NativeLowSource
