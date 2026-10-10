/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ContEulerCalculus

/-!
# Algebra of the continuum Euler covector

Generic calculus for the continuum Euler–Lagrange covector
`𝓔₀(Y)(z) = ∂_wL(J¹Y(z)) - Σ_μ ∂_μ[∂_{p_μ}L(J¹Y)](z)` (`DiscreteEulerConsistency.contEuler`) of a
first-order density `L(w, p)`, used for bridge step P3-stress of `thm:native-closure`
(Einstein–Standard-Model action-closure manuscript).

* `contEuler_add` — additivity in the density;
* `contEuler_comp_prodMap` — for a continuous linear map `P : V → W` acting on jets
  (`P̂ = P × P^4`), `𝓔₀[L ∘ P̂](Y) = 𝓔₀[L](P ∘ Y) ∘ P`;
* **`contEuler_of_null`** — the *null-direction trick*: if a smooth field `f` of directions is
  null for every jet slot, `∂_{p_μ}L(J¹Y(z'))[f(z')] = 0` for all `z'` and `μ`, then
  `𝓔₀(Y)(z)[f(z)] = DL(J¹Y(z))[J¹f(z)]`: the divergence term is absorbed by the product rule.
-/

namespace RenewalGeometry

namespace ContEulerAlg

open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The jet slot `μ`: `v ↦ (0, [·=μ]v)`. -/
def slot (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Fin 4) :
    V →L[ℝ] V × (Fin 4 → V) :=
  (ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp (ContinuousLinearMap.single ℝ (fun _ => V) μ)

theorem contEuler_eq (L : V × (Fin 4 → V) → ℝ) (Y : R4 → V) (z : R4) :
    contEuler L Y z = (fderiv ℝ L (jet1 Y z)).comp (ContinuousLinearMap.inl ℝ V (Fin 4 → V)) -
      ∑ μ, fderiv ℝ (fun z' => (fderiv ℝ L (jet1 Y z')).comp (slot V μ)) z (evec μ) := rfl

/-- **Additivity of the Euler covector in the density.** -/
theorem contEuler_add {L₁ L₂ : V × (Fin 4 → V) → ℝ} {U : Set (V × (Fin 4 → V))} (hU : IsOpen U)
    (h₁ : ContDiffOn ℝ ∞ L₁ U) (h₂ : ContDiffOn ℝ ∞ L₂ U) {Y : R4 → V} (hY : ContDiff ℝ ∞ Y)
    (hJU : ∀ y, jet1 Y y ∈ U) (z : R4) :
    contEuler (fun w => L₁ w + L₂ w) Y z = contEuler L₁ Y z + contEuler L₂ Y z := by
  have hd : ∀ y, fderiv ℝ (fun w => L₁ w + L₂ w) (jet1 Y y) =
      fderiv ℝ L₁ (jet1 Y y) + fderiv ℝ L₂ (jet1 Y y) := fun y =>
    fderiv_fun_add ((h₁.contDiffAt (hU.mem_nhds (hJU y))).differentiableAt (by simp))
      ((h₂.contDiffAt (hU.mem_nhds (hJU y))).differentiableAt (by simp))
  have hF₁ := ContEulerCalc.contDiff_fderiv_jet1 hU h₁ hY hJU
  have hF₂ := ContEulerCalc.contDiff_fderiv_jet1 hU h₂ hY hJU
  rw [contEuler_eq, contEuler_eq, contEuler_eq]
  simp only [hd, ContinuousLinearMap.add_comp]
  have hsum : ∀ μ, fderiv ℝ (fun z' => (fderiv ℝ L₁ (jet1 Y z')).comp (slot V μ) +
      (fderiv ℝ L₂ (jet1 Y z')).comp (slot V μ)) z =
      fderiv ℝ (fun z' => (fderiv ℝ L₁ (jet1 Y z')).comp (slot V μ)) z +
        fderiv ℝ (fun z' => (fderiv ℝ L₂ (jet1 Y z')).comp (slot V μ)) z := fun μ =>
    fderiv_fun_add (((hF₁.clm_comp contDiff_const).differentiable (by simp)) z)
      (((hF₂.clm_comp contDiff_const).differentiable (by simp)) z)
  simp only [hsum, ContinuousLinearMap.add_apply, Finset.sum_add_distrib]
  abel

/-- The jet map `P̂ = P × P⁴` of a continuous linear map. -/
def jetMap (P : V →L[ℝ] W) : V × (Fin 4 → V) →L[ℝ] W × (Fin 4 → W) :=
  P.prodMap (ContinuousLinearMap.pi fun μ => P.comp (ContinuousLinearMap.proj μ))

theorem jetMap_apply (P : V →L[ℝ] W) (wp : V × (Fin 4 → V)) :
    jetMap P wp = (P wp.1, fun μ => P (wp.2 μ)) := rfl

theorem jetMap_jet1 (P : V →L[ℝ] W) {Y : R4 → V} (hY : Differentiable ℝ Y) (z : R4) :
    jetMap P (jet1 Y z) = jet1 (fun y => P (Y y)) z := by
  refine Prod.ext rfl (funext fun μ => ?_)
  show P (fderiv ℝ Y z (evec μ)) = fderiv ℝ (fun y => P (Y y)) z (evec μ)
  rw [show (fun y => P (Y y)) = P ∘ Y from rfl, fderiv_comp z P.differentiableAt (hY z)]
  simp

/-- **Euler covector of a density pulled back by a linear map of the fields.** -/
theorem contEuler_comp_jetMap (P : V →L[ℝ] W) {L : W × (Fin 4 → W) → ℝ}
    {U : Set (W × (Fin 4 → W))} (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) {Y : R4 → V}
    (hY : ContDiff ℝ ∞ Y) (hJU : ∀ y, jet1 (fun y => P (Y y)) y ∈ U) (z : R4) :
    contEuler (fun w => L (jetMap P w)) Y z = (contEuler L (fun y => P (Y y)) z).comp P := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  have hPY : ContDiff ℝ ∞ (fun y => P (Y y)) := P.contDiff.comp hY
  have hdL : ∀ y, DifferentiableAt ℝ L (jetMap P (jet1 Y y)) := fun y => by
    rw [jetMap_jet1 P hYd]
    exact (hL.contDiffAt (hU.mem_nhds (hJU y))).differentiableAt (by simp)
  have hchain : ∀ y, fderiv ℝ (fun w => L (jetMap P w)) (jet1 Y y) =
      (fderiv ℝ L (jet1 (fun y => P (Y y)) y)).comp (jetMap P) := by
    intro y
    have h := ((hdL y).hasFDerivAt.comp (jet1 Y y) (jetMap P).hasFDerivAt).fderiv
    rw [jetMap_jet1 P hYd] at h
    exact h
  have hinl : (jetMap P).comp (ContinuousLinearMap.inl ℝ V (Fin 4 → V)) =
      (ContinuousLinearMap.inl ℝ W (Fin 4 → W)).comp P := by
    ext v
    · rfl
    · simp [jetMap_apply]
  have hslot : ∀ μ, (jetMap P).comp (slot V μ) = (slot W μ).comp P := by
    intro μ
    ext v ν
    · simp [jetMap_apply, slot]
    · simp only [ContinuousLinearMap.comp_apply, jetMap_apply, slot,
        ContinuousLinearMap.inr_apply, ContinuousLinearMap.single_apply]
      by_cases h : ν = μ
      · subst h; simp
      · simp [h]
  have hF := ContEulerCalc.contDiff_fderiv_jet1 hU hL hPY hJU
  set T : (W →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ V W ℝ).flip P
  have hT : ∀ A : W →L[ℝ] ℝ, T A = A.comp P := fun A => rfl
  have hfun : ∀ μ, (fun z' => (fderiv ℝ (fun w => L (jetMap P w)) (jet1 Y z')).comp (slot V μ)) =
      fun z' => T ((fderiv ℝ L (jet1 (fun y => P (Y y)) z')).comp (slot W μ)) := by
    intro μ
    funext z'
    rw [hchain, hT, ContinuousLinearMap.comp_assoc, hslot, ContinuousLinearMap.comp_assoc]
  have hd : ∀ μ, fderiv ℝ (fun z' => T ((fderiv ℝ L (jet1 (fun y => P (Y y)) z')).comp
      (slot W μ))) z = T.comp (fderiv ℝ (fun z' => (fderiv ℝ L (jet1 (fun y => P (Y y)) z')).comp
      (slot W μ)) z) := fun μ =>
    ((T.hasFDerivAt.comp z ((((hF.clm_comp contDiff_const).differentiable (by simp)) z).hasFDerivAt))
      ).fderiv
  ext v
  rw [contEuler_eq, contEuler_eq]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.comp_apply]
  congr 1
  · rw [hchain z, ContinuousLinearMap.comp_apply]
    congr 1
    exact congrArg (fun A => A v) hinl
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hfun μ, hd μ]
    rfl

/-- **The null-direction trick.**  If `f` is a smooth field of directions such that
`DL(J¹Y(z'))[(0, [·=μ]f(z'))] = 0` for every `z'` and every jet slot `μ`, then the Euler covector
in the direction `f(z)` is the derivative of `L` along the first jet of `f`:
`𝓔₀(Y)(z)[f(z)] = DL(J¹Y(z))[J¹f(z)]`. -/
theorem contEuler_of_null {L : V × (Fin 4 → V) → ℝ} {U : Set (V × (Fin 4 → V))} (hU : IsOpen U)
    (hL : ContDiffOn ℝ ∞ L U) {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) (hJU : ∀ y, jet1 Y y ∈ U)
    {f : R4 → V} (hf : ContDiff ℝ ∞ f)
    (hnull : ∀ μ z', fderiv ℝ L (jet1 Y z') (slot V μ (f z')) = 0) (z : R4) :
    contEuler L Y z (f z) = fderiv ℝ L (jet1 Y z) (jet1 f z) := by
  have hF := ContEulerCalc.contDiff_fderiv_jet1 hU hL hY hJU
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hpd : ∀ μ, fderiv ℝ (fun z' => (fderiv ℝ L (jet1 Y z')).comp (slot V μ)) z (evec μ) (f z) =
      -fderiv ℝ L (jet1 Y z) (slot V μ (fderiv ℝ f z (evec μ))) := by
    intro μ
    set G : R4 → V →L[ℝ] ℝ := fun z' => (fderiv ℝ L (jet1 Y z')).comp (slot V μ)
    have hG : DifferentiableAt ℝ G z := ((hF.clm_comp contDiff_const).differentiable (by simp)) z
    have hH := hG.hasFDerivAt.clm_apply (hfd z).hasFDerivAt
    have hzero : (fun z' => G z' (f z')) = fun _ => (0 : ℝ) := by
      funext z'
      exact hnull μ z'
    have h0 := hH.fderiv
    rw [hzero, fderiv_const_apply] at h0
    have h1 := congrArg (fun A : R4 →L[ℝ] ℝ => A (evec μ)) h0
    simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at h1
    have : fderiv ℝ G z (evec μ) (f z) = -(G z (fderiv ℝ f z (evec μ))) := by
      linarith
    exact this
  have hjet : jet1 f z = (f z, 0) + ∑ μ, slot V μ (fderiv ℝ f z (evec μ)) := by
    refine Prod.ext ?_ (funext fun ν => ?_)
    · simp [jet1, slot, Prod.fst_sum]
    · simp only [jet1, slot, Prod.snd_add, Prod.snd_sum, Pi.add_apply, Finset.sum_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.single_apply, Pi.zero_apply, zero_add]
      rw [Finset.sum_eq_single ν (fun b _ hb => by simp [Ne.symm hb])
        (by simp)]
      simp
  rw [contEuler_eq, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply]
  simp only [hpd, Finset.sum_neg_distrib, sub_neg_eq_add, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply]
  rw [hjet, map_add, map_sum]

end

end ContEulerAlg

end RenewalGeometry
