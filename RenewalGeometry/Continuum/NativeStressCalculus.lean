/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeStressAlgebra

/-!
# Coframe derivatives of the native matter densities (the Standard-Model stress)

Bridge step P3-stress of `thm:native-closure` (Einstein–Standard-Model action-closure
manuscript), matter sectors: the derivative of the Yang–Mills, Higgs and Dirac densities of the
native continuum Lagrangian `L₀` under a variation of the coframe.

* `hasDerivAt_volume_affine`, `hasDerivAt_ginv_affine`, `hasDerivAt_inv_affine` — first
  variations of `v(e)`, `g^{μν}(e)` and `e⁻¹` along `e + tδ`
  (`δv = ½ v g^{μν}δg_{μν}`, `δg^{μν} = -g^{μa}δg_{ab}g^{bν}`, `δg = δᵀηe + eᵀηδ`);
* `ymStressN`, `higgsStressN` — the Yang–Mills and Higgs stresses
  `T^{YM}_{μν} = g^{αβ}⟨F_{μα}, F_{νβ}⟩ - ¼g_{μν}⟨F, F⟩`,
  `T^H_{μν} = 2⟨K_μ, K_ν⟩ - g_{μν}(g^{αβ}⟨K_α, K_β⟩ + V(H))` (the formulas of
  `ActualJetRecon.ymStressB`, `higgsStressB`);
* **`hasDerivAt_LYMc_coframe`**, **`hasDerivAt_LHc_coframe`** — along any coframe line
  `e + tδ` (gauge and Higgs jets fixed) the bosonic matter densities move by
  `-(v/2) T_{μν} δg^{μν}`;
* `raise`, `raise_contract` — `-(v/2) T_{μν}δg^{μν} = (v/2) T^{ab}δg_{ab}`.
-/

namespace RenewalGeometry

namespace NativeStressEuler

open Finset HarmonicDefect PalatiniEuler NativeDiracEuler NativeBosonicEuler EHFieldVariation
open NativeScaling (Mat eta metric readerOmega readerG readerGamma)
open NativeDensity
open ActualJetSystem (ginvOf)
open scoped Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### First variations of the metric quantities along a coframe line -/

section Metric

/-- `δg^{lσ} = -g^{la}δg_{ab}g^{bσ}`. -/
def dgi (E δ : Mat) (l σ : Fin 4) : ℝ :=
  -∑ a, ∑ b, ginv E l a * metricVarM E δ a b * ginv E b σ

theorem ginv_eq_ginvOf (E : Mat) (a b : Fin 4) :
    ginv E a b = ginvOf (fun μ ν => metric E μ ν) a b := rfl

theorem volume_eq_volM' (E : Mat) : volume E = volM (fun μ ν => metric E μ ν) := rfl

theorem hasDerivAt_metric_affine (E δ : Mat) (μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => metric (E + s • δ) μ ν) (metricVarM E δ μ ν) 0 := by
  have hf : (fun s : ℝ => metric (E + s • δ) μ ν) =
      fun s => metric E μ ν + s * metricVarM E δ μ ν + s ^ 2 * metric δ μ ν := by
    funext s
    rw [metric_add_smul]
    simp [Matrix.add_apply, Matrix.smul_apply]
  rw [hf]
  have h := (((hasDerivAt_id' (0 : ℝ)).mul_const (metricVarM E δ μ ν)).const_add
    (metric E μ ν)).fun_add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (metric δ μ ν))
  exact h.congr_deriv (by simp)

theorem det_metric_neg {E : Mat} (hE : E.det ≠ 0) :
    (Matrix.of (fun μ ν => metric E μ ν)).det < 0 := by
  show (metric E).det < 0
  rw [det_metric]
  have : 0 < E.det ^ 2 := by positivity
  linarith

/-- `δv = ½ v g^{μν}δg_{μν}` along `e + tδ`. -/
theorem hasDerivAt_volume_affine {E : Mat} (hE : E.det ≠ 0) (δ : Mat) :
    HasDerivAt (fun t : ℝ => volume (E + t • δ))
      (1 / 2 * volume E * trG (fun a b => ginv E a b) (fun a b => metricVarM E δ a b)) 0 := by
  have h := hasDerivAt_volM_curve (G := fun s μ ν => metric (E + s • δ) μ ν)
    (k := fun μ ν => metricVarM E δ μ ν) (t := 0)
    (fun μ ν => hasDerivAt_metric_affine E δ μ ν) (by simpa using det_metric_neg hE)
    (fun μ ν => by simpa using metric_symm E μ ν)
  simp only [zero_smul, add_zero] at h
  exact h

/-- `δg^{lσ} = -g^{la}δg_{ab}g^{bσ}` along `e + tδ`. -/
theorem hasDerivAt_ginv_affine {E : Mat} (hE : E.det ≠ 0) (δ : Mat) (l σ : Fin 4) :
    HasDerivAt (fun t : ℝ => ginv (E + t • δ) l σ) (dgi E δ l σ) 0 := by
  have h := JetCurve.hasDerivAt_ginvOf (g := fun s μ ν => metric (E + s • δ) μ ν)
    (t := 0) (dg := fun _ μ ν => metricVarM E δ μ ν) 0
    (fun μ ν => hasDerivAt_metric_affine E δ μ ν) (by simpa using (det_metric_neg hE).ne) l σ
  simp only [zero_smul, add_zero] at h
  exact h

theorem ginv_symm (E : Mat) (a b : Fin 4) : ginv E a b = ginv E b a :=
  NativeBosonicEuler.ginv_symm' E a b

theorem metricVarM_symm (E δ : Mat) (a b : Fin 4) :
    metricVarM E δ a b = metricVarM E δ b a := by
  unfold metricVarM
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [add_comm]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [PalatiniEuler.eta_symm j i]; ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [PalatiniEuler.eta_symm j i]; ring

theorem sum_metric_ginv {E : Mat} (hE : E.det ≠ 0) (a c : Fin 4) :
    ∑ b, metric E a b * ginv E b c = if a = c then 1 else 0 :=
  metric_mul_inv hE a c

/-- Reordering four finite sums. -/
theorem sum4_swap {M : Type*} [AddCommMonoid M] (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → M) :
    ∑ μ, ∑ ν, ∑ a, ∑ b, f μ ν a b = ∑ a, ∑ b, ∑ μ, ∑ ν, f μ ν a b := by
  calc ∑ μ, ∑ ν, ∑ a, ∑ b, f μ ν a b = ∑ μ, ∑ a, ∑ ν, ∑ b, f μ ν a b :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_comm
    _ = ∑ μ, ∑ a, ∑ b, ∑ ν, f μ ν a b :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ μ, ∑ b, ∑ ν, f μ ν a b := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ μ, ∑ ν, f μ ν a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- `Σ g_{μν}δg^{μν} = -g^{ab}δg_{ab}`. -/
theorem sum_metric_dgi {E : Mat} (hE : E.det ≠ 0) (δ : Mat) :
    ∑ μ, ∑ ν, metric E μ ν * dgi E δ μ ν =
      -trG (fun a b => ginv E a b) (fun a b => metricVarM E δ a b) := by
  unfold dgi trG
  simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
  congr 1
  have h1 : ∀ a b, ∑ μ, ∑ ν, metric E μ ν * (ginv E μ a * metricVarM E δ a b * ginv E b ν) =
      ginv E a b * metricVarM E δ a b := by
    intro a b
    have : ∀ μ, ∑ ν, metric E μ ν * (ginv E μ a * metricVarM E δ a b * ginv E b ν) =
        ginv E μ a * metricVarM E δ a b * ∑ ν, metric E μ ν * ginv E ν b := by
      intro μ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [ginv_symm E b ν]; ring
    simp only [this, sum_metric_ginv hE, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    rw [ginv_symm E b a]
  rw [sum4_swap (fun μ ν a b => metric E μ ν * (ginv E μ a * metricVarM E δ a b * ginv E b ν))]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h1 a b

/-- Raised indices `T^{ab} = g^{aμ}g^{bν}T_{μν}`. -/
def raise (E : Mat) (T : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) : ℝ :=
  ∑ μ, ∑ ν, ginv E a μ * ginv E b ν * T μ ν

/-- `-T_{μν}δg^{μν} = T^{ab}δg_{ab}`. -/
theorem raise_contract (E δ : Mat) (T : Fin 4 → Fin 4 → ℝ) :
    -∑ μ, ∑ ν, T μ ν * dgi E δ μ ν = ∑ a, ∑ b, raise E T a b * metricVarM E δ a b := by
  unfold dgi raise
  simp only [mul_neg, Finset.sum_neg_distrib, neg_neg, Finset.mul_sum, Finset.sum_mul]
  rw [sum4_swap (fun μ ν a b => T μ ν * (ginv E μ a * metricVarM E δ a b * ginv E b ν))]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [ginv_symm E μ a]
  ring

theorem sum4_swap23 {M : Type*} [AddCommMonoid M] (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
  Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem sum4_swap12_34 {M : Type*} [AddCommMonoid M] (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ a, ∑ d, ∑ c, f a b c d := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

end Metric

/-! ### The bosonic matter stresses -/

section Bosonic

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- The Yang–Mills stress `T^{YM}_{μν} = g^{αβ}⟨F_{μα}, F_{νβ}⟩ - ¼g_{μν}g^{αγ}g^{βδ}⟨F_{αβ},
F_{γδ}⟩` of a first jet (the formula of `ActualJetRecon.ymStressB`). -/
def ymStressN (wp : FJ 𝔄 𝓗 𝓢) (μ ν : Fin 4) : ℝ :=
  ∑ α, ∑ β, ginv wp.1.1 α β * D.ipA (FA wp μ α) (FA wp ν β) -
    1 / 4 * metric wp.1.1 μ ν * ∑ α, ∑ β, ∑ γ, ∑ δ, ginv wp.1.1 α γ * ginv wp.1.1 β δ *
      D.ipA (FA wp α β) (FA wp γ δ)

/-- The Higgs stress `T^H_{μν} = 2⟨K_μ, K_ν⟩ - g_{μν}(g^{αβ}⟨K_α, K_β⟩ + V(H))` of a first jet
(the formula of `ActualJetRecon.higgsStressB`). -/
def higgsStressN (wp : FJ 𝔄 𝓗 𝓢) (μ ν : Fin 4) : ℝ :=
  2 * D.hermH (KH D wp μ) (KH D wp ν) -
    metric wp.1.1 μ ν * (∑ α, ∑ β, ginv wp.1.1 α β * D.hermH (KH D wp α) (KH D wp β) +
      potential D wp.1.2.2.1)

/-- The Yang–Mills variation algebra. -/
theorem ym_alg {E δ : Mat} (hE : E.det ≠ 0) (B : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hB : ∀ μ ν ρ σ, B ν μ σ ρ = B μ ν ρ σ) (v : ℝ) :
    -(4⁻¹ * (1 / 2 * v * trG (fun a b => ginv E a b) (fun a b => metricVarM E δ a b)) *
        (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ginv E μ ρ * ginv E ν σ * B μ ν ρ σ) +
      4⁻¹ * v * ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
        (dgi E δ μ ρ * ginv E ν σ + ginv E μ ρ * dgi E δ ν σ) * B μ ν ρ σ) =
    -(v / 2) * ∑ μ, ∑ ν, (∑ α, ∑ β, ginv E α β * B μ α ν β -
      1 / 4 * metric E μ ν * ∑ α, ∑ β, ∑ γ, ∑ δ', ginv E α γ * ginv E β δ' * B α β γ δ') *
        dgi E δ μ ν := by
  set tr := trG (fun a b => ginv E a b) (fun a b => metricVarM E δ a b)
  set Q := ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ginv E μ ρ * ginv E ν σ * B μ ν ρ σ
  set Y := ∑ μ, ∑ ν, ∑ ρ, ∑ σ, dgi E δ μ ρ * ginv E ν σ * B μ ν ρ σ
  have hY2 : ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
      (dgi E δ μ ρ * ginv E ν σ + ginv E μ ρ * dgi E δ ν σ) * B μ ν ρ σ = 2 * Y := by
    have h2 : ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ginv E μ ρ * dgi E δ ν σ * B μ ν ρ σ = Y := by
      rw [sum4_swap12_34 (fun μ ν ρ σ => ginv E μ ρ * dgi E δ ν σ * B μ ν ρ σ)]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      rw [← hB a b c d]; ring
    simp only [add_mul, Finset.sum_add_distrib, h2]
    ring
  have hX : ∑ μ, ∑ ν, (∑ α, ∑ β, ginv E α β * B μ α ν β) * dgi E δ μ ν = Y := by
    simp only [Finset.sum_mul]
    rw [sum4_swap23 (fun μ ν α β => ginv E α β * B μ α ν β * dgi E δ μ ν)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hM := sum_metric_dgi hE δ
  have hsplit : ∑ μ, ∑ ν, (∑ α, ∑ β, ginv E α β * B μ α ν β -
      1 / 4 * metric E μ ν * Q) * dgi E δ μ ν =
      ∑ μ, ∑ ν, (∑ α, ∑ β, ginv E α β * B μ α ν β) * dgi E δ μ ν -
        1 / 4 * Q * ∑ μ, ∑ ν, metric E μ ν * dgi E δ μ ν := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    ring
  rw [hY2, hsplit, hX, hM]
  ring

/-- **The Yang–Mills density along a coframe line**: if the gauge jets are fixed and the coframe
moves along `e + tδ`, `d/dt L_{YM} = -(v/2) T^{YM}_{μν} δg^{μν}`. -/
theorem hasDerivAt_LYMc_coframe (wp d : FJ 𝔄 𝓗 𝓢) (hE : wp.1.1.det ≠ 0) (δ : Mat)
    (he : ∀ t : ℝ, (wp + t • d).1.1 = wp.1.1 + t • δ)
    (hF : ∀ (t : ℝ) μ ν, FA (wp + t • d) μ ν = FA wp μ ν) :
    HasDerivAt (fun t : ℝ => LYMc D (wp + t • d))
      (-(volume wp.1.1 / 2) * ∑ μ, ∑ ν, ymStressN D wp μ ν * dgi wp.1.1 δ μ ν) 0 := by
  set E := wp.1.1
  set B : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun μ ν ρ σ => D.ipA (FA wp μ ν) (FA wp ρ σ)
    with hBdef
  have hB : ∀ μ ν ρ σ, B ν μ σ ρ = B μ ν ρ σ := by
    intro μ ν ρ σ
    simp only [hBdef, FA_anti wp ν μ, FA_anti wp σ ρ, map_neg, neg_apply,
      neg_neg]
  have hfun : (fun t : ℝ => LYMc D (wp + t • d)) = fun t => -(4⁻¹ * volume (E + t • δ) *
      ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ginv (E + t • δ) μ ρ * ginv (E + t • δ) ν σ * B μ ν ρ σ) := by
    funext t
    unfold LYMc
    simp only [he, hF, hBdef]
  rw [hfun]
  have hg := hasDerivAt_ginv_affine hE δ
  have hsum : HasDerivAt (fun t : ℝ => ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
      ginv (E + t • δ) μ ρ * ginv (E + t • δ) ν σ * B μ ν ρ σ)
      (∑ μ, ∑ ν, ∑ ρ, ∑ σ, (dgi E δ μ ρ * ginv E ν σ + ginv E μ ρ * dgi E δ ν σ) *
        B μ ν ρ σ) 0 := by
    refine HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun ν _ =>
      HasDerivAt.fun_sum fun ρ _ => HasDerivAt.fun_sum fun σ _ => ?_
    have h := ((hg μ ρ).fun_mul (hg ν σ)).mul_const (B μ ν ρ σ)
    simpa only [zero_smul, add_zero] using h
  have hv := hasDerivAt_volume_affine hE δ
  have htot := ((hv.const_mul 4⁻¹).fun_mul hsum).neg
  simp only [zero_smul, add_zero] at htot
  refine htot.congr_deriv ?_
  exact ym_alg hE B hB (volume E)

/-- **The Higgs density along a coframe line**: if the Higgs and gauge jets are fixed and the
coframe moves along `e + tδ`, `d/dt L_H = -(v/2) T^H_{μν} δg^{μν}`. -/
theorem hasDerivAt_LHc_coframe (wp d : FJ 𝔄 𝓗 𝓢) (hE : wp.1.1.det ≠ 0) (δ : Mat)
    (he : ∀ t : ℝ, (wp + t • d).1.1 = wp.1.1 + t • δ)
    (hK : ∀ (t : ℝ) μ, KH D (wp + t • d) μ = KH D wp μ)
    (hH : ∀ t : ℝ, (wp + t • d).1.2.2.1 = wp.1.2.2.1) :
    HasDerivAt (fun t : ℝ => LHc D (wp + t • d))
      (-(volume wp.1.1 / 2) * ∑ μ, ∑ ν, higgsStressN D wp μ ν * dgi wp.1.1 δ μ ν) 0 := by
  set E := wp.1.1
  set P := ∑ α, ∑ β, ginv E α β * D.hermH (KH D wp α) (KH D wp β)
  set pot := potential D wp.1.2.2.1
  have hfun : (fun t : ℝ => LHc D (wp + t • d)) = fun t =>
      -(volume (E + t • δ) * ∑ μ, ∑ ν, ginv (E + t • δ) μ ν *
        D.hermH (KH D wp μ) (KH D wp ν)) - volume (E + t • δ) * pot := by
    funext t
    unfold LHc
    simp only [he, hK, hH]
    rfl
  rw [hfun]
  have hg := hasDerivAt_ginv_affine hE δ
  have hsum : HasDerivAt (fun t : ℝ => ∑ μ, ∑ ν, ginv (E + t • δ) μ ν *
      D.hermH (KH D wp μ) (KH D wp ν))
      (∑ μ, ∑ ν, dgi E δ μ ν * D.hermH (KH D wp μ) (KH D wp ν)) 0 :=
    HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun ν _ =>
      (hg μ ν).mul_const _
  have hv := hasDerivAt_volume_affine hE δ
  have htot := (hv.fun_mul hsum).neg.sub (hv.mul_const pot)
  simp only [zero_smul, add_zero] at htot
  refine htot.congr_deriv ?_
  have hM := sum_metric_dgi hE δ
  have hsplit : ∑ μ, ∑ ν, higgsStressN D wp μ ν * dgi E δ μ ν =
      2 * ∑ μ, ∑ ν, dgi E δ μ ν * D.hermH (KH D wp μ) (KH D wp ν) -
        (P + pot) * ∑ μ, ∑ ν, metric E μ ν * dgi E δ μ ν := by
    unfold higgsStressN
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      ring
    · refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      ring
  rw [hsplit, hM]
  ring

end Bosonic

end

end NativeStressEuler

end RenewalGeometry
