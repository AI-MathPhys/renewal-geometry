/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeRecordTuple

/-!
# The Dirac residuals of the actual tuple of a native field

Einstein–Standard-Model action-closure manuscript, `thm:native-closure`, bridge step P2 (Dirac
rows): for a native field satisfying `RecordTuple.TupleHyp`, the Dirac residuals of its actual
field tuple `RecordTuple.toTuple` (slab theory data `SlabData.toSMData`) are the native ones:

* **`rD_toTuple`** — `r_D = Σ_b ε_bc_bX_b - 𝓜(H)Ψ` is the native Dirac residual
  `NativeModel.diracRes = Jγ^μ(e)∇_μΨ - 𝓜_𝐘(H)Ψ`;
* **`rDb_toTuple`** — the dual residual `Σ_b ε_bc̄_bX̄_b - 𝓜̄(H)Ψ̄` (transposed Clifford frame,
  `c̄_bΨ̄ = Ψ̄∘c_b`) is the native dual residual `NativeModel.diracResBar = (∇_μΨ̄)γ^μJ + Ψ̄𝓜_𝐘(H)`.

Generic: `spinPart_cliffMap`, `spinPart_cliffAnti`, `resD_cliffMap`.
-/

open Finset
open scoped Matrix

namespace RenewalGeometry.RecordTuple

open SobolevOpen (pd)
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open NativeScaling (Mat eta metric readerOmega readerG)
open NativeDensity NativeModel NativeFrameBridge NativeBosonicEuler NativeDiracEuler PalatiniEuler
open ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetFrame SlabData SpinorProlongation
open TwistedHalfRicci (CliffordFrame)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Generic transport of the spin part and of the Dirac residual -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]

theorem spinPart_cliffMap (Fr : CliffordFrame ι A) (f : A →ₐ[ℝ] B) (W : ι → ι → ℝ) :
    spinPart (cliffMap Fr f) W = f (spinPart Fr W) := by
  unfold spinPart cliffMap
  simp only [map_smul, map_sum, map_mul]

theorem spinPart_cliffAnti (Fr : CliffordFrame ι A) (f : A →ₗ[ℝ] B) (hf1 : f 1 = 1)
    (hmul : ∀ x y, f (x * y) = f y * f x) (W : ι → ι → ℝ) :
    spinPart (cliffAnti Fr f hf1 hmul) W = f (spinPart Fr fun c d => W d c) := by
  unfold spinPart cliffAnti
  simp only [map_smul, map_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [← hmul]
  congr 1
  ring

theorem spinPart_neg (Fr : CliffordFrame ι A) (W : ι → ι → ℝ) :
    spinPart Fr (fun c d => -W c d) = -spinPart Fr W := by
  unfold spinPart
  simp only [mul_neg, neg_smul, Finset.sum_neg_distrib, smul_neg]

variable {S W : Type*} [AddCommGroup S] [Module ℝ S] [AddCommGroup W] [Module ℝ W]

/-- The slab Dirac residual is unchanged when the Clifford data are transported to `Module.End`
along `T ↦ T` (the action of `toEndAlg T` is the application of `T`). -/
theorem resD_toEnd {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢]
    (Fr : CliffordFrame ι (𝓢 →L[ℝ] 𝓢)) (ω : ι → (𝓢 →L[ℝ] 𝓢)) (L : W →ₗ[ℝ] (𝓢 →L[ℝ] 𝓢))
    (h : W) (ψ : 𝓢) (dψ : ι → 𝓢) :
    resD (cliffMap Fr toEndAlg) (fun b => toEndAlg (ω b)) (0 : Module.End ℝ 𝓢)
        (toEndAlg.toLinearMap.comp L) h ψ dψ =
      resD Fr ω (0 : 𝓢 →L[ℝ] 𝓢) L h ψ dψ := by
  unfold resD dirac cov mass cliffMap
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, zero_add, Module.End.smul_def]
  rfl

end Generic

/-! ### The spinor residual -/

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} {M : SlabModel 𝔄 𝓗 𝓢 m}
variable {δ : ℝ} {Y : R4 → Field 𝔄 𝓗 𝓢} (hδ : 0 < δ) (h : TupleHyp M δ Y)

include hδ h in
/-- The frame connection coefficients of the tuple are those of the native frame. -/
theorem G_toTuple (x : R4) (B : Fin 4) :
    Gfun ((toTuple hδ h).jet x).FJ.g ((toTuple hδ h).jet x).FJ.gi ((toTuple hδ h).jet x).FJ.dg
        ((toTuple hδ h).jet x).AF.fr ((toTuple hδ h).jet x).FJ.de B =
      Gfun (fun a b => metric (Y x).1 a b) (fun a b => (metric (Y x).1)⁻¹ a b)
        (readerG (Y x).1 (qJ Y x)) (fun A μ => ((Y x).1)⁻¹ μ A)
        (fun γ B μ => -(((Y x).1)⁻¹ * qJ Y x γ * ((Y x).1)⁻¹) μ B) B := by
  have he : ((toTuple hδ h).jet x).AF.fr = fun A μ => ((Y x).1)⁻¹ μ A := by
    rw [← ((toTuple hδ h).jet x).e_eq]
    funext A μ
    exact e_toTuple hδ h x A μ
  have hde : ((toTuple hδ h).jet x).FJ.de =
      fun γ B μ => -(((Y x).1)⁻¹ * qJ Y x γ * ((Y x).1)⁻¹) μ B := by
    funext γ B μ
    exact de_toTuple hδ h x γ B μ
  have hdg : ((toTuple hδ h).jet x).FJ.dg = fun α i j => readerG (Y x).1 (qJ Y x) α i j :=
    dg_toTuple hδ h x
  rw [he, hde, hdg]
  rfl

include hδ h in
/-- **The slab spin connection of the tuple is the native one** (spinor block). -/
theorem omega_D_toTuple (x : R4) (B : Fin 4) :
    (((toTuple hδ h).jet x).LJ (diracD M)).ω B =
      toEndAlg (slabOmega M.toModel (Y x).1 (qJ Y x) (Y x).2.1 B) := by
  rw [ActualJet.LJ_ω]
  unfold omegaU slabOmega
  rw [G_toTuple hδ h x B]
  have he : ((toTuple hδ h).jet x).AF.fr = fun A μ => ((Y x).1)⁻¹ μ A := by
    rw [← ((toTuple hδ h).jet x).e_eq]
    funext A μ
    exact e_toTuple hδ h x A μ
  rw [he]
  show spinPart (cliffMap (slabCliff M.toModel) toEndAlg) _ +
      ∑ μ, ((Y x).1)⁻¹ μ B • toEndAlg (rhoSL M (M.φ ((Y x).2.1 μ))) = _
  rw [spinPart_cliffMap, map_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_smul, rhoSL_apply, AlgEquiv.symm_apply_apply]

include hδ h in
set_option maxHeartbeats 1600000 in
/-- **The Dirac residual of the tuple is the native Dirac residual.** -/
theorem rD_toTuple (x : R4) :
    ((toTuple hδ h).jet x).rD (diracD M) ((toTuple hδ h).jet x).ψ ((toTuple hδ h).jet x).cψ =
      diracRes M.toModel Y x := by
  set z := toTuple hδ h
  have hYd : Differentiable ℝ Y := h.smooth.differentiable (by simp)
  unfold ActualJet.rD
  have hω : ((z.jet x).LJ (diracD M)).ω =
      fun B => toEndAlg (slabOmega M.toModel (Y x).1 (qJ Y x) (Y x).2.1 B) :=
    funext fun B => omega_D_toTuple hδ h x B
  rw [hω]
  have hdψ : ActualJetSpinor.dψf (z.jet x).FJ (z.jet x).cψ =
      fun B => ∑ γ, ((Y x).1)⁻¹ γ B • ((jet1 Y x).2 γ).2.2.2.1 := by
    funext B
    unfold ActualJetSpinor.dψf
    refine Finset.sum_congr rfl fun γ _ => ?_
    have h1 : (z.jet x).FJ.e B γ = ((Y x).1)⁻¹ γ B := e_toTuple hδ h x B γ
    have h2 : (z.jet x).cψ γ = ((jet1 Y x).2 γ).2.2.2.1 := by
      show pd z.ψ γ x = _
      exact (pd_clm (projψ (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) (hYd x) γ)
    rw [h1, h2]
  rw [hdψ]
  show resD (cliffMap (slabCliff M.toModel) toEndAlg) _ (0 : Module.End ℝ 𝓢)
    (toEndAlg.toLinearMap.comp (yukL M)) _ _ _ = _
  rw [resD_toEnd]
  have hs := slab_resD_eq M.toModel (h.det_ne x) (qJ Y x) (Y x).2.1 (Y x).2.2.1 (Y x).2.2.2.1
    (fun γ => ((jet1 Y x).2 γ).2.2.2.1)
  refine hs.trans ?_
  have hq : (fun l => ((jet1 Y x).2 l).1) = qJ Y x := by
    funext l
    exact (pd_clm (ContinuousLinearMap.fst ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢))
      (hYd x) l).symm
  unfold diracRes DPsi omC
  rw [hq]
  rfl

/-! ### The co-spinor residual -/

include hδ h in
/-- **The slab spin connection of the tuple on co-spinors** is `-(·∘ω_B)` with the native spinor
connection `ω_B` (`G_{Bcd}` is antisymmetric in `c, d`). -/
theorem omega_Db_toTuple (x : R4) (B : Fin 4) :
    (((toTuple hδ h).jet x).LJ (diracDb M)).ω B =
      -transL (slabOmega M.toModel (Y x).1 (qJ Y x) (Y x).2.1 B) := by
  set J := (toTuple hδ h).jet x
  rw [ActualJet.LJ_ω]
  unfold omegaU
  have hGa : (fun c d => Gfun J.FJ.g J.FJ.gi J.FJ.dg J.AF.fr J.FJ.de B d c) =
      fun c d => -Gfun J.FJ.g J.FJ.gi J.FJ.dg J.AF.fr J.FJ.de B c d := by
    funext c d
    rw [← J.G_eq]
    exact J.FJ.G_anti B c d
  show spinPart (cliffAnti (slabCliff M.toModel) transL transL_one transL_mul) _ +
      ∑ μ, J.AF.fr B μ • negRho M (M.φ ((Y x).2.1 μ)) = _
  rw [spinPart_cliffAnti, hGa, spinPart_neg, G_toTuple hδ h x B]
  have he : J.AF.fr = fun A μ => ((Y x).1)⁻¹ μ A := by
    rw [← J.e_eq]
    funext A μ
    exact e_toTuple hδ h x A μ
  rw [he]
  unfold slabOmega
  ext φ χ
  simp [negRho_apply, rhoSL_apply, transL_apply, map_sum, Finset.sum_apply]
  ring

include hδ h in
/-- The co-spinor covariant jets of the tuple: `X̄_B = e_B{}^γ∇_γΨ̄`. -/
theorem cov_Db_toTuple (x : R4) (B : Fin 4) :
    cov (((toTuple hδ h).jet x).LJ (diracDb M)).ω ((toTuple hδ h).jet x).ψb
        (ActualJetSpinor.dψf ((toTuple hδ h).jet x).FJ ((toTuple hδ h).jet x).cψb) B =
      ∑ γ, ((Y x).1)⁻¹ γ B • DPsiBar M.toData (jet1 Y x) γ := by
  set J := (toTuple hδ h).jet x
  have hYd : Differentiable ℝ Y := h.smooth.differentiable (by simp)
  have hq : (fun l => ((jet1 Y x).2 l).1) = qJ Y x := by
    funext l
    exact (pd_clm (ContinuousLinearMap.fst ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢))
      (hYd x) l).symm
  unfold cov
  rw [omega_Db_toTuple hδ h x B, slabOmega_eq M.toModel (h.det_ne x)]
  unfold ActualJetSpinor.dψf
  have h1 : ∀ γ, J.FJ.e B γ = ((Y x).1)⁻¹ γ B := fun γ => e_toTuple hδ h x B γ
  have h2 : ∀ γ, J.cψb γ = ((jet1 Y x).2 γ).2.2.2.2 := fun γ =>
    (pd_clm (projψb (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) (hYd x) γ)
  simp only [h1, h2]
  unfold DPsiBar omC
  rw [hq]
  have hψb : J.ψb = (Y x).2.2.2.2 := rfl
  rw [hψb]
  ext χ
  simp [Module.End.smul_def, transL_apply, map_sum, Finset.sum_apply, LinearMap.sum_apply,
    Finset.smul_sum, smul_add, Finset.sum_add_distrib, jet1_fst]
  simp only [mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

include hδ h in
set_option maxHeartbeats 1600000 in
/-- **The dual Dirac residual of the tuple is the native dual Dirac residual.** -/
theorem rDb_toTuple (x : R4) :
    ((toTuple hδ h).jet x).rD (diracDb M) ((toTuple hδ h).jet x).ψb ((toTuple hδ h).jet x).cψb =
      diracResBar M.toModel Y x := by
  set J := (toTuple hδ h).jet x
  unfold ActualJet.rD resD dirac mass
  have hc : ∀ b, cov (J.LJ (diracDb M)).ω J.ψb (ActualJetSpinor.dψf J.FJ J.cψb) b =
      ∑ γ, ((Y x).1)⁻¹ γ b • DPsiBar M.toData (jet1 Y x) γ := cov_Db_toTuple hδ h x
  simp only [hc]
  unfold diracResBar
  have hψb : J.ψb = (Y x).2.2.2.2 := rfl
  have hH : J.H = (Y x).2.2.1 := rfl
  rw [hψb, hH]
  ext χ
  simp [cliffAnti, slabCliff_c, transL_apply, negYuk_apply, yukL_apply, Module.End.smul_def,
    map_sum, Finset.sum_apply, LinearMap.sum_apply, Finset.smul_sum, smul_smul, gammaMu_eq,
    diracDb]
  have hy : ((negYuk M) (show HSp M from (Y x).2.2.1) (Y x).2.2.2.2) χ =
      -((Y x).2.2.2.2 ((M.yukawa (Y x).2.2.1) χ)) := rfl
  erw [hy]
  rw [sub_neg_eq_add, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun b _ => ?_
  have hJ : M.J ((M.γ b) χ) = (M.γ b) (M.J χ) := by
    rw [← ContinuousLinearMap.mul_apply, M.J_gamma, ContinuousLinearMap.mul_apply]
  have hε : ((lorentzSign b : ℝ) : ℂ) * (lorentzSign b : ℂ) = 1 := by
    exact_mod_cast NativeFrameBridge.lorentzSign_sq b
  rw [hJ, slabCliff_ε]
  linear_combination ((((Y x).1)⁻¹ γ b : ℂ) * (DPsiBar M.toData (jet1 Y x) γ) ((M.γ b) (M.J χ))) * hε

end

end RenewalGeometry.RecordTuple
