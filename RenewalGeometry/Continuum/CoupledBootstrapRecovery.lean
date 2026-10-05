/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CoupledActualJetBootstrap
import RenewalGeometry.Continuum.SlabDifferenceCalculus
import RenewalGeometry.Analysis.SobolevChainRule

/-!
# Curvature and stress recovery in `prop:coupled-bootstrap` (`eq:bootstrap-curvature`)

Einstein–Standard-Model action-closure manuscript, `prop:coupled-bootstrap`, the last paragraph
of the proof: "The equation bounds `∂_tW` in `L²_tH^{k-1}_x` by the same state and forcing
quantities. Recover ordinary first metric derivatives algebraically from `(g,p,q)`, and
differentiate these identities once, using the metric first-jet rows for the time derivative. All
second metric derivatives then differ by `O(d)` in `L²_tH^{k-1}`. The coordinate curvature
formula, linear in these second derivatives and quadratic in first derivatives, proves the
curvature estimate. For the complete stress, normal-spinor elimination gives smooth algebraic maps
with `T^{SM}(z) = 𝒯_0(𝒰) + 𝒯_1(𝒰)(r_D, r̄_D)`."

* `RiemF` — the coordinate Riemann tensor `R^l{}_{σγρ}` of the metric of a tuple
  (`FrameCurvature.rie` of the Christoffel jets);
* `riem_affine` — `RiemF = Ψ₀(𝒰) + Σ_{δ,b} Ψ₁^{δb}(𝒰) ∂_δu_b` with coefficient maps smooth on the
  chart (`rie_split`: linear in the second metric derivatives; `ddg_chain`: the second metric
  derivatives are the derivatives of the reconstructed first jets `dgOf(𝒰)`);
* `TactF`, `stress_affine` — the complete off-shell stress
  `T^{SM} = 𝒯_0(𝒰) - Σ_i 𝒯_1^i(𝒰) R_{D,i}` (`ActualJetSystem.ActualJet.Tact_eq`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.CoupledBootstrap

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy QLDiff QLRecovery FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetCompleteForcing ActualJetState ActualJetRecon SpinorProlongation
  TwistedHalfRicci

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### The Riemann tensor is affine in the second metric derivatives -/

/-- Curvature components are indexed by `(l, σ, γ, ρ)`. -/
abbrev RIdx := Fin 4 × Fin 4 × Fin 4 × Fin 4

/-- The part of `R^l{}_{σγρ}` free of second metric derivatives. -/
def rieP (gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (c : RIdx) : ℝ :=
  dchr1 gi dg c.2.2.1 c.1 c.2.2.2 c.2.1 - dchr1 gi dg c.2.2.2 c.1 c.2.2.1 c.2.1 +
    ∑ κ, (chr gi dg c.1 c.2.2.1 κ * chr gi dg κ c.2.2.2 c.2.1 -
      chr gi dg c.1 c.2.2.2 κ * chr gi dg κ c.2.2.1 c.2.1)

/-- The part of `R^l{}_{σγρ}` linear in the second metric derivatives. -/
def rieLin (gi : Fin 4 → Fin 4 → ℝ) (D : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (c : RIdx) : ℝ :=
  dchr2 gi D c.2.2.1 c.1 c.2.2.2 c.2.1 - dchr2 gi D c.2.2.2 c.1 c.2.2.1 c.2.1

theorem rie_split (gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (ddg : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (c : RIdx) :
    rie (chr gi dg) (dchr gi dg ddg) c.1 c.2.1 c.2.2.1 c.2.2.2 = rieP gi dg c + rieLin gi ddg c := by
  unfold rie dchr rieP rieLin
  ring

theorem dchr2_sum {ι : Type*} (s : Finset ι) (gi : Fin 4 → Fin 4 → ℝ) (w : ι → ℝ)
    (D : ι → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (δ l μ ν : Fin 4) :
    dchr2 gi (fun δ α μ ν => ∑ q ∈ s, w q * D q δ α μ ν) δ l μ ν =
      ∑ q ∈ s, w q * dchr2 gi (D q) δ l μ ν := by
  have key : ∀ σ, gi l σ * (∑ q ∈ s, w q * D q δ μ σ ν + ∑ q ∈ s, w q * D q δ ν σ μ -
      ∑ q ∈ s, w q * D q δ σ μ ν) =
      ∑ q ∈ s, w q * (gi l σ * (D q δ μ σ ν + D q δ ν σ μ - D q δ σ μ ν)) := by
    intro σ
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  unfold dchr2
  simp_rw [key]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem rieLin_sum {ι : Type*} (s : Finset ι) (gi : Fin 4 → Fin 4 → ℝ) (w : ι → ℝ)
    (D : ι → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (c : RIdx) :
    rieLin gi (fun δ α μ ν => ∑ q ∈ s, w q * D q δ α μ ν) c = ∑ q ∈ s, w q * rieLin gi (D q) c := by
  unfold rieLin
  rw [dchr2_sum, dchr2_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring


/-! ### Coefficient maps of the curvature and the stress -/

section Coefficients

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')

/-- The inverse metric as a function of the state coordinates. -/
def Φgi (l σ : Fin 4) (v : Fin n → ℝ) : ℝ := ginvOf (eX v).1.1 l σ

/-- The reconstructed metric first jet `∂_αg_{μν}` as a function of the state coordinates. -/
def Φdg (α μ ν : Fin 4) (v : Fin n → ℝ) : ℝ := dgOf (eX v).1 α μ ν

/-- Its partial derivatives in the state coordinates. -/
def dΦdg (b : Fin n) (α μ ν : Fin 4) (v : Fin n → ℝ) : ℝ :=
  fderiv ℝ (Φdg eX α μ ν) v (Pi.single b 1)

/-- The curvature coefficient free of derivatives of the state. -/
def Ψ0 (c : RIdx) (v : Fin n → ℝ) : ℝ :=
  rieP (fun l σ => Φgi eX l σ v) (fun α μ ν => Φdg eX α μ ν v) c

/-- The curvature coefficient of `∂_δu_b`, `p = (δ, b)`. -/
def Ψ1 (c : RIdx) (p : Fin 4 × Fin n) (v : Fin n → ℝ) : ℝ :=
  rieLin (fun l σ => Φgi eX l σ v)
    (fun δ α μ ν => if δ = p.1 then dΦdg eX p.2 α μ ν v else 0) c

theorem contDiffAt_Φgi {v : Fin n → ℝ} (hv : v ∈ chartC eX) (l σ : Fin 4) :
    ContDiffAt ℝ ∞ (Φgi eX l σ) v := by
  have h : ContDiffAt ℝ ∞ (fun v => (eX v).1.1) v := by fun_prop
  exact ContDiffAt.ginvOf h hv.1 l σ

theorem contDiffAt_Φdg {v : Fin n → ℝ} (hv : v ∈ chartC eX) (α μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (Φdg eX α μ ν) v := by
  have h : ContDiffAt ℝ ∞ (fun v => (eX v).1) v := by fun_prop
  exact ContDiffAt.comp (g := fun y => dgOf y α μ ν) (f := fun v => (eX v).1) v
    (contDiffAt_dgOf hv α μ ν) h

theorem contDiffAt_dΦdg {v : Fin n → ℝ} (hv : v ∈ chartC eX) (b : Fin n) (α μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (dΦdg eX b α μ ν) v := by
  have hO := (isOpen_chartC eX).mem_nhds hv
  have h : ContDiffAt ℝ ∞ (Φdg eX α μ ν) v := contDiffAt_Φdg eX hv α μ ν
  have h2 : ContDiffAt ℝ ∞ (fderiv ℝ (Φdg eX α μ ν)) v := h.fderiv_right (m := ∞) le_rfl
  exact h2.clm_apply contDiffAt_const

theorem contDiffOn_Ψ0 (c : RIdx) : ContDiffOn ℝ ∞ (Ψ0 eX c) (chartC eX) := by
  intro v hv
  have h1 := contDiffAt_Φgi eX hv
  have h2 := contDiffAt_Φdg eX hv
  refine ContDiffAt.contDiffWithinAt ?_
  unfold Ψ0 rieP dchr1 dginv chr
  fun_prop

theorem contDiffOn_Ψ1 (c : RIdx) (p : Fin 4 × Fin n) :
    ContDiffOn ℝ ∞ (Ψ1 eX c p) (chartC eX) := by
  intro v hv
  have h1 := contDiffAt_Φgi eX hv
  have h3 := contDiffAt_dΦdg eX hv
  have h4 : ∀ δ α μ ν, ContDiffAt ℝ ∞
      (fun v => if δ = p.1 then dΦdg eX p.2 α μ ν v else 0) v := by
    intro δ α μ ν
    by_cases h : δ = p.1
    · simp only [h, ite_true]; exact h3 _ _ _ _
    · simp only [h, ite_false]; exact contDiffAt_const
  refine ContDiffAt.contDiffWithinAt ?_
  unfold Ψ1 rieLin dchr2
  fun_prop

variable (z : Tuple m V S S')

theorem eX_uC (x : ST 3) : eX (fun b => uC SM eX z b x) = stateF SM z x := by
  rw [uC_vec, ContinuousLinearEquiv.apply_symm_apply]

theorem uC_mem_chart (x : ST 3) : (fun b => uC SM eX z b x) ∈ chartC eX := by
  show MetChart (eX (fun b => uC SM eX z b x)).1
  rw [eX_uC]
  exact ⟨z.det_ne x, z.lor x⟩

theorem gi_eq_Φ (x : ST 3) (l σ : Fin 4) :
    z.gi x l σ = Φgi eX l σ (fun b => uC SM eX z b x) := by
  rw [Φgi, eX_uC]; rfl

theorem dg_eq_Φ (x : ST 3) (α μ ν : Fin 4) :
    z.dg x α μ ν = Φdg eX α μ ν (fun b => uC SM eX z b x) := by
  rw [Φdg, eX_uC, ← jet_dg_eq SM z x]; rfl

/-- **The second metric derivatives are derivatives of the reconstructed first jets**:
`∂_δ∂_αg_{μν} = Σ_b ∂_b(dgOf)(𝒰) ∂_δu_b`. -/
theorem ddg_chain (x : ST 3) (δ α μ ν : Fin 4) :
    z.ddg x δ α μ ν = ∑ b, dΦdg eX b α μ ν (fun b => uC SM eX z b x) *
      pd (uC SM eX z b) δ x := by
  have h1 : z.ddg x δ α μ ν = pd (fun y => z.dg y α μ ν) δ x := by
    show pd (pd z.g α) δ x μ ν = pd (fun y => pd z.g α y μ ν) δ x
    have a1 := pd_apply ((contDiff_pd z.g_smooth α).differentiable (by simp) x) δ μ
    have a2 := pd_apply (F := fun y => pd z.g α y μ)
      ((contDiff_pi.1 (contDiff_pd z.g_smooth α) μ).differentiable (by simp) x) δ ν
    rw [a2, a1]
  have h2 : (fun y => z.dg y α μ ν) = fun y => Φdg eX α μ ν (fun b => uC SM eX z b y) :=
    funext fun y => dg_eq_Φ SM eX z y α μ ν
  rw [h1, h2]
  have hd : DifferentiableAt ℝ (Φdg eX α μ ν) (fun b => uC SM eX z b x) :=
    (contDiffAt_Φdg eX (uC_mem_chart SM eX z x) α μ ν).differentiableAt (by simp)
  rw [SobolevOpen.pd_comp hd (fun b => ((contDiff_uC SM eX z b).differentiable (by simp)) x) δ]
  rfl

/-- The coordinate Riemann tensor `R^l{}_{σγρ}` of the metric of a tuple. -/
def RiemF (x : ST 3) (c : RIdx) : ℝ :=
  rie (chr (z.gi x) (z.dg x)) (dchr (z.gi x) (z.dg x) (z.ddg x)) c.1 c.2.1 c.2.2.1 c.2.2.2

/-- **The Riemann tensor is affine in the first derivatives of the state**:
`R = Ψ₀(𝒰) + Σ_{δ,b} Ψ₁^{δb}(𝒰) ∂_δu_b`. -/
theorem riem_affine (x : ST 3) (c : RIdx) :
    RiemF z x c = Ψ0 eX c (fun b => uC SM eX z b x) +
      ∑ p : Fin 4 × Fin n, pd (uC SM eX z p.2) p.1 x * Ψ1 eX c p (fun b => uC SM eX z b x) := by
  have hgi : z.gi x = fun l σ => Φgi eX l σ (fun b => uC SM eX z b x) :=
    funext fun l => funext fun σ => gi_eq_Φ SM eX z x l σ
  have hdg : z.dg x = fun α μ ν => Φdg eX α μ ν (fun b => uC SM eX z b x) :=
    funext fun α => funext fun μ => funext fun ν => dg_eq_Φ SM eX z x α μ ν
  have hddg : z.ddg x = fun δ α μ ν => ∑ p ∈ (Finset.univ : Finset (Fin 4 × Fin n)),
      pd (uC SM eX z p.2) p.1 x *
        (if δ = p.1 then dΦdg eX p.2 α μ ν (fun b => uC SM eX z b x) else 0) := by
    funext δ α μ ν
    rw [ddg_chain SM eX z x δ α μ ν, Fintype.sum_prod_type,
      Finset.sum_eq_single δ (fun δ' _ hne => by simp [Ne.symm hne]) (by simp)]
    simp only [ite_true]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [RiemF, rie_split, hddg, rieLin_sum, hgi, hdg]
  rfl

end Coefficients

/-! ### The stress is affine in the Dirac residuals -/

section Stress

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')
variable {nb : ℕ} (eYD : (Fin nb → ℝ) ≃L[ℝ] S × S')

/-- The tangential-state stress `𝒯_0(𝒰)` in coordinates. -/
def T0c (μ ν : Fin 4) (v : Fin n → ℝ) : ℝ := stressF SM (recon SM (ofP (eX v))) μ ν

/-- The coefficients `𝒯_1^i(𝒰)` of the Dirac residual coordinates in the stress. -/
def T1c (μ ν : Fin 4) (i : Fin nb) (v : Fin n → ℝ) : ℝ :=
  stressR SM (recon SM (ofP (eX v))) (ofR (dirR (m := m) (V := V) (eYD (Pi.single i 1)))) μ ν

set_option maxHeartbeats 8000000 in
theorem contDiffOn_T0c (hS : SMSmooth SM) (μ ν : Fin 4) :
    ContDiffOn ℝ ∞ (T0c SM eX μ ν) (chartC eX) := by
  intro v hv
  have hx : MetChart (eX v).1 := hv
  have h : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => stressF SM (recon SM (ofP x)) μ ν)
      (eX v) := by
    simp (config := { maxSteps := 16000000 }) only [stressF, recon, ofP, cof, gradOfpq,
      gradOfPQ, lorentzSign, ymStressB, higgsStressB, DiracStressForm.coord,
      DiracStressForm.frame, XnatU, mass, Module.End.smul_def, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
    fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)
  exact (h.comp v eX.contDiff.contDiffAt).contDiffWithinAt

set_option maxHeartbeats 4000000 in
theorem contDiffOn_T1c (μ ν : Fin 4) (i : Fin nb) :
    ContDiffOn ℝ ∞ (T1c SM eX eYD μ ν i) (chartC eX) := by
  intro v hv
  have hx : MetChart (eX v).1 := hv
  have h : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => stressR SM (recon SM (ofP x))
      (ofR (dirR (m := m) (V := V) (eYD (Pi.single i 1)))) μ ν) (eX v) := by
    simp only [stressR, recon, ofP, ofR, dirR, DiracStressForm.stressRes, cof, lorentzSign]
    fun_prop (disch := first | exact hx.1 | exact hx.2)
  exact (h.comp v eX.contDiff.contDiffAt).contDiffWithinAt

/-- The residual stress as a linear map of the Dirac residuals. -/
def stressRL (fj : FirstJet (MatLie m) V S S') : (S × S') →ₗ[ℝ] (Fin 4 → Fin 4 → ℝ) where
  toFun y := stressR SM fj (ofR (dirR (m := m) (V := V) y))
  map_add' y y' := by
    rw [show dirR (m := m) (V := V) (y + y') = dirR y + dirR y' by ext <;> simp [dirR]]
    exact stressR_add SM fj _ _
  map_smul' c y := by
    rw [show dirR (m := m) (V := V) (c • y) = c • dirR y by ext <;> simp [dirR]]
    exact stressR_smul SM fj c _

variable (z : Tuple m V S S')

/-- The complete off-shell Standard-Model stress `T^{SM}_{μν}` of a tuple. -/
def TactF (x : ST 3) (μ ν : Fin 4) : ℝ := (z.jet x).Tact SM μ ν

/-- **`T^{SM} = 𝒯_0(𝒰) - Σ_i 𝒯_1^i(𝒰) R_{D,i}`** (`ActualJet.Tact_eq` in coordinates). -/
theorem stress_affine (x : ST 3) (μ ν : Fin 4) :
    TactF SM z x μ ν = T0c SM eX μ ν (fun b => uC SM eX z b x) -
      ∑ i, RDc SM eYD z i x * T1c SM eX eYD μ ν i (fun b => uC SM eX z b x) := by
  rw [TactF, ActualJet.Tact_eq]
  have hs : (z.jet x).state SM = ofP (eX fun b => uC SM eX z b x) := by
    rw [eX_uC]; rfl
  have hR : stressR SM (recon SM ((z.jet x).state SM)) ((z.jet x).res SM) =
      stressRL SM (recon SM ((z.jet x).state SM)) (dirF SM z x) := rfl
  have hD : dirF SM z x = ∑ i, RDc SM eYD z i x • eYD (Pi.single i 1) := by
    have h1 : dirF SM z x = eYD (eYD.symm (dirF SM z x)) :=
      (ContinuousLinearEquiv.apply_symm_apply eYD _).symm
    have h2 : eYD.symm (dirF SM z x) = ∑ i, RDc SM eYD z i x • (Pi.single i 1 : Fin nb → ℝ) := by
      funext j; simp [RDc, Finset.sum_apply, Pi.single_apply]
    rw [h1, h2, map_sum]
    simp only [map_smul]
  rw [hR, hD, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hs]
  rfl

end Stress

/-! ### The slice estimates for curvature and stress -/

section SliceEstimates

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')
variable {nb : ℕ} (eYD : (Fin nb → ℝ) ≃L[ℝ] S × S')

/-- Smooth extensions of the curvature and stress coefficients from a compact chart margin. -/
theorem exists_recovery_cutoffs (hS : SMSmooth SM) {K' : Set (Fin n → ℝ)} (hK' : IsCompact K')
    (hK'O : K' ⊆ chartC eX) :
    ∃ (P0 : RIdx → (Fin n → ℝ) → ℝ) (P1 : RIdx → Fin 4 × Fin n → (Fin n → ℝ) → ℝ)
      (Q0 : Fin 4 → Fin 4 → (Fin n → ℝ) → ℝ) (Q1 : Fin 4 → Fin 4 → Fin nb → (Fin n → ℝ) → ℝ),
      (∀ c, ContDiff ℝ ∞ (P0 c)) ∧ (∀ c p, ContDiff ℝ ∞ (P1 c p)) ∧
      (∀ μ ν, ContDiff ℝ ∞ (Q0 μ ν)) ∧ (∀ μ ν i, ContDiff ℝ ∞ (Q1 μ ν i)) ∧
      (∀ v ∈ K', ∀ c, P0 c v = Ψ0 eX c v) ∧ (∀ v ∈ K', ∀ c p, P1 c p v = Ψ1 eX c p v) ∧
      (∀ v ∈ K', ∀ μ ν, Q0 μ ν v = T0c SM eX μ ν v) ∧
      (∀ v ∈ K', ∀ μ ν i, Q1 μ ν i v = T1c SM eX eYD μ ν i v) := by
  have hO := isOpen_chartC eX
  choose P0 hP0 hP0K using fun c => SlabMoser.exists_contDiff_eqOn hO hK' hK'O
    (contDiffOn_Ψ0 eX c)
  choose P1 hP1 hP1K using fun c p => SlabMoser.exists_contDiff_eqOn hO hK' hK'O
    (contDiffOn_Ψ1 eX c p)
  choose Q0 hQ0 hQ0K using fun μ ν => SlabMoser.exists_contDiff_eqOn hO hK' hK'O
    (contDiffOn_T0c SM eX hS μ ν)
  choose Q1 hQ1 hQ1K using fun μ ν i => SlabMoser.exists_contDiff_eqOn hO hK' hK'O
    (contDiffOn_T1c SM eX eYD μ ν i)
  exact ⟨P0, P1, Q0, Q1, hP0, hP1, hQ0, hQ1, fun v hv c => hP0K c v hv,
    fun v hv c p => hP1K c p v hv, fun v hv μ ν => hQ0K μ ν v hv,
    fun v hv μ ν i => hQ1K μ ν i v hv⟩

end SliceEstimates

/-! ### Smoothness of the curvature and stress fields -/

section FieldSmooth

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')
variable {nb : ℕ} (eYD : (Fin nb → ℝ) ≃L[ℝ] S × S')
variable (z : Tuple m V S S')

theorem contDiffAt_onChart {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f (chartC eX))
    (x : ST 3) : ContDiffAt ℝ ∞ (fun x => f (fun b => uC SM eX z b x)) x :=
  ContDiffAt.comp (g := f) (f := fun x => fun b => uC SM eX z b x) x
    (hf.contDiffAt ((isOpen_chartC eX).mem_nhds (uC_mem_chart SM eX z x)))
    (contDiff_pi.2 fun b => contDiff_uC SM eX z b).contDiffAt

theorem contDiff_RiemF (c : RIdx) : ContDiff ℝ ∞ (fun x => RiemF z x c) := by
  have h1 := z.contDiff_gi
  have h2 := z.contDiff_dg
  have h3 := z.contDiff_ddg
  unfold RiemF rie dchr dchr1 dchr2 dginv chr
  fun_prop

include eX eYD in
theorem contDiff_TactF (hS : SMSmooth SM) (μ ν : Fin 4) : ContDiff ℝ ∞ (fun x => TactF SM z x μ ν) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have h := funext fun x => stress_affine SM eX eYD z x μ ν
  rw [h]
  exact (contDiffAt_onChart SM eX z (contDiffOn_T0c SM eX hS μ ν) x).sub
    (ContDiffAt.sum fun i _ => (contDiff_RDc SM eYD z i).contDiffAt.mul
      (contDiffAt_onChart SM eX z (contDiffOn_T1c SM eX eYD μ ν i) x))

theorem isSPeriodic_RiemF (c : RIdx) : IsSPeriodic (fun x => RiemF z x c) := fun k x => by
  have h1 : z.gi (x + sshift k) = z.gi x := gi_per z k x
  have h2 : z.dg (x + sshift k) = z.dg x := dg_per z k x
  have h3 : z.ddg (x + sshift k) = z.ddg x :=
    funext fun β => funext fun α => isSPeriodic_pd' (isSPeriodic_pd' z.g_per α) β k x
  simp only [RiemF, h1, h2, h3]

theorem isSPeriodic_TactF (μ ν : Fin 4) : IsSPeriodic (fun x => TactF SM z x μ ν) := fun k x => by
  simp only [TactF, jet_per z k x]

end FieldSmooth

/-! ### `prop:coupled-bootstrap`: state, curvature and stress (squared form) -/

section Main

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')
variable {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m V) (eYD : (Fin nb → ℝ) ≃L[ℝ] S × S')

/-- The squared `L²_tH^{k-1}_x` curvature difference `∫₀ᵀ Σ_c Q_{k-1}(R̂_c - R_{*,c})`. -/
def curvSq (k : ℕ) (T : ℝ) (zh zs : Tuple m V S S') : ℝ :=
  ∫ t in (0 : ℝ)..T, ∑ c : RIdx, Q (k - 1) (fun x => RiemF zh x c - RiemF zs x c) t

/-- The squared `L²_tH^k_x` stress difference `∫₀ᵀ Σ_{μν} Q_k(T̂_{μν} - T_{*,μν})`. -/
def stressSq (k : ℕ) (T : ℝ) (zh zs : Tuple m V S S') : ℝ :=
  ∫ t in (0 : ℝ)..T, ∑ p : Fin 4 × Fin 4,
    Q k (fun x => TactF SM zh x p.1 p.2 - TactF SM zs x p.1 p.2) t

set_option maxHeartbeats 2000000 in
/-- **`prop:coupled-bootstrap`** (squared form; `eq:bootstrap-state` and
`eq:bootstrap-curvature`).  Under the hypotheses of `bootstrap_core`, there are `δ_*, C_*` such
that `d² ≤ δ_*` implies
`sup_t ‖𝒰̂(t) - 𝒰_*(t)‖²_{H^k} ≤ C_*d²`, `‖Riem(ĝ) - Riem(g_*)‖²_{L²_tH^{k-1}_x} ≤ C_*d²` and
`‖T^{SM}(ẑ) - T^{SM}(z_*)‖²_{L²_tH^k_x} ≤ C_*d²`. -/
theorem coupled_bootstrap_sq (hS : SMSmooth SM)
    (hAsym : ∀ j a b v, Aco SM eX j a b v = Aco SM eX j b a v)
    {k : ℕ} (hk : 4 ≤ k) {T : ℝ} (hT : 0 < T) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKO : K ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ δs Cs : ℝ, 0 < δs ∧ 0 ≤ Cs ∧ ∀ zs zh : Tuple m V S S', ExactOn SM T zs →
      (∀ x : ST 3, x 0 ∈ Icc 0 T → (fun b => uC SM eX zs b x) ∈ K) →
      (∀ t ∈ Icc 0 T, energyQ (k + 1) (uC SM eX zs) t ≤ R₁ ^ 2) →
      misSq SM eX eY eYD k T zh zs ≤ δs →
      (∀ t ∈ Icc 0 T, energyQ k (subF (uC SM eX zh) (uC SM eX zs)) t ≤
        Cs * misSq SM eX eY eYD k T zh zs) ∧
      curvSq k T zh zs ≤ Cs * misSq SM eX eY eYD k T zh zs ∧
      stressSq SM k T zh zs ≤ Cs * misSq SM eX eY eYD k T zh zs := by
  obtain ⟨K', A', F', δs, Cs0, CM, R, hK'c, hK'O, hKK', hA', hF', hAK, hFK, hδs, hCs0, hCM0,
    hR, hR1R, hcore⟩ := bootstrap_core SM eX eY eYD hS hAsym hk hT hK hKO hR₁
  obtain ⟨P0, P1, Q0, Q1, hP0, hP1, hQ0, hQ1, hP0K, hP1K, hQ0K, hQ1K⟩ :=
    exists_recovery_cutoffs SM eX eYD hS hK'c hK'O
  set R' := Real.sqrt 2 * R with hR'def
  have hR' : 0 ≤ R' := by positivity
  have hR'2 : R' ^ 2 = 2 * R ^ 2 := by
    rw [hR'def, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hCR := fun c : RIdx => affine_slice_bound (d := 3) (m := 2) (k := k) (by norm_num)
    (by omega) hA' hF' (hP0 c) (hP1 c) hR'
  choose CR hCR0 hCR using hCR
  have hCT := fun p : Fin 4 × Fin 4 => affineRes_slice_bound (d := 3) (m := 2) (k := k)
    (ι := Fin nb) (by norm_num) (by omega) (hQ0 p.1 p.2) (hQ1 p.1 p.2) hR'
  choose CT hCT0 hCT using hCT
  set CRs := ∑ c, CR c
  set CTs := ∑ p, CT p
  have hCRs : 0 ≤ CRs := Finset.sum_nonneg fun c _ => hCR0 c
  have hCTs : 0 ≤ CTs := Finset.sum_nonneg fun p _ => hCT0 p
  refine ⟨δs, Cs0 + CRs * (T * Cs0 + CM) + CTs * (T * Cs0 + 1), hδs, by positivity, ?_⟩
  intro zs zh hex hKs hR1s hmis
  have hmis0 := misSq_nonneg SM eX eY eYD k hT.le zh zs
  set D2 := misSq SM eX eY eYD k T zh zs with hD2
  have hu := contDiff_uC SM eX zs
  have hv := contDiff_uC SM eX zh
  have hpu := isSPeriodic_uC SM eX zs
  have hpv := isSPeriodic_uC SM eX zh
  set e : Fin n → ST 3 → ℝ := fun c x => pd (uC SM eX zh c) 0 x -
    genG A' F' (uC SM eX zh) c x with hedef
  have he : ∀ c, ContDiff ℝ ∞ (e c) := fun c =>
    (contDiff_pd_top (hv c) 0).sub (contDiff_genG hA' hF' hv c)
  have hstate : ∀ t ∈ Icc 0 T, energyQ k (subF (uC SM eX zh) (uC SM eX zs)) t ≤ Cs0 * D2 :=
    fun t ht => (hcore zs zh hex hKs hR1s hmis t ht).1
  -- the forcing integral is part of `d²`
  have hFint : ∫ t in (0 : ℝ)..T, forcingSq SM eY eYD k zh t ≤ D2 := by
    rw [hD2, misSq]; linarith [energyQ_nonneg k (subF (uC SM eX zh) (uC SM eX zs)) 0]
  have hFc := continuous_forcingSq SM eY eYD zh hS k
  have hEc : Continuous (energyQ k (subF (uC SM eX zh) (uC SM eX zs))) :=
    continuous_energyQ k (contDiff_subF hu hv)
  -- slice facts
  have hball : ∀ t ∈ Icc 0 T, energyQ k (uC SM eX zs) t + energyQ k (uC SM eX zh) t ≤ R' ^ 2 ∧
      energyQ (k + 1) (uC SM eX zs) t ≤ R' ^ 2 := by
    intro t ht
    have h1 : energyQ k (uC SM eX zs) t ≤ R₁ ^ 2 :=
      (Finset.sum_le_sum fun b _ => Q_mono (Nat.le_succ k) _ _).trans (hR1s t ht)
    have h2 := (hcore zs zh hex hKs hR1s hmis t ht).2.2.1
    constructor <;> nlinarith [hR1s t ht, sq_nonneg R]
  have hU : ∀ t ∈ Icc 0 T, ∀ a, ∀ x : ST 3, x 0 = t →
      pd (uC SM eX zs a) 0 x = genG A' F' (uC SM eX zs) a x := fun t ht a x hx =>
    ref_pde SM eX zs hAK hFK hT hex (fun x hx => hKK' (hKs x hx)) a x (by rw [hx]; exact ht)
  have hV : ∀ a, ∀ x : ST 3, pd (uC SM eX zh a) 0 x = genG A' F' (uC SM eX zh) a x + e a x :=
    fun a x => by simp only [hedef]; ring
  -- curvature at one time
  have hcurv : ∀ t ∈ Icc 0 T, ∑ c : RIdx, Q (k - 1) (fun x => RiemF zh x c - RiemF zs x c) t ≤
      CRs * (Cs0 * D2 + CM * forcingSq SM eY eYD k zh t) := by
    intro t ht
    obtain ⟨hEt, hK't, -, hft⟩ := hcore zs zh hex hKs hR1s hmis t ht
    have hterm : ∀ c, Q (k - 1) (fun x => RiemF zh x c - RiemF zs x c) t ≤
        CR c * (Cs0 * D2 + CM * forcingSq SM eY eYD k zh t) := by
      intro c
      have hcong := SliceForcing.Q_congr_slice
        ((contDiff_RiemF zh c).sub (contDiff_RiemF zs c))
        (f := fun x => RiemF zh x c - RiemF zs x c)
        (g := fun x => (P0 c (fun b => uC SM eX zh b x) + ∑ p : Fin (3 + 1) × Fin n,
            P1 c p (fun b => uC SM eX zh b x) * pd (uC SM eX zh p.2) p.1 x) -
          (P0 c (fun b => uC SM eX zs b x) + ∑ p : Fin (3 + 1) × Fin n,
            P1 c p (fun b => uC SM eX zs b x) * pd (uC SM eX zs p.2) p.1 x))
        (((contDiff_compF (hP0 c) hv).add (ContDiff.sum fun p _ =>
            (contDiff_compF (hP1 c p) hv).mul (contDiff_pd_top (hv p.2) _))).sub
          ((contDiff_compF (hP0 c) hu).add (ContDiff.sum fun p _ =>
            (contDiff_compF (hP1 c p) hu).mul (contDiff_pd_top (hu p.2) _)))) t
        (fun y => by
          have hvK : (fun b => uC SM eX zh b (Fin.cons t y)) ∈ K' := hK't y
          have huK : (fun b => uC SM eX zs b (Fin.cons t y)) ∈ K' :=
            hKK' (hKs _ (by simpa using ht))
          rw [riem_affine SM eX zh, riem_affine SM eX zs, hP0K _ hvK, hP0K _ huK]
          simp only [hP1K _ hvK, hP1K _ huK, mul_comm]) (k - 1)
      rw [hcong]
      refine (hCR c (uC SM eX zs) (uC SM eX zh) e hu hv he hpu hpv t (hball t ht).1
        (hball t ht).2 (hU t ht) (fun a x _ => hV a x)).trans ?_
      have := hCR0 c
      gcongr
    calc ∑ c : RIdx, Q (k - 1) (fun x => RiemF zh x c - RiemF zs x c) t
        ≤ ∑ c : RIdx, CR c * (Cs0 * D2 + CM * forcingSq SM eY eYD k zh t) :=
          Finset.sum_le_sum fun c _ => hterm c
      _ = CRs * (Cs0 * D2 + CM * forcingSq SM eY eYD k zh t) := by rw [← Finset.sum_mul]
  -- stress at one time
  have hstress : ∀ t ∈ Icc 0 T, ∑ p : Fin 4 × Fin 4,
      Q k (fun x => TactF SM zh x p.1 p.2 - TactF SM zs x p.1 p.2) t ≤
      CTs * (Cs0 * D2 + forcingSq SM eY eYD k zh t) := by
    intro t ht
    obtain ⟨hEt, hK't, -, -⟩ := hcore zs zh hex hKs hR1s hmis t ht
    have hRD : ∑ i, Q k (RDc SM eYD zh i) t ≤ forcingSq SM eY eYD k zh t := by
      have h1 : ∑ i, Q k (RDc SM eYD zh i) t ≤ ∑ i, Q (k + 1) (RDc SM eYD zh i) t :=
        Finset.sum_le_sum fun i _ => Q_mono (Nat.le_succ k) _ _
      have h0 := fun (f : ST 3 → ℝ) (j : ℕ) => Q_nonneg j f t
      unfold forcingSq
      have a1 : 0 ≤ ∑ i, Q k (RBc SM eY zh i) t := Finset.sum_nonneg fun i _ => h0 _ _
      have a2 : 0 ≤ ∑ l, Q (k + 1) (Cc zh l) t := Finset.sum_nonneg fun i _ => h0 _ _
      have a3 : 0 ≤ ∑ l, Q k (dtCc zh l) t := Finset.sum_nonneg fun i _ => h0 _ _
      linarith
    have hterm : ∀ p : Fin 4 × Fin 4, Q k (fun x => TactF SM zh x p.1 p.2 -
        TactF SM zs x p.1 p.2) t ≤ CT p * (Cs0 * D2 + forcingSq SM eY eYD k zh t) := by
      intro p
      have hcong := SliceForcing.Q_congr_slice
        ((contDiff_TactF SM eX eYD zh hS p.1 p.2).sub (contDiff_TactF SM eX eYD zs hS p.1 p.2))
        (f := fun x => TactF SM zh x p.1 p.2 - TactF SM zs x p.1 p.2)
        (g := fun x => (Q0 p.1 p.2 (fun b => uC SM eX zh b x) -
          ∑ i, RDc SM eYD zh i x * Q1 p.1 p.2 i (fun b => uC SM eX zh b x)) -
          Q0 p.1 p.2 (fun b => uC SM eX zs b x))
        (((contDiff_compF (hQ0 p.1 p.2) hv).sub (ContDiff.sum fun i _ =>
          (contDiff_RDc SM eYD zh i).mul (contDiff_compF (hQ1 p.1 p.2 i) hv))).sub
          (contDiff_compF (hQ0 p.1 p.2) hu)) t
        (fun y => by
          have hvK : (fun b => uC SM eX zh b (Fin.cons t y)) ∈ K' := hK't y
          have hslab : (Fin.cons t y : ST 3) 0 ∈ Icc 0 T := by simpa using ht
          have huK : (fun b => uC SM eX zs b (Fin.cons t y)) ∈ K' := hKK' (hKs _ hslab)
          have hRD0 : ∀ i, RDc SM eYD zs i (Fin.cons t y) = 0 := fun i => by
            simp [RDc, (hex _ hslab).2.1]
          rw [stress_affine SM eX eYD zh, stress_affine SM eX eYD zs, hQ0K _ hvK, hQ0K _ huK]
          simp only [hQ1K _ hvK, hRD0, zero_mul, Finset.sum_const_zero, sub_zero]) k
      rw [hcong]
      refine (hCT p (uC SM eX zs) (uC SM eX zh) (RDc SM eYD zh) hu hv
        (contDiff_RDc SM eYD zh) hpu hpv (isSPeriodic_RDc SM eYD zh) t (hball t ht).1).trans ?_
      have := hCT0 p
      gcongr
    calc ∑ p : Fin 4 × Fin 4, Q k (fun x => TactF SM zh x p.1 p.2 - TactF SM zs x p.1 p.2) t
        ≤ ∑ p : Fin 4 × Fin 4, CT p * (Cs0 * D2 + forcingSq SM eY eYD k zh t) :=
          Finset.sum_le_sum fun p _ => hterm p
      _ = CTs * (Cs0 * D2 + forcingSq SM eY eYD k zh t) := by rw [← Finset.sum_mul]
  -- integrate
  have hcurvc : Continuous fun t => ∑ c : RIdx, Q (k - 1)
      (fun x => RiemF zh x c - RiemF zs x c) t :=
    continuous_finsetSum _ fun c _ => continuous_Q _ ((contDiff_RiemF zh c).sub
      (contDiff_RiemF zs c))
  have hstressc : Continuous fun t => ∑ p : Fin 4 × Fin 4,
      Q k (fun x => TactF SM zh x p.1 p.2 - TactF SM zs x p.1 p.2) t :=
    continuous_finsetSum _ fun p _ => continuous_Q _
      ((contDiff_TactF SM eX eYD zh hS p.1 p.2).sub (contDiff_TactF SM eX eYD zs hS p.1 p.2))
  have hIF0 : 0 ≤ ∫ t in (0 : ℝ)..T, forcingSq SM eY eYD k zh t :=
    intervalIntegral.integral_nonneg hT.le fun s _ => forcingSq_nonneg SM eY eYD zh k s
  have hcurvI : curvSq k T zh zs ≤ CRs * (T * Cs0 + CM) * D2 := by
    unfold curvSq
    calc ∫ t in (0 : ℝ)..T, ∑ c : RIdx, Q (k - 1) (fun x => RiemF zh x c - RiemF zs x c) t
        ≤ ∫ t in (0 : ℝ)..T, CRs * (Cs0 * D2 + CM * forcingSq SM eY eYD k zh t) :=
          intervalIntegral.integral_mono_on hT.le (hcurvc.intervalIntegrable 0 T)
            ((continuous_const.mul (continuous_const.add (continuous_const.mul hFc))).intervalIntegrable
              0 T) hcurv
      _ = CRs * (T * (Cs0 * D2) + CM * ∫ t in (0 : ℝ)..T, forcingSq SM eY eYD k zh t) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
            intervalIntegrable_const ((hFc.intervalIntegrable 0 T).const_mul CM),
            intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
          simp
      _ ≤ CRs * (T * Cs0 + CM) * D2 := by
          have := mul_le_mul_of_nonneg_left hFint hCM0
          nlinarith [mul_le_mul_of_nonneg_left this hCRs]
  have hstressI : stressSq SM k T zh zs ≤ CTs * (T * Cs0 + 1) * D2 := by
    unfold stressSq
    calc ∫ t in (0 : ℝ)..T, ∑ p : Fin 4 × Fin 4,
          Q k (fun x => TactF SM zh x p.1 p.2 - TactF SM zs x p.1 p.2) t
        ≤ ∫ t in (0 : ℝ)..T, CTs * (Cs0 * D2 + forcingSq SM eY eYD k zh t) :=
          intervalIntegral.integral_mono_on hT.le (hstressc.intervalIntegrable 0 T)
            ((continuous_const.mul (continuous_const.add hFc)).intervalIntegrable 0 T) hstress
      _ = CTs * (T * (Cs0 * D2) + ∫ t in (0 : ℝ)..T, forcingSq SM eY eYD k zh t) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
            intervalIntegrable_const (hFc.intervalIntegrable 0 T), intervalIntegral.integral_const]
          simp
      _ ≤ CTs * (T * Cs0 + 1) * D2 := by
          nlinarith [mul_le_mul_of_nonneg_left hFint hCTs]
  have hA1 : 0 ≤ CRs * (T * Cs0 + CM) * D2 := by positivity
  have hA2 : 0 ≤ CTs * (T * Cs0 + 1) * D2 := by positivity
  refine ⟨fun t ht => (hstate t ht).trans ?_, hcurvI.trans ?_, hstressI.trans ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

end Main
end RenewalGeometry.CoupledBootstrap
