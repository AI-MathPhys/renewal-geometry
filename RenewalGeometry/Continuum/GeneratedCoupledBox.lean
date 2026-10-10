/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledNormalEq

/-!
# The forcing of the normal prolongation defect: Clifford algebra of `κ𝒟'R`

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors.  The Dirac equation of the normal prolongation defect (`GenCplP.P_dirac`) is
forced by `κ𝒟'R`, `R = 𝓜(H)Y - ricTerm(∇_{(μ}C_{ν)})Ψ`.  This file isolates its structure:

* `γF` — the coordinate Clifford generators `γ^μ = Σ_Aε_Ae_A{}^μc_A`; **`gamma_anticomm`**
  `γ^μγ^α + γ^αγ^μ = -2g^{μα}`;
* **`clif3_sym12`**, **`clif3_sym13`** — `Σ X_{αμν}γ^μγ^αγ^ν = -Σ_ν(g^{αμ}X_{αμν})γ^ν` for `X`
  symmetric in `(α, μ)`, and the analogue for `(α, ν)`;
* `kD` — the operator `V ↦ κ(Σ_aε_ac_a(e_aV + ω'_aV))` on one-form fields, linear;
* **`kD_mass`** — `κ𝒟'(𝓜Y) = 𝓜κ(𝒟'Y) + (order zero in Y)` (the mass commutes with even Clifford
  products);
* **`kD_ric`** — `κ𝒟'(ricTerm(T)Ψ) = ½Σ ∂_αT_{μν}γ^μγ^αγ^νΨ + (order zero in T)`.
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplBox

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState SymHypEnergy GenSFJ
  GenCplCov GenCplN GenCplRows GenCplX GenCplP JetCurve

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

variable (z : Tuple m V S S') (D : DiracData (MatLie m) V S₀)

/-! ### Coordinate Clifford generators -/

/-- `γ^μ = Σ_A ε_Ae_A{}^μ c_A`. -/
def γF (x : ST 3) (μ : Fin 4) : Module.End ℝ S₀ :=
  ∑ A, (lorentzSign A * (frameU (z.gi x)).fr A μ) • D.Fr.c A

theorem eps_eq : D.Fr.ε = lorentzSign := by
  funext A
  induction A using Fin.cases with
  | zero => rw [D.lorentz.1]; rfl
  | succ a => rw [D.lorentz.2 a]; simp [lorentzSign, Fin.succ_ne_zero]

/-- Products of two finite linear combinations. -/
theorem sum_mul_sum_smul {A : Type*} [Ring A] [Algebra ℝ A] (u v : Fin 4 → ℝ) (c : Fin 4 → A) :
    (∑ i, u i • c i) * (∑ j, v j • c j) = ∑ i, ∑ j, (u i * v j) • (c i * c j) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm]

/-- **Clifford relation for real linear combinations of Clifford generators**:
`(Σu_ic_i)(Σv_jc_j) + (Σv_jc_j)(Σu_ic_i) = -2(Σ_iε_iu_iv_i)`. -/
theorem lin_anticomm {A : Type*} [Ring A] [Algebra ℝ A] (Fr : CliffordFrame (Fin 4) A)
    (u v : Fin 4 → ℝ) :
    (∑ i, u i • Fr.c i) * (∑ j, v j • Fr.c j) + (∑ j, v j • Fr.c j) * (∑ i, u i • Fr.c i) =
      (-2 * ∑ i, Fr.ε i * u i * v i) • 1 := by
  rw [sum_mul_sum_smul, sum_mul_sum_smul]
  rw [Finset.sum_comm (f := fun j i => (v j * u i) • (Fr.c j * Fr.c i))]
  rw [← Finset.sum_add_distrib]
  have e : ∀ i, ∑ j, (u i * v j) • (Fr.c i * Fr.c j) + ∑ j, (v j * u i) • (Fr.c j * Fr.c i) =
      (-2 * (Fr.ε i * u i * v i)) • 1 := by
    intro i
    rw [← Finset.sum_add_distrib]
    have e2 : ∀ j, (u i * v j) • (Fr.c i * Fr.c j) + (v j * u i) • (Fr.c j * Fr.c i) =
        (u i * v j * ((-2 : ℝ) * (if i = j then Fr.ε i else 0))) • 1 := by
      intro j
      rw [mul_comm (v j) (u i), ← smul_add, Fr.anticomm, smul_smul]
    rw [Finset.sum_congr rfl fun j _ => e2 j, Finset.sum_eq_single i
      (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero, mul_zero, zero_smul]) (by simp)]
    rw [if_pos rfl]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.sum_smul, Finset.mul_sum]

/-- **`γ^μγ^α + γ^αγ^μ = -2g^{μα}`.** -/
theorem gamma_anticomm (x : ST 3) (μ α : Fin 4) :
    γF z D x μ * γF z D x α + γF z D x α * γF z D x μ = (-2 * z.gi x μ α) • 1 := by
  unfold γF
  rw [lin_anticomm D.Fr, eps_eq D, z.compl x μ α]
  congr 2
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [GenGauss.e_eq_frameU, GenGauss.e_eq_frameU]
  have := ActualJetBridge.lorentzSign_sq A
  linear_combination ((frameU (z.gi x)).fr A μ * (frameU (z.gi x)).fr A α * lorentzSign A) * this

/-- **The Clifford pair contraction of a symmetric array**:
`Σ Y_{ab}γ^aγ^b = -(Σ g^{ab}Y_{ab})`. -/
theorem pair_sym (x : ST 3) (Y : Fin 4 → Fin 4 → ℝ) (hY : ∀ a b, Y a b = Y b a) :
    ∑ a, ∑ b, Y a b • (γF z D x a * γF z D x b) = -(∑ a, ∑ b, z.gi x a b * Y a b) • 1 := by
  set P := ∑ a, ∑ b, Y a b • (γF z D x a * γF z D x b) with hP
  have hswap : P = ∑ a, ∑ b, Y a b • (γF z D x b * γF z D x a) := by
    rw [hP, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hY]
  have h2 : P + P = ∑ a, ∑ b, (Y a b * (-2 * z.gi x a b)) • (1 : Module.End ℝ S₀) := by
    conv_lhs => arg 2; rw [hswap]
    rw [hP, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_add, gamma_anticomm, smul_smul]
  have hP2 : P = (1 / 2 : ℝ) • (P + P) := by rw [← two_smul ℝ P, smul_smul]; norm_num
  have h3 : ∑ a, ∑ b, (Y a b * (-2 * z.gi x a b)) • (1 : Module.End ℝ S₀) =
      (∑ a, ∑ b, Y a b * (-2 * z.gi x a b)) • 1 := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_smul]
  rw [hP2, h2, h3, smul_smul]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Clifford contraction of a tensor symmetric in its first two indices.** -/
theorem clif3_sym12 (x : ST 3) (X : Fin 4 → Fin 4 → Fin 4 → ℝ) (hX : ∀ α μ ν, X α μ ν = X μ α ν) :
    ∑ α, ∑ μ, ∑ ν, X α μ ν • (γF z D x μ * γF z D x α * γF z D x ν) =
      -∑ ν, (∑ α, ∑ μ, z.gi x α μ * X α μ ν) • γF z D x ν := by
  have e : ∀ ν, ∑ α, ∑ μ, X α μ ν • (γF z D x μ * γF z D x α) =
      -(∑ α, ∑ μ, z.gi x α μ * X α μ ν) • 1 := by
    intro ν
    have := pair_sym z D x (fun a b => X b a ν) (fun a b => by rw [hX])
    rw [Finset.sum_comm] at this
    rw [this]
    congr 2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [z.gi_symm x b a]
  calc ∑ α, ∑ μ, ∑ ν, X α μ ν • (γF z D x μ * γF z D x α * γF z D x ν) =
      ∑ ν, (∑ α, ∑ μ, X α μ ν • (γF z D x μ * γF z D x α)) * γF z D x ν := by
        simp only [Finset.sum_mul, smul_mul_assoc]
        calc ∑ α, ∑ μ, ∑ ν, X α μ ν • (γF z D x μ * γF z D x α * γF z D x ν) =
            ∑ α, ∑ ν, ∑ μ, X α μ ν • (γF z D x μ * γF z D x α * γF z D x ν) :=
              Finset.sum_congr rfl fun α _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
    _ = _ := by
        simp only [e, neg_smul, neg_mul, smul_mul_assoc, one_mul, Finset.sum_neg_distrib]

/-- **Clifford contraction of a tensor symmetric in its first and third indices.** -/
theorem clif3_sym13 (x : ST 3) (X : Fin 4 → Fin 4 → Fin 4 → ℝ) (hX : ∀ α μ ν, X α μ ν = X ν μ α) :
    ∑ α, ∑ μ, ∑ ν, X α μ ν • (γF z D x μ * γF z D x α * γF z D x ν) =
      -∑ μ, (∑ α, ∑ ν, z.gi x α ν * X α μ ν) • γF z D x μ := by
  have e : ∀ μ, ∑ α, ∑ ν, X α μ ν • (γF z D x α * γF z D x ν) =
      -(∑ α, ∑ ν, z.gi x α ν * X α μ ν) • 1 := fun μ =>
    pair_sym z D x (fun a b => X a μ b) (fun a b => by rw [hX])
  calc ∑ α, ∑ μ, ∑ ν, X α μ ν • (γF z D x μ * γF z D x α * γF z D x ν) =
      ∑ μ, γF z D x μ * (∑ α, ∑ ν, X α μ ν • (γF z D x α * γF z D x ν)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [mul_smul_comm, mul_assoc]
    _ = _ := by
        simp only [e, neg_smul, mul_neg, mul_smul_comm, mul_one, Finset.sum_neg_distrib]

/-! ### The operator `κ𝒟'` on one-form fields -/

/-- `κ𝒟'V = κ(Σ_aε_ac_a(e_aV + ω'_aV))`. -/
def kD (Vf : ST 3 → Fin 4 → S₀) (x : ST 3) : S₀ :=
  kap D.Fr (∑ a, (liftFr D.Fr).ε a • ((liftFr D.Fr).c a •
    (fd z Vf a x + omegaP (ωF z D x) (ΓF z x) a (Vf x))))

theorem kD_apply (Vf : ST 3 → Fin 4 → S₀) (x : ST 3) :
    kD z D Vf x = ∑ A, ∑ a, (D.Fr.ε A * D.Fr.ε a) • D.Fr.c A (D.Fr.c a (fd z Vf a x A +
      (ωF z D x a (Vf x A) - ∑ C, ΓF z x a A C • Vf x C))) := by
  unfold kD
  rw [kap_apply]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, Module.End.smul_def, liftFr, liftE_apply,
    Pi.add_apply, omegaP_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]

theorem kD_sub {Vf Vf' : ST 3 → Fin 4 → S₀} {x : ST 3} (hV : DifferentiableAt ℝ Vf x)
    (hV' : DifferentiableAt ℝ Vf' x) :
    kD z D (fun y => Vf y - Vf' y) x = kD z D Vf x - kD z D Vf' x := by
  have hfd : ∀ a, fd z (fun y => Vf y - Vf' y) a x = fd z Vf a x - fd z Vf' a x := by
    intro a
    rw [fd_eq_sum, fd_eq_sum, fd_eq_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← smul_sub, GenDefJet.pd_sub_eq hV hV']
  unfold kD
  simp only [hfd, map_sub, ← map_sub, ← Finset.sum_sub_distrib, ← smul_sub]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  rw [map_sub]
  abel

/-- The product rule for the mass term along the tuple. -/
theorem fd_mass {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) (x : ST 3) (a A : Fin 4) :
    fd z (fun y => mass D.m0 D.L (z.H y) (Y y A)) a x =
      D.L (fd z z.H a x) (Y x A) + mass D.m0 D.L (z.H x) (fd z Y a x A) := by
  have hYA := contDiff_comp_apply hY A
  have hpd : ∀ γ, pd (fun y => mass D.m0 D.L (z.H y) (Y y A)) γ x =
      D.L (pd z.H γ x) (Y x A) + mass D.m0 D.L (z.H x) (pd (fun y => Y y A) γ x) := by
    intro γ
    have hd : DifferentiableAt ℝ (fun y => mass D.m0 D.L (z.H y) (Y y A)) x := by
      simp only [mass, LinearMap.add_apply]
      refine ((LinearMap.toContinuousLinearMap D.m0).differentiableAt.comp x
        (hYA.differentiable (by simp) x)).add ?_
      exact (ContDiffAt.bilinApply D.L z.H_smooth.contDiffAt hYA.contDiffAt).differentiableAt
        (by simp)
    refine pd_eq_of_line hd ?_
    have h1 := hasDerivAt_lin D.m0 (hasDerivAt_line0 (hYA.differentiable (by simp) x) γ)
    have h2 := hasDerivAt_bilin D.L (hasDerivAt_line0 (z.H_smooth.differentiable (by simp) x) γ)
      (hasDerivAt_line0 (hYA.differentiable (by simp) x) γ)
    have h := h1.add h2
    simp only [zero_smul, add_zero] at h
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · simp only [mass, LinearMap.add_apply, Pi.add_apply]
    · simp only [mass, LinearMap.add_apply, map_add]
      abel
  rw [fd_eq_sum, fd_eq_sum, fd_apply z (hY.differentiable (by simp) x), fd_eq_sum]
  simp only [hpd, smul_add, Finset.sum_add_distrib, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, pd_apply_smooth hY, Finset.sum_apply, Pi.smul_apply]

theorem mass_cc (w : V) (A a : Fin 4) (v : S₀) :
    mass D.m0 D.L w (D.Fr.c A (D.Fr.c a v)) = D.Fr.c A (D.Fr.c a (mass D.m0 D.L w v)) := by
  have h := congrArg (fun T : Module.End ℝ S₀ => T v) (D.mass_cl w A a)
  simpa [Module.End.mul_apply] using h

theorem contDiff_massY {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (fun y => fun A => mass D.m0 D.L (z.H y) (Y y A)) := by
  refine contDiff_pi.2 fun A => ?_
  have hYA := contDiff_comp_apply hY A
  simp only [mass, LinearMap.add_apply]
  refine ((LinearMap.toContinuousLinearMap D.m0).contDiff.comp hYA).add ?_
  exact contDiff_iff_contDiffAt.2 fun y =>
    ContDiffAt.bilinApply D.L z.H_smooth.contDiffAt hYA.contDiffAt

/-- **`κ𝒟'(𝓜Y) = 𝓜κ(𝒟'Y) + (order zero in Y)`.** -/
theorem kD_mass {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) (x : ST 3) :
    kD z D (fun y => fun A => mass D.m0 D.L (z.H y) (Y y A)) x =
      mass D.m0 D.L (z.H x) (kap D.Fr (QF z D Y x)) +
        ∑ A, ∑ a, (D.Fr.ε A * D.Fr.ε a) • D.Fr.c A (D.Fr.c a (D.L (fd z z.H a x) (Y x A) +
          (ωF z D x a (mass D.m0 D.L (z.H x) (Y x A)) -
            mass D.m0 D.L (z.H x) (ωF z D x a (Y x A))))) := by
  rw [kD_apply]
  have hfdA : ∀ a A, fd z (fun y => fun A => mass D.m0 D.L (z.H y) (Y y A)) a x A =
      D.L (fd z z.H a x) (Y x A) + mass D.m0 D.L (z.H x) (fd z Y a x A) := by
    intro a A
    rw [fd_apply z ((contDiff_massY z D hY).differentiable (by simp) x), fd_mass z D hY]
  simp only [hfdA]
  have hM : mass D.m0 D.L (z.H x) (kap D.Fr (QF z D Y x)) = ∑ A, ∑ a, (D.Fr.ε A * D.Fr.ε a) •
      D.Fr.c A (D.Fr.c a (mass D.m0 D.L (z.H x) (covF z D Y x a A))) := by
    rw [kap_apply, map_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [QF_apply, map_smul, map_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, map_smul, mass_cc, smul_smul]
  rw [hM, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← smul_add, ← map_add, ← map_add, covF_apply]
  congr 3
  simp only [map_add, map_sub, map_sum, map_smul]
  abel

/-! ### The Ricci-elimination term -/

variable {T : ST 3 → Fin 4 → Fin 4 → ℝ} {ψ : ST 3 → S₀}

/-- `Ξ_μ = ½Σ_νT_{μν}γ^νΨ`. -/
def Ξ (T : ST 3 → Fin 4 → Fin 4 → ℝ) (ψ : ST 3 → S₀) (μ : Fin 4) (y : ST 3) : S₀ :=
  (1 / 2 : ℝ) • ∑ ν, T y μ ν • γF z D y ν (ψ y)

theorem γF_apply (y : ST 3) (ν : Fin 4) (v : S₀) :
    γF z D y ν v = ∑ A, (lorentzSign A * (frameU (z.gi y)).fr A ν) • D.Fr.c A v := by
  unfold γF
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]

/-- **The Ricci-elimination term in coordinate Clifford form**:
`ricTerm(T)_A = Σ_μ e_A{}^μΞ_μ`. -/
theorem ric_gamma (y : ST 3) (A : Fin 4) :
    ricTerm D (z.g y) (z.gi y) (frameU (z.gi y)) (T y) (ψ y) A =
      ∑ μ, (frameU (z.gi y)).fr A μ • Ξ z D T ψ μ y := by
  unfold ricTerm Ξ frT2
  simp only [γF_apply, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum, smul_smul,
    Finset.sum_smul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun B _ => ?_
  rw [smul_assoc, Module.End.smul_def]
  congr 1
  ring

theorem contDiff_γψ (hψ : ContDiff ℝ ∞ ψ) (ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => γF z D y ν (ψ y)) := by
  simp only [γF_apply]
  refine ContDiff.sum fun A _ => ContDiff.smul ?_ ?_
  · exact contDiff_const.mul (contDiff_fr (z := z) A ν)
  · exact (LinearMap.toContinuousLinearMap (D.Fr.c A)).contDiff.comp hψ

theorem contDiff_Ξ (hψ : ContDiff ℝ ∞ ψ) (hT : ∀ μ ν, ContDiff ℝ ∞ (fun y => T y μ ν))
    (μ : Fin 4) : ContDiff ℝ ∞ (Ξ z D T ψ μ) := by
  unfold Ξ
  exact ContDiff.const_smul _ (ContDiff.sum fun ν _ => (hT μ ν).smul (contDiff_γψ z D hψ ν))

theorem pd_Ξ (hψ : ContDiff ℝ ∞ ψ) (hT : ∀ μ ν, ContDiff ℝ ∞ (fun y => T y μ ν)) (μ α : Fin 4)
    (x : ST 3) : pd (Ξ z D T ψ μ) α x = (1 / 2 : ℝ) • ∑ ν, (pd (fun y => T y μ ν) α x •
      γF z D x ν (ψ x) + T x μ ν • pd (fun y => γF z D y ν (ψ y)) α x) := by
  refine pd_eq_of_line ((contDiff_Ξ z D hψ hT μ).differentiable (by simp) x) ?_
  unfold Ξ
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun ν _ =>
    (hasDerivAt_line0 ((hT μ ν).differentiable (by simp) x) α).smul
      (hasDerivAt_line0 ((contDiff_γψ z D hψ ν).differentiable (by simp) x) α)
  have h2 := h.const_smul (1 / 2 : ℝ)
  simp only [zero_smul, add_zero] at h2
  refine h2.congr_deriv ?_
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [add_comm]

theorem sum4_perm {M : Type*} [AddCommMonoid M] (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → M) :
    ∑ A, ∑ a, ∑ μ, ∑ α, f A a μ α = ∑ μ, ∑ α, ∑ A, ∑ a, f A a μ α := by
  calc ∑ A, ∑ a, ∑ μ, ∑ α, f A a μ α = ∑ A, ∑ μ, ∑ a, ∑ α, f A a μ α :=
        Finset.sum_congr rfl fun A _ => Finset.sum_comm
    _ = ∑ μ, ∑ A, ∑ a, ∑ α, f A a μ α := Finset.sum_comm
    _ = ∑ μ, ∑ A, ∑ α, ∑ a, f A a μ α :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun A _ => Finset.sum_comm
    _ = ∑ μ, ∑ α, ∑ A, ∑ a, f A a μ α :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_comm

/-- **Two frame contractions with Clifford generators give `γγ`.** -/
theorem gamma2 (x : ST 3) (w : Fin 4 → Fin 4 → S₀) :
    ∑ A, ∑ a, (D.Fr.ε A * D.Fr.ε a) • D.Fr.c A (D.Fr.c a (∑ μ, ∑ α,
      ((frameU (z.gi x)).fr A μ * (frameU (z.gi x)).fr a α) • w μ α)) =
      ∑ μ, ∑ α, γF z D x μ (γF z D x α (w μ α)) := by
  simp only [γF_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [eps_eq D, sum4_perm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun a _ => ?_
  congr 1
  ring

/-- The one-form field of the Ricci-elimination term. -/
def Vric (T : ST 3 → Fin 4 → Fin 4 → ℝ) (ψ : ST 3 → S₀) (y : ST 3) : Fin 4 → S₀ :=
  fun A => ricTerm D (z.g y) (z.gi y) (frameU (z.gi y)) (T y) (ψ y) A

theorem contDiff_Vric (hψ : ContDiff ℝ ∞ ψ) (hT : ∀ μ ν, ContDiff ℝ ∞ (fun y => T y μ ν)) :
    ContDiff ℝ ∞ (Vric z D T ψ) :=
  contDiff_pi.2 fun A => contDiff_ricTerm (z := z) D hψ T hT A

/-- The remainder of `κ𝒟'` of the Ricci-elimination term (order zero in `T`). -/
def remR (T : ST 3 → Fin 4 → Fin 4 → ℝ) (ψ : ST 3 → S₀) (x : ST 3) : S₀ :=
  (1 / 2 : ℝ) • ∑ μ, ∑ α, ∑ ν, T x μ ν • γF z D x μ (γF z D x α
      (pd (fun y => γF z D y ν (ψ y)) α x)) +
    ∑ A, ∑ a, (D.Fr.ε A * D.Fr.ε a) • D.Fr.c A (D.Fr.c a (∑ μ, fd z (fun y =>
      (frameU (z.gi y)).fr A μ) a x • Ξ z D T ψ μ x + (ωF z D x a (Vric z D T ψ x A) -
        ∑ C, ΓF z x a A C • Vric z D T ψ x C)))

/-- **`κ𝒟'(ricTerm(T)Ψ) = ½Σ∂_αT_{μν}γ^μγ^αγ^νΨ + remR`.** -/
theorem kD_ric (hψ : ContDiff ℝ ∞ ψ) (hT : ∀ μ ν, ContDiff ℝ ∞ (fun y => T y μ ν)) (x : ST 3) :
    kD z D (Vric z D T ψ) x = (1 / 2 : ℝ) • ∑ μ, ∑ α, ∑ ν, pd (fun y => T y μ ν) α x •
      γF z D x μ (γF z D x α (γF z D x ν (ψ x))) + remR z D T ψ x := by
  have hfr := contDiff_fr (z := z)
  have hΞ := contDiff_Ξ z D hψ hT
  -- the frame derivative of the field
  have hfd : ∀ a A, fd z (Vric z D T ψ) a x A = ∑ μ, fd z (fun y => (frameU (z.gi y)).fr A μ) a x •
      Ξ z D T ψ μ x + ∑ μ, ∑ α, ((frameU (z.gi x)).fr A μ * (frameU (z.gi x)).fr a α) •
        pd (Ξ z D T ψ μ) α x := by
    intro a A
    rw [fd_apply z ((contDiff_Vric z D hψ hT).differentiable (by simp) x)]
    have hV : (fun y => Vric z D T ψ y A) = fun y => ∑ μ, (frameU (z.gi y)).fr A μ • Ξ z D T ψ μ y :=
      funext fun y => ric_gamma z D y A
    rw [hV, fd_sum z Finset.univ (f := fun μ y => (frameU (z.gi y)).fr A μ • Ξ z D T ψ μ y)
      (fun μ _ => ((hfr A μ).smul (hΞ μ)).differentiable (by simp) x)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hprod : ∀ γ, pd (fun y => (frameU (z.gi y)).fr A μ • Ξ z D T ψ μ y) γ x =
        pd (fun y => (frameU (z.gi y)).fr A μ) γ x • Ξ z D T ψ μ x +
          (frameU (z.gi x)).fr A μ • pd (Ξ z D T ψ μ) γ x := by
      intro γ
      unfold SobolevOpen.pd
      rw [fderiv_fun_smul ((hfr A μ).differentiable (by simp) x) ((hΞ μ).differentiable (by simp) x)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [add_comm]
    rw [fd_eq_sum, fd_eq_sum]
    simp only [hprod, smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul]
    congr 1
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [GenCplN.frU_eq z x a γ]
    congr 1
    ring
  rw [kD_apply]
  simp only [hfd]
  have hsplit : ∀ A a, (D.Fr.ε A * D.Fr.ε a) • D.Fr.c A (D.Fr.c a (∑ μ, fd z (fun y =>
      (frameU (z.gi y)).fr A μ) a x • Ξ z D T ψ μ x + ∑ μ, ∑ α, ((frameU (z.gi x)).fr A μ *
        (frameU (z.gi x)).fr a α) • pd (Ξ z D T ψ μ) α x + (ωF z D x a (Vric z D T ψ x A) -
        ∑ C, ΓF z x a A C • Vric z D T ψ x C))) =
      (D.Fr.ε A * D.Fr.ε a) • D.Fr.c A (D.Fr.c a (∑ μ, ∑ α, ((frameU (z.gi x)).fr A μ *
        (frameU (z.gi x)).fr a α) • pd (Ξ z D T ψ μ) α x)) +
      (D.Fr.ε A * D.Fr.ε a) • D.Fr.c A (D.Fr.c a (∑ μ, fd z (fun y =>
        (frameU (z.gi y)).fr A μ) a x • Ξ z D T ψ μ x + (ωF z D x a (Vric z D T ψ x A) -
          ∑ C, ΓF z x a A C • Vric z D T ψ x C))) := by
    intro A a
    rw [← smul_add, ← map_add, ← map_add]
    congr 3
    abel
  simp only [hsplit, Finset.sum_add_distrib]
  rw [gamma2]
  have hmain : ∑ μ, ∑ α, γF z D x μ (γF z D x α (pd (Ξ z D T ψ μ) α x)) =
      (1 / 2 : ℝ) • ∑ μ, ∑ α, ∑ ν, pd (fun y => T y μ ν) α x •
        γF z D x μ (γF z D x α (γF z D x ν (ψ x))) +
      (1 / 2 : ℝ) • ∑ μ, ∑ α, ∑ ν, T x μ ν • γF z D x μ (γF z D x α
        (pd (fun y => γF z D y ν (ψ y)) α x)) := by
    simp only [pd_Ξ z D hψ hT, map_smul, map_sum, map_add, Finset.smul_sum, ← smul_add,
      ← Finset.sum_add_distrib]
  rw [hmain]
  unfold remR
  abel

/-! ### The harmonic-defect tensor through the lowered defect `c = gC` -/

/-- **`∇_μC_ν = ∂_μc_ν - Γ^l_{μν}c_l`** for the lowered harmonic defect `c = GenHarmonic.cF`. -/
theorem nablaDefect_eq (y : ST 3) (μ ν : Fin 4) :
    nablaDefect (z.g y) (z.gi y) (z.dg y) (z.ddg y) μ ν =
      pd (GenHarmonic.cF z) μ y ν - ∑ l, chr (z.gi y) (z.dg y) l μ ν * GenHarmonic.cF z y l := by
  have hcF : GenHarmonic.cF z = fun y b => ∑ k, z.g y b k * CF z y k := rfl
  have hpd : pd (GenHarmonic.cF z) μ y ν =
      ∑ k, (z.dg y μ ν k * CF z y k + z.g y ν k * pd (CF z) μ y k) := by
    rw [← pd_apply ((GenHarmonic.contDiff_cF z).differentiable (by simp) y) μ ν]
    rw [hcF]
    refine pd_eq_of_line ((contDiff_pi.1 (GenHarmonic.contDiff_cF z) ν).differentiable (by simp) y)
      ?_
    refine HasDerivAt.fun_sum fun k _ => ?_
    have h1 := z.line_g y μ ν k
    have h2 := hasDerivAt_line0_apply ((contDiff_CF z).differentiable (by simp) y) μ k
    have h := h1.mul h2
    simp only [zero_smul, add_zero] at h
    refine h.congr_deriv ?_
    ring
  rw [hpd, pd_CF]
  unfold nablaDefect nablaC CF ActualJetWriter.C ActualJetWriter.dC cDown
  rfl

/-- `∇_{(μ}C_{ν)} = ½(∂_μc_ν + ∂_νc_μ) - Γ^l_{μν}c_l`. -/
theorem sD_eq (y : ST 3) (μ ν : Fin 4) :
    sD z y μ ν = (1 / 2 : ℝ) * (pd (GenHarmonic.cF z) μ y ν + pd (GenHarmonic.cF z) ν y μ) -
      ∑ l, chr (z.gi y) (z.dg y) l μ ν * GenHarmonic.cF z y l := by
  unfold sD symDefect
  rw [nablaDefect_eq, nablaDefect_eq]
  have hc : ∀ l, chr (z.gi y) (z.dg y) l ν μ = chr (z.gi y) (z.dg y) l μ ν := fun l =>
    chr_symm' (z.gi y) (z.dg y) (z.dg_symm y) l ν μ
  simp only [hc]
  ring

/-- The first-derivative part of `∇_{(μ}C_{ν)}`. -/
def sD2 (y : ST 3) (μ ν : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (pd (GenHarmonic.cF z) μ y ν + pd (GenHarmonic.cF z) ν y μ)

/-- The Christoffel part of `∇_{(μ}C_{ν)}`. -/
def sD1 (y : ST 3) (μ ν : Fin 4) : ℝ := -∑ l, chr (z.gi y) (z.dg y) l μ ν * GenHarmonic.cF z y l

theorem sD_split (y : ST 3) (μ ν : Fin 4) : sD z y μ ν = sD2 z y μ ν + sD1 z y μ ν := by
  rw [sD_eq]; unfold sD2 sD1; ring

/-- The wave operator on the lowered harmonic defect, `□c_ν = g^{αβ}∂_α∂_βc_ν`. -/
def boxc (x : ST 3) (ν : Fin 4) : ℝ :=
  ∑ α, ∑ β, z.gi x α β * pd (pd (GenHarmonic.cF z) β) α x ν

theorem pd_sD2 (x : ST 3) (α μ ν : Fin 4) : pd (fun y => sD2 z y μ ν) α x =
    (1 / 2 : ℝ) * (pd (pd (GenHarmonic.cF z) μ) α x ν + pd (pd (GenHarmonic.cF z) ν) α x μ) := by
  have hc := GenHarmonic.contDiff_cF z
  have h1 : ∀ μ' ν', (fun y => pd (GenHarmonic.cF z) μ' y ν') =
      pd (fun y => GenHarmonic.cF z y ν') μ' := fun μ' ν' =>
    funext fun y => (pd_apply (hc.differentiable (by simp) y) μ' ν').symm
  have hd : ∀ μ' ν', ContDiff ℝ ∞ (fun y => pd (GenHarmonic.cF z) μ' y ν') := fun μ' ν' =>
    contDiff_pi.1 (contDiff_pd hc μ') ν'
  refine pd_eq_of_line ((contDiff_const.mul ((hd μ ν).add (hd ν μ))).differentiable (by simp) x) ?_
  have hl := fun μ' ν' => hasDerivAt_line0_apply ((contDiff_pd hc μ').differentiable (by simp) x) α ν'
  have h := ((hl μ ν).add (hl ν μ)).const_mul (1 / 2 : ℝ)
  exact h

/-- **The principal part of `κ𝒟'(ricTerm(∇_{(μ}C_{ν)}))`**:
`½Σ∂_α(∇_{(μ}C_{ν)})γ^μγ^αγ^ν = -½Σ_ν(□c_ν)γ^ν + (order ≤ 1 in c)`; here for the first-derivative
part: `Σ∂_α(sD2)_{μν}γ^μγ^αγ^ν = -Σ_ν(□c_ν)γ^ν`. -/
theorem principal_sD2 (x : ST 3) (v : S₀) :
    ∑ μ, ∑ α, ∑ ν, pd (fun y => sD2 z y μ ν) α x • γF z D x μ (γF z D x α (γF z D x ν v)) =
      -∑ ν, boxc z x ν • γF z D x ν v := by
  have hc := GenHarmonic.contDiff_cF z
  have hsym : ∀ μ α, pd (pd (GenHarmonic.cF z) μ) α x = pd (pd (GenHarmonic.cF z) α) μ x :=
    fun μ α => pd_pd_comm' hc μ α x
  set X1 : Fin 4 → Fin 4 → Fin 4 → ℝ := fun α μ ν => pd (pd (GenHarmonic.cF z) μ) α x ν
  set X2 : Fin 4 → Fin 4 → Fin 4 → ℝ := fun α μ ν => pd (pd (GenHarmonic.cF z) ν) α x μ
  have h1 := clif3_sym12 z D x X1 (fun α μ ν => by simp only [X1]; rw [hsym])
  have h2 := clif3_sym13 z D x X2 (fun α μ ν => by simp only [X2]; rw [hsym])
  have e : ∀ μ α ν, pd (fun y => sD2 z y μ ν) α x • γF z D x μ (γF z D x α (γF z D x ν v)) =
      (1 / 2 : ℝ) • ((X1 α μ ν + X2 α μ ν) • (γF z D x μ * γF z D x α * γF z D x ν) v) := by
    intro μ α ν
    rw [pd_sD2, smul_smul]
    rfl
  simp only [e]
  have k : ∀ X : Fin 4 → Fin 4 → Fin 4 → ℝ,
      ∑ μ, ∑ α, ∑ ν, X α μ ν • (γF z D x μ * γF z D x α * γF z D x ν) v =
      (∑ α, ∑ μ, ∑ ν, X α μ ν • (γF z D x μ * γF z D x α * γF z D x ν)) v := by
    intro X
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Finset.sum_comm]
  have hsplit : ∑ μ, ∑ α, ∑ ν, (1 / 2 : ℝ) • ((X1 α μ ν + X2 α μ ν) •
      (γF z D x μ * γF z D x α * γF z D x ν) v) = (1 / 2 : ℝ) •
      (∑ μ, ∑ α, ∑ ν, X1 α μ ν • (γF z D x μ * γF z D x α * γF z D x ν) v +
        ∑ μ, ∑ α, ∑ ν, X2 α μ ν • (γF z D x μ * γF z D x α * γF z D x ν) v) := by
    simp only [add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  rw [hsplit, k X1, k X2, h1, h2]
  have b1 : ∀ ν, ∑ α, ∑ μ, z.gi x α μ * X1 α μ ν = boxc z x ν := fun ν => rfl
  have b2 : ∀ μ, ∑ α, ∑ ν, z.gi x α ν * X2 α μ ν = boxc z x μ := fun μ => rfl
  simp only [b1, b2, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [← two_smul ℝ, smul_smul]
  norm_num

end RenewalGeometry.GenCplBox
