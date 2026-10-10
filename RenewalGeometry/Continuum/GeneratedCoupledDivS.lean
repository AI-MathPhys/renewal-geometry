/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledSubsidiary

/-!
# The divergence of the auxiliary Dirac stress

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors: the source `∇^μΔS_{μb}` of the coupled subsidiary equation
(`GenCplSub.coupled_subsidiary`).  With `ΔS_{μν} = θ^A{}_μθ^B{}_νK_{AB}(Y, Ȳ)`:

* `gi_θ` — `g^{ea}θ^A{}_a = ε_Ae_A{}^e`;
* **`divS_main`** — `∇^aΔS_{ab} = Σ_{A,B}θ^B{}_bε_A e_A(K_{AB}) + (order zero in K)`;
* **`frame_div_K`** — `Σ_Aε_Ae_A(K_{AB})` is `-¼[⟨Ψ̄, Σ_Aε_Ac_Ae_A(Y_B)⟩ + ⟨Ψ̄, c_BΣ_Aε_Ae_A(Y_A)⟩
  - (dual)]` plus terms of order zero in the defects;
* **`dirac_frame_Y`**, **`div_frame_Y`** — `Σ_Aε_Ac_Ae_A(Y_B) = (𝒟'Y)_B - (connection)` and, for a
  Clifford-traceless one-form, `Σ_Aε_Ae_A(Y_A) = -½(κ(𝒟'Y) - (connection))`: only the twisted
  Dirac operator of the defect (and the defect itself) enters, no Clifford curl.
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplDiv

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState SymHypEnergy GenSFJ
  GenCplCov GenCplN GenCplRows GenCplX GenCplP GenCplEin GenDStress GenCplBox GenCplSD GenStress
  GenHarmonic ContractedBianchiJet ContractedBianchiJet.SubsidiarySource GenCplSub

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

variable (z : Tuple m V S S')

/-- **`g^{ea}θ^A{}_a = ε_Ae_A{}^e`.** -/
theorem gi_θ (x : ST 3) (e A : Fin 4) :
    ∑ a, z.gi x e a * θF z x A a = lorentzSign A * (frameU (z.gi x)).fr A e := by
  unfold θF cof
  have h : ∀ a, z.gi x e a * (lorentzSign A * ∑ ν, z.g x a ν * (frameU (z.gi x)).fr A ν) =
      lorentzSign A * ∑ ν, z.gi x e a * z.g x a ν * (frameU (z.gi x)).fr A ν := by
    intro a; rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  simp only [h]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  have hinv : ∀ ν, ∑ a, z.gi x e a * z.g x a ν = if e = ν then 1 else 0 := by
    intro ν
    have h1 := z.hinv x ν e
    have h2 : ∑ a, z.gi x e a * z.g x a ν = ∑ b, z.g x ν b * z.gi x b e :=
      Finset.sum_congr rfl fun a _ => by rw [z.gi_symm x e a, z.g_symm x a ν, mul_comm]
    rw [h2, h1]
    by_cases h : ν = e
    · simp [h]
    · simp [h, Ne.symm h]
  simp only [← Finset.sum_mul, hinv, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- A general coordinate tensor in frame form: `S_{ab} = Σ θ^A{}_aθ^B{}_bK_{AB}`. -/
def frameTensor (K : ST 3 → Fin 4 → Fin 4 → ℝ) (y : ST 3) (a b : Fin 4) : ℝ :=
  ∑ A, ∑ B, θF z y A a * θF z y B b * K y A B

/-- The order-zero remainder of the divergence of a frame tensor. -/
def remDiv (K : ST 3 → Fin 4 → Fin 4 → ℝ) (x : ST 3) (b : Fin 4) : ℝ :=
  ∑ e, ∑ a, z.gi x e a * (∑ A, ∑ B, (pd (fun y => θF z y A a) e x * θF z x B b +
      θF z x A a * pd (fun y => θF z y B b) e x) * K x A B -
    ∑ l, chr (z.gi x) (z.dg x) l e a * frameTensor z K x l b -
    ∑ l, frameTensor z K x a l * chr (z.gi x) (z.dg x) l e b)

/-- **The divergence of a frame tensor**: the principal part is the frame divergence of `K`. -/
theorem divS_main {K : ST 3 → Fin 4 → Fin 4 → ℝ} (hK : ∀ A B, ContDiff ℝ ∞ (fun y => K y A B))
    (x : ST 3) (b : Fin 4) :
    divS (jet3 z x) (Matrix.of (frameTensor z K x))
        (fun e => Matrix.of fun a' b' => pd (fun y => frameTensor z K y a' b') e x) b =
      ∑ A, ∑ B, (θF z x B b * lorentzSign A) * fd z (fun y => K y A B) A x + remDiv z K x b := by
  have hθ := contDiff_θF (z := z)
  have hpd : ∀ e a' b', pd (fun y => frameTensor z K y a' b') e x =
      ∑ A, ∑ B, ((pd (fun y => θF z y A a') e x * θF z x B b' +
        θF z x A a' * pd (fun y => θF z y B b') e x) * K x A B +
        θF z x A a' * θF z x B b' * pd (fun y => K y A B) e x) := by
    intro e a' b'
    unfold frameTensor
    refine pd_eq_of_line ((ContDiff.sum fun A _ => ContDiff.sum fun B _ =>
      ((hθ A a').mul (hθ B b')).mul (hK A B)).differentiable (by simp) x) ?_
    refine HasDerivAt.fun_sum fun A _ => HasDerivAt.fun_sum fun B _ => ?_
    have h1 := hasDerivAt_line0 ((hθ A a').differentiable (by simp) x) e
    have h2 := hasDerivAt_line0 ((hθ B b').differentiable (by simp) x) e
    have h3 := hasDerivAt_line0 ((hK A B).differentiable (by simp) x) e
    have h := (h1.mul h2).mul h3
    simp only [zero_smul, add_zero] at h
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, zero_smul, add_zero]
  unfold divS remDiv
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hpd]
  have hG : ∀ e a', (jet3 z x).G e a' = z.gi x e a' := fun e a' => rfl
  have hc : ∀ e l a', (jet3 z x).chr e l a' = chr (z.gi x) (z.dg x) l e a' := fun e l a' =>
    jet3_chr z x e l a'
  simp only [hG, hc]
  -- isolate the principal part
  have hmain : ∑ e, ∑ a, z.gi x e a * ∑ A, ∑ B, θF z x A a * θF z x B b *
      pd (fun y => K y A B) e x =
      ∑ A, ∑ B, (θF z x B b * lorentzSign A) * fd z (fun y => K y A B) A x := by
    have e1 : ∀ e, ∑ a, z.gi x e a * ∑ A, ∑ B, θF z x A a * θF z x B b *
        pd (fun y => K y A B) e x = ∑ A, ∑ B, (lorentzSign A * (frameU (z.gi x)).fr A e) *
          θF z x B b * pd (fun y => K y A B) e x := by
      intro e
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun A _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [← gi_θ z x e A, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    simp only [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [fd_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [GenCplN.frU_eq, smul_eq_mul]
    ring
  rw [← hmain]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  unfold frameTensor
  simp only [Finset.mul_sum, Finset.sum_mul]
  ring_nf

end RenewalGeometry.GenCplDiv
