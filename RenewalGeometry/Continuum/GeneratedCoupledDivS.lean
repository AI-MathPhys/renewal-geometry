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
  GenHarmonic ContractedBianchiJet ContractedBianchiJet.SubsidiarySource GenCplSub JetCurve

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

/-! ### Frame derivatives of the kinetic stress and of the defects -/

/-- **`Σ_Aε_Ac_Ae_A(Y_B) = (𝒟'Y)_B - (connection)`.** -/
theorem dirac_frame_Y (D : DiracData (MatLie m) V S₀) (X : ST 3 → Fin 4 → S₀) (x : ST 3)
    (B : Fin 4) :
    ∑ A, D.Fr.ε A • D.Fr.c A (fd z X A x B) = QF z D X x B -
      ∑ A, D.Fr.ε A • D.Fr.c A (ωF z D x A (X x B) - ∑ C, ΓF z x A B C • X x C) := by
  rw [QF_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [covF_apply, ← smul_sub, ← map_sub]
  congr 2
  abel

/-- **The divergence of a Clifford-traceless one-form**: if `κ(e_CY) = 0` for all `C`, then
`Σ_Aε_Ae_A(Y_A) = -½(κ(𝒟'Y) - Σ_{A,C}ε_Aε_Cc_Ac_C(ω'_CY)_A)`. -/
theorem div_frame_Y (D : DiracData (MatLie m) V S₀) (X : ST 3 → Fin 4 → S₀) (x : ST 3)
    (hκ : ∀ C, kap D.Fr (fd z X C x) = 0) :
    ∑ A, D.Fr.ε A • fd z X A x A = -(1 / 2 : ℝ) • (kap D.Fr (QF z D X x) -
      ∑ A, ∑ C, (D.Fr.ε A * D.Fr.ε C) • D.Fr.c A (D.Fr.c C (ωF z D x C (X x A) -
        ∑ E, ΓF z x C A E • X x E))) := by
  have hQ : kap D.Fr (QF z D X x) = ∑ A, ∑ C, (D.Fr.ε A * D.Fr.ε C) •
      (D.Fr.c A * D.Fr.c C) (fd z X C x A) + ∑ A, ∑ C, (D.Fr.ε A * D.Fr.ε C) •
        D.Fr.c A (D.Fr.c C (ωF z D x C (X x A) - ∑ E, ΓF z x C A E • X x E)) := by
    rw [kap_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [QF_apply, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [covF_apply, map_smul, smul_smul, Module.End.mul_apply, ← smul_add, ← map_add, ← map_add]
  -- the Clifford relation on the derivative part
  have hsym : ∑ A, ∑ C, (D.Fr.ε A * D.Fr.ε C) • (D.Fr.c A * D.Fr.c C) (fd z X C x A) =
      (-2 : ℝ) • ∑ A, D.Fr.ε A • fd z X A x A := by
    have e1 : ∑ A, ∑ C, (D.Fr.ε A * D.Fr.ε C) • (D.Fr.c C * D.Fr.c A) (fd z X C x A) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun C _ => ?_
      have := hκ C
      rw [kap_apply] at this
      have e2 : ∑ A, (D.Fr.ε A * D.Fr.ε C) • (D.Fr.c C * D.Fr.c A) (fd z X C x A) =
          D.Fr.ε C • D.Fr.c C (∑ A, D.Fr.ε A • D.Fr.c A (fd z X C x A)) := by
        rw [map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [map_smul, smul_smul, Module.End.mul_apply, mul_comm]
      rw [e2, this, map_zero, smul_zero]
    have e3 : ∀ A C, (D.Fr.c A * D.Fr.c C) = -(D.Fr.c C * D.Fr.c A) +
        ((-2 : ℝ) * (if A = C then D.Fr.ε A else 0)) • (1 : Module.End ℝ S₀) := by
      intro A C
      rw [← D.Fr.anticomm A C]; abel
    have e4 : ∀ A C, (D.Fr.ε A * D.Fr.ε C) • (D.Fr.c A * D.Fr.c C) (fd z X C x A) =
        -((D.Fr.ε A * D.Fr.ε C) • (D.Fr.c C * D.Fr.c A) (fd z X C x A)) +
          (D.Fr.ε A * D.Fr.ε C * ((-2 : ℝ) * (if A = C then D.Fr.ε A else 0))) • fd z X C x A := by
      intro A C
      rw [e3 A C, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
        Module.End.one_apply, smul_add, smul_neg, smul_smul]
    simp only [e4, Finset.sum_add_distrib, Finset.sum_neg_distrib, e1, neg_zero, zero_add]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.sum_eq_single A (fun C _ hC => by rw [if_neg (Ne.symm hC)]; simp) (by simp),
      if_pos rfl, smul_smul]
    congr 1
    have := D.Fr.sign_sq A
    linear_combination (-2 * D.Fr.ε A) * this
  rw [hQ, hsym, add_sub_cancel_right, smul_smul]
  norm_num

/-- Frame derivatives of a bilinear pairing of fields (product rule). -/
theorem fd_bilin {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (Bf : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] ℝ) {f : ST 3 → E₁} {g : ST 3 → E₂} {x : ST 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (C : Fin 4) :
    fd z (fun y => Bf (f y) (g y)) C x = Bf (fd z f C x) (g x) + Bf (f x) (fd z g C x) := by
  have hpd : ∀ γ, pd (fun y => Bf (f y) (g y)) γ x = Bf (pd f γ x) (g x) + Bf (f x) (pd g γ x) := by
    intro γ
    refine pd_eq_of_line ((contDiff_iff_contDiffAt.2 fun y =>
      ContDiffAt.bilinApply Bf hf.contDiffAt hg.contDiffAt).differentiable (by simp) x) ?_
    have h := hasDerivAt_bilin Bf (hasDerivAt_line0 (hf.differentiable (by simp) x) γ)
      (hasDerivAt_line0 (hg.differentiable (by simp) x) γ)
    simp only [zero_smul, add_zero] at h
    exact h
  rw [fd_eq_sum, fd_eq_sum, fd_eq_sum]
  simp only [hpd, smul_eq_mul, mul_add, Finset.sum_add_distrib, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply]

theorem fd_clm_apply {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (L : E₁ →ₗ[ℝ] E₂)
    {f : ST 3 → E₁} {x : ST 3} (hf : ContDiff ℝ ∞ f) (C : Fin 4) :
    fd z (fun y => L (f y)) C x = L (fd z f C x) :=
  fd_lin z L (hf.differentiable (by simp) x) C

variable {S₁ : Type*} [NormedAddCommGroup S₁] [NormedSpace ℝ S₁] [FiniteDimensional ℝ S₁]

/-- **The frame derivative of the kinetic Dirac stress** (product rule). -/
theorem fd_kinT (D : DiracData (MatLie m) V S₀) (P : S₁ →ₗ[ℝ] S₀ →ₗ[ℝ] ℝ) {ψ : ST 3 → S₀}
    {ψb : ST 3 → S₁} {X : ST 3 → Fin 4 → S₀} {Xb : ST 3 → Fin 4 → S₁} (hψ : ContDiff ℝ ∞ ψ)
    (hψb : ContDiff ℝ ∞ ψb) (hX : ContDiff ℝ ∞ X) (hXb : ContDiff ℝ ∞ Xb) (x : ST 3)
    (A B C : Fin 4) :
    fd z (fun y => kinT D P (ψ y) (X y) (ψb y) (Xb y) A B) C x =
      -(1 / 4 : ℝ) * (P (fd z ψb C x) (D.Fr.c A (X x B)) + P (ψb x) (D.Fr.c A (fd z X C x B)) +
        P (fd z ψb C x) (D.Fr.c B (X x A)) + P (ψb x) (D.Fr.c B (fd z X C x A)) -
        P (fd z Xb C x B) (D.Fr.c A (ψ x)) - P (Xb x B) (D.Fr.c A (fd z ψ C x)) -
        P (fd z Xb C x A) (D.Fr.c B (ψ x)) - P (Xb x A) (D.Fr.c B (fd z ψ C x))) := by
  have hXc := fun E => contDiff_pi.1 hX E
  have hXbc := fun E => contDiff_pi.1 hXb E
  have hc : ∀ (E : Fin 4) {f : ST 3 → S₀}, ContDiff ℝ ∞ f →
      ContDiff ℝ ∞ (fun y => D.Fr.c E (f y)) := fun E f hf =>
    (LinearMap.toContinuousLinearMap (D.Fr.c E)).contDiff.comp hf
  have hcom : ∀ (E : Fin 4) {f : ST 3 → S₀}, ContDiff ℝ ∞ f →
      fd z (fun y => D.Fr.c E (f y)) C x = D.Fr.c E (fd z f C x) := fun E f hf =>
    fd_clm_apply z (D.Fr.c E) hf C
  have hP : ∀ {f : ST 3 → S₁} {g : ST 3 → S₀}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      ContDiff ℝ ∞ (fun y => P (f y) (g y)) := fun hf hg =>
    contDiff_iff_contDiffAt.2 fun y => ContDiffAt.bilinApply P hf.contDiffAt hg.contDiffAt
  have hfdX : ∀ E, fd z (fun y => X y E) C x = fd z X C x E := fun E =>
    (fd_apply z (hX.differentiable (by simp) x) C E).symm
  have hfdXb : ∀ E, fd z (fun y => Xb y E) C x = fd z Xb C x E := fun E =>
    (fd_apply z (hXb.differentiable (by simp) x) C E).symm
  unfold kinT
  have h1 := fd_bilin z P hψb (hc A (hXc B)) C (x := x)
  have h2 := fd_bilin z P hψb (hc B (hXc A)) C (x := x)
  have h3 := fd_bilin z P (hXbc B) (hc A hψ) C (x := x)
  have h4 := fd_bilin z P (hXbc A) (hc B hψ) C (x := x)
  rw [hcom A (hXc B), hfdX] at h1
  rw [hcom B (hXc A), hfdX] at h2
  rw [hcom A hψ, hfdXb] at h3
  rw [hcom B hψ, hfdXb] at h4
  -- linearity of the frame derivative
  have hd : ∀ {f : ST 3 → ℝ}, ContDiff ℝ ∞ f → DifferentiableAt ℝ f x := fun hf =>
    hf.differentiable (by simp) x
  have f1 := hP hψb (hc A (hXc B))
  have f2 := hP hψb (hc B (hXc A))
  have f3 := hP (hXbc B) (hc A hψ)
  have f4 := hP (hXbc A) (hc B hψ)
  have hlin : fd z (fun y => -(1 / 4 : ℝ) * (P (ψb y) (D.Fr.c A (X y B)) + P (ψb y) (D.Fr.c B (X y A)) -
      P (Xb y B) (D.Fr.c A (ψ y)) - P (Xb y A) (D.Fr.c B (ψ y)))) C x =
      -(1 / 4 : ℝ) * (fd z (fun y => P (ψb y) (D.Fr.c A (X y B))) C x +
        fd z (fun y => P (ψb y) (D.Fr.c B (X y A))) C x -
        fd z (fun y => P (Xb y B) (D.Fr.c A (ψ y))) C x -
        fd z (fun y => P (Xb y A) (D.Fr.c B (ψ y))) C x) := by
    rw [fd_eq_sum, fd_eq_sum, fd_eq_sum, fd_eq_sum, fd_eq_sum]
    simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hpd : pd (fun y => -(1 / 4 : ℝ) * (P (ψb y) (D.Fr.c A (X y B)) +
        P (ψb y) (D.Fr.c B (X y A)) - P (Xb y B) (D.Fr.c A (ψ y)) -
        P (Xb y A) (D.Fr.c B (ψ y)))) γ x = -(1 / 4 : ℝ) * (pd (fun y => P (ψb y) (D.Fr.c A (X y B))) γ x +
          pd (fun y => P (ψb y) (D.Fr.c B (X y A))) γ x -
          pd (fun y => P (Xb y B) (D.Fr.c A (ψ y))) γ x -
          pd (fun y => P (Xb y A) (D.Fr.c B (ψ y))) γ x) := by
      refine pd_eq_of_line ((contDiff_const.mul (((f1.add f2).sub f3).sub f4)).differentiable
        (by simp) x) ?_
      exact ((((hasDerivAt_line0 (hd f1) γ).add (hasDerivAt_line0 (hd f2) γ)).sub
        (hasDerivAt_line0 (hd f3) γ)).sub (hasDerivAt_line0 (hd f4) γ)).const_mul _
    rw [hpd]
    ring
  rw [hlin, h1, h2, h3, h4]
  ring

end RenewalGeometry.GenCplDiv
