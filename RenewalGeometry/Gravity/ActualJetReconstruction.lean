/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ActualJetSpinorRows

/-!
# Reconstruction of the first jets from the actual-jet state; the off-shell stress
  (`prop:actual-jet-writer`, clause (d))

Einstein–Standard-Model action-closure manuscript, `prop:actual-jet-writer` and the paragraph
before it: "The complete torsion-free Standard-Model stress is algebraic in the actual first jets
`(g, F, H, DH, Ψ, Ψ̄, X_a, X̄_a)` and contains no derivative of `F`, `DH` or `X`.  After
`eq:normal-spinor-jet` it is a smooth algebraic function of the tangential actual-jet state and is
at most linear in the Dirac residual."

## Coframe inversion

For an orthonormal frame jet (`FrameCurvature.FrameJet`) the lowered frame
`θ^A{}_μ = ε_A g_{μν}e_A{}^ν` (`cof`) is the dual coframe: `Σ_A θ^A{}_μe_A{}^α = δ_μ^α`
(`cof_dual`).  Hence every coordinate component is recovered from the frame components
(`inv_vec`, `inv_tensor`):
* `∂_γg_{μν} = θ^0{}_γ p_{μν} + Σ_a θ^a{}_γ q_{a,μν}` (metric first jets from `(p, q)`);
* `F_{μν} = Σ_{AB} θ^A{}_μθ^B{}_ν F(e_A, e_B)` with `F(e_0, e_a) = E_a`,
  `F(e_b, e_c) = -ε_{bcd}B_d` (`fieldOfEB`, `Fm_recon`);
* `D_μH = θ^0{}_μΠ + Σ_a θ^a{}_μQ_a` (`DH_recon`);
* `∂_γΨ = Σ_A θ^A{}_γ(X_A - ω_AΨ)` (spinor first jets from `X`).

## The off-shell stress (clause (d))

* `ymStressB`, `higgsStressB` — `eq:YM-stress`, `eq:H-stress` (with a fixed invariant inner
  product on the gauge algebra and a real inner product on the Higgs space);
* `DiracStressForm` — every stress of the bilinear first-order Dirac–Yukawa type
  `T^D_{AB} = Σ_C (P_{ABC}(Ψ̄, X_C) + P'_{ABC}(X̄_C, Ψ)) + P''_{AB}(H)(Ψ̄, Ψ)` in the frame (the complete
  metric variation of `eq:dirac-density` is of this type, since the density is bilinear in
  `(Ψ̄, ∇Ψ)` and `(∇Ψ̄, Ψ)`);
* **`stress_elimination`** — after `eq:normal-spinor-jet` (`X_0 = X_0^♮ - c_0r_D`,
  `X̄_0 = X̄_0^♮ - c̄_0r̄_D`) the complete stress is `T = 𝒯_0 + 𝒯_1(r_D, r̄_D)` with `𝒯_0` evaluated
  on the tangential state and `𝒯_1` linear (`stressRes`).
-/

namespace RenewalGeometry.ActualJetRecon

open Finset FrameCurvature ActualJetWriter ActualJetGauge

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Coframe inversion -/

section Coframe

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The lowered frame (coframe) `θ^A{}_μ = ε_A g_{μν}e_A{}^ν`. -/
def cof (g : n → n → ℝ) (ε : ι → ℝ) (e : ι → n → ℝ) (A : ι) (μ : n) : ℝ :=
  ε A * ∑ ν, g μ ν * e A ν

/-- **The coframe is dual to the frame**: `Σ_A θ^A{}_μ e_A{}^α = δ_μ^α`. -/
theorem cof_dual (F : FrameJet n ι) (μ α : n) :
    ∑ A, cof F.g F.ε F.e A μ * F.e A α = if μ = α then 1 else 0 := by
  have h : ∑ A, cof F.g F.ε F.e A μ * F.e A α = ∑ ν, F.g μ ν * F.gi ν α := by
    unfold cof
    simp only [F.compl, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun A _ => by ring
  rw [h, F.hinv]

/-- **Inversion of frame components of a covector-like family**:
`w_γ = Σ_A θ^A{}_γ (e_A{}^βw_β)`. -/
theorem inv_vec {M : Type*} [AddCommGroup M] [Module ℝ M] (F : FrameJet n ι) (w : n → M)
    (γ : n) : w γ = ∑ A, cof F.g F.ε F.e A γ • ∑ β, F.e A β • w β := by
  have : ∑ A, cof F.g F.ε F.e A γ • ∑ β, F.e A β • w β =
      ∑ β, (∑ A, cof F.g F.ε F.e A γ * F.e A β) • w β := by
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [this]
  simp only [cof_dual, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

/-- **Inversion of frame components of a 2-tensor**:
`T_{μν} = Σ_{A,B} θ^A{}_μθ^B{}_ν T(e_A, e_B)`. -/
theorem inv_tensor {M : Type*} [AddCommGroup M] [Module ℝ M] (F : FrameJet n ι)
    (T : n → n → M) (μ ν : n) :
    T μ ν = ∑ A, ∑ B, (cof F.g F.ε F.e A μ * cof F.g F.ε F.e B ν) •
      ∑ α, ∑ β, (F.e A α * F.e B β) • T α β := by
  have h1 : ∀ α, T α ν = ∑ B, cof F.g F.ε F.e B ν • ∑ β, F.e B β • T α β :=
    fun α => inv_vec F (fun β => T α β) ν
  rw [inv_vec F (fun α => T α ν) μ]
  simp only [h1]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun β _ => ?_
  congr 1; ring

end Coframe

/-! ### The field strength from `(E, B)` and the Higgs gradient from `(Π, Q)` -/

section Gauge

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

/-- The frame components of the field strength in terms of the electric and magnetic fields:
`F(e_0, e_0) = 0`, `F(e_0, e_a) = E_a`, `F(e_a, e_0) = -E_a`, `F(e_b, e_c) = -Σ_d ε_{bcd}B_d`. -/
def fieldOfEB (E B : Fin 3 → 𝔤) (X Y : Fin 4) : 𝔤 :=
  Fin.cases (Fin.cases 0 (fun c => E c) Y)
    (fun b => Fin.cases (-E b) (fun c => -∑ d, eps3 b c d • B d) Y) X

variable (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
  (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤)

/-- **The frame components of the field strength are determined by `(E, B)`**. -/
theorem frT_Fm_eq (X Y : Fin 4) :
    frT AF (Fm A dA) X Y = fieldOfEB (elec AF A dA) (magn AF A dA) X Y := by
  induction X using Fin.cases with
  | zero =>
    induction Y using Fin.cases with
    | zero =>
      have h := frT_anti AF (Fm_anti A dA) 0 0
      show frT AF (Fm A dA) 0 0 = 0
      have : (2 : ℝ) • frT AF (Fm A dA) 0 0 = 0 := by rw [two_smul]; nth_rw 1 [h]; abel
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero
    | succ c => rfl
  | succ b =>
    induction Y using Fin.cases with
    | zero =>
      show frT AF (Fm A dA) b.succ 0 = -elec AF A dA b
      rw [frT_anti AF (Fm_anti A dA)]; rfl
    | succ c =>
      show Fsp AF A dA b c = -∑ d, eps3 b c d • magn AF A dA d
      exact anti_eq_eps_dual (Fsp_anti AF A dA) b c

/-- **`F_{μν} = Σ_{AB} θ^A{}_μθ^B{}_ν F(e_A, e_B)`** with the frame components from `(E, B)`. -/
theorem Fm_recon (FJ : FrameJet (Fin 4) (Fin 4)) (hfr : ∀ B μ, FJ.e B μ = AF.fr B μ)
    (μ ν : Fin 4) :
    Fm A dA μ ν = ∑ X, ∑ Y, (cof FJ.g FJ.ε FJ.e X μ * cof FJ.g FJ.ε FJ.e Y ν) •
      fieldOfEB (elec AF A dA) (magn AF A dA) X Y := by
  rw [inv_tensor FJ (Fm A dA) μ ν]
  refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun Y _ => ?_
  rw [← frT_Fm_eq]
  unfold frT
  simp only [hfr]

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]

/-- The frame components of the Higgs gradient: `D_{e_0}H = Π`, `D_{e_a}H = Q_a`. -/
def gradOfPQ (Pm : V) (Q : Fin 3 → V) (X : Fin 4) : V := Fin.cases Pm Q X

/-- **`D_μH = Σ_A θ^A{}_μ D_{e_A}H`** with `D_{e_0}H = Π`, `D_{e_a}H = Q_a`. -/
theorem DH_recon (FJ : FrameJet (Fin 4) (Fin 4)) (hfr : ∀ B μ, FJ.e B μ = AF.fr B μ)
    (H : V) (dH : Fin 4 → V) (μ : Fin 4) :
    ActualJetGauge.DH A H dH μ = ∑ X, cof FJ.g FJ.ε FJ.e X μ •
      gradOfPQ (frV AF A H dH 0) (fun a => frV AF A H dH a.succ) X := by
  rw [inv_vec FJ (ActualJetGauge.DH A H dH) μ]
  refine Finset.sum_congr rfl fun X _ => ?_
  congr 1
  induction X using Fin.cases with
  | zero => unfold gradOfPQ frV; simp only [hfr]; rfl
  | succ a => unfold gradOfPQ frV; simp only [hfr]; rfl

end Gauge

/-! ### The metric first jets from `(p, q)` -/

/-- The frame derivatives of a metric component: `e_0(u) = p`, `e_a(u) = q_a`. -/
def gradOfpq (p : ℝ) (q : Fin 3 → ℝ) (X : Fin 4) : ℝ := Fin.cases p q X

/-- **`∂_γg_{μν} = Σ_A θ^A{}_γ e_A(g_{μν})`** with `e_0(g_{μν}) = p_{μν}`, `e_a(g_{μν}) = q_{a,μν}`. -/
theorem dg_recon (FJ : FrameJet (Fin 4) (Fin 4)) (AF : AdaptedFrame)
    (hfr : ∀ B μ, FJ.e B μ = AF.fr B μ) (γ μ ν : Fin 4) :
    FJ.dg γ μ ν = ∑ X, cof FJ.g FJ.ε FJ.e X γ *
      gradOfpq (AF.pJ (fun α => FJ.dg α μ ν)) (fun a => AF.qJ (fun α => FJ.dg α μ ν) a) X := by
  have := inv_vec FJ (fun α => FJ.dg α μ ν) γ
  simp only [smul_eq_mul] at this
  rw [this]
  refine Finset.sum_congr rfl fun X _ => ?_
  congr 1
  induction X using Fin.cases with
  | zero => unfold gradOfpq AdaptedFrame.pJ; simp only [hfr]; rfl
  | succ a => unfold gradOfpq AdaptedFrame.qJ; simp only [hfr]; rfl

/-! ### The off-shell stress -/

section Stress

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The Yang–Mills stress `eq:YM-stress` with an invariant inner product `⟨·,·⟩` on the gauge
algebra: `T_{μν} = g^{αβ}⟨F_{μα}, F_{νβ}⟩ - ¼g_{μν}g^{αγ}g^{βδ}⟨F_{αβ}, F_{γδ}⟩`. -/
def ymStressB (ipG : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] ℝ) (g gi : Fin 4 → Fin 4 → ℝ) (F : Fin 4 → Fin 4 → 𝔤)
    (μ ν : Fin 4) : ℝ :=
  ∑ α, ∑ β, gi α β * ipG (F μ α) (F ν β) -
    (1 / 4) * g μ ν * ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ * ipG (F α β) (F γ δ)

/-- The Higgs stress `eq:H-stress`:
`T^H_{μν} = 2⟨D_μH, D_νH⟩ - g_{μν}(g^{αβ}⟨D_αH, D_βH⟩ + λ(|H|² - v²)²)`. -/
def higgsStressB (ipV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (lam v : ℝ) (g gi : Fin 4 → Fin 4 → ℝ) (H : V)
    (DH : Fin 4 → V) (μ ν : Fin 4) : ℝ :=
  2 * ipV (DH μ) (DH ν) -
    g μ ν * (∑ α, ∑ β, gi α β * ipV (DH α) (DH β) + lam * (ipV H H - v ^ 2) ^ 2)

/-- A stress of bilinear first-order Dirac–Yukawa type, in the frame:
`T^D_{AB} = Σ_C (P_{ABC}(Ψ̄, X_C) + P'_{ABC}(X̄_C, Ψ)) + P''_{AB}(H)(Ψ̄, Ψ)`. -/
structure DiracStressForm (S S' W : Type*) [AddCommGroup S] [Module ℝ S] [AddCommGroup S']
    [Module ℝ S'] where
  P : Fin 4 → Fin 4 → Fin 4 → S' →ₗ[ℝ] S →ₗ[ℝ] ℝ
  P' : Fin 4 → Fin 4 → Fin 4 → S' →ₗ[ℝ] S →ₗ[ℝ] ℝ
  P'' : Fin 4 → Fin 4 → W → S' →ₗ[ℝ] S →ₗ[ℝ] ℝ

variable {S S' : Type*} [AddCommGroup S] [Module ℝ S] [AddCommGroup S'] [Module ℝ S']

/-- The frame components of a Dirac–Yukawa stress. -/
def DiracStressForm.frame (D : DiracStressForm S S' V) (H : V) (ψ : S) (X : Fin 4 → S)
    (ψb : S') (Xb : Fin 4 → S') (A B : Fin 4) : ℝ :=
  ∑ C, (D.P A B C ψb (X C) + D.P' A B C (Xb C) ψ) + D.P'' A B H ψb ψ

/-- Its coordinate components `T^D_{μν} = θ^A{}_μθ^B{}_νT^D_{AB}`. -/
def DiracStressForm.coord (D : DiracStressForm S S' V) (g : Fin 4 → Fin 4 → ℝ) (ε : Fin 4 → ℝ)
    (e : Fin 4 → Fin 4 → ℝ) (H : V) (ψ : S) (X : Fin 4 → S) (ψb : S') (Xb : Fin 4 → S')
    (μ ν : Fin 4) : ℝ :=
  ∑ A, ∑ B, cof g ε e A μ * cof g ε e B ν * D.frame H ψ X ψb Xb A B

/-- The residual part `𝒯_1(r_D, r̄_D)` of the stress, linear in the Dirac residuals. -/
def DiracStressForm.stressRes (D : DiracStressForm S S' V) (g : Fin 4 → Fin 4 → ℝ)
    (ε : Fin 4 → ℝ) (e : Fin 4 → Fin 4 → ℝ) (ψ : S) (ψb : S') (kr : S) (kbr : S')
    (μ ν : Fin 4) : ℝ :=
  ∑ A, ∑ B, cof g ε e A μ * cof g ε e B ν *
    (D.P A B 0 ψb kr + D.P' A B 0 kbr ψ)

/-- **Normal-jet elimination in the stress** (clause (d)): if `X_0 = X_0^♮ - k` and
`X̄_0 = X̄_0^♮ - k̄` (`eq:normal-spinor-jet` with `k = c_0r_D`, `k̄ = c̄_0r̄_D`), then
`T^D(X) = T^D(X^♮) - 𝒯_1(k, k̄)`: the stress is the tangential-state stress plus a term linear in
the Dirac residuals. -/
theorem DiracStressForm.stress_elimination (D : DiracStressForm S S' V)
    (g : Fin 4 → Fin 4 → ℝ) (ε : Fin 4 → ℝ) (e : Fin 4 → Fin 4 → ℝ) (H : V) (ψ : S) (X Xn : Fin 4 → S) (ψb : S')
    (Xb Xbn : Fin 4 → S') (k : S) (kb : S') (hX : X 0 = Xn 0 - k)
    (hXt : ∀ a : Fin 3, X a.succ = Xn a.succ) (hXb : Xb 0 = Xbn 0 - kb)
    (hXbt : ∀ a : Fin 3, Xb a.succ = Xbn a.succ) (μ ν : Fin 4) :
    D.coord g ε e H ψ X ψb Xb μ ν =
      D.coord g ε e H ψ Xn ψb Xbn μ ν - D.stressRes g ε e ψ ψb k kb μ ν := by
  unfold coord stressRes frame
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun B _ => ?_
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hX, hXb, hXt, hXbt, map_sub,
    LinearMap.sub_apply]
  ring

end Stress

end

end RenewalGeometry.ActualJetRecon
