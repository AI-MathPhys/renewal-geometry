/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedStressNoether

/-!
# The Dirac current and the Yukawa source in the theory data: the current Noether identity

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`): the Gauss constraint propagates along the independent symmetric system
when the gauge current is covariantly conserved on the matter equations
(`GenNoether.CurrentNoether`).  `GenNoether.currentNoether_of_variational` proves this for
Yang–Mills–Higgs data whose current and Higgs source do not see the spinors.  This file adds the
**spinor pairing** and the **Dirac current and Yukawa source** of the Dirac Lagrangian
`L_D = ⟨Ψ̄, 𝒟Ψ - 𝓜(H)Ψ⟩` to the theory data and proves the current Noether identity **with the
Dirac terms**:

* `DiracPairing SM` — a bilinear pairing `⟨·,·⟩ : S' × S → ℝ` for which the co-spinor Dirac block
  is the transpose of the spinor block (`c̄_A = c_Aᵀ`, `ρ̄ = -ρᵀ`, `𝓜̄ = -𝓜ᵀ`), a nondegenerate gauge
  form, and the **spinor moment map** `μ_S : S' × S → 𝔤`, `⟨X, μ_S(φ, x)⟩_𝔤 = ⟨φ, ρ(X)x⟩`,
  gauge equivariant;
* `diracCur` — the Dirac current `J^D_ν = -g_{νμ} Σ_A ε_A e_A{}^μ μ_S(Ψ̄, c_AΨ)` in the adapted
  frame `e = frU(g⁻¹)` of the actual-jet model (`J = -δL_D/δA`);
* `VariationalDirac SM` — theory data whose current is the Higgs current plus the Dirac current
  and whose Higgs source is the potential force plus the Yukawa source
  `2⟨η, S_Y⟩_V = ⟨Ψ̄, 𝓜_H[η]Ψ⟩` (the Euler–Lagrange sources of
  `-¼⟨F,F⟩ - ⟨DH,DH⟩ - λ(⟨H,H⟩ - v²)² + ⟨Ψ̄, 𝒟Ψ - 𝓜(H)Ψ⟩`);
* `frame_div` — the coordinate divergence of a frame vector field is the frame trace of the
  connection coefficients, `∇_μe_C{}^μ = Σ_A ε_A G_{ACA}`;
* **`currentNoether_of_variationalDirac`** — such data satisfy the current Noether identity
  `ϱ D^νJ_ν = ϱ(2μ(H, r_H) - μ_S(r̄_D, Ψ) - μ_S(Ψ̄, r_D))`: the Dirac current is conserved on the
  Dirac equations up to the Yukawa force, which cancels the Yukawa part of the Higgs current.

The stress Noether identity with the Dirac stress and the propagation of the spinor defining-jet
identities are NOT derived here (see the record notes: the prolonged spinor defect is coupled to
the harmonic defect at first order through the Dirac stress).
-/

open Finset Set
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenDiracCur

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState JetCurve GenNoether

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-! ### The spinor pairing -/

section Pairing

/-- **A spinor pairing for the theory data**: a bilinear pairing `⟨·,·⟩ : S' × S → ℝ` for which
the co-spinor Dirac block is the transpose of the spinor block (Clifford generators transposed,
gauge action and mass map transposed with a sign), a nondegenerate gauge form and the spinor
moment map `μ_S`, dual to the gauge action on spinors and gauge equivariant. -/
structure DiracPairing (SM : SMData (MatLie m) V S S') where
  /-- the pairing `⟨Ψ̄, Ψ⟩` -/
  P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ
  c_tr : ∀ A φ x, P (SM.Db.Fr.c A φ) x = P φ (SM.D.Fr.c A x)
  ρ_tr : ∀ X φ x, P (SM.Db.ρ X φ) x = -P φ (SM.D.ρ X x)
  m0_tr : ∀ φ x, P (SM.Db.m0 φ) x = -P φ (SM.D.m0 x)
  L_tr : ∀ w φ x, P (SM.Db.L w φ) x = -P φ (SM.D.L w x)
  /-- the gauge form is nondegenerate -/
  ipG_nondeg : ∀ Y, (∀ X, SM.ipG X Y = 0) → Y = 0
  /-- the spinor moment map -/
  μS : S' →ₗ[ℝ] S →ₗ[ℝ] MatLie m
  μS_dual : ∀ X φ x, SM.ipG X (μS φ x) = P φ (SM.D.ρ X x)
  μS_equiv : ∀ X φ x, ⁅X, μS φ x⁆ = μS (SM.Db.ρ X φ) x + μS φ (SM.D.ρ X x)

variable {SM : SMData (MatLie m) V S S'}

/-- Both Dirac blocks carry the Lorentzian signs. -/
theorem eps_Db_eq : SM.Db.Fr.ε = SM.D.Fr.ε := by
  funext A
  induction A using Fin.cases with
  | zero => rw [SM.Db.lorentz.1, SM.D.lorentz.1]
  | succ a => rw [SM.Db.lorentz.2 a, SM.D.lorentz.2 a]

theorem eps_D_eq : SM.D.Fr.ε = lorentzSign := by
  funext A
  induction A using Fin.cases with
  | zero => rw [SM.D.lorentz.1]; rfl
  | succ a => rw [SM.D.lorentz.2 a]; simp [lorentzSign, Fin.succ_ne_zero]

namespace DiracPairing

variable (hP : DiracPairing SM)

/-- The moment map identity transfers along a pair of transposed operators commuting with the
gauge action. -/
theorem μS_transpose {T : Module.End ℝ S} {T' : Module.End ℝ S'}
    (htr : ∀ φ x, hP.P (T' φ) x = hP.P φ (T x)) (hc : ∀ X, SM.D.ρ X * T = T * SM.D.ρ X)
    (φ : S') (x : S) : hP.μS (T' φ) x = hP.μS φ (T x) := by
  have h := hP.ipG_nondeg (hP.μS (T' φ) x - hP.μS φ (T x)) fun X => by
    rw [map_sub, hP.μS_dual, hP.μS_dual, htr]
    have : SM.D.ρ X (T x) = T (SM.D.ρ X x) := by
      have := congrArg (fun F : Module.End ℝ S => F x) (hc X)
      simpa using this
    rw [this, sub_self]
  exact sub_eq_zero.1 h

/-- `μ_S(c̄_Aφ, x) = μ_S(φ, c_Ax)`. -/
theorem μS_c (A : Fin 4) (φ : S') (x : S) :
    hP.μS (SM.Db.Fr.c A φ) x = hP.μS φ (SM.D.Fr.c A x) :=
  hP.μS_transpose (hP.c_tr A) (fun X => SM.D.comm X A) φ x

/-- The pairing of a product of two transposed Clifford generators reverses the order. -/
theorem P_cc (c d : Fin 4) (φ : S') (x : S) :
    hP.P ((SM.Db.Fr.c c * SM.Db.Fr.c d) φ) x = hP.P φ ((SM.D.Fr.c d * SM.D.Fr.c c) x) := by
  simp only [Module.End.mul_apply]
  rw [hP.c_tr, hP.c_tr]

/-- **The transposed spin lift is minus the spin lift** for an antisymmetric array:
`⟨X̄_Wφ, x⟩ = -⟨φ, X_Wx⟩`. -/
theorem P_spin (W : Fin 4 → Fin 4 → ℝ) (hW : ∀ c d, W d c = -W c d) (φ : S') (x : S) :
    hP.P (spinPart SM.Db.Fr W φ) x = -hP.P φ (spinPart SM.D.Fr W x) := by
  unfold spinPart
  rw [eps_Db_eq]
  simp only [LinearMap.smul_apply, map_smul, map_sum,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, P_cc hP]
  -- relabel and use the antisymmetry of `W`
  have e : ∑ c, ∑ d, SM.D.Fr.ε c * SM.D.Fr.ε d * W c d *
      hP.P φ ((SM.D.Fr.c d * SM.D.Fr.c c) x) =
      -∑ c, ∑ d, SM.D.Fr.ε c * SM.D.Fr.ε d * W c d * hP.P φ ((SM.D.Fr.c c * SM.D.Fr.c d) x) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hW c d]
    ring
  simp only [Module.End.mul_apply] at e ⊢
  rw [e]
  ring

/-- The gauge action commutes with every spin lift. -/
theorem ρ_spin (X : MatLie m) (W : Fin 4 → Fin 4 → ℝ) :
    SM.D.ρ X * spinPart SM.D.Fr W = spinPart SM.D.Fr W * SM.D.ρ X :=
  commute_spinPart SM.D.Fr _ (commute_pair_of_commute SM.D.Fr _ (fun b => SM.D.comm X b)) W

/-- `μ_S(X̄_Wφ, x) = -μ_S(φ, X_Wx)`. -/
theorem μS_spin (W : Fin 4 → Fin 4 → ℝ) (hW : ∀ c d, W d c = -W c d) (φ : S') (x : S) :
    hP.μS (spinPart SM.Db.Fr W φ) x = -hP.μS φ (spinPart SM.D.Fr W x) := by
  have h := hP.μS_transpose (T := -spinPart SM.D.Fr W) (T' := spinPart SM.Db.Fr W)
    (fun φ x => by rw [hP.P_spin W hW]; simp) (fun X => by
      rw [mul_neg, neg_mul, ρ_spin]) φ x
  rw [h]
  simp

/-- **The mass terms of the two Dirac blocks pair to the gauge commutator of the mass map**:
`⟨X, μ_S(𝓜̄φ, x) + μ_S(φ, 𝓜x)⟩_𝔤 = ⟨φ, 𝓜_H[X·H]x⟩`. -/
theorem ipG_μS_mass (H : V) (X : MatLie m) (φ : S') (x : S) :
    SM.ipG X (hP.μS (mass SM.Db.m0 SM.Db.L H φ) x + hP.μS φ (mass SM.D.m0 SM.D.L H x)) =
      hP.P φ (SM.D.L ⁅X, H⁆ x) := by
  have hm : ∀ y, hP.P (mass SM.Db.m0 SM.Db.L H φ) y = -hP.P φ (mass SM.D.m0 SM.D.L H y) := by
    intro y
    simp only [mass, LinearMap.add_apply, map_add, LinearMap.add_apply, hP.m0_tr, hP.L_tr]
    ring
  rw [map_add, hP.μS_dual, hP.μS_dual, hm]
  have h := SM.D.mass_eq X H
  have h2 := congrArg (fun F : Module.End ℝ S => hP.P φ (F x)) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub] at h2
  rw [← h2]
  ring

end DiracPairing

end Pairing

/-! ### The frame divergence -/

section FrameDiv

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- **The coordinate divergence of a frame vector field is the frame trace of the connection
coefficients**: `Σ_γ (∇_γe_C)^γ = Σ_A ε_A G_{ACA}`. -/
theorem frame_div (F : FrameJet n ι) (C : ι) :
    ∑ γ, F.Ne C γ γ = ∑ A, F.ε A * F.G A C A := by
  have e1 : ∑ A, F.ε A * F.G A C A =
      ∑ γ, ∑ μ, ∑ ν, F.g μ ν * F.Ne C γ μ * ∑ A, F.ε A * F.e A γ * F.e A ν := by
    unfold FrameJet.G FrameJet.P ipg
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun A _ => ?_
    ring
  rw [e1]
  simp only [← F.compl]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have e2 : ∀ μ, ∑ ν, F.g μ ν * F.Ne C γ μ * F.gi γ ν = F.Ne C γ μ * (if μ = γ then 1 else 0) := by
    intro μ
    rw [← F.hinv μ γ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [F.gi_symm γ ν]
    ring
  simp only [e2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end FrameDiv


/-! ### The Dirac current and variational Dirac theory data -/

section Current

/-- **The Dirac current** `J^D_ν = -g_{νμ} Σ_A ε_A e_A{}^μ μ_S(Ψ̄, c_AΨ)` in the adapted frame
`e = frU(g⁻¹)` of the actual-jet model (`J = -δL_D/δA`, `L_D = ⟨Ψ̄, 𝒟Ψ - 𝓜(H)Ψ⟩`). -/
def diracCur (μS : S' →ₗ[ℝ] S →ₗ[ℝ] MatLie m) (Fr : CliffordFrame (Fin 4) (Module.End ℝ S))
    (g gi : Fin 4 → Fin 4 → ℝ) (ψ : S) (ψb : S') (ν : Fin 4) : MatLie m :=
  -∑ μ, g ν μ • ∑ A, (lorentzSign A * frU gi A μ) • μS ψb (Fr.c A ψ)

/-- **Variational Einstein–Yang–Mills–Higgs–Dirac theory data**: the sources are the
Euler–Lagrange sources of `-¼⟨F,F⟩ - ⟨DH,DH⟩ - λ(⟨H,H⟩ - v²)² + ⟨Ψ̄, 𝒟Ψ - 𝓜(H)Ψ⟩`: a spinor
pairing (`DiracPairing`), the Higgs moment map `μ` (as in `GenNoether.VariationalBosonic`), the
current `J_ν = 2μ(H, D_νH) + J^D_ν` (Higgs plus Dirac current) and the Higgs source
`S_H = 2λ(⟨H,H⟩ - v²)H + S_Y` with the Yukawa source `2⟨η, S_Y⟩_V = ⟨Ψ̄, 𝓜_H[η]Ψ⟩`. -/
structure VariationalDirac (SM : SMData (MatLie m) V S S') extends DiracPairing SM where
  μ : V →ₗ[ℝ] V →ₗ[ℝ] MatLie m
  moment : ∀ (X : MatLie m) (u w : V), SM.ipG X (μ u w) = SM.ipV ⁅X, u⁆ w
  alt : ∀ u, μ u u = 0
  equiv : ∀ (X : MatLie m) (u w : V), ⁅X, μ u w⁆ = μ ⁅X, u⁆ w + μ u ⁅X, w⁆
  /-- the Yukawa source -/
  yuk : S' →ₗ[ℝ] S →ₗ[ℝ] V
  yuk_dual : ∀ η φ x, 2 * SM.ipV η (yuk φ x) = P φ (SM.D.L η x)
  J_eq : ∀ g gi H DH ψ ψb ν, SM.Jcur g gi H DH ψ ψb ν =
    (2 : ℝ) • μ H (DH ν) + diracCur μS SM.D.Fr g gi ψ ψb ν
  SH_eq : ∀ g gi H ψ ψb, SM.SH g gi H ψ ψb =
    (2 * SM.lamH * (SM.ipV H H - SM.vH ^ 2)) • H + yuk ψb ψ

variable {SM : SMData (MatLie m) V S S'}

/-- The bosonic part of variational Dirac data (Higgs current and potential force only). -/
def bosData (SM : SMData (MatLie m) V S S') (hV : VariationalDirac SM) :
    SMData (MatLie m) V S S' :=
  { SM with
    Jcur := fun _ _ H DH _ _ ν => (2 : ℝ) • hV.μ H (DH ν)
    SH := fun _ _ H _ _ => (2 * SM.lamH * (SM.ipV H H - SM.vH ^ 2)) • H }

/-- The bosonic part is variational Yang–Mills–Higgs data. -/
def bosVariational (hV : VariationalDirac SM) : VariationalBosonic (bosData SM hV) where
  μ := hV.μ
  moment := hV.moment
  alt := hV.alt
  equiv := hV.equiv
  J_eq := fun _ _ _ _ _ _ _ => rfl
  SH_eq := fun _ _ _ _ _ => rfl

end Current

/-! ### The Dirac current along a tuple -/

section Field

variable {SM : SMData (MatLie m) V S S'} (hV : VariationalDirac SM) (z : Tuple m V S S')

/-- `Ψ_A = μ_S(Ψ̄, c_AΨ)` along the tuple. -/
def psiA (A : Fin 4) (y : ST 3) : MatLie m := hV.μS (z.ψb y) (SM.D.Fr.c A (z.ψ y))

/-- The Dirac current along the tuple. -/
def JDf (y : ST 3) : Fin 4 → MatLie m :=
  diracCur hV.μS SM.D.Fr (z.g y) (z.gi y) (z.ψ y) (z.ψb y)

/-- The Dirac current density `ϱ g^{νβ}J^D_β`. -/
def densD (y : ST 3) (ν : Fin 4) : MatLie m := rho z y • ∑ β, z.gi y ν β • JDf hV z y β

/-- Its gauge-covariant divergence. -/
def divD (x : ST 3) : MatLie m :=
  ∑ ν, (pd (fun y => densD hV z y ν) ν x + ⁅z.A x ν, densD hV z x ν⁆)

theorem gi_g (y : ST 3) (ν μ : Fin 4) :
    ∑ β, z.gi y ν β * z.g y β μ = if ν = μ then 1 else 0 := by
  have h := z.hinv y μ ν
  rw [show (if ν = μ then (1 : ℝ) else 0) = if μ = ν then 1 else 0 by
    by_cases h' : ν = μ
    · subst h'; simp
    · simp [h', Ne.symm h']]
  rw [← h]
  exact Finset.sum_congr rfl fun b _ => by rw [z.gi_symm y ν b, z.g_symm y b μ, mul_comm]

/-- **The Dirac current density in the frame**: `ϱ g^{νβ}J^D_β = -ϱ Σ_A ε_A e_A{}^ν Ψ_A`. -/
theorem densD_eq (y : ST 3) (ν : Fin 4) :
    densD hV z y ν = -∑ A, (lorentzSign A * (rho z y * z.e y A ν)) • psiA hV z A y := by
  have key : densD hV z y ν = -∑ A, ∑ μ, ∑ β,
      (rho z y * (z.gi y ν β * z.g y β μ) * (lorentzSign A * z.e y A μ)) • psiA hV z A y := by
    unfold densD JDf diracCur psiA
    simp only [Finset.smul_sum, smul_neg, Finset.sum_neg_distrib, smul_smul]
    congr 1
    calc _ = ∑ β, ∑ A, ∑ μ, (rho z y * (z.gi y ν β * (z.g y β μ * (lorentzSign A *
          frU (z.gi y) A μ)))) • hV.μS (z.ψb y) (SM.D.Fr.c A (z.ψ y)) :=
          Finset.sum_congr rfl fun β _ => Finset.sum_comm
      _ = ∑ A, ∑ β, ∑ μ, (rho z y * (z.gi y ν β * (z.g y β μ * (lorentzSign A *
          frU (z.gi y) A μ)))) • hV.μS (z.ψb y) (SM.D.Fr.c A (z.ψ y)) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun β _ => ?_
          congr 1
          show _ = rho z y * (z.gi y ν β * z.g y β μ) * (lorentzSign A * frU (z.gi y) A μ)
          ring
  rw [key]
  congr 1
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [← Finset.sum_smul]
  congr 1
  have h : ∀ μ, ∑ β, rho z y * (z.gi y ν β * z.g y β μ) * (lorentzSign A * z.e y A μ) =
      rho z y * (lorentzSign A * z.e y A μ) * (if ν = μ then 1 else 0) := by
    intro μ
    rw [← gi_g z y ν μ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem contDiff_psiA (A : Fin 4) : ContDiff ℝ ∞ (psiA hV z A) := by
  have h2 : ContDiff ℝ ∞ (fun y => SM.D.Fr.c A (z.ψ y)) :=
    (LinearMap.toContinuousLinearMap (SM.D.Fr.c A)).contDiff.comp z.ψ_smooth
  exact contDiff_iff_contDiffAt.2 fun y =>
    ContDiffAt.bilinApply hV.μS z.ψb_smooth.contDiffAt h2.contDiffAt

theorem contDiff_densD (ν : Fin 4) : ContDiff ℝ ∞ (fun y => densD hV z y ν) := by
  have h1 := contDiff_rho z
  have h2 := fun A => z.contDiff_e A ν
  have h3 := contDiff_psiA hV z
  rw [show (fun y => densD hV z y ν) = fun y =>
    -∑ A, (lorentzSign A * (rho z y * z.e y A ν)) • psiA hV z A y from
    funext fun y => densD_eq hV z y ν]
  fun_prop

/-- The current density of the theory data splits into its bosonic and Dirac parts. -/
theorem densJ_split (y : ST 3) (ν : Fin 4) :
    densJ SM z y ν = densJ (bosData SM hV) z y ν + densD hV z y ν := by
  unfold densJ densD
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← smul_add]
  congr 1
  show SM.Jcur _ _ _ _ _ _ β = (2 : ℝ) • hV.μ _ _ + JDf hV z y β
  rw [hV.J_eq]
  rfl

theorem contDiff_densJ_bos (ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => densJ (bosData SM hV) z y ν) := by
  have h1 := contDiff_rho z
  have h2 := z.contDiff_gi
  have hDH := contDiff_DHf z
  have hH := z.H_smooth
  have h3 : ∀ β, ContDiff ℝ ∞ (fun y => Jf (bosData SM hV) z y β) := fun β =>
    (contDiff_iff_contDiffAt.2 fun y => ContDiffAt.bilinApply hV.μ hH.contDiffAt
      ((contDiff_pi.1 hDH) β).contDiffAt).const_smul (2 : ℝ)
  show ContDiff ℝ ∞ (fun y => rho z y • ∑ β, z.gi y ν β • Jf (bosData SM hV) z y β)
  fun_prop

/-- **The divergence of the current splits**: `ϱD^νJ_ν = ϱD^νJ^{H}_ν + ϱD^νJ^D_ν`. -/
theorem divJ_split (x : ST 3) : divJ SM z x = divJ (bosData SM hV) z x + divD hV z x := by
  unfold divJ divD
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hf : (fun y => densJ SM z y ν) =
      fun y => densJ (bosData SM hV) z y ν + densD hV z y ν := funext fun y => densJ_split hV z y ν
  have hpd : pd (fun y => densJ SM z y ν) ν x =
      pd (fun y => densJ (bosData SM hV) z y ν) ν x + pd (fun y => densD hV z y ν) ν x := by
    rw [hf]
    unfold SobolevOpen.pd
    rw [fderiv_fun_add (((contDiff_densJ_bos hV z ν).differentiable (by simp)) x)
      (((contDiff_densD hV z ν).differentiable (by simp)) x)]
    rfl
  rw [hpd, densJ_split hV z x ν, lie_add]
  abel

end Field


/-! ### The divergence of the Dirac current -/

section Divergence

variable {SM : SMData (MatLie m) V S S'} (hV : VariationalDirac SM) (z : Tuple m V S S')

theorem line_psiA (x : ST 3) (A δ : Fin 4) :
    HasDerivAt (fun s : ℝ => psiA hV z A (x + s • ev δ))
      (hV.μS (pd z.ψb δ x) (SM.D.Fr.c A (z.ψ x)) +
        hV.μS (z.ψb x) (SM.D.Fr.c A (pd z.ψ δ x))) 0 := by
  have h1 := hasDerivAt_line0 (z.ψb_smooth.differentiable (by simp) x) δ
  have h2 := hasDerivAt_lin (SM.D.Fr.c A) (hasDerivAt_line0 (z.ψ_smooth.differentiable (by simp) x) δ)
  have h := hasDerivAt_bilin hV.μS h1 h2
  simp only [zero_smul, add_zero] at h
  exact h

/-- The coordinate derivative of the Dirac current density along its own index. -/
theorem pd_densD (x : ST 3) (ν : Fin 4) :
    pd (fun y => densD hV z y ν) ν x = -∑ A,
      ((lorentzSign A * (rho z x * z.e x A ν)) •
          (hV.μS (pd z.ψb ν x) (SM.D.Fr.c A (z.ψ x)) +
            hV.μS (z.ψb x) (SM.D.Fr.c A (pd z.ψ ν x))) +
        (lorentzSign A * (rho z x * (∑ k, chr (z.gi x) (z.dg x) k k ν) * z.e x A ν +
          rho z x * z.de x ν A ν)) • psiA hV z A x) := by
  have hf : (fun y => densD hV z y ν) =
      fun y => -∑ A, (lorentzSign A * (rho z y * z.e y A ν)) • psiA hV z A y :=
    funext fun y => densD_eq hV z y ν
  refine pd_eq_of_line ((contDiff_densD hV z ν).differentiable (by simp) x) ?_
  simp only [densD_eq]
  refine HasDerivAt.neg (HasDerivAt.fun_sum fun A _ => ?_)
  have hc : HasDerivAt (fun s : ℝ => lorentzSign A * (rho z (x + s • ev ν) * z.e (x + s • ev ν) A ν))
      (lorentzSign A * (rho z x * (∑ k, chr (z.gi x) (z.dg x) k k ν) * z.e x A ν +
        rho z x * z.de x ν A ν)) 0 := by
    have h := ((line_rho z x ν).mul (z.line_e x ν A ν)).const_mul (lorentzSign A)
    simp only [zero_smul, add_zero] at h
    exact h
  have h := hc.smul (line_psiA hV z x A ν)
  simp only [zero_smul, add_zero] at h
  exact h

/-- The gauge-covariant frame derivative `T_A = e_AΨ + ρ(A(e_A))Ψ` of a spinor. -/
def covT {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (x : ST 3) (ψ : S₀) (cψ : Fin 4 → S₀) (A : Fin 4) : S₀ :=
  ∑ ν, z.e x A ν • cψ ν + ∑ μ, z.e x A μ • D.ρ (z.A x μ) ψ

/-- The frame divergence `∇_μe_A{}^μ` of the adapted frame of the tuple. -/
def divE (x : ST 3) (A : Fin 4) : ℝ :=
  ∑ ν, (z.de x ν A ν + ∑ σ, chr (z.gi x) (z.dg x) ν ν σ * z.e x A σ)

theorem divE_eq_frame (x : ST 3) (A : Fin 4) :
    divE z x A = ∑ B, lorentzSign B * (z.FJ x).G B A B := by
  show _ = ∑ B, (z.FJ x).ε B * (z.FJ x).G B A B
  rw [← frame_div (z.FJ x) A]
  rfl

theorem sum_coef_divE (x : ST 3) (A : Fin 4) :
    ∑ ν, (rho z x * (∑ k, chr (z.gi x) (z.dg x) k k ν) * z.e x A ν + rho z x * z.de x ν A ν) =
      rho z x * divE z x A := by
  have h : ∑ ν, ∑ σ, chr (z.gi x) (z.dg x) ν ν σ * z.e x A σ =
      ∑ ν, (∑ k, chr (z.gi x) (z.dg x) k k ν) * z.e x A ν := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => by rw [Finset.sum_mul]
  unfold divE
  rw [Finset.sum_add_distrib (f := fun ν => z.de x ν A ν), h, mul_add, Finset.mul_sum,
    Finset.mul_sum, Finset.sum_add_distrib, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

end Divergence


section Divergence2

variable {SM : SMData (MatLie m) V S S'} (hV : VariationalDirac SM) (z : Tuple m V S S')

/-- The frame derivative `e_AΨ = Σ_ν e_A{}^ν ∂_νΨ`. -/
def frD {E : Type*} [AddCommGroup E] [Module ℝ E] (x : ST 3) (A : Fin 4) (c : Fin 4 → E) : E :=
  ∑ ν, z.e x A ν • c ν

/-- The frame gauge field `ρ(A(e_A)) = Σ_μ e_A{}^μ ρ(A_μ)`. -/
def rhoA {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀) (x : ST 3)
    (A : Fin 4) : Module.End ℝ S₀ :=
  ∑ μ, z.e x A μ • D.ρ (z.A x μ)

theorem sum_pd_densD (x : ST 3) :
    ∑ ν, pd (fun y => densD hV z y ν) ν x = -∑ A, lorentzSign A •
      ((rho z x * divE z x A) • psiA hV z A x +
        rho z x • (hV.μS (frD z x A fun ν => pd z.ψb ν x) (SM.D.Fr.c A (z.ψ x)) +
          hV.μS (z.ψb x) (SM.D.Fr.c A (frD z x A fun ν => pd z.ψ ν x)))) := by
  simp only [pd_densD]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_add_distrib, smul_add, add_comm]
  congr 1
  · rw [← Finset.sum_smul, ← sum_coef_divE, smul_smul, Finset.mul_sum]
  · unfold frD
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_add,
      Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib]

theorem sum_bracket_densD (x : ST 3) :
    ∑ ν, ⁅z.A x ν, densD hV z x ν⁆ = -∑ A, lorentzSign A • (rho z x •
      (hV.μS (rhoA z SM.Db x A (z.ψb x)) (SM.D.Fr.c A (z.ψ x)) +
        hV.μS (z.ψb x) (SM.D.Fr.c A (rhoA z SM.D x A (z.ψ x))))) := by
  simp only [densD_eq, lie_neg, lie_sum, lie_smul]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun A _ => ?_
  have hc : ∀ ν, SM.D.ρ (z.A x ν) (SM.D.Fr.c A (z.ψ x)) = SM.D.Fr.c A (SM.D.ρ (z.A x ν) (z.ψ x)) :=
    fun ν => by
      have := congrArg (fun F : Module.End ℝ S => F (z.ψ x)) (SM.D.comm (z.A x ν) A)
      simpa using this
  simp only [psiA, hV.μS_equiv, hc]
  unfold rhoA
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    smul_add, Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib]

end Divergence2


section Assembly

variable {SM : SMData (MatLie m) V S S'} (hV : VariationalDirac SM) (z : Tuple m V S S')

/-- **The spin-connection terms of the Dirac current divergence cancel against the frame
divergence**: `Σ_A ε_A (∇_μe_A{}^μ Ψ_A + μ_S(Ψ̄, [X_{G_A}, c_A]Ψ)) = 0` (Clifford multiplication is
parallel and the frame divergence is the frame trace of the connection). -/
theorem frame_cancel (x : ST 3) :
    ∑ A, lorentzSign A • (divE z x A • psiA hV z A x +
      (hV.μS (z.ψb x) ((spinPart SM.D.Fr ((z.FJ x).G A) * SM.D.Fr.c A) (z.ψ x)) -
        hV.μS (z.ψb x) ((SM.D.Fr.c A * spinPart SM.D.Fr ((z.FJ x).G A)) (z.ψ x)))) = 0 := by
  have hcomm : ∀ A, hV.μS (z.ψb x) ((spinPart SM.D.Fr ((z.FJ x).G A) * SM.D.Fr.c A) (z.ψ x)) -
      hV.μS (z.ψb x) ((SM.D.Fr.c A * spinPart SM.D.Fr ((z.FJ x).G A)) (z.ψ x)) =
      ∑ d, (lorentzSign d * (z.FJ x).G A A d) • psiA hV z d x := by
    intro A
    rw [← map_sub, ← LinearMap.sub_apply,
      comm_spinPart SM.D.Fr ((z.FJ x).G A) (fun c d => (z.FJ x).G_anti A c d) A]
    rw [eps_D_eq]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    rfl
  simp only [hcomm, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm (f := fun A d => (lorentzSign A * (lorentzSign d * (z.FJ x).G A A d)) •
    psiA hV z d x)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [← Finset.sum_smul, ← add_smul]
  have h1 : ∑ A, lorentzSign A * (lorentzSign d * (z.FJ x).G A A d) =
      -(lorentzSign d * divE z x d) := by
    rw [divE_eq_frame, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [(z.FJ x).G_anti A A d]
    ring
  rw [h1, add_neg_cancel, zero_smul]

/-- The actual spinor jet in expanded form: `X_A = e_AΨ + ρ(A(e_A))Ψ + X_{G_A}Ψ`. -/
theorem Xs_split {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (D : DiracData (MatLie m) V S₀) (x : ST 3) (ψ : S₀) (cψ : Fin 4 → S₀) (A : Fin 4) :
    (z.jet x).Xs D ψ cψ A =
      frD z x A cψ + rhoA z D x A ψ + spinPart D.Fr ((z.FJ x).G A) ψ := by
  rw [ActualJetBridge.Xs_eq]
  unfold frD rhoA
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  have e1 : (z.jet x).FJ.e = z.e x := rfl
  have e2 : (z.jet x).A = z.A x := rfl
  have e3 : (z.jet x).FJ.G A = (z.FJ x).G A := rfl
  rw [e1, e2, e3]
  show _ + spinPart D.Fr ((z.FJ x).G A) ψ + _ = _
  abel

/-- **The Clifford sums of the jets are the Dirac operators**:
`Σ_A ε_A (μ_S(X̄_A, c_AΨ) + μ_S(Ψ̄, c_AX_A)) = μ_S(𝒟̄Ψ̄, Ψ) + μ_S(Ψ̄, 𝒟Ψ)`. -/
theorem dirac_sum (x : ST 3) :
    ∑ A, lorentzSign A • (hV.μS ((z.jet x).Xs SM.Db (z.ψb x) (fun γ => pd z.ψb γ x) A)
        (SM.D.Fr.c A (z.ψ x)) +
      hV.μS (z.ψb x) (SM.D.Fr.c A ((z.jet x).Xs SM.D (z.ψ x) (fun γ => pd z.ψ γ x) A))) =
      hV.μS (dirac SM.Db.Fr ((z.jet x).LJ SM.Db).ω (z.ψb x)
          (ActualJetSpinor.dψf (z.jet x).FJ fun γ => pd z.ψb γ x)) (z.ψ x) +
        hV.μS (z.ψb x) (dirac SM.D.Fr ((z.jet x).LJ SM.D).ω (z.ψ x)
          (ActualJetSpinor.dψf (z.jet x).FJ fun γ => pd z.ψ γ x)) := by
  unfold dirac
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_add,
    Finset.sum_add_distrib]
  rw [eps_Db_eq, eps_D_eq]
  congr 1
  refine Finset.sum_congr rfl fun A _ => ?_
  congr 1
  rw [← hV.μS_c]
  rfl

end Assembly


section Assembly2

variable {SM : SMData (MatLie m) V S S'} (hV : VariationalDirac SM) (z : Tuple m V S S')

theorem per_frame (x : ST 3) (A : Fin 4) :
    lorentzSign A • ((rho z x * divE z x A) • psiA hV z A x +
        rho z x • (hV.μS (frD z x A fun ν => pd z.ψb ν x) (SM.D.Fr.c A (z.ψ x)) +
          hV.μS (z.ψb x) (SM.D.Fr.c A (frD z x A fun ν => pd z.ψ ν x)))) +
      lorentzSign A • (rho z x • (hV.μS (rhoA z SM.Db x A (z.ψb x)) (SM.D.Fr.c A (z.ψ x)) +
        hV.μS (z.ψb x) (SM.D.Fr.c A (rhoA z SM.D x A (z.ψ x))))) =
    rho z x • (lorentzSign A • (hV.μS ((z.jet x).Xs SM.Db (z.ψb x) (fun γ => pd z.ψb γ x) A)
        (SM.D.Fr.c A (z.ψ x)) +
      hV.μS (z.ψb x) (SM.D.Fr.c A ((z.jet x).Xs SM.D (z.ψ x) (fun γ => pd z.ψ γ x) A))) +
      lorentzSign A • (divE z x A • psiA hV z A x +
      (hV.μS (z.ψb x) ((spinPart SM.D.Fr ((z.FJ x).G A) * SM.D.Fr.c A) (z.ψ x)) -
        hV.μS (z.ψb x) ((SM.D.Fr.c A * spinPart SM.D.Fr ((z.FJ x).G A)) (z.ψ x))))) := by
  rw [Xs_split, Xs_split]
  simp only [map_add, LinearMap.add_apply, Module.End.mul_apply]
  rw [hV.μS_spin _ (fun c d => (z.FJ x).G_anti A c d)]
  unfold psiA
  module

/-- **The divergence of the Dirac current**: `ϱ D^νJ^D_ν = -ϱ(μ_S(𝒟̄Ψ̄, Ψ) + μ_S(Ψ̄, 𝒟Ψ))`. -/
theorem divD_eq (x : ST 3) :
    divD hV z x = -(rho z x • (hV.μS (dirac SM.Db.Fr ((z.jet x).LJ SM.Db).ω (z.ψb x)
          (ActualJetSpinor.dψf (z.jet x).FJ fun γ => pd z.ψb γ x)) (z.ψ x) +
        hV.μS (z.ψb x) (dirac SM.D.Fr ((z.jet x).LJ SM.D).ω (z.ψ x)
          (ActualJetSpinor.dψf (z.jet x).FJ fun γ => pd z.ψ γ x)))) := by
  unfold divD
  rw [Finset.sum_add_distrib, sum_pd_densD, sum_bracket_densD, ← neg_add,
    ← Finset.sum_add_distrib]
  congr 1
  simp only [per_frame, ← Finset.smul_sum, Finset.sum_add_distrib]
  rw [frame_cancel, add_zero, dirac_sum]

end Assembly2


/-! ### The current Noether identity with the Dirac current -/

section Noether

variable {SM : SMData (MatLie m) V S S'} (hV : VariationalDirac SM)

/-- **The Yukawa force balances the mass commutator of the Dirac current**:
`2μ(H, S_Y(Ψ̄, Ψ)) = μ_S(𝓜̄(H)Ψ̄, Ψ) + μ_S(Ψ̄, 𝓜(H)Ψ)` (both pair with `X ∈ 𝔤` to
`⟨Ψ̄, 𝓜_H[X·H]Ψ⟩`). -/
theorem yuk_mass (H : V) (φ : S') (x : S) :
    (2 : ℝ) • hV.μ H (hV.yuk φ x) =
      hV.μS (mass SM.Db.m0 SM.Db.L H φ) x + hV.μS φ (mass SM.D.m0 SM.D.L H x) := by
  refine sub_eq_zero.1 (hV.ipG_nondeg _ fun X => ?_)
  rw [map_sub, map_smul, hV.moment, smul_eq_mul, hV.yuk_dual, DiracPairing.ipG_μS_mass, sub_self]

/-- The Higgs residual of the bosonic part differs from that of the data by the Yukawa source. -/
theorem rH_bos (z : Tuple m V S S') (x : ST 3) :
    (bosF (bosData SM hV) z x).2.2 = (bosF SM z x).2.2 + hV.yuk (z.ψb x) (z.ψ x) := by
  show higgsRes _ _ _ _ _ _ _ (((2 * SM.lamH * (SM.ipV _ _ - SM.vH ^ 2)) • (z.jet x).H)) =
    higgsRes _ _ _ _ _ _ _ (SM.SH _ _ _ _ _) + _
  rw [hV.SH_eq]
  unfold higgsRes
  show _ = _ - (_ + hV.yuk (z.ψb x) (z.ψ x)) + hV.yuk (z.ψb x) (z.ψ x)
  abel

/-- The Dirac operator is the Dirac residual plus the mass term. -/
theorem dirac_eq_rD {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (D : DiracData (MatLie m) V S₀) (z : Tuple m V S S') (x : ST 3) (ψ : S₀)
    (cψ : Fin 4 → S₀) :
    dirac D.Fr ((z.jet x).LJ D).ω ψ (ActualJetSpinor.dψf (z.jet x).FJ cψ) =
      (z.jet x).rD D ψ cψ + mass D.m0 D.L (z.H x) ψ := by
  unfold ActualJet.rD resD
  show _ = _ - mass D.m0 D.L (z.H x) ψ + mass D.m0 D.L (z.H x) ψ
  rw [sub_add_cancel]

/-- **The current Noether identity with the Dirac current** (field level): for every smooth
tuple, `ϱ D^νJ_ν = ϱ(2μ(H, r_H) - μ_S(r̄_D, Ψ) - μ_S(Ψ̄, r_D))`. -/
theorem divJ_variationalDirac (z : Tuple m V S S') (x : ST 3) :
    divJ SM z x = rho z x • ((2 : ℝ) • hV.μ (z.H x) ((bosF SM z x).2.2) -
      hV.μS (dirF SM z x).2 (z.ψ x) - hV.μS (z.ψb x) (dirF SM z x).1) := by
  rw [divJ_split hV z x, divJ_variational z (bosVariational hV) x, rH_bos, divD_eq,
    dirac_eq_rD, dirac_eq_rD]
  have hy := yuk_mass hV (z.H x) (z.ψb x) (z.ψ x)
  show rho z x • ((2 : ℝ) • hV.μ (z.H x) ((bosF SM z x).2.2 + hV.yuk (z.ψb x) (z.ψ x))) +
    -(rho z x • (hV.μS ((z.jet x).rD SM.Db (z.ψb x) (fun γ => pd z.ψb γ x) +
        mass SM.Db.m0 SM.Db.L (z.H x) (z.ψb x)) (z.ψ x) +
      hV.μS (z.ψb x) ((z.jet x).rD SM.D (z.ψ x) (fun γ => pd z.ψ γ x) +
        mass SM.D.m0 SM.D.L (z.H x) (z.ψ x)))) = _
  rw [map_add, smul_add, hy]
  simp only [map_add, LinearMap.add_apply]
  show _ = rho z x • ((2 : ℝ) • hV.μ (z.H x) ((bosF SM z x).2.2) -
      hV.μS ((z.jet x).rD SM.Db (z.ψb x) (fun γ => pd z.ψb γ x)) (z.ψ x) -
      hV.μS (z.ψb x) ((z.jet x).rD SM.D (z.ψ x) (fun γ => pd z.ψ γ x)))
  module

/-- The residual coefficients of the Dirac current Noether identity:
`K(r_H, r_D, r̄_D) = 2μ(H, r_H) - μ_S(r̄_D, Ψ) - μ_S(Ψ̄, r_D)`. -/
def diracK (H : V) (ψ : S) (ψb : S') : (V × (S × S')) →ₗ[ℝ] MatLie m :=
  (2 : ℝ) • (hV.μ H).comp (LinearMap.fst ℝ V (S × S')) -
    (hV.μS.flip ψ).comp ((LinearMap.snd ℝ S S').comp (LinearMap.snd ℝ V (S × S'))) -
    (hV.μS ψb).comp ((LinearMap.fst ℝ S S').comp (LinearMap.snd ℝ V (S × S')))

/-- **Variational Einstein–Yang–Mills–Higgs–Dirac data satisfy the current Noether identity**
(`GenNoether.CurrentNoether`) **with the Dirac current and the Yukawa source**:
`ϱ D^νJ_ν = ϱ(2μ(H, r_H) - μ_S(r̄_D, Ψ) - μ_S(Ψ̄, r_D))`. -/
def currentNoether_of_variationalDirac : CurrentNoether SM where
  K := fun _ _ H _ ψ ψb => diracK hV H ψ ψb
  div_eq := fun z x => by
    rw [divJ_variationalDirac hV z x]
    rfl

end Noether


/-! ### A charged-spinor instance (non-vacuity) -/

section QuaternionModel

/-- The spinor space `ℍ × ℍ ≅ ℝ⁸` (the real Clifford module of `Cl_{1,3}`). -/
abbrev SQ := Quaternion ℝ × Quaternion ℝ

/-- The imaginary quaternion units. -/
def qU (i : Fin 3) : Quaternion ℝ :=
  ⟨0, if i = 0 then 1 else 0, if i = 1 then 1 else 0, if i = 2 then 1 else 0⟩

@[simp] theorem qU_re (i : Fin 3) : (qU i).re = 0 := rfl
@[simp] theorem qU_imI (i : Fin 3) : (qU i).imI = if i = 0 then 1 else 0 := rfl
@[simp] theorem qU_imJ (i : Fin 3) : (qU i).imJ = if i = 1 then 1 else 0 := rfl
@[simp] theorem qU_imK (i : Fin 3) : (qU i).imK = if i = 2 then 1 else 0 := rfl

/-- `c₀(x, y) = (y, x)`. -/
def swapQ : Module.End ℝ SQ where
  toFun p := (p.2, p.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem swapQ_apply (p : SQ) : swapQ p = (p.2, p.1) := rfl

/-- `c_i(x, y) = s(q_ix, -q_iy)`. -/
def diagQ (s : ℝ) (i : Fin 3) : Module.End ℝ SQ where
  toFun p := (s • (qU i * p.1), -(s • (qU i * p.2)))
  map_add' p p' := by
    refine Prod.ext ?_ ?_ <;> simp [mul_add, smul_add] <;> abel
  map_smul' c p := by
    refine Prod.ext ?_ ?_ <;> simp [mul_smul_comm, smul_comm s c]

@[simp] theorem diagQ_apply (s : ℝ) (i : Fin 3) (p : SQ) :
    diagQ s i p = (s • (qU i * p.1), -(s • (qU i * p.2))) := rfl

/-- The Clifford generators `c₀ = swap`, `c_i = s diag(q_i, -q_i)` (`s = ±1`). -/
def cQ (s : ℝ) : Fin 4 → Module.End ℝ SQ := ![swapQ, diagQ s 0, diagQ s 1, diagQ s 2]

theorem lorentzSign_zero : lorentzSign 0 = -1 := rfl
theorem lorentzSign_succ (i : Fin 3) : lorentzSign i.succ = 1 := by
  simp [lorentzSign, Fin.succ_ne_zero]

set_option maxHeartbeats 4000000 in
/-- **A Lorentzian Clifford frame on `ℍ × ℍ`** (`s = ±1`). -/
def frQ (s : ℝ) (hs : s ^ 2 = 1) : CliffordFrame (Fin 4) (Module.End ℝ SQ) where
  c := cQ s
  ε := lorentzSign
  sign_sq := ActualJetBridge.lorentzSign_sq
  anticomm := by
    intro a b
    refine LinearMap.ext fun x => ?_
    fin_cases a <;> fin_cases b <;> ext
    all_goals simp [cQ, lorentzSign, Module.End.mul_apply]
    all_goals ring_nf
    all_goals (try simp only [hs])
    all_goals (try ring_nf)
    all_goals (try rfl)

/-- The gauge action of `gl(1)` on spinors: `ρ(X)(x, y) = X₀₀ (x i, y i)` (right multiplication by
`i`, commuting with the Clifford generators). -/
def rightI : Module.End ℝ SQ where
  toFun p := (p.1 * qU 0, p.2 * qU 0)
  map_add' p p' := by refine Prod.ext ?_ ?_ <;> simp [add_mul]
  map_smul' c p := by refine Prod.ext ?_ ?_ <;> simp [smul_mul_assoc]

@[simp] theorem rightI_apply (p : SQ) : rightI p = (p.1 * qU 0, p.2 * qU 0) := rfl

def rhoQ : MatLie 1 →ₗ[ℝ] Module.End ℝ SQ where
  toFun X := X 0 0 • rightI
  map_add' X Y := by
    show (X + Y) 0 0 • rightI = X 0 0 • rightI + Y 0 0 • rightI
    rw [show (X + Y) 0 0 = X 0 0 + Y 0 0 from rfl, add_smul]
  map_smul' c X := by
    show (c • X) 0 0 • rightI = c • (X 0 0 • rightI)
    rw [show (c • X) 0 0 = c * X 0 0 from rfl, mul_smul]

theorem lie_one (X Y : MatLie 1) : ⁅X, Y⁆ = 0 := by
  rw [Ring.lie_def, sub_eq_zero]
  have h : ∀ (A B : Matrix (Fin 1) (Fin 1) ℝ), A * B = B * A := fun A B => by
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, mul_comm]
  exact h X Y

/-- The Yukawa map `𝓜_H[w] = w₀₀ · 1` (scalar Yukawa coupling of the real Higgs). -/
def LQ (s : ℝ) : MatLie 1 →ₗ[ℝ] Module.End ℝ SQ where
  toFun w := (s * w 0 0) • (1 : Module.End ℝ SQ)
  map_add' X Y := by
    show (s * (X + Y) 0 0) • (1 : Module.End ℝ SQ) = (s * X 0 0) • 1 + (s * Y 0 0) • 1
    rw [show (X + Y) 0 0 = X 0 0 + Y 0 0 from rfl, mul_add, add_smul]
  map_smul' c X := by
    show (s * (c • X) 0 0) • (1 : Module.End ℝ SQ) = c • ((s * X 0 0) • 1)
    rw [show (c • X) 0 0 = c * X 0 0 from rfl, smul_smul]
    ring_nf

set_option maxHeartbeats 4000000 in
/-- **A charged Dirac block on `ℍ × ℍ`** with gauge group `U(1) ⊂ GL(1)` and a scalar Yukawa
coupling (`s = 1`: spinors; `s = -1`: co-spinors, the transposed block). -/
def diracQ (s : ℝ) (hs : s ^ 2 = 1) : DiracData (MatLie 1) (MatLie 1) SQ where
  Fr := frQ s hs
  ρ := rhoQ
  ρ_lie X Y := by
    rw [lie_one, map_zero]
    refine LinearMap.ext fun x => ?_
    ext
    all_goals simp [rhoQ, Module.End.mul_apply]
    all_goals (try ring_nf)
    all_goals (try rfl)
  m0 := 0
  L := LQ s
  lorentz := ⟨lorentzSign_zero, lorentzSign_succ⟩
  comm X b := by
    refine LinearMap.ext fun x => ?_
    fin_cases b <;> ext
    all_goals simp [frQ, cQ, rhoQ, Module.End.mul_apply]
  mass_cl w c d := by
    simp only [mass, zero_add, LQ, LinearMap.coe_mk, AddHom.coe_mk, smul_mul_assoc, one_mul,
      mul_smul_comm, mul_one]
  mass_eq X w := by
    rw [lie_one, map_zero]
    simp only [mass, zero_add, LQ, LinearMap.coe_mk, AddHom.coe_mk, smul_mul_assoc, one_mul,
      mul_smul_comm, mul_one, sub_self]

end QuaternionModel


section QuaternionData

/-- The Euclidean pairing of quaternions. -/
def dotQ (a b : Quaternion ℝ) : ℝ := a.re * b.re + a.imI * b.imI + a.imJ * b.imJ + a.imK * b.imK

/-- The spinor pairing `⟨Ψ̄, Ψ⟩` on `ℍ × ℍ` (the Euclidean pairing). -/
def PQ : SQ →ₗ[ℝ] SQ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun φ x => dotQ φ.1 x.1 + dotQ φ.2 x.2)
    (fun φ φ' x => by simp only [dotQ, Prod.fst_add, Prod.snd_add, Quaternion.re_add,
      Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add]; ring)
    (fun c φ x => by simp only [dotQ, Prod.smul_fst, Prod.smul_snd, Quaternion.re_smul,
      Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul, smul_eq_mul]; ring)
    (fun φ x x' => by simp only [dotQ, Prod.fst_add, Prod.snd_add, Quaternion.re_add,
      Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add]; ring)
    (fun c φ x => by simp only [dotQ, Prod.smul_fst, Prod.smul_snd, Quaternion.re_smul,
      Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul, smul_eq_mul]; ring)

theorem PQ_apply (φ x : SQ) : PQ φ x = dotQ φ.1 x.1 + dotQ φ.2 x.2 := rfl

/-- A scalar `1 × 1` matrix. -/
def sc (r : ℝ) : MatLie 1 := fun _ _ => r

theorem sc_apply (r : ℝ) (i j : Fin 1) : sc r i j = r := rfl

theorem sc_add (r r' : ℝ) : sc (r + r') = sc r + sc r' := rfl
theorem sc_smul (c r : ℝ) : sc (c * r) = c • sc r := rfl

/-- The spinor moment map `μ_S(φ, x) = ⟨φ, x i⟩` (as a `1 × 1` matrix). -/
def μSQ : SQ →ₗ[ℝ] SQ →ₗ[ℝ] MatLie 1 :=
  LinearMap.mk₂ ℝ (fun φ x => sc (PQ φ (rightI x)))
    (fun φ φ' x => by rw [map_add, LinearMap.add_apply, sc_add])
    (fun c φ x => by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, sc_smul])
    (fun φ x x' => by rw [map_add, map_add, sc_add])
    (fun c φ x => by rw [map_smul, map_smul, smul_eq_mul, sc_smul])

/-- The Yukawa source `S_Y(φ, x) = ½⟨φ, x⟩` (as a `1 × 1` matrix). -/
def yukQ : SQ →ₗ[ℝ] SQ →ₗ[ℝ] MatLie 1 :=
  LinearMap.mk₂ ℝ (fun φ x => sc ((1 / 2 : ℝ) * PQ φ x))
    (fun φ φ' x => by rw [map_add, LinearMap.add_apply, mul_add, sc_add])
    (fun c φ x => by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_left_comm, sc_smul])
    (fun φ x x' => by rw [map_add, mul_add, sc_add])
    (fun c φ x => by rw [map_smul, smul_eq_mul, mul_left_comm, sc_smul])

theorem traceForm_one (X Y : MatLie 1) : traceForm 1 X Y = X 0 0 * Y 0 0 := by
  rw [traceForm_apply, Matrix.trace_fin_one, Matrix.mul_apply, Fin.sum_univ_one]
  rfl

/-- **Charged Einstein–Yang–Mills–Higgs–Dirac theory data on `ℍ × ℍ`**: gauge algebra `gl(1)`
acting on the spinors by right multiplication by `i` (a `U(1)` charge), real Higgs with scalar
Yukawa coupling, the transposed co-spinor block, the Dirac current and the Yukawa source. -/
def quatSM : SMData (MatLie 1) (MatLie 1) SQ SQ where
  Λ := 0
  κ := 1
  D := diracQ 1 (by norm_num)
  Db := diracQ (-1) (by norm_num)
  Jcur := fun g gi H DH ψ ψb ν =>
    (2 : ℝ) • (0 : MatLie 1 →ₗ[ℝ] MatLie 1 →ₗ[ℝ] MatLie 1) H (DH ν) +
      diracCur μSQ (diracQ 1 (by norm_num)).Fr g gi ψ ψb ν
  SH := fun _ _ H ψ ψb => (2 * 0 * (traceForm 1 H H - 0 ^ 2)) • H + yukQ ψb ψ
  ipG := traceForm 1
  ipV := traceForm 1
  lamH := 0
  vH := 0
  TD := ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

theorem dotQ_mulLeft (i : Fin 3) (a b : Quaternion ℝ) :
    dotQ (qU i * a) b = -dotQ a (qU i * b) := by
  fin_cases i <;> simp [dotQ] <;> ring

theorem dotQ_mulRight (a b : Quaternion ℝ) : dotQ (a * qU 0) b = -dotQ a (b * qU 0) := by
  simp [dotQ]; ring

theorem dotQ_mulRight2 (a b : Quaternion ℝ) :
    dotQ (a * qU 0) (b * qU 0) + dotQ a (b * qU 0 * qU 0) = 0 := by
  simp [dotQ]; ring

/-- **The quaternionic data are variational Einstein–Yang–Mills–Higgs–Dirac data.** -/
def quatVariationalDirac : VariationalDirac quatSM where
  P := PQ
  c_tr := by
    intro A φ x
    fin_cases A
    · show PQ (swapQ φ) x = PQ φ (swapQ x)
      simp only [PQ_apply, swapQ_apply, dotQ]; ring
    all_goals
      show PQ (diagQ (-1) _ φ) x = PQ φ (diagQ 1 _ x)
      simp only [PQ_apply, diagQ_apply]
      simp only [dotQ, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
        Quaternion.imK_smul, Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg,
        Quaternion.imK_neg, smul_eq_mul, Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul, qU_re, qU_imI, qU_imJ, qU_imK]
      simp
      ring
  ρ_tr := by
    intro X φ x
    show PQ (X 0 0 • rightI φ) x = -PQ φ (X 0 0 • rightI x)
    rw [map_smul, map_smul, LinearMap.smul_apply, PQ_apply, PQ_apply, rightI_apply, rightI_apply,
      dotQ_mulRight, dotQ_mulRight, smul_eq_mul, smul_eq_mul]
    ring
  m0_tr := by intro φ x; show PQ 0 x = -PQ φ 0; simp
  L_tr := by
    intro w φ x
    show PQ ((-1 * w 0 0) • (1 : Module.End ℝ SQ) φ) x = -PQ φ ((1 * w 0 0) • (1 : Module.End ℝ SQ) x)
    simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  ipG_nondeg := by
    intro Y h
    have h1 := h (sc 1)
    rw [show quatSM.ipG = traceForm 1 from rfl, traceForm_one, sc_apply, one_mul] at h1
    funext i j
    fin_cases i; fin_cases j
    exact h1
  μS := μSQ
  μS_dual := by
    intro X φ x
    show traceForm 1 X (μSQ φ x) = PQ φ (X 0 0 • rightI x)
    rw [traceForm_one, map_smul, smul_eq_mul]
    rfl
  μS_equiv := by
    intro X φ x
    rw [lie_one]
    show (0 : MatLie 1) = μSQ (X 0 0 • rightI φ) x + μSQ φ (X 0 0 • rightI x)
    rw [map_smul, map_smul, LinearMap.smul_apply, ← smul_add]
    have : μSQ (rightI φ) x + μSQ φ (rightI x) = 0 := by
      show sc (PQ (rightI φ) (rightI x)) + sc (PQ φ (rightI (rightI x))) = 0
      rw [← sc_add]
      simp only [PQ_apply, rightI_apply]
      have h1 := dotQ_mulRight2 φ.1 x.1
      have h2 := dotQ_mulRight2 φ.2 x.2
      rw [show dotQ (φ.1 * qU 0) (x.1 * qU 0) + dotQ (φ.2 * qU 0) (x.2 * qU 0) +
        (dotQ φ.1 (x.1 * qU 0 * qU 0) + dotQ φ.2 (x.2 * qU 0 * qU 0)) = 0 by linarith]
      rfl
    rw [this, smul_zero]
  μ := 0
  moment := by
    intro X u w
    rw [lie_one]
    show traceForm 1 X 0 = traceForm 1 0 w
    simp
  alt := fun _ => rfl
  equiv := by intro X u w; simp
  yuk := yukQ
  yuk_dual := by
    intro η φ x
    show 2 * traceForm 1 η (sc ((1 / 2 : ℝ) * PQ φ x)) = PQ φ ((1 * η 0 0) • (1 : Module.End ℝ SQ) x)
    rw [traceForm_one, sc_apply, map_smul, smul_eq_mul, Module.End.one_apply]
    ring
  J_eq := fun _ _ _ _ _ _ _ => rfl
  SH_eq := fun _ _ _ _ _ => rfl

/-- **Non-vacuity: the current Noether identity with the Dirac current holds for the charged
quaternionic data**, whose spinor space is nonzero and whose spinor moment map is nonzero
(`μ_S(Ψ̄, c₀Ψ) ≠ 0` for `Ψ = (1, 0)`, `Ψ̄ = (0, i)`). -/
example : Nonempty (CurrentNoether quatSM) ∧ Nontrivial SQ ∧
    quatVariationalDirac.μS ((0 : Quaternion ℝ), qU 0) (quatSM.D.Fr.c 0 ((1 : Quaternion ℝ), 0)) ≠ 0 :=
  by
  refine ⟨⟨currentNoether_of_variationalDirac quatVariationalDirac⟩, inferInstance, ?_⟩
  intro h
  have h1 := congrFun (congrFun h 0) 0
  change PQ ((0 : Quaternion ℝ), qU 0) (rightI (swapQ ((1 : Quaternion ℝ), 0))) = 0 at h1
  simp [PQ_apply, dotQ] at h1
  change (0 : ℝ) * 0 + 0 * 0 + 0 * 0 + 0 * 0 + 1 = 0 at h1
  norm_num at h1

end QuaternionData

end RenewalGeometry.GenDiracCur
