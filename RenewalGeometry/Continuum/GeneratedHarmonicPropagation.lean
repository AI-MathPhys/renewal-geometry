/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedStressNoether
import RenewalGeometry.Gravity.SubsidiarySourceJet
import RenewalGeometry.Gravity.MetricJetChainRule

/-!
# Propagation of the harmonic constraint along the actual-jet symmetric system

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`) and `prop:subsidiary` (`eq:subsidiary`): along a smooth tuple whose
actual-jet state solves the independent symmetric system `eq:generated-extension`, the metric
`p`-row is the reduced Einstein equation `Ĝ + Λg = κT` (once the Dirac residuals vanish, which the
symmetric system forces); its covariant divergence — contracted Bianchi identity and the stress
Noether identity `GenStress.StressNoether` — is the subsidiary wave system
`□c_ν + Ric_ν{}^μc_μ = -2κ∇^μT_{μν} = 0` for the harmonic gauge covector `c = g·C(g)` once the
Yang–Mills residual vanishes (Gauss propagation, `GenGauss.gauss_propagation`).  A first-order
symmetric reduction of the wave operator in the adapted frame and the `L²` energy estimate give
`c ≡ 0` from `c = ∂_tc = 0` on the initial slice.

## Generic results (no renewal notions)

* `cplxPi`, `cM` — complexification of real vectors and real coefficient matrices;
* **`sym_unique`** — uniqueness for linear first-order systems `Σ_μ A^μ∂_μW = BW` with real
  symmetric `C¹` periodic coefficients and `A⁰ = a₀·1`, `a₀ ≥ κ > 0`, on `[t₀, t₁] × 𝕋^d`
  (`SymHypEnergy.l2_energy_estimate`);
* **`wave_unique`** — uniqueness for linear second-order systems with a Lorentzian principal part
  `g^{αβ}∂_α∂_βu = O(|u| + |∂u|)` on `[t₀, t₁] × 𝕋³`, given a `C¹` adapted frame
  (`e_0 = N⁻¹(∂_t - βʲ∂_j)`, `e_a` spatial, `g^{-1} = -e_0⊗e_0 + Σ_a e_a⊗e_a`) and a continuous
  coframe: the frame components `(u, e_0u, e_au)` satisfy the symmetric system with
  `A^μ = e_0{}^μ·1 - Σ_a e_a{}^μ(E_{1,a+1} + E_{a+1,1})`.

## The Einstein–Standard-Model application

* `jet3` — the metric 3-jet of a smooth tuple; `jet3_valid`, `pathDeriv_jet3` (the formal jets are
  the actual derivatives along coordinate lines); `cF` — the lower-index gauge covector field;
* `errF_p_gen` — the metric row of the residual forcing when the Dirac residuals vanish to first
  order: `2N(𝓔^{tr} - ∇_{(μ}C_{ν)})`; **`reduced_einstein_of_symEqAt`** — the reduced Einstein
  equation `Ĝ + Λg - κT = 0` at every point where the symmetric system holds;
* **`subsidiary_of_symEqAt`** — `□c + Ric·c = -2κ∇^μT_{μν}` on the slab;
* **`harmonic_propagation`** — for theory data with the current and stress Noether identities,
  if the actual-jet state of a smooth tuple solves the symmetric system on `(a, b) × 𝕋³` and the
  Gauss constraint, `C` and `∂_tC` vanish at `t₀`, then `C ≡ 0` on `[t₀, t₁] × 𝕋³` (`t₁ < b`);
* **`physical_of_constraints`** — such a tuple is a physical solution on `(t₀, b) × 𝕋³`.

Regularity: the tuple is `C^∞` (`ActualJetBridge.Tuple`); the argument uses third derivatives of
the metric.  `Σ = 𝕋³` (disclosed).
-/

open MeasureTheory Filter Topology Set Finset
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.GenHarmonic

open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  JetCurve GenConstraint GenNoether GenGauss GenStress ActualJetCompleteForcing ActualJetRecon

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Uniqueness for linear symmetric systems with real coefficients -/

section SymUnique

variable {d : ℕ} {N : Type*} [Fintype N] [DecidableEq N]

/-- Complexification of real vectors. -/
def cplxPi : (N → ℝ) →L[ℝ] (N → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

theorem cplxPi_apply (v : N → ℝ) (i : N) : cplxPi v i = (v i : ℂ) := rfl

theorem norm_cplxPi (v : N → ℝ) : ‖cplxPi v‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · rw [cplxPi_apply, Complex.norm_real]
    exact norm_le_pi_norm v i
  · have := norm_le_pi_norm (cplxPi v) i
    rw [cplxPi_apply, Complex.norm_real] at this
    exact this

theorem cplxPi_eq_zero {v : N → ℝ} (h : cplxPi v = 0) : v = 0 := by
  have := norm_cplxPi v
  rw [h, norm_zero] at this
  exact norm_eq_zero.1 this.symm

/-- Complexification of real matrices. -/
def cM : (N → N → ℝ) →L[ℝ] (N → N → ℂ) :=
  ContinuousLinearMap.pi fun i => cplxPi.comp (ContinuousLinearMap.proj i)

theorem cM_apply (c : N → N → ℝ) (i k : N) : cM c i k = (c i k : ℂ) := rfl

theorem mv_cM (c : N → N → ℝ) (v : N → ℝ) :
    mv (cM c) (cplxPi v) = cplxPi (fun i => ∑ k, c i k * v k) := by
  funext i
  simp only [mv, cM_apply, cplxPi_apply]
  push_cast
  rfl

/-- The partial derivative of a field composed with a continuous linear map. -/
theorem pd_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) {W : ST d → E} {x : ST d} (hW : DifferentiableAt ℝ W x)
    (μ : Fin (d + 1)) : pd (fun y => L (W y)) μ x = L (pd W μ x) := by
  unfold SobolevOpen.pd
  have h : HasFDerivAt (fun y => L (W y)) (L.comp (fderiv ℝ W x)) x :=
    L.hasFDerivAt.comp x hW.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- **Uniqueness for linear symmetric hyperbolic systems with real coefficients** on
`[t₀, t₁] × 𝕋^d`: if `W` is `C¹` on `(a, b) × ℝ^d` and spatially periodic, the coefficient
matrices `c^μ` are real symmetric, `C¹` and periodic with `c⁰ = a₀·1`, `a₀ ≥ κ > 0` on the slab,
`‖Σ_μ c^μ∂_μW‖ ≤ K‖W‖` on the slab, and `W(t₀) = 0`, then `W = 0` on the slab
(`SymHypEnergy.l2_energy_estimate` for the complexified system). -/
theorem sym_unique {W : ST d → N → ℝ} {c : Fin (d + 1) → ST d → N → N → ℝ} {a0 : ST d → ℝ}
    {a t₀ t₁ b : ℝ} (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b)
    (hW : ContDiffOn ℝ 1 W (openSlab a b)) (hWp : IsSPeriodic W)
    (hc : ∀ μ, ContDiffOn ℝ 1 (c μ) (openSlab a b)) (hcp : ∀ μ, IsSPeriodic (c μ))
    (hsym : ∀ μ x i k, c μ x i k = c μ x k i)
    (h0 : ∀ x i k, c 0 x i k = if i = k then a0 x else 0)
    {κ : ℝ} (hκ : 0 < κ) (ha0 : ∀ x ∈ slab t₀ t₁, κ ≤ a0 x)
    {K : ℝ} (hK : 0 ≤ K)
    (heq : ∀ x ∈ slab t₀ t₁, ‖(fun i => ∑ μ, ∑ k, c μ x i k * pd W μ x k)‖ ≤ K * ‖W x‖)
    (hinit : ∀ y : Fin d → ℝ, W (Fin.cons t₀ y) = 0) : ∀ x ∈ slab t₀ t₁, W x = 0 := by
  set w : ST d → N → ℂ := fun x => cplxPi (W x) with hw
  set A : Fin (d + 1) → ST d → N → N → ℂ := fun μ x => cM (c μ x) with hA
  have hws : ContDiffOn ℝ 1 w (openSlab a b) := (cplxPi (N := N)).contDiff.comp_contDiffOn hW
  have hwp : IsSPeriodic w := fun k x => by simp only [hw, hWp k x]
  have hAs : ∀ μ, ContDiffOn ℝ 1 (A μ) (openSlab a b) := fun μ =>
    (cM (N := N)).contDiff.comp_contDiffOn (hc μ)
  have hAp : ∀ μ, IsSPeriodic (A μ) := fun μ k x => by simp only [hA, hcp μ k x]
  have hL : ∀ μ, ∃ L : ℝ≥0, LipschitzOnWith L (A μ) (slab t₀ t₁) := fun μ =>
    KatoGalerkin.exists_lipschitzOnWith_slab (hAs μ) (hAp μ) ha hb
  choose L hL using hL
  have hB : ∀ μ, ∃ C, ∀ x ∈ slab t₀ t₁, ‖A μ x‖ ≤ C := fun μ =>
    KatoGalerkin.exists_bound_slab (hAs μ).continuousOn (hAp μ) ha hb
  choose C hC using hB
  have hsymh : SymHyp A w a t₀ t₁ b (∑ μ, L μ) (∑ μ, |C μ|) := by
    refine ⟨ha, h01, hb, hws, hwp, hAp, fun μ x i k => ?_, fun μ => ?_, fun μ x hx => ?_⟩
    · simp only [hA, cM_apply, hsym μ x k i, Complex.star_def, Complex.conj_ofReal]
    · exact (hL μ).weaken (Finset.single_le_sum (f := L) (fun i _ => bot_le) (Finset.mem_univ μ))
    · refine (hC μ x hx).trans ((le_abs_self _).trans ?_)
      exact Finset.single_le_sum (f := fun μ => |C μ|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ μ)
  have hpos : ∀ x ∈ slab t₀ t₁, ∀ ξ : N → ℂ, κ * ∑ i, ‖ξ i‖ ^ 2 ≤ ip ξ (mv (A 0 x) ξ) := by
    intro x hx ξ
    have hmv : mv (A 0 x) ξ = a0 x • ξ := by
      funext i
      simp only [mv, hA, cM_apply, h0, Pi.smul_apply, Complex.real_smul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    rw [hmv, ip_smul_right, ip_self_eq]
    exact mul_le_mul_of_nonneg_right (ha0 x hx) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hprinc : ∀ x ∈ slab t₀ t₁, ‖SymHypEnergy.princ A w x‖ ≤ (fun _ => (0 : ℝ)) x +
      K * ‖w x‖ := by
    intro x hx
    have hd : DifferentiableAt ℝ W x :=
      (hW.differentiableOn one_ne_zero x (slab_subset_openSlab ha hb hx)).differentiableAt
        ((isOpen_openSlab a b).mem_nhds (slab_subset_openSlab ha hb hx))
    have e : SymHypEnergy.princ A w x = cplxPi (fun i => ∑ μ, ∑ k, c μ x i k * pd W μ x k) := by
      unfold SymHypEnergy.princ
      have : ∀ μ, pd w μ x = cplxPi (pd W μ x) := fun μ => pd_clm cplxPi hd μ
      simp only [this, hA, mv_cM]
      rw [← map_sum]
      congr 1
      funext i
      simp [Finset.sum_apply]
    rw [e, norm_cplxPi, zero_add, hw, norm_cplxPi]
    exact heq x hx
  have hest := l2_energy_estimate hsymh hκ hK hpos continuousOn_const hprinc
  have hl0 : l2sq w t₀ = 0 := by
    unfold l2sq
    simp [hw, hinit]
  intro x hx
  have ht : x 0 ∈ Icc t₀ t₁ := hx
  have hb' := hest (x 0) ht
  rw [hl0] at hb'
  simp only [mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    MeasureTheory.integral_zero, intervalIntegral.integral_zero] at hb'
  have hnn : 0 ≤ l2sq w (x 0) := setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _
  have hzero : l2sq w (x 0) = 0 := le_antisymm (by nlinarith [hb']) hnn
  have hcont : Continuous fun y : Fin d → ℝ => w (Fin.cons (x 0) y) := hsymh.w_slice_cont ht
  have hcube := SymHypUniqueness.eq_zero_on_cube_of_integral_eq_zero hcont hzero
  have hper : IsZPeriodic fun y : Fin d → ℝ => w (Fin.cons (x 0) y) := hwp.slice (x 0)
  have hfr : (fun i => Int.fract (Fin.tail x i)) ∈ Icc (0 : Fin d → ℝ) 1 :=
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  have := hcube _ hfr
  rw [hper.apply_fract (Fin.tail x), Fin.cons_self_tail] at this
  exact cplxPi_eq_zero this

end SymUnique

/-! ### The first-order frame reduction of a wave operator (jet algebra) -/

section FrameRows

/-- Frame components `e_A(u) = Σ_β e_A{}^β∂_βu`. -/
def fc (e : Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ) (A : Fin 4) : ℝ := ∑ β, e A β * du β

/-- Their derivative jets `∂_μ(e_A(u)) = Σ_β(∂_μe_A{}^β ∂_βu + e_A{}^β∂_μ∂_βu)`. -/
def dfc (e : Fin 4 → Fin 4 → ℝ) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ)
    (ddu : Fin 4 → Fin 4 → ℝ) (μ A : Fin 4) : ℝ :=
  ∑ β, (de μ A β * du β + e A β * ddu μ β)

/-- **The `P`-row** `e_0(e_0u) - Σ_a e_a(e_au) = -g^{μβ}∂_μ∂_βu + (lower order)` for an adapted
frame `g^{-1} = -e_0⊗e_0 + Σ_a e_a⊗e_a`. -/
theorem rowP (gi e : Fin 4 → Fin 4 → ℝ)
    (hadapt : ∀ μ ν, gi μ ν = -(e 0 μ * e 0 ν) + ∑ a : Fin 3, e a.succ μ * e a.succ ν)
    (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ) (ddu : Fin 4 → Fin 4 → ℝ) :
    ∑ μ, e 0 μ * dfc e de du ddu μ 0 - ∑ a : Fin 3, ∑ μ, e a.succ μ * dfc e de du ddu μ a.succ =
      -(∑ μ, ∑ β, gi μ β * ddu μ β) + ∑ β, (∑ μ, e 0 μ * de μ 0 β -
        ∑ a : Fin 3, ∑ μ, e a.succ μ * de μ a.succ β) * du β := by
  simp only [dfc, hadapt, mul_add, Finset.mul_sum, add_mul, neg_mul, Finset.sum_mul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_mul, Finset.sum_sub_distrib]
  have h1 : ∑ μ, ∑ β, e 0 μ * (de μ 0 β * du β) = ∑ β, ∑ μ, e 0 μ * de μ 0 β * du β := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun μ _ => by ring
  have h2 : ∀ a : Fin 3, ∑ μ, ∑ β, e a.succ μ * (de μ a.succ β * du β) =
      ∑ β, ∑ μ, e a.succ μ * de μ a.succ β * du β := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun μ _ => by ring
  have h3 : ∑ μ, ∑ β, e 0 μ * (e 0 β * ddu μ β) = ∑ μ, ∑ β, e 0 μ * e 0 β * ddu μ β :=
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun β _ => by ring
  have h4 : ∀ a : Fin 3, ∑ μ, ∑ β, e a.succ μ * (e a.succ β * ddu μ β) =
      ∑ μ, ∑ β, e a.succ μ * e a.succ β * ddu μ β := fun a =>
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun β _ => by ring
  have h5 : ∑ μ, ∑ β, ∑ a : Fin 3, e a.succ μ * e a.succ β * ddu μ β =
      ∑ a : Fin 3, ∑ μ, ∑ β, e a.succ μ * e a.succ β * ddu μ β := by
    rw [Finset.sum_congr rfl fun μ _ => Finset.sum_comm, Finset.sum_comm]
  simp only [h1, h2, h3, h4]
  rw [h5]
  have h6 : ∑ a : Fin 3, ∑ β, ∑ μ, e a.succ μ * de μ a.succ β * du β =
      ∑ β, ∑ a : Fin 3, ∑ μ, e a.succ μ * de μ a.succ β * du β := Finset.sum_comm
  rw [h6]
  ring

/-- **The `Q`-rows** `e_0(e_au) - e_a(e_0u) = [e_0, e_a](u)`: no second derivatives remain
(symmetry of `∂∂u`). -/
theorem rowQ (e : Fin 4 → Fin 4 → ℝ) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ)
    (ddu : Fin 4 → Fin 4 → ℝ) (hs : ∀ μ β, ddu μ β = ddu β μ) (a : Fin 3) :
    ∑ μ, e 0 μ * dfc e de du ddu μ a.succ - ∑ μ, e a.succ μ * dfc e de du ddu μ 0 =
      ∑ β, (∑ μ, (e 0 μ * de μ a.succ β - e a.succ μ * de μ 0 β)) * du β := by
  simp only [dfc, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have hs2 : ∑ μ, ∑ β, e 0 μ * (e a.succ β * ddu μ β) =
      ∑ μ, ∑ β, e a.succ μ * (e 0 β * ddu μ β) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun μ _ => by rw [hs]; ring
  rw [hs2]
  have h1 : ∑ μ, ∑ β, e 0 μ * (de μ a.succ β * du β) - ∑ μ, ∑ β, e a.succ μ * (de μ 0 β * du β) =
      ∑ β, (∑ μ, (e 0 μ * de μ a.succ β - e a.succ μ * de μ 0 β)) * du β := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun μ β => e a.succ μ * (de μ 0 β * du β)),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun μ _ => by ring
  linear_combination h1

end FrameRows

/-! ### Slab-local calculus -/

section LocalCalc

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem diffAt_of_contDiffOn {F : ST d → E} {U : Set (ST d)} (hU : IsOpen U)
    {n : WithTop ℕ∞} (hF : ContDiffOn ℝ n F U) (hn : n ≠ 0) {x : ST d} (hx : x ∈ U) :
    DifferentiableAt ℝ F x :=
  (hF.differentiableOn hn x hx).differentiableAt (hU.mem_nhds hx)

/-- Partial derivatives of a `C^{n+1}` field on an open set are `C^n` there. -/
theorem contDiffOn_pd {F : ST d → E} {U : Set (ST d)} (hU : IsOpen U) {n : ℕ}
    (hF : ContDiffOn ℝ (n + 1) F U) (μ : Fin (d + 1)) : ContDiffOn ℝ n (pd F μ) U := by
  unfold SobolevOpen.pd
  exact (hF.fderiv_of_isOpen hU (by norm_cast)).clm_apply contDiffOn_const

/-- Symmetry of second partial derivatives of a `C²` field at a point of an open set. -/
theorem pd_pd_symm_at {F : ST d → E} {U : Set (ST d)} (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U)
    {x : ST d} (hx : x ∈ U) (μ ν : Fin (d + 1)) : pd (pd F μ) ν x = pd (pd F ν) μ x := by
  have hF2 : ContDiffAt ℝ 2 F x := hF.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsymm := hF2.isSymmSndFDerivAt (by simp)
  show fderiv ℝ (fun y => fderiv ℝ F y (Pi.single μ 1)) x (Pi.single ν 1) =
    fderiv ℝ (fun y => fderiv ℝ F y (Pi.single ν 1)) x (Pi.single μ 1)
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd
    (differentiableAt_const _)]
  simp
  exact hsymm _ _

end LocalCalc

/-! ### The principal block of the frame reduction -/

section Block

/-- **The principal block** of the frame reduction of a wave operator, indices `0` (`u`),
`1` (`e_0u`), `a+2` (`e_{a+1}u`): `A^μ = e_0{}^μ·1 - Σ_a e_{a+1}{}^μ(E_{1,a+2} + E_{a+2,1})`. -/
def blk (E : Fin 4 → Fin 4 → ℝ) (μ : Fin 4) (r r' : Fin 5) : ℝ :=
  (if r = r' then E 0 μ else 0) -
    ∑ a : Fin 3, (if (r = 1 ∧ r' = a.succ.succ) ∨ (r = a.succ.succ ∧ r' = 1) then E a.succ μ else 0)

theorem blk_symm (E : Fin 4 → Fin 4 → ℝ) (μ : Fin 4) (r r' : Fin 5) :
    blk E μ r r' = blk E μ r' r := by
  unfold blk
  congr 1
  · by_cases h : r = r'
    · simp [h]
    · simp [h, Ne.symm h]
  · refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    exact propext ⟨fun h => h.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩),
      fun h => h.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)⟩

theorem blk_zero_time (E : Fin 4 → Fin 4 → ℝ) (hE : ∀ a : Fin 3, E a.succ 0 = 0) (r r' : Fin 5) :
    blk E 0 r r' = if r = r' then E 0 0 else 0 := by
  unfold blk
  simp [hE]

theorem blk_row0 (E : Fin 4 → Fin 4 → ℝ) (μ : Fin 4) (v : Fin 5 → ℝ) :
    ∑ r', blk E μ 0 r' * v r' = E 0 μ * v 0 := by
  simp [blk, Fin.sum_univ_five, Fin.sum_univ_three]

theorem blk_row1 (E : Fin 4 → Fin 4 → ℝ) (μ : Fin 4) (v : Fin 5 → ℝ) :
    ∑ r', blk E μ 1 r' * v r' = E 0 μ * v 1 - ∑ a : Fin 3, E a.succ μ * v a.succ.succ := by
  simp [blk, Fin.sum_univ_five, Fin.sum_univ_three]
  ring

theorem blk_rowQ (E : Fin 4 → Fin 4 → ℝ) (μ : Fin 4) (v : Fin 5 → ℝ) (a : Fin 3) :
    ∑ r', blk E μ a.succ.succ r' * v r' = E 0 μ * v a.succ.succ - E a.succ μ * v 1 := by
  fin_cases a <;> simp [blk, Fin.sum_univ_five, Fin.sum_univ_three] <;> ring

end Block

/-! ### Uniqueness for wave systems with a Lorentzian principal part -/

section WaveUnique

/-- `|Σ_i c_i v_i| ≤ (Σ_i |c_i|) B` when `|v_i| ≤ B`. -/
theorem abs_sum_mul_le {ι : Type*} [Fintype ι] (c v : ι → ℝ) {B : ℝ} (hv : ∀ i, |v i| ≤ B) :
    |∑ i, c i * v i| ≤ (∑ i, |c i|) * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)

/-- The frame-reduction state `(u, e_0u, e_1u, e_2u, e_3u)` of a field. -/
def frameState {k : ℕ} (u : ST 3 → Fin k → ℝ) (e : ST 3 → Fin 4 → Fin 4 → ℝ) (x : ST 3) :
    Fin k × Fin 5 → ℝ :=
  fun p => Fin.cases (u x p.1) (fun B => fc (e x) (fun β => pd u β x p.1) B) p.2

/-- The coefficients of the frame reduction, block diagonal in the components. -/
def frameCoeff {k : ℕ} (e : ST 3 → Fin 4 → Fin 4 → ℝ) (μ : Fin 4) (x : ST 3) :
    Fin k × Fin 5 → Fin k × Fin 5 → ℝ :=
  fun p p' => if p.1 = p'.1 then blk (e x) μ p.2 p'.2 else 0

/-- **Uniqueness for linear wave systems with a Lorentzian principal part** on `[t₀, t₁] × 𝕋³`
(generic; the first-order frame reduction of `prop:subsidiary`): let `u` be `C²` on
`(a, b) × ℝ³` and periodic, `e` a `C¹` periodic adapted frame (`e_a{}^0 = 0`, `e_0{}^0 > 0`,
`g^{-1} = -e_0⊗e_0 + Σ_ae_a⊗e_a`) with a continuous periodic coframe `θ`
(`v_γ = Σ_Bθ^B{}_γ e_B{}^βv_β`).  If `|g^{μβ}∂_μ∂_βu_i| ≤ K(‖u‖ + Σ_γ‖∂_γu‖)` on the slab and
`u = ∂_tu = 0` at `t₀`, then `u = 0` on `[t₀, t₁] × 𝕋³`. -/
theorem wave_unique {k : ℕ} {u : ST 3 → Fin k → ℝ} {e gi θ : ST 3 → Fin 4 → Fin 4 → ℝ}
    {a t₀ t₁ b : ℝ} (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b)
    (hu : ContDiffOn ℝ 2 u (openSlab a b)) (hup : IsSPeriodic u)
    (he : ContDiffOn ℝ 1 e (openSlab a b)) (hep : IsSPeriodic e)
    (he0 : ∀ x (c : Fin 3), e x c.succ 0 = 0) (he00 : ∀ x, 0 < e x 0 0)
    (hadapt : ∀ x μ ν, gi x μ ν = -(e x 0 μ * e x 0 ν) + ∑ c : Fin 3, e x c.succ μ * e x c.succ ν)
    (hθ : ContinuousOn θ (openSlab a b)) (hθp : IsSPeriodic θ)
    (hcof : ∀ x ∈ openSlab a b, ∀ (v : Fin 4 → ℝ) γ, v γ = ∑ B, θ x B γ * ∑ β, e x B β * v β)
    {K : ℝ} (hK : 0 ≤ K)
    (heq : ∀ x ∈ slab t₀ t₁, ∀ i, |∑ μ, ∑ β, gi x μ β * pd (pd u β) μ x i| ≤
      K * (‖u x‖ + ∑ γ, ‖pd u γ x‖))
    (h0 : ∀ y : Fin 3 → ℝ, u (Fin.cons t₀ y) = 0) (h0t : ∀ y : Fin 3 → ℝ, pd u 0 (Fin.cons t₀ y) = 0) :
    ∀ x ∈ slab t₀ t₁, u x = 0 := by
  set U := openSlab (d := 3) a b with hUdef
  have hU : IsOpen U := isOpen_openSlab a b
  have hsub : slab (d := 3) t₀ t₁ ⊆ U := slab_subset_openSlab ha hb
  -- regularity
  have hu1 : ContDiffOn ℝ 1 u U := hu.of_le (by norm_num)
  have hpdu : ∀ β, ContDiffOn ℝ 1 (pd u β) U := fun β => contDiffOn_pd hU (n := 1) hu β
  have hec : ∀ A μ, ContDiffOn ℝ 1 (fun x => e x A μ) U := fun A μ =>
    contDiffOn_pi.1 (contDiffOn_pi.1 he A) μ
  have hpdui : ∀ β i, ContDiffOn ℝ 1 (fun x => pd u β x i) U := fun β i =>
    contDiffOn_pi.1 (hpdu β) i
  have hui : ∀ i, ContDiffOn ℝ 1 (fun x => u x i) U := fun i => contDiffOn_pi.1 hu1 i
  -- the reduced state and its regularity
  set W := frameState u e with hWdef
  have hW : ContDiffOn ℝ 1 W U := by
    refine contDiffOn_pi.2 fun p => ?_
    rcases p with ⟨i, r⟩
    induction r using Fin.cases with
    | zero => exact hui i
    | succ B =>
      show ContDiffOn ℝ 1 (fun x => ∑ β, e x B β * pd u β x i) U
      exact ContDiffOn.sum fun β _ => (hec B β).mul (hpdui β i)
  have hpdp : ∀ (k' : Fin 3 → ℤ) β, IsSPeriodic (pd u β) := fun _ β k' x => by
    unfold SobolevOpen.pd
    have : (fun z => u (z + sshift k')) = u := funext fun z => hup k' z
    rw [← fderiv_comp_add_right, this]
  have hWp : IsSPeriodic W := fun k' x => by
    funext p
    simp only [hWdef, frameState, fc, hup k' x, hep k' x]
    rcases p with ⟨i, r⟩
    induction r using Fin.cases with
    | zero => rfl
    | succ B => simp only [Fin.cases_succ, hpdp k' _ k' x]
  -- derivatives of the reduced state
  have hdW0 : ∀ x ∈ U, ∀ μ i, pd W μ x (i, 0) = pd u μ x i := by
    intro x hx μ i
    rw [← pd_apply (diffAt_of_contDiffOn hU hW one_ne_zero hx) μ (i, 0),
      ← pd_apply (diffAt_of_contDiffOn hU hu1 one_ne_zero hx) μ i]
    rfl
  have hdWB : ∀ x ∈ U, ∀ μ i (B : Fin 4), pd W μ x (i, B.succ) =
      dfc (e x) (fun μ' A β => pd e μ' x A β) (fun β => pd u β x i)
        (fun μ' β => pd (pd u β) μ' x i) μ B := by
    intro x hx μ i B
    rw [← pd_apply (diffAt_of_contDiffOn hU hW one_ne_zero hx) μ (i, B.succ)]
    have hfun : (fun y => W y (i, B.succ)) = fun y => ∑ β, e y B β * pd u β y i := rfl
    rw [hfun]
    refine pd_eq_of_line ?_ ?_
    · exact diffAt_of_contDiffOn hU (ContDiffOn.sum fun β _ => (hec B β).mul (hpdui β i))
        one_ne_zero hx
    · refine HasDerivAt.fun_sum fun β _ => ?_
      have h1 := hasDerivAt_line0 (diffAt_of_contDiffOn hU (hec B β) one_ne_zero hx) μ
      have h2 := hasDerivAt_line0 (diffAt_of_contDiffOn hU (hpdui β i) one_ne_zero hx) μ
      have h3 := h1.mul h2
      simp only [zero_smul, add_zero] at h3
      rw [pd_apply (diffAt_of_contDiffOn hU (hpdu β) one_ne_zero hx) μ i,
        pd_apply (diffAt_of_contDiffOn hU (contDiffOn_pi.1 he B) one_ne_zero hx) μ β,
        pd_apply (diffAt_of_contDiffOn hU he one_ne_zero hx) μ B] at h3
      exact h3
  -- the coefficients
  set c : Fin 4 → ST 3 → Fin k × Fin 5 → Fin k × Fin 5 → ℝ := fun μ => frameCoeff e μ with hc
  have hcs : ∀ μ, ContDiffOn ℝ 1 (c μ) U := by
    intro μ
    refine contDiffOn_pi.2 fun p => contDiffOn_pi.2 fun p' => ?_
    show ContDiffOn ℝ 1 (fun x => if p.1 = p'.1 then blk (e x) μ p.2 p'.2 else 0) U
    by_cases hp : p.1 = p'.1
    · simp only [hp, if_true]
      unfold blk
      refine ContDiffOn.sub ?_ (ContDiffOn.sum fun a' _ => ?_)
      · by_cases hr : p.2 = p'.2
        · simp only [hr, if_true]; exact hec 0 μ
        · simp only [hr, if_false]; exact contDiffOn_const
      · split_ifs
        · exact hec _ μ
        · exact contDiffOn_const
    · simp only [hp, if_false]; exact contDiffOn_const
  have hcp : ∀ μ, IsSPeriodic (c μ) := fun μ k' x => by
    show frameCoeff e μ (x + sshift k') = frameCoeff e μ x
    unfold frameCoeff
    rw [hep k' x]
  have hcsym : ∀ μ x p p', c μ x p p' = c μ x p' p := by
    intro μ x p p'
    simp only [hc, frameCoeff]
    by_cases hp : p.1 = p'.1
    · rw [if_pos hp, if_pos hp.symm, blk_symm]
    · rw [if_neg hp, if_neg (Ne.symm hp)]
  have hc0 : ∀ x p p', c 0 x p p' = if p = p' then e x 0 0 else 0 := by
    intro x p p'
    simp only [hc, frameCoeff, blk_zero_time (e x) (he0 x)]
    rcases p with ⟨i, r⟩
    rcases p' with ⟨i', r'⟩
    by_cases hi : i = i' <;> by_cases hr : r = r' <;> simp [hi, hr]
  obtain ⟨κ, hκ, hκle⟩ := exists_pos_lower_slab (hec 0 0).continuousOn
    (fun k' x => by simp only [hep k' x]) he00 ha hb
  -- coefficient bounds
  have hpe : IsSPeriodic (fderiv ℝ e) := KatoGalerkin.isSPeriodic_fderiv hep
  obtain ⟨Cde, hCde⟩ := KatoGalerkin.exists_bound_slab
    (he.continuousOn_fderiv_of_isOpen hU le_rfl) hpe ha hb
  obtain ⟨Ce, hCe⟩ := KatoGalerkin.exists_bound_slab he.continuousOn hep ha hb
  obtain ⟨Cθ, hCθ⟩ := KatoGalerkin.exists_bound_slab hθ hθp ha hb
  have hCe0 : 0 ≤ Ce := by
    have := hCe (Fin.cons t₀ 0) (cons_mem_slab 0 |>.2 ⟨le_rfl, h01.le⟩)
    exact (norm_nonneg _).trans this
  have hCde0 : 0 ≤ Cde := by
    have := hCde (Fin.cons t₀ 0) (cons_mem_slab 0 |>.2 ⟨le_rfl, h01.le⟩)
    exact (norm_nonneg _).trans this
  have hCθ0 : 0 ≤ Cθ := by
    have := hCθ (Fin.cons t₀ 0) (cons_mem_slab 0 |>.2 ⟨le_rfl, h01.le⟩)
    exact (norm_nonneg _).trans this
  have be : ∀ x ∈ slab t₀ t₁, ∀ A μ, |e x A μ| ≤ Ce := fun x hx A μ =>
    ((norm_le_pi_norm (e x A) μ).trans (norm_le_pi_norm (e x) A)).trans (hCe x hx)
  have bde : ∀ x ∈ slab t₀ t₁, ∀ μ A β, |pd e μ x A β| ≤ Cde := by
    intro x hx μ A β
    have h1 : ‖pd e μ x‖ ≤ Cde := by
      unfold SobolevOpen.pd
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [Pi.norm_single, norm_one, mul_one]
      exact hCde x hx
    exact ((norm_le_pi_norm (pd e μ x A) β).trans (norm_le_pi_norm (pd e μ x) A)).trans h1
  have bθ : ∀ x ∈ slab t₀ t₁, ∀ B γ, |θ x B γ| ≤ Cθ := fun x hx B γ =>
    ((norm_le_pi_norm (θ x B) γ).trans (norm_le_pi_norm (θ x) B)).trans (hCθ x hx)
  -- the first jets are controlled by the frame components
  have bdu : ∀ x ∈ slab t₀ t₁, ∀ γ i, |pd u γ x i| ≤ 4 * Cθ * ‖W x‖ := by
    intro x hx γ i
    rw [hcof x (hsub hx) (fun β => pd u β x i) γ]
    have hWB : ∀ B, |∑ β, e x B β * pd u β x i| ≤ ‖W x‖ := fun B =>
      (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm (W x) (i, B.succ))
    refine (abs_sum_mul_le (fun B => θ x B γ) _ hWB).trans ?_
    have : ∑ B, |θ x B γ| ≤ 4 * Cθ := by
      calc ∑ B, |θ x B γ| ≤ ∑ _B : Fin 4, Cθ := Finset.sum_le_sum fun B _ => bθ x hx B γ
        _ = 4 * Cθ := by simp
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have bu : ∀ x, ∀ i, |u x i| ≤ ‖W x‖ := fun x i =>
    (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm (W x) (i, 0))
  have bnu : ∀ x, ‖u x‖ ≤ ‖W x‖ := fun x =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (Real.norm_eq_abs _).le.trans (bu x i)
  have bnpdu : ∀ x ∈ slab t₀ t₁, ∀ γ, ‖pd u γ x‖ ≤ 4 * Cθ * ‖W x‖ := fun x hx γ =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
      (Real.norm_eq_abs _).le.trans (bdu x hx γ i)
  -- the constant
  set K' : ℝ := 1 + K * (1 + 16 * Cθ) + 64 * Ce * Cde * (4 * Cθ) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  refine fun x hx => funext fun i => ?_
  have hsol := sym_unique (N := Fin k × Fin 5) (W := W) (c := c) (a0 := fun x => e x 0 0)
    ha h01 hb hW hWp hcs hcp hcsym hc0 hκ hκle hK'0 ?_ ?_ x hx
  · have := congrFun hsol (i, 0)
    exact this
  · -- the principal part is controlled
    intro x hx
    have hxU := hsub hx
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_
    rcases p with ⟨i, r⟩
    rw [Real.norm_eq_abs]
    have hcoll : ∑ μ, ∑ p', c μ x (i, r) p' * pd W μ x p' =
        ∑ μ, ∑ r', blk (e x) μ r r' * pd W μ x (i, r') := by
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Fintype.sum_prod_type]
      simp only [hc, frameCoeff, ite_mul, zero_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    rw [hcoll]
    -- the frame derivatives
    set du : Fin 4 → ℝ := fun β => pd u β x i with hdu
    set ddu : Fin 4 → Fin 4 → ℝ := fun μ β => pd (pd u β) μ x i with hddu
    set de : Fin 4 → Fin 4 → Fin 4 → ℝ := fun μ A β => pd e μ x A β with hde
    have hv : ∀ μ, (fun r' => pd W μ x (i, r')) =
        fun r' => Fin.cases (pd u μ x i) (fun B => dfc (e x) de du ddu μ B) r' := by
      intro μ
      funext r'
      induction r' using Fin.cases with
      | zero => exact hdW0 x hxU μ i
      | succ B => exact hdWB x hxU μ i B
    have bdu' : ∀ β, |du β| ≤ 4 * Cθ * ‖W x‖ := fun β => bdu x hx β i
    -- the bound for a lower-order term `Σ_β L_β du_β`
    have blow : ∀ L : Fin 4 → ℝ, (∀ β, |L β| ≤ 16 * Ce * Cde) →
        |∑ β, L β * du β| ≤ 64 * Ce * Cde * (4 * Cθ) * ‖W x‖ := by
      intro L hL
      refine (abs_sum_mul_le L du bdu').trans ?_
      have : ∑ β, |L β| ≤ 64 * Ce * Cde := by
        calc ∑ β, |L β| ≤ ∑ _β : Fin 4, 16 * Ce * Cde := Finset.sum_le_sum fun β _ => hL β
          _ = 64 * Ce * Cde := by simp; ring
      calc (∑ β, |L β|) * (4 * Cθ * ‖W x‖) ≤ 64 * Ce * Cde * (4 * Cθ * ‖W x‖) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = _ := by ring
    have bprod : ∀ A A' μ β, |e x A μ * de μ A' β| ≤ Ce * Cde := fun A A' μ β => by
      rw [abs_mul]
      exact mul_le_mul (be x hx A μ) (bde x hx μ A' β) (abs_nonneg _) hCe0
    have hWnn := norm_nonneg (W x)
    induction r using Fin.cases with
    | zero =>
      -- `e_0(u) = P`
      have : ∑ μ, ∑ r', blk (e x) μ 0 r' * pd W μ x (i, r') = W x (i, 1) := by
        simp only [blk_row0]
        rw [Finset.sum_congr rfl fun μ _ => by rw [hdW0 x hxU μ i]]
        rfl
      rw [this]
      calc |W x (i, 1)| ≤ ‖W x‖ := (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm _ _)
        _ ≤ K' * ‖W x‖ := le_mul_of_one_le_left hWnn (by
            have : 0 ≤ K * (1 + 16 * Cθ) := by positivity
            have : 0 ≤ 64 * Ce * Cde * (4 * Cθ) := by positivity
            rw [hK']; linarith)
    | succ r1 =>
      induction r1 using Fin.cases with
      | zero =>
        -- the `P`-row
        have hrow : ∑ μ, ∑ r', blk (e x) μ (Fin.succ 0) r' * pd W μ x (i, r') =
            ∑ μ, e x 0 μ * dfc (e x) de du ddu μ 0 -
              ∑ c : Fin 3, ∑ μ, e x c.succ μ * dfc (e x) de du ddu μ c.succ := by
          rw [show (Fin.succ 0 : Fin 5) = 1 from rfl]
          simp only [blk_row1, Finset.sum_sub_distrib]
          congr 1
          · exact Finset.sum_congr rfl fun μ _ => congrArg (e x 0 μ * ·) (hdWB x hxU μ i 0)
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun μ _ => by
              rw [hdWB x hxU μ i c.succ]
        rw [hrow, rowP (gi x) (e x) (hadapt x) de du ddu]
        have h1 := heq x hx i
        have h2 := blow (fun β => ∑ μ, e x 0 μ * de μ 0 β -
          ∑ c : Fin 3, ∑ μ, e x c.succ μ * de μ c.succ β) (fun β => by
            refine (abs_sub _ _).trans ?_
            refine le_trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
              (Finset.abs_sum_le_sum_abs _ _)) ?_
            have e1 : ∑ μ, |e x 0 μ * de μ 0 β| ≤ 4 * (Ce * Cde) := by
              calc ∑ μ, |e x 0 μ * de μ 0 β| ≤ ∑ _μ : Fin 4, Ce * Cde :=
                    Finset.sum_le_sum fun μ _ => bprod 0 0 μ β
                _ = 4 * (Ce * Cde) := by simp
            have e2 : ∑ c : Fin 3, |∑ μ, e x c.succ μ * de μ c.succ β| ≤ 12 * (Ce * Cde) := by
              calc ∑ c : Fin 3, |∑ μ, e x c.succ μ * de μ c.succ β| ≤
                    ∑ _c : Fin 3, 4 * (Ce * Cde) := Finset.sum_le_sum fun c _ =>
                    (Finset.abs_sum_le_sum_abs _ _).trans (by
                      calc ∑ μ, |e x c.succ μ * de μ c.succ β| ≤ ∑ _μ : Fin 4, Ce * Cde :=
                            Finset.sum_le_sum fun μ _ => bprod _ _ μ β
                        _ = 4 * (Ce * Cde) := by simp)
                _ = 12 * (Ce * Cde) := by simp; ring
            linarith)
        have h3 : ‖u x‖ + ∑ γ, ‖pd u γ x‖ ≤ (1 + 16 * Cθ) * ‖W x‖ := by
          have : ∑ γ, ‖pd u γ x‖ ≤ 16 * Cθ * ‖W x‖ := by
            calc ∑ γ, ‖pd u γ x‖ ≤ ∑ _γ : Fin 4, 4 * Cθ * ‖W x‖ :=
                  Finset.sum_le_sum fun γ _ => bnpdu x hx γ
              _ = 16 * Cθ * ‖W x‖ := by simp; ring
          linarith [bnu x]
        calc |-(∑ μ, ∑ β, gi x μ β * ddu μ β) + ∑ β, (∑ μ, e x 0 μ * de μ 0 β -
              ∑ c : Fin 3, ∑ μ, e x c.succ μ * de μ c.succ β) * du β|
            ≤ |∑ μ, ∑ β, gi x μ β * ddu μ β| + |∑ β, (∑ μ, e x 0 μ * de μ 0 β -
              ∑ c : Fin 3, ∑ μ, e x c.succ μ * de μ c.succ β) * du β| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_neg]
          _ ≤ K * ((1 + 16 * Cθ) * ‖W x‖) + 64 * Ce * Cde * (4 * Cθ) * ‖W x‖ :=
              add_le_add (h1.trans (mul_le_mul_of_nonneg_left h3 hK)) h2
          _ ≤ K' * ‖W x‖ := by rw [hK']; nlinarith
      | succ s =>
        -- the `Q`-rows
        have hrow : ∑ μ, ∑ r', blk (e x) μ s.succ.succ r' * pd W μ x (i, r') =
            ∑ μ, e x 0 μ * dfc (e x) de du ddu μ s.succ -
              ∑ μ, e x s.succ μ * dfc (e x) de du ddu μ 0 := by
          simp only [blk_rowQ, Finset.sum_sub_distrib]
          congr 1
          · exact Finset.sum_congr rfl fun μ _ => by rw [hdWB x hxU μ i s.succ]
          · exact Finset.sum_congr rfl fun μ _ =>
              congrArg (e x s.succ μ * ·) (hdWB x hxU μ i 0)
        have hs : ∀ μ β, ddu μ β = ddu β μ := fun μ β => by
          simp only [hddu]
          rw [pd_pd_symm_at hU hu hxU β μ]
        rw [hrow, rowQ (e x) de du ddu hs s]
        refine (blow _ fun β => ?_).trans ?_
        · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ μ, |e x 0 μ * de μ s.succ β - e x s.succ μ * de μ 0 β| ≤
                ∑ _μ : Fin 4, 2 * (Ce * Cde) := Finset.sum_le_sum fun μ _ =>
                  (abs_sub _ _).trans (by linarith [bprod 0 s.succ μ β, bprod s.succ 0 μ β])
            _ ≤ 16 * Ce * Cde := by simp; nlinarith [mul_nonneg hCe0 hCde0]
        · rw [hK']; nlinarith [mul_nonneg (mul_nonneg hK (by positivity : (0:ℝ) ≤ 1 + 16 * Cθ)) hWnn]
  · -- vanishing initial reduced state
    intro y
    funext p
    rcases p with ⟨i, r⟩
    have hy : (Fin.cons t₀ y : ST 3) ∈ U := ⟨ha, h01.trans hb⟩
    induction r using Fin.cases with
    | zero => simp [hWdef, frameState, h0 y]
    | succ B =>
      show fc (e (Fin.cons t₀ y)) (fun β => pd u β (Fin.cons t₀ y) i) B = 0
      have hdu0 : ∀ β, pd u β (Fin.cons t₀ y) = 0 := by
        intro β
        induction β using Fin.cases with
        | zero => exact h0t y
        | succ j =>
          refine pd_eq_of_line (diffAt_of_contDiffOn hU hu1 one_ne_zero hy) ?_
          have : (fun s : ℝ => u ((Fin.cons t₀ y : ST 3) + s • ev j.succ)) = fun _ => 0 := by
            funext s
            have : (Fin.cons t₀ y : ST 3) + s • ev j.succ = Fin.cons t₀ (y + s • Pi.single j 1) := by
              funext q
              induction q using Fin.cases with
              | zero => simp [ev]
              | succ q => simp [ev, Pi.single_apply, Fin.succ_inj]
            rw [this, h0]
          rw [this]
          exact hasDerivAt_const _ _
      simp [fc, hdu0]

end WaveUnique

/-! ### Trace reversal -/

section TraceRev

/-- **Trace reversal is injective in dimension four**: `X - ½g tr_gX = 0` forces `X = 0`. -/
theorem traceRev_inj (g gi : Fin 4 → Fin 4 → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0) (X : Fin 4 → Fin 4 → ℝ)
    (h : ∀ μ ν, traceRev g gi X μ ν = 0) : ∀ μ ν, X μ ν = 0 := by
  have htr : trG gi (fun μ ν => traceRev g gi X μ ν) = -trG gi X := by
    have e : (fun μ ν => traceRev g gi X μ ν) = fun μ ν =>
        1 * X μ ν + (-(1 / 2) * trG gi X) * g μ ν + 0 * g μ ν := by
      funext μ ν
      unfold traceRev
      ring
    rw [e, trG_comb, trG_metric g gi hgi hinv]
    simp only [Fintype.card_fin]
    ring
  have h0 : trG gi (fun μ ν => traceRev g gi X μ ν) = 0 := by
    unfold trG
    simp [h]
  have hX : trG gi X = 0 := by linarith
  intro μ ν
  have := h μ ν
  unfold traceRev at this
  rw [hX, mul_zero, sub_zero] at this
  exact this

end TraceRev

/-! ### The metric row of the residual forcing -/

section MetricRow

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')

/-- The gauge part of the residual forcing is the gauge forcing `𝔊` of the actual jet. -/
theorem errF_gauge (x : ST 3) :
    GcL (stateF SM z x) (CF z x) + GdL 0 (stateF SM z x) (pd (CF z) 0 x) +
      ∑ j : Fin 3, GdL j.succ (stateF SM z x) (pd (CF z) j.succ x) =
    toP (Gsys (𝔤 := MatLie m) (V := V) (S := S) (S' := S')
      (frameU (ginvOf ((z.jet x).state SM).g)) ((z.jet x).state SM).g
      (ginvOf ((z.jet x).state SM).g) (z.jet x).FJ.dg (z.jet x).FJ.ddg) := by
  rw [jet_dg_eq SM z x]
  have := Gsys_split (V := V) (S := S) (S' := S') (stateF SM z x) (z.jet x).FJ.ddg
  refine Eq.trans ?_ this.symm
  rw [pd_CF z x 0]
  simp only [pd_CF z x]
  rw [← jet_dg_eq SM z x]
  rfl

/-- **The metric row of the residual forcing** when the Dirac residuals vanish to first order:
`errF_p = 2N 𝓔^{tr} - 2N∇_{(μ}C_{ν)}` (no assumption on the harmonic defect). -/
theorem errF_p_gen (x : ST 3) (hD : dirF SM z x = 0) (hdD : ∀ j : Fin 3, pd (dirF SM z) j.succ x = 0)
    (μ ν : Fin 4) : (errF SM z x).1.2.1 μ ν =
      2 * (frameU (z.gi x)).N * (bosF SM z x).1 μ ν +
        gaugeForce (frameU (z.gi x)) (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν := by
  unfold errF
  rw [errF_gauge SM z x, hD]
  simp only [hdD, map_zero, add_zero, Finset.sum_const_zero]
  have hG := Gsys_eq (𝔤 := MatLie m) (V := V) (S := S) (S' := S')
    (frameU (ginvOf ((z.jet x).state SM).g)) ((z.jet x).state SM).g
    (ginvOf ((z.jet x).state SM).g) (z.jet x).FJ.dg (z.jet x).FJ.ddg (z.jet x).FJ.dg_symm μ ν
  have hB : (BmL SM (stateF SM z x) (bosF SM z x)).1.2.1 μ ν =
      2 * (frameU (ginvOf (ofP (stateF SM z x)).g)).N * (bosF SM z x).1 μ ν := by
    simp [BmL, toP, Bsys, bosR, ofR, recon, stressR, DiracStressForm.stressRes, traceRev, trG]
  have e1 : (BmL SM (stateF SM z x) (bosF SM z x) + toP (Gsys (𝔤 := MatLie m) (V := V) (S := S)
      (S' := S') (frameU (ginvOf ((z.jet x).state SM).g)) ((z.jet x).state SM).g
      (ginvOf ((z.jet x).state SM).g) (z.jet x).FJ.dg (z.jet x).FJ.ddg)).1.2.1 μ ν =
      (BmL SM (stateF SM z x) (bosF SM z x)).1.2.1 μ ν + (Gsys (𝔤 := MatLie m) (V := V) (S := S)
      (S' := S') (frameU (ginvOf ((z.jet x).state SM).g)) ((z.jet x).state SM).g
      (ginvOf ((z.jet x).state SM).g) (z.jet x).FJ.dg (z.jet x).FJ.ddg).p μ ν := rfl
  rw [e1, hB, hG]
  rfl

/-- **The reduced Einstein equation along a solution of the symmetric system**
(`prop:actual-jet-writer`, metric row): at a point where the actual-jet state solves the
independent symmetric system and the Dirac residuals vanish to first order,
`Ĝ_{μν} + Λg_{μν} - κT_{μν} = 0` (`Ĝ = G - ∇_{(μ}C_{ν)} + ½g∇·C`, `T` the complete stress). -/
theorem reduced_einstein_of_symEqAt {x : ST 3} (h : SymEqAt SM z x) (hD : dirF SM z x = 0)
    (hdD : ∀ j : Fin 3, pd (dirF SM z) j.succ x = 0) (μ ν : Fin 4) :
    reducedEinstein (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν + SM.Λ * z.g x μ ν -
      SM.κ * Tf SM z x μ ν = 0 := by
  have h0 := (symEqAt_iff SM z x).1 h
  have hN := (frameU (z.gi x)).N_pos
  have hrow : ∀ μ ν, (bosF SM z x).1 μ ν = symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν := by
    intro μ ν
    have := errF_p_gen SM z x hD hdD μ ν
    rw [h0] at this
    simp only [Prod.snd_zero, Prod.fst_zero, Pi.zero_apply] at this
    unfold gaugeForce at this
    have h2 : 2 * (frameU (z.gi x)).N * ((bosF SM z x).1 μ ν -
        symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν) = 0 := by linarith
    have hN2 : 2 * (frameU (z.gi x)).N ≠ 0 := by positivity
    linarith [(mul_eq_zero.mp h2).resolve_left hN2]
  have hgi := fun a b => z.gi_symm x a b
  have hinv := z.hinv x
  have htr : ∀ μ ν, traceRev (z.g x) (z.gi x) (fun a b => reducedEinstein (z.g x) (z.gi x)
      (z.dg x) (z.ddg x) a b + SM.Λ * z.g x a b - SM.κ * Tf SM z x a b) μ ν = 0 := by
    intro μ ν
    rw [harmonic_residual_trace_reversal (z.g x) (z.gi x) (z.dg x) (z.ddg x) hgi hinv
      (by simp) (Tf SM z x) SM.Λ SM.κ μ ν, ← hrow μ ν]
    show traceRev _ _ _ μ ν - ((z.jet x).res SM).Etr μ ν = 0
    rw [sub_eq_zero]
    rfl
  exact traceRev_inj (z.g x) (z.gi x) hgi hinv _ htr μ ν

end MetricRow

/-! ### The metric 3-jet of a smooth tuple -/

section Jet3Tuple

open ContractedBianchiJet

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (z : Tuple m V S S')

/-- **The metric 3-jet of a smooth tuple at `x`** (actual derivatives up to order three). -/
def jet3 (x : ST 3) : Jet3 (Fin 4) :=
  ⟨Matrix.of (z.g x), Matrix.of (z.gi x), fun a => Matrix.of (z.dg x a),
    fun a b => Matrix.of (z.ddg x a b),
    fun a b c => Matrix.of fun μ ν => pd (fun y => z.ddg y b c μ ν) a x⟩

theorem arraysValid (x : ST 3) : ArraysValid (z.g x) (z.gi x) (z.dg x) (z.ddg x) where
  hinv := z.hinv x
  hg := z.g_symm x
  hgi := z.gi_symm x
  hdg := z.dg_symm x
  hs1 := z.ddg_symm1 x
  hs2 := z.ddg_symm2 x

theorem jet3_resM (x : ST 3) (a b : Fin 4) :
    (jet3 z x).resM (jet3 z x).gc (jet3 z x).dgc a b =
      reducedEinstein (z.g x) (z.gi x) (z.dg x) (z.ddg x) a b :=
  resM_ofArrays (arraysValid z x) a b

theorem jet3_chr (x : ST 3) (a l s : Fin 4) :
    (jet3 z x).chr a l s = chr (z.gi x) (z.dg x) l a s :=
  chr_ofArrays (z.g x) (z.gi x) (z.dg x) (z.ddg x) a l s

theorem jet3_dchr (x : ST 3) (b a l s : Fin 4) :
    (jet3 z x).dchr b a l s = dchr (z.gi x) (z.dg x) (z.ddg x) b l a s :=
  dchr_ofArrays (z.g x) (z.gi x) (z.dg x) (z.ddg x) b a l s

theorem jet3_ricM (x : ST 3) (s b : Fin 4) :
    (jet3 z x).ricM s b = ricci (z.gi x) (z.dg x) (z.ddg x) s b :=
  ricM_ofArrays (arraysValid z x) s b

theorem jet3_gc (x : ST 3) (b : Fin 4) :
    (jet3 z x).gc b = ∑ k, z.g x b k * CF z x k := by
  rw [show (jet3 z x).gc b = (ofArrays (z.g x) (z.gi x) (z.dg x) (z.ddg x)).gc b from rfl,
    gc_ofArrays]
  rfl

theorem contDiff_ddgc (β α μ ν : Fin 4) : ContDiff ℝ ∞ (fun y => z.ddg y β α μ ν) :=
  z.contDiff_ddg β α μ ν

/-- Validity of the metric 3-jet (symmetries of the actual derivatives). -/
theorem jet3_valid (x : ST 3) : (jet3 z x).Valid where
  gG := (arraysValid z x).valid.gG
  g_symm := (arraysValid z x).valid.g_symm
  G_symm := (arraysValid z x).valid.G_symm
  dg_symm := (arraysValid z x).valid.dg_symm
  ddg_symm := (arraysValid z x).valid.ddg_symm
  ddg_comm := (arraysValid z x).valid.ddg_comm
  dddg_symm := fun a b c => by
    ext μ ν
    simp only [jet3, Matrix.transpose_apply, Matrix.of_apply]
    congr 1
    funext y
    exact z.ddg_symm2 y b c ν μ
  dddg_comm1 := fun a b c => by
    ext μ ν
    simp only [jet3, Matrix.of_apply]
    have h : ∀ β, (fun y => z.ddg y β c μ ν) = pd (fun y => z.dg y c μ ν) β := fun β =>
      funext fun y => by rw [z.ddg_apply]; congr 1; funext y'; exact (z.dg_apply y' c μ ν).symm
    rw [h b, h a]
    exact pd_pd_comm' (z.contDiff_dg c μ ν) b a x
  dddg_comm2 := fun a b c => by
    ext μ ν
    simp only [jet3, Matrix.of_apply]
    congr 1
    funext y
    exact z.ddg_symm1 y b c μ ν

theorem jet3_line_zero (x : ST 3) (e : Fin 4) : jet3 z (x + (0 : ℝ) • ev e) = jet3 z x := by
  simp

/-- **The formal jets are the actual derivatives** along every coordinate line. -/
theorem pathDeriv_jet3 (x : ST 3) (e : Fin 4) :
    Jet3.PathDeriv (fun s : ℝ => jet3 z (x + s • ev e)) e 0 := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun a i j => ?_, fun a b i j => ?_⟩
  · simp only [jet3, Matrix.of_apply, e0_line]
    exact z.line_g x e i j
  · simp only [jet3_line_zero]
    have h := z.line_gi x e i j
    rw [show (jet3 z x).dG e i j = (ofArrays (z.g x) (z.gi x) (z.dg x) (z.ddg x)).dG e i j from rfl,
      dG_ofArrays]
    exact h
  · simp only [jet3, Matrix.of_apply, e0_line]
    exact z.line_dg x e a i j
  · simp only [jet3, Matrix.of_apply, e0_line]
    exact ActualJetBridge.hasDerivAt_line0 ((z.contDiff_ddg a b i j).differentiable (by simp) x) e

/-- **The lower-index harmonic gauge covector** `c_b = g_{bk}C^k` of the tuple. -/
def cF (y : ST 3) : Fin 4 → ℝ := fun b => ∑ k, z.g y b k * CF z y k

theorem cF_eq (y : ST 3) : cF z y = fun b => (jet3 z y).gc b :=
  funext fun b => (jet3_gc z y b).symm

theorem contDiff_cF : ContDiff ℝ ∞ (cF z) := by
  refine contDiff_pi.2 fun b => ?_
  have h1 := z.contDiff_gc
  have h2 := fun k => contDiff_pi.1 (contDiff_CF z) k
  unfold cF
  fun_prop

theorem isSPeriodic_cF : IsSPeriodic (cF z) := fun k y => by
  unfold cF
  rw [isSPeriodic_CF z k y, z.g_per k y]

theorem pd_cF (x : ST 3) (e : Fin 4) : pd (cF z) e x = fun b => (jet3 z x).dgc e b := by
  refine pd_eq_of_line ((contDiff_cF z).differentiable (by simp) x) ?_
  refine hasDerivAt_pi.2 fun b => ?_
  have h := (pathDeriv_jet3 z x e).gc b
  simp only [jet3_line_zero] at h
  have hf : (fun s : ℝ => cF z (x + s • ev e) b) = fun s => (jet3 z (x + s • ev e)).gc b :=
    funext fun s => by rw [cF_eq]
  rw [hf]
  exact h

theorem pd_pd_cF (x : ST 3) (a e : Fin 4) :
    pd (pd (cF z) a) e x = fun b => (jet3 z x).ddgc e a b := by
  have hfun : pd (cF z) a = fun y b => (jet3 z y).dgc a b := funext fun y => pd_cF z y a
  rw [hfun]
  refine pd_eq_of_line ?_ ?_
  · rw [← hfun]
    exact (contDiff_pd (contDiff_cF z) a).differentiable (by simp) x
  · refine hasDerivAt_pi.2 fun b => ?_
    have h := (pathDeriv_jet3 z x e).dgc a b
    simp only [jet3_line_zero] at h
    exact h

end Jet3Tuple

/-! ### The subsidiary wave system along a solution of the symmetric system -/

section Subsidiary

open ContractedBianchiJet ContractedBianchiJet.SubsidiarySource

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')

theorem contDiff_reducedEinstein (a b : Fin 4) :
    ContDiff ℝ ∞ (fun y => reducedEinstein (z.g y) (z.gi y) (z.dg y) (z.ddg y) a b) := by
  have h1 := z.contDiff_gc
  have h2 := z.contDiff_gi
  have h3 := z.contDiff_dg
  have h4 := z.contDiff_ddg
  simp only [reducedEinstein, einstein, ricci, ricciJ, dchr, dchr1, dchr2, chr, dginv, symDefect,
    nablaDefect, nablaC, cUp, dcUp, cDown, divDefect, trG]
  fun_prop

theorem pd_eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ST 3 → E} {x : ST 3} (h : f =ᶠ[𝓝 x] g) (μ : Fin 4) : pd f μ x = pd g μ x := by
  unfold SobolevOpen.pd
  rw [h.fderiv_eq]

/-- On an open set where the symmetric system holds, the Dirac residuals vanish together with
their first derivatives (residual slaving). -/
theorem dirF_eq_zero_of_symEq {O : Set (ST 3)} (hO : IsOpen O)
    (hsym : ∀ y ∈ O, SymEqAt SM z y) {x : ST 3} (hx : x ∈ O) :
    dirF SM z x = 0 ∧ ∀ j : Fin 3, pd (dirF SM z) j.succ x = 0 := by
  refine ⟨(matter_of_symEqAt SM z (hsym x hx)).1, fun j => ?_⟩
  have ev : dirF SM z =ᶠ[𝓝 x] 0 := Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy =>
    (matter_of_symEqAt SM z (hsym y hy)).1
  exact pd_eq_zero_of_eventually ev j.succ

/-- **The reduced Einstein equation holds with its first derivatives**: on an open set where the
symmetric system holds, `Ĝ + Λg = κT` and `∂_e(Ĝ + Λg) = κ∂_eT` (formal jets of the 3-jet). -/
theorem reduced_jets {O : Set (ST 3)} (hO : IsOpen O) (hsym : ∀ y ∈ O, SymEqAt SM z y)
    {x : ST 3} (hx : x ∈ O) :
    (jet3 z x).resM (jet3 z x).gc (jet3 z x).dgc + SM.Λ • (jet3 z x).g =
        SM.κ • Matrix.of (Tf SM z x) + 0 ∧
      ∀ e, (jet3 z x).dresM (jet3 z x).gc (jet3 z x).dgc (jet3 z x).ddgc e +
        SM.Λ • (jet3 z x).dg e =
        SM.κ • Matrix.of (fun a b => pd (fun y => Tf SM z y a b) e x) + 0 := by
  have hRE : ∀ y ∈ O, ∀ a b, reducedEinstein (z.g y) (z.gi y) (z.dg y) (z.ddg y) a b +
      SM.Λ * z.g y a b = SM.κ * Tf SM z y a b := by
    intro y hy a b
    obtain ⟨hD, hdD⟩ := dirF_eq_zero_of_symEq SM z hO hsym hy
    have := reduced_einstein_of_symEqAt SM z (hsym y hy) hD hdD a b
    linarith
  refine ⟨?_, fun e => ?_⟩
  · ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, jet3_resM, Matrix.of_apply,
      Matrix.zero_apply, add_zero]
    exact hRE x hx a b
  · ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
      Matrix.zero_apply, add_zero]
    -- the line derivative of `Ĝ + Λg`
    set G : ST 3 → ℝ := fun y => reducedEinstein (z.g y) (z.gi y) (z.dg y) (z.ddg y) a b +
      SM.Λ * z.g y a b with hG
    have hGs : ContDiff ℝ ∞ G := (contDiff_reducedEinstein z a b).add
      (contDiff_const.mul (z.contDiff_gc a b))
    have hline : HasDerivAt (fun s : ℝ => G (x + s • ev e))
        ((jet3 z x).dresM (jet3 z x).gc (jet3 z x).dgc (jet3 z x).ddgc e a b +
          SM.Λ * (jet3 z x).dg e a b) 0 := by
      have h1 := (pathDeriv_jet3 z x e).resM a b
      simp only [jet3_line_zero] at h1
      have h2 := (z.line_g x e a b).const_mul SM.Λ
      have hf : (fun s : ℝ => G (x + s • ev e)) = fun s =>
          (jet3 z (x + s • ev e)).resM (jet3 z (x + s • ev e)).gc (jet3 z (x + s • ev e)).dgc a b +
            SM.Λ * z.g (x + s • ev e) a b := funext fun s => by rw [hG, jet3_resM]
      rw [hf]
      exact h1.add h2
    have hpdG : pd G e x = (jet3 z x).dresM (jet3 z x).gc (jet3 z x).dgc (jet3 z x).ddgc e a b +
        SM.Λ * (jet3 z x).dg e a b :=
      pd_eq_of_line (hGs.differentiable (by simp) x) hline
    rw [← hpdG]
    by_cases hκ : SM.κ = 0
    · rw [hκ, zero_mul]
      have ev : G =ᶠ[𝓝 x] fun _ => 0 := Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => by
        have := hRE y hy a b
        rw [hκ, zero_mul] at this
        exact this
      rw [pd_eq_of_eventuallyEq ev e]
      simp [SobolevOpen.pd]
    · have ev : (fun y => Tf SM z y a b) =ᶠ[𝓝 x] fun y => SM.κ⁻¹ * G y :=
        Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => by
          show Tf SM z y a b = SM.κ⁻¹ * (reducedEinstein (z.g y) (z.gi y) (z.dg y) (z.ddg y) a b +
            SM.Λ * z.g y a b)
          rw [hRE y hy a b]
          field_simp
      rw [pd_eq_of_eventuallyEq ev e]
      have hd : pd (fun y => SM.κ⁻¹ * G y) e x = SM.κ⁻¹ * pd G e x := by
        refine pd_eq_of_line ((contDiff_const.mul hGs).differentiable (by simp) x) ?_
        exact (hasDerivAt_line0 (hGs.differentiable (by simp) x) e).const_mul _
      rw [hd]
      field_simp

/-- The Jet3 divergence of the stress is the covariant divergence `divT`. -/
theorem divS_eq_divT (x : ST 3) (b : Fin 4) :
    divS (jet3 z x) (Matrix.of (Tf SM z x))
      (fun e => Matrix.of fun a b => pd (fun y => Tf SM z y a b) e x) b = divT SM z x b := by
  unfold divS divT
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    jet3_chr]
  rw [Finset.sum_congr rfl fun l _ => mul_comm (Tf SM z x a l) (chr (z.gi x) (z.dg x) l e b)]
  rfl

/-- **The subsidiary wave system** (`prop:subsidiary`, `eq:subsidiary`) along a solution of the
symmetric system: for theory data with the stress Noether identity, at a point of an open set
where the actual-jet state solves the symmetric system and the Yang–Mills residual vanishes, the
harmonic gauge covector satisfies `□c_b + Ric^l{}_bc_l = 0`. -/
theorem subsidiary_of_symEqAt (hT : StressNoether SM) {O : Set (ST 3)} (hO : IsOpen O)
    (hsym : ∀ y ∈ O, SymEqAt SM z y) {x : ST 3} (hx : x ∈ O) (hA : (bosF SM z x).2.1 = 0)
    (b : Fin 4) :
    (jet3 z x).boxC (jet3 z x).gc (jet3 z x).dgc (jet3 z x).ddgc b +
      (jet3 z x).ricC (jet3 z x).gc b = 0 := by
  obtain ⟨heq, hdeq⟩ := reduced_jets SM z hO hsym hx
  have hv := jet3_valid z x
  have h := subsidiary_with_source hv (jet3 z x).gc (jet3 z x).dgc (jet3 z x).ddgc
    (fun e a => Jet3.ddgc_swap hv e a) SM.Λ SM.κ (Matrix.of (Tf SM z x)) 0
    (fun e => Matrix.of fun a b => pd (fun y => Tf SM z y a b) e x) (fun _ => 0) heq hdeq b
  have hm := matter_of_symEqAt SM z (hsym x hx)
  have hdiv : divT SM z x b = 0 := divT_eq_zero z hT hA hm.2.1 hm.1 b
  have h0 : divS (jet3 z x) 0 (fun _ => 0) b = 0 := by simp [divS]
  rw [h, divS_eq_divT, hdiv, h0]
  ring

end Subsidiary

/-! ### The lower-order part of the subsidiary operator -/

section Lower

open ContractedBianchiJet

theorem abs_sum_fin_le {n : ℕ} (f : Fin n → ℝ) {B : ℝ} (h : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ n * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |f i| ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ => h i
    _ = n * B := by simp

/-- **The principal part of the subsidiary operator is controlled by the operator itself and the
first jets**: `|g^{ea}∂_e∂_ac_b| ≤ |□c_b + Ric^l{}_bc_l| + 1000M³(X + Y)` when the inverse metric,
the Christoffel symbols, their derivatives and the Ricci tensor are bounded by `M ≥ 1`,
`|c| ≤ X`, `|∂c| ≤ Y`. -/
theorem principal_le (J : Jet3 (Fin 4)) (c : Fin 4 → ℝ) (dc : Matrix (Fin 4) (Fin 4) ℝ)
    (ddc : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) {M : ℝ} (hM1 : 1 ≤ M) (hG : ∀ i j, |J.G i j| ≤ M)
    (hc : ∀ a l s, |J.chr a l s| ≤ M) (hd : ∀ b a l s, |J.dchr b a l s| ≤ M)
    (hr : ∀ i j, |J.ricM i j| ≤ M) {X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hX : ∀ l, |c l| ≤ X)
    (hY : ∀ e l, |dc e l| ≤ Y) (b : Fin 4) :
    |∑ e, ∑ a, J.G e a * ddc e a b| ≤ |J.boxC c dc ddc b + J.ricC c b| + 1000 * M ^ 3 * (X + Y) := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  set L : Fin 4 → Fin 4 → ℝ := fun e a =>
    ∑ l, J.dchr e a l b * c l + ∑ l, J.chr a l b * dc e l + ∑ l, J.chr e l a * dc l b
      - ∑ l, ∑ m', J.chr e l a * (J.chr l m' b * c m') + ∑ l, J.chr e l b * dc a l
      - ∑ l, ∑ m', J.chr e l b * (J.chr a m' l * c m') with hL
  have hnnc : ∀ e a, J.nnc c dc ddc e a b = ddc e a b - L e a := by
    intro e a
    rw [J.nnc_apply, hL]
    ring
  have hsplit : ∑ e, ∑ a, J.G e a * ddc e a b =
      (J.boxC c dc ddc b + J.ricC c b) - J.ricC c b + ∑ e, ∑ a, J.G e a * L e a := by
    unfold Jet3.boxC
    simp only [hnnc, mul_sub, Finset.sum_sub_distrib]
    ring
  -- bounds
  have hprod : ∀ p q, |p| ≤ M → |q| ≤ M → |p * q| ≤ M * M := fun p q hp hq => by
    rw [abs_mul]; exact mul_le_mul hp hq (abs_nonneg _) hM0
  have bL : ∀ e a, |L e a| ≤ 48 * M ^ 2 * (X + Y) := by
    intro e a
    have t1 : |∑ l, J.dchr e a l b * c l| ≤ 4 * (M * X) := abs_sum_fin_le _ fun l => by
      rw [abs_mul]; exact mul_le_mul (hd _ _ _ _) (hX l) (abs_nonneg _) hM0
    have t2 : |∑ l, J.chr a l b * dc e l| ≤ 4 * (M * Y) := abs_sum_fin_le _ fun l => by
      rw [abs_mul]; exact mul_le_mul (hc _ _ _) (hY _ _) (abs_nonneg _) hM0
    have t3 : |∑ l, J.chr e l a * dc l b| ≤ 4 * (M * Y) := abs_sum_fin_le _ fun l => by
      rw [abs_mul]; exact mul_le_mul (hc _ _ _) (hY _ _) (abs_nonneg _) hM0
    have t4 : |∑ l, ∑ m', J.chr e l a * (J.chr l m' b * c m')| ≤ 4 * (4 * (M * (M * X))) :=
      abs_sum_fin_le _ fun l => abs_sum_fin_le _ fun m' => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hc _ _ _) (mul_le_mul (hc _ _ _) (hX _) (abs_nonneg _) hM0)
          (by positivity) hM0
    have t5 : |∑ l, J.chr e l b * dc a l| ≤ 4 * (M * Y) := abs_sum_fin_le _ fun l => by
      rw [abs_mul]; exact mul_le_mul (hc _ _ _) (hY _ _) (abs_nonneg _) hM0
    have t6 : |∑ l, ∑ m', J.chr e l b * (J.chr a m' l * c m')| ≤ 4 * (4 * (M * (M * X))) :=
      abs_sum_fin_le _ fun l => abs_sum_fin_le _ fun m' => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hc _ _ _) (mul_le_mul (hc _ _ _) (hX _) (abs_nonneg _) hM0)
          (by positivity) hM0
    have hMM : M ≤ M ^ 2 := by nlinarith
    calc |L e a| ≤ |∑ l, J.dchr e a l b * c l| + |∑ l, J.chr a l b * dc e l| +
          |∑ l, J.chr e l a * dc l b| + |∑ l, ∑ m', J.chr e l a * (J.chr l m' b * c m')| +
          |∑ l, J.chr e l b * dc a l| + |∑ l, ∑ m', J.chr e l b * (J.chr a m' l * c m')| := by
          rw [hL]
          refine (abs_sub _ _).trans ?_
          refine add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
            (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl))
            le_rfl)) le_rfl
      _ ≤ 4 * (M * X) + 4 * (M * Y) + 4 * (M * Y) + 4 * (4 * (M * (M * X))) + 4 * (M * Y) +
          4 * (4 * (M * (M * X))) := by gcongr
      _ ≤ 48 * M ^ 2 * (X + Y) := by nlinarith [mul_nonneg hM0 hX0, mul_nonneg hM0 hY0]
  have bGL : |∑ e, ∑ a, J.G e a * L e a| ≤ 4 * (4 * (M * (48 * M ^ 2 * (X + Y)))) :=
    abs_sum_fin_le _ fun e => abs_sum_fin_le _ fun a => by
      rw [abs_mul]; exact mul_le_mul (hG _ _) (bL e a) (abs_nonneg _) hM0
  have bric : |J.ricC c b| ≤ 4 * (4 * (M * M) * X) := by
    unfold Jet3.ricC
    refine abs_sum_fin_le _ fun l => ?_
    rw [abs_mul]
    refine mul_le_mul ?_ (hX l) (abs_nonneg _) (by positivity)
    exact abs_sum_fin_le _ fun k => by
      rw [abs_mul]; exact mul_le_mul (hG _ _) (hr _ _) (abs_nonneg _) hM0
  rw [hsplit]
  have hM3 : M * M ≤ M ^ 3 := by nlinarith
  calc |(J.boxC c dc ddc b + J.ricC c b) - J.ricC c b + ∑ e, ∑ a, J.G e a * L e a|
      ≤ |J.boxC c dc ddc b + J.ricC c b| + |J.ricC c b| + |∑ e, ∑ a, J.G e a * L e a| := by
        refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ |J.boxC c dc ddc b + J.ricC c b| + 4 * (4 * (M * M) * X) +
        4 * (4 * (M * (48 * M ^ 2 * (X + Y)))) := by gcongr
    _ ≤ |J.boxC c dc ddc b + J.ricC c b| + 1000 * M ^ 3 * (X + Y) := by
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ M ^ 3) hX0,
          mul_nonneg (by positivity : (0:ℝ) ≤ M ^ 3) hY0, mul_le_mul_of_nonneg_right hM3 hX0]

end Lower

/-! ### Harmonic propagation -/

section Propagation

open ContractedBianchiJet

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')

theorem ddg_per (k : Fin 3 → ℤ) (y : ST 3) : z.ddg (y + sshift k) = z.ddg y :=
  funext fun β => funext fun α => isSPeriodic_pd' (isSPeriodic_pd' z.g_per α) β k y

/-- Sizes of the coefficient arrays of the subsidiary operator at a point. -/
def sG (x : ST 3) : ℝ := ∑ i, ∑ j, |z.gi x i j|
def sC (x : ST 3) : ℝ := ∑ a, ∑ l, ∑ s, |chr (z.gi x) (z.dg x) l a s|
def sD (x : ST 3) : ℝ := ∑ b, ∑ a, ∑ l, ∑ s, |dchr (z.gi x) (z.dg x) (z.ddg x) b l a s|
def sR (x : ST 3) : ℝ := ∑ i, ∑ j, |ricci (z.gi x) (z.dg x) (z.ddg x) i j|

/-- The size of the coefficients of the subsidiary operator at a point. -/
def coefSize (x : ST 3) : ℝ := 1 + sG z x + sC z x + sD z x + sR z x

theorem sG_nonneg (x : ST 3) : 0 ≤ sG z x := by unfold sG; positivity
theorem sC_nonneg (x : ST 3) : 0 ≤ sC z x := by unfold sC; positivity
theorem sD_nonneg (x : ST 3) : 0 ≤ sD z x := by unfold sD; positivity
theorem sR_nonneg (x : ST 3) : 0 ≤ sR z x := by unfold sR; positivity

theorem contDiff_chr_field (l a s : Fin 4) :
    ContDiff ℝ ∞ (fun x => chr (z.gi x) (z.dg x) l a s) := by
  have h2 := z.contDiff_gi
  have h3 := z.contDiff_dg
  simp only [chr]
  fun_prop

theorem contDiff_dchr_field (b l a s : Fin 4) :
    ContDiff ℝ ∞ (fun x => dchr (z.gi x) (z.dg x) (z.ddg x) b l a s) := by
  have h2 := z.contDiff_gi
  have h3 := z.contDiff_dg
  have h4 := z.contDiff_ddg
  simp only [dchr, dchr1, dchr2, dginv]
  fun_prop

theorem contDiff_ricci_field (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x => ricci (z.gi x) (z.dg x) (z.ddg x) i j) := by
  have h2 := z.contDiff_gi
  have h3 := z.contDiff_dg
  have h4 := z.contDiff_ddg
  simp only [ricci, ricciJ, dchr, dchr1, dchr2, chr, dginv]
  fun_prop

theorem continuous_coefSize : Continuous (coefSize z) := by
  have h1 := fun i j => (z.contDiff_gi i j).continuous
  have h2 := fun l a s => (contDiff_chr_field z l a s).continuous
  have h3 := fun b l a s => (contDiff_dchr_field z b l a s).continuous
  have h4 := fun i j => (contDiff_ricci_field z i j).continuous
  unfold coefSize sG sC sD sR
  fun_prop

theorem isSPeriodic_coefSize : IsSPeriodic (coefSize z) := fun k x => by
  unfold coefSize sG sC sD sR
  rw [ActualJetState.gi_per z k x, ActualJetState.dg_per z k x, ddg_per z k x]

theorem le_coefSize_gi (x : ST 3) (i j : Fin 4) : |z.gi x i j| ≤ coefSize z x := by
  have h1 : |z.gi x i j| ≤ sG z x :=
    (Finset.single_le_sum (f := fun j => |z.gi x i j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, |z.gi x i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have := sC_nonneg z x; have := sD_nonneg z x; have := sR_nonneg z x
  unfold coefSize
  linarith

theorem le_coefSize_chr (x : ST 3) (l a s : Fin 4) :
    |chr (z.gi x) (z.dg x) l a s| ≤ coefSize z x := by
  have h1 : |chr (z.gi x) (z.dg x) l a s| ≤ sC z x := by
    refine (Finset.single_le_sum (f := fun s => |chr (z.gi x) (z.dg x) l a s|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)).trans ?_
    refine (Finset.single_le_sum (f := fun l => ∑ s, |chr (z.gi x) (z.dg x) l a s|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ l, ∑ s, |chr (z.gi x) (z.dg x) l a s|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_univ a)
  have := sG_nonneg z x; have := sD_nonneg z x; have := sR_nonneg z x
  unfold coefSize
  linarith

theorem le_coefSize_dchr (x : ST 3) (b l a s : Fin 4) :
    |dchr (z.gi x) (z.dg x) (z.ddg x) b l a s| ≤ coefSize z x := by
  have h1 : |dchr (z.gi x) (z.dg x) (z.ddg x) b l a s| ≤ sD z x := by
    refine (Finset.single_le_sum (f := fun s => |dchr (z.gi x) (z.dg x) (z.ddg x) b l a s|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)).trans ?_
    refine (Finset.single_le_sum (f := fun l => ∑ s, |dchr (z.gi x) (z.dg x) (z.ddg x) b l a s|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)).trans ?_
    refine (Finset.single_le_sum
      (f := fun a => ∑ l, ∑ s, |dchr (z.gi x) (z.dg x) (z.ddg x) b l a s|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_univ a)).trans ?_
    exact Finset.single_le_sum
      (f := fun b => ∑ a, ∑ l, ∑ s, |dchr (z.gi x) (z.dg x) (z.ddg x) b l a s|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ b)
  have := sG_nonneg z x; have := sC_nonneg z x; have := sR_nonneg z x
  unfold coefSize
  linarith

theorem le_coefSize_ricci (x : ST 3) (i j : Fin 4) :
    |ricci (z.gi x) (z.dg x) (z.ddg x) i j| ≤ coefSize z x := by
  have h1 : |ricci (z.gi x) (z.dg x) (z.ddg x) i j| ≤ sR z x :=
    (Finset.single_le_sum (f := fun j => |ricci (z.gi x) (z.dg x) (z.ddg x) i j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans (Finset.single_le_sum
      (f := fun i => ∑ j, |ricci (z.gi x) (z.dg x) (z.ddg x) i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have := sG_nonneg z x; have := sC_nonneg z x; have := sD_nonneg z x
  unfold coefSize
  linarith

theorem one_le_coefSize (x : ST 3) : 1 ≤ coefSize z x := by
  have := sG_nonneg z x; have := sC_nonneg z x; have := sD_nonneg z x; have := sR_nonneg z x
  unfold coefSize
  linarith

/-- The coframe `θ^A{}_γ = ε_A g_{γν}e_A{}^ν` of the tuple's adapted frame. -/
def cofF (x : ST 3) : Fin 4 → Fin 4 → ℝ := fun A γ => cof (z.g x) lorentzSign (z.e x) A γ

theorem cF_eq_zero_of_CF {x : ST 3} (h : CF z x = 0) : cF z x = 0 := by
  funext b
  simp [cF, h]

theorem CF_eq_of_cF (x : ST 3) (k : Fin 4) : CF z x k = ∑ b, z.gi x k b * cF z x b := by
  unfold cF
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ l, ∑ b, z.gi x k b * (z.g x b l * CF z x l) = (∑ b, z.g x l b * z.gi x b k) * CF z x l :=
    fun l => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by rw [z.g_symm x b l, z.gi_symm x k b]; ring
  simp only [this, z.hinv x, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- **Propagation of the harmonic constraint** (`lem:generated-physical-identification`,
`prop:subsidiary`): for theory data with smooth sources satisfying the current and stress Noether
identities, if the actual-jet state field of a smooth tuple solves the independent symmetric system
on `(a, b) × 𝕋³` and the Gauss constraint, the harmonic defect `C` and its time derivative vanish
at `t₀ ∈ (a, b)`, then `C ≡ 0` on `[t₀, t₁] × 𝕋³` for every `t₁ ∈ (t₀, b)`. -/
theorem harmonic_propagation (hN : CurrentNoether SM) (hT : StressNoether SM) (hS : SMSmooth SM)
    {a t₀ t₁ b : ℝ} (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b)
    (hsym : ∀ x ∈ openSlab a b, SymEqAt SM z x)
    (hG0 : ∀ y : Fin 3 → ℝ, gaussF SM z (Fin.cons t₀ y) = 0)
    (hC0 : ∀ y : Fin 3 → ℝ, CF z (Fin.cons t₀ y) = 0)
    (hdC0 : ∀ y : Fin 3 → ℝ, pd (CF z) 0 (Fin.cons t₀ y) = 0) :
    ∀ x ∈ slab t₀ t₁, CF z x = 0 := by
  have hgauss := gauss_propagation SM z hN hS ha h01 hb hsym hG0
  have hA : ∀ x ∈ slab t₀ t₁, (bosF SM z x).2.1 = 0 := by
    intro x hx
    obtain ⟨-, -, hE⟩ := matter_of_symEqAt SM z (hsym x (slab_subset_openSlab ha hb hx))
    refine eq_zero_of_frame_components z x _ fun A => ?_
    induction A using Fin.cases with
    | zero => exact hgauss x hx
    | succ c => exact hE c
  have hsub : ∀ x ∈ slab t₀ t₁, ∀ c, (jet3 z x).boxC (jet3 z x).gc (jet3 z x).dgc
      (jet3 z x).ddgc c + (jet3 z x).ricC (jet3 z x).gc c = 0 := fun x hx c =>
    subsidiary_of_symEqAt SM z hT (isOpen_openSlab a b) hsym (slab_subset_openSlab ha hb hx)
      (hA x hx) c
  -- uniform coefficient bound
  obtain ⟨Mb, hMb⟩ := KatoGalerkin.exists_bound_slab (continuous_coefSize z).continuousOn
    (isSPeriodic_coefSize z) ha hb
  set M := max Mb 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMx : ∀ x ∈ slab t₀ t₁, coefSize z x ≤ M := fun x hx => by
    have := hMb x hx
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le one_pos (one_le_coefSize z x))] at this
    exact this.trans (le_max_left _ _)
  -- the frame data
  have heC : ContDiff ℝ ∞ (fun x => z.e x) :=
    contDiff_pi.2 fun A => contDiff_pi.2 fun μ => z.contDiff_e A μ
  have hep : IsSPeriodic (fun x => z.e x) := fun k y => funext fun A => funext fun μ =>
    e_per z k y A μ
  have he0 : ∀ x (c : Fin 3), z.e x c.succ 0 = 0 := fun x c => by
    rw [e_eq_frameU]; exact AdaptedFrame.fr_succ_zero _ c
  have he00 : ∀ x, 0 < z.e x 0 0 := fun x => by
    rw [e_eq_frameU, AdaptedFrame.fr_zero_zero]; exact inv_pos.2 (frameU (z.gi x)).N_pos
  have hadapt : ∀ x μ ν, z.gi x μ ν = -(z.e x 0 μ * z.e x 0 ν) +
      ∑ c : Fin 3, z.e x c.succ μ * z.e x c.succ ν := fun x μ ν => by
    rw [z.compl x μ ν, Fin.sum_univ_succ]
    simp [lorentzSign, Fin.succ_ne_zero]
  have hθ : Continuous (cofF z) := by
    have h1 := z.contDiff_gc
    have h2 := z.contDiff_e
    refine continuous_pi fun A => continuous_pi fun γ => ?_
    show Continuous fun x => lorentzSign A * ∑ ν, z.g x γ ν * z.e x A ν
    have : ContDiff ℝ ∞ fun x => lorentzSign A * ∑ ν, z.g x γ ν * z.e x A ν := by fun_prop
    exact this.continuous
  have hθp : IsSPeriodic (cofF z) := fun k y => by
    funext A γ
    simp only [cofF, cof, z.g_per k y, e_per z k y]
  have hcof : ∀ x ∈ openSlab a b, ∀ (v : Fin 4 → ℝ) γ,
      v γ = ∑ B, cofF z x B γ * ∑ β, z.e x B β * v β := fun x _ v γ => by
    have := ActualJetRecon.inv_vec (z.jet x).FJ v γ
    simp only [smul_eq_mul] at this
    exact this
  -- the wave estimate for `c = cF`
  have hK : (0 : ℝ) ≤ 1000 * M ^ 3 := by positivity
  have heq : ∀ x ∈ slab t₀ t₁, ∀ i, |∑ μ, ∑ β, z.gi x μ β * pd (pd (cF z) β) μ x i| ≤
      1000 * M ^ 3 * (‖cF z x‖ + ∑ γ, ‖pd (cF z) γ x‖) := by
    intro x hx i
    have e1 : ∑ μ, ∑ β, z.gi x μ β * pd (pd (cF z) β) μ x i =
        ∑ e, ∑ a', (jet3 z x).G e a' * (jet3 z x).ddgc e a' i := by
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun β _ => ?_
      rw [pd_pd_cF z x β μ]
      rfl
    rw [e1]
    have hMxx := hMx x hx
    have h := principal_le (jet3 z x) (jet3 z x).gc (jet3 z x).dgc (jet3 z x).ddgc hM1
      (fun i j => (le_coefSize_gi z x i j).trans hMxx)
      (fun a' l s => by rw [jet3_chr]; exact (le_coefSize_chr z x l a' s).trans hMxx)
      (fun b' a' l s => by rw [jet3_dchr]; exact (le_coefSize_dchr z x b' l a' s).trans hMxx)
      (fun i j => by rw [jet3_ricM]; exact (le_coefSize_ricci z x i j).trans hMxx)
      (norm_nonneg (cF z x)) (Finset.sum_nonneg fun γ _ => norm_nonneg (pd (cF z) γ x))
      (fun l => by
        rw [show (jet3 z x).gc l = cF z x l from (congrFun (cF_eq z x) l).symm]
        exact (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm _ l))
      (fun e l => by
        have h1 : (jet3 z x).dgc e l = pd (cF z) e x l := by rw [pd_cF z x e]
        rw [h1]
        refine ((Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm _ l)).trans ?_
        exact Finset.single_le_sum (f := fun γ => ‖pd (cF z) γ x‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ e)) i
    rw [hsub x hx i, abs_zero, zero_add] at h
    exact h
  have h0 : ∀ y : Fin 3 → ℝ, cF z (Fin.cons t₀ y) = 0 := fun y =>
    cF_eq_zero_of_CF z (hC0 y)
  have h0t : ∀ y : Fin 3 → ℝ, pd (cF z) 0 (Fin.cons t₀ y) = 0 := by
    intro y
    have hC := hC0 y
    have hdC := hdC0 y
    refine pd_eq_of_line ((contDiff_cF z).differentiable (by simp) (Fin.cons t₀ y)) ?_
    refine hasDerivAt_pi.2 fun c => ?_
    have hCl := hasDerivAt_line0 ((contDiff_CF z).differentiable (by simp) (Fin.cons t₀ y)) 0
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun k (_ : k ∈ Finset.univ) =>
      (z.line_g (Fin.cons t₀ y) 0 c k).fun_mul (hasDerivAt_pi.1 hCl k)
    simp only [zero_smul, add_zero, hC, hdC, Pi.zero_apply, mul_zero, zero_mul,
      Finset.sum_const_zero] at h
    rw [Pi.zero_apply]
    exact h
  have hc := wave_unique (u := cF z) (e := fun x => z.e x) (gi := z.gi) (θ := cofF z) ha h01 hb
    ((contDiff_cF z).of_le (by norm_cast)).contDiffOn (isSPeriodic_cF z)
    ((heC.of_le (by norm_cast)).contDiffOn) hep he0 he00 hadapt hθ.continuousOn hθp
    hcof hK heq h0 h0t
  intro x hx
  funext k
  rw [CF_eq_of_cF z x k, hc x hx]
  simp

/-- **Physical identification of smooth tuples from constrained data**
(`lem:generated-physical-identification`, smooth-tuple form): for theory data with smooth
sources and the current and stress Noether identities, a smooth tuple whose actual-jet state solves
the independent symmetric system on `(a, b) × 𝕋³` and whose Gauss constraint, harmonic defect and
its time derivative vanish at `t₀ ∈ (a, b)` is a physical solution on `(t₀, b) × 𝕋³`: the
Einstein, Yang–Mills, Higgs, Dirac and dual Dirac residuals and `C` vanish there. -/
theorem physical_of_constraints (hN : CurrentNoether SM) (hT : StressNoether SM)
    (hS : SMSmooth SM) {a t₀ b : ℝ} (ha : a < t₀) (hsym : ∀ x ∈ openSlab a b, SymEqAt SM z x)
    (hG0 : ∀ y : Fin 3 → ℝ, gaussF SM z (Fin.cons t₀ y) = 0)
    (hC0 : ∀ y : Fin 3 → ℝ, CF z (Fin.cons t₀ y) = 0)
    (hdC0 : ∀ y : Fin 3 → ℝ, pd (CF z) 0 (Fin.cons t₀ y) = 0) :
    IsPhysicalOn SM z (openSlab t₀ b) := by
  refine (physical_iff_constraints SM z (isOpen_openSlab t₀ b)).2 fun x hx => ?_
  have hxo : x ∈ openSlab a b := ⟨ha.trans hx.1, hx.2⟩
  obtain ⟨t₁, ht₁, ht₁b⟩ := exists_between hx.2
  refine ⟨hsym x hxo, ?_, ?_⟩
  · exact harmonic_propagation SM z hN hT hS ha (hx.1.trans ht₁) ht₁b hsym hG0 hC0 hdC0 x
      ⟨hx.1.le, ht₁.le⟩
  · exact gauss_propagation SM z hN hS ha (hx.1.trans ht₁) ht₁b hsym hG0 x ⟨hx.1.le, ht₁.le⟩

end Propagation

/-! ### The time derivative of the harmonic defect from the Einstein constraints -/

section InitialConstraints

/-- **Algebra of the initial harmonic constraint**: if the covariant derivative of a covector
vanishing on the initial slice is `∇_μc_ν = δ_μ^0 v_ν` and the normal components
`𝓗(e_0, ·)` of `𝓗_{μν} = ∇_{(μ}c_{ν)} - ½g_{μν}∇·c` vanish, then `v = 0`
(`g^{0β} = -e_0^0e_0^β`, `g(e_0, e_0) = -1`, `e_0^0 > 0`). -/
theorem normal_defect_alg (g gi : Fin 4 → Fin 4 → ℝ) (e0 v : Fin 4 → ℝ) (he00 : 0 < e0 0)
    (hgi0 : ∀ β, gi 0 β = -(e0 0 * e0 β)) (hnorm : ∑ μ, ∑ ν, g μ ν * e0 μ * e0 ν = -1)
    (h : ∀ ν, ∑ μ, e0 μ * (((if μ = 0 then v ν else 0) + (if ν = 0 then v μ else 0)) / 2 -
      (1 / 2) * g μ ν * ∑ α, ∑ β, gi α β * (if α = 0 then v β else 0)) = 0) : v = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, s = ∑ β, e0 β * v β := ⟨_, rfl⟩
  have htr : ∑ α, ∑ β, gi α β * (if α = 0 then v β else 0) = -(e0 0 * s) := by
    rw [Fin.sum_univ_succ]
    simp only [↓reduceIte, Fin.succ_ne_zero, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hs, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun β _ => by rw [hgi0]; ring
  have hrow : ∀ ν, ∑ μ, e0 μ * (((if μ = 0 then v ν else 0) + (if ν = 0 then v μ else 0)) / 2 -
      (1 / 2) * g μ ν * ∑ α, ∑ β, gi α β * (if α = 0 then v β else 0)) =
      (1 / 2) * e0 0 * v ν + (1 / 2) * (if ν = 0 then s else 0) +
        (1 / 2) * e0 0 * s * ∑ μ, g μ ν * e0 μ := by
    intro ν
    rw [htr]
    have e1 : ∑ μ, e0 μ * ((if μ = 0 then v ν else 0) / 2) = (1 / 2) * e0 0 * v ν := by
      rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hb]) (by simp)]
      simp only [↓reduceIte]
      ring
    have e2 : ∑ μ, e0 μ * ((if ν = 0 then v μ else 0) / 2) =
        (1 / 2) * (if ν = 0 then s else 0) := by
      by_cases hν : ν = 0
      · simp only [hν, ↓reduceIte]
        rw [hs, Finset.mul_sum]
        exact Finset.sum_congr rfl fun μ _ => by ring
      · simp [hν]
    have e3 : ∑ μ, e0 μ * (1 / 2 * g μ ν * -(e0 0 * s)) =
        -((1 / 2) * e0 0 * s * ∑ μ, g μ ν * e0 μ) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun μ _ => by ring
    have e4 : ∑ μ, e0 μ * (((if μ = 0 then v ν else 0) + (if ν = 0 then v μ else 0)) / 2 -
        (1 / 2) * g μ ν * -(e0 0 * s)) =
        ∑ μ, e0 μ * ((if μ = 0 then v ν else 0) / 2) +
          ∑ μ, e0 μ * ((if ν = 0 then v μ else 0) / 2) -
          ∑ μ, e0 μ * (1 / 2 * g μ ν * -(e0 0 * s)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun μ _ => by ring
    rw [e4, e1, e2, e3]
    ring
  -- contraction with `e_0`
  have hs0 : s = 0 := by
    have hc : ∑ ν, e0 ν * ((1 / 2) * e0 0 * v ν + (1 / 2) * (if ν = 0 then s else 0) +
        (1 / 2) * e0 0 * s * ∑ μ, g μ ν * e0 μ) = 0 := by
      refine Finset.sum_eq_zero fun ν _ => ?_
      rw [← hrow ν, h ν, mul_zero]
    have f1 : ∑ ν, e0 ν * ((1 / 2) * e0 0 * v ν) = (1 / 2) * e0 0 * s := by
      rw [hs, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ν _ => by ring
    have f2 : ∑ ν, e0 ν * ((1 / 2) * (if ν = 0 then s else 0)) = (1 / 2) * e0 0 * s := by
      rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hb]) (by simp)]
      simp only [↓reduceIte]
      ring
    have f3 : ∑ ν, e0 ν * ((1 / 2) * e0 0 * s * ∑ μ, g μ ν * e0 μ) =
        (1 / 2) * e0 0 * s * ∑ μ, ∑ ν, g μ ν * e0 μ * e0 ν := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
    have e1 : ∑ ν, e0 ν * ((1 / 2) * e0 0 * v ν + (1 / 2) * (if ν = 0 then s else 0) +
        (1 / 2) * e0 0 * s * ∑ μ, g μ ν * e0 μ) =
        ∑ ν, e0 ν * ((1 / 2) * e0 0 * v ν) + ∑ ν, e0 ν * ((1 / 2) * (if ν = 0 then s else 0)) +
          ∑ ν, e0 ν * ((1 / 2) * e0 0 * s * ∑ μ, g μ ν * e0 μ) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ν _ => by ring
    rw [e1, f1, f2, f3, hnorm] at hc
    have : (1 / 2) * e0 0 * s = 0 := by linarith
    have he : (1 / 2) * e0 0 ≠ 0 := by positivity
    exact (mul_eq_zero.mp this).resolve_left he
  funext ν
  have := h ν
  rw [hrow ν, hs0] at this
  simp only [mul_zero, zero_mul, add_zero, ite_self] at this
  have he : (1 / 2) * e0 0 ≠ 0 := by positivity
  exact (mul_eq_zero.mp this).resolve_left he

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')

/-- **The Einstein constraints** (Hamiltonian and momentum constraints): the normal components
`(G + Λg - κT)(e_0, ·)` of the Einstein residual. -/
def einsteinConstraint (x : ST 3) (ν : Fin 4) : ℝ :=
  ∑ μ, z.e x 0 μ * (einstein (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν + SM.Λ * z.g x μ ν -
    SM.κ * Tf SM z x μ ν)

/-- Where `C` vanishes, `∇_μc_ν = g_{νl}∂_μC^l`. -/
theorem nablaDefect_of_CF {x : ST 3} (hC : CF z x = 0) (μ ν : Fin 4) :
    nablaDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν = ∑ l, z.g x ν l * pd (CF z) μ x l := by
  have hC' : ∀ l, cUp (z.gi x) (chr (z.gi x) (z.dg x)) l = 0 := fun l => congrFun hC l
  unfold nablaDefect nablaC cDown
  simp only [hC', mul_zero, Finset.sum_const_zero, zero_add, sub_zero]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pd_CF z x μ]
  rfl

/-- **`∂_tC = 0` on the initial slice from the Einstein constraints**: if the actual-jet state solves
the symmetric system near the slice, `C` vanishes on the slice `t = t₀` and the Einstein
constraints `(G + Λg - κT)(e_0, ·)` vanish there, then `∂_tC = 0` on the slice (the reduced Einstein
equation gives `𝓗(e_0, ·) = 0`, and `normal_defect_alg`). -/
theorem dtC_of_constraints {a b t₀ : ℝ} (ha : a < t₀) (hb : t₀ < b)
    (hsym : ∀ x ∈ openSlab a b, SymEqAt SM z x)
    (hC0 : ∀ y : Fin 3 → ℝ, CF z (Fin.cons t₀ y) = 0)
    (hE0 : ∀ (y : Fin 3 → ℝ) ν, einsteinConstraint SM z (Fin.cons t₀ y) ν = 0)
    (y : Fin 3 → ℝ) : pd (CF z) 0 (Fin.cons t₀ y) = 0 := by
  obtain ⟨x, hxdef⟩ : ∃ x : ST 3, x = Fin.cons t₀ y := ⟨_, rfl⟩
  rw [← hxdef]
  have hx : x ∈ openSlab a b := by rw [hxdef]; exact ⟨ha, hb⟩
  have hC : CF z x = 0 := by rw [hxdef]; exact hC0 y
  -- spatial derivatives of `C` vanish on the slice
  have hsp : ∀ j : Fin 3, pd (CF z) j.succ x = 0 := by
    intro j
    refine pd_eq_of_line ((contDiff_CF z).differentiable (by simp) x) ?_
    have : (fun s : ℝ => CF z (x + s • ev j.succ)) = fun _ => 0 := by
      funext s
      have : x + s • ev j.succ = Fin.cons t₀ (y + s • Pi.single j 1) := by
        funext q
        induction q using Fin.cases with
        | zero => simp [hxdef, ev]
        | succ q => simp [hxdef, ev, Pi.single_apply, Fin.succ_inj]
      rw [this, hC0]
    rw [this]
    exact hasDerivAt_const _ _
  -- the reduced Einstein equation at `x`
  obtain ⟨hD, hdD⟩ := dirF_eq_zero_of_symEq SM z (isOpen_openSlab a b) hsym hx
  have hred := reduced_einstein_of_symEqAt SM z (hsym x hx) hD hdD
  -- `v_ν = g_{νl}∂_tC^l`
  set v : Fin 4 → ℝ := fun ν => ∑ l, z.g x ν l * pd (CF z) 0 x l with hv
  have hw : ∀ μ ν, nablaDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν =
      if μ = 0 then v ν else 0 := by
    intro μ ν
    rw [nablaDefect_of_CF z hC]
    induction μ using Fin.cases with
    | zero => rfl
    | succ j => simp [hsp j, Fin.succ_ne_zero]
  have hH : ∀ ν, ∑ μ, z.e x 0 μ * defectTensor (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν = 0 := by
    intro ν
    have h1 := hE0 y ν
    rw [← hxdef] at h1
    unfold einsteinConstraint at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have := hred μ ν
    rw [reducedEinstein_eq] at this
    congr 1
    linarith
  have hv0 : v = 0 := by
    refine normal_defect_alg (z.g x) (z.gi x) (z.e x 0) v ?_ ?_ ?_ fun ν => ?_
    · rw [e_eq_frameU, AdaptedFrame.fr_zero_zero]; exact inv_pos.2 (frameU (z.gi x)).N_pos
    · intro β
      rw [z.compl x 0 β, Fin.sum_univ_succ]
      have : ∀ c : Fin 3, z.e x c.succ 0 = 0 := fun c => by
        rw [e_eq_frameU]; exact AdaptedFrame.fr_succ_zero _ c
      simp [lorentzSign, Fin.succ_ne_zero, this]
    · simpa [ipg, lorentzSign] using z.orth_at x 0 0
    · have := hH ν
      simpa only [defectTensor, symDefect, divDefect, trG, hw] using this
  funext l
  have hdc : pd (CF z) 0 x l = ∑ ν, z.gi x l ν * v ν := by
    rw [hv]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ k, ∑ ν, z.gi x l ν * (z.g x ν k * pd (CF z) 0 x k) =
        (∑ ν, z.g x k ν * z.gi x ν l) * pd (CF z) 0 x k := fun k => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun ν _ => by rw [z.g_symm x ν k, z.gi_symm x l ν]; ring
    simp only [this, z.hinv x, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  rw [hdc, hv0]
  simp

/-- **Physical identification of smooth tuples from constrained Cauchy data**
(`lem:generated-physical-identification`, smooth-tuple form with the physical initial
constraints): for theory data with smooth sources and the current and stress Noether identities,
a smooth tuple whose actual-jet state solves the independent symmetric system on `(a, b) × 𝕋³` and
whose initial slice `t = t₀` satisfies the Gauss law, the harmonic gauge condition `C = 0` and the
Einstein (Hamiltonian and momentum) constraints is a physical solution on `(t₀, b) × 𝕋³`. -/
theorem physical_of_initial_constraints (hN : CurrentNoether SM) (hT : StressNoether SM)
    (hS : SMSmooth SM) {a t₀ b : ℝ} (ha : a < t₀) (hb : t₀ < b)
    (hsym : ∀ x ∈ openSlab a b, SymEqAt SM z x)
    (hG0 : ∀ y : Fin 3 → ℝ, gaussF SM z (Fin.cons t₀ y) = 0)
    (hC0 : ∀ y : Fin 3 → ℝ, CF z (Fin.cons t₀ y) = 0)
    (hE0 : ∀ (y : Fin 3 → ℝ) ν, einsteinConstraint SM z (Fin.cons t₀ y) ν = 0) :
    IsPhysicalOn SM z (openSlab t₀ b) :=
  physical_of_constraints SM z hN hT hS ha hsym hG0 hC0
    (dtC_of_constraints SM z ha hb hsym hC0 hE0)

end InitialConstraints

/-! ### Non-vacuity -/

section NonVacuity

open CoupledBootstrap.FlatVacuum

/-- The Einstein constraints hold wherever the Einstein residual vanishes. -/
theorem einsteinConstraint_of_bosF {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
    {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
    (SM : SMData (MatLie m) V S S') (z : Tuple m V S S') {x : ST 3}
    (h : (bosF SM z x).1 = 0) (ν : Fin 4) : einsteinConstraint SM z x ν = 0 := by
  have hE := traceRev_inj (z.g x) (z.gi x) (fun a b => z.gi_symm x a b) (z.hinv x)
    (fun a b => einstein (z.g x) (z.gi x) (z.dg x) (z.ddg x) a b + SM.Λ * z.g x a b -
      SM.κ * Tf SM z x a b) (fun μ ν => congrFun (congrFun h μ) ν)
  unfold einsteinConstraint
  exact Finset.sum_eq_zero fun μ _ => by rw [hE μ ν, mul_zero]

/-- **Non-vacuity of `physical_of_initial_constraints`** (flat vacuum, variational data
`trivSMM` with the current and stress Noether identities): all hypotheses hold on every slab. -/
example : IsPhysicalOn trivSMM flat (openSlab 0 1) :=
  physical_of_initial_constraints trivSMM flat (currentNoether_of_variational trivSMM_variational)
    trivSMM_stressNoether trivSMM_smooth (a := -1) (by norm_num) (by norm_num)
    (fun x _ => symEqAt_of_physical trivSMM flat isOpen_univ flat_isPhysicalOn trivial)
    (fun y => by unfold gaussF; rw [flat_bosF]; simp) (fun y => flat_CF _)
    (fun y ν => einsteinConstraint_of_bosF trivSMM flat (by rw [flat_bosF]; rfl) ν)

/-- **The theory-data hypotheses hold for the `gl(m)` Yang–Mills–adjoint-Higgs model**: for every
smooth tuple of this model, `physical_of_initial_constraints` applies (current and stress Noether
identities and smooth sources are proved for these data). -/
example (m : ℕ) (Λ κ lam v : ℝ) (z : Tuple m (MatLie m) PUnit PUnit) {a t₀ b : ℝ} (ha : a < t₀)
    (hb : t₀ < b) (hsym : ∀ x ∈ openSlab a b, SymEqAt (adjSM m Λ κ lam v) z x)
    (hG0 : ∀ y : Fin 3 → ℝ, gaussF (adjSM m Λ κ lam v) z (Fin.cons t₀ y) = 0)
    (hC0 : ∀ y : Fin 3 → ℝ, CF z (Fin.cons t₀ y) = 0)
    (hE0 : ∀ (y : Fin 3 → ℝ) ν, einsteinConstraint (adjSM m Λ κ lam v) z (Fin.cons t₀ y) ν = 0) :
    IsPhysicalOn (adjSM m Λ κ lam v) z (openSlab t₀ b) :=
  physical_of_initial_constraints _ z (adjSM_currentNoether m Λ κ lam v)
    (adjSM_stressNoether m Λ κ lam v) (adjSM_smooth m Λ κ lam v) ha hb hsym hG0 hC0 hE0

end NonVacuity

end RenewalGeometry.GenHarmonic
