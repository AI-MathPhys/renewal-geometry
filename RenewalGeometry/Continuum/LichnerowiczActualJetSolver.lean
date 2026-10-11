/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.LichnerowiczActualJetBridge
import RenewalGeometry.Continuum.LichnerowiczSmoothSources

/-!
# The constrained-initial solver produces constrained actual-jet data

Einstein–Standard-Model action-closure manuscript, `prop:generated-initial` and
`ass:constrained-initial-solver`, composed with the actual-jet data class of
`lem:generated-physical-identification`.

For theory data whose Yang–Mills source vanishes at zero Higgs field and zero spinors, a Higgs
normal momentum `Π₀` with `𝖠_* = 2κ|Π₀|² > 0` and a mean curvature `τ` fixed by the background
constraint `⅔τ² - 2Λ - 2κλv⁴ = 𝖠_*` (`LichData` `bgData`: `G_* = B_* = 0`, `C_* = 𝖠_*`,
`μ_* = 12𝖠_*`):

* `seedSource σ` — the source `δ𝖠 = |σ|²` of a transverse–traceless seed, real, smooth, in every
  `H^r` and every weighted Wiener algebra;
* **`solver_constrained`** — for every TT seed with `‖δ𝖠‖_{H^r} ≤ ε_r` (`eq:generated-source-small`
  with `‖|σ|²‖_{H^r} ≤ K_r Σ‖σᵢⱼ‖²_{H^r}`, `seedSource_small`), the conformal factor `w` produced by the
  Banach contraction `LichnerowiczContraction.lichnerowicz_solution` is **`C^∞`** (elliptic
  regularity at all orders, `LichReg.wsum_all_of_hamiltonianEq`), `1/2 < w < 3/2`, and the
  conformal Cauchy datum `(w⁴δ, w⁻²σ + (τ/3)w⁴δ, A = Ȧ = 0, H = 0, Ḣ = w⁻⁶Π₀, Ψ = Ψ̄ = 0)`
  satisfies the complete Hamiltonian, momentum and Gauss constraints;
* **`solver_constrainedData`** — its Cauchy-data completion is slice-constrained and its
  actual-jet state is a `GenPhysIdClosed.ConstrainedData` datum.
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ContDiff ComplexConjugate

namespace RenewalGeometry.GenSlice.ConfSolver

open SobolevOpen (pd)
open TorusFourierTruncation TorusSobolevTransfer PeriodicGridSobolev PeriodicGridSobolev.Sampling
  PeriodicGridSobolev.Composition LichnerowiczContraction SobolevBoxCr LichReg Conf ActualJetSystem ActualJetSmooth ActualJetBridge
  ActualJetState GenPhysIdClosed GenPhysId ActualJetKato

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable section

/-! ### Fourier facts -/

/-- `Σ_n |F̂(n)| ≤ √c ‖F‖_{H²}`. -/
theorem tsum_norm_le_sn_two {F : CT} (hF : MemH 2 ⇑F) :
    ∑' n, ‖mFourierCoeff ⇑F n‖ ≤ Real.sqrt cEmb * sn 2 ⇑F := by
  have hW : ∀ n, 0 < trigWeight 2 n := fun n => trigWeight_pos 2 n
  obtain ⟨hs, hb⟩ := norm_tsum_sq_le (fun n => ((‖mFourierCoeff ⇑F n‖ : ℝ) : ℂ))
    (fun n => (trigWeight 2 n)⁻¹) (fun n => trigWeight 2 n * ‖mFourierCoeff ⇑F n‖ ^ 2)
    (fun n => (inv_pos.mpr (hW n)).le) (fun n => mul_nonneg (hW n).le (sq_nonneg _))
    (fun n => by
      rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), ← mul_assoc,
        inv_mul_cancel₀ (hW n).ne', one_mul])
    (summable_inv_trigWeight 2 le_rfl) hF
  have hsr : Summable fun n => ‖mFourierCoeff ⇑F n‖ := summable_norm_of_trigWeight le_rfl hF
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ =>
    norm_nonneg _)] at hb
  have hb' : (∑' n, ‖mFourierCoeff ⇑F n‖) ^ 2 ≤ cEmb * trigSobSq 2 ⇑F := hb
  unfold sn
  rw [← Real.sqrt_mul cEmb_nonneg]
  exact Real.le_sqrt_of_sq_le hb'

theorem trigWeight_le (r : ℕ) (n : Fin 3 → ℤ) :
    trigWeight r n ≤ (r + 1) ^ 3 * ((2 * π) ^ 2) ^ r * (1 + ab n) ^ (2 * r) := by
  set X : ℝ := (2 * π * (1 + ab n)) ^ 2 with hX
  have hab := ab_nonneg n
  have hX1 : 1 ≤ X := by
    rw [hX]
    have : (1 : ℝ) ≤ 2 * π * (1 + ab n) := by nlinarith [Real.pi_gt_three]
    nlinarith
  have hfac : ∀ i : Fin 3, (2 * π * (n i : ℝ)) ^ 2 ≤ X := by
    intro i
    rw [hX, ← sq_abs (2 * π * (n i : ℝ))]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have := abs_le_ab n i
    nlinarith [Real.pi_pos]
  have hterm : ∀ α ∈ multiIndices r, tsymSq α n ≤ X ^ r := by
    intro α hα
    rw [mem_multiIndices] at hα
    unfold deg at hα
    unfold tsymSq
    calc ((2 * π * (n 0 : ℝ)) ^ 2) ^ α 0 * ((2 * π * (n 1 : ℝ)) ^ 2) ^ α 1 *
          ((2 * π * (n 2 : ℝ)) ^ 2) ^ α 2 ≤ X ^ α 0 * X ^ α 1 * X ^ α 2 := by
          gcongr
          · exact hfac 0
          · exact hfac 1
          · exact hfac 2
      _ = X ^ (α 0 + α 1 + α 2) := by rw [pow_add, pow_add]
      _ ≤ X ^ r := pow_le_pow_right₀ hX1 hα
  have hcard : ((multiIndices r).card : ℝ) ≤ (r + 1) ^ 3 := by
    have : (multiIndices r).card ≤ (r + 1) ^ 3 := by
      unfold multiIndices
      refine (card_filter_le _ _).trans (le_of_eq ?_)
      simp
    exact_mod_cast this
  unfold trigWeight
  calc ∑ α ∈ multiIndices r, tsymSq α n ≤ ∑ _α ∈ multiIndices r, X ^ r := sum_le_sum hterm
    _ = (multiIndices r).card * X ^ r := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (r + 1) ^ 3 * X ^ r := by gcongr
    _ = (r + 1) ^ 3 * ((2 * π) ^ 2) ^ r * (1 + ab n) ^ (2 * r) := by
        rw [hX, mul_pow (2 * π) (1 + ab n) 2, mul_pow ((2 * π) ^ 2) ((1 + ab n) ^ 2) r,
          ← pow_mul (1 + ab n) 2 r, mul_assoc]

/-- **Weighted Wiener regularity gives Sobolev regularity**: `WSum 1 (2r) F → F ∈ H^r`. -/
theorem memH_of_wsum {r : ℕ} {F : CT} (hF : WSum 1 (2 * r) F) : MemH r ⇑F := by
  have hs := hF.summable_norm one_pos
  set M := ∑' n, ‖mFourierCoeff ⇑F n‖
  have hle : ∀ n, ‖mFourierCoeff ⇑F n‖ ≤ M := fun n =>
    hs.le_tsum n fun m _ => norm_nonneg _
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (trigWeight_nonneg r n) (sq_nonneg _))
    (fun n => ?_) (hF.mul_left (((r : ℝ) + 1) ^ 3 * ((2 * π) ^ 2) ^ r * M))
  have h1 := trigWeight_le r n
  have h0 := norm_nonneg (mFourierCoeff ⇑F n)
  have hwt : wt 1 (2 * r) n = (1 + ab n) ^ (2 * r) := by simp [wt]
  rw [hwt]
  calc trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2
      ≤ ((r + 1) ^ 3 * ((2 * π) ^ 2) ^ r * (1 + ab n) ^ (2 * r)) * (‖mFourierCoeff ⇑F n‖ * M) := by
        rw [sq]
        exact mul_le_mul h1 (mul_le_mul_of_nonneg_left (hle n) h0) (by positivity)
          (by have := ab_nonneg n; positivity)
    _ = ((r : ℝ) + 1) ^ 3 * ((2 * π) ^ 2) ^ r * M * ((1 + ab n) ^ (2 * r) *
          ‖mFourierCoeff ⇑F n‖) := by ring

/-! ### The source of a transverse–traceless seed -/

theorem contDiff_sqσ (σ : TTSeed) : ContDiff ℝ ∞ (sqσ σ) := by
  have h : ∀ i j, ContDiff ℝ ∞ (fun y => σ.σ y i j) := fun i j =>
    contDiff_pi.1 (contDiff_pi.1 σ.smooth i) j
  unfold sqσ
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (h i j).pow 2

theorem contDiff_sqσC (σ : TTSeed) : ContDiff ℝ ∞ (fun y => ((sqσ σ y : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_sqσ σ)

theorem isPeriodic_sqσC (σ : TTSeed) : SobolevBoxCr.IsPeriodic (fun y => ((sqσ σ y : ℝ) : ℂ)) := by
  intro n y
  show ((sqσ σ (y + fun i => (n i : ℝ)) : ℝ) : ℂ) = ((sqσ σ y : ℝ) : ℂ)
  have : (y + fun i => (n i : ℝ)) = y + PeriodicCube.zvec n := rfl
  rw [this]
  simp only [sqσ, σ.per n y]

/-- **The source `δ𝖠 = |σ|²`** of the conformal Hamiltonian equation, on `𝕋³`. -/
def seedSource (σ : TTSeed) : CT := SobolevBoxCr.descend (contDiff_sqσC σ).continuous (isPeriodic_sqσC σ)

theorem seedSource_apply (σ : TTSeed) (y : Fin 3 → ℝ) :
    seedSource σ (torusMk y) = ((sqσ σ y : ℝ) : ℂ) :=
  descendFun_mk (isPeriodic_sqσC σ) y

theorem seedSource_wsum (σ : TTSeed) (k : ℕ) : WSum 1 k (seedSource σ) :=
  wsum_of_smooth (contDiff_sqσC σ) (isPeriodic_sqσC σ) k

theorem seedSource_memH (σ : TTSeed) (r : ℕ) : MemH r ⇑(seedSource σ) :=
  memH_of_wsum (seedSource_wsum σ (2 * r))

theorem seedSource_real (σ : TTSeed) : conjCT (seedSource σ) = seedSource σ := by
  ext t
  simp only [conjCT_apply, seedSource, SobolevBoxCr.descend, descendFun, ContinuousMap.coe_mk]
  exact Complex.conj_ofReal _

/-! ### The background data -/

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (P0 : V) (τ : ℝ)

/-- **Admissible background** (`eq:generated-background-coeffs`, `eq:generated-Lstar`): positive
Higgs-momentum coefficient `𝖠_* = 2κ|Π₀|² > 0` and the background Hamiltonian constraint
`⅔τ² - 2Λ - 2κλv⁴ = 𝖠_*`. -/
structure Background : Prop where
  pos : 0 < 2 * SM.κ * SM.ipV P0 P0
  bg : 2 / 3 * τ ^ 2 - 2 * SM.Λ - 2 * SM.κ * (SM.lamH * SM.vH ^ 4) = 2 * SM.κ * SM.ipV P0 P0

/-- The `LichData` of the background: `A_* = C_* = 2κ|Π₀|²`, `G_* = B_* = 0`, `μ_* = 12A_*`. -/
def bgData (hb : Background SM P0 τ) : LichData where
  A := 2 * SM.κ * SM.ipV P0 P0
  G := 0
  B := 0
  C := 2 * SM.κ * SM.ipV P0 P0
  μ := 12 * (2 * SM.κ * SM.ipV P0 P0)
  hC := by ring
  hμ := by ring
  μ_pos := by have := hb.pos; linarith


/-! ### The solver output -/

/-- The real lift `y ↦ Re F(y mod ℤ³)`. -/
def liftR (F : CT) (y : Fin 3 → ℝ) : ℝ := (F (torusMk y)).re

theorem wsum_zero (k : ℕ) : WSum 1 k (0 : CT) := by
  unfold WSum
  refine summable_zero.congr fun n => ?_
  rw [← coeffL_apply, map_zero, norm_zero, mul_zero]

theorem liftR_per (F : CT) : PeriodicCube.IsZPeriodic (liftR F) := by
  intro k y
  have := isPeriodic_lift F k y
  simp only at this
  show (F (torusMk (y + PeriodicCube.zvec k))).re = (F (torusMk y)).re
  rw [show (y + PeriodicCube.zvec k) = (y + fun i => (k i : ℝ)) from rfl, this]

/-- The real part of the conformal Hamiltonian residual at a real conformal factor. -/
theorem hamRes_re (D : LichData) (a W : ℝ) (L : ℂ) :
    (hamRes D (a : ℂ) 0 0 (W : ℂ) L).re =
      -8 * L.re - (D.A + a) * (W⁻¹) ^ 7 - D.G * W - D.B * (W⁻¹) ^ 3 + D.C * W ^ 5 := by
  have key : hamRes D (a : ℂ) 0 0 (W : ℂ) L =
      ((-8 * L.re - (D.A + a) * (W⁻¹) ^ 7 - D.G * W - D.B * (W⁻¹) ^ 3 + D.C * W ^ 5 : ℝ) : ℂ) +
        (-8) * (L - (L.re : ℂ)) := by
    unfold hamRes; push_cast; ring
  rw [key, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  simp

/-- **`prop:generated-initial`, actual-jet form**: for every transverse–traceless seed with small
source `‖|σ|²‖_{H^r} ≤ ε_r`, the conformal factor `w` of the Banach contraction is a smooth positive
periodic function (`1/2 < w < 3/2`) and the conformal Cauchy datum satisfies the complete
Hamiltonian, momentum and Gauss constraints. -/
theorem solver_constrained (hb : Background SM P0 τ)
    (hJ : ∀ (g gi : Met) (DH : Fin 4 → V), SM.Jcur g gi 0 DH 0 0 = 0) {r : ℕ} (hr : 2 ≤ r)
    (σ : TTSeed) (hη : sn r ⇑(seedSource σ) ≤ eps (bgData SM P0 τ hb) r hr) :
    ∃ w : CT, MemH (r + 2) ⇑w ∧ HamiltonianEq (bgData SM P0 τ hb) (seedSource σ) 0 0 w ∧
      sn (r + 2) ⇑(w - 1) ≤ 2 * cL (bgData SM P0 τ hb) * sn r ⇑(seedSource σ) ∧
      (∀ k, WSum 1 k w) ∧
      ∃ F : ConfFactor, F.w = liftR w ∧ (∀ y, 1 / 2 < F.w y ∧ F.w y < 3 / 2) ∧
        (confDatum (m := m) (S := S) (S' := S') F σ τ P0).Constrained SM := by
  set D := bgData SM P0 τ hb with hD
  have hη' : sn r ⇑(seedSource σ) + sn r ⇑(0 : CT) + sn r ⇑(0 : CT) ≤ eps D r hr := by
    rw [sn_zero_CT r, add_zero, add_zero]; exact hη
  obtain ⟨w, hw, hE, hbd, hsmall, -, hreal⟩ := lichnerowicz_solution D r hr (seedSource_memH σ r)
    (memH_zero r) (memH_zero r) hη'
  have hconj0 : conjCT (0 : CT) = 0 := by ext; simp
  have hre := hreal (seedSource_real σ) hconj0 hconj0
  rw [sn_zero_CT r, add_zero, add_zero] at hbd
  -- `u = w - 1`
  set u : CT := w - 1 with hu
  have hwu : w = 1 + u := by rw [hu]; abel
  have huH : MemH (r + 2) ⇑u := memH_sub hw (memH_const (r + 2) 1)
  have hE' : HamiltonianEq D (seedSource σ) 0 0 (1 + u) := by rw [← hwu]; exact hE
  -- the Wiener norm of `u` is `< 1`
  have hrad : sn (r + 2) ⇑u ≤ rad D r hr := by
    refine hbd.trans ?_
    have h1 : eps D r hr ≤ rad D r hr / (2 * cL D) := min_le_right _ _
    have h2 := cL_pos D
    have h3 : 2 * cL D * sn r ⇑(seedSource σ) ≤ 2 * cL D * (rad D r hr / (2 * cL D)) :=
      mul_le_mul_of_nonneg_left (hη.trans h1) (by positivity)
    rwa [mul_div_cancel₀ _ (by positivity)] at h3
  have hl1 : ∑' n, ‖mFourierCoeff ⇑u n‖ < 1 := by
    refine (tsum_norm_le_sn_two (memH_mono (by omega) huH)).trans_lt ?_
    have hc := Real.sqrt_nonneg cEmb
    have h4 : rad D r hr ≤ 1 / (4 * (Real.sqrt cEmb + 1)) := min_le_right _ _
    have h5 := sn_mono' (show 2 ≤ r + 2 by omega) huH
    have h6 : Real.sqrt cEmb * sn 2 ⇑u ≤ Real.sqrt cEmb * (1 / (4 * (Real.sqrt cEmb + 1))) :=
      mul_le_mul_of_nonneg_left (h5.trans (hrad.trans h4)) hc
    refine h6.trans_lt ?_
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    nlinarith
  -- regularity at all orders
  have hwsu := wsum_all_of_hamiltonianEq D hr huH hl1 (seedSource_wsum σ) wsum_zero wsum_zero hE'
  have hwsw : ∀ k, WSum 1 k w := fun k => by rw [hwu]; exact wsum_add (wsum_one' k) (hwsu k)
  -- the conformal factor on `ℝ³`
  have hsm : ContDiff ℝ ∞ (liftR w) := Complex.reCLM.contDiff.comp (contDiff_lift hwsw)
  have hpos : ∀ y, 0 < liftR w y := fun y => by
    have := (hre (torusMk y)).2.1; unfold liftR; linarith
  set F : ConfFactor := ⟨liftR w, hsm, liftR_per w, hpos⟩ with hF
  refine ⟨w, hw, hE, hbd, hwsw, F, rfl, fun y => ⟨(hre (torusMk y)).2.1, (hre (torusMk y)).2.2⟩, ?_⟩
  refine (constrained_iff_lichnerowicz SM F σ τ P0 hJ).2 fun y => ?_
  -- the Hamiltonian equation at `y`
  have hx := hE (torusMk y)
  have hWx : w (torusMk y) = ((F.w y : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hF, liftR]
    · simp [(hre (torusMk y)).1]
  have hδ := seedSource_apply σ y
  have hlap : (lap w (torusMk y)).re = lapR F.w y := by
    rw [← lapR_lift_re hwsw (fun x => (hre x).1) y, Fin.sum_univ_three]
    rfl
  rw [hWx, hδ] at hx
  simp only [ContinuousMap.zero_apply] at hx
  have hx' := congrArg Complex.re hx
  rw [hamRes_re, Complex.zero_re, hlap] at hx'
  unfold lichLHS
  have hbg := hb.bg
  simp only [hD, bgData] at hx'
  rw [hbg, inv_pow, inv_pow] at *
  linear_combination hx'


/-! ### The source bound `eq:generated-source-small` -/

theorem contDiff_seedC (σ : TTSeed) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun y => ((σ.σ y i j : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_pi.1 (contDiff_pi.1 σ.smooth i) j)

theorem isPeriodic_seedC (σ : TTSeed) (i j : Fin 3) :
    SobolevBoxCr.IsPeriodic (fun y => ((σ.σ y i j : ℝ) : ℂ)) := by
  intro n y
  show ((σ.σ (y + fun i => (n i : ℝ)) i j : ℝ) : ℂ) = ((σ.σ y i j : ℝ) : ℂ)
  have : (y + fun i => (n i : ℝ)) = y + PeriodicCube.zvec n := rfl
  rw [this, σ.per n y]

/-- The seed component `σᵢⱼ` on `𝕋³`. -/
def seedComp (σ : TTSeed) (i j : Fin 3) : CT :=
  SobolevBoxCr.descend (contDiff_seedC σ i j).continuous (isPeriodic_seedC σ i j)

theorem seedComp_memH (σ : TTSeed) (i j : Fin 3) (r : ℕ) : MemH r ⇑(seedComp σ i j) :=
  memH_of_wsum (wsum_of_smooth (contDiff_seedC σ i j) (isPeriodic_seedC σ i j) (2 * r))

theorem seedSource_eq (σ : TTSeed) :
    seedSource σ = ∑ i, ∑ j, seedComp σ i j * seedComp σ i j := by
  ext t
  simp only [seedSource, seedComp, SobolevBoxCr.descend, descendFun, ContinuousMap.coe_mk,
    ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.mul_apply, sqσ]
  push_cast
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem sn_sum_le {ι : Type*} (s : Finset ι) {r : ℕ} (F : ι → CT) (hF : ∀ i, MemH r ⇑(F i)) :
    MemH r ⇑(∑ i ∈ s, F i) ∧ sn r ⇑(∑ i ∈ s, F i) ≤ ∑ i ∈ s, sn r ⇑(F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty, sum_empty]
    exact ⟨memH_zero r, le_of_eq (sn_zero_CT r)⟩
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact ⟨memH_add (hF a) ih.1, (sn_add_le' (hF a) ih.1).trans (add_le_add le_rfl ih.2)⟩

/-- **`eq:generated-source-small`**: `‖δ𝖠‖_{H^r} = ‖|σ|²‖_{H^r} ≤ C Σᵢⱼ ‖σᵢⱼ‖²_{H^r}`. -/
theorem seedSource_small {r : ℕ} (hr : 2 ≤ r) :
    ∃ C ≥ 0, ∀ σ : TTSeed, sn r ⇑(seedSource σ) ≤ C * ∑ i, ∑ j, sn r ⇑(seedComp σ i j) ^ 2 := by
  obtain ⟨K, hK, hmul⟩ := memH_mul r hr
  refine ⟨K, hK, fun σ => ?_⟩
  have hc := fun i j => seedComp_memH σ i j r
  have hsq : ∀ i j, MemH r ⇑(seedComp σ i j * seedComp σ i j) ∧
      sn r ⇑(seedComp σ i j * seedComp σ i j) ≤ K * sn r ⇑(seedComp σ i j) ^ 2 := fun i j => by
    obtain ⟨h1, h2⟩ := hmul _ _ (hc i j) (hc i j)
    exact ⟨h1, by rw [sq, ← mul_assoc]; exact h2⟩
  have hrow : ∀ i, MemH r ⇑(∑ j, seedComp σ i j * seedComp σ i j) ∧
      sn r ⇑(∑ j, seedComp σ i j * seedComp σ i j) ≤ ∑ j, K * sn r ⇑(seedComp σ i j) ^ 2 :=
    fun i => let h := sn_sum_le univ _ (fun j => (hsq i j).1)
      ⟨h.1, h.2.trans (sum_le_sum fun j _ => (hsq i j).2)⟩
  have htot := sn_sum_le univ _ (fun i => (hrow i).1)
  rw [seedSource_eq]
  refine htot.2.trans ((sum_le_sum fun i _ => (hrow i).2).trans (le_of_eq ?_))
  rw [mul_sum]
  exact sum_congr rfl fun i _ => by rw [mul_sum]

/-! ### Composition with the Cauchy-data completion -/

/-- **The constrained-initial solver produces constrained actual-jet data**
(`prop:generated-initial` → `lem:generated-physical-identification`): for theory data with
smooth bosonic residual fields and symmetric stress, every TT seed with small source gives a
smooth conformal factor whose conformal Cauchy datum completes to a slice-constrained tuple; its
actual-jet state is a `GenPhysIdClosed.ConstrainedData` datum. -/
theorem solver_constrainedData (hB : ∀ z : Tuple m V S S', ContDiff ℝ ∞ (bosF SM z))
    (hT : GenSlice.StressSymm SM) (hb : Background SM P0 τ)
    (hJ : ∀ (g gi : Met) (DH : Fin 4 → V), SM.Jcur g gi 0 DH 0 0 = 0) {r : ℕ} (hr : 2 ≤ r)
    (σ : TTSeed) (hη : sn r ⇑(seedSource σ) ≤ eps (bgData SM P0 τ hb) r hr)
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) :
    ∃ (w : CT) (F : ConfFactor) (z : Tuple m V S S'),
      MemH (r + 2) ⇑w ∧ HamiltonianEq (bgData SM P0 τ hb) (seedSource σ) 0 0 w ∧
      sn (r + 2) ⇑(w - 1) ≤ 2 * cL (bgData SM P0 τ hb) * sn r ⇑(seedSource σ) ∧
      F.w = liftR w ∧ (∀ y, 1 / 2 < F.w y ∧ F.w y < 3 / 2) ∧
      (confDatum (m := m) (S := S) (S' := S') F σ τ P0).Constrained SM ∧
      SliceConstrained SM z ∧ ConstrainedData SM κ (stU κ SM z) ∧
      ∀ y : Fin 3 → ℝ,
        z.g (Fin.cons 0 y) = met4 (-1) 0 (confγ F.w y) ∧
        pd z.g 0 (Fin.cons 0 y) = (confDatum (m := m) (S := S) (S' := S') F σ τ P0).vt y ∧
        z.H (Fin.cons 0 y) = 0 ∧ pd z.H 0 (Fin.cons 0 y) = (F.w y ^ 6)⁻¹ • P0 ∧
        z.ψ (Fin.cons 0 y) = 0 ∧ z.ψb (Fin.cons 0 y) = 0 := by
  obtain ⟨w, hw, hE, hbd, -, F, hF, hbds, hc⟩ := solver_constrained SM P0 τ hb hJ hr σ hη
  obtain ⟨z, hz, hcd, hd⟩ := (confDatum (m := m) (S := S) (S' := S') F σ τ P0).constrainedData
    hB hT hc κ
  refine ⟨w, F, z, hw, hE, hbd, hF, hbds, hc, hz, hcd, fun y => ?_⟩
  obtain ⟨h1, h2, -, -, h5, h6, h7, h8⟩ := hd y
  exact ⟨h1, h2, h5, h6, h7, h8⟩

end

end RenewalGeometry.GenSlice.ConfSolver
