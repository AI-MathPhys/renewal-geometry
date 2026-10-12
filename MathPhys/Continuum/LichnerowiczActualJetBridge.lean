/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Continuum.ActualJetSliceConstrained
import MathPhys.Continuum.LichnerowiczContraction

/-!
# The conformal method in actual-jet variables: the Lichnerowicz equation is the Hamiltonian row

Einstein–Standard-Model action-closure manuscript, `prop:generated-initial`
(`eq:generated-background-coeffs`, `eq:generated-Lstar`, `eq:generated-Hamiltonian`) and
`ass:constrained-initial-solver` ("the chosen conformal weights and matter data give the scalar
equation").  We assemble Cauchy slice data from a conformal factor `w > 0`, a transverse–traceless
seed `σ` (`∂ʲσ_{ji} = 0`, `tr σ = 0`), a constant mean curvature `τ` and a constant Higgs normal
momentum `P0` (the paper's spatially homogeneous background with zero gauge field and zero
spinor), in the unit-lapse zero-shift temporal gauge:

`γ = w⁴δ`, `K = w⁻²σ + (τ/3)w⁴δ`, `A = Ȧ = 0`, `H = 0`, `Ḣ = w⁻⁶P0`, `Ψ = Ψ̄ = 0`.

**Proved identities** (no conformal identity is assumed):

* `scal_conf`: `R(w⁴δ) = -8w⁻⁵Δw` (3-jet computation);
* `trK_conf`, `normK2_conf`: `tr_γK = τ`, `|K|²_γ = w⁻¹²|σ|² + τ²/3`;
* `momC_conf`: the momentum constraint expression `∇^jK_{ji} - ∂ᵢtr_γK` vanishes for a TT seed;
* `Tsl_conf`: the stress of the data: `T₀₀ = |Π|² + λv⁴` (`Π = w⁻⁶P0`, Higgs stress of
  `eq:H-stress`), `T₀ᵢ = 0`; `gaussRow_conf`: the Gauss row vanishes when the Yang–Mills source
  vanishes at zero Higgs field and zero spinors;
* **`constrained_iff_lichnerowicz`**: the slice datum satisfies the complete Einstein, gauge and
  matter initial constraints (`SliceCauchy.Constrained`) **iff** `w` solves the conformal
  Hamiltonian equation `eq:generated-Hamiltonian`
  `-8Δw - 𝖠w⁻⁷ + C w⁵ = 0`, `𝖠 = 2κ|P0|² + |σ|²` (`A_*⁰ = 2κ|P0|²`, `δ𝖠 = |σ|²`),
  `C = ⅔τ² - 2Λ - 2κλv⁴`, i.e. `G_*⁰ = B_*⁰ = 0`, `𝖡 = 𝖸 = 0`.
-/

open Finset
open scoped ContDiff

noncomputable section

namespace MathPhys.GenSlice.Conf

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState ActualJetGauge
  ActualJetSpinor SpinorProlongation SliceExt GenHarmonic GenStress GenConstraint GenPhysIdClosed
  ActualJetRecon ContractedBianchiJet

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Jet algebra of conformally flat slices -/

set_option maxHeartbeats 4000000 in
/-- **The scalar curvature of a conformally flat 3-metric** `w⁴δ`: `R = -8w⁻⁵Δw`
(`p = ∂w`, `q = ∂∂w`). -/
theorem scal_conf (w : ℝ) (hw : w ≠ 0) (p : Fin 3 → ℝ) (q : Fin 3 → Fin 3 → ℝ) :
    (⟨(w ^ 4) • (1 : Matrix (Fin 3) (Fin 3) ℝ), (w ^ 4)⁻¹ • 1, fun k => (4 * w ^ 3 * p k) • 1,
      fun k l => (12 * w ^ 2 * p k * p l + 4 * w ^ 3 * q k l) • 1, fun _ _ _ => 0⟩ :
      Jet3 (Fin 3)).scal = -8 * (w ^ 5)⁻¹ * (q 0 0 + q 1 1 + q 2 2) := by
  simp only [Jet3.scal, Jet3.ricM, Jet3.riem, Jet3.dchr, Jet3.chr, Jet3.low, Jet3.dlow,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply,
    Matrix.one_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply,
    smul_eq_mul]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, mul_one, mul_zero, zero_add, add_zero]
  field_simp
  ring

/-- The conformally flat slice jet with extrinsic curvature `w⁻²σ + (τ/3)w⁴δ`. -/
def confSD (w : ℝ) (p : Fin 3 → ℝ) (q : Fin 3 → Fin 3 → ℝ) (τ : ℝ)
    (σ : Matrix (Fin 3) (Fin 3) ℝ) (dσ : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) (v00 : ℝ)
    (v0 dv00 : Fin 3 → ℝ) (dv0 : Fin 3 → Fin 3 → ℝ) (W : Matrix (Fin 4) (Fin 4) ℝ) : SliceData :=
  ⟨(w ^ 4) • (1 : Matrix (Fin 3) (Fin 3) ℝ), (w ^ 4)⁻¹ • 1, fun k => (4 * w ^ 3 * p k) • 1,
    fun k l => (12 * w ^ 2 * p k * p l + 4 * w ^ 3 * q k l) • 1,
    (w ^ 2)⁻¹ • σ + (τ / 3 * w ^ 4) • 1,
    fun k => (-2 * (w ^ 3)⁻¹ * p k) • σ + (w ^ 2)⁻¹ • dσ k + (4 / 3 * τ * w ^ 3 * p k) • 1,
    v00, v0, dv00, dv0, W⟩

section ConfAlg

variable (w : ℝ) (hw : w ≠ 0) (p : Fin 3 → ℝ) (q : Fin 3 → Fin 3 → ℝ) (τ : ℝ)
  (σ : Matrix (Fin 3) (Fin 3) ℝ) (dσ : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) (v00 : ℝ)
  (v0 dv00 : Fin 3 → ℝ) (dv0 : Fin 3 → Fin 3 → ℝ) (W : Matrix (Fin 4) (Fin 4) ℝ)
include hw

theorem trK_conf (htr : σ 0 0 + σ 1 1 + σ 2 2 = 0) :
    (confSD w p q τ σ dσ v00 v0 dv00 dv0 W).trK = τ := by
  simp only [confSD, SliceData.trK, Fin.sum_univ_three, Matrix.smul_apply, Matrix.one_apply,
    Matrix.add_apply, smul_eq_mul]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, mul_one, mul_zero, zero_add, add_zero]
  field_simp
  linear_combination 3 * htr

set_option maxHeartbeats 4000000 in
theorem normK2_conf (hs : ∀ i j, σ i j = σ j i) (htr : σ 0 0 + σ 1 1 + σ 2 2 = 0) :
    (confSD w p q τ σ dσ v00 v0 dv00 dv0 W).normK2 =
      (w ^ 12)⁻¹ * ∑ i, ∑ j, σ i j ^ 2 + τ ^ 2 / 3 := by
  have h10 : σ 1 0 = σ 0 1 := hs 1 0
  have h20 : σ 2 0 = σ 0 2 := hs 2 0
  have h21 : σ 2 1 = σ 1 2 := hs 2 1
  simp only [confSD, SliceData.normK2, Fin.sum_univ_three, Matrix.smul_apply, Matrix.one_apply,
    Matrix.add_apply, smul_eq_mul]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, mul_one, mul_zero, zero_add, add_zero,
    h10, h20, h21]
  field_simp
  linear_combination (6 * τ * w ^ 6) * htr

set_option maxHeartbeats 4000000 in
theorem momC_conf (hs : ∀ i j, σ i j = σ j i)
    (htr : σ 0 0 + σ 1 1 + σ 2 2 = 0) (hdtr : ∀ k, dσ k 0 0 + dσ k 1 1 + dσ k 2 2 = 0)
    (hdiv : ∀ i, dσ 0 0 i + dσ 1 1 i + dσ 2 2 i = 0) (i : Fin 3) :
    (confSD w p q τ σ dσ v00 v0 dv00 dv0 W).momC i = 0 := by
  have h10 : σ 1 0 = σ 0 1 := hs 1 0
  have h20 : σ 2 0 = σ 0 2 := hs 2 0
  have h21 : σ 2 1 = σ 1 2 := hs 2 1
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  all_goals simp only [confSD, SliceData.momC, SliceData.divK, SliceData.dtrK, SliceData.spatial,
      Jet3.chr, Jet3.low, Jet3.dG, Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply,
      Matrix.one_apply, Matrix.of_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  all_goals simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, mul_one, mul_zero, zero_add,
      add_zero, h10, h20, h21]
  all_goals field_simp
  · linear_combination 24 * w ^ 3 * p 0 * htr + 6 * w ^ 4 * (hdiv 0 - hdtr 0)
  · linear_combination 24 * w ^ 3 * p 1 * htr + 6 * w ^ 4 * (hdiv 1 - hdtr 1)
  · linear_combination 24 * w ^ 3 * p 2 * htr + 6 * w ^ 4 * (hdiv 2 - hdtr 2)

/-- **The Hamiltonian constraint expression of a conformally flat TT slice**:
`R(γ) + (tr_γK)² - |K|²_γ = -8w⁻⁵Δw + ⅔τ² - w⁻¹²|σ|²`. -/
theorem hamC_conf (hs : ∀ i j, σ i j = σ j i) (htr : σ 0 0 + σ 1 1 + σ 2 2 = 0) :
    (confSD w p q τ σ dσ v00 v0 dv00 dv0 W).hamC =
      -8 * (w ^ 5)⁻¹ * (q 0 0 + q 1 1 + q 2 2) + 2 / 3 * τ ^ 2 -
        (w ^ 12)⁻¹ * ∑ i, ∑ j, σ i j ^ 2 := by
  rw [SliceData.hamC, trK_conf w hw p q τ σ dσ v00 v0 dv00 dv0 W htr,
    normK2_conf w hw p q τ σ dσ v00 v0 dv00 dv0 W hs htr]
  have : (confSD w p q τ σ dσ v00 v0 dv00 dv0 W).spatial.scal =
      -8 * (w ^ 5)⁻¹ * (q 0 0 + q 1 1 + q 2 2) := scal_conf w hw p q
  rw [this]
  ring

end ConfAlg


/-! ### Scalar calculus on `ℝ³` -/

section Calc

variable {w : (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ}

theorem pd3_comp (hw : DifferentiableAt ℝ w y) {φ : ℝ → ℝ} {φ' : ℝ} (hφ : HasDerivAt φ φ' (w y))
    (k : Fin 3) : pd (fun y => φ (w y)) k y = φ' * pd w k y := by
  unfold SobolevOpen.pd
  have h := hφ.hasFDerivAt.comp y hw.hasFDerivAt
  rw [show (fun y => φ (w y)) = φ ∘ w from rfl, h.fderiv]
  simp [smul_eq_mul, mul_comm]

theorem pd3_pow (hw : DifferentiableAt ℝ w y) (n : ℕ) (k : Fin 3) :
    pd (fun y => w y ^ n) k y = n * w y ^ (n - 1) * pd w k y :=
  pd3_comp hw (hasDerivAt_pow n (w y)) k

theorem pd3_inv_sq (hw : DifferentiableAt ℝ w y) (h0 : w y ≠ 0) (k : Fin 3) :
    pd (fun y => (w y ^ 2)⁻¹) k y = -2 * (w y ^ 3)⁻¹ * pd w k y := by
  have hφ : HasDerivAt (fun x : ℝ => (x ^ 2)⁻¹) (-2 * (w y ^ 3)⁻¹) (w y) := by
    have := (hasDerivAt_pow 2 (w y)).inv (pow_ne_zero 2 h0)
    refine this.congr_deriv ?_
    norm_num
    field_simp
  exact pd3_comp hw hφ k

theorem pd3_mul' {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : Fin 3)
    (y : Fin 3 → ℝ) : pd (fun y => f y * g y) k y = pd f k y * g y + f y * pd g k y :=
  SobolevOpen.pd_mul (hf.of_le (by norm_cast)) (hg.of_le (by norm_cast)) k y

end Calc

/-! ### The conformal Cauchy datum -/

/-- **A transverse–traceless seed** on `𝕋³`: smooth, periodic, symmetric, traceless and
divergence-free (`∂ʲσ_{ji} = 0`) with respect to the flat metric. -/
structure TTSeed where
  σ : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ
  smooth : ContDiff ℝ ∞ σ
  per : IsZPeriodic σ
  symm : ∀ y i j, σ y i j = σ y j i
  tr : ∀ y, σ y 0 0 + σ y 1 1 + σ y 2 2 = 0
  div : ∀ y i, pd σ 0 y 0 i + pd σ 1 y 1 i + pd σ 2 y 2 i = 0

/-- **A conformal factor**: smooth, periodic, positive. -/
structure ConfFactor where
  w : (Fin 3 → ℝ) → ℝ
  smooth : ContDiff ℝ ∞ w
  per : IsZPeriodic w
  pos : ∀ y, 0 < w y

namespace ConfFactor

variable (F : ConfFactor)

theorem ne (y : Fin 3 → ℝ) : F.w y ≠ 0 := (F.pos y).ne'

theorem diff (y : Fin 3 → ℝ) : DifferentiableAt ℝ F.w y :=
  (F.smooth.differentiable (by simp)) y

theorem contDiff_inv_pow (n : ℕ) : ContDiff ℝ ∞ (fun y => (F.w y ^ n)⁻¹) :=
  (F.smooth.pow n).inv fun y => pow_ne_zero n (F.ne y)

end ConfFactor

/-- `γ = w⁴δ`. -/
def confγ (w : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) (i j : Fin 3) : ℝ := if i = j then w y ^ 4 else 0

/-- `K = w⁻²σ + (τ/3)w⁴δ`. -/
def confK (w : (Fin 3 → ℝ) → ℝ) (σ : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ) (τ : ℝ) (y : Fin 3 → ℝ)
    (i j : Fin 3) : ℝ :=
  (w y ^ 2)⁻¹ * σ y i j + if i = j then τ / 3 * w y ^ 4 else 0

theorem met4_diag_mul (a : ℝ) (ha : a ≠ 0) :
    Matrix.of (met4 (-1) 0 (fun i j => if i = j then a else 0)) *
      Matrix.of (met4 (-1) 0 (fun i j => if i = j then a⁻¹ else 0)) = 1 := by
  ext μ ν
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν
  · simp
  · simp [Fin.succ_ne_zero, Matrix.one_apply, (Fin.succ_ne_zero j).symm]
  · simp [Fin.succ_ne_zero, Matrix.one_apply]
  · simp only [Matrix.of_apply, met4_succ_zero, met4_succ_succ, Pi.zero_apply, zero_mul, zero_add,
      Matrix.one_apply, Fin.succ_inj]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : i = j
    · subst h; simp [ha]
    · simp [h]

theorem ginvOf_met4_diag (a : ℝ) (ha : a ≠ 0) :
    ginvOf (met4 (-1) 0 (fun i j => if i = j then a else 0)) =
      met4 (-1) 0 (fun i j => if i = j then a⁻¹ else 0) := by
  funext μ ν
  unfold ginvOf
  rw [Matrix.inv_eq_right_inv (met4_diag_mul a ha)]
  rfl

theorem gchart_met4_diag (a : ℝ) (ha : 0 < a) :
    GChart (met4 (-1) 0 (fun i j => if i = j then a else 0)) := by
  refine ⟨Matrix.det_ne_zero_of_right_inverse (met4_diag_mul a ha.ne'), ?_⟩
  rw [ginvOf_met4_diag a ha.ne']
  have hb : 0 < a⁻¹ := inv_pos.2 ha
  have e : ∀ i j : Fin 3, met4 (-1) 0 (fun i j => if i = j then a⁻¹ else 0) i.succ j.succ =
      if i = j then a⁻¹ else 0 := fun _ _ => rfl
  have e0 : ∀ j : Fin 3, met4 (-1) 0 (fun i j => if i = j then a⁻¹ else 0) 0 j.succ = 0 :=
    fun _ => rfl
  have h00 : met4 (-1) 0 (fun i j => if i = j then a⁻¹ else 0) 0 0 = -1 := rfl
  refine ⟨by rw [h00]; norm_num, ?_, ?_, ?_⟩
  · simp only [hInv, e, e0, h00]; simp [hb]
  · simp only [hInv, L10, L00, e, e0, h00]; simp [hb]
  · simp only [hInv, L20, L21, L10, L00, L11, e, e0, h00]; simp [hb]

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

section Datum

variable (F : ConfFactor) (σ : TTSeed) (τ : ℝ) (P0 : V)

theorem contDiff_confγ : ContDiff ℝ ∞ (confγ F.w) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  unfold confγ
  split_ifs
  · exact F.smooth.pow 4
  · exact contDiff_const

theorem contDiff_confK : ContDiff ℝ ∞ (confK F.w σ.σ τ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  unfold confK
  have h1 := F.contDiff_inv_pow 2
  have h2 : ContDiff ℝ ∞ (fun y => σ.σ y i j) := contDiff_pi.1 (contDiff_pi.1 σ.smooth i) j
  split_ifs
  · exact (h1.mul h2).add (contDiff_const.mul (F.smooth.pow 4))
  · exact (h1.mul h2).add contDiff_const

/-- **The conformal Cauchy datum** `γ = w⁴δ`, `K = w⁻²σ + (τ/3)w⁴δ`, `A = Ȧ = 0`, `H = 0`,
`Ḣ = w⁻⁶P0`, `Ψ = Ψ̄ = 0`. -/
def confDatum : SliceCauchy m V S S' where
  γ := confγ F.w
  K := confK F.w σ.σ τ
  A := fun _ => 0
  Ad := fun _ => 0
  H := fun _ => 0
  Hd := fun y => (F.w y ^ 6)⁻¹ • P0
  ψ := fun _ => 0
  ψb := fun _ => 0
  γ_smooth := contDiff_confγ F
  K_smooth := contDiff_confK F σ τ
  A_smooth := contDiff_const
  Ad_smooth := contDiff_const
  H_smooth := contDiff_const
  Hd_smooth := (F.contDiff_inv_pow 6).smul contDiff_const
  ψ_smooth := contDiff_const
  ψb_smooth := contDiff_const
  γ_per := fun k y => by
    funext i j
    show (if i = j then F.w (y + zvec k) ^ 4 else 0) = (if i = j then F.w y ^ 4 else 0)
    rw [F.per k y]
  K_per := fun k y => by
    funext i j
    show (F.w (y + zvec k) ^ 2)⁻¹ * σ.σ (y + zvec k) i j +
        (if i = j then τ / 3 * F.w (y + zvec k) ^ 4 else 0) =
      (F.w y ^ 2)⁻¹ * σ.σ y i j + (if i = j then τ / 3 * F.w y ^ 4 else 0)
    rw [F.per k y, σ.per k y]
  A_per := fun _ _ => rfl
  Ad_per := fun _ _ => rfl
  H_per := fun _ _ => rfl
  Hd_per := fun k y => by
    show (F.w (y + zvec k) ^ 6)⁻¹ • P0 = (F.w y ^ 6)⁻¹ • P0
    rw [F.per k y]
  ψ_per := fun _ _ => rfl
  ψb_per := fun _ _ => rfl
  γ_symm := fun y i j => by unfold confγ; split_ifs with h1 h2 h2 <;> simp_all
  K_symm := fun y i j => by
    unfold confK; rw [σ.symm y i j]; split_ifs with h1 h2 h2 <;> simp_all
  chart := fun y => gchart_met4_diag _ (pow_pos (F.pos y) 4)

end Datum


/-! ### The slice jet of the conformal datum -/

section SliceJet

variable (F : ConfFactor) (σ : TTSeed) (τ : ℝ) (P0 : V)

theorem γi_conf (y : Fin 3 → ℝ) (i j : Fin 3) :
    (confDatum (m := m) (S := S) (S' := S') F σ τ P0).γi y i j =
      if i = j then (F.w y ^ 4)⁻¹ else 0 := by
  show ginvOf (met4 (-1) 0 (confγ F.w y)) i.succ j.succ = _
  rw [show confγ F.w y = fun i j => if i = j then F.w y ^ 4 else 0 from rfl,
    ginvOf_met4_diag _ (pow_ne_zero 4 (F.ne y))]
  rfl

theorem pd_confγ (y : Fin 3 → ℝ) (k i j : Fin 3) :
    pd (confγ F.w) k y i j = if i = j then 4 * F.w y ^ 3 * pd F.w k y else 0 := by
  rw [← pd3_apply ((contDiff_confγ F).differentiable (by simp) y) k i,
    ← pd3_apply (((contDiff_pi.1 (contDiff_confγ F) i)).differentiable (by simp) y) k j]
  unfold confγ
  split_ifs
  · rw [pd3_pow (F.diff y) 4 k]; norm_num
  · exact pd3_const 0 k y

theorem pd_confγ_fun (k : Fin 3) :
    pd (confγ F.w) k = fun y i j => if i = j then 4 * F.w y ^ 3 * pd F.w k y else 0 :=
  funext fun y => funext fun i => funext fun j => pd_confγ F y k i j

theorem pd3_add {f g : (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (k : Fin 3) :
    pd (fun y => f y + g y) k y = pd f k y + pd g k y := by
  unfold SobolevOpen.pd
  rw [show (fun y => f y + g y) = f + g from rfl, fderiv_add hf hg]
  rfl

theorem pd_pd_confγ (y : Fin 3 → ℝ) (k l i j : Fin 3) :
    pd (pd (confγ F.w) l) k y i j = if i = j then
      12 * F.w y ^ 2 * pd F.w k y * pd F.w l y + 4 * F.w y ^ 3 * pd (pd F.w l) k y else 0 := by
  have hc : ContDiff ℝ ∞ (fun (y : Fin 3 → ℝ) (i j : Fin 3) =>
      if i = j then 4 * F.w y ^ 3 * pd F.w l y else (0 : ℝ)) := by
    rw [← pd_confγ_fun F l]; exact contDiff_pd3 (contDiff_confγ F) l
  rw [pd_confγ_fun F l, ← pd3_apply (hc.differentiable (by simp) y) k i,
    ← pd3_apply ((contDiff_pi.1 hc i).differentiable (by simp) y) k j]
  by_cases h : i = j
  · simp only [h, if_true]
    have h1 : ContDiff ℝ ∞ (fun y => 4 * F.w y ^ 3) := contDiff_const.mul (F.smooth.pow 3)
    have h2 : ContDiff ℝ ∞ (pd F.w l) := contDiff_pd3 F.smooth l
    rw [pd3_mul' h1 h2 k y]
    have hφ : HasDerivAt (fun x : ℝ => 4 * x ^ 3) (4 * ((3 : ℕ) * F.w y ^ (3 - 1))) (F.w y) :=
      (hasDerivAt_pow 3 (F.w y)).const_mul 4
    rw [pd3_comp (F.diff y) hφ k]
    simp only [Nat.cast_ofNat, Nat.reduceSub]
    ring
  · simp only [h, if_false]
    exact pd3_const 0 k y

theorem pd_σ (y : Fin 3 → ℝ) (k i j : Fin 3) :
    pd (fun y => σ.σ y i j) k y = pd σ.σ k y i j := by
  rw [pd3_apply (F := fun y => σ.σ y i) ((contDiff_pi.1 σ.smooth i).differentiable (by simp) y) k j,
    pd3_apply (F := σ.σ) ((σ.smooth.differentiable (by simp)) y) k i]

theorem pd_confK (y : Fin 3 → ℝ) (k i j : Fin 3) :
    pd (confK F.w σ.σ τ) k y i j = -2 * (F.w y ^ 3)⁻¹ * pd F.w k y * σ.σ y i j +
      (F.w y ^ 2)⁻¹ * pd σ.σ k y i j + (if i = j then 4 / 3 * τ * F.w y ^ 3 * pd F.w k y else 0) := by
  rw [← pd3_apply ((contDiff_confK F σ τ).differentiable (by simp) y) k i,
    ← pd3_apply (((contDiff_pi.1 (contDiff_confK F σ τ) i)).differentiable (by simp) y) k j]
  have h1 := F.contDiff_inv_pow 2
  unfold confK
  by_cases h : i = j
  · subst h
    simp only [if_true]
    have h2 : ContDiff ℝ ∞ (fun y => σ.σ y i i) := contDiff_pi.1 (contDiff_pi.1 σ.smooth i) i
    have h3 : ContDiff ℝ ∞ (fun y => τ / 3 * F.w y ^ 4) := contDiff_const.mul (F.smooth.pow 4)
    rw [pd3_add ((h1.mul h2).differentiable (by simp) y) (h3.differentiable (by simp) y) k,
      pd3_mul' h1 h2 k y, pd3_inv_sq (F.diff y) (F.ne y) k, pd_σ σ y k i i]
    have hφ : HasDerivAt (fun x : ℝ => τ / 3 * x ^ 4) (τ / 3 * ((4 : ℕ) * F.w y ^ (4 - 1))) (F.w y) :=
      (hasDerivAt_pow 4 (F.w y)).const_mul (τ / 3)
    rw [pd3_comp (F.diff y) hφ k]
    simp only [Nat.cast_ofNat, Nat.reduceSub]
    ring
  · simp only [h, if_false, add_zero]
    have h2 : ContDiff ℝ ∞ (fun y => σ.σ y i j) := contDiff_pi.1 (contDiff_pi.1 σ.smooth i) j
    rw [pd3_mul' h1 h2 k y, pd3_inv_sq (F.diff y) (F.ne y) k, pd_σ σ y k i j]

/-- **The slice jet of the conformal datum is the conformally flat TT jet** `confSD`. -/
theorem sd_conf (y : Fin 3 → ℝ) :
    (confDatum (m := m) (S := S) (S' := S') F σ τ P0).sd 0 y =
      confSD (F.w y) (fun k => pd F.w k y) (fun k l => pd (pd F.w l) k y) τ (Matrix.of (σ.σ y))
        (fun k => Matrix.of (pd σ.σ k y))
        ((confDatum (m := m) (S := S) (S' := S') F σ τ P0).v00 y)
        ((confDatum (m := m) (S := S) (S' := S') F σ τ P0).v0 y)
        (fun k => pd (confDatum (m := m) (S := S) (S' := S') F σ τ P0).v00 k y)
        (fun k => pd (confDatum (m := m) (S := S) (S' := S') F σ τ P0).v0 k y) 0 := by
  simp only [SliceCauchy.sd, confSD]
  congr 1
  · ext i j; simp [confDatum, confγ, Matrix.one_apply]
  · ext i j; simp only [Matrix.of_apply, γi_conf, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  · funext k; ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [show (confDatum (m := m) (S := S) (S' := S') F σ τ P0).γ = confγ F.w from rfl, pd_confγ]
    split_ifs <;> simp
  · funext k l; ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [show (confDatum (m := m) (S := S) (S' := S') F σ τ P0).γ = confγ F.w from rfl, pd_pd_confγ]
    split_ifs <;> simp
  · ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    show confK F.w σ.σ τ y i j = _
    unfold confK
    split_ifs <;> simp
  · funext k; ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    rw [show (confDatum (m := m) (S := S) (S' := S') F σ τ P0).K = confK F.w σ.σ τ from rfl,
      pd_confK]
    split_ifs <;> simp

end SliceJet


/-! ### The matter rows of the conformal datum -/

section Matter

variable (SM : SMData (MatLie m) V S S') (F : ConfFactor) (σ : TTSeed) (τ : ℝ) (P0 : V)

/-- The first jets of the conformal datum on the slice (base completion). -/
theorem firstJet_conf (y : Fin 3 → ℝ) :
    let J := ((confDatum (m := m) (S := S) (S' := S') F σ τ P0).base).jet (Fin.cons 0 y)
    (J.firstJet SM).g = met4 (-1) 0 (confγ F.w y) ∧
      (J.firstJet SM).gi = met4 (-1) 0 (fun i j => if i = j then (F.w y ^ 4)⁻¹ else 0) ∧
      (J.firstJet SM).F = 0 ∧ (J.firstJet SM).H = 0 ∧
      (J.firstJet SM).DH = (fun μ => Fin.cases ((F.w y ^ 6)⁻¹ • P0) (fun _ => 0) μ) ∧
      (J.firstJet SM).ψ = 0 ∧ (J.firstJet SM).ψb = 0 ∧ J.A = 0 ∧ J.dA = 0 ∧ J.ddA = 0 := by
  intro J
  set D := confDatum (m := m) (S := S) (S' := S') F σ τ P0
  have hch := D.exists_eps0.choose_spec.2
  have hε := D.ε0_ne
  have hA : J.A = 0 := by
    show D.base.A (Fin.cons 0 y) = 0
    rw [D.mk_A (hch := hch) y]; funext μ; refine Fin.cases rfl (fun j => rfl) μ
  have hdA : J.dA = 0 := by
    funext γ μ
    show pd D.base.A γ (Fin.cons 0 y) μ = 0
    rw [D.mk_dA (hch := hch) y hε γ]
    refine Fin.cases ?_ (fun j => ?_) γ
    · refine Fin.cases rfl (fun j => rfl) μ
    · simp only [Fin.cases_succ]
      rw [show (fun y : Fin 3 → ℝ => padL (D.A y)) = fun _ => (0 : Fin 4 → MatLie m) by
        funext y; funext μ; refine Fin.cases rfl (fun j => rfl) μ, pd3_const]
      rfl
  have hddA : J.ddA = 0 := by
    funext δ γ μ
    show pd (pd D.base.A γ) δ (Fin.cons 0 y) μ = 0
    have h0 : (fun y : Fin 3 → ℝ => padL (D.A y)) = fun _ => (0 : Fin 4 → MatLie m) := by
      funext y; funext μ; refine Fin.cases rfl (fun j => rfl) μ
    have h1 : (fun y : Fin 3 → ℝ => padL (D.Ad y)) = fun _ => (0 : Fin 4 → MatLie m) := by
      funext y; funext μ; refine Fin.cases rfl (fun j => rfl) μ
    have h2 : padL ((Params.zero (m := m) (V := V) (S := S) (S' := S')).Aa y) = 0 := by
      funext μ; refine Fin.cases rfl (fun j => rfl) μ
    rw [D.mk_ddA (hch := hch) y hε δ γ]
    refine Fin.cases ?_ (fun k => ?_) δ <;> refine Fin.cases ?_ (fun j => ?_) γ
    · simp only [Fin.cases_zero]; rw [h2]; rfl
    · simp only [Fin.cases_zero, Fin.cases_succ]; rw [h1, pd3_const]; rfl
    · simp only [Fin.cases_zero, Fin.cases_succ]; rw [h1, pd3_const]; rfl
    · simp only [Fin.cases_succ]
      rw [h0, show pd (fun _ : Fin 3 → ℝ => (0 : Fin 4 → MatLie m)) j = fun _ => 0 from
        funext fun y => pd3_const 0 j y, pd3_const]
      rfl
  have hH : J.H = 0 := D.mk_H (hch := hch) y
  have hdH : J.dH = fun μ => Fin.cases ((F.w y ^ 6)⁻¹ • P0) (fun _ => 0) μ := by
    funext μ
    show pd D.base.H μ (Fin.cons 0 y) = _
    rw [D.mk_dH (hch := hch) y hε μ]
    refine Fin.cases rfl (fun j => ?_) μ
    simp only [Fin.cases_succ]
    exact pd3_const 0 j y
  refine ⟨D.mk_g (hch := hch) y, ?_, ?_, hH, ?_, D.mk_ψ (hch := hch) y, D.mk_ψb (hch := hch) y,
    hA, hdA, hddA⟩
  · show D.base.gi (Fin.cons 0 y) = _
    rw [D.mk_gi (hch := hch) y]
    congr 1
    funext i j
    exact γi_conf F σ τ P0 y i j
  · show Fm J.A J.dA = 0
    rw [hA, hdA]
    funext μ ν
    simp [Fm, fieldStrength]
  · show ActualJetGauge.DH J.A J.H J.dH = _
    rw [hA, hH, hdH]
    funext μ
    simp [ActualJetGauge.DH]

/-- **The stress of the conformal datum**: `T₀₀ = |Π|² + λv⁴` (`Π = w⁻⁶Π₀`), `T₀ᵢ = 0`. -/
theorem Tsl_conf (y : Fin 3 → ℝ) :
    (confDatum (m := m) (S := S) (S' := S') F σ τ P0).Tsl SM y 0 0 =
        (F.w y ^ 12)⁻¹ * SM.ipV P0 P0 + SM.lamH * SM.vH ^ 4 ∧
      ∀ i : Fin 3, (confDatum (m := m) (S := S) (S' := S') F σ τ P0).Tsl SM y 0 i.succ = 0 := by
  obtain ⟨hg, hgi, hF, hH, hDH, hψ, hψb, -, -, -⟩ := firstJet_conf SM F σ τ P0 y
  unfold SliceCauchy.Tsl stressF
  rw [hg, hgi, hF, hH, hDH, hψ, hψb]
  have hY : ∀ μ ν, ymStressB SM.ipG (met4 (-1) 0 (confγ F.w y))
      (met4 (-1) 0 (fun i j => if i = j then (F.w y ^ 4)⁻¹ else 0)) 0 μ ν = 0 := by
    intro μ ν; simp [ymStressB]
  have hD : ∀ (e : Met) (X : Fin 4 → S) (Xb : Fin 4 → S') μ ν,
      SM.TD.coord (met4 (-1) 0 (confγ F.w y)) lorentzSign e 0 0 X 0 Xb μ ν = 0 := by
    intro e X Xb μ ν
    simp [DiracStressForm.coord, DiracStressForm.frame]
  refine ⟨?_, fun i => ?_⟩
  · rw [hY, hD, add_zero, zero_add]
    simp only [higgsStressB, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, met4_zero_zero,
      met4_zero_succ, met4_succ_zero, Pi.zero_apply, map_zero, LinearMap.zero_apply, mul_zero,
      zero_mul, Finset.sum_const_zero, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [hY, hD, add_zero, zero_add]
    simp [higgsStressB, met4_zero_succ]

/-- **The Gauss row of the conformal datum vanishes** when the Yang–Mills source vanishes at zero
Higgs field and zero spinors. -/
theorem gaussRow_conf (hJ : ∀ (g gi : Met) (DH : Fin 4 → V), SM.Jcur g gi 0 DH 0 0 = 0)
    (y : Fin 3 → ℝ) : (confDatum (m := m) (S := S) (S' := S') F σ τ P0).gaussRow SM y = 0 := by
  obtain ⟨-, -, -, hH, -, hψ, hψb, hA, hdA, hddA⟩ := firstJet_conf SM F σ τ P0 y
  set J := ((confDatum (m := m) (S := S) (S' := S') F σ τ P0).base).jet (Fin.cons 0 y)
  have hH' : J.H = 0 := hH
  have hψ' : J.ψ = 0 := hψ
  have hψb' : J.ψb = 0 := hψb
  show ymRes J.A J.dA J.ddA J.FJ.gi (chr J.FJ.gi J.FJ.dg)
    (SM.Jcur J.FJ.g J.FJ.gi J.H (ActualJetGauge.DH J.A J.H J.dH) J.ψ J.ψb) 0 = 0
  rw [hA, hdA, hddA, hH', hψ', hψb', hJ]
  simp [ymRes, ymDiv, dFm, Fm, fieldStrength]

end Matter

/-! ### The conformal identity -/

section Identity

variable (SM : SMData (MatLie m) V S S') (F : ConfFactor) (σ : TTSeed) (τ : ℝ) (P0 : V)

/-- The flat Laplacian `Δw = Σᵢ ∂ᵢ∂ᵢw`. -/
def lapR (w : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  pd (pd w 0) 0 y + pd (pd w 1) 1 y + pd (pd w 2) 2 y

/-- `|σ|² = Σᵢⱼ σᵢⱼ²`. -/
def sqσ (σ : TTSeed) (y : Fin 3 → ℝ) : ℝ := ∑ i, ∑ j, σ.σ y i j ^ 2

/-- The left-hand side of `eq:generated-Hamiltonian` for the conformal datum:
`-8Δw - (2κ|Π₀|² + |σ|²)w⁻⁷ + (⅔τ² - 2Λ - 2κλv⁴)w⁵`. -/
def lichLHS (y : Fin 3 → ℝ) : ℝ :=
  -8 * lapR F.w y - (2 * SM.κ * SM.ipV P0 P0 + sqσ σ y) * (F.w y ^ 7)⁻¹ +
    (2 / 3 * τ ^ 2 - 2 * SM.Λ - 2 * SM.κ * (SM.lamH * SM.vH ^ 4)) * F.w y ^ 5

theorem dtr_σ (y : Fin 3 → ℝ) (k : Fin 3) :
    pd σ.σ k y 0 0 + pd σ.σ k y 1 1 + pd σ.σ k y 2 2 = 0 := by
  have hc : ∀ i j, ContDiff ℝ ∞ (fun y => σ.σ y i j) := fun i j =>
    contDiff_pi.1 (contDiff_pi.1 σ.smooth i) j
  rw [← pd_σ σ y k 0 0, ← pd_σ σ y k 1 1, ← pd_σ σ y k 2 2,
    ← pd3_add ((hc 0 0).differentiable (by simp) y) ((hc 1 1).differentiable (by simp) y),
    ← pd3_add (((hc 0 0).add (hc 1 1)).differentiable (by simp) y)
      ((hc 2 2).differentiable (by simp) y)]
  rw [show (fun y => σ.σ y 0 0 + σ.σ y 1 1 + σ.σ y 2 2) = fun _ => (0 : ℝ) from
    funext σ.tr]
  exact pd3_const 0 k y

/-- **The Hamiltonian row of the conformal datum is `½w⁻⁵` times the conformal Hamiltonian
equation.** -/
theorem hamRow_conf (y : Fin 3 → ℝ) :
    (confDatum (m := m) (S := S) (S' := S') F σ τ P0).hamRow SM y =
      (1 / 2) * (F.w y ^ 5)⁻¹ * lichLHS SM F σ τ P0 y := by
  have hw := F.ne y
  unfold SliceCauchy.hamRow
  rw [sd_conf, hamC_conf (F.w y) hw _ _ τ (Matrix.of (σ.σ y)) _ _ _ _ _ _ (fun i j => σ.symm y i j)
    (σ.tr y),
    (Tsl_conf SM F σ τ P0 y).1]
  unfold lichLHS lapR sqσ
  simp only [Matrix.of_apply]
  field_simp
  ring

theorem momRow_conf (y : Fin 3 → ℝ) (i : Fin 3) :
    (confDatum (m := m) (S := S) (S' := S') F σ τ P0).momRow SM y i = 0 := by
  unfold SliceCauchy.momRow
  rw [sd_conf, momC_conf (F.w y) (F.ne y) _ _ τ (Matrix.of (σ.σ y)) (fun k => Matrix.of (pd σ.σ k y))
    _ _ _ _ _ (fun i j => σ.symm y i j) (σ.tr y) (fun k => dtr_σ σ y k) (fun i => σ.div y i),
    (Tsl_conf SM F σ τ P0 y).2 i]
  ring

/-- **The conformal identity** (`ass:constrained-initial-solver`, the clause "the chosen conformal
weights and matter data give the scalar equation", proved): the conformal Cauchy datum satisfies
the complete Hamiltonian, momentum and Gauss constraints if and only if the conformal factor
solves `eq:generated-Hamiltonian`. -/
theorem constrained_iff_lichnerowicz
    (hJ : ∀ (g gi : Met) (DH : Fin 4 → V), SM.Jcur g gi 0 DH 0 0 = 0) :
    (confDatum (m := m) (S := S) (S' := S') F σ τ P0).Constrained SM ↔
      ∀ y, lichLHS SM F σ τ P0 y = 0 := by
  constructor
  · intro h y
    have h0 := (h y).1
    rw [hamRow_conf] at h0
    have hp : (1 / 2) * (F.w y ^ 5)⁻¹ ≠ 0 := by
      have := F.ne y; positivity
    exact (mul_eq_zero.mp h0).resolve_left hp
  · intro h y
    refine ⟨?_, fun i => momRow_conf SM F σ τ P0 y i, gaussRow_conf SM F σ τ P0 hJ y⟩
    rw [hamRow_conf, h y, mul_zero]

end Identity

end MathPhys.GenSlice.Conf
