/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeCoulombCompactness
import RenewalGeometry.Analysis.LpProductContinuity
import RenewalGeometry.StandardModel.FiniteEinsteinStandardModelInterface

/-!
# The complete finite Yang–Mills first variation with coframes
  (metric clause of `prop:native-YM-identification`, Einstein–SM action closure)

Setting: the unit-torus rendering of `Continuum/NativeYangMillsIdentification.lean` (grid
`(ℤ/N)⁴`, mesh `h = 1/N`), connections in a complete normed complex algebra `𝔸` with `‖1‖ = 1`
whose Lie-algebra metric is read through `T : 𝔸 →L[ℝ] E` (`⟨X, Y⟩ = ⟪T X, T Y⟫`), nodal coframes
`e(x) = (e^a_μ(x))`.

* `gMet`, `gInv`, `vol`: `g = eᵀ η e`, `g⁻¹`, `v(e) = √(-det g)`; `ymCoef e = v(e) g^{μρ} g^{νσ}`
  is `C¹` on the nondegenerate chart (`contDiffOn_ymCoef`);
* `liftK e k`: the symmetric coframe lift `ė^a_μ(k) = -½ e^a_α g_{μβ} k^{αβ}` (`eq:metric-lift`);
* `Fext`: the literal plaquettes `F^h_{μν}` for `μ < ν` (`eq:native-plaquettes`), extended
  antisymmetrically;
* `ymDens`, `actionYM`: **the finite Yang–Mills action of `eq:native-densities`**,
  `S_{YM,h} = h⁴ Σ_x -¼ v(e) g^{μρ} g^{νσ} ⟨F^h_{μν}, F^h_{ρσ}⟩`;
* `firstVarYM`: the complete first variation `d/dt S_{YM,h}(e + t ė_h(k), A + t 𝒮_h a)|₀` in the
  joint metric (nodally lifted) and gauge direction, and `hasDerivAt_actionYM` its explicit form;
* `unif_FextV`: `R_h^0 D_A F_h[𝒮_h a] → d_{A}a` in `L²`, uniformly over `C^{1,1}`-bounded gauge
  tests;
* `native_YM_metric_variation` (**metric clause**): under `R_h^0 A_h → A` in `L⁴`,
  `R_h^0 F_h → F` in `L²` and `R_h^0 e_h → e` in `L²` with values in a compact set of
  nondegenerate coframes, `firstVarYM` converges to the continuum first variation `firstVarCont`
  uniformly over metric tests with `‖k‖_{C^{0,1}} ≤ M` and gauge tests with `‖a‖_{C^{1,1}} ≤ M`
  (bounded `C^r` sets, `r ≥ 2`, are contained in such sets).  The metric row is the product of
  bounded coefficients `D_eΘ(e_h)` converging in measure with the strongly convergent `L¹` packet
  `F_h ⊗ F_h` (`lem:products`, `LpProductContinuity.LpTendsto.coeff`); the gauge rows are strong
  `L²`–strong `L²` pairings.
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal RealInnerProductSpace

namespace RenewalGeometry.NativeYMMetric

open TorusTrigReconstruction NativeCriticalGrid TorusPiecewiseConstantTranslation LogBCH
  NativeYMIdentification PlaquetteLogDerivative NativeYMVariation NativeGridLp NativeHiggs
  NativeCoulomb

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Coframe coefficients -/

section Coefficients

/-- Coframe values `e^a_μ`. -/
abbrev Cof := Fin 4 → Fin 4 → ℝ

/-- Index quadruples `(μ, ν, ρ, σ)`. -/
abbrev Coef4 := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- The metric `g = eᵀ η e`. -/
def gMet (e : Cof) : Matrix (Fin 4) (Fin 4) ℝ := coframeMetric (Matrix.of e)

/-- The inverse metric `g^{μν}`. -/
def gInv (e : Cof) : Matrix (Fin 4) (Fin 4) ℝ := (gMet e)⁻¹

/-- The volume factor `v(e) = √(-det g)`. -/
def vol (e : Cof) : ℝ := Real.sqrt (-(gMet e).det)

/-- The nondegenerate coframes. -/
def GLc : Set Cof := {e | (Matrix.of e).det ≠ 0}

/-- The Yang–Mills coefficients `v(e) g^{μρ} g^{νσ}`. -/
def ymCoef (e : Cof) : Coef4 := fun μ ν ρ σ => vol e * gInv e μ ρ * gInv e ν σ

/-- **The symmetric coframe lift** `ė^a_μ(k) = -½ e^a_α g_{μβ} k^{αβ}` (`eq:metric-lift`). -/
def liftK (e k : Cof) : Cof := fun a μ => -(1 / 2) * ∑ α, ∑ β, e a α * gMet e μ β * k α β

theorem gMet_apply (e : Cof) (μ ν : Fin 4) :
    gMet e μ ν = ∑ a, ∑ b, minkowskiEta a b * (e a μ * e b ν) := by
  simp only [gMet, coframeMetric, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem det_gMet (e : Cof) : (gMet e).det = -((Matrix.of e).det) ^ 2 := by
  simp [gMet, coframeMetric, Matrix.det_mul, Matrix.det_transpose, minkowskiEta,
    Matrix.det_diagonal, Fin.prod_univ_four]
  ring

theorem vol_eq (e : Cof) : vol e = |(Matrix.of e).det| := by
  rw [vol, det_gMet, neg_neg, Real.sqrt_sq_eq_abs]

theorem contDiff_det_cof {n : WithTop ℕ∞} : ContDiff ℝ n (fun e : Cof => (Matrix.of e).det) := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  fun_prop

theorem isOpen_GLc : IsOpen GLc :=
  isOpen_ne_fun (contDiff_det_cof (n := 0)).continuous continuous_const

theorem contDiff_gMet (μ ν : Fin 4) {n : WithTop ℕ∞} : ContDiff ℝ n (fun e : Cof => gMet e μ ν) := by
  simp only [gMet_apply]
  fun_prop

theorem contDiffAt_gInv (μ ν : Fin 4) {n : WithTop ℕ∞} {e : Cof} (he : e ∈ GLc) :
    ContDiffAt ℝ n (fun e : Cof => gInv e μ ν) e := by
  have hdet : ContDiff ℝ n (fun e : Cof => (gMet e).det) := by
    simp only [det_gMet]; exact (contDiff_det_cof.pow 2).neg
  have hadj : ContDiff ℝ n (fun e : Cof => (gMet e).adjugate μ ν) := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply', Matrix.updateRow_apply]
    refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun k _ => ?_)
    split_ifs
    · exact contDiff_const
    · exact contDiff_gMet _ _
  have hne : (gMet e).det ≠ 0 := by
    rw [det_gMet]; exact neg_ne_zero.mpr (pow_ne_zero 2 he)
  have : (fun e : Cof => gInv e μ ν) = fun e => ((gMet e).det)⁻¹ * (gMet e).adjugate μ ν := by
    funext e
    rw [gInv, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [this]
  exact ((contDiffAt_inv ℝ hne).comp e hdet.contDiffAt).mul hadj.contDiffAt

theorem contDiffAt_vol {n : ℕ} {e : Cof} (he : e ∈ GLc) :
    ContDiffAt ℝ n vol e := by
  have : vol = (fun x : ℝ => |x|) ∘ fun e : Cof => (Matrix.of e).det := funext vol_eq
  rw [this]
  exact (contDiffAt_abs (n := n) he).comp e (contDiff_det_cof (n := n)).contDiffAt

theorem contDiffOn_ymCoef {n : ℕ} : ContDiffOn ℝ n ymCoef GLc := by
  intro e he
  refine (contDiffAt_pi.2 fun μ => contDiffAt_pi.2 fun ν => contDiffAt_pi.2 fun ρ =>
    contDiffAt_pi.2 fun σ => ?_).contDiffWithinAt
  exact ((contDiffAt_vol he).mul (contDiffAt_gInv μ ρ he)).mul (contDiffAt_gInv ν σ he)

theorem continuous_liftK : Continuous fun p : Cof × Cof => liftK p.1 p.2 := by
  refine continuous_pi fun a => continuous_pi fun μ => ?_
  simp only [liftK]
  refine continuous_const.mul (continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
    ?_)
  have h1 : Continuous fun p : Cof × Cof => p.1 a α :=
    (continuous_apply α).comp ((continuous_apply a).comp continuous_fst)
  have h2 : Continuous fun p : Cof × Cof => gMet p.1 μ β :=
    (contDiff_gMet μ β (n := 0)).continuous.comp continuous_fst
  have h3 : Continuous fun p : Cof × Cof => p.2 α β :=
    (continuous_apply β).comp ((continuous_apply α).comp continuous_snd)
  exact (h1.mul h2).mul h3

/-- The metric derivative of the coefficients along the lift: `D Θ(e)[ė(k)]`. -/
def dCoef (e k : Cof) : Coef4 := fderiv ℝ ymCoef e (liftK e k)

theorem continuousOn_dCoef : ContinuousOn (fun p : Cof × Cof => dCoef p.1 p.2) (GLc ×ˢ univ) := by
  have h1 : ContinuousOn (fderiv ℝ ymCoef) GLc :=
    (contDiffOn_ymCoef (n := 1)).continuousOn_fderiv_of_isOpen isOpen_GLc le_rfl
  have h2 : ContinuousOn (fun p : Cof × Cof => fderiv ℝ ymCoef p.1) (GLc ×ˢ univ) :=
    h1.comp continuous_fst.continuousOn fun p hp => hp.1
  exact (isBoundedBilinearMap_apply.continuous.comp_continuousOn
    (h2.prodMk continuous_liftK.continuousOn) :)

theorem continuousOn_ymCoef : ContinuousOn ymCoef GLc :=
  (contDiffOn_ymCoef (n := 0)).continuousOn

end Coefficients

/-! ### The finite Yang–Mills action -/

section Action

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : ℕ}

/-- The literal plaquettes `F^h_{μν}` (`μ < ν`, `eq:native-plaquettes`), extended antisymmetrically. -/
def Fext (N : ℕ) (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) : 𝔸 :=
  if μ < ν then curvLog N A x μ ν else if ν < μ then -curvLog N A x ν μ else 0

/-- The literal first variations `D_A F^h_{μν}[w]`, extended antisymmetrically. -/
def FextV (N : ℕ) (A w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) : 𝔸 :=
  if μ < ν then curvVar N A w x μ ν else if ν < μ then -curvVar N A w x ν μ else 0

/-- The Yang–Mills density `-¼ θ^{μνρσ} ⟨F_{μν}, F_{ρσ}⟩`, `θ = v(e) g^{μρ} g^{νσ}`. -/
def ymDens (T : 𝔸 →L[ℝ] E) (θ : Coef4) (F : Fin 4 → Fin 4 → 𝔸) : ℝ :=
  -(1 / 4) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, θ μ ν ρ σ * ⟪T (F μ ν), T (F ρ σ)⟫

/-- **The finite Yang–Mills action of `eq:native-densities`**:
`S_{YM,h}(e, A) = h⁴ Σ_x -¼ v(e) g^{μρ} g^{νσ} ⟨F^h_{μν}, F^h_{ρσ}⟩`, `h = 1/N`. -/
def actionYM (T : 𝔸 →L[ℝ] E) (N : ℕ) [NeZero N] (e : LatticeTorusPlancherel.Grid 4 N → Cof)
    (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) : ℝ :=
  ((N : ℝ)⁻¹) ^ 4 * ∑ x, ymDens T (ymCoef (e x)) (Fext N A x)

/-- **The complete finite Yang–Mills first variation** along the coframe direction `κ` (the nodal
symmetric lift of a metric test) and the gauge direction `w`. -/
def firstVarYM (T : 𝔸 →L[ℝ] E) (N : ℕ) [NeZero N] (e κ : LatticeTorusPlancherel.Grid 4 N → Cof)
    (A w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) : ℝ :=
  deriv (fun t : ℝ => actionYM T N (e + t • κ) (A + t • w)) 0

/-- The pointwise first-variation density
`-¼ Σ [θ'^{μνρσ} ⟨F_{μν}, F_{ρσ}⟩ + θ^{μνρσ}(⟨F_{μν}, F'_{ρσ}⟩ + ⟨F'_{μν}, F_{ρσ}⟩)]`. -/
def varDens (T : 𝔸 →L[ℝ] E) (θ θ' : Coef4) (F F' : Fin 4 → Fin 4 → 𝔸) : ℝ :=
  -(1 / 4) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, (θ' μ ν ρ σ * ⟪T (F μ ν), T (F ρ σ)⟫ +
    θ μ ν ρ σ * (⟪T (F μ ν), T (F' ρ σ)⟫ + ⟪T (F' μ ν), T (F ρ σ)⟫))

theorem hasDerivAt_Fext [NeZero N] (A w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N)
    (hch : ∀ μ ν, (N : ℝ)⁻¹ * normSum (slots A x μ ν) ≤ 1 / 32) (μ ν : Fin 4) :
    HasDerivAt (fun t : ℝ => Fext N (A + t • w) x μ ν) (FextV N A w x μ ν) 0 := by
  have hcv : ∀ μ ν, HasDerivAt (fun t : ℝ => curvLog N (A + t • w) x μ ν) (curvVar N A w x μ ν) 0 := by
    intro μ ν
    obtain ⟨R, hR, -⟩ := hasDerivAt_curvLog A w x μ ν (hch μ ν)
    have := hR.deriv
    rw [curvVar, this]
    exact hR
  unfold Fext FextV
  split_ifs with h1 h2
  · exact hcv μ ν
  · exact (hcv ν μ).neg
  · exact hasDerivAt_const _ _

/-- **The explicit complete first variation** of the finite Yang–Mills action, on the
nondegenerate coframe chart and the scaled plaquette chart. -/
theorem hasDerivAt_actionYM [NeZero N] (T : 𝔸 →L[ℝ] E) (e κ : LatticeTorusPlancherel.Grid 4 N → Cof)
    (A w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) (he : ∀ x, e x ∈ GLc)
    (hch : ∀ x μ ν, (N : ℝ)⁻¹ * normSum (slots A x μ ν) ≤ 1 / 32) :
    HasDerivAt (fun t : ℝ => actionYM T N (e + t • κ) (A + t • w))
      (((N : ℝ)⁻¹) ^ 4 * ∑ x, varDens T (ymCoef (e x)) (fderiv ℝ ymCoef (e x) (κ x))
        (Fext N A x) (FextV N A w x)) 0 := by
  unfold actionYM
  refine (HasDerivAt.fun_sum (u := Finset.univ) fun x _ => ?_).const_mul (((N : ℝ)⁻¹) ^ 4)
  -- the coefficient
  have hθ : HasDerivAt (fun t : ℝ => ymCoef ((e + t • κ) x)) (fderiv ℝ ymCoef (e x) (κ x)) 0 := by
    have hd : DifferentiableAt ℝ ymCoef (e x) :=
      ((contDiffOn_ymCoef (n := 1)).contDiffAt (isOpen_GLc.mem_nhds (he x))).differentiableAt
        (by norm_num)
    have hl : HasDerivAt (fun t : ℝ => e x + t • κ x) (κ x) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const (κ x)).const_add (e x)
      simpa using this
    have hd' : HasFDerivAt ymCoef (fderiv ℝ ymCoef (e x)) (e x + (0 : ℝ) • κ x) := by
      rw [zero_smul, add_zero]; exact hd.hasFDerivAt
    have := hd'.comp_hasDerivAt (0 : ℝ) hl
    exact this
  have hF := fun μ ν => hasDerivAt_Fext A w x (hch x) μ ν
  unfold ymDens varDens
  refine (HasDerivAt.fun_sum (u := Finset.univ) fun μ _ => HasDerivAt.fun_sum (u := Finset.univ)
    fun ν _ => HasDerivAt.fun_sum (u := Finset.univ) fun ρ _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun σ _ => ?_).const_mul (-(1 / 4 : ℝ))
  have hc : HasDerivAt (fun t : ℝ => ymCoef ((e + t • κ) x) μ ν ρ σ)
      (fderiv ℝ ymCoef (e x) (κ x) μ ν ρ σ) 0 := by
    have h1 := (hasDerivAt_pi.1 hθ) μ
    have h2 := (hasDerivAt_pi.1 h1) ν
    have h3 := (hasDerivAt_pi.1 h2) ρ
    exact (hasDerivAt_pi.1 h3) σ
  have hTμν := T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hF μ ν)
  have hTρσ := T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hF ρ σ)
  have hin := HasDerivAt.inner ℝ hTμν hTρσ
  have key := hc.mul hin
  simp only [Function.comp_apply, zero_smul, add_zero] at key
  exact key

end Action

/-! ### Bounded test sets and the uniform finite-difference estimate -/

section TestBounds

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- **Bounded `C^{1,1}` gauge tests**: `|a| ≤ M`, `|∂a| ≤ M`, and `a`, `∂a` are `M`-Lipschitz on
`𝕋⁴`.  Every bounded set of smooth tests in `C^r`, `r ≥ 2`, is contained in such a set. -/
structure GaugeBound (M : NNReal) (a : C1Test 𝔸) : Prop where
  a_le : ∀ ν y, ‖a.a ν y‖ ≤ M
  a_lip : ∀ ν, LipschitzWith M (a.a ν)
  da_le : ∀ μ ν y, ‖a.da μ ν y‖ ≤ M
  da_lip : ∀ μ ν, LipschitzWith M (a.da μ ν)

/-- Bounded `C^{0,1}` metric tests. -/
structure MetricBound (M : NNReal) (k : C(UnitAddTorus (Fin 4), Cof)) : Prop where
  k_le : ∀ y, ‖k y‖ ≤ M
  k_lip : LipschitzWith M k

/-- Finite differences of a test with `M`-Lipschitz derivatives: `‖s⁻¹(a(y+se_μ) - a(y)) - ∂_μa(y)‖ ≤
M s`. -/
theorem norm_fd_sub_le {M : NNReal} (a : C1Test 𝔸) (μ ν : Fin 4)
    (hlip : LipschitzWith M (a.da μ ν)) (y : UnitAddTorus (Fin 4)) {s : ℝ} (hs : 0 < s) :
    ‖s⁻¹ • (a.a ν (y + KolmogorovRieszTorus.coordPt μ s) - a.a ν y) - a.da μ ν y‖ ≤ M * s := by
  set g : ℝ → 𝔸 := fun u => a.a ν (y + KolmogorovRieszTorus.coordPt μ u) - u • a.da μ ν y
  have hg : ∀ u ∈ Icc (0 : ℝ) s, HasDerivWithinAt g
      (a.da μ ν (y + KolmogorovRieszTorus.coordPt μ u) - a.da μ ν y) (Icc 0 s) u := by
    intro u _
    have := (hasDerivAt_line a μ ν y u).sub ((hasDerivAt_id u).smul_const (a.da μ ν y))
    exact (this.congr_deriv (by simp)).hasDerivWithinAt
  have hb : ∀ u ∈ Ico (0 : ℝ) s,
      ‖a.da μ ν (y + KolmogorovRieszTorus.coordPt μ u) - a.da μ ν y‖ ≤ M * s := by
    intro u hu
    have h1 := hlip.dist_le_mul (y + KolmogorovRieszTorus.coordPt μ u) y
    rw [dist_eq_norm] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ M.2)
    refine (dist_add_coordPt_le y μ u).trans ?_
    rw [abs_of_nonneg hu.1]; exact hu.2.le
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hg hb s ⟨hs.le, le_rfl⟩
  have e : s⁻¹ • (a.a ν (y + KolmogorovRieszTorus.coordPt μ s) - a.a ν y) - a.da μ ν y =
      s⁻¹ • (g s - g 0) := by
    simp only [g, coordPt_zero, add_zero, zero_smul, sub_zero, smul_sub, smul_smul,
      inv_mul_cancel₀ hs.ne', one_smul]
    abel
  rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
  calc s⁻¹ * ‖g s - g 0‖ ≤ s⁻¹ * (↑M * s * (s - 0)) := mul_le_mul_of_nonneg_left hmv (by positivity)
    _ = M * s := by rw [sub_zero]; field_simp

/-- **Uniform consistency of sampled forward differences** for `C^{1,1}`-bounded tests:
`‖R_h^0 D⁺_μ 𝒮_h a_ν (y) - ∂_μ a_ν(y)‖ ≤ 3M/N`. -/
theorem norm_pc_DpV_sample_sub_le {M : NNReal} (a : C1Test 𝔸) (ha : GaugeBound M a) {N : ℕ}
    [NeZero N] (μ ν : Fin 4) (y : UnitAddTorus (Fin 4)) :
    ‖pc (DpV μ (fun x => sampleTest N a x ν)) y - a.da μ ν y‖ ≤ 3 * M * (N : ℝ)⁻¹ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set x := TorusPiecewiseConstantTranslation.index N y
  set y₀ := TorusCellEmbedding.samplePt x
  have hpc : pc (DpV μ (fun x => sampleTest N a x ν)) y =
      ((N : ℝ)⁻¹)⁻¹ • (a.a ν (y₀ + KolmogorovRieszTorus.coordPt μ ((N : ℝ)⁻¹)) - a.a ν y₀) := by
    simp only [pc, DpV, sampleTest, inv_inv]
    rw [VariableTorusDirac.samplePt_add_single]
    rfl
  have h1 := norm_fd_sub_le a μ ν (ha.da_lip μ ν) y₀ (inv_pos.2 hN)
  have h2 : ‖a.da μ ν y₀ - a.da μ ν y‖ ≤ M * (2 * (N : ℝ)⁻¹) := by
    have := (ha.da_lip μ ν).dist_le_mul y₀ y
    rw [dist_eq_norm] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ M.2)
    have := dist_samplePt_index_add_le (N := N) y μ 0 (by norm_num)
    simpa [x, y₀] using this
  rw [hpc]
  calc ‖((N : ℝ)⁻¹)⁻¹ • (a.a ν (y₀ + KolmogorovRieszTorus.coordPt μ ((N : ℝ)⁻¹)) - a.a ν y₀) -
        a.da μ ν y‖
      = ‖(((N : ℝ)⁻¹)⁻¹ • (a.a ν (y₀ + KolmogorovRieszTorus.coordPt μ ((N : ℝ)⁻¹)) - a.a ν y₀) -
          a.da μ ν y₀) + (a.da μ ν y₀ - a.da μ ν y)‖ := by congr 1; abel
    _ ≤ M * (N : ℝ)⁻¹ + M * (2 * (N : ℝ)⁻¹) := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = 3 * M * (N : ℝ)⁻¹ := by ring

/-- Sampled test values are within `2M/N` of the continuum values. -/
theorem norm_sample_sub_le {M : NNReal} (a : C1Test 𝔸) (ha : GaugeBound M a) {N : ℕ} [NeZero N]
    (ν : Fin 4) (y : UnitAddTorus (Fin 4)) (m : ℕ) (hm : m ≤ 1) (μ : Fin 4) :
    ‖a.a ν (TorusCellEmbedding.samplePt
      (TorusPiecewiseConstantTranslation.index N y + m • Pi.single μ 1)) - a.a ν y‖ ≤
      M * (2 * (N : ℝ)⁻¹) := by
  have := (ha.a_lip ν).dist_le_mul (TorusCellEmbedding.samplePt
    (TorusPiecewiseConstantTranslation.index N y + m • Pi.single μ 1)) y
  rw [dist_eq_norm] at this
  exact this.trans (mul_le_mul_of_nonneg_left (dist_samplePt_index_add_le y μ m hm) M.2)

end TestBounds

/-! ### The uniform `L²` estimate for the literal first variation of the curvature -/

section UnifVariation

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

theorem sum_subList {L L' : List 𝔸} (h : L.length = L'.length) :
    (subList L L').sum = L.sum - L'.sum := by
  induction L generalizing L' with
  | nil => cases L' with
    | nil => simp [subList]
    | cons b L' => simp at h
  | cons a L ih => cases L' with
    | nil => simp at h
    | cons b L' =>
        have := ih (L' := L') (by simpa using h)
        simp only [subList] at this ⊢
        simp only [List.zipWith_cons_cons, List.sum_cons, this]
        abel

/-- Bilinearity of the polarised commutator term. -/
theorem commPol_sub {L L' W W' : List 𝔸} (h1 : L.length = L'.length) (h2 : W.length = W'.length) :
    commPol L W - commPol L' W' = commPol (subList L L') W + commPol L' (subList W W') := by
  induction L generalizing L' W W' with
  | nil => cases L' with
    | nil => simp [commPol, subList]
    | cons b L' => simp at h1
  | cons x L ih => cases L' with
    | nil => simp at h1
    | cons x' L' => cases W with
      | nil => cases W' with
        | nil => simp [commPol, subList]
        | cons w' W' => simp at h2
      | cons w W => cases W' with
        | nil => simp at h2
        | cons w' W' =>
            have hl1 : L.length = L'.length := by simpa using h1
            have hl2 : W.length = W'.length := by simpa using h2
            have hih := ih hl1 hl2
            have hs1 := sum_subList hl1
            have hs2 := sum_subList hl2
            simp only [subList] at hih hs1 hs2 ⊢
            simp only [List.zipWith_cons_cons, commPol, hs1, hs2]
            rw [show (1 / 2 : ℝ) • (x * W.sum + w * L.sum - L.sum * w - W.sum * x) + commPol L W -
                ((1 / 2 : ℝ) • (x' * W'.sum + w' * L'.sum - L'.sum * w' - W'.sum * x') +
                  commPol L' W') =
                (1 / 2 : ℝ) • (x * W.sum + w * L.sum - L.sum * w - W.sum * x) -
                (1 / 2 : ℝ) • (x' * W'.sum + w' * L'.sum - L'.sum * w' - W'.sum * x') +
                  (commPol L W - commPol L' W') by abel, hih]
            simp only [mul_sub, sub_mul, smul_sub, smul_add]
            abel

/-- The continuum covariant derivative `(d_A a)_{μν} = ∂_μa_ν - ∂_νa_μ + [A_μ, a_ν] + [a_μ, A_ν]`. -/
def DaT (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (a : C1Test 𝔸) (y : UnitAddTorus (Fin 4))
    (μ ν : Fin 4) : 𝔸 :=
  (a.da μ ν y - a.da ν μ y) + ((A₀ μ y * a.a ν y - a.a ν y * A₀ μ y) +
    (a.a μ y * A₀ ν y - A₀ ν y * a.a μ y))

theorem DaT_antisymm (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (a : C1Test 𝔸)
    (y : UnitAddTorus (Fin 4)) (μ ν : Fin 4) : DaT A₀ a y ν μ = -DaT A₀ a y μ ν := by
  simp only [DaT]; abel

theorem DaT_self (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (a : C1Test 𝔸)
    (y : UnitAddTorus (Fin 4)) (μ : Fin 4) : DaT A₀ a y μ μ = 0 := by
  simp only [DaT]; abel

/-- The limit slot list `(A_μ, A_ν, -A_μ, -A_ν)`. -/
def limSlots (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (y : UnitAddTorus (Fin 4)) (μ ν : Fin 4) :
    List 𝔸 := [A₀ μ y, A₀ ν y, -A₀ μ y, -A₀ ν y]

theorem normSum_slots_sample_le' {M : NNReal} (a : C1Test 𝔸) (ha : GaugeBound M a) {N : ℕ}
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) :
    normSum (slots (sampleTest N a) x μ ν) ≤ 4 * M := by
  rw [normSum_slots]
  simp only [sampleTest]
  linarith [ha.a_le μ (TorusCellEmbedding.samplePt x), ha.a_le ν
    (TorusCellEmbedding.samplePt (x + Pi.single μ 1)), ha.a_le μ
    (TorusCellEmbedding.samplePt (x + Pi.single ν 1)), ha.a_le ν (TorusCellEmbedding.samplePt x)]

theorem normSum_subList_sample_le {M : NNReal} (a : C1Test 𝔸) (ha : GaugeBound M a) {N : ℕ}
    [NeZero N] (y : UnitAddTorus (Fin 4)) (μ ν : Fin 4) :
    normSum (subList (slots (sampleTest N a) (TorusPiecewiseConstantTranslation.index N y) μ ν)
      [a.a μ y, a.a ν y, -a.a μ y, -a.a ν y]) ≤ 4 * (M * (2 * (N : ℝ)⁻¹)) := by
  set x := TorusPiecewiseConstantTranslation.index N y
  have h0 : ∀ κ, ‖a.a κ (TorusCellEmbedding.samplePt x) - a.a κ y‖ ≤ M * (2 * (N : ℝ)⁻¹) := by
    intro κ
    have := norm_sample_sub_le a ha (N := N) κ y 0 (by norm_num) μ
    simpa [x] using this
  have h1 : ∀ κ ρ, ‖a.a κ (TorusCellEmbedding.samplePt (x + Pi.single ρ 1)) - a.a κ y‖ ≤
      M * (2 * (N : ℝ)⁻¹) := by
    intro κ ρ
    have := norm_sample_sub_le a ha (N := N) κ y 1 le_rfl ρ
    simpa [x] using this
  simp only [subList, slots, sampleTest, List.zipWith_cons_cons, List.zipWith_nil_right,
    normSum_cons, normSum_nil, add_zero]
  have e1 : ‖-a.a μ (TorusCellEmbedding.samplePt (x + Pi.single ν 1)) - -a.a μ y‖ =
      ‖a.a μ (TorusCellEmbedding.samplePt (x + Pi.single ν 1)) - a.a μ y‖ := by
    rw [neg_sub_neg, norm_sub_rev]
  have e2 : ‖-a.a ν (TorusCellEmbedding.samplePt x) - -a.a ν y‖ =
      ‖a.a ν (TorusCellEmbedding.samplePt x) - a.a ν y‖ := by
    rw [neg_sub_neg, norm_sub_rev]
  rw [e1, e2]
  linarith [h0 μ, h1 ν μ, h1 μ ν, h0 ν]

end UnifVariation

section UnifPointwise

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- **Pointwise uniform estimate** of the literal first variation against `d_A a`:
on the chart, at `y` with `x = index y`,
`‖D_A F_h[𝒮_h a]_{μν}(x) - (d_A a)_{μν}(y)‖ ≤ 6M/N + 4M D(y) + (8M/N) |W(A)(y)| + 192 M σ |W_h(x)|`,
where `D(y) = Σ_i ‖W_i(A_h)(x) - W_i(A)(y)‖` and `σ ≥ h |W_h(x)|`. -/
theorem norm_curvVar_sub_DaT_le {M : NNReal} (a : C1Test 𝔸) (ha : GaugeBound M a) {N : ℕ}
    [NeZero N] (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (y : UnitAddTorus (Fin 4)) (μ ν : Fin 4) {σ : ℝ}
    (hch : (N : ℝ)⁻¹ * normSum (slots A (TorusPiecewiseConstantTranslation.index N y) μ ν) ≤ 1 / 32)
    (hσ : (N : ℝ)⁻¹ * normSum (slots A (TorusPiecewiseConstantTranslation.index N y) μ ν) ≤ σ) :
    ‖curvVar N A (sampleTest N a) (TorusPiecewiseConstantTranslation.index N y) μ ν -
        DaT A₀ a y μ ν‖ ≤
      6 * M * (N : ℝ)⁻¹ +
        4 * M * normSum (subList (slots A (TorusPiecewiseConstantTranslation.index N y) μ ν)
          (limSlots A₀ y μ ν)) +
        8 * M * (N : ℝ)⁻¹ * normSum (limSlots A₀ y μ ν) +
        192 * M * σ * normSum (slots A (TorusPiecewiseConstantTranslation.index N y) μ ν) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set x := TorusPiecewiseConstantTranslation.index N y
  set s := normSum (slots A x μ ν)
  have hs0 : 0 ≤ s := normSum_nonneg _
  set W : List 𝔸 := [a.a μ y, a.a ν y, -a.a μ y, -a.a ν y]
  -- the three pieces
  have hrem := norm_curvVar_sub_le A (sampleTest N a) x μ ν hch
  have hw := normSum_slots_sample_le' a ha (N := N) x μ ν
  have hlin : ‖linCurl (sampleTest N a) x μ ν - (a.da μ ν y - a.da ν μ y)‖ ≤ 6 * M * (N : ℝ)⁻¹ := by
    have h1 := norm_pc_DpV_sample_sub_le a ha (N := N) μ ν y
    have h2 := norm_pc_DpV_sample_sub_le a ha (N := N) ν μ y
    have e : linCurl (sampleTest N a) x μ ν - (a.da μ ν y - a.da ν μ y) =
        (pc (DpV μ (fun x => sampleTest N a x ν)) y - a.da μ ν y) -
          (pc (DpV ν (fun x => sampleTest N a x μ)) y - a.da ν μ y) := by
      simp only [linCurl, pc, DpA, DpV, x]; abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hcomm : ‖commPol (slots A x μ ν) (slots (sampleTest N a) x μ ν) - commPol (limSlots A₀ y μ ν) W‖ ≤
      4 * M * normSum (subList (slots A x μ ν) (limSlots A₀ y μ ν)) +
        8 * M * (N : ℝ)⁻¹ * normSum (limSlots A₀ y μ ν) := by
    rw [commPol_sub (by simp [slots, limSlots]) (by simp [slots, W])]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_commPol_le _ _).trans ?_
      have h0 := normSum_nonneg (subList (slots A x μ ν) (limSlots A₀ y μ ν))
      nlinarith
    · refine (norm_commPol_le _ _).trans ?_
      have h0 := normSum_nonneg (limSlots A₀ y μ ν)
      have := normSum_subList_sample_le a ha (N := N) y μ ν
      have h8 : normSum (subList (slots (sampleTest N a) x μ ν) W) ≤ 8 * M * (N : ℝ)⁻¹ := by
        have : 4 * (↑M * (2 * (N : ℝ)⁻¹)) = 8 * M * (N : ℝ)⁻¹ := by ring
        linarith
      nlinarith
  have hDa : DaT A₀ a y μ ν = (a.da μ ν y - a.da ν μ y) + commPol (limSlots A₀ y μ ν) W := by
    rw [DaT, limSlots, commPol_limit]
  have hsplit : curvVar N A (sampleTest N a) x μ ν - DaT A₀ a y μ ν =
      (curvVar N A (sampleTest N a) x μ ν - linCurl (sampleTest N a) x μ ν -
        commPol (slots A x μ ν) (slots (sampleTest N a) x μ ν)) +
      (linCurl (sampleTest N a) x μ ν - (a.da μ ν y - a.da ν μ y)) +
      (commPol (slots A x μ ν) (slots (sampleTest N a) x μ ν) - commPol (limSlots A₀ y μ ν) W) := by
    rw [hDa]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  have hr : ‖curvVar N A (sampleTest N a) x μ ν - linCurl (sampleTest N a) x μ ν -
      commPol (slots A x μ ν) (slots (sampleTest N a) x μ ν)‖ ≤ 192 * M * σ * s := by
    refine hrem.trans ?_
    have hw0 : 0 ≤ normSum (slots (sampleTest N a) x μ ν) := normSum_nonneg _
    calc 48 * (N : ℝ)⁻¹ * s ^ 2 * normSum (slots (sampleTest N a) x μ ν)
        = 48 * ((N : ℝ)⁻¹ * s) * s * normSum (slots (sampleTest N a) x μ ν) := by ring
      _ ≤ 48 * σ * s * (4 * M) := by
          have hσ0 : 0 ≤ σ := (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹ * s).trans hσ
          gcongr
      _ = 192 * M * σ * s := by ring
  linarith

end UnifPointwise

section UnifL2

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fact_one_le_four_m : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_two_m : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem toReal_eLpNorm_add_le {F : Type*} [NormedAddCommGroup F] {f g : UnitAddTorus (Fin 4) → F}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (eLpNorm (f + g) 2 volume).toReal ≤ (eLpNorm f 2 volume).toReal + (eLpNorm g 2 volume).toReal := by
  rw [← ENNReal.toReal_add hf.2.ne hg.2.ne]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.2.ne, hg.2.ne⟩)
    (eLpNorm_add_le hf.1 hg.1 (by norm_num))

theorem toReal_eLpNorm_mono {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {f : UnitAddTorus (Fin 4) → F} {g : UnitAddTorus (Fin 4) → G} (hg : MemLp g 2 volume)
    (h : ∀ y, ‖f y‖ ≤ ‖g y‖) : (eLpNorm f 2 volume).toReal ≤ (eLpNorm g 2 volume).toReal :=
  ENNReal.toReal_mono hg.2.ne (eLpNorm_mono h)

theorem toReal_eLpNorm_const_mul {f : UnitAddTorus (Fin 4) → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    (eLpNorm (fun y => c * f y) 2 volume).toReal = c * (eLpNorm f 2 volume).toReal := by
  have : (fun y => c * f y) = c • f := rfl
  rw [this, eLpNorm_const_smul, ENNReal.toReal_mul]
  simp [abs_of_nonneg hc]

theorem toReal_eLpNorm_const (c : ℝ) (hc : 0 ≤ c) :
    (eLpNorm (fun _ : UnitAddTorus (Fin 4) => c) 2 volume).toReal = c := by
  rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero _)]
  simp [abs_of_nonneg hc]

/-- `R_h^0` of a one-step shifted slot, as a function of `y`. -/
theorem slots_index_eq {N : ℕ} [NeZero N] (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (y : UnitAddTorus (Fin 4)) (μ ν : Fin 4) :
    slots A (TorusPiecewiseConstantTranslation.index N y) μ ν =
      [pc (fun x => A x μ) y, pc (T μ (fun x => A x ν)) y, -pc (T ν (fun x => A x μ)) y,
        -pc (fun x => A x ν) y] := rfl

/-- **Uniform `L²` convergence of the literal first variation** over `C^{1,1}`-bounded gauge tests:
there are `δ_k → 0` such that eventually (on the plaquette chart), for every test with
`GaugeBound M a`, `‖R_h^0 D_A F_h[𝒮_h a]_{μν} - (d_A a)_{μν}‖_{L²} ≤ δ_k` (antisymmetric
extension). -/
theorem unif_FextV (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ)) (M : NNReal) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ k in atTop,
      (∀ x μ ν, ((n k : ℝ))⁻¹ * normSum (slots (A k) x μ ν) ≤ 1 / 32) ∧
      ∀ a : C1Test 𝔸, GaugeBound M a → ∀ μ ν,
        (eLpNorm (fun y => pc (fun x => FextV (n k) (A k) (sampleTest (n k) a) x μ ν) y -
          DaT A₀ a y μ ν) 2 volume).toReal ≤ δ k := by
  have hA2 : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => A k x μ)) (A₀ μ) := fun μ =>
    (hA μ).mono (by norm_num) (by norm_num)
  -- the slot-size control
  set σ : ℕ → ℝ := fun k => 4 * ∑ κ, meshSup (fun x => A k x κ)
  have hσ : Tendsto σ atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun κ _ =>
      tendsto_meshSup hn (hA κ).memLp_lim (hA κ).tendsto
    simpa using this.const_mul 4
  have hσ0 : ∀ k, 0 ≤ σ k := fun k =>
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => meshSup_nonneg _)
  have hslot : ∀ k x μ ν, ((n k : ℝ))⁻¹ * normSum (slots (A k) x μ ν) ≤ σ k := by
    intro k x μ ν
    rw [normSum_slots]
    have hm : ∀ κ g, ((n k : ℝ))⁻¹ * ‖A k g κ‖ ≤ ∑ κ, meshSup (fun x => A k x κ) := fun κ g =>
      (le_meshSup (fun x => A k x κ) g).trans (Finset.single_le_sum
        (f := fun κ => meshSup (fun x => A k x κ)) (fun _ _ => meshSup_nonneg _) (Finset.mem_univ κ))
    have h1 := hm μ x
    have h2 := hm ν (x + Pi.single μ 1)
    have h3 := hm μ (x + Pi.single ν 1)
    have h4 := hm ν x
    simp only [σ]
    nlinarith
  -- the three auxiliary functions for a pair `(p, q)`
  set Dfun : ℕ → Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → ℝ := fun k p q y =>
    ‖pc (fun x => A k x p) y - A₀ p y‖ + ‖pc (T p (fun x => A k x q)) y - A₀ q y‖ +
      ‖pc (T q (fun x => A k x p)) y - A₀ p y‖ + ‖pc (fun x => A k x q) y - A₀ q y‖
  set Pfun : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → ℝ := fun p q y =>
    ‖A₀ p y‖ + ‖A₀ q y‖ + ‖A₀ p y‖ + ‖A₀ q y‖
  set Sfun : ℕ → Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → ℝ := fun k p q y =>
    ‖pc (fun x => A k x p) y‖ + ‖pc (T p (fun x => A k x q)) y‖ +
      ‖pc (T q (fun x => A k x p)) y‖ + ‖pc (fun x => A k x q) y‖
  have hDslot : ∀ k p q y, normSum (subList (slots (A k) (TorusPiecewiseConstantTranslation.index
      (n k) y) p q) (limSlots A₀ y p q)) = Dfun k p q y := by
    intro k p q y
    rw [slots_index_eq]
    simp only [subList, limSlots, List.zipWith_cons_cons, List.zipWith_nil_right, normSum_cons,
      normSum_nil, add_zero, neg_sub_neg, Dfun]
    rw [norm_sub_rev (A₀ p y), norm_sub_rev (A₀ q y)]
    ring
  have hPslot : ∀ p q y, normSum (limSlots A₀ y p q) = Pfun p q y := by
    intro p q y
    simp only [limSlots, normSum_cons, normSum_nil, add_zero, norm_neg, Pfun]
    ring
  have hSslot : ∀ k p q y, normSum (slots (A k) (TorusPiecewiseConstantTranslation.index (n k) y)
      p q) = Sfun k p q y := by
    intro k p q y
    rw [slots_index_eq]
    simp only [normSum_cons, normSum_nil, add_zero, norm_neg, Sfun]
    ring
  -- convergence of the auxiliary norms
  have hDL : ∀ p q, LpTendsto volume 2 (fun k => Dfun k p q) 0 := by
    intro p q
    have hz : ∀ {u : ℕ → UnitAddTorus (Fin 4) → 𝔸} {u₀ : UnitAddTorus (Fin 4) → 𝔸},
        LpTendsto volume 2 u u₀ → LpTendsto volume 2 (fun k y => ‖u k y - u₀ y‖) 0 := by
      intro u u₀ hu
      refine ⟨fun k => ((hu.memLp k).sub hu.memLp_lim).norm, MemLp.zero, ?_⟩
      refine hu.tendsto.congr fun k => ?_
      rw [sub_zero, ← eLpNorm_norm]
      rfl
    have := (((hz (hA2 p)).add (hz ((hA2 q).shift hn (by norm_num) p))).add
      (hz ((hA2 p).shift hn (by norm_num) q))).add (hz (hA2 q))
    refine this.congr (fun k => Eventually.of_forall fun y => rfl)
      (Eventually.of_forall fun y => by simp)
  have hSL : ∀ p q, LpTendsto volume 2 (fun k => Sfun k p q) (Pfun p q) := by
    intro p q
    have := ((((hA2 p).norm.add ((hA2 q).shift hn (by norm_num) p).norm).add
      ((hA2 p).shift hn (by norm_num) q).norm).add (hA2 q).norm)
    exact this.congr (fun k => Eventually.of_forall fun y => rfl)
      (Eventually.of_forall fun y => rfl)
  have hPmem : ∀ p q, MemLp (Pfun p q) 2 volume := fun p q => (hSL p q).memLp_lim
  set δpq : ℕ → Fin 4 → Fin 4 → ℝ := fun k p q =>
    6 * M * ((n k : ℝ))⁻¹ + 4 * M * (eLpNorm (Dfun k p q) 2 volume).toReal +
      8 * M * ((n k : ℝ))⁻¹ * (eLpNorm (Pfun p q) 2 volume).toReal +
        192 * M * σ k * (eLpNorm (Sfun k p q) 2 volume).toReal
  set δ : ℕ → ℝ := fun k => ∑ p, ∑ q, δpq k p q
  refine ⟨δ, ?_, ?_⟩
  · -- `δ_k → 0`
    have hpq : ∀ p q, Tendsto (fun k => δpq k p q) atTop (𝓝 0) := by
      intro p q
      have h1 := tendsto_inv_n hn
      have h2 : Tendsto (fun k => (eLpNorm (Dfun k p q) 2 volume).toReal) atTop (𝓝 0) := by
        have := (hDL p q).tendsto_toReal_eLpNorm
        simpa using this
      have h3 := (hSL p q).tendsto_toReal_eLpNorm
      have := ((((h1.const_mul (6 * (M : ℝ))).add (h2.const_mul (4 * (M : ℝ)))).add
        ((h1.const_mul (8 * (M : ℝ))).mul_const (eLpNorm (Pfun p q) 2 volume).toReal)).add
        ((hσ.const_mul (192 * (M : ℝ))).mul h3))
      simpa [δpq, mul_assoc] using this
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun p _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun q _ => hpq p q
    simpa [δ] using this
  -- the eventual estimate
  filter_upwards [(tendsto_order.1 hσ).2 (1 / 32) (by norm_num)] with k hk
  have hch : ∀ x μ ν, ((n k : ℝ))⁻¹ * normSum (slots (A k) x μ ν) ≤ 1 / 32 :=
    fun x μ ν => (hslot k x μ ν).trans hk.le
  refine ⟨hch, fun a ha μ ν => ?_⟩
  -- pointwise bound for every pair
  set bnd : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → ℝ := fun p q y =>
    6 * M * ((n k : ℝ))⁻¹ + 4 * M * Dfun k p q y + 8 * M * ((n k : ℝ))⁻¹ * Pfun p q y +
      192 * M * σ k * Sfun k p q y
  have hbnd0 : ∀ p q y, 0 ≤ bnd p q y := by
    intro p q y
    simp only [bnd, Dfun, Pfun, Sfun]
    have := hσ0 k
    positivity
  have hpt : ∀ p q y, ‖curvVar (n k) (A k) (sampleTest (n k) a)
      (TorusPiecewiseConstantTranslation.index (n k) y) p q - DaT A₀ a y p q‖ ≤ bnd p q y := by
    intro p q y
    have := norm_curvVar_sub_DaT_le a ha (A k) A₀ y p q (hch _ p q) (hslot k _ p q)
    rw [hDslot, hPslot, hSslot] at this
    exact this
  have hall : ∀ y, ‖pc (fun x => FextV (n k) (A k) (sampleTest (n k) a) x μ ν) y - DaT A₀ a y μ ν‖ ≤
      ∑ p, ∑ q, bnd p q y := by
    intro y
    have hle : ∀ p q, bnd p q y ≤ ∑ p, ∑ q, bnd p q y := fun p q =>
      (Finset.single_le_sum (f := fun q => bnd p q y) (fun q _ => hbnd0 p q y)
        (Finset.mem_univ q)).trans (Finset.single_le_sum (f := fun p => ∑ q, bnd p q y)
          (fun p _ => Finset.sum_nonneg fun q _ => hbnd0 p q y) (Finset.mem_univ p))
    simp only [pc, FextV]
    split_ifs with h1 h2
    · exact (hpt μ ν y).trans (hle μ ν)
    · rw [DaT_antisymm A₀ a y ν μ, neg_sub_neg, norm_sub_rev]
      exact (hpt ν μ y).trans (hle ν μ)
    · have : μ = ν := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      subst this
      rw [DaT_self, sub_zero, norm_zero]
      exact (hbnd0 μ μ y).trans (hle μ μ)
  -- integrate
  have hbmem : ∀ p q, MemLp (bnd p q) 2 volume := by
    intro p q
    have h1 : MemLp (fun _ : UnitAddTorus (Fin 4) => 6 * M * ((n k : ℝ))⁻¹) 2 volume := memLp_const _
    have h2 := ((hDL p q).memLp k).const_mul (4 * M)
    have h3 := (hPmem p q).const_mul (8 * M * ((n k : ℝ))⁻¹)
    have h4 := ((hSL p q).memLp k).const_mul (192 * M * σ k)
    exact ((h1.add h2).add h3).add h4
  have hbδ : ∀ p q, (eLpNorm (bnd p q) 2 volume).toReal ≤ δpq k p q := by
    intro p q
    have h1 : MemLp (fun _ : UnitAddTorus (Fin 4) => 6 * M * ((n k : ℝ))⁻¹) 2 volume := memLp_const _
    have h2 := ((hDL p q).memLp k).const_mul (4 * M)
    have h3 := (hPmem p q).const_mul (8 * M * ((n k : ℝ))⁻¹)
    have h4 := ((hSL p q).memLp k).const_mul (192 * M * σ k)
    have e : bnd p q = (((fun _ => 6 * M * ((n k : ℝ))⁻¹) + fun y => 4 * M * Dfun k p q y) +
        fun y => 8 * M * ((n k : ℝ))⁻¹ * Pfun p q y) + fun y => 192 * M * σ k * Sfun k p q y := by
      funext y; simp only [bnd, Pi.add_apply]
    rw [e]
    calc (eLpNorm ((((fun _ => 6 * M * ((n k : ℝ))⁻¹) + fun y => 4 * M * Dfun k p q y) +
          fun y => 8 * M * ((n k : ℝ))⁻¹ * Pfun p q y) + fun y => 192 * M * σ k * Sfun k p q y)
          2 volume).toReal
        ≤ (eLpNorm (((fun _ => 6 * M * ((n k : ℝ))⁻¹) + fun y => 4 * M * Dfun k p q y) +
          fun y => 8 * M * ((n k : ℝ))⁻¹ * Pfun p q y) 2 volume).toReal +
          (eLpNorm (fun y => 192 * M * σ k * Sfun k p q y) 2 volume).toReal :=
          toReal_eLpNorm_add_le ((h1.add h2).add h3) h4
      _ ≤ ((eLpNorm ((fun _ => 6 * M * ((n k : ℝ))⁻¹) + fun y => 4 * M * Dfun k p q y) 2
          volume).toReal + (eLpNorm (fun y => 8 * M * ((n k : ℝ))⁻¹ * Pfun p q y) 2 volume).toReal) +
          (eLpNorm (fun y => 192 * M * σ k * Sfun k p q y) 2 volume).toReal :=
          add_le_add (toReal_eLpNorm_add_le (h1.add h2) h3) le_rfl
      _ ≤ (((eLpNorm (fun _ : UnitAddTorus (Fin 4) => 6 * M * ((n k : ℝ))⁻¹) 2 volume).toReal +
          (eLpNorm (fun y => 4 * M * Dfun k p q y) 2 volume).toReal) +
          (eLpNorm (fun y => 8 * M * ((n k : ℝ))⁻¹ * Pfun p q y) 2 volume).toReal) +
          (eLpNorm (fun y => 192 * M * σ k * Sfun k p q y) 2 volume).toReal :=
          add_le_add (add_le_add (toReal_eLpNorm_add_le h1 h2) le_rfl) le_rfl
      _ = δpq k p q := by
          rw [toReal_eLpNorm_const _ (by positivity), toReal_eLpNorm_const_mul (by positivity),
            toReal_eLpNorm_const_mul (by positivity), toReal_eLpNorm_const_mul
              (mul_nonneg (by positivity) (hσ0 k))]
  have hsum_mem : MemLp (fun y => ∑ p, ∑ q, bnd p q y) 2 volume := by
    have : (fun y => ∑ p, ∑ q, bnd p q y) = ∑ p, ∑ q, bnd p q := by
      funext y; simp [Finset.sum_apply]
    rw [this]
    exact memLp_finset_sum' _ fun p _ => memLp_finset_sum' _ fun q _ => hbmem p q
  refine (toReal_eLpNorm_mono hsum_mem fun y => ?_).trans ?_
  · rw [Real.norm_of_nonneg (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
      hbnd0 p q y)]
    exact hall y
  · have hsum : (eLpNorm (fun y => ∑ p, ∑ q, bnd p q y) 2 volume).toReal ≤
        ∑ p, ∑ q, (eLpNorm (bnd p q) 2 volume).toReal := by
      have e : (fun y => ∑ p, ∑ q, bnd p q y) = ∑ p, ∑ q, bnd p q := by
        funext y; simp [Finset.sum_apply]
      rw [e]
      have hle := eLpNorm_sum_le (s := Finset.univ) (f := fun p => ∑ q, bnd p q)
        (μ := (volume : Measure (UnitAddTorus (Fin 4)))) (p := 2)
        (fun p _ => (memLp_finset_sum' _ fun q _ => hbmem p q).1) (by norm_num)
      have hle2 : ∀ p, eLpNorm (∑ q, bnd p q) 2 volume ≤ ∑ q, eLpNorm (bnd p q) 2 volume :=
        fun p => eLpNorm_sum_le (fun q _ => (hbmem p q).1) (by norm_num)
      have hfin : ∀ p q, eLpNorm (bnd p q) 2 volume ≠ ∞ := fun p q => (hbmem p q).2.ne
      calc (eLpNorm (∑ p, ∑ q, bnd p q) 2 volume).toReal
          ≤ (∑ p, ∑ q, eLpNorm (bnd p q) 2 volume).toReal := by
            refine ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun p _ =>
              ENNReal.sum_ne_top.2 fun q _ => hfin p q) (hle.trans (Finset.sum_le_sum fun p _ =>
                hle2 p))
        _ = ∑ p, ∑ q, (eLpNorm (bnd p q) 2 volume).toReal := by
            rw [ENNReal.toReal_sum fun p _ => ENNReal.sum_ne_top.2 fun q _ => hfin p q]
            exact Finset.sum_congr rfl fun p _ => ENNReal.toReal_sum fun q _ => hfin p q
    exact hsum.trans (Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hbδ p q)

end UnifL2

/-! ### Uniform convergence of the coefficient-weighted terms -/

section Terms

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fact_one_le_two_s : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance holder221_s : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

/-- `∫ R_h^0 u = h⁴ Σ_x u(x)` (unit torus, `h = 1/N`). -/
theorem integral_pc_real {N : ℕ} [NeZero N] (u : LatticeTorusPlancherel.Grid 4 N → ℝ) :
    ∫ y, pc u y = ((N : ℝ)⁻¹) ^ 4 * ∑ x, u x := by
  have h := pc_eq_sum_indicator (d := Fin 4) (N := N) u
  have e : (fun y => pc u y) = fun y => ∑ g, (cellD g).indicator (fun _ => u g) y := by
    funext y
    rw [← Finset.sum_apply, ← h]
  rw [e, integral_finset_sum _ fun g _ =>
    (integrable_const (u g)).indicator (measurableSet_cellD g)]
  simp_rw [integral_indicator_const _ (measurableSet_cellD _)]
  have hv : ∀ g : LatticeTorusPlancherel.Grid 4 N,
      (volume : Measure (UnitAddTorus (Fin 4))).real (cellD g) = ((N : ℝ)⁻¹) ^ 4 := by
    intro g
    rw [Measure.real_def, volume_cellD, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
      Fintype.card_fin, one_div]
  simp only [hv, smul_eq_mul, Finset.mul_sum]

/-- `|∫ f - ∫ g| ≤ ‖f - g‖_{L¹}`. -/
theorem abs_integral_sub_le {f g : UnitAddTorus (Fin 4) → ℝ} (hf : Integrable f volume)
    (hg : Integrable g volume) : |(∫ y, f y) - ∫ y, g y| ≤ (eLpNorm (f - g) 1 volume).toReal := by
  rw [← integral_sub hf hg]
  refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
  have hfg : Integrable (fun a => |f a - g a|) volume := (hf.sub hg).abs
  rw [eLpNorm_one_eq_lintegral_enorm, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun y => abs_nonneg _) hfg.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun y => ?_
  simp [Real.enorm_eq_ofReal_abs]

/-- **Cauchy–Schwarz**: `|∫ ⟪u, v⟫| ≤ ‖u‖_{L²} ‖v‖_{L²}`. -/
theorem abs_integral_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : UnitAddTorus (Fin 4) → E} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    |∫ y, ⟪u y, v y⟫| ≤ (eLpNorm u 2 volume).toReal * (eLpNorm v 2 volume).toReal := by
  have hB := eLpNorm_bilin_le' (p := 2) (q := 2) (r := 1) (ν := (volume : Measure
    (UnitAddTorus (Fin 4)))) (innerSL ℝ (E := E)) hu.1 hv.1
  have hn : ‖(innerSL ℝ (E := E))‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe]; exact norm_innerSL_le ℝ
  have hint : Integrable (fun y => ⟪u y, v y⟫) volume :=
    (LpTendsto.bilin (p := 2) (q := 2) (r := 1) (innerSL ℝ (E := E)) (LpTendsto.const hu)
      (LpTendsto.const hv)).memLp_lim.integrable le_rfl
  refine (abs_integral_le_integral_abs).trans ?_
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => abs_nonneg _)
    hint.abs.aestronglyMeasurable]
  have h1 : ∫⁻ y, ENNReal.ofReal |⟪u y, v y⟫| = eLpNorm (fun y => (innerSL ℝ (E := E)) (u y) (v y))
      1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr fun y => ?_
    simp [Real.enorm_eq_ofReal_abs]
  rw [h1]
  have h2 : eLpNorm (fun y => (innerSL ℝ (E := E)) (u y) (v y)) 1 volume ≤
      eLpNorm u 2 volume * eLpNorm v 2 volume := by
    refine hB.trans ?_
    calc (‖(innerSL ℝ (E := E))‖₊ : ℝ≥0∞) * eLpNorm u 2 volume * eLpNorm v 2 volume
        ≤ 1 * eLpNorm u 2 volume * eLpNorm v 2 volume := by gcongr; exact_mod_cast hn
      _ = _ := by rw [one_mul]
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hu.2.ne hv.2.ne) h2

/-- **Uniform scalar term**: if `R_h^0 g_h → g` in `L¹`, then
`|∫ R_h^0(φ(x/N) g_h) - ∫ φ g| ≤ M ‖R_h^0 g_h - g‖_{L¹} + η ‖g‖_{L¹}` for every `φ` with
`|φ| ≤ M` and `|φ(x/N) - φ| ≤ η` on the cells. -/
theorem abs_integral_sample_mul_sub_le {N : ℕ} [NeZero N] (gh : LatticeTorusPlancherel.Grid 4 N → ℝ)
    {g : UnitAddTorus (Fin 4) → ℝ} (hg : Integrable g volume) (φ : UnitAddTorus (Fin 4) → ℝ)
    (hφm : Continuous φ) {M η : ℝ} (hM : ∀ y, |φ y| ≤ M)
    (hη : ∀ y, |φ (TorusCellEmbedding.samplePt (TorusPiecewiseConstantTranslation.index N y)) - φ y| ≤ η) :
    |(∫ y, pc (fun x => φ (TorusCellEmbedding.samplePt x) * gh x) y) - ∫ y, φ y * g y| ≤
      M * (eLpNorm (pc gh - g) 1 volume).toReal + η * (eLpNorm g 1 volume).toReal := by
  have hgh : Integrable (pc gh) volume := (memLp_pc_gen gh 1).integrable le_rfl
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0)
  set ψ : UnitAddTorus (Fin 4) → ℝ := fun y =>
    φ (TorusCellEmbedding.samplePt (TorusPiecewiseConstantTranslation.index N y))
  have hψm : AEStronglyMeasurable ψ volume :=
    (stronglyMeasurable_pc (fun x => φ (TorusCellEmbedding.samplePt x))).aestronglyMeasurable
  have hψ : ∀ y, |ψ y| ≤ M := fun y => hM _
  have e : (fun y => pc (fun x => φ (TorusCellEmbedding.samplePt x) * gh x) y) =
      fun y => ψ y * pc gh y := rfl
  rw [e]
  have i1 : Integrable (fun y => ψ y * pc gh y) volume := hgh.bdd_mul hψm
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hψ y)
  have i2 : Integrable (fun y => ψ y * g y) volume := hg.bdd_mul hψm
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hψ y)
  have i3 : Integrable (fun y => φ y * g y) volume := hg.bdd_mul hφm.aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)
  have hsplit : (∫ y, ψ y * pc gh y) - ∫ y, φ y * g y =
      ((∫ y, ψ y * pc gh y) - ∫ y, ψ y * g y) + ((∫ y, ψ y * g y) - ∫ y, φ y * g y) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_integral_sub_le i1 i2).trans ?_
    have hb : eLpNorm ((fun y => ψ y * pc gh y) - fun y => ψ y * g y) 1 volume ≤
        ENNReal.ofReal M * eLpNorm (pc gh - g) 1 volume := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun y => ?_) 1
      simp only [Pi.sub_apply, ← mul_sub, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hψ y) (abs_nonneg _)
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ((memLp_pc_gen gh 1).sub (memLp_one_iff_integrable.2 hg)).2.ne) hb
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0] at this
  · refine (abs_integral_sub_le i2 i3).trans ?_
    have hb : eLpNorm ((fun y => ψ y * g y) - fun y => φ y * g y) 1 volume ≤
        ENNReal.ofReal η * eLpNorm g 1 volume := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun y => ?_) 1
      simp only [Pi.sub_apply, ← sub_mul, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hη y) (abs_nonneg _)
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (memLp_one_iff_integrable.2 hg).2.ne) hb
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη0] at this

/-- **Uniform inner-product term**: `|∫ ⟪U_h, V_h⟫ - ∫ ⟪U, V⟫| ≤
‖U_h - U‖ (‖V_h - V‖ + ‖V‖) + ‖U‖ ‖V_h - V‖` (all norms in `L²`). -/
theorem abs_integral_inner_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Uh U Vh V : UnitAddTorus (Fin 4) → E} (hUh : MemLp Uh 2 volume) (hU : MemLp U 2 volume)
    (hVh : MemLp Vh 2 volume) (hV : MemLp V 2 volume) :
    |(∫ y, ⟪Uh y, Vh y⟫) - ∫ y, ⟪U y, V y⟫| ≤
      (eLpNorm (Uh - U) 2 volume).toReal * ((eLpNorm (Vh - V) 2 volume).toReal +
        (eLpNorm V 2 volume).toReal) + (eLpNorm U 2 volume).toReal * (eLpNorm (Vh - V) 2 volume).toReal := by
  have hint : ∀ {u v : UnitAddTorus (Fin 4) → E}, MemLp u 2 volume → MemLp v 2 volume →
      Integrable (fun y => ⟪u y, v y⟫) volume := fun hu hv =>
    (LpTendsto.bilin (p := 2) (q := 2) (r := 1) (innerSL ℝ (E := E)) (LpTendsto.const hu)
      (LpTendsto.const hv)).memLp_lim.integrable le_rfl
  have e : (∫ y, ⟪Uh y, Vh y⟫) - ∫ y, ⟪U y, V y⟫ =
      (∫ y, ⟪(Uh - U) y, Vh y⟫) + ∫ y, ⟪U y, (Vh - V) y⟫ := by
    rw [← integral_add (hint (hUh.sub hU) hVh) (hint hU (hVh.sub hV)),
      ← integral_sub (hint hUh hVh) (hint hU hV)]
    congr 1; funext y
    simp only [Pi.sub_apply, inner_sub_left, inner_sub_right]
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ (abs_integral_inner_le hU (hVh.sub hV)))
  refine (abs_integral_inner_le (hUh.sub hU) hVh).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  have : Vh = (Vh - V) + V := by abel
  calc (eLpNorm Vh 2 volume).toReal = (eLpNorm ((Vh - V) + V) 2 volume).toReal := by
        rw [← this]
    _ ≤ _ := toReal_eLpNorm_add_le (hVh.sub hV) hV

end Terms

/-! ### Bounded coefficients converging in measure -/

section Coefs

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- **Coefficient products** (`lem:products`, bounded-coefficient clause, specialised): for `Φ`
continuous on a compact chart `K` containing all coframe values, if `R_h^0 e_h → e` in `L²` and
`u_h → u` in `L^p` (`1 ≤ p < ∞`), then `Φ(R_h^0 e_h) u_h → Φ(e) u` in `L^p`. -/
theorem lpTendsto_coef_smul {K : Set Cof} (hK : IsCompact K) {Φ : Cof → ℝ} (hΦ : ContinuousOn Φ K)
    {e : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Cof} {e₀ : UnitAddTorus (Fin 4) → Cof}
    (he : LpTendsto volume 2 (fun k => pc (e k)) e₀) (heK : ∀ k x, e k x ∈ K)
    (he₀K : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin 4))), e₀ y ∈ K)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {u : ℕ → UnitAddTorus (Fin 4) → F} {u₀ : UnitAddTorus (Fin 4) → F}
    (hu : LpTendsto volume p u u₀) :
    LpTendsto volume p (fun k y => Φ (pc (e k) y) • u k y) (fun y => Φ (e₀ y) • u₀ y) := by
  set Ψ : Cof → F →L[ℝ] F := fun c => Φ c • ContinuousLinearMap.id ℝ F
  have hΨ : ContinuousOn Ψ K := hΦ.smul continuousOn_const
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΨ
  have hin : TendstoInMeasure volume (fun k y => pc (e k) y) atTop e₀ :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (fun k => (he.memLp k).1) he.memLp_lim.1
      he.tendsto
  have hmeas := LpProductContinuity.tendstoInMeasure_comp_of_continuousOn hK hΨ
    (fun k => Eventually.of_forall fun y => heK k _) he₀K hin
  have hβm : ∀ k, AEStronglyMeasurable (fun y => Ψ (pc (e k) y)) volume := fun k =>
    (stronglyMeasurable_pc (fun x => Ψ (e k x))).aestronglyMeasurable
  have h := LpProductContinuity.LpTendsto.coeff hp hβm hmeas (K := C)
    (fun k => Eventually.of_forall fun y => hC _ (heK k _)) hu
  refine h.congr (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · simp [Ψ]
  · simp [Ψ]

/-- The scalar coefficient converges in measure and is bounded; its limit is a.e. strongly
measurable. -/
theorem coef_aestronglyMeasurable {K : Set Cof} (hK : IsCompact K) {Φ : Cof → ℝ}
    (hΦ : ContinuousOn Φ K) {e : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Cof}
    {e₀ : UnitAddTorus (Fin 4) → Cof} (he : LpTendsto volume 2 (fun k => pc (e k)) e₀)
    (heK : ∀ k x, e k x ∈ K) (he₀K : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin 4))), e₀ y ∈ K) :
    AEStronglyMeasurable (fun y => Φ (e₀ y)) volume ∧ ∃ C, ∀ᵐ y ∂(volume : Measure
      (UnitAddTorus (Fin 4))), |Φ (e₀ y)| ≤ C := by
  have hin : TendstoInMeasure volume (fun k y => pc (e k) y) atTop e₀ :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (fun k => (he.memLp k).1) he.memLp_lim.1
      he.tendsto
  have hmeas := LpProductContinuity.tendstoInMeasure_comp_of_continuousOn hK hΦ
    (fun k => Eventually.of_forall fun y => heK k _) he₀K hin
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ
  refine ⟨hmeas.aestronglyMeasurable fun k =>
    (stronglyMeasurable_pc (fun x => Φ (e k x))).aestronglyMeasurable, C, ?_⟩
  filter_upwards [he₀K] with y hy
  rw [← Real.norm_eq_abs]; exact hC _ hy

end Coefs

/-! ### The metric clause of `prop:native-YM-identification` -/

section MetricClause

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fact_one_le_two_y : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance holder221_y : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

/-- The antisymmetric extension of a continuum two-form given on `μ < ν`. -/
def FextC (F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (y : UnitAddTorus (Fin 4))
    (μ ν : Fin 4) : 𝔸 :=
  if μ < ν then F μ ν y else if ν < μ then -F ν μ y else 0

/-- **The continuum Yang–Mills first variation** at `(e, A)` with curvature `F`, along the metric
test `k` (through the symmetric lift `ė(k)`) and the gauge test `a`:
`∫ -¼ [D_eΘ(e)[ė(k)]^{μνρσ} ⟨F_{μν}, F_{ρσ}⟩ + Θ^{μνρσ}(⟨F_{μν}, (d_Aa)_{ρσ}⟩ + ⟨(d_Aa)_{μν}, F_{ρσ}⟩)]`. -/
def firstVarCont (T : 𝔸 →L[ℝ] E) (e₀ : UnitAddTorus (Fin 4) → Cof)
    (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸)
    (k : UnitAddTorus (Fin 4) → Cof) (a : C1Test 𝔸) : ℝ :=
  ∫ y, varDens T (ymCoef (e₀ y)) (dCoef (e₀ y) (k y)) (FextC F y) (fun μ ν => DaT A₀ a y μ ν)

/-- The elementary symmetric-tensor directions. -/
def Eab (α β : Fin 4) : Cof := fun a b => if a = α ∧ b = β then 1 else 0

theorem liftK_linear (e k : Cof) : liftK e k = ∑ α, ∑ β, k α β • liftK e (Eab α β) := by
  funext a μ
  simp only [liftK, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Eab]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have : ∑ α', ∑ β', e a α' * gMet e μ β' * (if α' = α ∧ β' = β then (1 : ℝ) else 0) =
      e a α * gMet e μ β := by
    rw [Finset.sum_eq_single α]
    · rw [Finset.sum_eq_single β]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [this]; ring

theorem dCoef_linear (e k : Cof) (μ ν ρ σ : Fin 4) :
    dCoef e k μ ν ρ σ = ∑ α, ∑ β, k α β * dCoef e (Eab α β) μ ν ρ σ := by
  simp only [dCoef]
  rw [liftK_linear e k]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end MetricClause

section MetricClause2

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The three pieces of the first-variation density. -/
def vt1 (T : 𝔸 →L[ℝ] E) (D : Fin 4 → Fin 4 → Coef4) (k : Cof) (F : Fin 4 → Fin 4 → 𝔸) : ℝ :=
  ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ α, ∑ β, k α β * (D α β μ ν ρ σ * ⟪T (F μ ν), T (F ρ σ)⟫)

/-- Second piece `Σ ⟨θ F_{μν}, F'_{ρσ}⟩`. -/
def vt2 (T : 𝔸 →L[ℝ] E) (θ : Coef4) (F F' : Fin 4 → Fin 4 → 𝔸) : ℝ :=
  ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ⟪θ μ ν ρ σ • T (F μ ν), T (F' ρ σ)⟫

/-- Third piece `Σ ⟨θ F_{ρσ}, F'_{μν}⟩`. -/
def vt3 (T : 𝔸 →L[ℝ] E) (θ : Coef4) (F F' : Fin 4 → Fin 4 → 𝔸) : ℝ :=
  ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ⟪θ μ ν ρ σ • T (F ρ σ), T (F' μ ν)⟫

theorem varDens_expand (T : 𝔸 →L[ℝ] E) (e k : Cof) (F F' : Fin 4 → Fin 4 → 𝔸) :
    varDens T (ymCoef e) (dCoef e k) F F' =
      -(1 / 4) * (vt1 T (fun α β => dCoef e (Eab α β)) k F + vt2 T (ymCoef e) F F' +
        vt3 T (ymCoef e) F F') := by
  simp only [varDens, vt1, vt2, vt3, dCoef_linear e k, real_inner_smul_left]
  congr 1
  simp only [← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [real_inner_comm (T (F' μ ν))]
  have : ∑ α, ∑ β, k α β * dCoef e (Eab α β) μ ν ρ σ * ⟪T (F μ ν), T (F ρ σ)⟫ =
      ∑ α, ∑ β, k α β * (dCoef e (Eab α β) μ ν ρ σ * ⟪T (F μ ν), T (F ρ σ)⟫) := by
    simp only [mul_assoc]
  rw [this]
  ring

end MetricClause2

section MetricMain

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fact_one_le_two_z : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_z : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance holder221_z : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

theorem abs_sum_sub_le {ι : Type*} [Fintype ι] (f g b : ι → ℝ) (h : ∀ i, |f i - g i| ≤ b i) :
    |∑ i, f i - ∑ i, g i| ≤ ∑ i, b i := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h i)

theorem lpTendsto_Fext {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hF : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x => curvLog (n k) (A k) x μ ν)) (F μ ν))
    (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => Fext (n k) (A k) x μ ν)) (fun y => FextC F y μ ν) := by
  by_cases h1 : μ < ν
  · refine (hF μ ν).congr (fun k => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · simp [pc, Fext, h1]
    · simp [FextC, h1]
  · by_cases h2 : ν < μ
    · refine (hF ν μ).neg.congr (fun k => Eventually.of_forall fun y => ?_)
        (Eventually.of_forall fun y => ?_)
      · simp [pc, Fext, h1, h2]
      · simp [FextC, h1, h2]
    · refine (LpTendsto.const (p := 2) (ν := (volume : Measure (UnitAddTorus (Fin 4))))
        (MemLp.zero : MemLp (0 : UnitAddTorus (Fin 4) → 𝔸) 2 volume)).congr
        (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
      · simp [pc, Fext, h1, h2]
      · simp [FextC, h1, h2]

theorem norm_DaT_le {M : NNReal} (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (a : C1Test 𝔸)
    (ha : GaugeBound M a) (y : UnitAddTorus (Fin 4)) (ρ σ : Fin 4) :
    ‖DaT A₀ a y ρ σ‖ ≤ M * (2 + 2 * (‖A₀ ρ y‖ + ‖A₀ σ y‖)) := by
  have h1 := ha.da_le ρ σ y
  have h2 := ha.da_le σ ρ y
  have h3 := ha.a_le σ y
  have h4 := ha.a_le ρ y
  have n1 := norm_mul_le (A₀ ρ y) (a.a σ y)
  have n2 := norm_mul_le (a.a σ y) (A₀ ρ y)
  have n3 := norm_mul_le (a.a ρ y) (A₀ σ y)
  have n4 := norm_mul_le (A₀ σ y) (a.a ρ y)
  have hA1 := norm_nonneg (A₀ ρ y)
  have hA2 := norm_nonneg (A₀ σ y)
  simp only [DaT]
  calc ‖a.da ρ σ y - a.da σ ρ y + (A₀ ρ y * a.a σ y - a.a σ y * A₀ ρ y +
        (a.a ρ y * A₀ σ y - A₀ σ y * a.a ρ y))‖
      ≤ (‖a.da ρ σ y‖ + ‖a.da σ ρ y‖) + ((‖A₀ ρ y * a.a σ y‖ + ‖a.a σ y * A₀ ρ y‖) +
          (‖a.a ρ y * A₀ σ y‖ + ‖A₀ σ y * a.a ρ y‖)) := by
        refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ((norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))))
    _ ≤ M * (2 + 2 * (‖A₀ ρ y‖ + ‖A₀ σ y‖)) := by nlinarith

end MetricMain

section MetricTheorem

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fact_one_le_two_w : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_w : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance holder221_w : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

theorem integral_pc_sum {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι)
    (f : ι → LatticeTorusPlancherel.Grid 4 N → ℝ) :
    ∫ y, pc (fun x => ∑ i ∈ s, f i x) y = ∑ i ∈ s, ∫ y, pc (f i) y := by
  simp only [integral_pc_real, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem integral_pc_mul_left {N : ℕ} [NeZero N] (c : ℝ) (f : LatticeTorusPlancherel.Grid 4 N → ℝ) :
    ∫ y, pc (fun x => c * f x) y = c * ∫ y, pc f y := by
  simp only [integral_pc_real, ← Finset.mul_sum]
  ring

theorem integral_pc_add {N : ℕ} [NeZero N] (f g : LatticeTorusPlancherel.Grid 4 N → ℝ) :
    ∫ y, pc (fun x => f x + g x) y = (∫ y, pc f y) + ∫ y, pc g y := by
  simp only [integral_pc_real, Finset.sum_add_distrib]
  ring

theorem sum_swap4 {X : Type*} [Fintype X] (f : X → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ x, ∑ μ, ∑ ν, ∑ ρ, ∑ σ, f x μ ν ρ σ = ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ x, f x μ ν ρ σ := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_comm]

theorem sum_swap2 {X : Type*} [Fintype X] (f : X → Fin 4 → Fin 4 → ℝ) :
    ∑ x, ∑ α, ∑ β, f x α β = ∑ α, ∑ β, ∑ x, f x α β := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]

/-- The grid form of the expanded first variation. -/
theorem firstVarYM_eq [NeZero N] (T : 𝔸 →L[ℝ] E) (e : LatticeTorusPlancherel.Grid 4 N → Cof)
    (kt : UnitAddTorus (Fin 4) → Cof) (A w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (he : ∀ x, e x ∈ GLc) (hch : ∀ x μ ν, (N : ℝ)⁻¹ * normSum (slots A x μ ν) ≤ 1 / 32) :
    firstVarYM T N e (fun x => liftK (e x) (kt (TorusCellEmbedding.samplePt x))) A w =
      -(1 / 4) * ((∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ α, ∑ β, ∫ y, pc (fun x =>
          kt (TorusCellEmbedding.samplePt x) α β * (dCoef (e x) (Eab α β) μ ν ρ σ *
            ⟪T (Fext N A x μ ν), T (Fext N A x ρ σ)⟫)) y) +
        (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∫ y, pc (fun x => ⟪ymCoef (e x) μ ν ρ σ • T (Fext N A x μ ν),
          T (FextV N A w x ρ σ)⟫) y) +
        (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∫ y, pc (fun x => ⟪ymCoef (e x) μ ν ρ σ • T (Fext N A x ρ σ),
          T (FextV N A w x μ ν)⟫) y)) := by
  rw [firstVarYM, (hasDerivAt_actionYM T e _ A w he hch).deriv, ← integral_pc_real]
  have hd : ∀ x, fderiv ℝ ymCoef (e x) (liftK (e x) (kt (TorusCellEmbedding.samplePt x))) =
      dCoef (e x) (kt (TorusCellEmbedding.samplePt x)) := fun x => rfl
  simp only [hd, varDens_expand, vt1, vt2, vt3, integral_pc_mul_left, integral_pc_add,
    integral_pc_sum]

end MetricTheorem

section MetricTheorem2

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

theorem integral_sum4 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → ℝ)
    (hf : ∀ μ ν ρ σ, Integrable (f μ ν ρ σ) volume) :
    ∫ y, ∑ μ, ∑ ν, ∑ ρ, ∑ σ, f μ ν ρ σ y = ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∫ y, f μ ν ρ σ y := by
  rw [integral_finset_sum _ fun μ _ => integrable_finset_sum _ fun ν _ =>
    integrable_finset_sum _ fun ρ _ => integrable_finset_sum _ fun σ _ => hf μ ν ρ σ]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [integral_finset_sum _ fun ν _ => integrable_finset_sum _ fun ρ _ =>
    integrable_finset_sum _ fun σ _ => hf μ ν ρ σ]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [integral_finset_sum _ fun ρ _ => integrable_finset_sum _ fun σ _ => hf μ ν ρ σ]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [integral_finset_sum _ fun σ _ => hf μ ν ρ σ]

theorem integral_sum2 (f : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → ℝ)
    (hf : ∀ α β, Integrable (f α β) volume) :
    ∫ y, ∑ α, ∑ β, f α β y = ∑ α, ∑ β, ∫ y, f α β y := by
  rw [integral_finset_sum _ fun α _ => integrable_finset_sum _ fun β _ => hf α β]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_finset_sum _ fun β _ => hf α β]

/-- First continuum piece (metric row, coordinate `(α, β)` of the metric test). -/
def w1 (T : 𝔸 →L[ℝ] E) (e₀ : UnitAddTorus (Fin 4) → Cof)
    (F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (kt : UnitAddTorus (Fin 4) → Cof)
    (μ ν ρ σ α β : Fin 4) (y : UnitAddTorus (Fin 4)) : ℝ :=
  kt y α β * (dCoef (e₀ y) (Eab α β) μ ν ρ σ * ⟪T (FextC F y μ ν), T (FextC F y ρ σ)⟫)

/-- Second continuum piece (gauge row). -/
def w2 (T : 𝔸 →L[ℝ] E) (e₀ : UnitAddTorus (Fin 4) → Cof)
    (F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸)
    (a : C1Test 𝔸) (μ ν ρ σ : Fin 4) (y : UnitAddTorus (Fin 4)) : ℝ :=
  ⟪ymCoef (e₀ y) μ ν ρ σ • T (FextC F y μ ν), T (DaT A₀ a y ρ σ)⟫

/-- Third continuum piece (gauge row, transposed). -/
def w3 (T : 𝔸 →L[ℝ] E) (e₀ : UnitAddTorus (Fin 4) → Cof)
    (F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸)
    (a : C1Test 𝔸) (μ ν ρ σ : Fin 4) (y : UnitAddTorus (Fin 4)) : ℝ :=
  ⟪ymCoef (e₀ y) μ ν ρ σ • T (FextC F y ρ σ), T (DaT A₀ a y μ ν)⟫

theorem integral_add3 (P1 P2 P3 : UnitAddTorus (Fin 4) → ℝ) (h1 : Integrable P1 volume)
    (h2 : Integrable P2 volume) (h3 : Integrable P3 volume) :
    ∫ y, (P1 y + P2 y + P3 y) = (∫ y, P1 y) + (∫ y, P2 y) + ∫ y, P3 y := by
  rw [integral_add (f := fun y => P1 y + P2 y) (h1.add h2) h3, integral_add h1 h2]

/-- The continuum first variation, expanded. -/
theorem firstVarCont_eq (T : 𝔸 →L[ℝ] E) (e₀ : UnitAddTorus (Fin 4) → Cof)
    (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸)
    (kt : UnitAddTorus (Fin 4) → Cof) (a : C1Test 𝔸)
    (h1 : ∀ μ ν ρ σ α β, Integrable (w1 T e₀ F kt μ ν ρ σ α β) volume)
    (h2 : ∀ μ ν ρ σ, Integrable (w2 T e₀ F A₀ a μ ν ρ σ) volume)
    (h3 : ∀ μ ν ρ σ, Integrable (w3 T e₀ F A₀ a μ ν ρ σ) volume) :
    firstVarCont T e₀ A₀ F kt a =
      -(1 / 4) * ((∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ α, ∑ β, ∫ y, w1 T e₀ F kt μ ν ρ σ α β y) +
        (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∫ y, w2 T e₀ F A₀ a μ ν ρ σ y) +
        (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∫ y, w3 T e₀ F A₀ a μ ν ρ σ y)) := by
  have hpt : ∀ y, varDens T (ymCoef (e₀ y)) (dCoef (e₀ y) (kt y)) (FextC F y)
      (fun μ ν => DaT A₀ a y μ ν) =
      -(1 / 4) * ((∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ α, ∑ β, w1 T e₀ F kt μ ν ρ σ α β y) +
        (∑ μ, ∑ ν, ∑ ρ, ∑ σ, w2 T e₀ F A₀ a μ ν ρ σ y) +
        (∑ μ, ∑ ν, ∑ ρ, ∑ σ, w3 T e₀ F A₀ a μ ν ρ σ y)) := by
    intro y
    rw [varDens_expand]
    rfl
  have i1 : ∀ μ ν ρ σ, Integrable (fun y => ∑ α, ∑ β, w1 T e₀ F kt μ ν ρ σ α β y) volume :=
    fun μ ν ρ σ => integrable_finset_sum _ fun α _ => integrable_finset_sum _ fun β _ =>
      h1 μ ν ρ σ α β
  have j1 : Integrable (fun y => ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ α, ∑ β, w1 T e₀ F kt μ ν ρ σ α β y) volume :=
    integrable_finset_sum _ fun μ _ => integrable_finset_sum _ fun ν _ =>
      integrable_finset_sum _ fun ρ _ => integrable_finset_sum _ fun σ _ => i1 μ ν ρ σ
  have j2 : Integrable (fun y => ∑ μ, ∑ ν, ∑ ρ, ∑ σ, w2 T e₀ F A₀ a μ ν ρ σ y) volume :=
    integrable_finset_sum _ fun μ _ => integrable_finset_sum _ fun ν _ =>
      integrable_finset_sum _ fun ρ _ => integrable_finset_sum _ fun σ _ => h2 μ ν ρ σ
  have j3 : Integrable (fun y => ∑ μ, ∑ ν, ∑ ρ, ∑ σ, w3 T e₀ F A₀ a μ ν ρ σ y) volume :=
    integrable_finset_sum _ fun μ _ => integrable_finset_sum _ fun ν _ =>
      integrable_finset_sum _ fun ρ _ => integrable_finset_sum _ fun σ _ => h3 μ ν ρ σ
  have hs : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∫ y, ∑ α, ∑ β, w1 T e₀ F kt μ ν ρ σ α β y) =
      ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ α, ∑ β, ∫ y, w1 T e₀ F kt μ ν ρ σ α β y :=
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
      Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ =>
        integral_sum2 _ fun α β => h1 μ ν ρ σ α β
  rw [firstVarCont, integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_add3 _ _ _ j1 j2 j3, integral_sum4 _ i1, integral_sum4 _ h2, integral_sum4 _ h3, hs]

end MetricTheorem2

section MetricTheorem3

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fact_one_le_two_v : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_v : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance holder221_v : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

theorem continuousOn_dCoef_eval {K : Set Cof} (hKGL : K ⊆ GLc) (α β μ ν ρ σ : Fin 4) :
    ContinuousOn (fun c : Cof => dCoef c (Eab α β) μ ν ρ σ) K := by
  have h : ContinuousOn (fun c : Cof => dCoef c (Eab α β)) K :=
    continuousOn_dCoef.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun c hc => ⟨hKGL hc, trivial⟩)
  exact (continuous_apply σ).comp_continuousOn ((continuous_apply ρ).comp_continuousOn
    ((continuous_apply ν).comp_continuousOn ((continuous_apply μ).comp_continuousOn h)))

theorem continuousOn_ymCoef_eval {K : Set Cof} (hKGL : K ⊆ GLc) (μ ν ρ σ : Fin 4) :
    ContinuousOn (fun c : Cof => ymCoef c μ ν ρ σ) K := by
  have h := continuousOn_ymCoef.mono hKGL
  exact (continuous_apply σ).comp_continuousOn ((continuous_apply ρ).comp_continuousOn
    ((continuous_apply ν).comp_continuousOn ((continuous_apply μ).comp_continuousOn h)))

theorem memLp_DaT {M : NNReal} {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA₀ : ∀ μ, MemLp (A₀ μ) 4 volume) (a : C1Test 𝔸) (ha : GaugeBound M a) (ρ σ : Fin 4) :
    MemLp (fun y => DaT A₀ a y ρ σ) 2 volume ∧
      (eLpNorm (fun y => DaT A₀ a y ρ σ) 2 volume).toReal ≤
        (M : ℝ) * (eLpNorm (fun y => (2 : ℝ) + 2 * (‖A₀ ρ y‖ + ‖A₀ σ y‖)) 2 volume).toReal := by
  have hA2 : ∀ μ, MemLp (A₀ μ) 2 volume := fun μ =>
    (hA₀ μ).mono_exponent (p := 2) (q := 4) (by norm_num)
  have hn1 : MemLp (fun y => ‖A₀ ρ y‖ + ‖A₀ σ y‖) 2 volume := (hA2 ρ).norm.add (hA2 σ).norm
  have hn2 : MemLp (fun y => (2 : ℝ) * (‖A₀ ρ y‖ + ‖A₀ σ y‖)) 2 volume := hn1.const_mul 2
  have hg : MemLp (fun y => (2 : ℝ) + 2 * (‖A₀ ρ y‖ + ‖A₀ σ y‖)) 2 volume :=
    (memLp_const (2 : ℝ)).add hn2
  have hcont : Continuous (fun p : 𝔸 × 𝔸 × UnitAddTorus (Fin 4) =>
      (a.da ρ σ p.2.2 - a.da σ ρ p.2.2) + ((p.1 * a.a σ p.2.2 - a.a σ p.2.2 * p.1) +
        (a.a ρ p.2.2 * p.2.1 - p.2.1 * a.a ρ p.2.2))) := by
    have h1 := (a.da ρ σ).continuous
    have h2 := (a.da σ ρ).continuous
    have h3 := (a.a σ).continuous
    have h4 := (a.a ρ).continuous
    fun_prop
  have hm : AEStronglyMeasurable (fun y => DaT A₀ a y ρ σ) volume :=
    hcont.comp_aestronglyMeasurable ((hA2 ρ).1.prodMk ((hA2 σ).1.prodMk aestronglyMeasurable_id))
  have hgM : MemLp (fun y => (M : ℝ) * ((2 : ℝ) + 2 * (‖A₀ ρ y‖ + ‖A₀ σ y‖))) 2 volume :=
    hg.const_mul (M : ℝ)
  have hb : ∀ y, ‖DaT A₀ a y ρ σ‖ ≤ ‖(M : ℝ) * ((2 : ℝ) + 2 * (‖A₀ ρ y‖ + ‖A₀ σ y‖))‖ := by
    intro y
    rw [Real.norm_of_nonneg (by positivity)]
    exact norm_DaT_le A₀ a ha y ρ σ
  have hmem : MemLp (fun y => DaT A₀ a y ρ σ) 2 volume := hgM.of_le hm (Eventually.of_forall hb)
  refine ⟨hmem, ?_⟩
  refine (toReal_eLpNorm_mono hgM hb).trans (le_of_eq ?_)
  exact toReal_eLpNorm_const_mul M.2

end MetricTheorem3

section MetricTheorem4

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fact_one_le_two_u : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_u : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance holder221_u : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

/-- The `L²` size of the gauge-field envelope `2 + 2(|A₀_ρ| + |A₀_σ|)`. -/
def CA (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (ρ σ : Fin 4) : ℝ :=
  (eLpNorm (fun y => (2 : ℝ) + 2 * (‖A₀ ρ y‖ + ‖A₀ σ y‖)) 2 volume).toReal

theorem tendsto_toReal_sub {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}
    {u : ℕ → UnitAddTorus (Fin 4) → F} {u₀ : UnitAddTorus (Fin 4) → F}
    (hu : LpTendsto volume p u u₀) :
    Tendsto (fun k => (eLpNorm (u k - u₀) p volume).toReal) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hu.tendsto
  rw [ENNReal.toReal_zero] at h
  exact h

theorem toReal_eLpNorm_clm_le (T : 𝔸 →L[ℝ] E) {f : UnitAddTorus (Fin 4) → 𝔸}
    (hf : MemLp f 2 volume) :
    (eLpNorm (fun y => T (f y)) 2 volume).toReal ≤ ‖T‖ * (eLpNorm f 2 volume).toReal := by
  have hb : ∀ y, ‖T (f y)‖ ≤ ‖‖T‖ * ‖f y‖‖ := fun y => by
    rw [Real.norm_of_nonneg (by positivity)]
    exact T.le_opNorm _
  refine (toReal_eLpNorm_mono (hf.norm.const_mul ‖T‖) hb).trans (le_of_eq ?_)
  rw [toReal_eLpNorm_const_mul (norm_nonneg T), eLpNorm_norm]

theorem integrable_inner_of_memLp {u v : UnitAddTorus (Fin 4) → E} (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) : Integrable (fun y => ⟪u y, v y⟫) volume :=
  (LpTendsto.bilin (p := 2) (q := 2) (r := 1) (innerSL ℝ (E := E)) (LpTendsto.const hu)
    (LpTendsto.const hv)).memLp_lim.integrable le_rfl

theorem integrable_kt_mul {M : NNReal} (kt : C(UnitAddTorus (Fin 4), Cof))
    (hkt : MetricBound M kt) {g : UnitAddTorus (Fin 4) → ℝ} (hg : Integrable g volume)
    (α β : Fin 4) : Integrable (fun y => kt y α β * g y) volume :=
  hg.bdd_mul (c := M) ((continuous_apply β).comp ((continuous_apply α).comp
    kt.continuous)).aestronglyMeasurable (Eventually.of_forall fun y =>
      (norm_le_pi_norm (kt y α) β).trans ((norm_le_pi_norm (kt y) α).trans (hkt.k_le y)))

/-- The metric-test term at fixed resolution. -/
theorem term1_le {N : ℕ} [NeZero N] {M : NNReal} (kt : C(UnitAddTorus (Fin 4), Cof))
    (hkt : MetricBound M kt) (gh : LatticeTorusPlancherel.Grid 4 N → ℝ)
    {g : UnitAddTorus (Fin 4) → ℝ} (hg : Integrable g volume) (α β : Fin 4) :
    |(∫ y, pc (fun x => kt (TorusCellEmbedding.samplePt x) α β * gh x) y) -
        ∫ y, kt y α β * g y| ≤
      (M : ℝ) * (eLpNorm (pc gh - g) 1 volume).toReal +
        (M : ℝ) * (2 * (N : ℝ)⁻¹) * (eLpNorm g 1 volume).toReal := by
  have hc : Continuous (fun y => kt y α β) :=
    (continuous_apply β).comp ((continuous_apply α).comp kt.continuous)
  have hM : ∀ y, |kt y α β| ≤ M := fun y => by
    have h1 := norm_le_pi_norm (kt y α) β
    have h2 := norm_le_pi_norm (kt y) α
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (h2.trans (hkt.k_le y))
  have hη : ∀ y, |kt (TorusCellEmbedding.samplePt (TorusPiecewiseConstantTranslation.index N y)) α β -
      kt y α β| ≤ M * (2 * (N : ℝ)⁻¹) := fun y => by
    set y₀ := TorusCellEmbedding.samplePt (TorusPiecewiseConstantTranslation.index N y)
    have h1 := norm_le_pi_norm ((kt y₀ - kt y) α) β
    have h2 := norm_le_pi_norm (kt y₀ - kt y) α
    have h3 := hkt.k_lip.dist_le_mul y₀ y
    have h4 : dist y₀ y ≤ 2 * (N : ℝ)⁻¹ := by
      have := dist_samplePt_index_add_le (N := N) y α 0 (by norm_num)
      simpa [y₀] using this
    rw [dist_eq_norm] at h3
    rw [Real.norm_eq_abs] at h1
    simp only [Pi.sub_apply] at h1 h2
    exact h1.trans (h2.trans (h3.trans (mul_le_mul_of_nonneg_left h4 M.2)))
  exact abs_integral_sample_mul_sub_le gh hg _ hc hM hη

/-- The gauge-test terms at fixed resolution. -/
theorem term2_le {Uh U Vh V : UnitAddTorus (Fin 4) → E} (hUh : MemLp Uh 2 volume)
    (hU : MemLp U 2 volume) (hVh : MemLp Vh 2 volume) (hV : MemLp V 2 volume) {d C : ℝ}
    (hd : (eLpNorm (Vh - V) 2 volume).toReal ≤ d) (hC : (eLpNorm V 2 volume).toReal ≤ C) :
    |(∫ y, ⟪Uh y, Vh y⟫) - ∫ y, ⟪U y, V y⟫| ≤
      (eLpNorm (Uh - U) 2 volume).toReal * (d + C) + (eLpNorm U 2 volume).toReal * d := by
  refine (abs_integral_inner_sub_le hUh hU hVh hV).trans ?_
  have h1 := ENNReal.toReal_nonneg (a := eLpNorm (Uh - U) 2 volume)
  have h2 := ENNReal.toReal_nonneg (a := eLpNorm U 2 volume)
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hd hC) h1)
    (mul_le_mul_of_nonneg_left hd h2)

theorem vh_bound {N : ℕ} [NeZero N] (T : 𝔸 →L[ℝ] E) {M : NNReal}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸} (hA₀ : ∀ μ, MemLp (A₀ μ) 4 volume) (a : C1Test 𝔸)
    (ha : GaugeBound M a) (v : LatticeTorusPlancherel.Grid 4 N → 𝔸) (ρ σ : Fin 4) {d : ℝ}
    (hd : (eLpNorm (fun y => pc v y - DaT A₀ a y ρ σ) 2 volume).toReal ≤ d) :
    MemLp (fun y => T (pc v y)) 2 volume ∧ MemLp (fun y => T (DaT A₀ a y ρ σ)) 2 volume ∧
      (eLpNorm ((fun y => T (pc v y)) - fun y => T (DaT A₀ a y ρ σ)) 2 volume).toReal ≤
        ‖T‖ * d ∧
      (eLpNorm (fun y => T (DaT A₀ a y ρ σ)) 2 volume).toReal ≤ ‖T‖ * ((M : ℝ) * CA A₀ ρ σ) := by
  obtain ⟨hD, hDb⟩ := memLp_DaT hA₀ a ha ρ σ
  have hv : MemLp (pc v) 2 volume := memLp_pc_gen v 2
  have hdiff : MemLp (fun y => pc v y - DaT A₀ a y ρ σ) 2 volume := hv.sub hD
  refine ⟨T.comp_memLp' hv, T.comp_memLp' hD, ?_, ?_⟩
  · have he : ((fun y => T (pc v y)) - fun y => T (DaT A₀ a y ρ σ)) =
        fun y => T (pc v y - DaT A₀ a y ρ σ) := by
      funext y
      simp [map_sub]
    rw [he]
    exact (toReal_eLpNorm_clm_le T hdiff).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg T))
  · exact (toReal_eLpNorm_clm_le T hD).trans (mul_le_mul_of_nonneg_left hDb (norm_nonneg T))

theorem tendsto_b1 (hn : Tendsto n atTop atTop) (M : NNReal)
    {G : ℕ → UnitAddTorus (Fin 4) → ℝ} {G₀ : UnitAddTorus (Fin 4) → ℝ}
    (hG : LpTendsto volume 1 G G₀) :
    Tendsto (fun k => (M : ℝ) * (eLpNorm (G k - G₀) 1 volume).toReal +
      (M : ℝ) * (2 * ((n k : ℝ))⁻¹) * (eLpNorm G₀ 1 volume).toReal) atTop (𝓝 0) := by
  have h1 := (tendsto_toReal_sub hG).const_mul (M : ℝ)
  have h2 := (((tendsto_inv_n hn).const_mul 2).const_mul (M : ℝ)).mul_const
    (eLpNorm G₀ 1 volume).toReal
  simpa using h1.add h2

theorem tendsto_b2 (T : 𝔸 →L[ℝ] E) {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (c : ℝ)
    {U : ℕ → UnitAddTorus (Fin 4) → E} {U₀ : UnitAddTorus (Fin 4) → E}
    (hU : LpTendsto volume 2 U U₀) :
    Tendsto (fun k => (eLpNorm (U k - U₀) 2 volume).toReal * (‖T‖ * δ k + ‖T‖ * c) +
      (eLpNorm U₀ 2 volume).toReal * (‖T‖ * δ k)) atTop (𝓝 0) := by
  have h1 := tendsto_toReal_sub hU
  have h2 := (hδ.const_mul ‖T‖).add_const (‖T‖ * c)
  have h3 := (hδ.const_mul ‖T‖).const_mul (eLpNorm U₀ 2 volume).toReal
  simpa using (h1.mul h2).add h3

theorem abs_sum4_sub_le (f g b : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : ∀ μ ν ρ σ, |f μ ν ρ σ - g μ ν ρ σ| ≤ b μ ν ρ σ) :
    |∑ μ, ∑ ν, ∑ ρ, ∑ σ, f μ ν ρ σ - ∑ μ, ∑ ν, ∑ ρ, ∑ σ, g μ ν ρ σ| ≤
      ∑ μ, ∑ ν, ∑ ρ, ∑ σ, b μ ν ρ σ :=
  abs_sum_sub_le _ _ _ fun μ => abs_sum_sub_le _ _ _ fun ν => abs_sum_sub_le _ _ _ fun ρ =>
    abs_sum_sub_le _ _ _ fun σ => h μ ν ρ σ

theorem abs_sum6_sub_le (f g b : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : ∀ μ ν ρ σ α β, |f μ ν ρ σ α β - g μ ν ρ σ α β| ≤ b μ ν ρ σ α β) :
    |∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ α, ∑ β, f μ ν ρ σ α β - ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ α, ∑ β, g μ ν ρ σ α β| ≤
      ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ α, ∑ β, b μ ν ρ σ α β :=
  abs_sum4_sub_le _ _ _ fun μ ν ρ σ => abs_sum_sub_le _ _ _ fun α => abs_sum_sub_le _ _ _
    fun β => h μ ν ρ σ α β

theorem abs_combo_le {a1 a2 a3 c1 c2 c3 B1 B2 B3 : ℝ} (h1 : |a1 - c1| ≤ B1)
    (h2 : |a2 - c2| ≤ B2) (h3 : |a3 - c3| ≤ B3) :
    |-(1 / 4) * (a1 + a2 + a3) - -(1 / 4) * (c1 + c2 + c3)| ≤ 1 / 4 * (B1 + B2 + B3) := by
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  rw [abs_le]
  constructor <;> linarith

end MetricTheorem4

section MetricTheorem5

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fact_one_le_two_m5 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_m5 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance holder221_m5 : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

/-- **Metric clause of `prop:native-YM-identification`** (unit-torus rendering).  Let the
reconstructed connections converge in `L⁴`, the native curvatures in `L²`, and the reconstructed
coframes in `L²` with values in a compact set `K` of invertible coframes.  Then the complete finite
first variation of the native Yang–Mills action `S_{YM,h}(e, A)` of `eq:native-densities`, taken
along the nodal symmetric lift `ė(k)` of a metric test `k` and the sampled gauge test `a`,
converges to the continuum first variation
`∫ -¼ [D_eΘ(e₀)[ė(k)] ⟨F, F⟩ + Θ(e₀)(⟨F, d_{A₀}a⟩ + ⟨d_{A₀}a, F⟩)]`,
**uniformly** over all metric tests with `‖k‖_{C^{0,1}} ≤ M` and gauge tests with
`‖a‖_{C^{1,1}} ≤ M`. -/
theorem native_YM_metric_variation (T : 𝔸 →L[ℝ] E) (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ))
    {F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hF : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x => curvLog (n k) (A k) x μ ν)) (F μ ν))
    {K : Set Cof} (hK : IsCompact K) (hKGL : K ⊆ GLc)
    {e : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Cof} {e₀ : UnitAddTorus (Fin 4) → Cof}
    (he : LpTendsto volume 2 (fun k => pc (e k)) e₀) (heK : ∀ k x, e k x ∈ K)
    (he₀K : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin 4))), e₀ y ∈ K) (M : NNReal) :
    ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧ ∀ᶠ k in atTop,
      ∀ (kt : C(UnitAddTorus (Fin 4), Cof)) (a : C1Test 𝔸), MetricBound M kt → GaugeBound M a →
        |firstVarYM T (n k) (e k) (fun x => liftK (e k x) (kt (TorusCellEmbedding.samplePt x)))
            (A k) (sampleTest (n k) a) - firstVarCont T e₀ A₀ F kt a| ≤ β k := by
  obtain ⟨δ, hδ, hev⟩ := unif_FextV hn hA M
  have hA₀ : ∀ μ, MemLp (A₀ μ) 4 volume := fun μ => (hA μ).memLp_lim
  have hip : ∀ μ ν ρ σ, LpTendsto volume 1
      (fun k y => ⟪T (pc (fun x => Fext (n k) (A k) x μ ν) y),
        T (pc (fun x => Fext (n k) (A k) x ρ σ) y)⟫)
      (fun y => ⟪T (FextC F y μ ν), T (FextC F y ρ σ)⟫) := fun μ ν ρ σ =>
    LpTendsto.bilin (p := 2) (q := 2) (r := 1) (innerSL ℝ (E := E))
      ((lpTendsto_Fext hF μ ν).clm T) ((lpTendsto_Fext hF ρ σ).clm T)
  have hG1 : ∀ μ ν ρ σ α β, LpTendsto volume 1
      (fun k => pc (fun x => dCoef (e k x) (Eab α β) μ ν ρ σ *
        ⟪T (Fext (n k) (A k) x μ ν), T (Fext (n k) (A k) x ρ σ)⟫))
      (fun y => dCoef (e₀ y) (Eab α β) μ ν ρ σ * ⟪T (FextC F y μ ν), T (FextC F y ρ σ)⟫) :=
    fun μ ν ρ σ α β => lpTendsto_coef_smul hK (continuousOn_dCoef_eval hKGL α β μ ν ρ σ) he heK
      he₀K (p := 1) ENNReal.one_ne_top (hip μ ν ρ σ)
  have hU : ∀ μ ν ρ σ μ' ν', LpTendsto volume 2
      (fun k y => ymCoef (pc (e k) y) μ ν ρ σ • T (pc (fun x => Fext (n k) (A k) x μ' ν') y))
      (fun y => ymCoef (e₀ y) μ ν ρ σ • T (FextC F y μ' ν')) := fun μ ν ρ σ μ' ν' =>
    lpTendsto_coef_smul hK (continuousOn_ymCoef_eval hKGL μ ν ρ σ) he heK he₀K (p := 2)
      (by norm_num) ((lpTendsto_Fext hF μ' ν').clm T)
  have hgi : ∀ μ ν ρ σ α β, Integrable
      (fun y => dCoef (e₀ y) (Eab α β) μ ν ρ σ * ⟪T (FextC F y μ ν), T (FextC F y ρ σ)⟫) volume :=
    fun μ ν ρ σ α β => (hG1 μ ν ρ σ α β).memLp_lim.integrable le_rfl
  refine ⟨fun k => 1 / 4 * (
    (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ α, ∑ β, ((M : ℝ) * (eLpNorm (pc (fun x =>
        dCoef (e k x) (Eab α β) μ ν ρ σ * ⟪T (Fext (n k) (A k) x μ ν), T (Fext (n k) (A k) x ρ σ)⟫) -
        fun y => dCoef (e₀ y) (Eab α β) μ ν ρ σ * ⟪T (FextC F y μ ν), T (FextC F y ρ σ)⟫) 1
          volume).toReal +
      (M : ℝ) * (2 * ((n k : ℝ))⁻¹) * (eLpNorm (fun y => dCoef (e₀ y) (Eab α β) μ ν ρ σ *
        ⟪T (FextC F y μ ν), T (FextC F y ρ σ)⟫) 1 volume).toReal)) +
    (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ((eLpNorm ((fun y => ymCoef (pc (e k) y) μ ν ρ σ •
        T (pc (fun x => Fext (n k) (A k) x μ ν) y)) - fun y => ymCoef (e₀ y) μ ν ρ σ •
        T (FextC F y μ ν)) 2 volume).toReal * (‖T‖ * δ k + ‖T‖ * ((M : ℝ) * CA A₀ ρ σ)) +
      (eLpNorm (fun y => ymCoef (e₀ y) μ ν ρ σ • T (FextC F y μ ν)) 2 volume).toReal *
        (‖T‖ * δ k))) +
    (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ((eLpNorm ((fun y => ymCoef (pc (e k) y) μ ν ρ σ •
        T (pc (fun x => Fext (n k) (A k) x ρ σ) y)) - fun y => ymCoef (e₀ y) μ ν ρ σ •
        T (FextC F y ρ σ)) 2 volume).toReal * (‖T‖ * δ k + ‖T‖ * ((M : ℝ) * CA A₀ μ ν)) +
      (eLpNorm (fun y => ymCoef (e₀ y) μ ν ρ σ • T (FextC F y ρ σ)) 2 volume).toReal *
        (‖T‖ * δ k)))), ?_, ?_⟩
  · have s1 := tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun μ _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun ν _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun ρ _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun σ _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun α _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun β _ =>
        tendsto_b1 hn M (hG1 μ ν ρ σ α β)
    have s2 := tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun μ _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun ν _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun ρ _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun σ _ =>
        tendsto_b2 T hδ ((M : ℝ) * CA A₀ ρ σ) (hU μ ν ρ σ μ ν)
    have s3 := tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun μ _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun ν _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun ρ _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun σ _ =>
        tendsto_b2 T hδ ((M : ℝ) * CA A₀ μ ν) (hU μ ν ρ σ ρ σ)
    simp only [Finset.sum_const_zero] at s1 s2 s3
    have h := ((s1.add s2).add s3).const_mul (1 / 4 : ℝ)
    rw [add_zero, add_zero, mul_zero] at h
    exact h
  · filter_upwards [hev] with k hk
    intro kt a hkt ha
    have hgl : ∀ x, e k x ∈ GLc := fun x => hKGL (heK k x)
    have hV : ∀ ρ σ, _ := fun ρ σ => vh_bound T hA₀ a ha
      (fun x => FextV (n k) (A k) (sampleTest (n k) a) x ρ σ) ρ σ (hk.2 a ha ρ σ)
    rw [firstVarYM_eq T (e k) kt (A k) (sampleTest (n k) a) hgl hk.1,
      firstVarCont_eq T e₀ A₀ F kt a
        (fun μ ν ρ σ α β => integrable_kt_mul kt hkt (hgi μ ν ρ σ α β) α β)
        (fun μ ν ρ σ => integrable_inner_of_memLp (hU μ ν ρ σ μ ν).memLp_lim (hV ρ σ).2.1)
        (fun μ ν ρ σ => integrable_inner_of_memLp (hU μ ν ρ σ ρ σ).memLp_lim (hV μ ν).2.1)]
    refine abs_combo_le ?_ ?_ ?_
    · refine abs_sum6_sub_le _ _ _ fun μ ν ρ σ α β => ?_
      exact term1_le kt hkt (fun x => dCoef (e k x) (Eab α β) μ ν ρ σ *
        ⟪T (Fext (n k) (A k) x μ ν), T (Fext (n k) (A k) x ρ σ)⟫) (hgi μ ν ρ σ α β) α β
    · refine abs_sum4_sub_le _ _ _ fun μ ν ρ σ => ?_
      exact term2_le ((hU μ ν ρ σ μ ν).memLp k) (hU μ ν ρ σ μ ν).memLp_lim (hV ρ σ).1
        (hV ρ σ).2.1 (hV ρ σ).2.2.1 (hV ρ σ).2.2.2
    · refine abs_sum4_sub_le _ _ _ fun μ ν ρ σ => ?_
      exact term2_le ((hU μ ν ρ σ ρ σ).memLp k) (hU μ ν ρ σ ρ σ).memLp_lim (hV μ ν).1
        (hV μ ν).2.1 (hV μ ν).2.2.1 (hV μ ν).2.2.2

end MetricTheorem5

section MetricNonVacuity

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The identity coframe. -/
def idCof : Cof := fun a b => if a = b then 1 else 0

theorem idCof_mem_GLc : idCof ∈ GLc := by
  have h : Matrix.of idCof = 1 := by
    ext a b
    simp [idCof, Matrix.one_apply]
  simp [GLc, h]

/-- Non-vacuity of `native_YM_metric_variation`: the hypotheses are met by the trivial connection
on the flat identity coframe (`𝔸 = E = ℂ`), so the uniform first-variation limit applies. -/
example (M : NNReal) : ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧ ∀ᶠ k in atTop,
    ∀ (kt : C(UnitAddTorus (Fin 4), Cof)) (a : C1Test ℂ), MetricBound M kt → GaugeBound M a →
      |firstVarYM (ContinuousLinearMap.id ℝ ℂ) (k + 1) (fun _ => idCof)
          (fun x => liftK idCof (kt (TorusCellEmbedding.samplePt x)))
          (fun _ _ => (0 : ℂ)) (sampleTest (k + 1) a) -
        firstVarCont (ContinuousLinearMap.id ℝ ℂ) (fun _ => idCof) (fun _ _ => (0 : ℂ))
          (fun _ _ _ => (0 : ℂ)) kt a| ≤ β k := by
  have hA : ∀ μ : Fin 4, LpTendsto volume 4 (fun k => pc (fun x : LatticeTorusPlancherel.Grid 4
      (k + 1) => (fun (_ : LatticeTorusPlancherel.Grid 4 (k + 1)) (_ : Fin 4) => (0 : ℂ)) x μ))
      (fun _ => (0 : ℂ)) := fun μ => by
    have e : (fun k => pc (fun x : LatticeTorusPlancherel.Grid 4 (k + 1) =>
        (fun (_ : LatticeTorusPlancherel.Grid 4 (k + 1)) (_ : Fin 4) => (0 : ℂ)) x μ)) =
        fun _ => (0 : UnitAddTorus (Fin 4) → ℂ) := by
      funext k y
      rfl
    rw [e]
    exact LpTendsto.const MemLp.zero
  have hF : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      curvLog (k + 1) (fun _ _ => (0 : ℂ)) x μ ν)) (fun _ => (0 : ℂ)) := by
    intro μ ν
    have e : (fun k => pc (fun x => curvLog (k + 1) (fun _ _ => (0 : ℂ)) x μ ν)) =
        fun _ => (0 : UnitAddTorus (Fin 4) → ℂ) := by
      funext k y
      exact curvLog_zero' (𝔸 := ℂ) (N := k + 1) _ μ ν
    rw [e]
    exact LpTendsto.const MemLp.zero
  have he : LpTendsto volume 2 (fun k => pc (fun _ : LatticeTorusPlancherel.Grid 4 (k + 1) =>
      idCof)) (fun _ => idCof) := LpTendsto.const (memLp_const idCof)
  exact native_YM_metric_variation (𝔸 := ℂ) (E := ℂ) (n := fun k => k + 1)
    (ContinuousLinearMap.id ℝ ℂ) (tendsto_add_atTop_nat 1) hA hF (isCompact_singleton (x := idCof))
    (by simpa using idCof_mem_GLc) he (fun _ _ => rfl) (Eventually.of_forall fun _ => rfl) M

end MetricNonVacuity

end

end RenewalGeometry.NativeYMMetric
