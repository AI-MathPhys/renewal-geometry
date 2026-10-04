/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMCompactnessCertificates
import RenewalGeometry.Analysis.SobolevChainRule
import RenewalGeometry.Analysis.LpProductContinuity

/-!
# Chart compositions and the Levi-Civita spin connection on a compact coframe chart
  (`lem:products`, clauses `eq:bounded-chart-composition` and `eq:spin-connection-convergence`,
  Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMCompactnessCertificates.lean` (compact chart = coordinate box `Q`,
coframes `e : ℝ⁴ → ℝ^{4×4}`, `H¹(Q) = W^{1,2}(Q)` with the weak gradient as data).

## Algebraic form of the spin connection

The library's Levi-Civita spin connection (`spinConn`, used by `firstVariation`) is
`ω_μ^a_b = e^a_ν(∂_μE^ν_b + Γ^ν_{μλ}E^λ_b)` with `E = e⁻¹` and the Christoffel symbols of
`g = eᵀηe`.  For a coframe differentiable at `x` with `det e(x) ≠ 0`,

* `pd_frameAt`: `∂_μE = -E (∂_μe) E`;
* `pd_metricAt`: `∂_i g_{μν} = η_{ab}(∂_ie^a_μ e^b_ν + e^a_μ ∂_ie^b_ν)` (`dMetricAlg`);
* `spinConn_eq_spinConnL`: **`ω(e)(x) = P(e(x)) ∂e(x)`**, where `spinConnL e` is the continuous
  linear map `∂e ↦ ω` (`spinConnAlg`), smooth in `e` on the nondegenerate chart
  `GL = {det e ≠ 0}` (`contDiffOn_spinConnL`).

## The metric variation of the spin connection

With the symmetric coframe lift `ė(k) = -½ e g k` (`metricLiftL e k`, `eq:metric-lift`) and its
first jet `∂_μė = D_e ė[∂_μe](k) + ė(∂_μk)`, the variation of `P(e)∂e` is
`ω̇(e, ∂e)[k, ∂k] = (D P(e)[ė(k)]) ∂e + P(e) ∂ė` (`spinConnVar`), the paper's
`P₁(e) k ∂e + P₂(e) ∂k`.  `hasDerivAt_spinConn_metricLift` proves that this is the derivative of
`ε ↦ ω(e + ε ė(k))(x)` for smooth `e, k`.

## Convergence on a compact chart

* `chart_composition`: **`eq:bounded-chart-composition`** — `e_h → e` strongly in `H¹(Q)` with
  values a.e. in a compact subset `K_e` of an open set `U` on which `Φ` is `C¹` (e.g. a smooth
  algebraic coefficient `F(e, e⁻¹)` on a compact subset of the nondegenerate chart): `Φ(e_h)`,
  `Φ(e)` lie in `H¹(Q)` with weak gradients `DΦ(e)·∂e` (weak chain rule), are uniformly
  bounded, and `Φ(e_h) → Φ(e)` strongly in `H¹(Q)` and in every finite `L^p(Q)`;
* `spinConn_L2_tendsto`, `spinConnVar_L2_tendsto`: **`eq:spin-connection-convergence`** —
  `P(e_h)∂e_h → P(e)∂e` in `L²(Q)` and the variation operators
  `(k, ∂k) ↦ ω̇(e_h, ∂e_h)[k, ∂k]` converge in `L²(Q)` in operator norm, hence uniformly for
  `(k, ∂k)` in bounded (in particular bounded `C¹`) test sets (`spinConnVar_uniform`).
  No `L^∞` convergence of `e_h` is used.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Fibres and the nondegenerate chart -/

/-- First-jet fibre of a coframe: `∂e = (∂_i e^a_μ)_i`. -/
abbrev CoframeJet := Fin 4 → CoframeFibre

/-- Spin-connection fibre `ω_μ^a_b` (index order `μ, a, b`). -/
abbrev SpinConnFibre := Fin 4 → Fin 4 → Fin 4 → ℝ

/-- The nondegenerate coframe chart `GL = {det e ≠ 0}` (open). -/
def coframeGL : Set CoframeFibre := {e | (Matrix.of e).det ≠ 0}

theorem contDiff_det_coframe {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun e : CoframeFibre => (Matrix.of e).det) := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  fun_prop

theorem isOpen_coframeGL : IsOpen coframeGL :=
  isOpen_ne_fun (contDiff_det_coframe (n := 0)).continuous continuous_const

theorem coframeChart_subset_GL : coframeChart ⊆ coframeGL := fun _ he => he.1.ne'

theorem contDiff_adjugate_coframe (i j : Fin 4) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun e : CoframeFibre => (Matrix.of e).adjugate i j) := by
  simp only [Matrix.adjugate_apply, Matrix.det_apply', Matrix.updateRow_apply, Matrix.of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun k _ => ?_)
  split_ifs <;> fun_prop

/-- The entries of the frame `E = e⁻¹` are smooth on the nondegenerate chart. -/
theorem contDiffAt_frameAt (μ a : Fin 4) {n : WithTop ℕ∞} {e : CoframeFibre}
    (he : e ∈ coframeGL) : ContDiffAt ℝ n (fun e : CoframeFibre => frameAt e μ a) e := by
  have : (fun e : CoframeFibre => frameAt e μ a) =
      fun e => ((Matrix.of e).det)⁻¹ * (Matrix.of e).adjugate μ a := by
    funext e
    rw [frameAt, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [this]
  exact ((contDiffAt_inv ℝ he).comp e contDiff_det_coframe.contDiffAt).mul
    (contDiff_adjugate_coframe μ a).contDiffAt

theorem contDiffOn_frameAt (μ a : Fin 4) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun e : CoframeFibre => frameAt e μ a) coframeGL := fun _ he =>
  (contDiffAt_frameAt μ a he).contDiffWithinAt

theorem metricAt_apply (e : CoframeFibre) (μ ν : Fin 4) :
    metricAt e μ ν = ∑ a, ∑ b, minkowskiEta a b * (e a μ * e b ν) := by
  simp only [metricAt, coframeMetric, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem contDiff_metricAt (μ ν : Fin 4) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun e : CoframeFibre => metricAt e μ ν) := by
  simp only [metricAt_apply]
  fun_prop

theorem det_metricAt (e : CoframeFibre) : (metricAt e).det = -((Matrix.of e).det) ^ 2 := by
  simp [metricAt, coframeMetric, Matrix.det_mul, Matrix.det_transpose, minkowskiEta,
    Matrix.det_diagonal, Fin.prod_univ_four]
  ring

theorem contDiffAt_metricInv (μ ν : Fin 4) {n : WithTop ℕ∞} {e : CoframeFibre}
    (he : e ∈ coframeGL) : ContDiffAt ℝ n (fun e : CoframeFibre => metricInv e μ ν) e := by
  have hdet : ContDiff ℝ n (fun e : CoframeFibre => (metricAt e).det) := by
    simp only [det_metricAt]; exact (contDiff_det_coframe.pow 2).neg
  have hadj : ContDiff ℝ n (fun e : CoframeFibre => (metricAt e).adjugate μ ν) := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply', Matrix.updateRow_apply]
    refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun k _ => ?_)
    split_ifs
    · exact contDiff_const
    · exact contDiff_metricAt _ _
  have hne : (metricAt e).det ≠ 0 := by
    rw [det_metricAt]; exact neg_ne_zero.mpr (pow_ne_zero 2 he)
  have : (fun e : CoframeFibre => metricInv e μ ν) =
      fun e => ((metricAt e).det)⁻¹ * (metricAt e).adjugate μ ν := by
    funext e
    rw [metricInv, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [this]
  exact ((contDiffAt_inv ℝ hne).comp e hdet.contDiffAt).mul hadj.contDiffAt

/-! ### The algebraic spin connection `ω = P(e) ∂e` -/

/-- Metric jet `∂_i g_{μν} = η_{ab}(∂_ie^a_μ e^b_ν + e^a_μ ∂_ie^b_ν)` from a coframe jet. -/
def dMetricAlg (e : CoframeFibre) (de : CoframeJet) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun i μ ν => ∑ a, ∑ b, minkowskiEta a b * (de i a μ * e b ν + e a μ * de i b ν)

/-- **The algebraic Levi-Civita spin connection** `ω_μ^a_b = e^a_ν(-(E ∂_μe E)^ν_b +
Γ^ν_{μλ}E^λ_b)`, `Γ = Γ(g⁻¹, ∂g)`. -/
def spinConnAlg (e : CoframeFibre) (de : CoframeJet) : SpinConnFibre :=
  fun μ a b => ∑ ν, e a ν * (-(∑ c, ∑ ρ, frameAt e ν c * de μ c ρ * frameAt e ρ b) +
    ∑ l, christoffel (metricInv e) (dMetricAlg e de) ν μ l * frameAt e l b)

theorem dMetricAlg_add (e : CoframeFibre) (d d' : CoframeJet) :
    dMetricAlg e (d + d') = dMetricAlg e d + dMetricAlg e d' := by
  funext i μ ν
  simp only [dMetricAlg, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem dMetricAlg_smul (e : CoframeFibre) (r : ℝ) (d : CoframeJet) :
    dMetricAlg e (r • d) = r • dMetricAlg e d := by
  funext i μ ν
  simp only [dMetricAlg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem christoffel_add (gi : Matrix (Fin 4) (Fin 4) ℝ) (d d' : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (c i j : Fin 4) :
    christoffel gi (d + d') c i j = christoffel gi d c i j + christoffel gi d' c i j := by
  simp only [christoffel, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun e _ => by ring

theorem christoffel_smul (gi : Matrix (Fin 4) (Fin 4) ℝ) (r : ℝ) (d : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (c i j : Fin 4) :
    christoffel gi (r • d) c i j = r * christoffel gi d c i j := by
  simp only [christoffel, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => by ring

theorem spinConnAlg_add (e : CoframeFibre) (d d' : CoframeJet) :
    spinConnAlg e (d + d') = spinConnAlg e d + spinConnAlg e d' := by
  funext μ a b
  have hc : ∀ ν l, christoffel (metricInv e) (dMetricAlg e (d + d')) ν μ l =
      christoffel (metricInv e) (dMetricAlg e d) ν μ l +
        christoffel (metricInv e) (dMetricAlg e d') ν μ l := fun ν l => by
    rw [dMetricAlg_add, christoffel_add]
  simp only [spinConnAlg, Pi.add_apply, hc, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [Finset.sum_add_distrib, add_mul, mul_add, neg_add]
  ring

theorem spinConnAlg_smul (e : CoframeFibre) (r : ℝ) (d : CoframeJet) :
    spinConnAlg e (r • d) = r • spinConnAlg e d := by
  funext μ a b
  have hc : ∀ ν l, christoffel (metricInv e) (dMetricAlg e (r • d)) ν μ l =
      r * christoffel (metricInv e) (dMetricAlg e d) ν μ l := fun ν l => by
    rw [dMetricAlg_smul, christoffel_smul]
  simp only [spinConnAlg, Pi.smul_apply, smul_eq_mul, hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [Finset.mul_sum, mul_add, mul_neg]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun ρ _ => by ring
  · refine Finset.sum_congr rfl fun l _ => by ring

/-- `ω = P(e) ∂e` as a linear map of the coframe jet. -/
def spinConnLin (e : CoframeFibre) : CoframeJet →ₗ[ℝ] SpinConnFibre where
  toFun := spinConnAlg e
  map_add' := spinConnAlg_add e
  map_smul' := spinConnAlg_smul e

/-- `ω = P(e) ∂e` as a continuous linear map of the coframe jet. -/
def spinConnL (e : CoframeFibre) : CoframeJet →L[ℝ] SpinConnFibre :=
  LinearMap.toContinuousLinearMap (spinConnLin e)

theorem spinConnL_apply (e : CoframeFibre) (de : CoframeJet) :
    spinConnL e de = spinConnAlg e de := rfl

/-! ### Identification with the library spin connection -/

theorem pd_apply₂ {f : E4 → CoframeFibre} {x : E4} (hf : DifferentiableAt ℝ f x)
    (i a μ : Fin 4) : pd (fun y => f y a μ) i x = pd f i x a μ := by
  unfold pd
  have h1 : HasFDerivAt (fun y => f y a) ((ContinuousLinearMap.proj a).comp (fderiv ℝ f x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → ℝ) a).hasFDerivAt.comp x
      hf.hasFDerivAt
  have h2 : HasFDerivAt (fun y => f y a μ) ((ContinuousLinearMap.proj μ).comp
      ((ContinuousLinearMap.proj a).comp (fderiv ℝ f x))) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) μ).hasFDerivAt.comp x h1
  rw [h2.fderiv]
  rfl

theorem differentiableAt_apply₂ {f : E4 → CoframeFibre} {x : E4} (hf : DifferentiableAt ℝ f x)
    (a μ : Fin 4) : DifferentiableAt ℝ (fun y => f y a μ) x :=
  differentiableAt_pi.mp (differentiableAt_pi.mp hf a) μ

theorem pd_mul' {f g : E4 → ℝ} {x : E4} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd (fun y => f y * g y) i x = pd f i x * g x + f x * pd g i x := by
  unfold pd
  rw [show (fun y => f y * g y) = f * g from rfl, (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem pd_sum {ι₀ : Type*} (s : Finset ι₀) {f : ι₀ → E4 → ℝ} {x : E4}
    (hf : ∀ j ∈ s, DifferentiableAt ℝ (f j) x) (i : Fin 4) :
    pd (fun y => ∑ j ∈ s, f j y) i x = ∑ j ∈ s, pd (f j) i x := by
  unfold pd
  rw [fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]

theorem pd_const_mul {f : E4 → ℝ} {x : E4} (c : ℝ) (hf : DifferentiableAt ℝ f x) (i : Fin 4) :
    pd (fun y => c * f y) i x = c * pd f i x := by
  unfold pd
  rw [fderiv_const_mul hf, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- `∂_i g_{μν} = dMetricAlg` for a differentiable coframe. -/
theorem pd_metricAt {e : E4 → CoframeFibre} {x : E4} (he : DifferentiableAt ℝ e x)
    (i μ ν : Fin 4) :
    pd (fun y => metricAt (e y) μ ν) i x = dMetricAlg (e x) (fun j => pd e j x) i μ ν := by
  simp only [metricAt_apply]
  have hd := fun a μ => differentiableAt_apply₂ he a μ
  rw [pd_sum (f := fun a y => ∑ b, minkowskiEta a b * (e y a μ * e y b ν)) _
    (fun a _ => DifferentiableAt.fun_sum fun b _ => ((hd a μ).mul (hd b ν)).const_mul _) i]
  unfold dMetricAlg
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pd_sum (f := fun b y => minkowskiEta a b * (e y a μ * e y b ν)) _
    (fun b _ => ((hd a μ).mul (hd b ν)).const_mul _) i]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pd_const_mul (f := fun y => e y a μ * e y b ν) _ ((hd a μ).mul (hd b ν)),
    pd_mul' (hd a μ) (hd b ν), pd_apply₂ he, pd_apply₂ he]

theorem frameAt_mul_self {e : CoframeFibre} (he : e ∈ coframeGL) (ν ρ : Fin 4) :
    ∑ c, frameAt e ν c * e c ρ = if ν = ρ then 1 else 0 := by
  have h := Matrix.nonsing_inv_mul (Matrix.of e) (Ne.isUnit he)
  have := congrFun (congrFun h ν) ρ
  simpa [Matrix.mul_apply, Matrix.one_apply, frameAt] using this

theorem self_mul_frameAt {e : CoframeFibre} (he : e ∈ coframeGL) (c b : Fin 4) :
    ∑ ρ, e c ρ * frameAt e ρ b = if c = b then 1 else 0 := by
  have h := Matrix.mul_nonsing_inv (Matrix.of e) (Ne.isUnit he)
  have := congrFun (congrFun h c) b
  simpa [Matrix.mul_apply, Matrix.one_apply, frameAt] using this

/-- **Derivative of the frame**: `∂_μE = -E (∂_μe) E` at a nondegenerate differentiable point. -/
theorem pd_frameAt {e : E4 → CoframeFibre} {x : E4} (he : DifferentiableAt ℝ e x)
    (hx : e x ∈ coframeGL) (μ ν b : Fin 4) :
    pd (fun y => frameAt (e y) ν b) μ x =
      -(∑ c, ∑ ρ, frameAt (e x) ν c * pd e μ x c ρ * frameAt (e x) ρ b) := by
  have hF : ∀ ν c, DifferentiableAt ℝ (fun y => frameAt (e y) ν c) x := fun ν c =>
    ((contDiffAt_frameAt ν c hx (n := 1)).differentiableAt one_ne_zero).comp x he
  have hd := fun a μ => differentiableAt_apply₂ he a μ
  -- `E e = 1` near `x`
  have hev : ∀ᶠ y in 𝓝 x, e y ∈ coframeGL :=
    he.continuousAt.preimage_mem_nhds (isOpen_coframeGL.mem_nhds hx)
  set D : Fin 4 → Fin 4 → ℝ := fun ν c => pd (fun y => frameAt (e y) ν c) μ x
  have key : ∀ ν ρ, ∑ c, D ν c * e x c ρ = -∑ c, frameAt (e x) ν c * pd e μ x c ρ := by
    intro ν ρ
    have hconst : (fun y => ∑ c, frameAt (e y) ν c * e y c ρ) =ᶠ[𝓝 x]
        fun _ => (if ν = ρ then 1 else 0 : ℝ) := by
      filter_upwards [hev] with y hy using frameAt_mul_self hy ν ρ
    have h0 : pd (fun y => ∑ c, frameAt (e y) ν c * e y c ρ) μ x = 0 := by
      unfold pd; rw [hconst.fderiv_eq]; simp
    rw [pd_sum (f := fun c y => frameAt (e y) ν c * e y c ρ) _
      (fun c _ => (hF ν c).mul (hd c ρ)) μ] at h0
    simp only [pd_mul' (hF _ _) (hd _ _), pd_apply₂ he, Finset.sum_add_distrib] at h0
    linarith
  calc pd (fun y => frameAt (e y) ν b) μ x = ∑ c, D ν c * (if c = b then 1 else 0) := by
        simp [D]
    _ = ∑ c, D ν c * ∑ ρ, e x c ρ * frameAt (e x) ρ b := by
        simp only [self_mul_frameAt hx]
    _ = ∑ ρ, (∑ c, D ν c * e x c ρ) * frameAt (e x) ρ b := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun c _ => by ring
    _ = -(∑ c, ∑ ρ, frameAt (e x) ν c * pd e μ x c ρ * frameAt (e x) ρ b) := by
        simp only [key, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
        rw [Finset.sum_comm]

/-- **`ω(e) = P(e) ∂e`**: at a point where the coframe is differentiable and nondegenerate, the
library spin connection is the algebraic one evaluated on the coframe and its first jet. -/
theorem spinConn_eq_spinConnL {e : E4 → CoframeFibre} {x : E4} (he : DifferentiableAt ℝ e x)
    (hx : e x ∈ coframeGL) : spinConn e x = spinConnL (e x) (fun i => pd e i x) := by
  funext μ a b
  have hdM : dMetric e x = dMetricAlg (e x) (fun j => pd e j x) := by
    funext i μ ν; exact pd_metricAt he i μ ν
  simp only [spinConnL_apply, spinConnAlg, spinConn, christoffelF, hdM, pd_frameAt he hx]

/-! ### Smoothness of `P(e)` on the nondegenerate chart -/

attribute [fun_prop] contDiffAt_frameAt contDiffAt_metricInv

theorem contDiffOn_spinConnAlg_apply (de : CoframeJet) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun e => spinConnAlg e de) coframeGL := by
  intro e₀ he₀
  refine ContDiffAt.contDiffWithinAt ?_
  refine contDiffAt_pi.mpr fun μ => contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
  simp only [spinConnAlg, christoffel, dMetricAlg]
  fun_prop (disch := assumption)

/-- `e ↦ P(e)` is smooth on the nondegenerate chart (as a map into continuous linear maps). -/
theorem contDiffOn_spinConnL {n : WithTop ℕ∞} : ContDiffOn ℝ n spinConnL coframeGL :=
  contDiffOn_clm_apply.mpr fun de => contDiffOn_spinConnAlg_apply de

/-! ### The symmetric coframe lift as a linear map -/

/-- The symmetric coframe lift `k ↦ ė(k) = -½ e g k` (`eq:metric-lift`) at a coframe value. -/
def metricLiftLin (e : CoframeFibre) : CoframeFibre →ₗ[ℝ] CoframeFibre where
  toFun k := fun a μ => -(1 / 2) * ∑ α, ∑ β, e a α * metricAt e μ β * k α β
  map_add' k k' := by
    funext a μ
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r k := by
    funext a μ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring

/-- The symmetric coframe lift as a continuous linear map. -/
def metricLiftL (e : CoframeFibre) : CoframeFibre →L[ℝ] CoframeFibre :=
  LinearMap.toContinuousLinearMap (metricLiftLin e)

theorem metricLift_eq (e k : E4 → CoframeFibre) (x : E4) :
    metricLift e k x = metricLiftL (e x) (k x) := rfl

theorem contDiff_metricLiftL {n : WithTop ℕ∞} : ContDiff ℝ n metricLiftL := by
  refine contDiff_clm_apply_iff.mpr fun k => ?_
  refine contDiff_pi.mpr fun a => contDiff_pi.mpr fun μ => ?_
  show ContDiff ℝ n (fun e : CoframeFibre => -(1 / 2) * ∑ α, ∑ β, e a α * metricAt e μ β * k α β)
  simp only [metricAt_apply]
  fun_prop

/-! ### The metric variation of the spin connection -/

/-- **The metric variation of the spin connection**
`ω̇(e, ∂e)[k, ∂k] = (DP(e)[ė(k)]) ∂e + P(e) ∂ė`, `∂_μė = Dė(e)[∂_μe](k) + ė(∂_μk)`. -/
def spinConnVar (e : CoframeFibre) (de : CoframeJet) (k : CoframeFibre) (dk : CoframeJet) :
    SpinConnFibre :=
  fderiv ℝ spinConnL e (metricLiftL e k) de +
    spinConnL e (fun μ => fderiv ℝ metricLiftL e (de μ) k + metricLiftL e (dk μ))

theorem differentiableAt_metricLift {e k : E4 → CoframeFibre} {x : E4}
    (he : DifferentiableAt ℝ e x) (hk : DifferentiableAt ℝ k x) :
    DifferentiableAt ℝ (metricLift e k) x := by
  have h1 : DifferentiableAt ℝ (fun y => metricLiftL (e y)) x :=
    ((contDiff_metricLiftL (n := 1)).differentiable one_ne_zero _).comp x he
  exact h1.clm_apply hk

theorem pd_metricLift {e k : E4 → CoframeFibre} {x : E4} (he : DifferentiableAt ℝ e x)
    (hk : DifferentiableAt ℝ k x) (i : Fin 4) :
    pd (metricLift e k) i x =
      fderiv ℝ metricLiftL (e x) (pd e i x) (k x) + metricLiftL (e x) (pd k i x) := by
  have h1 : HasFDerivAt (fun y => metricLiftL (e y))
      ((fderiv ℝ metricLiftL (e x)).comp (fderiv ℝ e x)) x :=
    (((contDiff_metricLiftL (n := 1)).differentiable one_ne_zero _).hasFDerivAt).comp x
      he.hasFDerivAt
  have h2 := h1.clm_apply hk.hasFDerivAt
  unfold pd
  rw [show metricLift e k = fun y => metricLiftL (e y) (k y) from rfl, h2.fderiv]
  simp [add_comm]

theorem pd_add_smul {f g : E4 → CoframeFibre} {x : E4} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (ε : ℝ) (i : Fin 4) :
    pd (f + ε • g) i x = pd f i x + ε • pd g i x := by
  unfold pd
  rw [fderiv_add hf (hg.const_smul ε), fderiv_const_smul hg]
  rfl

/-- **The metric variation of the spin connection is `P₁(e)k∂e + P₂(e)∂k`.**  For coframes and
metric tests differentiable at `x` with `det e(x) ≠ 0`,
`d/dε|₀ ω(e + ε ė(k))(x) = ω̇(e(x), ∂e(x))[k(x), ∂k(x)]`. -/
theorem hasDerivAt_spinConn_metricLift {e k : E4 → CoframeFibre} {x : E4}
    (he : DifferentiableAt ℝ e x) (hk : DifferentiableAt ℝ k x) (hx : e x ∈ coframeGL) :
    HasDerivAt (fun ε : ℝ => spinConn (e + ε • metricLift e k) x)
      (spinConnVar (e x) (fun i => pd e i x) (k x) (fun i => pd k i x)) 0 := by
  set ė := metricLift e k with hėdef
  have hė : DifferentiableAt ℝ ė x := differentiableAt_metricLift he hk
  set de : CoframeJet := fun i => pd e i x
  set dė : CoframeJet := fun i => pd ė i x
  -- eventually the perturbed coframe stays nondegenerate
  have hcurve : Continuous fun ε : ℝ => e x + ε • ė x := by fun_prop
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), e x + ε • ė x ∈ coframeGL := by
    refine hcurve.continuousAt.preimage_mem_nhds ?_
    simpa using isOpen_coframeGL.mem_nhds hx
  have heq : (fun ε : ℝ => spinConn (e + ε • ė) x) =ᶠ[𝓝 0]
      fun ε => spinConnL (e x + ε • ė x) (de + ε • dė) := by
    filter_upwards [hev] with ε hε
    have hd : DifferentiableAt ℝ (e + ε • ė) x := he.add (hė.const_smul ε)
    rw [spinConn_eq_spinConnL hd (by simpa using hε)]
    congr 1
    funext i
    exact pd_add_smul he hė ε i
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have hc : HasDerivAt (fun ε : ℝ => spinConnL (e x + ε • ė x))
      (fderiv ℝ spinConnL (e x) (ė x)) 0 := by
    have hS : HasFDerivAt spinConnL (fderiv ℝ spinConnL (e x)) (e x + (0 : ℝ) • ė x) := by
      rw [zero_smul, add_zero]
      exact ((contDiffOn_spinConnL (n := 1)).differentiableOn one_ne_zero _ hx
        |>.differentiableAt (isOpen_coframeGL.mem_nhds hx)).hasFDerivAt
    have hline : HasDerivAt (fun ε : ℝ => e x + ε • ė x) (ė x) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (ė x)).const_add (e x)
    exact hS.comp_hasDerivAt (0 : ℝ) hline
  have hu : HasDerivAt (fun ε : ℝ => de + ε • dė) dė 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const dė).const_add de
  have h := hc.clm_apply hu
  convert h using 1
  simp only [zero_smul, add_zero, spinConnVar]
  congr 1
  congr 1
  funext μ
  exact (pd_metricLift he hk μ).symm

/-! ### Measurability of compositions with chart coefficients -/

/-- A function continuous on an open set `s`, composed with an a.e.-strongly measurable map with
values a.e. in `s`, is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_comp_of_continuousOn {X Z W : Type*} [MeasurableSpace X]
    {μ : Measure X} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [NormedAddCommGroup W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    {s : Set Z} (hs : IsOpen s) {Φ : Z → W} (hΦ : ContinuousOn Φ s) {f : X → Z}
    (hf : AEMeasurable f μ) (hin : ∀ᵐ x ∂μ, f x ∈ s) :
    AEStronglyMeasurable (fun x => Φ (f x)) μ := by
  classical
  have hm : Measurable (s.piecewise Φ fun _ => 0) :=
    ContinuousOn.measurable_piecewise hΦ continuousOn_const hs.measurableSet
  refine (hm.comp_aemeasurable hf).aestronglyMeasurable.congr ?_
  filter_upwards [hin] with x hx
  simp [Function.comp, Set.piecewise, hx]

/-! ### Convergence of the spin connection and of its metric variation -/

/-- **`ω(e_h) → ω(e)` in `L²`** (`eq:spin-connection-convergence`, first part).  On a finite
measure space, if `e_h, e` take values a.e. in a compact `K_e ⊂ GL`, `e_h → e` in measure (e.g.
strongly in `L²` or `H¹`) and `∂e_h → ∂e` in `L²`, then `P(e_h)∂e_h → P(e)∂e` in `L²`. -/
theorem spinConn_L2_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKGL : Ke ⊆ coframeGL)
    {e : ℕ → X → CoframeFibre} {e₀ : X → CoframeFibre} {de : ℕ → X → CoframeJet}
    {de₀ : X → CoframeJet} (hem : ∀ n, AEMeasurable (e n) μ)
    (hin : ∀ n, ∀ᵐ x ∂μ, e n x ∈ Ke) (hin₀ : ∀ᵐ x ∂μ, e₀ x ∈ Ke)
    (he : TendstoInMeasure μ e atTop e₀) (hde : RenewalGeometry.LpTendsto μ 2 de de₀) :
    RenewalGeometry.LpTendsto μ 2 (fun n x => spinConnL (e n x) (de n x))
      (fun x => spinConnL (e₀ x) (de₀ x)) :=
  LpProductContinuity.LpTendsto.chainRule_term hKe
    ((contDiffOn_spinConnL (n := 0)).continuousOn.mono hKGL) hin hin₀ he
    (fun n => aestronglyMeasurable_comp_of_continuousOn isOpen_coframeGL
      (contDiffOn_spinConnL (n := 0)).continuousOn (hem n)
      (by filter_upwards [hin n] with x hx using hKGL hx)) hde

/-- The metric-test fibre `(k, ∂k)`. -/
abbrev MetricTestJet := CoframeFibre × CoframeJet

/-- The part of the variation operator that is linear in `∂e`:
`∂e ↦ ((k, ∂k) ↦ (DP(e)[ė(k)]) ∂e + P(e)(μ ↦ Dė(e)[∂_μe](k)))`. -/
def spinVarLinPart (e : CoframeFibre) : CoframeJet →L[ℝ] (MetricTestJet →L[ℝ] SpinConnFibre) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun de => LinearMap.toContinuousLinearMap
        { toFun := fun t => fderiv ℝ spinConnL e (metricLiftL e t.1) de +
            spinConnL e (fun μ => fderiv ℝ metricLiftL e (de μ) t.1)
          map_add' := fun t t' => by
            simp only [Prod.fst_add, map_add, ContinuousLinearMap.add_apply]
            rw [show (fun μ => fderiv ℝ metricLiftL e (de μ) t.1 +
                fderiv ℝ metricLiftL e (de μ) t'.1) =
                (fun μ => fderiv ℝ metricLiftL e (de μ) t.1) +
                  (fun μ => fderiv ℝ metricLiftL e (de μ) t'.1) from rfl, map_add]
            abel
          map_smul' := fun r t => by
            simp only [Prod.smul_fst, map_smul, ContinuousLinearMap.smul_apply, RingHom.id_apply,
              smul_add]
            rw [show (fun μ => r • fderiv ℝ metricLiftL e (de μ) t.1) =
                r • (fun μ => fderiv ℝ metricLiftL e (de μ) t.1) from rfl, map_smul] }
      map_add' := fun de de' => by
        refine ContinuousLinearMap.ext fun t => ?_
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          ContinuousLinearMap.add_apply, map_add, Pi.add_apply, ContinuousLinearMap.add_apply]
        rw [show (fun μ => fderiv ℝ metricLiftL e (de μ) t.1 +
            fderiv ℝ metricLiftL e (de' μ) t.1) =
            (fun μ => fderiv ℝ metricLiftL e (de μ) t.1) +
              (fun μ => fderiv ℝ metricLiftL e (de' μ) t.1) from rfl, map_add]
        abel
      map_smul' := fun r de => by
        refine ContinuousLinearMap.ext fun t => ?_
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          ContinuousLinearMap.smul_apply, map_smul, Pi.smul_apply, RingHom.id_apply, smul_add]
        rw [show (fun μ => r • fderiv ℝ metricLiftL e (de μ) t.1) =
            r • (fun μ => fderiv ℝ metricLiftL e (de μ) t.1) from rfl, map_smul] }

/-- The part of the variation operator independent of `∂e`: `(k, ∂k) ↦ P(e)(μ ↦ ė(∂_μk))`. -/
def spinVarConstPart (e : CoframeFibre) : MetricTestJet →L[ℝ] SpinConnFibre :=
  (spinConnL e).comp ((ContinuousLinearMap.pi fun μ =>
    (metricLiftL e).comp (ContinuousLinearMap.proj μ)).comp
      (ContinuousLinearMap.snd ℝ CoframeFibre CoframeJet))

/-- **The variation operator** `(k, ∂k) ↦ ω̇(e, ∂e)[k, ∂k]`. -/
def spinVarOp (e : CoframeFibre) (de : CoframeJet) : MetricTestJet →L[ℝ] SpinConnFibre :=
  spinVarLinPart e de + spinVarConstPart e

theorem spinVarOp_apply (e : CoframeFibre) (de : CoframeJet) (t : MetricTestJet) :
    spinVarOp e de t = spinConnVar e de t.1 t.2 := by
  change (fderiv ℝ spinConnL e (metricLiftL e t.1) de +
      spinConnL e (fun μ => fderiv ℝ metricLiftL e (de μ) t.1)) +
      spinConnL e (fun μ => metricLiftL e (t.2 μ)) = _
  rw [add_assoc, ← map_add]
  rfl

theorem continuousOn_fderiv_spinConnL : ContinuousOn (fderiv ℝ spinConnL) coframeGL :=
  (contDiffOn_spinConnL (n := 1)).continuousOn_fderiv_of_isOpen isOpen_coframeGL le_rfl

theorem continuous_fderiv_metricLiftL : Continuous (fderiv ℝ metricLiftL) :=
  (contDiff_metricLiftL (n := 1)).continuous_fderiv one_ne_zero

theorem continuousOn_spinVarLinPart : ContinuousOn spinVarLinPart coframeGL := by
  refine continuousOn_clm_apply.mpr fun de => continuousOn_clm_apply.mpr fun t => ?_
  change ContinuousOn (fun e => fderiv ℝ spinConnL e (metricLiftL e t.1) de +
    spinConnL e (fun μ => fderiv ℝ metricLiftL e (de μ) t.1)) coframeGL
  refine ContinuousOn.add ?_ ?_
  · exact (continuousOn_fderiv_spinConnL.clm_apply
      ((contDiff_metricLiftL (n := 0)).continuous.clm_apply continuous_const).continuousOn)
      |>.clm_apply continuousOn_const
  · refine (contDiffOn_spinConnL (n := 0)).continuousOn.clm_apply ?_
    exact (continuous_pi fun μ => (continuous_fderiv_metricLiftL.clm_apply continuous_const)
      |>.clm_apply continuous_const).continuousOn

theorem continuousOn_spinVarConstPart : ContinuousOn spinVarConstPart coframeGL := by
  refine continuousOn_clm_apply.mpr fun t => ?_
  change ContinuousOn (fun e => spinConnL e (fun μ => metricLiftL e (t.2 μ))) coframeGL
  exact (contDiffOn_spinConnL (n := 0)).continuousOn.clm_apply
    (continuous_pi fun μ => (contDiff_metricLiftL (n := 0)).continuous.clm_apply
      continuous_const).continuousOn

/-- **The metric variation of the spin connection converges in `L²` in operator norm**
(`eq:spin-connection-convergence`, second part): under the hypotheses of `spinConn_L2_tendsto`,
`(k, ∂k) ↦ ω̇(e_h, ∂e_h)[k, ∂k]` converges in `L²` to `(k, ∂k) ↦ ω̇(e, ∂e)[k, ∂k]`. -/
theorem spinVarOp_L2_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKGL : Ke ⊆ coframeGL)
    {e : ℕ → X → CoframeFibre} {e₀ : X → CoframeFibre} {de : ℕ → X → CoframeJet}
    {de₀ : X → CoframeJet} (hem : ∀ n, AEMeasurable (e n) μ)
    (hin : ∀ n, ∀ᵐ x ∂μ, e n x ∈ Ke) (hin₀ : ∀ᵐ x ∂μ, e₀ x ∈ Ke)
    (he : TendstoInMeasure μ e atTop e₀) (hde : RenewalGeometry.LpTendsto μ 2 de de₀) :
    RenewalGeometry.LpTendsto μ 2 (fun n x => spinVarOp (e n x) (de n x))
      (fun x => spinVarOp (e₀ x) (de₀ x)) := by
  have hGL : ∀ n, ∀ᵐ x ∂μ, e n x ∈ coframeGL := fun n => by
    filter_upwards [hin n] with x hx using hKGL hx
  have h1 := LpProductContinuity.LpTendsto.chainRule_term hKe
    (continuousOn_spinVarLinPart.mono hKGL) hin hin₀ he
    (fun n => aestronglyMeasurable_comp_of_continuousOn isOpen_coframeGL
      continuousOn_spinVarLinPart (hem n) (hGL n)) hde
  have h2 := (LpProductContinuity.LpTendsto.comp_of_continuousOn (p := 2) (by norm_num) hKe
    (continuousOn_spinVarConstPart.mono hKGL) hin hin₀ he
    (fun n => aestronglyMeasurable_comp_of_continuousOn isOpen_coframeGL
      continuousOn_spinVarConstPart (hem n) (hGL n))).2
  exact h1.add h2

/-- **Uniformity over bounded test sets**: for every measurable test field `t(x) = (k, ∂k)(x)`
with `‖t(x)‖ ≤ 1`, the `L²` distance of the varied spin connections is bounded by the operator
`L²` distance, which tends to zero (`spinVarOp_L2_tendsto`). -/
theorem spinConnVar_uniform {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {A A' : X → MetricTestJet →L[ℝ] SpinConnFibre} (hA : AEStronglyMeasurable A μ)
    (hA' : AEStronglyMeasurable A' μ) {t : X → MetricTestJet} (ht : AEStronglyMeasurable t μ)
    (ht1 : ∀ᵐ x ∂μ, ‖t x‖ ≤ 1) :
    eLpNorm (fun x => A x (t x) - A' x (t x)) 2 μ ≤ eLpNorm (A - A') 2 μ := by
  refine eLpNorm_mono_ae ?_
  filter_upwards [ht1] with x hx
  rw [← ContinuousLinearMap.sub_apply]
  exact ((A x - A' x).le_opNorm _).trans (by
    simpa using mul_le_of_le_one_right (norm_nonneg _) hx)

/-! ### Chart compositions (`eq:bounded-chart-composition`) -/

/-- The flattened coframe value `(e^a_μ)_{(a, μ)}`. -/
def coframeVec (e : CoframeFibre) : Fin 4 × Fin 4 → ℝ := fun p => e p.1 p.2

theorem continuous_coframeVec : Continuous coframeVec :=
  continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)

theorem norm_ofReal_vec {κ : Type*} [Fintype κ] (v : κ → ℝ) :
    ‖(fun p => ((v p : ℝ) : ℂ))‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun p => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun p => ?_)
  · rw [Complex.norm_real]; exact norm_le_pi_norm v p
  · rw [← Complex.norm_real]; exact norm_le_pi_norm (fun p => ((v p : ℝ) : ℂ)) p

theorem norm_ofReal_vec_unit {κ : Type*} [Fintype κ] (v : κ → ℝ) :
    ‖(fun p (_ : Unit) => ((v p : ℝ) : ℂ))‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun p => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun p => ?_)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun _ => ?_
    rw [Complex.norm_real]; exact norm_le_pi_norm v p
  · have h1 := norm_le_pi_norm (fun p (_ : Unit) => ((v p : ℝ) : ℂ)) p
    have h2 := norm_le_pi_norm (fun (_ : Unit) => ((v p : ℝ) : ℂ)) ()
    rw [Complex.norm_real] at h2
    exact h2.trans h1

theorem norm_re_vec_sub_le {κ : Type*} [Fintype κ] (u w : Fin 4 → κ → ℂ) :
    ‖(fun i p => (u i p).re) - (fun i p => (w i p).re)‖ ≤ ‖u - w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun p => ?_
  have h1 := norm_le_pi_norm (u - w) i
  have h2 := norm_le_pi_norm ((u - w) i) p
  simp only [Pi.sub_apply, Real.norm_eq_abs, ← Complex.sub_re] at h1 h2 ⊢
  exact (Complex.abs_re_le_norm _).trans (h2.trans h1)

theorem coframeC_sub_apply (e e' : E4 → CoframeFibre) (x : E4) :
    (coframeC e - coframeC e') x =
      fun p => (((coframeVec (e x) - coframeVec (e' x)) p : ℝ) : ℂ) := by
  funext p; simp [coframeC, coframeVec]

theorem norm_coframeC_sub (e e' : E4 → CoframeFibre) (x : E4) :
    ‖(coframeC e - coframeC e') x‖ = ‖coframeVec (e x) - coframeVec (e' x)‖ := by
  rw [coframeC_sub_apply, norm_ofReal_vec]

/-- The composite `Φ(e)` as a one-component complex field. -/
def chartComp (Φ : (Fin 4 × Fin 4 → ℝ) → ℝ) (e : E4 → CoframeFibre) : E4 → Unit → ℂ :=
  fun x _ => ((Φ (coframeVec (e x)) : ℝ) : ℂ)

/-- The chain-rule gradient `∂_i Φ(e) = Σ_{(a,μ)} ∂_{aμ}Φ(e) Re ∂_i e^a_μ`. -/
def chartGrad (Φ : (Fin 4 × Fin 4 → ℝ) → ℝ) (e : E4 → CoframeFibre)
    (de : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ) : E4 → Fin 4 → Unit → ℂ :=
  fun x i _ => ((∑ p, fderiv ℝ Φ (coframeVec (e x)) (Pi.single p 1) * (de x i p).re : ℝ) : ℂ)

/-- The real part of a complex coframe-gradient datum. -/
def reJet (de : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ) : E4 → Fin 4 → Fin 4 × Fin 4 → ℝ :=
  fun x i p => (de x i p).re

/-- `DΦ` applied componentwise to the four directional jets. -/
def chartGradL (Φ : (Fin 4 × Fin 4 → ℝ) → ℝ) (y : Fin 4 × Fin 4 → ℝ) :
    (Fin 4 → Fin 4 × Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi fun i => (fderiv ℝ Φ y).comp (ContinuousLinearMap.proj i)

theorem chartGrad_eq (Φ : (Fin 4 × Fin 4 → ℝ) → ℝ) (e : E4 → CoframeFibre)
    (de : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ) (x : E4) :
    chartGrad Φ e de x = fun i _ => ((chartGradL Φ (coframeVec (e x)) (reJet de x) i : ℝ) : ℂ) := by
  funext i u
  simp only [chartGrad, chartGradL, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply]
  congr 1
  rw [SobolevOpen.clm_apply_eq_sum]
  exact Finset.sum_congr rfl fun p _ => by rw [mul_comm]; rfl

theorem continuousOn_chartGradL {Φ : (Fin 4 × Fin 4 → ℝ) → ℝ} {U : Set (Fin 4 × Fin 4 → ℝ)}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 1 Φ U) : ContinuousOn (chartGradL Φ) U := by
  have hD : ContinuousOn (fderiv ℝ Φ) U := hΦ.continuousOn_fderiv_of_isOpen hU le_rfl
  refine continuousOn_clm_apply.mpr fun w => ?_
  refine continuousOn_pi.mpr fun i => ?_
  exact hD.clm_apply continuousOn_const

theorem memH1_coframe_measurable {T : ℝ} {Q : ChartBox T} {e : E4 → CoframeFibre}
    {de : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} (h : MemH1 Q (coframeC e) de) :
    AEMeasurable (fun x => coframeVec (e x)) Q.μ := by
  refine aemeasurable_pi_lambda _ fun p => ?_
  have := (Complex.continuous_re.comp_aestronglyMeasurable (h p).memLp.1).aemeasurable
  simpa [coframeC, coframeVec] using this

theorem memH1_coframe_grad_memLp {T : ℝ} {Q : ChartBox T} {e : E4 → CoframeFibre}
    {de : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} (h : MemH1 Q (coframeC e) de) :
    MemLp (reJet de) 2 Q.μ :=
  memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun p => ((h p).memLp_grad i).re

/-- Strong `H¹(Q)` coframe convergence gives convergence in measure of the flattened values. -/
theorem tendstoInMeasure_of_h1Tendsto {T : ℝ} {Q : ChartBox T} {e : ℕ → E4 → CoframeFibre}
    {de : ℕ → E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} {e₀ : E4 → CoframeFibre}
    {de₀ : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ}
    (hmem : ∀ n, MemH1 Q (coframeC (e n)) (de n)) (hmem₀ : MemH1 Q (coframeC e₀) de₀)
    (hconv : H1Tendsto Q (fun n => coframeC (e n)) de (coframeC e₀) de₀) :
    TendstoInMeasure Q.μ (fun n x => coframeVec (e n x)) atTop (fun x => coframeVec (e₀ x)) := by
  refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    (fun n => (memH1_coframe_measurable (hmem n)).aestronglyMeasurable)
    (memH1_coframe_measurable hmem₀).aestronglyMeasurable ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    (fun n => zero_le) fun n => ?_
  refine le_trans (le_of_eq ?_) le_self_add
  refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
  rw [norm_coframeC_sub]; rfl

/-- Strong `H¹(Q)` coframe convergence gives `L²` convergence of the real first jets. -/
theorem reJet_L2_tendsto {T : ℝ} {Q : ChartBox T} {e : ℕ → E4 → CoframeFibre}
    {de : ℕ → E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} {e₀ : E4 → CoframeFibre}
    {de₀ : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ}
    (hmem : ∀ n, MemH1 Q (coframeC (e n)) (de n)) (hmem₀ : MemH1 Q (coframeC e₀) de₀)
    (hconv : H1Tendsto Q (fun n => coframeC (e n)) de (coframeC e₀) de₀) :
    RenewalGeometry.LpTendsto Q.μ 2 (fun n => reJet (de n)) (reJet de₀) := by
  refine ⟨fun n => memH1_coframe_grad_memLp (hmem n), memH1_coframe_grad_memLp hmem₀, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    (fun n => zero_le) fun n => ?_
  refine le_trans ?_ le_add_self
  exact eLpNorm_mono fun x => norm_re_vec_sub_le (de n x) (de₀ x)

/-- **`eq:bounded-chart-composition`.**  Let `Q` be a chart box, `K_e` a compact set of coframe
values and `Φ` a `C¹` function on an open `U ⊇ K_e` (e.g. a smooth algebraic coefficient
`F(e, e⁻¹)` on a compact subset of the nondegenerate chart).  If `e_h, e ∈ H¹(Q)` take values
a.e. in `K_e` and `e_h → e` strongly in `H¹(Q)`, then `Φ(e_h), Φ(e) ∈ H¹(Q)` with the chain-rule
gradients, `Φ(e_h) → Φ(e)` strongly in `H¹(Q)`, `sup_h ‖Φ(e_h)‖_∞ < ∞`, and `Φ(e_h) → Φ(e)` in
every finite `L^p(Q)`. -/
theorem chart_composition {T : ℝ} (Q : ChartBox T) {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    {U : Set (Fin 4 × Fin 4 → ℝ)} (hU : IsOpen U) (hKU : coframeVec '' Ke ⊆ U)
    {Φ : (Fin 4 × Fin 4 → ℝ) → ℝ} (hΦ : ContDiffOn ℝ 1 Φ U)
    {e : ℕ → E4 → CoframeFibre} {de : ℕ → E4 → Fin 4 → Fin 4 × Fin 4 → ℂ}
    {e₀ : E4 → CoframeFibre} {de₀ : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ}
    (hmem : ∀ n, MemH1 Q (coframeC (e n)) (de n)) (hmem₀ : MemH1 Q (coframeC e₀) de₀)
    (hin : ∀ n, ∀ᵐ x ∂Q.μ, e n x ∈ Ke) (hin₀ : ∀ᵐ x ∂Q.μ, e₀ x ∈ Ke)
    (hconv : H1Tendsto Q (fun n => coframeC (e n)) de (coframeC e₀) de₀) :
    (∀ n, MemH1 Q (chartComp Φ (e n)) (chartGrad Φ (e n) (de n))) ∧
      MemH1 Q (chartComp Φ e₀) (chartGrad Φ e₀ de₀) ∧
      H1Tendsto Q (fun n => chartComp Φ (e n)) (fun n => chartGrad Φ (e n) (de n))
        (chartComp Φ e₀) (chartGrad Φ e₀ de₀) ∧
      (∃ M, ∀ n, ∀ᵐ x ∂Q.μ, ‖Φ (coframeVec (e n x))‖ ≤ M) ∧
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → Tendsto (fun n => eLpNorm (fun x =>
        Φ (coframeVec (e n x)) - Φ (coframeVec (e₀ x))) p Q.μ) atTop (𝓝 0) := by
  have hQo : IsOpen Q.set := SobolevOpen.isOpen_box Q.a Q.b
  have hQf : volume Q.set ≠ ⊤ := SobolevOpen.volume_box_ne_top Q.a Q.b
  set Kc := coframeVec '' Ke
  have hKc : IsCompact Kc := hKe.image continuous_coframeVec
  have hinc : ∀ n, ∀ᵐ x ∂Q.μ, coframeVec (e n x) ∈ Kc := fun n => by
    filter_upwards [hin n] with x hx using ⟨_, hx, rfl⟩
  have hinc₀ : ∀ᵐ x ∂Q.μ, coframeVec (e₀ x) ∈ Kc := by
    filter_upwards [hin₀] with x hx using ⟨_, hx, rfl⟩
  have hinU : ∀ n, ∀ᵐ x ∂Q.μ, coframeVec (e n x) ∈ U := fun n => by
    filter_upwards [hinc n] with x hx using hKU hx
  -- the weak chain rule
  have hW : ∀ {f : E4 → CoframeFibre} {df : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ},
      MemH1 Q (coframeC f) df → (∀ᵐ x ∂Q.μ, coframeVec (f x) ∈ Kc) →
      MemH1 Q (chartComp Φ f) (chartGrad Φ f df) := by
    intro f df hf hfin _
    exact SobolevOpen.MemW12.comp_of_mem_compact (u := fun (p : Fin 4 × Fin 4) x => f x p.1 p.2)
      (g := fun p i x => df x i p) hQo hQf
      (fun (p : Fin 4 × Fin 4) => (hf p : MemW12 Q.set (fun x => ((f x p.1 p.2 : ℝ) : ℂ))
        (fun i x => df x i p)))
      hU hKc hKU hfin hΦ
  -- convergence in measure and the bounded-coefficient compositions
  have hmeas := tendstoInMeasure_of_h1Tendsto hmem hmem₀ hconv
  have hΦm : ∀ n, AEStronglyMeasurable (fun x => Φ (coframeVec (e n x))) Q.μ := fun n =>
    aestronglyMeasurable_comp_of_continuousOn hU hΦ.continuousOn
      (memH1_coframe_measurable (hmem n)) (hinU n)
  have hcomp : ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      (∃ M, ∀ n, ∀ᵐ x ∂Q.μ, ‖Φ (coframeVec (e n x))‖ ≤ M) ∧
      RenewalGeometry.LpTendsto Q.μ p (fun n x => Φ (coframeVec (e n x)))
        (fun x => Φ (coframeVec (e₀ x))) := fun p hp hpt => by
    have : Fact (1 ≤ p) := ⟨hp⟩
    exact LpProductContinuity.LpTendsto.comp_of_continuousOn hpt hKc (hΦ.continuousOn.mono hKU)
      hinc hinc₀ hmeas hΦm
  refine ⟨fun n => hW (hmem n) (hinc n), hW hmem₀ hinc₀, ?_,
    (hcomp 2 (by norm_num) (by norm_num)).1, fun p hp hpt => (hcomp p hp hpt).2.tendsto⟩
  -- strong `H¹` convergence
  have hval : Tendsto (fun n => eLpNorm (chartComp Φ (e n) - chartComp Φ e₀) 2 Q.μ) atTop
      (𝓝 0) := by
    refine (hcomp 2 (by norm_num) (by norm_num)).2.tendsto.congr fun n => ?_
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    have : (chartComp Φ (e n) - chartComp Φ e₀) x =
        fun _ => (((Φ (coframeVec (e n x)) - Φ (coframeVec (e₀ x))) : ℝ) : ℂ) := by
      funext u; simp [chartComp]
    rw [this, Pi.sub_apply]
    exact le_antisymm (le_of_eq (by
      rw [show ‖(fun _ : Unit => (((Φ (coframeVec (e n x)) - Φ (coframeVec (e₀ x))) : ℝ) : ℂ))‖
          = ‖(((Φ (coframeVec (e n x)) - Φ (coframeVec (e₀ x))) : ℝ) : ℂ)‖ from
          (pi_norm_const _), Complex.norm_real]))
      (le_of_eq (by
        rw [show ‖(fun _ : Unit => (((Φ (coframeVec (e n x)) - Φ (coframeVec (e₀ x))) : ℝ) : ℂ))‖
          = ‖(((Φ (coframeVec (e n x)) - Φ (coframeVec (e₀ x))) : ℝ) : ℂ)‖ from
          (pi_norm_const _), Complex.norm_real]))
  have hgrad : Tendsto (fun n => eLpNorm (chartGrad Φ (e n) (de n) - chartGrad Φ e₀ de₀) 2 Q.μ)
      atTop (𝓝 0) := by
    have hD := LpProductContinuity.LpTendsto.chainRule_term hKc
      ((continuousOn_chartGradL hU hΦ).mono hKU) hinc hinc₀ hmeas
      (fun n => aestronglyMeasurable_comp_of_continuousOn hU (continuousOn_chartGradL hU hΦ)
        (memH1_coframe_measurable (hmem n)) (hinU n))
      (reJet_L2_tendsto hmem hmem₀ hconv)
    refine hD.tendsto.congr fun n => ?_
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    rw [Pi.sub_apply, Pi.sub_apply, chartGrad_eq, chartGrad_eq]
    have : (fun i (_ : Unit) => ((chartGradL Φ (coframeVec (e n x)) (reJet (de n) x) i : ℝ) : ℂ)) -
        (fun i (_ : Unit) => ((chartGradL Φ (coframeVec (e₀ x)) (reJet de₀ x) i : ℝ) : ℂ)) =
        fun i (_ : Unit) => (((chartGradL Φ (coframeVec (e n x)) (reJet (de n) x) -
          chartGradL Φ (coframeVec (e₀ x)) (reJet de₀ x)) i : ℝ) : ℂ) := by
      funext i u; simp
    rw [this, norm_ofReal_vec_unit]
  have := hval.add hgrad
  rw [add_zero] at this
  exact this

/-! ### The chart statements in the form used by the reduced convergence -/

/-- The coframe jet `(∂_i e^a_μ)` from the flattened real gradient data. -/
def toJet (w : Fin 4 → Fin 4 × Fin 4 → ℝ) : CoframeJet := fun i a μ => w i (a, μ)

theorem norm_coframeVec (a : CoframeFibre) : ‖coframeVec a‖ = ‖a‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr fun p => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i =>
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_)
  · exact (norm_le_pi_norm (a p.1) p.2).trans (norm_le_pi_norm a p.1)
  · exact norm_le_pi_norm (coframeVec a) (i, j)

theorem norm_toJet_le (w : Fin 4 → Fin 4 × Fin 4 → ℝ) : ‖toJet w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun i =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun a =>
      (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun μ => ?_
  exact (norm_le_pi_norm (w i) (a, μ)).trans (norm_le_pi_norm w i)

theorem toJet_sub (w w' : Fin 4 → Fin 4 × Fin 4 → ℝ) : toJet w - toJet w' = toJet (w - w') := rfl

/-- Strong `H¹(Q)` coframe convergence gives convergence in measure of the coframes. -/
theorem coframe_tendstoInMeasure {T : ℝ} {Q : ChartBox T} {e : ℕ → E4 → CoframeFibre}
    {de : ℕ → E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} {e₀ : E4 → CoframeFibre}
    {de₀ : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ}
    (hmem : ∀ n, MemH1 Q (coframeC (e n)) (de n)) (hmem₀ : MemH1 Q (coframeC e₀) de₀)
    (hconv : H1Tendsto Q (fun n => coframeC (e n)) de (coframeC e₀) de₀) :
    TendstoInMeasure Q.μ e atTop e₀ := by
  have h := tendstoInMeasure_of_h1Tendsto hmem hmem₀ hconv
  intro ε hε
  refine (h ε hε).congr fun n => ?_
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, edist_dist, dist_eq_norm, ← Pi.sub_apply]
  rw [show coframeVec (e n x) - coframeVec (e₀ x) = coframeVec (e n x - e₀ x) from rfl,
    norm_coframeVec, Pi.sub_apply]

theorem coframe_aemeasurable {T : ℝ} {Q : ChartBox T} {e : E4 → CoframeFibre}
    {de : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} (h : MemH1 Q (coframeC e) de) :
    AEMeasurable e Q.μ := by
  refine aemeasurable_pi_lambda _ fun a => aemeasurable_pi_lambda _ fun μ => ?_
  have := (Complex.continuous_re.comp_aestronglyMeasurable (h (a, μ)).memLp.1).aemeasurable
  simpa [coframeC] using this

/-- Strong `H¹(Q)` coframe convergence gives `L²` convergence of the coframe jets. -/
theorem coframeJet_L2_tendsto {T : ℝ} {Q : ChartBox T} {e : ℕ → E4 → CoframeFibre}
    {de : ℕ → E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} {e₀ : E4 → CoframeFibre}
    {de₀ : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ}
    (hmem : ∀ n, MemH1 Q (coframeC (e n)) (de n)) (hmem₀ : MemH1 Q (coframeC e₀) de₀)
    (hconv : H1Tendsto Q (fun n => coframeC (e n)) de (coframeC e₀) de₀) :
    RenewalGeometry.LpTendsto Q.μ 2 (fun n x => toJet (reJet (de n) x))
      (fun x => toJet (reJet de₀ x)) := by
  have h := reJet_L2_tendsto hmem hmem₀ hconv
  have hm : ∀ {w : E4 → Fin 4 → Fin 4 × Fin 4 → ℝ}, MemLp w 2 Q.μ →
      MemLp (fun x => toJet (w x)) 2 Q.μ := fun {w} hw =>
    hw.of_le (memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun a => memLp_pi_iff.mpr fun μ =>
      (memLp_pi_iff.mp (memLp_pi_iff.mp hw i)) (a, μ)).1
      (Eventually.of_forall fun x => norm_toJet_le _)
  refine ⟨fun n => hm (h.memLp n), hm h.memLp_lim, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h.tendsto
    (fun n => zero_le) fun n => eLpNorm_mono fun x => ?_
  simp only [Pi.sub_apply, toJet_sub]
  exact norm_toJet_le _

/-- For a classically differentiable coframe, the jet built from its classical gradient packet is
its first jet. -/
theorem toJet_reJet_coframeGrad {e : E4 → CoframeFibre} (x : E4) :
    toJet (reJet (coframeGrad e) x) = fun i => pd e i x := by
  funext i a μ; simp [toJet, reJet, coframeGrad]

/-- **`eq:spin-connection-convergence`, first part, on a compact chart**: under strong `H¹(Q)`
coframe convergence with values a.e. in a compact subset `K_e` of the nondegenerate chart,
`ω(e_h) = P(e_h)∂e_h → P(e)∂e = ω(e)` in `L²(Q)`. -/
theorem spinConn_L2_tendsto_of_h1 {T : ℝ} {Q : ChartBox T} {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hKGL : Ke ⊆ coframeGL) {e : ℕ → E4 → CoframeFibre}
    {de : ℕ → E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} {e₀ : E4 → CoframeFibre}
    {de₀ : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ}
    (hmem : ∀ n, MemH1 Q (coframeC (e n)) (de n)) (hmem₀ : MemH1 Q (coframeC e₀) de₀)
    (hin : ∀ n, ∀ᵐ x ∂Q.μ, e n x ∈ Ke) (hin₀ : ∀ᵐ x ∂Q.μ, e₀ x ∈ Ke)
    (hconv : H1Tendsto Q (fun n => coframeC (e n)) de (coframeC e₀) de₀) :
    RenewalGeometry.LpTendsto Q.μ 2 (fun n x => spinConnL (e n x) (toJet (reJet (de n) x)))
      (fun x => spinConnL (e₀ x) (toJet (reJet de₀ x))) :=
  spinConn_L2_tendsto hKe hKGL (fun n => coframe_aemeasurable (hmem n)) hin hin₀
    (coframe_tendstoInMeasure hmem hmem₀ hconv) (coframeJet_L2_tendsto hmem hmem₀ hconv)

/-- **`eq:spin-connection-convergence`, second part, on a compact chart**: the metric-variation
operators `(k, ∂k) ↦ ω̇(e_h)[ė_h(k)]` converge in `L²(Q)` in operator norm. -/
theorem spinVarOp_L2_tendsto_of_h1 {T : ℝ} {Q : ChartBox T} {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hKGL : Ke ⊆ coframeGL) {e : ℕ → E4 → CoframeFibre}
    {de : ℕ → E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} {e₀ : E4 → CoframeFibre}
    {de₀ : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ}
    (hmem : ∀ n, MemH1 Q (coframeC (e n)) (de n)) (hmem₀ : MemH1 Q (coframeC e₀) de₀)
    (hin : ∀ n, ∀ᵐ x ∂Q.μ, e n x ∈ Ke) (hin₀ : ∀ᵐ x ∂Q.μ, e₀ x ∈ Ke)
    (hconv : H1Tendsto Q (fun n => coframeC (e n)) de (coframeC e₀) de₀) :
    RenewalGeometry.LpTendsto Q.μ 2 (fun n x => spinVarOp (e n x) (toJet (reJet (de n) x)))
      (fun x => spinVarOp (e₀ x) (toJet (reJet de₀ x))) :=
  spinVarOp_L2_tendsto hKe hKGL (fun n => coframe_aemeasurable (hmem n)) hin hin₀
    (coframe_tendstoInMeasure hmem hmem₀ hconv) (coframeJet_L2_tendsto hmem hmem₀ hconv)

/-! ### `F(e, e⁻¹)` coefficients and non-vacuity -/

/-- Unflattening of a coframe vector. -/
def coframeOfVec (v : Fin 4 × Fin 4 → ℝ) : CoframeFibre := fun a μ => v (a, μ)

/-- The nondegenerate chart in flattened coordinates (open). -/
def coframeVecGL : Set (Fin 4 × Fin 4 → ℝ) := {v | coframeOfVec v ∈ coframeGL}

theorem contDiff_coframeOfVec {n : WithTop ℕ∞} : ContDiff ℝ n coframeOfVec :=
  contDiff_pi.mpr fun a => contDiff_pi.mpr fun μ => contDiff_apply ℝ ℝ (a, μ)

theorem isOpen_coframeVecGL : IsOpen coframeVecGL :=
  isOpen_coframeGL.preimage (contDiff_coframeOfVec (n := 0)).continuous

theorem coframeVec_image_subset {Ke : Set CoframeFibre} (hKe : Ke ⊆ coframeGL) :
    coframeVec '' Ke ⊆ coframeVecGL := by
  rintro _ ⟨a, ha, rfl⟩; exact hKe ha

/-- Every smooth coefficient `F(e, e⁻¹)` of the coframe and its inverse is `C¹` on the
nondegenerate chart, hence admissible in `chart_composition`. -/
theorem contDiffOn_coeff_frame {F : CoframeFibre × CoframeFibre → ℝ} (hF : ContDiff ℝ 1 F) :
    ContDiffOn ℝ 1 (fun v => F (coframeOfVec v, fun μ a => frameAt (coframeOfVec v) μ a))
      coframeVecGL := by
  intro v hv
  refine ContDiffAt.contDiffWithinAt ?_
  refine hF.contDiffAt.comp v (ContDiffAt.prodMk contDiff_coframeOfVec.contDiffAt ?_)
  refine contDiffAt_pi.mpr fun μ => contDiffAt_pi.mpr fun a => ?_
  exact (contDiffAt_frameAt μ a hv).comp v contDiff_coframeOfVec.contDiffAt

/-- Non-vacuity of `chart_composition`: the constant flat coframe sequence on any chart with the
inverse-frame entry `(e⁻¹)⁰₀` as coefficient. -/
example {T : ℝ} (Q : ChartBox T) :
    H1Tendsto Q (fun _ => chartComp (fun v => frameAt (coframeOfVec v) 0 0)
        (fun _ => flatCoframe))
      (fun _ => chartGrad (fun v => frameAt (coframeOfVec v) 0 0) (fun _ => flatCoframe)
        (fun _ _ _ => 0))
      (chartComp (fun v => frameAt (coframeOfVec v) 0 0) (fun _ => flatCoframe))
      (chartGrad (fun v => frameAt (coframeOfVec v) 0 0) (fun _ => flatCoframe)
        (fun _ _ _ => 0)) := by
  have hmem : MemH1 Q (coframeC fun _ => flatCoframe) (fun _ _ _ => 0) :=
    memH1_const Q (fun p : Fin 4 × Fin 4 => (flatCoframe p.1 p.2 : ℂ))
  have hc := chart_composition Q (Ke := {flatCoframe}) isCompact_singleton isOpen_coframeVecGL
    (coframeVec_image_subset (singleton_subset_iff.mpr (coframeChart_subset_GL
      flatCoframe_mem_chart)))
    (contDiffOn_coeff_frame (F := fun p => p.2 0 0) (by fun_prop))
    (fun _ => hmem) hmem (fun _ => Eventually.of_forall fun _ => rfl)
    (Eventually.of_forall fun _ => rfl) (h1Tendsto_const Q _ _)
  exact hc.2.2.1

end EinsteinSM
end RenewalGeometry
