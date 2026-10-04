/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.CoordinateCurvature
import RenewalGeometry.Analysis.FirstVariationCalculus

/-!
# The assembled strong–weak improvement criterion: the Einstein product
  (`prop:improvement`, Einstein–Standard-Model action-closure manuscript; clause-level)

`prop:improvement` asserts that for `g_h → g` in `W^{1,∞}`, `g_h ⇀ g` in `W^{2,p}` (`1 < p < ∞`),
uniform inverse bounds, and `H_h → H` in `L^{2p'}`, the assembled improvement
`f_h Ein(g_h) + (g_h□_{g_h} - ∇^h∇^h)f_h` (`f = |H|²`) converges in distributions, volume densities
included.  This file proves the **analytic core** and the **first (Einstein) product**:

* `tendsto_integral_clm_strong_weak` (generic): operator fields `Λ_h → Λ` strongly in `L^{p'}` paired
  with `W_h ⇀ W` weakly in `L^p` (bounded): `∫ Λ_h(W_h) → ∫ Λ(W)` — "pairing with strong `f_h` in
  `L^{p'}` passes the entire expression".
* The coordinate Einstein tensor of a metric jet `(g, ∂g, ∂²g)` (`einJ`, from the Christoffel symbols
  and the Riemann / Ricci / scalar curvature of `CoordinateCurvature.lean`, with
  `∂_cΓ^a_{db} = dGam0(g, ∂g) + dGamL(g)[∂²g]`), and its **affine structure**
  `Ein(g, ∂g, ∂²g) = Ein(g, ∂g, 0) + EinLin(g)[∂²g]` (`einJ_affine`): linear in the second
  derivatives with coefficients continuous in `g` on the nondegenerate set, plus a quadratic
  first-derivative part.
* `einstein_product_tendsto`: if the metric jets converge (`g_h → g`, `∂g_h → ∂g` in measure, e.g. in
  `L^∞`, with values in a compact subset of the nondegenerate set — uniform inverse bounds), the
  second derivatives converge weakly in `L^p` (bounded), and `f_h → f` in `L^{p'}`, then for every
  bounded measurable test tensor `k`,
  `∫ f_h ⟨k, Ein(g_h)⟩ √|g_h| → ∫ f ⟨k, Ein(g)⟩ √|g|`.

Rendering: a finite measure space `X` (the chart with the comparison measure), metric jets as
functions into the finite-dimensional jet spaces (the second-derivative field is the weak `∂²g`
of a `W^{2,p}` metric); the Hessian term `(g□ - ∇∇)f` of the assembled expression is not treated
here (see the record's plan).
-/

open MeasureTheory Filter Topology Set Finset
open scoped ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

namespace RenewalGeometry
namespace AssembledImprovement

/-! ### Strong `L^{p'}` × weak `L^p` pairings of operator fields -/

section StrongWeak

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Weak `L^p` convergence of `V`-valued fields, tested by `L^q` scalar functions and linear
functionals (`q` the dual exponent). -/
def WeakLpTendsto (μ : Measure X) (q : ℝ≥0∞) (W : ℕ → X → V) (W₀ : X → V) : Prop :=
  ∀ ℓ : V →L[ℝ] ℝ, ∀ φ : X → ℝ, MemLp φ q μ →
    Tendsto (fun n => ∫ x, φ x * ℓ (W n x) ∂μ) atTop (𝓝 (∫ x, φ x * ℓ (W₀ x) ∂μ))

theorem integrable_clm_apply_of_memLp {p q : ℝ≥0∞} [hpq : ENNReal.HolderTriple q p 1]
    {Λ : X → V →L[ℝ] ℝ} (hΛ : MemLp Λ q μ) {W : X → V} (hW : MemLp W p μ) :
    Integrable (fun x => Λ x (W x)) μ := by
  have hm : AEStronglyMeasurable (fun x => Λ x (W x)) μ :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (L : V →L[ℝ] ℝ) (w : V) => L w)
      (by fun_prop) hΛ.1 hW.1
  have hprod : MemLp (fun x => ‖Λ x‖ * ‖W x‖) 1 μ := hW.norm.mul' hΛ.norm
  exact (memLp_one_iff_integrable.mp hprod).mono' hm
    (Eventually.of_forall fun x => (Λ x).le_opNorm (W x))

theorem abs_integral_clm_le {p q : ℝ≥0∞} [hpq : ENNReal.HolderTriple q p 1]
    {Λ : X → V →L[ℝ] ℝ} (hΛ : AEStronglyMeasurable Λ μ) {W : X → V}
    (hW : AEStronglyMeasurable W μ) :
    ENNReal.ofReal |∫ x, Λ x (W x) ∂μ| ≤ eLpNorm Λ q μ * eLpNorm W p μ := by
  have hm : AEStronglyMeasurable (fun x => ‖Λ x‖ * ‖W x‖) μ := hΛ.norm.mul hW.norm
  calc ENNReal.ofReal |∫ x, Λ x (W x) ∂μ| = ‖∫ x, Λ x (W x) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
    _ ≤ ∫⁻ x, ‖Λ x (W x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => Λ x (W x)) 1 μ := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ eLpNorm (fun x => ‖Λ x‖ * ‖W x‖) 1 μ :=
        eLpNorm_mono_real fun x => (Λ x).le_opNorm (W x)
    _ ≤ eLpNorm (fun x => ‖Λ x‖) q μ * eLpNorm (fun x => ‖W x‖) p μ := by
        have := eLpNorm_smul_le_mul_eLpNorm (p := q) (q := p) (r := 1) hW.norm hΛ.norm
        exact (le_of_eq rfl).trans this
    _ = _ := by rw [eLpNorm_norm, eLpNorm_norm]

/-- **Strong × weak pairing of operator fields.**  If `Λ_h → Λ` strongly in `L^q(μ; V^*)` and
`W_h ⇀ W` weakly in `L^p(μ; V)` with `‖W_h‖_{L^p} ≤ B`, where `1/q + 1/p = 1`, then
`∫ Λ_h(W_h) dμ → ∫ Λ(W) dμ`. -/
theorem tendsto_integral_clm_strong_weak {p q : ℝ≥0∞} [hpq : ENNReal.HolderTriple q p 1]
    {Λ : ℕ → X → V →L[ℝ] ℝ} {Λ₀ : X → V →L[ℝ] ℝ} (hΛ : RenewalGeometry.LpTendsto μ q Λ Λ₀)
    {W : ℕ → X → V} {W₀ : X → V} (hW : ∀ n, MemLp (W n) p μ) (hW₀ : MemLp W₀ p μ)
    {B : ℝ≥0∞} (hB : B ≠ ⊤) (hWB : ∀ n, eLpNorm (W n) p μ ≤ B)
    (hweak : WeakLpTendsto μ q W W₀) :
    Tendsto (fun n => ∫ x, Λ n x (W n x) ∂μ) atTop (𝓝 (∫ x, Λ₀ x (W₀ x) ∂μ)) := by
  -- the fixed-coefficient part, through a basis of `V`
  set b := Module.finBasis ℝ V
  have hexp : ∀ (L : V →L[ℝ] ℝ) (w : V), L w = ∑ k, L (b k) * b.coord k w := by
    intro L w
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hcoef : ∀ k, MemLp (fun x => Λ₀ x (b k)) q μ := fun k => by
    have := (ContinuousLinearMap.apply ℝ ℝ (b k)).comp_memLp' hΛ.memLp_lim
    exact this
  have hfix : Tendsto (fun n => ∫ x, Λ₀ x (W n x) ∂μ) atTop (𝓝 (∫ x, Λ₀ x (W₀ x) ∂μ)) := by
    have hsum : ∀ w : X → V, MemLp w p μ → ∫ x, Λ₀ x (w x) ∂μ =
        ∑ k, ∫ x, Λ₀ x (b k) * (LinearMap.toContinuousLinearMap (b.coord k)) (w x) ∂μ := by
      intro w hw
      rw [← integral_finset_sum]
      · exact integral_congr_ae (Eventually.of_forall fun x => by
          simp only [LinearMap.coe_toContinuousLinearMap']
          exact hexp _ _)
      · intro k _
        have h1 := (LinearMap.toContinuousLinearMap (b.coord k)).comp_memLp' hw
        exact (h1.mul' (hcoef k)).integrable le_rfl |>.congr (Eventually.of_forall fun x => rfl)
    rw [hsum _ hW₀]
    refine (tendsto_finset_sum _ fun k _ => hweak _ _ (hcoef k)).congr fun n => ?_
    exact (hsum _ (hW n)).symm
  -- the strong part
  have hdiff : Tendsto (fun n => ∫ x, (Λ n x - Λ₀ x) (W n x) ∂μ) atTop (𝓝 0) := by
    have hle : ∀ n, ENNReal.ofReal |∫ x, (Λ n x - Λ₀ x) (W n x) ∂μ| ≤
        eLpNorm (Λ n - Λ₀) q μ * B := fun n =>
      (abs_integral_clm_le (p := p) (q := q) ((hΛ.memLp n).1.sub hΛ.memLp_lim.1) (hW n).1).trans
        (by gcongr; exact hWB n)
    have h0 : Tendsto (fun n => eLpNorm (Λ n - Λ₀) q μ * B) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hΛ.tendsto (Or.inr hB)
    have h1 : Tendsto (fun n => ENNReal.ofReal |∫ x, (Λ n x - Λ₀ x) (W n x) ∂μ|) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le) hle
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simp only [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_zero] at h2
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h2
  have hsplit : ∀ n, ∫ x, Λ n x (W n x) ∂μ =
      ∫ x, (Λ n x - Λ₀ x) (W n x) ∂μ + ∫ x, Λ₀ x (W n x) ∂μ := fun n => by
    have hi1 : Integrable (fun x => (Λ n x - Λ₀ x) (W n x)) μ :=
      integrable_clm_apply_of_memLp ((hΛ.memLp n).sub hΛ.memLp_lim) (hW n)
    have hi2 : Integrable (fun x => Λ₀ x (W n x)) μ :=
      integrable_clm_apply_of_memLp hΛ.memLp_lim (hW n)
    rw [← integral_add hi1 hi2]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp)
  simpa [hsplit] using hdiff.add hfix

end StrongWeak

/-! ### The coordinate Einstein tensor of a metric jet and its affine structure -/

section Jets

/-- Metric values `g_{μν}`. -/
abbrev MetJ : Type := Fin 4 → Fin 4 → ℝ
/-- First metric jets `∂_i g_{μν}`. -/
abbrev D1 : Type := Fin 4 → Fin 4 → Fin 4 → ℝ
/-- Second metric jets `∂_i∂_j g_{μν}`. -/
abbrev D2 : Type := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- The inverse metric `g^{μν}`. -/
def ginvJ (g : MetJ) : MetJ := fun i j => (Matrix.of g)⁻¹ i j

/-- `∂_c g^{ae} = -g^{ap} ∂_c g_{pq} g^{qe}` from the inverse metric and the first jet. -/
def dginvP (ginv : MetJ) (dg : D1) (c : Fin 4) : MetJ :=
  fun a e => -∑ p, ∑ q, ginv a p * dg c p q * ginv q e

/-- First-derivative part of `∂_cΓ^a_{db}`: `½ Σ_e ∂_c g^{ae}(∂_d g_{eb} + ∂_b g_{ed} - ∂_e g_{db})`. -/
def dGam0P (ginv : MetJ) (dg : D1) : D2 :=
  fun c a d b => (1 / 2) * ∑ e, dginvP ginv dg c a e * (dg d e b + dg b e d - dg e d b)

/-- Second-derivative part of `∂_cΓ^a_{db}`:
`½ Σ_e g^{ae}(∂_c∂_d g_{eb} + ∂_c∂_b g_{ed} - ∂_c∂_e g_{db})`. -/
def dGamLP (ginv : MetJ) (ddg : D2) : D2 :=
  fun c a d b => (1 / 2) * ∑ e, ginv a e * (ddg c d e b + ddg c b e d - ddg c e d b)

/-- The coordinate Einstein tensor `Ric - ½ g Scal` of a metric jet, written through the inverse
metric: Christoffel symbols `christoffel g^{-1} ∂g`, connection jet `∂Γ = dGam0P + dGamLP[∂²g]`, and
`ricci`, `scalarCurv` of `CoordinateCurvature.lean` (convention `∂_cΓ^a_{db}` in slot `c a d b`). -/
def einP (ginv g : MetJ) (dg : D1) (ddg : D2) : MetJ := fun b d =>
  ricci (christoffel ginv dg) (dGam0P ginv dg + dGamLP ginv ddg) b d -
    (1 / 2) * g b d * scalarCurv ginv (christoffel ginv dg) (dGam0P ginv dg + dGamLP ginv ddg)

/-- **The Einstein tensor of a `W^{2,p}` metric** at a point, from its jet `(g, ∂g, ∂²g)`. -/
def einJ (g : MetJ) (dg : D1) (ddg : D2) : MetJ := einP (ginvJ g) g dg ddg

/-- The volume density `√|det g|`. -/
def volJ (g : MetJ) : ℝ := Real.sqrt |(Matrix.of g).det|

/-- The tested Einstein density `Σ_{b,d} k^{bd} Ein_{bd} √|g|`. -/
def einTest (g : MetJ) (dg : D1) (ddg : D2) (k : MetJ) : ℝ :=
  ∑ b, ∑ d, k b d * einJ g dg ddg b d * volJ g

/-- The linear part of the Ricci tensor in the connection jet. -/
def ricciLin (Y : D2) : MetJ := fun b d => ∑ a, (Y a a d b - Y d a a b)

theorem ricci_add (Gam : D1) (X Y : D2) : ricci Gam (X + Y) = ricci Gam X + ricciLin Y := by
  funext b d
  simp only [ricci, riemann, ricciLin, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem scalarCurv_add (ginv : MetJ) (Gam : D1) (X Y : D2) :
    scalarCurv ginv Gam (X + Y) = scalarCurv ginv Gam X + ∑ b, ∑ d, ginv b d * ricciLin Y b d := by
  simp only [scalarCurv, ricci_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The linear part of the Einstein tensor in the connection jet. -/
def einLinP (ginv g : MetJ) (Y : D2) : MetJ := fun b d =>
  ricciLin Y b d - (1 / 2) * g b d * ∑ b', ∑ d', ginv b' d' * ricciLin Y b' d'

theorem dGamLP_zero (ginv : MetJ) : dGamLP ginv 0 = 0 := by
  funext c a d b; simp [dGamLP]

/-- **Affine structure of the Einstein tensor**: linear in the second derivatives, plus a part
depending on `(g, ∂g)` only. -/
theorem einP_affine (ginv g : MetJ) (dg : D1) (ddg : D2) :
    einP ginv g dg ddg = einP ginv g dg 0 + einLinP ginv g (dGamLP ginv ddg) := by
  funext b d
  simp only [einP, einLinP, dGamLP_zero, add_zero, ricci_add, scalarCurv_add, Pi.add_apply]
  ring

/-- The tested Einstein density through the inverse metric (polynomial in all arguments). -/
def einTestP (ginv g : MetJ) (dg : D1) (ddg : D2) (k : MetJ) : ℝ :=
  ∑ b, ∑ d, k b d * einP ginv g dg ddg b d * volJ g

theorem einTest_eq (g : MetJ) (dg : D1) (ddg : D2) (k : MetJ) :
    einTest g dg ddg k = einTestP (ginvJ g) g dg ddg k := rfl

theorem continuous_volJ : Continuous volJ := by
  unfold volJ
  exact (continuous_id.matrix_det.abs).sqrt

theorem continuous_einTestP : Continuous fun p : MetJ × MetJ × D1 × D2 × MetJ =>
    einTestP p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have hv : Continuous fun p : MetJ × MetJ × D1 × D2 × MetJ => volJ p.2.1 :=
    continuous_volJ.comp (continuous_fst.comp continuous_snd)
  unfold einTestP einP scalarCurv ricci riemann christoffel dGam0P dGamLP dginvP
  fun_prop

/-- The linear part of the tested Einstein density, `∂²g ↦ Σ k^{bd} EinLin(g)[∂²g]_{bd} √|g|`. -/
def einTestLinFun (ginv g k : MetJ) (ddg : D2) : ℝ :=
  ∑ b, ∑ d, k b d * einLinP ginv g (dGamLP ginv ddg) b d * volJ g

theorem einTestP_affine (ginv g : MetJ) (dg : D1) (ddg : D2) (k : MetJ) :
    einTestP ginv g dg ddg k = einTestP ginv g dg 0 k + einTestLinFun ginv g k ddg := by
  simp only [einTestP, einTestLinFun, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
  rw [einP_affine ginv g dg ddg]
  simp only [Pi.add_apply]
  ring

end Jets

/-! ### Linear packaging and continuity of the coefficients -/

section Packaging

theorem dGamLP_add (ginv : MetJ) (X Y : D2) :
    dGamLP ginv (X + Y) = dGamLP ginv X + dGamLP ginv Y := by
  funext c a d b
  simp only [dGamLP, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun e _ => by ring

theorem dGamLP_smul (ginv : MetJ) (r : ℝ) (X : D2) :
    dGamLP ginv (r • X) = r • dGamLP ginv X := by
  funext c a d b
  simp only [dGamLP, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by ring

theorem ricciLin_add (X Y : D2) : ricciLin (X + Y) = ricciLin X + ricciLin Y := by
  funext b d
  simp only [ricciLin, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem ricciLin_smul (r : ℝ) (X : D2) : ricciLin (r • X) = r • ricciLin X := by
  funext b d
  simp only [ricciLin, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem einLinP_add (ginv g : MetJ) (X Y : D2) :
    einLinP ginv g (X + Y) = einLinP ginv g X + einLinP ginv g Y := by
  funext b d
  simp only [einLinP, ricciLin_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem einLinP_smul (ginv g : MetJ) (r : ℝ) (X : D2) :
    einLinP ginv g (r • X) = r • einLinP ginv g X := by
  funext b d
  simp only [einLinP, ricciLin_smul, Pi.smul_apply, smul_eq_mul]
  have h : ∑ b', ∑ d', ginv b' d' * (r * ricciLin X b' d') =
      r * ∑ b', ∑ d', ginv b' d' * ricciLin X b' d' := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [h]
  ring

/-- The `(g, ∂g)`-part of the tested density as a linear functional of the test tensor. -/
def E0L (ginv g : MetJ) (dg : D1) : MetJ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun k => einTestP ginv g dg 0 k
      map_add' := fun k k' => by
        simp only [einTestP, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r k => by
        simp only [einTestP, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring }

theorem E0L_apply (ginv g : MetJ) (dg : D1) (k : MetJ) : E0L ginv g dg k = einTestP ginv g dg 0 k :=
  rfl

/-- The second-derivative part of the tested density, bilinear in the test tensor and `∂²g`. -/
def ELinL (ginv g : MetJ) : MetJ →L[ℝ] D2 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun k => LinearMap.toContinuousLinearMap
        { toFun := fun ddg => einTestLinFun ginv g k ddg
          map_add' := fun X Y => by
            simp only [einTestLinFun, dGamLP_add, einLinP_add, Pi.add_apply, mul_add, add_mul,
              Finset.sum_add_distrib]
          map_smul' := fun r X => by
            simp only [einTestLinFun, dGamLP_smul, einLinP_smul, Pi.smul_apply, smul_eq_mul,
              RingHom.id_apply, Finset.mul_sum]
            exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring }
      map_add' := fun k k' => by
        ext ddg
        simp only [einTestLinFun, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
          AddHom.coe_mk, ContinuousLinearMap.add_apply, Pi.add_apply, add_mul,
          Finset.sum_add_distrib]
      map_smul' := fun r k => by
        ext ddg
        simp only [einTestLinFun, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
          AddHom.coe_mk, ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring }

theorem ELinL_apply (ginv g k : MetJ) (ddg : D2) : ELinL ginv g k ddg = einTestLinFun ginv g k ddg :=
  rfl

theorem continuous_E0L : Continuous fun p : MetJ × MetJ × D1 => E0L p.1 p.2.1 p.2.2 := by
  refine continuous_clm_apply.mpr fun k => ?_
  simp only [E0L_apply]
  exact continuous_einTestP.comp (continuous_fst.prodMk (continuous_snd.fst.prodMk
    (continuous_snd.snd.prodMk (continuous_const.prodMk continuous_const))))

theorem continuous_ELinL : Continuous fun p : MetJ × MetJ => ELinL p.1 p.2 := by
  refine continuous_clm_apply.mpr fun k => continuous_clm_apply.mpr fun ddg => ?_
  simp only [ELinL_apply]
  have hv : Continuous fun p : MetJ × MetJ => volJ p.2 := continuous_volJ.comp continuous_snd
  unfold einTestLinFun einLinP ricciLin dGamLP
  fun_prop

/-- The nondegenerate set of metric values. -/
def nondeg : Set MetJ := {g | (Matrix.of g).det ≠ 0}

theorem continuousOn_ginvJ : ContinuousOn ginvJ nondeg := by
  have hdet : Continuous fun g : MetJ => (Matrix.of g).det := continuous_id.matrix_det
  have hadj : Continuous fun g : MetJ => (Matrix.of g).adjugate :=
    continuous_id.matrix_adjugate
  have h : ContinuousOn (fun g : MetJ => ((Matrix.of g).det)⁻¹ • (Matrix.of g).adjugate) nondeg :=
    (hdet.continuousOn.inv₀ fun g hg => hg).smul hadj.continuousOn
  refine h.congr fun g hg => ?_
  funext i j
  simp only [ginvJ, Matrix.inv_def, Ring.inverse_eq_inv']

end Packaging

/-! ### `prop:improvement`, the Einstein product -/

/-- The nondegenerate jets `(g, ∂g, k)`. -/
def nondegJ : Set (MetJ × D1 × MetJ) := Prod.fst ⁻¹' nondeg

theorem isOpen_nondegJ : IsOpen nondegJ :=
  (isOpen_ne_fun (continuous_id.matrix_det) continuous_const).preimage continuous_fst

theorem continuousOn_ginvJ_fst : ContinuousOn (fun z : MetJ × D1 × MetJ => ginvJ z.1) nondegJ :=
  continuousOn_ginvJ.comp continuous_fst.continuousOn fun _ hz => hz

/-- `L ↦ (c ↦ c • L)`, as a continuous linear map. -/
def scalL (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] : W →L[ℝ] ℝ →L[ℝ] W :=
  ContinuousLinearMap.smulRightL ℝ ℝ W (ContinuousLinearMap.id ℝ ℝ)

theorem scalL_apply {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : W) (c : ℝ) :
    scalL W L c = c • L := by
  simp [scalL]

/-- The `(g, ∂g)`-coefficient `c ↦ c · E0(g, ∂g; k)`. -/
def coefΦ1 (z : MetJ × D1 × MetJ) : ℝ →L[ℝ] ℝ :=
  scalL ℝ (einTestP (ginvJ z.1) z.1 z.2.1 0 z.2.2)

/-- The second-derivative coefficient `c ↦ c · EinLin(g; k)`. -/
def coefΦ2 (z : MetJ × D1 × MetJ) : ℝ →L[ℝ] D2 →L[ℝ] ℝ :=
  scalL (D2 →L[ℝ] ℝ) (ELinL (ginvJ z.1) z.1 z.2.2)

theorem continuous_einTestP0 : Continuous fun z : MetJ × MetJ × D1 × MetJ =>
    einTestP z.1 z.2.1 z.2.2.1 0 z.2.2.2 := by
  have hv : Continuous fun z : MetJ × MetJ × D1 × MetJ => volJ z.2.1 :=
    continuous_volJ.comp (continuous_fst.comp continuous_snd)
  unfold einTestP einP scalarCurv ricci riemann christoffel dGam0P dGamLP dginvP
  fun_prop

theorem coefΦ1_apply (z : MetJ × D1 × MetJ) (c : ℝ) :
    coefΦ1 z c = c * einTestP (ginvJ z.1) z.1 z.2.1 0 z.2.2 := by
  simp only [coefΦ1, scalL_apply, smul_eq_mul]

theorem coefΦ2_apply (z : MetJ × D1 × MetJ) (c : ℝ) (ddg : D2) :
    coefΦ2 z c ddg = c * einTestLinFun (ginvJ z.1) z.1 z.2.2 ddg := by
  simp only [coefΦ2, scalL_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ELinL_apply]

theorem continuousOn_coefΦ1 : ContinuousOn coefΦ1 nondegJ := by
  refine continuousOn_clm_apply.mpr fun c => ?_
  have hpair : ContinuousOn (fun z : MetJ × D1 × MetJ => (ginvJ z.1, z)) nondegJ :=
    continuousOn_ginvJ_fst.prodMk continuousOn_id
  have h := (continuousOn_const (c := c)).mul (continuous_einTestP0.comp_continuousOn hpair)
  exact h.congr fun z _ => coefΦ1_apply z c

theorem continuous_einTestLinFun (ddg : D2) :
    Continuous fun p : MetJ × MetJ × MetJ => einTestLinFun p.1 p.2.1 p.2.2 ddg := by
  have hv : Continuous fun p : MetJ × MetJ × MetJ => volJ p.2.1 :=
    continuous_volJ.comp (continuous_fst.comp continuous_snd)
  unfold einTestLinFun einLinP ricciLin dGamLP
  fun_prop

theorem continuousOn_coefΦ2 : ContinuousOn coefΦ2 nondegJ := by
  refine continuousOn_clm_apply.mpr fun c => continuousOn_clm_apply.mpr fun ddg => ?_
  have hpair : ContinuousOn (fun z : MetJ × D1 × MetJ => (ginvJ z.1, z.1, z.2.2)) nondegJ :=
    continuousOn_ginvJ_fst.prodMk (continuous_fst.continuousOn.prodMk
      continuous_snd.snd.continuousOn)
  have h := (continuousOn_const (c := c)).mul
    ((continuous_einTestLinFun ddg).comp_continuousOn hpair)
  exact h.congr fun z _ => coefΦ2_apply z c ddg

theorem einTest_split (G : MetJ) (dG : D1) (ddG : D2) (K' : MetJ) (c : ℝ) :
    c * einTest G dG ddG K' = coefΦ1 (G, dG, K') c + coefΦ2 (G, dG, K') c ddG := by
  simp only [coefΦ1, coefΦ2, scalL_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ELinL_apply, einTest_eq, einTestP_affine (ginvJ G) G dG ddG K']
  ring

section EinsteinProduct

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

set_option maxHeartbeats 4000000 in
/-- **The Einstein product of the assembled improvement passes to the limit**
(`prop:improvement`, first product, with the volume density).  Let `g_h → g` in `W^{1,∞}` (the first
jets `(g_h, ∂g_h) → (g, ∂g)` in `L^∞`) with values in a fixed compact subset of the nondegenerate
set (uniform inverse bounds), `∂g_h` uniformly bounded, the second derivatives `∂²g_h ⇀ ∂²g` weakly in
`L^p` (bounded: `g_h ⇀ g` in `W^{2,p}`), and `f_h → f` in `L^{p'}` (`1/p + 1/p' = 1`, `p' < ∞`).
Then for every bounded measurable test tensor `k`,
`∫ f_h ⟨k, Ein(g_h)⟩ √|g_h| dμ → ∫ f ⟨k, Ein(g)⟩ √|g| dμ`.  The proof is the manuscript's: the Einstein
tensor is linear in `∂²g` with strongly convergent bounded coefficients plus quadratic first-derivative
terms (`einP_affine`), and the strong `L^{p'}` factor passes the weak `L^p` second derivatives
(`tendsto_integral_clm_strong_weak`). -/
theorem einstein_product_tendsto {p q : ℝ≥0∞} [ENNReal.HolderTriple q p 1] [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) {g : ℕ → X → MetJ} {g₀ : X → MetJ} {dg : ℕ → X → D1} {dg₀ : X → D1}
    {ddg : ℕ → X → D2} {ddg₀ : X → D2} {k : X → MetJ}
    {Kg : Set MetJ} (hKg : IsCompact Kg) (hKgnd : Kg ⊆ nondeg)
    (hgK : ∀ n, ∀ᵐ x ∂μ, g n x ∈ Kg) (hg₀K : ∀ᵐ x ∂μ, g₀ x ∈ Kg)
    {D : ℝ} (hdgD : ∀ n, ∀ᵐ x ∂μ, ‖dg n x‖ ≤ D) (hdg₀D : ∀ᵐ x ∂μ, ‖dg₀ x‖ ≤ D)
    (hgm : ∀ n, AEStronglyMeasurable (g n) μ) (hdgm : ∀ n, AEStronglyMeasurable (dg n) μ)
    (hg : Tendsto (fun n => eLpNorm (g n - g₀) ⊤ μ) atTop (𝓝 0))
    (hdg : Tendsto (fun n => eLpNorm (dg n - dg₀) ⊤ μ) atTop (𝓝 0))
    (hddg : ∀ n, MemLp (ddg n) p μ) (hddg₀ : MemLp ddg₀ p μ) {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hddgB : ∀ n, eLpNorm (ddg n) p μ ≤ B) (hweak : WeakLpTendsto μ q ddg ddg₀)
    (hkm : AEStronglyMeasurable k μ) {Ck : ℝ} (hk : ∀ x, ‖k x‖ ≤ Ck)
    {f : ℕ → X → ℝ} {f₀ : X → ℝ} (hf : RenewalGeometry.LpTendsto μ q f f₀) :
    Tendsto (fun n => ∫ x, f n x * einTest (g n x) (dg n x) (ddg n x) (k x) ∂μ) atTop
      (𝓝 (∫ x, f₀ x * einTest (g₀ x) (dg₀ x) (ddg₀ x) (k x) ∂μ)) := by
  -- the jets `(g, ∂g, k)` converge in measure inside a compact subset of the nondegenerate set
  have hKJ : IsCompact (Kg ×ˢ Metric.closedBall (0 : D1) D ×ˢ Metric.closedBall (0 : MetJ) Ck) :=
    hKg.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hJK : ∀ n, ∀ᵐ x ∂μ, (g n x, dg n x, k x) ∈
      Kg ×ˢ Metric.closedBall (0 : D1) D ×ˢ Metric.closedBall (0 : MetJ) Ck := fun n => by
    filter_upwards [hgK n, hdgD n] with x h1 h2
    exact ⟨h1, mem_closedBall_zero_iff.mpr h2, mem_closedBall_zero_iff.mpr (hk x)⟩
  have hJ₀K : ∀ᵐ x ∂μ, (g₀ x, dg₀ x, k x) ∈
      Kg ×ˢ Metric.closedBall (0 : D1) D ×ˢ Metric.closedBall (0 : MetJ) Ck := by
    filter_upwards [hg₀K, hdg₀D] with x h1 h2
    exact ⟨h1, mem_closedBall_zero_iff.mpr h2, mem_closedBall_zero_iff.mpr (hk x)⟩
  have hJ : TendstoInMeasure μ (fun n x => (g n x, dg n x, k x)) atTop
      (fun x => (g₀ x, dg₀ x, k x)) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm_top ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hg.add hdg)
      (fun _ => bot_le) fun n => ?_
    calc eLpNorm ((fun x => (g n x, dg n x, k x)) - fun x => (g₀ x, dg₀ x, k x)) ⊤ μ ≤
          eLpNorm (fun x => ‖g n x - g₀ x‖ + ‖dg n x - dg₀ x‖) ⊤ μ :=
          eLpNorm_mono_real fun x => by
            simp only [Pi.sub_apply, Prod.mk_sub_mk, sub_self]
            exact norm_prod_le_iff.mpr ⟨le_add_of_nonneg_right (norm_nonneg _),
              norm_prod_le_iff.mpr ⟨le_add_of_nonneg_left (norm_nonneg _), by
                rw [norm_zero]; positivity⟩⟩
      _ ≤ eLpNorm (fun x => ‖g n x - g₀ x‖) ⊤ μ + eLpNorm (fun x => ‖dg n x - dg₀ x‖) ⊤ μ := by
          simp only [eLpNorm_exponent_top]
          exact eLpNormEssSup_add_le
      _ = _ := by rw [eLpNorm_norm, eLpNorm_norm]; rfl
  have hKJS : ∀ z ∈ Kg ×ˢ Metric.closedBall (0 : D1) D ×ˢ Metric.closedBall (0 : MetJ) Ck,
      z ∈ nondegJ := fun z hz => hKgnd hz.1
  have hJm : ∀ n, AEMeasurable (fun x => (g n x, dg n x, k x)) μ := fun n =>
    (hgm n).aemeasurable.prodMk ((hdgm n).aemeasurable.prodMk hkm.aemeasurable)
  have hJS : ∀ n, ∀ᵐ x ∂μ, (g n x, dg n x, k x) ∈ nondegJ := fun n =>
    (hJK n).mono fun x hx => hKJS _ hx
  have hΦ1m : ∀ n, AEStronglyMeasurable (fun x => coefΦ1 (g n x, dg n x, k x)) μ := fun n =>
    FirstVariationCalculus.aestronglyMeasurable_comp_of_continuousOn' (Φ := coefΦ1)
      isOpen_nondegJ continuousOn_coefΦ1 (hJm n) (hJS n)
  have hΦ2m : ∀ n, AEStronglyMeasurable (fun x => coefΦ2 (g n x, dg n x, k x)) μ := fun n =>
    FirstVariationCalculus.aestronglyMeasurable_comp_of_continuousOn' (Φ := coefΦ2)
      isOpen_nondegJ continuousOn_coefΦ2 (hJm n) (hJS n)
  -- the `(g, ∂g)` part: strong convergence in `L^{p'} ⊂ L¹`
  have P1 := FirstVariationCalculus.tendsto_coeff_apply hKJ (continuousOn_coefΦ1.mono hKJS) hJK
    hJ₀K hJ hΦ1m hq hf
  have P1L := P1.mono one_ne_zero (Fact.out : (1 : ℝ≥0∞) ≤ q)
  -- the second-derivative part: strong `L^{p'}` coefficients against weak `L^p` second jets
  have P2 := FirstVariationCalculus.tendsto_coeff_apply hKJ (continuousOn_coefΦ2.mono hKJS) hJK
    hJ₀K hJ hΦ2m hq hf
  have P2' := tendsto_integral_clm_strong_weak (p := p) (q := q) P2 hddg hddg₀ hB hddgB hweak
  have e1 : ∀ n, ∫ x, f n x * einTest (g n x) (dg n x) (ddg n x) (k x) ∂μ =
      ∫ x, coefΦ1 (g n x, dg n x, k x) (f n x) ∂μ +
        ∫ x, coefΦ2 (g n x, dg n x, k x) (f n x) (ddg n x) ∂μ := fun n => by
    rw [← integral_add (memLp_one_iff_integrable.mp (P1L.memLp n))
      (integrable_clm_apply_of_memLp (P2.memLp n) (hddg n))]
    exact integral_congr_ae (Eventually.of_forall fun x => einTest_split _ _ _ _ _)
  have e0 : ∫ x, f₀ x * einTest (g₀ x) (dg₀ x) (ddg₀ x) (k x) ∂μ =
      ∫ x, coefΦ1 (g₀ x, dg₀ x, k x) (f₀ x) ∂μ +
        ∫ x, coefΦ2 (g₀ x, dg₀ x, k x) (f₀ x) (ddg₀ x) ∂μ := by
    rw [← integral_add (memLp_one_iff_integrable.mp P1L.memLp_lim)
      (integrable_clm_apply_of_memLp P2.memLp_lim hddg₀)]
    exact integral_congr_ae (Eventually.of_forall fun x => einTest_split _ _ _ _ _)
  rw [e0]
  exact (P1L.tendsto_integral.add P2').congr fun n => (e1 n).symm

end EinsteinProduct

/-! ### Non-vacuity -/

/-- The Minkowski metric `diag(-1, 1, 1, 1)` as a metric value. -/
def minkJ : MetJ := fun i j => if i = j then (if i = 0 then -1 else 1) else 0

theorem minkJ_nondeg : minkJ ∈ nondeg := by
  show (Matrix.of minkJ).det ≠ 0
  have : Matrix.of minkJ = Matrix.diagonal fun i : Fin 4 => if i = 0 then (-1 : ℝ) else 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [minkJ]
    · simp [minkJ, Matrix.diagonal_apply_ne _ h, h]
  rw [this, Matrix.det_diagonal]
  simp [Fin.prod_univ_four]

/-- **Non-vacuity of `einstein_product_tendsto`**: constant Minkowski jets, zero second
derivatives, `f = 1` and `k = 1` on a one-point chart satisfy the hypothesis packet (`p = p' = 2`). -/
example : Tendsto (fun n : ℕ => ∫ x, (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) n x *
    einTest ((fun (_ : ℕ) (_ : Unit) => minkJ) n x) ((fun (_ : ℕ) (_ : Unit) => (0 : D1)) n x)
      ((fun (_ : ℕ) (_ : Unit) => (0 : D2)) n x) ((fun _ : Unit => (fun _ _ => 1 : MetJ)) x)
      ∂(Measure.dirac ())) atTop
    (𝓝 (∫ x, (fun _ : Unit => (1 : ℝ)) x * einTest ((fun _ : Unit => minkJ) x)
      ((fun _ : Unit => (0 : D1)) x) ((fun _ : Unit => (0 : D2)) x)
      ((fun _ : Unit => (fun _ _ => 1 : MetJ)) x) ∂(Measure.dirac ()))) := by
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  exact einstein_product_tendsto (p := 2) (q := 2) (by norm_num) (Kg := {minkJ})
    isCompact_singleton (by simpa using minkJ_nondeg) (fun _ => Eventually.of_forall fun _ => rfl)
    (Eventually.of_forall fun _ => rfl) (D := 0) (fun _ => Eventually.of_forall fun _ => by simp)
    (Eventually.of_forall fun _ => by simp) (fun _ => aestronglyMeasurable_const)
    (fun _ => aestronglyMeasurable_const) (by simp) (by simp) (fun _ => memLp_const _)
    (memLp_const _) (B := eLpNorm (fun _ : Unit => (0 : D2)) 2 (Measure.dirac ()))
    (by simp) (fun _ => le_rfl) (fun _ _ _ => tendsto_const_nhds) aestronglyMeasurable_const
    (Ck := ‖(fun _ _ => 1 : MetJ)‖) (fun _ => le_rfl)
    (RenewalGeometry.LpTendsto.const (memLp_const _))

end AssembledImprovement
end RenewalGeometry
