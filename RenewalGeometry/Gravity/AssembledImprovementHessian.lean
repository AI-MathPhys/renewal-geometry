/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.AssembledImprovementCriterion
import RenewalGeometry.Analysis.SobolevChainRule
import RenewalGeometry.Action.NativeDensitiesExact

/-!
# The assembled strong–weak improvement criterion: the Hessian term
  (`prop:improvement`, `eq:improvement-variation`; Einstein–Standard-Model action-closure manuscript)

`prop:improvement` concerns the assembled expression
`f_h Ein(g_h) + (g_h □_{g_h} - ∇^h∇^h) f_h` paired with a compactly supported test tensor `k`,
volume densities included.  For a `W^{2,p}` metric and `f ∈ L^{p'}` the Hessian term is not a
function; following the manuscript ("test the assembled expression and integrate both derivatives
onto the smooth test and metric-density coefficients") it is **defined by its adjoint**:

  `⟨(g□_g - ∇∇) f dV_g, k⟩ := ∫ f · Hess*_g(k)`,
  `Hess*_g(k) = ∂_b∂_a S^{ab} + ∂_l(S^{ab} Γ^l_{ab})`,  `S^{ab} = √|g| (g^{ab} tr_g k - k^{ab})`.

* Jet level.  `sDens (g, k) = S` and `gammaJ (g, ∂g) = Γ` are smooth on the nondegenerate set
  (`contDiffAt_sDens`, `contDiffAt_gammaJ`); `hessAdjJ g ∂g ∂²g k ∂k ∂²k` is the chain-rule
  expansion of `Hess*_g(k)` through the first and second Fréchet derivatives of `S` and of
  `Q_l = S^{ab}Γ^l_{ab}`, and it is **affine in `∂²g`** with coefficients continuous in the
  remaining jets on the nondegenerate set (`hessAdjJ_affine`, `continuousOn_hessCoef0`,
  `continuousOn_hessCoefL`).
* `hessian_consistency` (**integration-by-parts consistency**): for a smooth nondegenerate metric
  `g`, a smooth `f` and a smooth compactly supported test `k` on `ℝ⁴`,
  `∫ k^{μν}(g_{μν}□_g f - ∇_μ∇_ν f) √|g| = ∫ f · Hess*_g(k)` with `Hess*_g(k)` evaluated on the
  classical jets of `g` and `k` (two integrations by parts, compact support).
* `hessian_product_tendsto`: under the hypotheses of `prop:improvement` (`g_h → g` in `W^{1,∞}`
  with values in a compact subset of the nondegenerate set, `∂²g_h ⇀ ∂²g` weakly in `L^p`
  bounded, `f_h → f` in `L^{p'}`) the Hessian pairings converge.
* `improvement_tendsto` (**`prop:improvement`**): with `f_h = |H_h|²` and `H_h → H` in
  `L^{2p'}`, the full assembled pairing `∫ f_h ⟨k, Ein(g_h)⟩ √|g_h| + ∫ f_h Hess*_{g_h}(k)`
  converges to the same expression at the limit; `improved_variation_tendsto`: if moreover the
  minimal stress pairing converges and `ξ_h → ξ`, the full improved metric variation converges.

Rendering (as in `AssembledImprovementCriterion.lean`): the chart is a finite measure space `X`
for the convergence statement (fields given through their jets, the second jet being the weak
`∂²g` of a `W^{2,p}` metric, the test jets `(k, ∂k, ∂²k)` bounded measurable), and `ℝ⁴` with
Lebesgue measure for the integration-by-parts consistency (smooth metric nondegenerate on the
chart, test compactly supported).
-/

open MeasureTheory Filter Topology Set Finset
open scoped ENNReal NNReal ContDiff

noncomputable section

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

namespace RenewalGeometry
namespace AssembledImprovement

/-! ### Jet-level densities and their smoothness -/

section JetDensities

/-- The trace `tr_g k = g_{μν} k^{μν}`. -/
def trJ (G K : MetJ) : ℝ := ∑ μ, ∑ ν, G μ ν * K μ ν

/-- **The metric-density coefficient** `S^{ab} = √|g| (g^{ab} tr_g k - k^{ab})` of the
improvement. -/
def sDens (z : MetJ × MetJ) : MetJ :=
  fun a b => volJ z.1 * (ginvJ z.1 a b * trJ z.1 z.2 - z.2 a b)

/-- The Christoffel symbols `Γ^l_{ab}` of a metric jet `(g, ∂g)`. -/
def gammaJ (w : MetJ × D1) : D1 := christoffel (ginvJ w.1) w.2

/-- `Q_l = S^{ab} Γ^l_{ab}`. -/
def qDens (l : Fin 4) (w : MetJ × D1 × MetJ) : ℝ :=
  ∑ a, ∑ b, sDens (w.1, w.2.2) a b * gammaJ (w.1, w.2.1) l a b

theorem sDens_zero (G : MetJ) : sDens (G, 0) = 0 := by
  funext a b
  simp [sDens, trJ]

theorem qDens_zero (l : Fin 4) (G : MetJ) (dG : D1) : qDens l (G, dG, 0) = 0 := by
  simp [qDens, sDens_zero]

theorem isOpen_nondeg : IsOpen nondeg :=
  isOpen_ne.preimage (continuous_id.matrix_det)

theorem contDiffAt_ginvJ {G : MetJ} (hG : G ∈ nondeg) : ContDiffAt ℝ ∞ ginvJ G :=
  contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => NativeDensity.contDiffAt_invEntry i j hG

theorem contDiffAt_volJ {G : MetJ} (hG : G ∈ nondeg) : ContDiffAt ℝ ∞ volJ G := by
  have hdet : ContDiff ℝ ∞ fun G : MetJ => (Matrix.of G).det := NativeDensity.contDiff_det
  have h1 : ContDiffAt ℝ ∞ (fun G : MetJ => |(Matrix.of G).det|) G :=
    (contDiffAt_abs hG).comp G hdet.contDiffAt
  have h2 : |(Matrix.of G).det| ≠ 0 := abs_ne_zero.mpr hG
  exact (Real.contDiffAt_sqrt h2).comp G h1

theorem contDiffAt_sDens {z : MetJ × MetJ} (hz : z.1 ∈ nondeg) : ContDiffAt ℝ ∞ sDens z := by
  have hg : ContDiffAt ℝ ∞ (fun z : MetJ × MetJ => ginvJ z.1) z :=
    (contDiffAt_ginvJ hz).comp z contDiffAt_fst
  have hv : ContDiffAt ℝ ∞ (fun z : MetJ × MetJ => volJ z.1) z :=
    (contDiffAt_volJ hz).comp z contDiffAt_fst
  refine contDiffAt_pi.2 fun a => contDiffAt_pi.2 fun b => ?_
  have hga : ContDiffAt ℝ ∞ (fun z : MetJ × MetJ => ginvJ z.1 a b) z :=
    (contDiffAt_pi.1 (contDiffAt_pi.1 hg a) b)
  simp only [sDens, trJ]
  fun_prop

theorem contDiffAt_gammaJ {w : MetJ × D1} (hw : w.1 ∈ nondeg) : ContDiffAt ℝ ∞ gammaJ w := by
  have hg : ContDiffAt ℝ ∞ (fun w : MetJ × D1 => ginvJ w.1) w :=
    (contDiffAt_ginvJ hw).comp w contDiffAt_fst
  refine contDiffAt_pi.2 fun c => contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  have hge : ∀ e, ContDiffAt ℝ ∞ (fun w : MetJ × D1 => ginvJ w.1 c e) w := fun e =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hg c) e
  simp only [gammaJ, christoffel]
  fun_prop

theorem contDiffAt_qDens (l : Fin 4) {w : MetJ × D1 × MetJ} (hw : w.1 ∈ nondeg) :
    ContDiffAt ℝ ∞ (qDens l) w := by
  have hS : ContDiffAt ℝ ∞ (fun w : MetJ × D1 × MetJ => sDens (w.1, w.2.2)) w :=
    ContDiffAt.comp (g := sDens) (f := fun w : MetJ × D1 × MetJ => (w.1, w.2.2)) w
      (contDiffAt_sDens (z := (w.1, w.2.2)) hw) (by fun_prop)
  have hΓ : ContDiffAt ℝ ∞ (fun w : MetJ × D1 × MetJ => gammaJ (w.1, w.2.1)) w :=
    ContDiffAt.comp (g := gammaJ) (f := fun w : MetJ × D1 × MetJ => (w.1, w.2.1)) w
      (contDiffAt_gammaJ (w := (w.1, w.2.1)) hw) (by fun_prop)
  have hS' : ∀ a b, ContDiffAt ℝ ∞ (fun w : MetJ × D1 × MetJ => sDens (w.1, w.2.2) a b) w :=
    fun a b => contDiffAt_pi.1 (contDiffAt_pi.1 hS a) b
  have hΓ' : ∀ a b, ContDiffAt ℝ ∞ (fun w : MetJ × D1 × MetJ => gammaJ (w.1, w.2.1) l a b) w :=
    fun a b => contDiffAt_pi.1 (contDiffAt_pi.1 (contDiffAt_pi.1 hΓ l) a) b
  unfold qDens
  fun_prop

end JetDensities

/-! ### The adjoint Hessian jet and its affine structure -/

section AdjointJet

/-- **The adjoint Hessian density** `Hess*_g(k) = ∂_b∂_a S^{ab} + ∂_l(S^{ab}Γ^l_{ab})` written
through the jets `(g, ∂g, ∂²g)` of the metric and `(k, ∂k, ∂²k)` of the test, by the chain rule
for `S = sDens (g, k)` and `Q_l = qDens l (g, ∂g, k)`.  Jet conventions: `dG i = ∂_i g`,
`ddG c d = ∂_c ∂_d g`. -/
def hessAdjJ (G : MetJ) (dG : D1) (ddG : D2) (K : MetJ) (dK : D1) (ddK : D2) : ℝ :=
  (∑ a, ∑ b, (fderiv ℝ (fderiv ℝ sDens) (G, K) (dG b, dK b) (dG a, dK a) a b +
      fderiv ℝ sDens (G, K) (ddG b a, ddK b a) a b)) +
    ∑ l, fderiv ℝ (qDens l) (G, dG, K) (dG l, ddG l, dK l)

/-- The part of `Hess*_g(k)` linear in the second metric jet. -/
def hessLinFun (w : MetJ × D1 × MetJ) (ddG : D2) : ℝ :=
  (∑ a, ∑ b, fderiv ℝ sDens (w.1, w.2.2) (ddG b a, 0) a b) +
    ∑ l, fderiv ℝ (qDens l) w (0, ddG l, 0)

/-- **Affine structure of the adjoint Hessian density in `∂²g`.** -/
theorem hessAdjJ_affine (G : MetJ) (dG : D1) (ddG : D2) (K : MetJ) (dK : D1) (ddK : D2) :
    hessAdjJ G dG ddG K dK ddK = hessAdjJ G dG 0 K dK ddK + hessLinFun (G, dG, K) ddG := by
  have e1 : ∀ a b, ((ddG b a, ddK b a) : MetJ × MetJ) = ((0 : D2) b a, ddK b a) + (ddG b a, 0) :=
    fun a b => by simp
  have e2 : ∀ l, ((dG l, ddG l, dK l) : MetJ × D1 × MetJ) =
      (dG l, (0 : D2) l, dK l) + (0, ddG l, 0) := fun l => by simp
  simp only [hessAdjJ, hessLinFun, e1, e2, map_add, Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem hessLinFun_add (w : MetJ × D1 × MetJ) (X Y : D2) :
    hessLinFun w (X + Y) = hessLinFun w X + hessLinFun w Y := by
  have e1 : ∀ a b, ((X b a + Y b a, 0) : MetJ × MetJ) = (X b a, 0) + (Y b a, 0) :=
    fun a b => by simp
  have e2 : ∀ l, ((0, X l + Y l, 0) : MetJ × D1 × MetJ) = (0, X l, 0) + (0, Y l, 0) :=
    fun l => by simp
  simp only [hessLinFun, Pi.add_apply, e1, e2, map_add, Finset.sum_add_distrib]
  ring

theorem hessLinFun_smul (w : MetJ × D1 × MetJ) (r : ℝ) (X : D2) :
    hessLinFun w (r • X) = r * hessLinFun w X := by
  have e1 : ∀ a b, ((r • X b a, 0) : MetJ × MetJ) = r • (X b a, 0) := fun a b => by simp
  have e2 : ∀ l, ((0, r • X l, 0) : MetJ × D1 × MetJ) = r • (0, X l, 0) := fun l => by simp
  simp only [hessLinFun, Pi.smul_apply, e1, e2, map_smul, smul_eq_mul, Finset.mul_sum, mul_add]

/-- The linear part as a continuous linear functional of `∂²g`. -/
def hessLinL (w : MetJ × D1 × MetJ) : D2 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := hessLinFun w
      map_add' := hessLinFun_add w
      map_smul' := fun r X => by rw [hessLinFun_smul, smul_eq_mul, RingHom.id_apply] }

theorem hessLinL_apply (w : MetJ × D1 × MetJ) (X : D2) : hessLinL w X = hessLinFun w X := rfl

/-- The jets `(g, ∂g, k, ∂k, ∂²k)` entering the coefficients of `Hess*`. -/
abbrev HJ : Type := MetJ × D1 × MetJ × D1 × D2

/-- The nondegenerate jets. -/
def nondegH : Set HJ := Prod.fst ⁻¹' nondeg

theorem isOpen_nondegH : IsOpen nondegH := isOpen_nondeg.preimage continuous_fst

/-- The `∂²g`-free coefficient `c ↦ c · Hess*_g(k)|_{∂²g = 0}`. -/
def hessCoef0 (Z : HJ) : ℝ →L[ℝ] ℝ :=
  scalL ℝ (hessAdjJ Z.1 Z.2.1 0 Z.2.2.1 Z.2.2.2.1 Z.2.2.2.2)

/-- The second-derivative coefficient `c ↦ c · HessLin(g, ∂g; k)`. -/
def hessCoefL (Z : HJ) : ℝ →L[ℝ] D2 →L[ℝ] ℝ :=
  scalL (D2 →L[ℝ] ℝ) (hessLinL (Z.1, Z.2.1, Z.2.2.1))

theorem hess_split (Z : HJ) (ddG : D2) (c : ℝ) :
    c * hessAdjJ Z.1 Z.2.1 ddG Z.2.2.1 Z.2.2.2.1 Z.2.2.2.2 =
      hessCoef0 Z c + hessCoefL Z c ddG := by
  simp only [hessCoef0, hessCoefL, scalL_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    hessLinL_apply]
  rw [hessAdjJ_affine]
  ring

theorem continuousAt_fderiv_sDens {z : MetJ × MetJ} (hz : z.1 ∈ nondeg) :
    ContinuousAt (fderiv ℝ sDens) z :=
  (contDiffAt_sDens hz).continuousAt_fderiv (by simp)

theorem continuousAt_fderiv2_sDens {z : MetJ × MetJ} (hz : z.1 ∈ nondeg) :
    ContinuousAt (fderiv ℝ (fderiv ℝ sDens)) z :=
  ((contDiffAt_sDens hz).fderiv_right (m := ∞) (by simp)).continuousAt_fderiv (by simp)

theorem continuousAt_fderiv_qDens (l : Fin 4) {w : MetJ × D1 × MetJ} (hw : w.1 ∈ nondeg) :
    ContinuousAt (fderiv ℝ (qDens l)) w :=
  (contDiffAt_qDens l hw).continuousAt_fderiv (by simp)

theorem continuousAt_entry {Y : Type*} [TopologicalSpace Y] {F : Y → MetJ} {y : Y}
    (hF : ContinuousAt F y) (a b : Fin 4) : ContinuousAt (fun z => F z a b) y :=
  (continuous_apply b).continuousAt.comp ((continuous_apply a).continuousAt.comp hF)

theorem continuousAt_sum4 {Y : Type*} [TopologicalSpace Y] {F : Fin 4 → Y → ℝ} {y : Y}
    (hF : ∀ i, ContinuousAt (F i) y) : ContinuousAt (fun z => ∑ i, F i z) y :=
  tendsto_finset_sum _ fun i _ => hF i

theorem continuousAt_hessAdj0 {Z : HJ} (hZ : Z ∈ nondegH) :
    ContinuousAt (fun Z : HJ => hessAdjJ Z.1 Z.2.1 0 Z.2.2.1 Z.2.2.2.1 Z.2.2.2.2) Z := by
  have hS1 : ContinuousAt (fun Z : HJ => fderiv ℝ sDens (Z.1, Z.2.2.1)) Z :=
    ContinuousAt.comp (g := fderiv ℝ sDens) (continuousAt_fderiv_sDens (z := (Z.1, Z.2.2.1)) hZ)
      (by fun_prop)
  have hS2 : ContinuousAt (fun Z : HJ => fderiv ℝ (fderiv ℝ sDens) (Z.1, Z.2.2.1)) Z :=
    ContinuousAt.comp (g := fderiv ℝ (fderiv ℝ sDens))
      (continuousAt_fderiv2_sDens (z := (Z.1, Z.2.2.1)) hZ) (by fun_prop)
  have hQ : ∀ l, ContinuousAt (fun Z : HJ => fderiv ℝ (qDens l) (Z.1, Z.2.1, Z.2.2.1)) Z :=
    fun l => ContinuousAt.comp (g := fderiv ℝ (qDens l))
      (continuousAt_fderiv_qDens l (w := (Z.1, Z.2.1, Z.2.2.1)) hZ) (by fun_prop)
  unfold hessAdjJ
  refine ContinuousAt.add (continuousAt_sum4 fun a => continuousAt_sum4 fun b => ?_)
    (continuousAt_sum4 fun l => ?_)
  · refine ContinuousAt.add (continuousAt_entry ?_ a b) (continuousAt_entry ?_ a b)
    · exact (hS2.clm_apply (by fun_prop)).clm_apply (by fun_prop)
    · exact hS1.clm_apply (by fun_prop)
  · exact (hQ l).clm_apply (by fun_prop)

theorem continuousOn_hessCoef0 : ContinuousOn hessCoef0 nondegH := fun Z hZ =>
  ((scalL ℝ).continuous.continuousAt.comp (continuousAt_hessAdj0 hZ)).continuousWithinAt

theorem continuousOn_hessCoefL : ContinuousOn hessCoefL nondegH := by
  intro Z hZ
  refine ContinuousAt.continuousWithinAt ?_
  have hS1 : ContinuousAt (fun Z : HJ => fderiv ℝ sDens (Z.1, Z.2.2.1)) Z :=
    ContinuousAt.comp (g := fderiv ℝ sDens) (continuousAt_fderiv_sDens (z := (Z.1, Z.2.2.1)) hZ)
      (by fun_prop)
  have hQ : ∀ l, ContinuousAt (fun Z : HJ => fderiv ℝ (qDens l) (Z.1, Z.2.1, Z.2.2.1)) Z :=
    fun l => ContinuousAt.comp (g := fderiv ℝ (qDens l))
      (continuousAt_fderiv_qDens l (w := (Z.1, Z.2.1, Z.2.2.1)) hZ) (by fun_prop)
  have hL : ContinuousAt (fun Z : HJ => hessLinL (Z.1, Z.2.1, Z.2.2.1)) Z := by
    refine continuousAt_clm_apply.mpr fun X => ?_
    simp only [hessLinL_apply, hessLinFun]
    refine ContinuousAt.add (continuousAt_sum4 fun a => continuousAt_sum4 fun b => ?_)
      (continuousAt_sum4 fun l => ?_)
    · exact continuousAt_entry (hS1.clm_apply continuousAt_const) a b
    · exact (hQ l).clm_apply continuousAt_const
  unfold hessCoefL
  exact (scalL (D2 →L[ℝ] ℝ)).continuous.continuousAt.comp hL

end AdjointJet

/-! ### Convergence of the Hessian pairing -/

section HessianProduct

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

set_option maxHeartbeats 4000000 in
/-- **The Hessian part of the assembled improvement passes to the limit** (`prop:improvement`,
second product, volume densities included).  Under the hypotheses of `einstein_product_tendsto`
(`g_h → g` in `W^{1,∞}` with values in a compact subset of the nondegenerate set, `∂g_h` bounded,
`∂²g_h ⇀ ∂²g` weakly in `L^p` and bounded, `f_h → f` in `L^{p'}`, `p' < ∞`) and for every test
with bounded measurable jets `(k, ∂k, ∂²k)`, the adjoint Hessian pairings
`⟨(g_h□_{g_h} - ∇^h∇^h) f_h dV_{g_h}, k⟩ = ∫ f_h Hess*_{g_h}(k)` converge to
`⟨(g□_g - ∇∇) f dV_g, k⟩`. -/
theorem hessian_product_tendsto {p q : ℝ≥0∞} [ENNReal.HolderTriple q p 1] [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) {g : ℕ → X → MetJ} {g₀ : X → MetJ} {dg : ℕ → X → D1} {dg₀ : X → D1}
    {ddg : ℕ → X → D2} {ddg₀ : X → D2} {k : X → MetJ} {dk : X → D1} {ddk : X → D2}
    {Kg : Set MetJ} (hKg : IsCompact Kg) (hKgnd : Kg ⊆ nondeg)
    (hgK : ∀ n, ∀ᵐ x ∂μ, g n x ∈ Kg) (hg₀K : ∀ᵐ x ∂μ, g₀ x ∈ Kg)
    {D : ℝ} (hdgD : ∀ n, ∀ᵐ x ∂μ, ‖dg n x‖ ≤ D) (hdg₀D : ∀ᵐ x ∂μ, ‖dg₀ x‖ ≤ D)
    (hgm : ∀ n, AEStronglyMeasurable (g n) μ) (hdgm : ∀ n, AEStronglyMeasurable (dg n) μ)
    (hg : Tendsto (fun n => eLpNorm (g n - g₀) ⊤ μ) atTop (𝓝 0))
    (hdg : Tendsto (fun n => eLpNorm (dg n - dg₀) ⊤ μ) atTop (𝓝 0))
    (hddg : ∀ n, MemLp (ddg n) p μ) (hddg₀ : MemLp ddg₀ p μ) {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hddgB : ∀ n, eLpNorm (ddg n) p μ ≤ B) (hweak : WeakLpTendsto μ q ddg ddg₀)
    (hkm : AEStronglyMeasurable k μ) (hdkm : AEStronglyMeasurable dk μ)
    (hddkm : AEStronglyMeasurable ddk μ) {Ck : ℝ} (hk : ∀ x, ‖k x‖ ≤ Ck)
    (hdk : ∀ x, ‖dk x‖ ≤ Ck) (hddk : ∀ x, ‖ddk x‖ ≤ Ck)
    {f : ℕ → X → ℝ} {f₀ : X → ℝ} (hf : RenewalGeometry.LpTendsto μ q f f₀) :
    Tendsto (fun n => ∫ x, f n x * hessAdjJ (g n x) (dg n x) (ddg n x) (k x) (dk x) (ddk x) ∂μ)
      atTop (𝓝 (∫ x, f₀ x * hessAdjJ (g₀ x) (dg₀ x) (ddg₀ x) (k x) (dk x) (ddk x) ∂μ)) := by
  set KJ : Set HJ := Kg ×ˢ Metric.closedBall (0 : D1) D ×ˢ Metric.closedBall (0 : MetJ) Ck ×ˢ
    Metric.closedBall (0 : D1) Ck ×ˢ Metric.closedBall (0 : D2) Ck with hKJdef
  have hKJ : IsCompact KJ :=
    hKg.prod ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))))
  have hJK : ∀ n, ∀ᵐ x ∂μ, (g n x, dg n x, k x, dk x, ddk x) ∈ KJ := fun n => by
    filter_upwards [hgK n, hdgD n] with x h1 h2
    exact ⟨h1, mem_closedBall_zero_iff.mpr h2, mem_closedBall_zero_iff.mpr (hk x),
      mem_closedBall_zero_iff.mpr (hdk x), mem_closedBall_zero_iff.mpr (hddk x)⟩
  have hJ₀K : ∀ᵐ x ∂μ, (g₀ x, dg₀ x, k x, dk x, ddk x) ∈ KJ := by
    filter_upwards [hg₀K, hdg₀D] with x h1 h2
    exact ⟨h1, mem_closedBall_zero_iff.mpr h2, mem_closedBall_zero_iff.mpr (hk x),
      mem_closedBall_zero_iff.mpr (hdk x), mem_closedBall_zero_iff.mpr (hddk x)⟩
  have hJ : TendstoInMeasure μ (fun n x => (g n x, dg n x, k x, dk x, ddk x)) atTop
      (fun x => (g₀ x, dg₀ x, k x, dk x, ddk x)) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm_top ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hg.add hdg)
      (fun _ => bot_le) fun n => ?_
    calc eLpNorm ((fun x => (g n x, dg n x, k x, dk x, ddk x)) -
            fun x => (g₀ x, dg₀ x, k x, dk x, ddk x)) ⊤ μ ≤
          eLpNorm (fun x => ‖g n x - g₀ x‖ + ‖dg n x - dg₀ x‖) ⊤ μ :=
          eLpNorm_mono_real fun x => by
            simp only [Pi.sub_apply, Prod.mk_sub_mk, sub_self]
            refine norm_prod_le_iff.mpr ⟨le_add_of_nonneg_right (norm_nonneg _),
              norm_prod_le_iff.mpr ⟨le_add_of_nonneg_left (norm_nonneg _), ?_⟩⟩
            simpa using add_nonneg (norm_nonneg (g n x - g₀ x)) (norm_nonneg (dg n x - dg₀ x))
      _ ≤ eLpNorm (fun x => ‖g n x - g₀ x‖) ⊤ μ + eLpNorm (fun x => ‖dg n x - dg₀ x‖) ⊤ μ := by
          simp only [eLpNorm_exponent_top]
          exact eLpNormEssSup_add_le
      _ = _ := by rw [eLpNorm_norm, eLpNorm_norm]; rfl
  have hKJS : ∀ z ∈ KJ, z ∈ nondegH := fun z hz => hKgnd hz.1
  have hJm : ∀ n, AEMeasurable (fun x => (g n x, dg n x, k x, dk x, ddk x)) μ := fun n =>
    (hgm n).aemeasurable.prodMk ((hdgm n).aemeasurable.prodMk (hkm.aemeasurable.prodMk
      (hdkm.aemeasurable.prodMk hddkm.aemeasurable)))
  have hJS : ∀ n, ∀ᵐ x ∂μ, (g n x, dg n x, k x, dk x, ddk x) ∈ nondegH := fun n =>
    (hJK n).mono fun x hx => hKJS _ hx
  have hΦ1m : ∀ n, AEStronglyMeasurable
      (fun x => hessCoef0 (g n x, dg n x, k x, dk x, ddk x)) μ := fun n =>
    FirstVariationCalculus.aestronglyMeasurable_comp_of_continuousOn' (Φ := hessCoef0)
      isOpen_nondegH continuousOn_hessCoef0 (hJm n) (hJS n)
  have hΦ2m : ∀ n, AEStronglyMeasurable
      (fun x => hessCoefL (g n x, dg n x, k x, dk x, ddk x)) μ := fun n =>
    FirstVariationCalculus.aestronglyMeasurable_comp_of_continuousOn' (Φ := hessCoefL)
      isOpen_nondegH continuousOn_hessCoefL (hJm n) (hJS n)
  have P1 := FirstVariationCalculus.tendsto_coeff_apply hKJ (continuousOn_hessCoef0.mono hKJS)
    hJK hJ₀K hJ hΦ1m hq hf
  have P1L := P1.mono one_ne_zero (Fact.out : (1 : ℝ≥0∞) ≤ q)
  have P2 := FirstVariationCalculus.tendsto_coeff_apply hKJ (continuousOn_hessCoefL.mono hKJS)
    hJK hJ₀K hJ hΦ2m hq hf
  have P2' := tendsto_integral_clm_strong_weak (p := p) (q := q) P2 hddg hddg₀ hB hddgB hweak
  have e1 : ∀ n, ∫ x, f n x * hessAdjJ (g n x) (dg n x) (ddg n x) (k x) (dk x) (ddk x) ∂μ =
      ∫ x, hessCoef0 (g n x, dg n x, k x, dk x, ddk x) (f n x) ∂μ +
        ∫ x, hessCoefL (g n x, dg n x, k x, dk x, ddk x) (f n x) (ddg n x) ∂μ := fun n => by
    rw [← integral_add (memLp_one_iff_integrable.mp (P1L.memLp n))
      (integrable_clm_apply_of_memLp (P2.memLp n) (hddg n))]
    exact integral_congr_ae (Eventually.of_forall fun x =>
      hess_split (g n x, dg n x, k x, dk x, ddk x) (ddg n x) (f n x))
  have e0 : ∫ x, f₀ x * hessAdjJ (g₀ x) (dg₀ x) (ddg₀ x) (k x) (dk x) (ddk x) ∂μ =
      ∫ x, hessCoef0 (g₀ x, dg₀ x, k x, dk x, ddk x) (f₀ x) ∂μ +
        ∫ x, hessCoefL (g₀ x, dg₀ x, k x, dk x, ddk x) (f₀ x) (ddg₀ x) ∂μ := by
    rw [← integral_add (memLp_one_iff_integrable.mp P1L.memLp_lim)
      (integrable_clm_apply_of_memLp P2.memLp_lim hddg₀)]
    exact integral_congr_ae (Eventually.of_forall fun x =>
      hess_split (g₀ x, dg₀ x, k x, dk x, ddk x) (ddg₀ x) (f₀ x))
  rw [e0]
  exact (P1L.tendsto_integral.add P2').congr fun n => (e1 n).symm

/-- `‖H_h‖² → ‖H‖²` in `L^{p'}` when `H_h → H` in `L^{2p'}` (Hölder with `1/(2p') + 1/(2p') = 1/p'`). -/
theorem normSq_lpTendsto {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {H : ℕ → X → V} {H₀ : X → V}
    (hH : RenewalGeometry.LpTendsto μ (2 * q) H H₀) :
    RenewalGeometry.LpTendsto μ q (fun n x => ‖H n x‖ ^ 2) (fun x => ‖H₀ x‖ ^ 2) := by
  have : Fact (1 ≤ 2 * q) := ⟨le_trans (Fact.out : (1 : ℝ≥0∞) ≤ q) (by
    calc q = 1 * q := (one_mul q).symm
      _ ≤ 2 * q := by gcongr; norm_num)⟩
  have : ENNReal.HolderTriple (2 * q) (2 * q) q := ⟨by
    rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]⟩
  have h := RenewalGeometry.LpTendsto.bilin (p := 2 * q) (q := 2 * q) (r := q)
    (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) hH hH
  refine h.congr (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · show innerSL ℝ (H n x) (H n x) = ‖H n x‖ ^ 2
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  · show innerSL ℝ (H₀ x) (H₀ x) = ‖H₀ x‖ ^ 2
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]

end HessianProduct

/-! ### `prop:improvement` -/

section Improvement

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

set_option maxHeartbeats 4000000 in
/-- **`prop:improvement`** (the assembled strong–weak improvement criterion).  Let `1 < p < ∞`
with dual exponent `p' = q < ∞`; let `g_h → g` in `W^{1,∞}` (`(g_h, ∂g_h) → (g, ∂g)` in `L^∞`,
values in a compact subset of the nondegenerate set: uniform inverse bounds), `∂g_h` bounded and
`g_h ⇀ g` weakly in `W^{2,p}` (`∂²g_h ⇀ ∂²g` weakly in `L^p`, bounded), and `H_h → H` in
`L^{2p'}`; put `f = |H|²`.  Then for every test tensor with bounded measurable jets `(k, ∂k, ∂²k)`
the assembled improvement pairs convergently, volume densities included:
`∫ f_h ⟨k, Ein(g_h)⟩ √|g_h| + ⟨(g_h□_{g_h} - ∇^h∇^h) f_h dV_{g_h}, k⟩ →
 ∫ f ⟨k, Ein(g)⟩ √|g| + ⟨(g□_g - ∇∇) f dV_g, k⟩`,
the Hessian pairing being the adjoint pairing `∫ f Hess*_g(k)` (consistent with the classical one
by `hessian_consistency`). -/
theorem improvement_tendsto {p q : ℝ≥0∞} [ENNReal.HolderTriple q p 1] [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) {g : ℕ → X → MetJ} {g₀ : X → MetJ} {dg : ℕ → X → D1} {dg₀ : X → D1}
    {ddg : ℕ → X → D2} {ddg₀ : X → D2} {k : X → MetJ} {dk : X → D1} {ddk : X → D2}
    {Kg : Set MetJ} (hKg : IsCompact Kg) (hKgnd : Kg ⊆ nondeg)
    (hgK : ∀ n, ∀ᵐ x ∂μ, g n x ∈ Kg) (hg₀K : ∀ᵐ x ∂μ, g₀ x ∈ Kg)
    {D : ℝ} (hdgD : ∀ n, ∀ᵐ x ∂μ, ‖dg n x‖ ≤ D) (hdg₀D : ∀ᵐ x ∂μ, ‖dg₀ x‖ ≤ D)
    (hgm : ∀ n, AEStronglyMeasurable (g n) μ) (hdgm : ∀ n, AEStronglyMeasurable (dg n) μ)
    (hg : Tendsto (fun n => eLpNorm (g n - g₀) ⊤ μ) atTop (𝓝 0))
    (hdg : Tendsto (fun n => eLpNorm (dg n - dg₀) ⊤ μ) atTop (𝓝 0))
    (hddg : ∀ n, MemLp (ddg n) p μ) (hddg₀ : MemLp ddg₀ p μ) {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hddgB : ∀ n, eLpNorm (ddg n) p μ ≤ B) (hweak : WeakLpTendsto μ q ddg ddg₀)
    (hkm : AEStronglyMeasurable k μ) (hdkm : AEStronglyMeasurable dk μ)
    (hddkm : AEStronglyMeasurable ddk μ) {Ck : ℝ} (hk : ∀ x, ‖k x‖ ≤ Ck)
    (hdk : ∀ x, ‖dk x‖ ≤ Ck) (hddk : ∀ x, ‖ddk x‖ ≤ Ck)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {H : ℕ → X → V} {H₀ : X → V}
    (hH : RenewalGeometry.LpTendsto μ (2 * q) H H₀) :
    Tendsto (fun n => ∫ x, ‖H n x‖ ^ 2 * einTest (g n x) (dg n x) (ddg n x) (k x) ∂μ +
        ∫ x, ‖H n x‖ ^ 2 * hessAdjJ (g n x) (dg n x) (ddg n x) (k x) (dk x) (ddk x) ∂μ) atTop
      (𝓝 (∫ x, ‖H₀ x‖ ^ 2 * einTest (g₀ x) (dg₀ x) (ddg₀ x) (k x) ∂μ +
        ∫ x, ‖H₀ x‖ ^ 2 * hessAdjJ (g₀ x) (dg₀ x) (ddg₀ x) (k x) (dk x) (ddk x) ∂μ)) := by
  have hf := normSq_lpTendsto hH
  exact (einstein_product_tendsto hq hKg hKgnd hgK hg₀K hdgD hdg₀D hgm hdgm hg hdg hddg hddg₀ hB
    hddgB hweak hkm hk hf).add
    (hessian_product_tendsto hq hKg hKgnd hgK hg₀K hdgD hdg₀D hgm hdgm hg hdg hddg hddg₀ hB
      hddgB hweak hkm hdkm hddkm hk hdk hddk hf)

/-- **`prop:improvement`, closing sentence**: if moreover the minimal stress pairings converge,
`m_h → m`, and `ξ_h → ξ`, the full improved metric variation
`m_h + ξ_h ⟨f_h Ein(g_h) dV + (g_h□ - ∇∇) f_h dV, k⟩` (`eq:improvement-variation`) converges. -/
theorem improved_variation_tendsto {m : ℕ → ℝ} {m₀ : ℝ} (hm : Tendsto m atTop (𝓝 m₀))
    {ξ : ℕ → ℝ} {ξ₀ : ℝ} (hξ : Tendsto ξ atTop (𝓝 ξ₀)) {I : ℕ → ℝ} {I₀ : ℝ}
    (hI : Tendsto I atTop (𝓝 I₀)) :
    Tendsto (fun n => m n + ξ n * I n) atTop (𝓝 (m₀ + ξ₀ * I₀)) :=
  hm.add (hξ.mul hI)

end Improvement

/-! ### Integration-by-parts consistency of the adjoint Hessian pairing -/

section Consistency

open SobolevOpen (pd)

/-- The chart `ℝ⁴`. -/
abbrev X4 : Type := Fin 4 → ℝ

/-- The classical first jet `∂_i g` of a metric field. -/
def dgF (g : X4 → MetJ) (x : X4) : D1 := fun i => pd g i x

/-- The classical second jet `∂_c ∂_d g` of a metric field. -/
def ddgF (g : X4 → MetJ) (x : X4) : D2 := fun c d => pd (fun y => pd g d y) c x

/-- The classical covariant Hessian `∇_a∇_b f = ∂_a∂_b f - Γ^l_{ab} ∂_l f`. -/
def covHessF (g : X4 → MetJ) (f : X4 → ℝ) (x : X4) (a b : Fin 4) : ℝ :=
  pd (fun y => pd f b y) a x - ∑ l, gammaJ (g x, dgF g x) l a b * pd f l x

/-- The classical wave operator `□_g f = g^{ab} ∇_a∇_b f`. -/
def boxF (g : X4 → MetJ) (f : X4 → ℝ) (x : X4) : ℝ :=
  ∑ a, ∑ b, ginvJ (g x) a b * covHessF g f x a b

/-! #### Calculus lemmas -/

theorem pd_proj {β : Type*} [Fintype β] {E : β → Type*} [∀ b, NormedAddCommGroup (E b)]
    [∀ b, NormedSpace ℝ (E b)] {F : X4 → ∀ b, E b} {x : X4} (hF : DifferentiableAt ℝ F x)
    (b : β) (i : Fin 4) : pd (fun y => F y b) i x = pd F i x b := by
  unfold pd
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := E) b).hasFDerivAt.comp x
    hF.hasFDerivAt).fderiv
  rw [show (fun y => F y b) = (ContinuousLinearMap.proj (R := ℝ) (φ := E) b) ∘ F from rfl, h]
  rfl

theorem pd_entry {F : X4 → MetJ} {x : X4} (hF : DifferentiableAt ℝ F x) (a b : Fin 4)
    (i : Fin 4) : pd (fun y => F y a b) i x = pd F i x a b := by
  have hFa : DifferentiableAt ℝ (fun y => F y a) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → ℝ) a).differentiableAt.comp
      x hF
  rw [pd_proj hFa b i, pd_proj hF a i]

theorem pd_prod {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] {F : X4 → V} {G : X4 → W} {x : X4} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (i : Fin 4) :
    pd (fun y => (F y, G y)) i x = (pd F i x, pd G i x) := by
  unfold pd
  rw [hF.fderiv_prodMk hG]
  rfl

theorem contDiff_pd {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : X4 → V}
    (hF : ContDiff ℝ ∞ F) (i : Fin 4) : ContDiff ℝ ∞ fun y => pd F i y := by
  unfold pd
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem pd_comp_eq {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {U : V → W} {Z : X4 → V} {y : X4}
    (hU : DifferentiableAt ℝ U (Z y)) (hZ : DifferentiableAt ℝ Z y) (i : Fin 4) :
    pd (fun y => U (Z y)) i y = fderiv ℝ U (Z y) (pd Z i y) := by
  unfold pd
  rw [show (fun y => U (Z y)) = U ∘ Z from rfl, fderiv_comp y hU hZ]
  rfl

/-- **Second-order chain rule** for partial derivatives. -/
theorem pd_pd_comp {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {U : V → W} {Z : X4 → V}
    (hU : ∀ y, ContDiffAt ℝ ∞ U (Z y)) (hZ : ContDiff ℝ ∞ Z) (i j : Fin 4) (x : X4) :
    pd (fun y => pd (fun y => U (Z y)) i y) j x =
      fderiv ℝ (fderiv ℝ U) (Z x) (pd Z j x) (pd Z i x) +
        fderiv ℝ U (Z x) (pd (fun y => pd Z i y) j x) := by
  have hZd : ∀ y, DifferentiableAt ℝ Z y := fun y => hZ.differentiable (by simp) y
  have h1 : (fun y => pd (fun y => U (Z y)) i y) = fun y => fderiv ℝ U (Z y) (pd Z i y) :=
    funext fun y => pd_comp_eq ((hU y).differentiableAt (by simp)) (hZd y) i
  have hc : DifferentiableAt ℝ (fun y => fderiv ℝ U (Z y)) x :=
    (((hU x).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).comp x (hZd x)
  have hu : DifferentiableAt ℝ (fun y => pd Z i y) x :=
    (contDiff_pd hZ i).differentiable (by simp) x
  have hcd : fderiv ℝ (fun y => fderiv ℝ U (Z y)) x (Pi.single j 1) =
      fderiv ℝ (fderiv ℝ U) (Z x) (pd Z j x) := by
    rw [show (fun y => fderiv ℝ U (Z y)) = fderiv ℝ U ∘ Z from rfl,
      fderiv_comp x (((hU x).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)) (hZd x)]
    rfl
  rw [h1]
  show fderiv ℝ (fun y => fderiv ℝ U (Z y) (pd Z i y)) x (Pi.single j 1) = _
  rw [fderiv_clm_apply hc hu]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [hcd, add_comm]
  rfl

/-! #### The coefficient fields -/

variable {g k : X4 → MetJ} {f : X4 → ℝ}

theorem contDiff_dgF (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (dgF g) :=
  contDiff_pi.2 fun i => contDiff_pd hg i

theorem contDiff_sDens_comp (hg : ContDiff ℝ ∞ g) (hnd : ∀ x, g x ∈ nondeg)
    (hk : ContDiff ℝ ∞ k) : ContDiff ℝ ∞ fun y => sDens (g y, k y) :=
  contDiff_iff_contDiffAt.2 fun y =>
    ContDiffAt.comp (g := sDens) y (contDiffAt_sDens (z := (g y, k y)) (hnd y))
      (hg.prodMk hk).contDiffAt

theorem contDiff_qDens_comp (hg : ContDiff ℝ ∞ g) (hnd : ∀ x, g x ∈ nondeg)
    (hk : ContDiff ℝ ∞ k) (l : Fin 4) : ContDiff ℝ ∞ fun y => qDens l (g y, dgF g y, k y) :=
  contDiff_iff_contDiffAt.2 fun y =>
    ContDiffAt.comp (g := qDens l) y (contDiffAt_qDens l (w := (g y, dgF g y, k y)) (hnd y))
      (hg.prodMk ((contDiff_dgF hg).prodMk hk)).contDiffAt

theorem contDiff_sDens_entry (hg : ContDiff ℝ ∞ g) (hnd : ∀ x, g x ∈ nondeg)
    (hk : ContDiff ℝ ∞ k) (a b : Fin 4) : ContDiff ℝ ∞ fun y => sDens (g y, k y) a b :=
  (contDiff_apply_apply ℝ ℝ a b).comp (contDiff_sDens_comp hg hnd hk)

theorem hasCompactSupport_sDens_entry (hkc : HasCompactSupport k) (a b : Fin 4) :
    HasCompactSupport fun y => sDens (g y, k y) a b := by
  refine hkc.mono' fun y hy => subset_tsupport _ ?_
  intro hk0
  apply hy
  simp only [hk0, sDens_zero, Pi.zero_apply]

theorem hasCompactSupport_qDens (hkc : HasCompactSupport k) (l : Fin 4) :
    HasCompactSupport fun y => qDens l (g y, dgF g y, k y) := by
  refine hkc.mono' fun y hy => subset_tsupport _ ?_
  intro hk0
  apply hy
  simp only [hk0, qDens_zero]

theorem hasCompactSupport_pd {φ : X4 → ℝ} (hφ : HasCompactSupport φ) (i : Fin 4) :
    HasCompactSupport fun y => pd φ i y := by
  unfold pd
  exact (hφ.fderiv (𝕜 := ℝ)).mono' fun y hy => subset_tsupport _ fun h0 => hy (by simp [h0])

/-! #### Pointwise identities -/

/-- `k^{μν}(g_{μν} g^{ab} - δ^a_μ δ^b_ν) C_{ab} √|g| = S^{ab} C_{ab}`. -/
theorem trace_form_eq (G K C : MetJ) :
    ∑ μ, ∑ ν, K μ ν * (G μ ν * (∑ a, ∑ b, ginvJ G a b * C a b) - C μ ν) * volJ G =
      ∑ a, ∑ b, sDens (G, K) a b * C a b := by
  set S := ∑ a, ∑ b, ginvJ G a b * C a b
  set v := volJ G
  have hL : ∀ μ ν, K μ ν * (G μ ν * S - C μ ν) * v = G μ ν * K μ ν * (v * S) - v * K μ ν * C μ ν :=
    fun μ ν => by ring
  have hR : ∀ a b, sDens (G, K) a b * C a b =
      ginvJ G a b * C a b * (v * trJ G K) - v * K a b * C a b := fun a b => by
    simp only [sDens]; ring
  simp only [hL, hR, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [trJ]
  ring

end Consistency

section ConsistencyMain

open SobolevOpen (pd)

theorem sum3_comm (F : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ l, F a b l = ∑ l, ∑ a, ∑ b, F a b l :=
  calc ∑ a, ∑ b, ∑ l, F a b l = ∑ a, ∑ l, ∑ b, F a b l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, F a b l := Finset.sum_comm

variable {g k : X4 → MetJ} {f : X4 → ℝ}

/-- The chain-rule identification of the second derivatives of `S = sDens (g, k)`. -/
theorem pd_pd_sDens_entry (hg : ContDiff ℝ ∞ g) (hnd : ∀ x, g x ∈ nondeg)
    (hk : ContDiff ℝ ∞ k) (a b : Fin 4) (x : X4) :
    pd (fun y => pd (fun y => sDens (g y, k y) a b) a y) b x =
      (fderiv ℝ (fderiv ℝ sDens) (g x, k x) (dgF g x b, dgF k x b) (dgF g x a, dgF k x a) +
        fderiv ℝ sDens (g x, k x) (ddgF g x b a, ddgF k x b a)) a b := by
  have hZ : ContDiff ℝ ∞ fun y => (g y, k y) := hg.prodMk hk
  have hSZ := contDiff_sDens_comp hg hnd hk
  have hd : ∀ {F : X4 → MetJ}, ContDiff ℝ ∞ F → ∀ y, DifferentiableAt ℝ F y :=
    fun hF y => hF.differentiable (by simp) y
  have e1 : (fun y => pd (fun y => sDens (g y, k y) a b) a y) =
      fun y => pd (fun y => sDens (g y, k y)) a y a b :=
    funext fun y => pd_entry (hd hSZ y) a b a
  rw [e1, pd_entry (hd (contDiff_pd hSZ a) x) a b b]
  have hU : ∀ y, ContDiffAt ℝ ∞ sDens ((fun y => (g y, k y)) y) := fun y =>
    contDiffAt_sDens (z := (g y, k y)) (hnd y)
  rw [pd_pd_comp (U := sDens) (Z := fun y => (g y, k y)) hU hZ a b x]
  have hgd : ∀ y, DifferentiableAt ℝ g y := hd hg
  have hkd : ∀ y, DifferentiableAt ℝ k y := hd hk
  have e2 : (fun y => pd (fun y => (g y, k y)) a y) = fun y => (pd g a y, pd k a y) :=
    funext fun y => pd_prod (hgd y) (hkd y) a
  rw [e2, pd_prod (hgd x) (hkd x) b, pd_prod (hgd x) (hkd x) a,
    pd_prod ((contDiff_pd hg a).differentiable (by simp) x)
      ((contDiff_pd hk a).differentiable (by simp) x) b]
  rfl

/-- The chain-rule identification of `∂_l Q_l`, `Q_l = qDens l (g, ∂g, k)`. -/
theorem pd_qDens (hg : ContDiff ℝ ∞ g) (hnd : ∀ x, g x ∈ nondeg) (hk : ContDiff ℝ ∞ k)
    (l : Fin 4) (x : X4) :
    pd (fun y => qDens l (g y, dgF g y, k y)) l x =
      fderiv ℝ (qDens l) (g x, dgF g x, k x) (dgF g x l, ddgF g x l, dgF k x l) := by
  have hd : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : X4 → V},
      ContDiff ℝ ∞ F → ∀ y, DifferentiableAt ℝ F y :=
    fun hF y => hF.differentiable (by simp) y
  have hW : DifferentiableAt ℝ (fun y => (g y, dgF g y, k y)) x :=
    hd (hg.prodMk ((contDiff_dgF hg).prodMk hk)) x
  rw [pd_comp_eq (U := qDens l) (Z := fun y => (g y, dgF g y, k y))
    ((contDiffAt_qDens l (w := (g x, dgF g x, k x)) (hnd x)).differentiableAt (by simp)) hW l]
  rw [pd_prod (hd hg x) ((hd (contDiff_dgF hg) x).prodMk (hd hk x)) l,
    pd_prod (hd (contDiff_dgF hg) x) (hd hk x) l]
  have hdd : pd (dgF g) l x = ddgF g x l := by
    funext i
    rw [← pd_proj (hd (contDiff_dgF hg) x) i l]
    rfl
  rw [hdd]
  rfl

/-- **Integration-by-parts consistency of the adjoint Hessian pairing** (`eq:improvement-variation`,
`prop:improvement`).  For a smooth metric `g` nondegenerate on the chart `ℝ⁴`, a smooth function
`f` and a smooth compactly supported symmetric-or-not test tensor `k`,
`∫ k^{μν} (g_{μν} □_g f - ∇_μ∇_ν f) √|g| = ∫ f · Hess*_g(k)`, where `Hess*_g(k)` is `hessAdjJ`
evaluated on the classical jets of `g` and `k`. -/
theorem hessian_consistency (hg : ContDiff ℝ ∞ g) (hnd : ∀ x, g x ∈ nondeg)
    (hf : ContDiff ℝ ∞ f) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    ∫ x, ∑ μ, ∑ ν, k x μ ν * (g x μ ν * boxF g f x - covHessF g f x μ ν) * volJ (g x) =
      ∫ x, f x * hessAdjJ (g x) (dgF g x) (ddgF g x) (k x) (dgF k x) (ddgF k x) := by
  set s : Fin 4 → Fin 4 → X4 → ℝ := fun a b y => sDens (g y, k y) a b with hs
  set Q : Fin 4 → X4 → ℝ := fun l y => qDens l (g y, dgF g y, k y) with hQ
  have hsC : ∀ a b, ContDiff ℝ ∞ (s a b) := fun a b => contDiff_sDens_entry hg hnd hk a b
  have hsK : ∀ a b, HasCompactSupport (s a b) := fun a b => hasCompactSupport_sDens_entry hkc a b
  have hQC : ∀ l, ContDiff ℝ ∞ (Q l) := fun l => contDiff_qDens_comp hg hnd hk l
  have hQK : ∀ l, HasCompactSupport (Q l) := fun l => hasCompactSupport_qDens hkc l
  have hfC : ∀ i, ContDiff ℝ ∞ fun y => pd f i y := fun i => contDiff_pd hf i
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  -- pointwise form of the left integrand
  have hpt : ∀ x, ∑ μ, ∑ ν, k x μ ν * (g x μ ν * boxF g f x - covHessF g f x μ ν) * volJ (g x) =
      (∑ a, ∑ b, s a b x * pd (fun y => pd f b y) a x) - ∑ l, Q l x * pd f l x := by
    intro x
    rw [boxF, trace_form_eq]
    simp only [covHessF, mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp only [hQ, qDens, Finset.mul_sum, Finset.sum_mul]
    rw [sum3_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by ring
  -- integrability
  have hint1 : ∀ a b, Integrable fun x => s a b x * pd (fun y => pd f b y) a x := fun a b =>
    ((hsC a b).continuous.mul (contDiff_pd (hfC b) a).continuous).integrable_of_hasCompactSupport
      (hsK a b).mul_right
  have hint2 : ∀ l, Integrable fun x => Q l x * pd f l x := fun l =>
    ((hQC l).continuous.mul (hfC l).continuous).integrable_of_hasCompactSupport (hQK l).mul_right
  have hint3 : ∀ a b, Integrable fun x => pd (fun y => pd (s a b) a y) b x * f x := fun a b =>
    ((contDiff_pd (contDiff_pd (hsC a b) a) b).continuous.mul hf.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_pd (hasCompactSupport_pd (hsK a b) a) b).mul_right
  have hint4 : ∀ l, Integrable fun x => pd (Q l) l x * f x := fun l =>
    ((contDiff_pd (hQC l) l).continuous.mul hf.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_pd (hQK l) l).mul_right
  -- integration by parts
  have hibp1 : ∀ a b, ∫ x, s a b x * pd (fun y => pd f b y) a x =
      ∫ x, pd (fun y => pd (s a b) a y) b x * f x := by
    intro a b
    have h1 := SobolevOpen.integral_pd_mul_eq_neg_real ((hfC b).of_le (by simp)) (hsC a b)
      (hsK a b) a
    have h2 := SobolevOpen.integral_pd_mul_eq_neg_real hf1 (contDiff_pd (hsC a b) a)
      (hasCompactSupport_pd (hsK a b) a) b
    linarith
  have hibp2 : ∀ l, ∫ x, Q l x * pd f l x = -∫ x, pd (Q l) l x * f x := by
    intro l
    have h1 := SobolevOpen.integral_pd_mul_eq_neg_real hf1 (hQC l) (hQK l) l
    linarith
  -- the right integrand
  have hrt : ∀ x, f x * hessAdjJ (g x) (dgF g x) (ddgF g x) (k x) (dgF k x) (ddgF k x) =
      (∑ a, ∑ b, pd (fun y => pd (s a b) a y) b x * f x) + ∑ l, pd (Q l) l x * f x := by
    intro x
    simp only [hs, hQ, pd_pd_sDens_entry hg hnd hk, pd_qDens hg hnd hk, hessAdjJ, mul_add,
      Finset.mul_sum, Pi.add_apply]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    · refine Finset.sum_congr rfl fun l _ => by ring
  simp only [hpt, hrt]
  rw [integral_sub (integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hint1 a b)
      (integrable_finset_sum _ fun l _ => hint2 l),
    integral_add (integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hint3 a b)
      (integrable_finset_sum _ fun l _ => hint4 l),
    integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hint1 a b,
    integral_finset_sum _ fun l _ => hint2 l,
    integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hint3 a b,
    integral_finset_sum _ fun l _ => hint4 l]
  simp only [fun a => integral_finset_sum _ fun b (_ : b ∈ Finset.univ) => hint1 a b,
    fun a => integral_finset_sum _ fun b (_ : b ∈ Finset.univ) => hint3 a b, hibp1, hibp2,
    Finset.sum_neg_distrib, sub_neg_eq_add]

end ConsistencyMain

/-! ### Non-vacuity -/

/-- The hypotheses of `hessian_consistency` are satisfiable (Minkowski metric on the chart, zero
function and zero test). -/
example : ∫ x, ∑ μ, ∑ ν, (0 : MetJ) μ ν * ((fun _ : X4 => minkJ) x μ ν *
      boxF (fun _ => minkJ) (fun _ => (0 : ℝ)) x -
      covHessF (fun _ => minkJ) (fun _ => (0 : ℝ)) x μ ν) * volJ minkJ =
    ∫ x, (0 : ℝ) * hessAdjJ minkJ (dgF (fun _ => minkJ) x) (ddgF (fun _ => minkJ) x) 0
      (dgF (fun _ => (0 : MetJ)) x) (ddgF (fun _ => (0 : MetJ)) x) :=
  hessian_consistency (g := fun _ => minkJ) (k := fun _ => 0) (f := fun _ => 0) contDiff_const
    (fun _ => minkJ_nondeg) contDiff_const contDiff_const HasCompactSupport.zero

/-- **Non-vacuity of `improvement_tendsto`**: constant Minkowski jets, zero second derivatives,
constant Higgs field and unit test jets on a one-point chart (`p = p' = 2`). -/
example : Tendsto (fun n : ℕ =>
    ∫ x, ‖(fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) n x‖ ^ 2 * einTest minkJ 0 0 (fun _ _ => 1)
      ∂(Measure.dirac ()) +
    ∫ x, ‖(fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) n x‖ ^ 2 *
      hessAdjJ minkJ 0 0 (fun _ _ => 1) 0 0 ∂(Measure.dirac ())) atTop
    (𝓝 (∫ x, ‖(fun (_ : Unit) => (1 : ℝ)) x‖ ^ 2 * einTest minkJ 0 0 (fun _ _ => 1)
      ∂(Measure.dirac ()) +
    ∫ x, ‖(fun (_ : Unit) => (1 : ℝ)) x‖ ^ 2 *
      hessAdjJ minkJ 0 0 (fun _ _ => 1) 0 0 ∂(Measure.dirac ()))) := by
  have : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  exact improvement_tendsto (p := 2) (q := 2) (by norm_num) (Kg := {minkJ})
    (g := fun _ _ => minkJ) (g₀ := fun _ => minkJ) (dg := fun _ _ => 0) (dg₀ := fun _ => 0)
    (ddg := fun _ _ => 0) (ddg₀ := fun _ => 0) (k := fun _ => fun _ _ => 1) (dk := fun _ => 0)
    (ddk := fun _ => 0)
    isCompact_singleton (by simpa using minkJ_nondeg) (fun _ => Eventually.of_forall fun _ => rfl)
    (Eventually.of_forall fun _ => rfl) (D := 0) (fun _ => Eventually.of_forall fun _ => by simp)
    (Eventually.of_forall fun _ => by simp) (fun _ => aestronglyMeasurable_const)
    (fun _ => aestronglyMeasurable_const) (by simp) (by simp) (fun _ => memLp_const _)
    (memLp_const _) (B := eLpNorm (fun _ : Unit => (0 : D2)) 2 (Measure.dirac ()))
    (by simp) (fun _ => le_rfl) (fun _ _ _ => tendsto_const_nhds) aestronglyMeasurable_const
    aestronglyMeasurable_const aestronglyMeasurable_const
    (Ck := ‖(fun _ _ => 1 : MetJ)‖) (fun _ => le_rfl) (fun _ => by simp) (fun _ => by simp)
    (RenewalGeometry.LpTendsto.const (memLp_const _))

end AssembledImprovement
end RenewalGeometry
