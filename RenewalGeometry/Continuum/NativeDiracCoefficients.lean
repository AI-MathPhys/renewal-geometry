/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeDiracVariation
import RenewalGeometry.Continuum.NativeGravityFirstJet
import RenewalGeometry.Analysis.WeakJetPairing
import RenewalGeometry.Algebra.SeriesLogChart

/-!
# Convergence of the spin–gauge link coefficients of the native Dirac–Yukawa sector
  (`prop:native-spinor-variation`, coefficient part; Einstein–SM action-closure manuscript)

Setting: the unit-torus rendering (grid `(ℤ/N)⁴`, mesh `h = 1/N`, raw reconstructions `R_h^0 = pc`)
of `Continuum/NativeGravityFirstJet.lean` and `Continuum/NativeYangMillsMetricVariation.lean`.

The paper's proof of `prop:native-spinor-variation`: "The physical spin–gauge link can be written
exactly as `∇^h_μΨ_h = D⁺_{μ,h}Ψ_h + B_{μ,h}T_{μ,1}Ψ_h`, with the analogous dual identity.  The
coefficient `B_{μ,h}` splits into the coframe-derived spin coefficient and the compact internal-link
coefficient.  Strong first-jet coframe convergence gives the former and its metric variation
strongly in `L²` by `lem:products`; strong `L⁴` connection convergence gives the latter by
`eq:native-link-coeff`."  This file proves exactly these coefficient limits for the literal
link quotients `W_μ = (V_μ - 1)/h`, `W'_μ = (V_μ⁻¹ - 1)/h` of `NativeDirac`:

* generic calculus: `lpTendsto_of_bdd_tendstoInMeasure` (bounded + in measure ⇒ `L^p`),
  `lpTendsto_add_remainder` (a remainder dominated by a bounded coefficient converging to `0` in
  measure times a strongly convergent field is negligible), `tendstoInMeasure_zero_of_norm_le`,
  `tendstoInMeasure_comp_ball` (continuous chart compositions on a compact ball);
* `linkQ` (`h⁻¹(e^{hX} - 1)`) and `norm_linkQ_sub_le`;
* `lpTendsto_omega`: `R^0 ω_{μ,h} → Ω_μ(e, ∂e)` in `L²` (the coframe-derived spin connection);
* `lpTendsto_wL`, `lpTendsto_wR`: `R^0 W_μ → σ(ω_μ) + ρ_S(A_μ)` and `R^0 W'_μ → -(σ(ω_μ) + ρ_S(A_μ))`
  strongly in `L²` under strong first-jet coframe convergence, the scaled spin-link margin
  `h|ω_{μ,h}| ≤ c_*` and strong `L⁴` connection convergence.
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace
open scoped BigOperators ENNReal NNReal

namespace RenewalGeometry.NativeDiracConv

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Generic calculus of strong and in-measure convergence -/

section Generic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Bounded and convergent in measure ⇒ strongly convergent in every `L^p`, `p < ∞`.** -/
theorem lpTendsto_of_bdd_tendstoInMeasure {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℕ → X → E} {f₀ : X → E} (hfm : ∀ k, AEStronglyMeasurable (f k) μ)
    (hf : TendstoInMeasure μ f atTop f₀) {M : ℝ} (hM : ∀ k, ∀ᵐ x ∂μ, ‖f k x‖ ≤ M) :
    LpTendsto μ p f f₀ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hf₀m : AEStronglyMeasurable f₀ μ := hf.aestronglyMeasurable hfm
  have hM₀ := LpProductContinuity.ae_norm_le_of_tendstoInMeasure hf hM
  refine ⟨fun k => MemLp.of_bound (hfm k) M (hM k), MemLp.of_bound hf₀m M hM₀, ?_⟩
  refine LpProductContinuity.tendsto_eLpNorm_of_tendstoInMeasure_dominated hp0 hp hf
    (K := M + M) (fun k => ?_) (fun k => (hfm k).sub hf₀m) (memLp_const (1 : ℝ))
    (Eventually.of_forall fun _ => zero_le_one) (fun k => Eventually.of_forall fun x => ?_)
  · filter_upwards [hM k, hM₀] with x h1 h2
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  · simp

/-- **Negligible remainders.**  If `f_k → f` in `L^p` and `‖R_k‖ ≤ θ_k ‖f_k‖` with `θ_k` bounded
and `θ_k → 0` in measure, then `f_k + R_k → f` in `L^p`. -/
theorem lpTendsto_add_remainder {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {f : ℕ → X → E}
    {f₀ : X → E} (hf : LpTendsto μ p f f₀) {R : ℕ → X → E}
    (hRm : ∀ k, AEStronglyMeasurable (R k) μ) {θ : ℕ → X → ℝ}
    (hθm : ∀ k, AEStronglyMeasurable (θ k) μ) (hθ : TendstoInMeasure μ θ atTop 0) {M : ℝ}
    (hθb : ∀ k, ∀ᵐ x ∂μ, ‖θ k x‖ ≤ M) (hR : ∀ k, ∀ᵐ x ∂μ, ‖R k x‖ ≤ θ k x * ‖f k x‖) :
    LpTendsto μ p (fun k x => f k x + R k x) f₀ := by
  -- `θ_k f_k → 0`
  set β : ℕ → X → E →L[ℝ] E := fun k x => θ k x • ContinuousLinearMap.id ℝ E
  have hβm : ∀ k, AEStronglyMeasurable (β k) μ := fun k =>
    (hθm k).smul aestronglyMeasurable_const
  have hβ : TendstoInMeasure μ β atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hθ ⊢
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hθ ε hε) (fun k => zero_le)
      fun k => measure_mono fun x hx => ?_
    simp only [Set.mem_setOf_eq, Pi.zero_apply, sub_zero, β] at hx ⊢
    refine hx.trans ?_
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
  have hβb : ∀ k, ∀ᵐ x ∂μ, ‖β k x‖ ≤ M := fun k => by
    filter_upwards [hθb k] with x hx
    rw [norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans hx
  have h1 := LpProductContinuity.LpTendsto.coeff hp hβm hβ hβb hf
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply] at h1
  have hR0 : LpTendsto μ p R 0 := by
    refine ⟨fun k => ?_, MemLp.zero, ?_⟩
    · refine (h1.memLp k).of_le (hRm k) ?_
      filter_upwards [hR k] with x hx
      simp only [β, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul]
      exact hx.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    · have h2 := h1.tendsto
      simp only [sub_zero] at h2 ⊢
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun k => zero_le)
        fun k => eLpNorm_mono_ae ?_
      filter_upwards [hR k] with x hx
      simp only [β, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul,
        Pi.sub_apply, Pi.zero_apply, sub_zero, Real.norm_eq_abs]
      exact hx.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have := hf.add hR0
  rw [add_zero] at this
  exact this

/-- Uniform smallness implies convergence to `0` in measure. -/
theorem tendstoInMeasure_zero_of_norm_le {f : ℕ → X → E} {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hf : ∀ k x, ‖f k x‖ ≤ s k) :
    TendstoInMeasure μ f atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hev : ∀ᶠ k in atTop, s k < ε := (tendsto_order.1 hs).2 ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with k hk
  symm
  refine measure_eq_zero_iff_ae_notMem.2 (Eventually.of_forall fun x hx => ?_)
  simp only [Set.mem_setOf_eq, Pi.zero_apply, sub_zero] at hx
  linarith [hf k x]

theorem tendstoInMeasure_of_lpTendsto {p : ℝ≥0∞} (hp0 : p ≠ 0) {f : ℕ → X → E} {f₀ : X → E}
    (hf : LpTendsto μ p f f₀) : TendstoInMeasure μ f atTop f₀ :=
  tendstoInMeasure_of_tendsto_eLpNorm hp0 (fun k => (hf.memLp k).1) hf.memLp_lim.1 hf.tendsto

/-- Continuous compositions on a compact ball preserve convergence in measure and boundedness. -/
theorem tendstoInMeasure_comp_ball [FiniteDimensional ℝ E] {f : ℕ → X → E} {f₀ : X → E}
    (hf : TendstoInMeasure μ f atTop f₀) {R : ℝ}
    (hR : ∀ k x, ‖f k x‖ ≤ R) {Φ : E → F} (hΦ : ContinuousOn Φ (closedBall 0 R)) :
    TendstoInMeasure μ (fun k x => Φ (f k x)) atTop (fun x => Φ (f₀ x)) ∧
      ∃ M, ∀ k x, ‖Φ (f k x)‖ ≤ M := by
  have hin : ∀ k, ∀ᵐ x ∂μ, f k x ∈ closedBall (0 : E) R := fun k =>
    Eventually.of_forall fun x => by simpa using hR k x
  have hin' : ∀ᵐ x ∂μ, f₀ x ∈ closedBall (0 : E) R := by
    have := LpProductContinuity.ae_norm_le_of_tendstoInMeasure hf (K := R)
      (fun k => Eventually.of_forall fun x => hR k x)
    filter_upwards [this] with x hx using by simpa using hx
  refine ⟨LpProductContinuity.tendstoInMeasure_comp_of_continuousOn (isCompact_closedBall 0 R)
    hΦ hin hin' hf, ?_⟩
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : E) R).image_of_continuousOn hΦ).isBounded
    |>.exists_norm_le
  exact ⟨M, fun k x => hM _ ⟨_, by simpa using hR k x, rfl⟩⟩

/-- A real factor tending to `0` kills a strongly convergent sequence in measure. -/
theorem tendstoInMeasure_smul_of_lpTendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) {f : ℕ → X → E} {f₀ : X → E}
    (hf : LpTendsto μ p f f₀) : TendstoInMeasure μ (fun k x => c k • f k x) atTop 0 := by
  obtain ⟨C, hC, hfC⟩ := NativeGridLp.exists_bound_of_lpTendsto hf
  refine tendstoInMeasure_of_tendsto_eLpNorm hp0 (fun k => ((hf.memLp k).1.const_smul (c k)))
    aestronglyMeasurable_const ?_
  have hb : ∀ k, eLpNorm ((fun x => c k • f k x) - 0) p μ ≤ ENNReal.ofReal |c k| * C := by
    intro k
    simp only [sub_zero]
    rw [show (fun x => c k • f k x) = c k • f k from rfl, eLpNorm_const_smul,
      ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hfC k) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun k => zero_le) hb
  have h1 : Tendsto (fun k => ENNReal.ofReal |c k|) atTop (𝓝 0) := by
    have habs : Tendsto (fun k => |c k|) atTop (𝓝 0) := by simpa using hc.abs
    have := (ENNReal.continuous_ofReal.tendsto 0).comp habs
    rw [ENNReal.ofReal_zero] at this
    exact this
  simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hC)

end Generic
/-! ### Chart coefficients -/

section Chart

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open NativeGravityFirstJet (M4)

variable {Z Z' W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup Z']
  [NormedSpace ℝ Z'] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The coframe limit stays in the closed chart. -/
theorem ae_mem_of_lpTendsto {p : ℝ≥0∞} (hp0 : p ≠ 0) {Ke : Set M4} (hKe : IsClosed Ke)
    {e : ℕ → UnitAddTorus (Fin 4) → M4} {e₀ : UnitAddTorus (Fin 4) → M4}
    (he : LpTendsto volume p e e₀) (hval : ∀ k y, e k y ∈ Ke) : ∀ᵐ y, e₀ y ∈ Ke :=
  HomogeneousJetVariation.ae_mem_of_tendstoInMeasure hKe (tendstoInMeasure_of_lpTendsto hp0 he)
    fun k => Eventually.of_forall fun y => hval k y

/-- **Chart coefficients times strongly convergent fields** (`lem:products`): if the coframes
`e_k → e₀` in measure with values in a compact chart `K_e` and `Φ` is continuous on `K_e`, then
`B(Φ(e_k), s_k) → B(Φ(e₀), s)` in `L^p` whenever `s_k → s` in `L^p`. -/
theorem lpTendsto_chart_bilin {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ke : Set M4}
    (hKe : IsCompact Ke) {Φ : M4 → Z} (hΦ : ContinuousOn Φ Ke)
    {e : ℕ → UnitAddTorus (Fin 4) → M4} {e₀ : UnitAddTorus (Fin 4) → M4}
    (hΦm : ∀ k, AEStronglyMeasurable (fun y => Φ (e k y)) volume)
    (he : TendstoInMeasure volume e atTop e₀)
    (hval : ∀ k y, e k y ∈ Ke) (he₀ : ∀ᵐ y, e₀ y ∈ Ke) (B : Z →L[ℝ] Z' →L[ℝ] W)
    {s : ℕ → UnitAddTorus (Fin 4) → Z'} {s₀ : UnitAddTorus (Fin 4) → Z'}
    (hs : LpTendsto volume p s s₀) :
    LpTendsto volume p (fun k y => B (Φ (e k y)) (s k y)) (fun y => B (Φ (e₀ y)) (s₀ y)) := by
  obtain ⟨M, hM⟩ := (hKe.image_of_continuousOn hΦ).isBounded.exists_norm_le
  have hc := LpProductContinuity.tendstoInMeasure_comp_of_continuousOn hKe hΦ
    (fun k => Eventually.of_forall fun y => hval k y) he₀ he
  have hcB : TendstoInMeasure volume (fun k y => B (Φ (e k y))) atTop (fun y => B (Φ (e₀ y))) :=
    HomogeneousJetVariation.tendstoInMeasure_of_lipschitz (L := ‖B‖ + 1) (by positivity)
      (fun a b => by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)))
      hc
  refine LpProductContinuity.LpTendsto.coeff hp (fun k => B.continuous.comp_aestronglyMeasurable
    (hΦm k)) hcB (K := ‖B‖ * M) (fun k => Eventually.of_forall fun y => ?_) hs
  exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM _ ⟨_, hval k y, rfl⟩) (norm_nonneg _))

end Chart

/-! ### The coframe-derived connection as a linear function of the first difference -/

section Omega

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open NativeScaling (Mat readerOmega omegaLink)
open NativeGravityFirstJet (M4 asM4)

/-- The reader `Ω_μ(e, ·)` as a linear map of the first jet. -/
def omegaLin (e : Mat) (μ : Fin 4) : (Fin 4 → Mat) →ₗ[ℝ] Mat where
  toFun q := readerOmega e q μ
  map_add' q q' := NativeScaling.readerOmega_add e q q' μ
  map_smul' c q := NativeScaling.readerOmega_smul e c q μ

/-- The jet basis `E_{λij} = δ_λ ⊗ e_{ij}`. -/
def jetBasis (lam : Fin 4) (i j : Fin 4) : Fin 4 → Mat := Pi.single lam (Matrix.single i j 1)

theorem jet_expand (q : Fin 4 → Mat) :
    q = ∑ lam, ∑ i, ∑ j, q lam i j • jetBasis lam i j := by
  funext lam' a b
  simp [jetBasis, Finset.sum_apply, Pi.single_apply]
  rw [← Matrix.matrix_eq_sum_single]

/-- The coefficient functions `G_{μλij}(e) = Ω_μ(e, E_{λij})` on the sup-normed arrays. -/
def omegaCoef (μ lam i j : Fin 4) (e : M4) : M4 := asM4 (readerOmega e (jetBasis lam i j) μ)

/-- **`Ω_μ(e, q) = Σ q_{λij} G_{μλij}(e)`**: the reader is linear in the first difference with
smooth coefficients. -/
theorem readerOmega_expand (e : Mat) (q : Fin 4 → Mat) (μ : Fin 4) :
    asM4 (readerOmega e q μ) = ∑ lam, ∑ i, ∑ j, q lam i j • omegaCoef μ lam i j e := by
  have h := congrArg (omegaLin e μ) (jet_expand q)
  simp only [map_sum, map_smul] at h
  exact h

theorem contDiffAt_omegaCoef (μ lam i j : Fin 4) {e : M4} (he : Matrix.det (show Mat from e) ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (omegaCoef μ lam i j) e := by
  refine contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
  have h := NativeDensity.contDiffAt_readerOmega_entry μ a b (q := ((e : Mat), jetBasis lam i j)) he
  have hl : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun e' : M4 => (((e' : Mat), jetBasis lam i j) : Mat × (Fin 4 → Mat))) e :=
    (contDiff_prodMk_left _).contDiffAt
  exact h.comp e hl

theorem continuousOn_omegaCoef (μ lam i j : Fin 4) {Ke : Set M4}
    (hKe : ∀ M ∈ Ke, Matrix.det (show Mat from M) ≠ 0) :
    ContinuousOn (omegaCoef μ lam i j) Ke := fun e he =>
  (contDiffAt_omegaCoef μ lam i j (hKe e he)).continuousAt.continuousWithinAt

end Omega

/-! ### The literal link quotients -/

section LinkQ

variable {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [CompleteSpace 𝔅] [NormOneClass 𝔅]

/-- `linkQ h X = h⁻¹(e^{hX} - 1)`. -/
def linkQ (h : ℝ) (X : 𝔅) : 𝔅 := h⁻¹ • (exp (h • X) - 1)

/-- `‖linkQ h X - X‖ ≤ ‖X‖ (h‖X‖ e^{h‖X‖})` for `h > 0`. -/
theorem norm_linkQ_sub_le {h : ℝ} (hh : 0 < h) (X : 𝔅) :
    ‖linkQ h X - X‖ ≤ (h * ‖X‖ * Real.exp (h * ‖X‖)) * ‖X‖ := by
  have hlin := LogBCH.norm_exp_sub_linear_le (h • X)
  rw [norm_smul, Real.norm_of_nonneg hh.le] at hlin
  have e : linkQ h X - X = h⁻¹ • (exp (h • X) - 1 - h • X) := by
    simp only [linkQ, smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hh.le)]
  calc h⁻¹ * ‖exp (h • X) - 1 - h • X‖ ≤ h⁻¹ * ((h * ‖X‖) ^ 2 * Real.exp (h * ‖X‖)) :=
        mul_le_mul_of_nonneg_left hlin (inv_nonneg.2 hh.le)
    _ = (h * ‖X‖ * Real.exp (h * ‖X‖)) * ‖X‖ := by field_simp

/-- `e^{hX} e^{hY} - 1 = h (linkQ h X · e^{hY} + linkQ h Y)`. -/
theorem linkQ_mul_split (h : ℝ) (X Y : 𝔅) :
    h⁻¹ • (exp (h • X) * exp (h • Y) - 1) = linkQ h X * exp (h • Y) + linkQ h Y := by
  simp only [linkQ, smul_mul_assoc, sub_mul, one_mul, ← smul_add]
  congr 1
  abel

end LinkQ

/-! ### The standing hypotheses on coframes and connections -/

section Hyp

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)
open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat readerOmega omegaLink)
open NativeGravityFirstJet (M4 asM4 coframeM)
open NativeDensity NativeDirac

local instance fact_one_le_two_dc : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_dc : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]

/-- Finite sums of strongly convergent sequences. -/
theorem lpTendsto_finset_sum {X V : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ι' : Type*} (s : Finset ι') {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {f : ι' → ℕ → X → V} {f₀ : ι' → X → V}
    (hf : ∀ i ∈ s, LpTendsto ν p (f i) (f₀ i)) :
    LpTendsto ν p (fun k x => ∑ i ∈ s, f i k x) (fun x => ∑ i ∈ s, f₀ i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LpTendsto.const (ν := ν) (p := p) (u := fun _ : X => (0 : V)) MemLp.zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The forward difference of the coframe on the sup-normed arrays. -/
def qM {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (lam : Fin 4) : Grid N → M4 :=
  fun x => fwdDiff (N : ℝ)⁻¹ lam (coframe y) x

/-- The coframe-derived connection on the sup-normed arrays. -/
def ωM {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (μ : Fin 4) : Grid N → M4 :=
  fun x => asM4 (omegaLink (N : ℝ)⁻¹ (coframe y) x μ)

/-- **The coframe and connection hypotheses** of `prop:native-spinor-variation` (unit-torus
rendering): nodal coframes in one compact oriented chart `K_e`, the scaled spin-link margin
`h |ω_{μ,h}| ≤ c_*` (`eq:native-gravity-log-margin`), strong `L²` first-jet coframe convergence
(`eq:native-coframe-firstjet`) and strong `L⁴` connection convergence. -/
structure CoHyp (n : ℕ → ℕ) [∀ k, NeZero (n k)] (y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢) where
  hn : Tendsto n atTop atTop
  Ke : Set M4
  hKe : IsCompact Ke
  hKdet : ∀ M ∈ Ke, Matrix.det (show Mat from M) ≠ 0
  hval : ∀ k x, coframeM (y k) x ∈ Ke
  c : ℝ
  hmar : ∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ c
  e₀ : UnitAddTorus (Fin 4) → M4
  he : LpTendsto volume 2 (fun k => pc (coframeM (y k))) e₀
  p : Fin 4 → UnitAddTorus (Fin 4) → M4
  hp : ∀ lam, LpTendsto volume 2 (fun k => pc (qM (y k) lam)) (p lam)
  A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔄
  hA : ∀ μ, LpTendsto volume 4 (fun k => pc (gauge (y k) μ)) (A₀ μ)

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

namespace CoHyp

variable (H : CoHyp n y)

theorem e₀_mem : ∀ᵐ z, H.e₀ z ∈ H.Ke :=
  ae_mem_of_lpTendsto two_ne_zero H.hKe.isClosed H.he fun k z => H.hval k _

theorem tendstoInMeasure_e : TendstoInMeasure volume (fun k => pc (coframeM (y k))) atTop H.e₀ :=
  tendstoInMeasure_of_lpTendsto two_ne_zero H.he

/-- The limit connection coefficient `ω₀_μ = Ω_μ(e, ∂e)` (Levi-Civita at `p = ∂e`). -/
def ω₀ (μ : Fin 4) (z : UnitAddTorus (Fin 4)) : M4 :=
  asM4 (readerOmega (H.e₀ z) (fun lam => H.p lam z) μ)

/-- The coordinate functional `M ↦ M_{ij}`. -/
def entryL (i j : Fin 4) : M4 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 =>
    Fin 4 → ℝ) i)

theorem lpTendsto_q_coord (lam i j : Fin 4) :
    LpTendsto volume 2 (fun k z => pc (qM (y k) lam) z i j) (fun z => H.p lam z i j) :=
  (H.hp lam).clm (entryL i j)

/-- **`R^0 ω_{μ,h} → Ω_μ(e, ∂e)` strongly in `L²`** (`lem:products`). -/
theorem lpTendsto_omega (μ : Fin 4) :
    LpTendsto volume 2 (fun k => pc (ωM (y k) μ)) (H.ω₀ μ) := by
  have he : ∀ k z, pc (ωM (y k) μ) z =
      ∑ lam, ∑ i, ∑ j, pc (qM (y k) lam) z i j • omegaCoef μ lam i j (pc (coframeM (y k)) z) :=
    fun k z => by simp only [pc, ωM, omegaLink, readerOmega_expand]; rfl
  have he₀ : ∀ z, H.ω₀ μ z = ∑ lam, ∑ i, ∑ j, H.p lam z i j • omegaCoef μ lam i j (H.e₀ z) :=
    fun z => readerOmega_expand _ _ _
  have key : LpTendsto volume 2
      (fun k z => ∑ lam, ∑ i, ∑ j, pc (qM (y k) lam) z i j •
        omegaCoef μ lam i j (pc (coframeM (y k)) z))
      (fun z => ∑ lam, ∑ i, ∑ j, H.p lam z i j • omegaCoef μ lam i j (H.e₀ z)) := by
    refine lpTendsto_finset_sum _ fun lam _ => lpTendsto_finset_sum _ fun i _ =>
      lpTendsto_finset_sum _ fun j _ => ?_
    exact lpTendsto_chart_bilin (p := 2) (by norm_num) H.hKe
      (continuousOn_omegaCoef μ lam i j H.hKdet)
      (fun k => (stronglyMeasurable_pc (fun x => omegaCoef μ lam i j (coframeM (y k) x)))
        |>.aestronglyMeasurable)
      H.tendstoInMeasure_e (fun k z => H.hval k _) H.e₀_mem
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] M4 →L[ℝ] M4).flip (H.lpTendsto_q_coord lam i j)
  exact key.congr (fun k => Eventually.of_forall fun z => (he k z).symm)
    (Eventually.of_forall fun z => (he₀ z).symm)

end CoHyp

end Hyp

/-! ### Convergence of the link quotients `W_μ`, `W'_μ` -/

section Links

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)
open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat readerOmega omegaLink)
open NativeGravityFirstJet (M4 asM4 coframeM)
open NativeDensity NativeDirac

local instance fact_one_le_two_dl : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_dl : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem hpos_inv (N : ℕ) [NeZero N] : (0 : ℝ) < (N : ℝ)⁻¹ := by
  have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  positivity

/-- The spin representation as a continuous linear map on the sup-normed arrays. -/
def σL (D : NativeDensity.Data 𝔄 𝓗 𝓢) : M4 →L[ℝ] Spin 𝓢 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => D.σ (M : Mat), map_add' := fun M M' => map_add D.σ (M : Mat) M',
      map_smul' := fun c M => map_smul D.σ c (M : Mat) }

theorem σL_apply (D : NativeDensity.Data 𝔄 𝓗 𝓢) (M : Mat) : σL D (asM4 M) = D.σ M := rfl

/-- `ρ_S(e^{hA}) = e^{h ρ_S(A)}`. -/
theorem ρS_exp_smul (D : NativeDensity.Data 𝔄 𝓗 𝓢) (h : ℝ) (A : 𝔄) :
    D.ρS (exp (h • A)) = exp (h • D.ρSL A) := by
  rw [algHom_map_exp D.ρS D.ρS_cont, map_smul, Data.ρSL_apply]

theorem wL_eq (D : NativeDensity.Data 𝔄 𝓗 𝓢) {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢)
    (x : Grid N) (μ : Fin 4) :
    wL D (N : ℝ)⁻¹ y x μ = linkQ (N : ℝ)⁻¹ (σL D (ωM y μ x)) *
        exp ((N : ℝ)⁻¹ • D.ρSL (gauge y μ x)) + linkQ (N : ℝ)⁻¹ (D.ρSL (gauge y μ x)) := by
  rw [wL, spinLink, NativeScaling.spinLink, ContinuousLinearMap.coe_coe, ρS_exp_smul]
  exact linkQ_mul_split _ _ _

theorem wR_eq (D : NativeDensity.Data 𝔄 𝓗 𝓢) {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢)
    (x : Grid N) (μ : Fin 4) :
    wR D (N : ℝ)⁻¹ y x μ = linkQ (N : ℝ)⁻¹ (-D.ρSL (gauge y μ x)) *
        exp ((N : ℝ)⁻¹ • -σL D (ωM y μ x)) + linkQ (N : ℝ)⁻¹ (-σL D (ωM y μ x)) := by
  rw [wR, spinLinkInv, ← smul_neg, ← smul_neg, ρS_exp_smul, map_neg]
  exact linkQ_mul_split _ _ _

/-- Right multiplication `M ↦ M E`. -/
def mulRight (E : Spin 𝓢) : Spin 𝓢 →L[ℝ] Spin 𝓢 := (ContinuousLinearMap.mul ℝ (Spin 𝓢)).flip E

@[simp] theorem mulRight_apply (E M : Spin 𝓢) : mulRight E M = M * E := rfl

theorem norm_mulRight_le (E : Spin 𝓢) : ‖mulRight E‖ ≤ ‖E‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun M => by
    rw [mulRight_apply, mul_comm ‖E‖]; exact norm_mul_le _ _

/-- Right multiplication by `e^{Z_k}` tends to the identity in measure when `Z_k → 0` in
measure, and stays bounded when `‖Z_k‖ ≤ R`. -/
theorem tendstoInMeasure_mulRight_exp {Z : ℕ → UnitAddTorus (Fin 4) → Spin 𝓢}
    (hZ : TendstoInMeasure volume Z atTop 0) {R : ℝ} (hR : ∀ k z, ‖Z k z‖ ≤ R) :
    TendstoInMeasure volume (fun k z => mulRight (exp (Z k z))) atTop
        (fun _ => ContinuousLinearMap.id ℝ (Spin 𝓢)) ∧
      ∀ k z, ‖mulRight (exp (Z k z))‖ ≤ Real.exp R := by
  refine ⟨?_, fun k z => (norm_mulRight_le _).trans ((LogBCH.norm_exp_le_real_exp _).trans
    (Real.exp_le_exp.2 (hR k z)))⟩
  rw [tendstoInMeasure_iff_norm] at hZ ⊢
  intro ε hε
  have hδ : 0 < min 1 (ε / 2) := lt_min one_pos (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hZ _ hδ) (fun k => zero_le)
    fun k => measure_mono fun z hz => ?_
  simp only [Set.mem_setOf_eq, Pi.zero_apply, sub_zero] at hz ⊢
  by_contra hlt
  push_neg at hlt
  have h1 : ‖Z k z‖ ≤ 1 := hlt.le.trans (min_le_left _ _)
  have h2 : ‖mulRight (exp (Z k z)) - ContinuousLinearMap.id ℝ (Spin 𝓢)‖ ≤ 2 * ‖Z k z‖ := by
    have e : mulRight (exp (Z k z)) - ContinuousLinearMap.id ℝ (Spin 𝓢) =
        mulRight (exp (Z k z) - 1) := by
      ext M v; simp [mul_sub]
    rw [e]
    exact (norm_mulRight_le _).trans (SeriesLogChart.norm_exp_sub_one_le h1)
  have h3 : 2 * ‖Z k z‖ < ε := by
    have := hlt.trans_le (min_le_right _ _); linarith
  linarith

/-- **`linkQ_h(X_k) → X` in `L²`** when `X_k → X` in `L²`, `h X_k → 0` in measure and
`h ‖X_k‖ ≤ R`. -/
theorem lpTendsto_linkQ {X : ℕ → UnitAddTorus (Fin 4) → Spin 𝓢}
    {X₀ : UnitAddTorus (Fin 4) → Spin 𝓢} (hX : LpTendsto volume 2 X X₀)
    (hXm : ∀ k, AEStronglyMeasurable (fun z => linkQ (n k : ℝ)⁻¹ (X k z) - X k z) volume)
    (hhX : TendstoInMeasure volume (fun k z => (n k : ℝ)⁻¹ • X k z) atTop 0)
    (hhXm : ∀ k, AEStronglyMeasurable (fun z => (n k : ℝ)⁻¹ • X k z) volume) {R : ℝ}
    (hR : ∀ k z, ‖(n k : ℝ)⁻¹ • X k z‖ ≤ R) :
    LpTendsto volume 2 (fun k z => linkQ (n k : ℝ)⁻¹ (X k z)) X₀ := by
  have hθ : TendstoInMeasure volume (fun k z => ‖(n k : ℝ)⁻¹ • X k z‖ *
      Real.exp ‖(n k : ℝ)⁻¹ • X k z‖) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hhX ⊢
    intro ε hε
    have hδ : 0 < min 1 (ε / Real.exp 1) := lt_min one_pos (by positivity)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hhX _ hδ)
      (fun k => zero_le) fun k => measure_mono fun z hz => ?_
    simp only [Set.mem_setOf_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hz ⊢
    by_contra hlt
    push_neg at hlt
    set a := ‖(n k : ℝ)⁻¹ • X k z‖
    have ha0 : 0 ≤ a := norm_nonneg _
    have h1 : a ≤ 1 := hlt.le.trans (min_le_left _ _)
    have h2 : a < ε / Real.exp 1 := hlt.trans_le (min_le_right _ _)
    have h3 : a * Real.exp a ≤ a * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) ha0
    have h4 : a * Real.exp 1 < ε := by
      rwa [lt_div_iff₀ (Real.exp_pos 1)] at h2
    rw [abs_of_nonneg (by positivity)] at hz
    linarith
  have hθm : ∀ k, AEStronglyMeasurable (fun z => ‖(n k : ℝ)⁻¹ • X k z‖ *
      Real.exp ‖(n k : ℝ)⁻¹ • X k z‖) volume := fun k =>
    (hhXm k).norm.mul (Real.continuous_exp.comp_aestronglyMeasurable (hhXm k).norm)
  have := lpTendsto_add_remainder (p := 2) (by norm_num) hX hXm hθm hθ (M := R * Real.exp R)
    (fun k => Eventually.of_forall fun z => ?_) (fun k => Eventually.of_forall fun z => ?_)
  · simpa using this
  · rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul (hR k z) (Real.exp_le_exp.2 (hR k z)) (by positivity)
      ((norm_nonneg _).trans (hR k z))
  · have h1 := norm_linkQ_sub_le (hpos_inv (n k)) (X k z)
    have h2 : (n k : ℝ)⁻¹ * ‖X k z‖ = ‖(n k : ℝ)⁻¹ • X k z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hpos_inv (n k)).le]
    rw [← h2]
    exact h1

variable {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- The scaled sup norm of the internal links, `s_μ(k) = ‖ρ_S‖ h ‖A_{μ,h}‖_∞ → 0`. -/
def sA (D : NativeDensity.Data 𝔄 𝓗 𝓢) (y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢) (μ : Fin 4)
    (k : ℕ) : ℝ :=
  ‖D.ρSL‖ * NativeCriticalGrid.meshSup (N := n k) (gauge (y k) μ)

theorem norm_h_ρS_le (D : NativeDensity.Data 𝔄 𝓗 𝓢) (μ : Fin 4) (k : ℕ) (x : Grid (n k)) :
    ‖(n k : ℝ)⁻¹ • D.ρSL (gauge (y k) μ x)‖ ≤ sA D y μ k := by
  rw [norm_smul, Real.norm_of_nonneg (hpos_inv (n k)).le]
  calc (n k : ℝ)⁻¹ * ‖D.ρSL (gauge (y k) μ x)‖ ≤ (n k : ℝ)⁻¹ * (‖D.ρSL‖ * ‖gauge (y k) μ x‖) :=
        mul_le_mul_of_nonneg_left (D.ρSL.le_opNorm _) (hpos_inv (n k)).le
    _ = ‖D.ρSL‖ * ((n k : ℝ)⁻¹ * ‖gauge (y k) μ x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (NativeCriticalGrid.le_meshSup (N := n k) _ x)
        (ContinuousLinearMap.opNorm_nonneg _)

namespace CoHyp

variable (H : CoHyp n y) (D : NativeDensity.Data 𝔄 𝓗 𝓢)

include H

theorem tendsto_h : Tendsto (fun k => ((n k : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp H.hn)

theorem tendsto_sA (μ : Fin 4) : Tendsto (sA D y μ) atTop (𝓝 0) := by
  have h := NativeCriticalGrid.tendsto_meshSup H.hn (A := fun k => gauge (y k) μ)
    (H.hA μ).memLp_lim (H.hA μ).tendsto
  have := h.const_mul ‖D.ρSL‖
  rw [mul_zero] at this
  exact this

theorem exists_bound_sA (μ : Fin 4) : ∃ S, ∀ k, sA D y μ k ≤ S := by
  obtain ⟨S, hS⟩ := (H.tendsto_sA D μ).bddAbove_range
  exact ⟨S, fun k => hS (Set.mem_range_self k)⟩

/-- `h σ(ω_{μ,h}) → 0` in measure. -/
theorem tendstoInMeasure_hσω (μ : Fin 4) :
    TendstoInMeasure volume (fun k => pc (fun x => (n k : ℝ)⁻¹ • σL D (ωM (y k) μ x))) atTop 0 :=
by
  have h1 := (H.lpTendsto_omega μ).clm (σL D)
  have h2 := tendstoInMeasure_smul_of_lpTendsto (p := 2) two_ne_zero H.tendsto_h h1
  refine TendstoInMeasure.congr_left (fun k => Eventually.of_forall fun z => ?_) h2
  rfl

/-- The scaled spin-link margin bounds `h σ(ω_{μ,h})`. -/
theorem norm_hσω_le (k : ℕ) (x : Grid (n k)) (μ : Fin 4) :
    ‖(n k : ℝ)⁻¹ • σL D (ωM (y k) μ x)‖ ≤ ‖σL D‖ * H.c := by
  rw [norm_smul, Real.norm_of_nonneg (hpos_inv (n k)).le]
  calc (n k : ℝ)⁻¹ * ‖σL D (ωM (y k) μ x)‖
      ≤ (n k : ℝ)⁻¹ * (‖σL D‖ * ‖ωM (y k) μ x‖) :=
        mul_le_mul_of_nonneg_left ((σL D).le_opNorm _) (hpos_inv (n k)).le
    _ = ‖σL D‖ * ((n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖) := by ring
    _ ≤ ‖σL D‖ * H.c :=
        mul_le_mul_of_nonneg_left (H.hmar k x μ) (ContinuousLinearMap.opNorm_nonneg _)

/-- **The spin coefficient**: `R^0 linkQ_h(σ(ω_{μ,h})) → σ(Ω_μ(e, ∂e))` in `L²`. -/
theorem lpTendsto_linkQ_σω (μ : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => linkQ (n k : ℝ)⁻¹ (σL D (ωM (y k) μ x))))
      (fun z => σL D (H.ω₀ μ z)) :=
  lpTendsto_linkQ ((H.lpTendsto_omega μ).clm (σL D))
    (fun k => (stronglyMeasurable_pc (fun x => linkQ (n k : ℝ)⁻¹ (σL D (ωM (y k) μ x)) -
      σL D (ωM (y k) μ x))).aestronglyMeasurable)
    (H.tendstoInMeasure_hσω D μ)
    (fun k => (stronglyMeasurable_pc (fun x => (n k : ℝ)⁻¹ • σL D (ωM (y k) μ x))).aestronglyMeasurable)
    (fun k z => H.norm_hσω_le D k _ μ)

theorem tendstoInMeasure_neg_hσω (μ : Fin 4) :
    TendstoInMeasure volume (fun k => pc (fun x => (n k : ℝ)⁻¹ • -σL D (ωM (y k) μ x))) atTop 0 := by
  have h := H.tendstoInMeasure_hσω D μ
  rw [tendstoInMeasure_iff_norm] at h ⊢
  intro ε hε
  refine (h ε hε).congr fun k => ?_
  congr 1
  ext z
  simp [pc, smul_neg]

theorem lpTendsto_linkQ_neg_σω (μ : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => linkQ (n k : ℝ)⁻¹ (-σL D (ωM (y k) μ x))))
      (fun z => -σL D (H.ω₀ μ z)) :=
  lpTendsto_linkQ (((H.lpTendsto_omega μ).clm (σL D)).neg)
    (fun k => (stronglyMeasurable_pc (fun x => linkQ (n k : ℝ)⁻¹ (-σL D (ωM (y k) μ x)) -
      -σL D (ωM (y k) μ x))).aestronglyMeasurable)
    (H.tendstoInMeasure_neg_hσω D μ)
    (fun k => (stronglyMeasurable_pc (fun x => (n k : ℝ)⁻¹ • -σL D (ωM (y k) μ x))).aestronglyMeasurable)
    (R := ‖σL D‖ * H.c) (fun k z => by simpa [pc, smul_neg] using H.norm_hσω_le D k _ μ)

/-- The internal-link coefficient `linkQ_h(ρ(A)) → ρ(A)` in `L⁴` (`eq:native-link-coeff`). -/
theorem lpTendsto_linkQ_ρA (μ : Fin 4) (ρ : 𝔄 →L[ℝ] Spin 𝓢) :
    LpTendsto volume 4 (fun k => pc (fun x => linkQ (n k : ℝ)⁻¹ (ρ (gauge (y k) μ x))))
      (fun z => ρ (H.A₀ μ z)) := by
  have h := NativeCriticalGrid.tendsto_linkCoeff H.hn ρ (A := fun k => gauge (y k) μ)
    (H.hA μ).memLp_lim (H.hA μ).tendsto
  refine ⟨fun k => NativeYMIdentification.memLp_pc_gen _ 4,
    ((H.hA μ).memLp_lim.continuousLinearMap_comp ρ), ?_⟩
  refine h.congr fun k => ?_
  congr 1
  funext z
  simp [pc, NativeCriticalGrid.linkCoeff, linkQ]

/-- **`R^0 W_μ → σ(Ω_μ(e, ∂e)) + ρ_S(A_μ)` strongly in `L²`.** -/
theorem lpTendsto_wL (μ : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => wL D (n k : ℝ)⁻¹ (y k) x μ))
      (fun z => σL D (H.ω₀ μ z) + D.ρSL (H.A₀ μ z)) := by
  obtain ⟨S, hS⟩ := H.exists_bound_sA D μ
  have hZ : TendstoInMeasure volume
      (fun k => pc (fun x => (n k : ℝ)⁻¹ • D.ρSL (gauge (y k) μ x))) atTop 0 :=
    tendstoInMeasure_zero_of_norm_le (H.tendsto_sA D μ) fun k z => norm_h_ρS_le D μ k _
  obtain ⟨hβ, hM⟩ := tendstoInMeasure_mulRight_exp hZ (R := S)
    (fun k z => (norm_h_ρS_le D μ k _).trans (hS k))
  have h1 := LpProductContinuity.LpTendsto.coeff (p := 2) (by norm_num)
    (fun k => (stronglyMeasurable_pc (fun x => mulRight
      (exp ((n k : ℝ)⁻¹ • D.ρSL (gauge (y k) μ x))))).aestronglyMeasurable)
    hβ (fun k => Eventually.of_forall fun z => hM k z) (H.lpTendsto_linkQ_σω D μ)
  have h2 := (H.lpTendsto_linkQ_ρA μ D.ρSL).mono (p := 2) two_ne_zero (by norm_num)
  have := h1.add h2
  refine this.congr (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · simp only [Pi.add_apply, mulRight_apply, pc, wL_eq D]
  · simp

/-- **`R^0 W'_μ → -(σ(Ω_μ(e, ∂e)) + ρ_S(A_μ))` strongly in `L²`.** -/
theorem lpTendsto_wR (μ : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => wR D (n k : ℝ)⁻¹ (y k) x μ))
      (fun z => -(σL D (H.ω₀ μ z) + D.ρSL (H.A₀ μ z))) := by
  obtain ⟨hβ, hM⟩ := tendstoInMeasure_mulRight_exp (H.tendstoInMeasure_neg_hσω D μ)
    (R := ‖σL D‖ * H.c) (fun k z => by simpa [pc, smul_neg] using H.norm_hσω_le D k _ μ)
  have h1 := LpProductContinuity.LpTendsto.coeff (p := 2) (by norm_num)
    (fun k => (stronglyMeasurable_pc (fun x => mulRight
      (exp ((n k : ℝ)⁻¹ • -σL D (ωM (y k) μ x))))).aestronglyMeasurable)
    hβ (fun k => Eventually.of_forall fun z => hM k z)
    ((H.lpTendsto_linkQ_ρA μ (-D.ρSL)).mono (p := 2) two_ne_zero (by norm_num))
  have h2 := H.lpTendsto_linkQ_neg_σω D μ
  have := h1.add h2
  refine this.congr (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · simp only [Pi.add_apply, mulRight_apply, pc, wR_eq D, ContinuousLinearMap.neg_apply]
  · simp only [Pi.add_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply]
    abel

end CoHyp

end Links

end

end RenewalGeometry.NativeDiracConv
