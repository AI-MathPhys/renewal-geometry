/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeDiracLimit

/-!
# Convergence of the Dirac–Yukawa slot fields (`prop:native-spinor-variation`)

Unit-torus rendering.  Under the coframe/connection hypotheses `CoHyp`, strong `L²` convergence of
the Higgs field and strong `L²` convergence with uniform `L⁴` bounds of the spinor and co-spinor
fields (the conclusions of the first assertion, `native_spinor_weak_compactness`), the operator
fields `Gop` (value-paired part) and `Λop` (difference-paired part) of the finite Dirac–Yukawa first
variation, evaluated at the grid slots of the records, converge strongly — `Gop` in `L¹`, `Λop` in
`L²` — to the same fields evaluated at the **continuum slots** `contSlots` (`h = 0`).

Generic tools (no renewal notions):
* `lpTendsto_tri` — **trilinear products** `Θ(Φ_k, C_k, w_k)` with `Φ_k, w_k → ` strongly in `L²`
  and bounded in `L⁴`, `C_k →` strongly in `L²`, converge strongly in `L¹`;
* `lpTendsto_chart_gen` — bounded chart coefficients `Φ(e_k)` (compact chart, convergence in
  measure) times strongly `L^p`-convergent fields;
* `tendstoInMeasure_prod` — pairs of sequences converging in measure.
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace
open scoped BigOperators ENNReal NNReal

namespace RenewalGeometry.NativeDiracConvergence

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance fact_one_le_two_dc : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_dc : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance holder221_dc : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
local instance holder442_dc : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

/-! ### Generic tools -/

section Generic

variable {E F A W Z Z' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup Z']
  [NormedSpace ℝ Z']

/-- A real factor tending to `0` times a strongly convergent sequence tends to `0` strongly. -/
theorem lpTendsto_smul_zero {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    {f : ℕ → 𝕋 → E} {f₀ : 𝕋 → E} (hf : LpTendsto volume p f f₀) :
    LpTendsto volume p (fun k z => c k • f k z) 0 := by
  obtain ⟨C, hC, hfC⟩ := NativeGridLp.exists_bound_of_lpTendsto hf
  refine ⟨fun k => (hf.memLp k).const_smul (c k), MemLp.zero, ?_⟩
  have hb : ∀ k, eLpNorm ((fun z => c k • f k z) - 0) p volume ≤ ‖c k‖ₑ * C := by
    intro k
    rw [sub_zero, show (fun z => c k • f k z) = c k • f k from rfl, eLpNorm_const_smul]
    exact mul_le_mul_of_nonneg_left (hfC k) zero_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun k => zero_le) hb
  have h1 : Tendsto (fun k => ‖c k‖ₑ) atTop (𝓝 0) := by
    have := (continuous_enorm.tendsto (0 : ℝ)).comp hc
    simpa [Function.comp_def] using this
  simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hC)

/-- **Trilinear products** (`lem:products`, critical spinor bilinears): if `Φ_k → Φ` and
`w_k → w` strongly in `L²` with uniform `L⁴` bounds and `C_k → C` strongly in `L²`, then
`Θ(Φ_k, C_k, w_k) → Θ(Φ, C, w)` strongly in `L¹` for every bounded trilinear `Θ`. -/
theorem lpTendsto_tri (Θ : E →L[ℝ] A →L[ℝ] F →L[ℝ] W) {K : ℝ≥0}
    (hK : ∀ e a w, ‖Θ e a w‖ ≤ K * ‖e‖ * ‖a‖ * ‖w‖) {Φ : ℕ → 𝕋 → E} {Φ₀ : 𝕋 → E}
    (hΦ : LpTendsto volume 2 Φ Φ₀) {B₁ : ℝ≥0∞} (hB₁ : B₁ ≠ ∞)
    (hΦ4 : ∀ k, eLpNorm (Φ k) 4 volume ≤ B₁) {C : ℕ → 𝕋 → A} {C₀ : 𝕋 → A}
    (hC : LpTendsto volume 2 C C₀) {w : ℕ → 𝕋 → F} {w₀ : 𝕋 → F} (hw : LpTendsto volume 2 w w₀)
    {B₂ : ℝ≥0∞} (hB₂ : B₂ ≠ ∞) (hw4 : ∀ k, eLpNorm (w k) 4 volume ≤ B₂) :
    LpTendsto volume 1 (fun k z => Θ (Φ k z) (C k z) (w k z)) (fun z => Θ (Φ₀ z) (C₀ z) (w₀ z)) := by
  set β : E →L[ℝ] F →L[ℝ] A →L[ℝ] W :=
    (ContinuousLinearMap.flipₗᵢ ℝ A F W).toContinuousLinearEquiv.toContinuousLinearMap.comp Θ
  have hβ : ∀ e w, ‖β e w‖₊ ≤ K * ‖e‖₊ * ‖w‖₊ := fun e w => by
    rw [← NNReal.coe_le_coe]; push_cast
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
    have := hK e a w
    calc ‖Θ e a w‖ ≤ K * ‖e‖ * ‖a‖ * ‖w‖ := this
      _ = K * ‖e‖ * ‖w‖ * ‖a‖ := by ring
  have hv : LpTendsto volume 1 (fun k z => β (Φ k z) (w k z)) (fun z => β (Φ₀ z) (w₀ z)) :=
    LpTendsto.bilin (p := 2) (q := 2) (r := 1) β hΦ hw
  have hv2 : ∀ k, eLpNorm (fun z => β (Φ k z) (w k z)) 2 volume ≤ K * B₁ * B₂ := fun k =>
    (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 4) (q := 4) (r := 2) (hΦ.memLp k).1
      (hw.memLp k).1 (fun a b => β a b) K (Eventually.of_forall fun z => by
        simpa [mul_assoc] using hβ (Φ k z) (w k z))).trans (by
          rw [mul_assoc, mul_assoc]; gcongr; exacts [hΦ4 k, hw4 k])
  have hfin : (K : ℝ≥0∞) * B₁ * B₂ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hB₁) hB₂
  exact WeakJetPairing.lpTendsto_bilin_two_one (ContinuousLinearMap.apply ℝ W) hC hv hfin hv2

/-- Pairs of sequences converging in measure converge in measure. -/
theorem tendstoInMeasure_prod {f : ℕ → 𝕋 → E} {f₀ : 𝕋 → E} {g : ℕ → 𝕋 → F} {g₀ : 𝕋 → F}
    (hf : TendstoInMeasure volume f atTop f₀) (hg : TendstoInMeasure volume g atTop g₀) :
    TendstoInMeasure volume (fun k z => (f k z, g k z)) atTop (fun z => (f₀ z, g₀ z)) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have hs := (hf ε hε).add (hg ε hε)
  rw [add_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun k => zero_le)
    fun k => (measure_mono fun z hz => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_setOf_eq, Prod.mk_sub_mk, Prod.norm_def] at hz
  rcases le_max_iff.1 hz with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **Bounded chart coefficients times strongly convergent fields** (general compact chart). -/
theorem lpTendsto_chart_gen {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {K : Set Z} (hK : IsCompact K)
    {Φ : Z → Z'} (hΦ : ContinuousOn Φ K) {e : ℕ → 𝕋 → Z} {e₀ : 𝕋 → Z}
    (hΦm : ∀ k, AEStronglyMeasurable (fun y => Φ (e k y)) volume)
    (he : TendstoInMeasure volume e atTop e₀) (hval : ∀ k y, e k y ∈ K) (he₀ : ∀ᵐ y, e₀ y ∈ K)
    (B : Z' →L[ℝ] E →L[ℝ] W) {s : ℕ → 𝕋 → E} {s₀ : 𝕋 → E} (hs : LpTendsto volume p s s₀) :
    LpTendsto volume p (fun k y => B (Φ (e k y)) (s k y)) (fun y => B (Φ (e₀ y)) (s₀ y)) := by
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn hΦ).isBounded.exists_norm_le
  have hc := LpProductContinuity.tendstoInMeasure_comp_of_continuousOn hK hΦ
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

/-- A bounded chart coefficient alone converges strongly in every `L^p`, `p < ∞`. -/
theorem lpTendsto_chart {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {K : Set Z} (hK : IsCompact K)
    {Φ : Z → Z'} (hΦ : ContinuousOn Φ K) {e : ℕ → 𝕋 → Z} {e₀ : 𝕋 → Z}
    (hΦm : ∀ k, AEStronglyMeasurable (fun y => Φ (e k y)) volume)
    (he : TendstoInMeasure volume e atTop e₀) (hval : ∀ k y, e k y ∈ K) (he₀ : ∀ᵐ y, e₀ y ∈ K) :
    LpTendsto volume p (fun k y => Φ (e k y)) (fun y => Φ (e₀ y)) := by
  have := lpTendsto_chart_gen hp hK hΦ hΦm he hval he₀
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Z' →L[ℝ] Z').flip
    (LpTendsto.const (memLp_const (1 : ℝ)))
  simpa using this

/-- Constant fields are strongly convergent with uniform `L⁴` bounds. -/
theorem eLpNorm_const_le (c : E) : eLpNorm (fun _ : 𝕋 => c) 4 volume ≤ ‖c‖ₑ := by
  rw [eLpNorm_const _ (by norm_num) (NeZero.ne _)]
  simp

end Generic

/-! ### Continuum slots and chart coefficients -/

section Slots

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)
open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat readerOmega omegaLink)
open NativeGravityFirstJet (M4 asM4 coframeM liftM liftL dqLift dqLiftL)
open NativeDensity NativeDirac NativeDiracConv NativeDiracLimit

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

/-- The continuum connection `B_μ = σ(Ω_μ(e, ∂e)) + ρ_S(A_μ)` at one point. -/
def contB (e : M4) (p : Fin 4 → M4) (A : Fin 4 → 𝔄) (μ : Fin 4) : Spin 𝓢 :=
  σL D (asM4 (readerOmega e p μ)) + D.ρSL (A μ)

/-- Its variation `δB_μ[J] = σ(δω_μ[J]) + ρ_S(a_μ)` (the metric variation of the Levi-Civita spin
connection plus the gauge test). -/
def contdB (e : M4) (p : Fin 4 → M4) (μ : Fin 4) : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] Spin 𝓢 :=
  (σL D).comp (δωL e (fun _ => e) p μ) +
    D.ρSL.comp ((ContinuousLinearMap.proj μ).comp (πa 𝔄 𝓗 𝓢 W'))

/-- **The continuum slots** at one point (`h = 0`, `T_μΨ = Ψ`, `W = B`, `W' = -B`):
`(e, ∂e, A, H, Ψ, χ)` are the values of the continuum coframe, its derivatives, the gauge
connection, the Higgs field, the spinor and the co-spinor frame field. -/
def contSlots (e : M4) (p : Fin 4 → M4) (A : Fin 4 → 𝔄) (H : 𝓗) (Ψ : 𝓢) (χ : W') :
    Slots 𝔄 𝓗 𝓢 W' where
  h := 0
  v := volM e
  dv := (fderiv ℝ volM e).comp (εL e)
  γ μ := gammaM D μ e
  dγ μ := (fderiv ℝ (gammaM D μ) e).comp (εL e)
  Wl μ := contB D e p A μ
  Wr μ := -contB D e p A μ
  dWl μ := contdB D e p μ
  dWr μ := -contdB (W' := W') D e p μ
  YH := D.yukawa H
  Ψ := Ψ
  Ψp _ := Ψ
  Ψb := κ χ
  Ψbp _ := κ χ

theorem contDiffAt_gammaM (μ : Fin 4) {M : M4} (hM : Matrix.det (show Mat from M) ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gammaM D μ) M :=
  contDiffAt_gammaMu D μ hM

theorem continuousAt_fderiv_apply {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {f : M4 → E'} {M : M4} (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f M)
    {g : M4 → M4} (hg : ContinuousAt g M) :
    ContinuousAt (fun M' => fderiv ℝ f M' (g M')) M := by
  have h1 : ContinuousAt (fderiv ℝ f) M :=
    (hf.fderiv_right (m := 0) (by simp)).continuousAt
  exact h1.clm_apply hg

/-- The chart coefficients at a fixed test-jet vector `t`: `v`, `dv[t]`, `γ^μ`, `dγ^μ[t]`. -/
def chV (M : M4) : ℝ := volM M
def chDV (t : Jet 𝔄 𝓗 𝓢 W') (M : M4) : ℝ := fderiv ℝ volM M (liftL M t.1)
def chG (μ : Fin 4) (M : M4) : Spin 𝓢 := gammaM D μ M
def chDG (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) (M : M4) : Spin 𝓢 :=
  fderiv ℝ (gammaM D μ) M (liftL M t.1)

variable {Ke : Set M4} (hKdet : ∀ M ∈ Ke, Matrix.det (show Mat from M) ≠ 0)
include hKdet

theorem continuousOn_chV : ContinuousOn chV Ke := fun M hM =>
  (NativeGravityFirstJet.contDiffAt_volM (hKdet M hM)).continuousAt.continuousWithinAt

theorem continuousOn_chDV (t : Jet 𝔄 𝓗 𝓢 W') : ContinuousOn (chDV t) Ke := fun M hM =>
  (continuousAt_fderiv_apply (NativeGravityFirstJet.contDiffAt_volM (hKdet M hM))
    ((NativeGravityFirstJet.continuous_liftL.clm_apply continuous_const).continuousAt)
    ).continuousWithinAt

theorem continuousOn_chG (μ : Fin 4) : ContinuousOn (chG D μ) Ke := fun M hM =>
  (contDiffAt_gammaM D μ (hKdet M hM)).continuousAt.continuousWithinAt

theorem continuousOn_chDG (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) : ContinuousOn (chDG D t μ) Ke :=
  fun M hM => (continuousAt_fderiv_apply (contDiffAt_gammaM D μ (hKdet M hM))
    ((NativeGravityFirstJet.continuous_liftL.clm_apply continuous_const).continuousAt)
    ).continuousWithinAt

end Slots

/-! ### The trilinear form of the slot fields -/

section Tri

open NativeDensity NativeDirac NativeDiracLimit

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

/-- The trilinear form `(Φ̄, A, w) ↦ Re(c Φ̄(A w))`. -/
def triL (c : ℂ) : CoSpinor 𝓢 →L[ℝ] Spin 𝓢 →L[ℝ] 𝓢 →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ 𝓢 𝓢 ℝ).comp (bForm c)

theorem triL_apply (c : ℂ) (Φ : CoSpinor 𝓢) (A : Spin 𝓢) (w : 𝓢) :
    triL c Φ A w = bForm c Φ (A w) := rfl

theorem norm_triL_le (c : ℂ) (Φ : CoSpinor 𝓢) (A : Spin 𝓢) (w : 𝓢) :
    ‖triL c Φ A w‖ ≤ ‖c‖₊ * ‖Φ‖ * ‖A‖ * ‖w‖ := by
  rw [triL_apply, bForm_apply, Real.norm_eq_abs, coe_nnnorm]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (Φ.le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)

/-- The coefficient on `Ψ̄ ⊗ T_μΨ`: `δΞ_μ[t] = dv γ W + v dγ W + v γ dW`. -/
def c1 (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) : Spin 𝓢 :=
  (S.dv t • S.γ μ) * S.Wl μ + (S.v • S.dγ μ t) * S.Wl μ + (S.v • S.γ μ) * S.dWl μ t

/-- The coefficient on `T_μΨ̄ ⊗ Ψ`: `δΞ'_μ[t] = W' dv γ + dW' v γ + W' v dγ`. -/
def c2 (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) : Spin 𝓢 :=
  S.Wr μ * (S.dv t • S.γ μ) + S.dWr μ t * (S.v • S.γ μ) + S.Wr μ * (S.v • S.dγ μ t)

/-- `Ξ_μ = v γ^μ W_μ`. -/
def c3 (S : Slots 𝔄 𝓗 𝓢 W') (μ : Fin 4) : Spin 𝓢 := (S.v • S.γ μ) * S.Wl μ

/-- `v γ^μ + h W'_μ v γ^μ` (the co-spinor-difference test term). -/
def c4 (S : Slots 𝔄 𝓗 𝓢 W') (μ : Fin 4) : Spin 𝓢 :=
  S.v • S.γ μ + S.h • (S.Wr μ * (S.v • S.γ μ))

/-- `Ξ'_μ = W'_μ v γ^μ`. -/
def c5 (S : Slots 𝔄 𝓗 𝓢 W') (μ : Fin 4) : Spin 𝓢 := S.Wr μ * (S.v • S.γ μ)

/-- `v γ^μ + h v γ^μ W_μ` (the spinor-difference test term). -/
def c6 (S : Slots 𝔄 𝓗 𝓢 W') (μ : Fin 4) : Spin 𝓢 :=
  S.v • S.γ μ + S.h • ((S.v • S.γ μ) * S.Wl μ)

/-- The Yukawa coefficient variation `dv 𝓜(H) + v 𝓜(η)`. -/
def c9 (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') : Spin 𝓢 :=
  S.dv t • S.YH + S.v • D.yukawa t.2.2.2.1

/-- `v 𝓜(H)`. -/
def c10 (S : Slots 𝔄 𝓗 𝓢 W') : Spin 𝓢 := S.v • S.YH

theorem spin_mul_apply' (A B : Spin 𝓢) (w : 𝓢) : (A * B) w = A (B w) := rfl

theorem Gμ_eq_tri (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    Gμ κ S t μ = triL (Complex.I / 2) S.Ψb (c1 S t μ) (S.Ψp μ) -
      triL (Complex.I / 2) (S.Ψbp μ) (c2 S t μ) S.Ψ +
      triL (Complex.I / 2) (κ t.2.2.2.2.2.2.1) (c3 S μ) (S.Ψp μ) -
      triL (Complex.I / 2) (κ (t.2.2.2.2.2.2.2 μ)) (c4 S μ) S.Ψ -
      triL (Complex.I / 2) (κ t.2.2.2.2.2.2.1) (c5 S μ) S.Ψ +
      triL (Complex.I / 2) S.Ψb (c6 S μ) (t.2.2.2.2.2.1 μ) +
      triL (Complex.I / 2) S.Ψb (c3 S μ) t.2.2.2.2.1 -
      triL (Complex.I / 2) (S.Ψbp μ) (c5 S μ) t.2.2.2.2.1 := by
  simp only [Gμ, triL_apply, c1, c2, c3, c4, c5, c6, bI, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, spin_mul_apply', map_add, map_smul, smul_eq_mul]
  ring

theorem G0_eq_tri (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') :
    G0 D κ S t = triL 1 S.Ψb (c9 D S t) S.Ψ + triL 1 (κ t.2.2.2.2.2.2.1) (c10 S) S.Ψ +
      triL 1 S.Ψb (c10 S) t.2.2.2.2.1 := by
  simp only [G0, triL_apply, c9, c10, bR, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, map_add, map_smul, smul_eq_mul]

theorem Λμ_eq_tri (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') (u : Dif 𝓢 W') (μ : Fin 4) :
    Λμ κ S t u μ =
      triL (Complex.I / 2) S.Ψb (S.dv t • S.γ μ + S.v • S.dγ μ t) (u.1 μ) -
      triL (Complex.I / 2) (κ (u.2 μ)) (S.dv t • S.γ μ + S.v • S.dγ μ t) S.Ψ +
      triL (Complex.I / 2) (κ t.2.2.2.2.2.2.1) (S.v • S.γ μ) (u.1 μ) -
      triL (Complex.I / 2) (κ (u.2 μ)) (S.v • S.γ μ) t.2.2.2.2.1 := by
  simp only [Λμ, triL_apply, bI, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    map_add, map_smul, smul_eq_mul]
  ring

end Tri

/-! ### Convergence of the metric variation of the spin connection -/

section DeltaOmega

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)
open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat readerOmega omegaLink)
open NativeGravityFirstJet (M4 asM4 coframeM liftM liftL dqLift dqLiftL)
open NativeDensity NativeDirac NativeDiracConv NativeDiracLimit

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- Chart coefficients of the coframe sequence, times a strongly convergent field. -/
theorem chart_bilin (H : CoHyp n y) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {Z' E W : Type*}
    [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : M4 → Z'} (hΦ : ContinuousOn Φ H.Ke)
    (B : Z' →L[ℝ] E →L[ℝ] W) {s : ℕ → 𝕋 → E} {s₀ : 𝕋 → E} (hs : LpTendsto volume p s s₀) :
    LpTendsto volume p (fun k z => B (Φ (pc (coframeM (y k)) z)) (s k z))
      (fun z => B (Φ (H.e₀ z)) (s₀ z)) :=
  lpTendsto_chart_gen hp H.hKe hΦ
    (fun k => (stronglyMeasurable_pc (fun x => Φ (coframeM (y k) x))).aestronglyMeasurable)
    H.tendstoInMeasure_e (fun k z => H.hval k _) H.e₀_mem B hs

/-- The shifted coframes converge to the same limit. -/
theorem lpTendsto_eP (H : CoHyp n y) (lam : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => coframeM (y k) (x + unitVec (n k) lam))) H.e₀ :=
  NativeGravityFirstJet.lpTendsto_unitVec H.hn (by norm_num) H.he lam

/-- Pair-chart coefficients `Φ(e_k, e_k(· + λ))` times a strongly convergent field. -/
theorem pair_bilin (H : CoHyp n y) (lam : Fin 4) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {Z' E W : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : M4 × M4 → Z'}
    (hΦ : ContinuousOn Φ (H.Ke ×ˢ H.Ke)) (B : Z' →L[ℝ] E →L[ℝ] W) {s : ℕ → 𝕋 → E}
    {s₀ : 𝕋 → E} (hs : LpTendsto volume p s s₀) :
    LpTendsto volume p
      (fun k z => B (Φ (pc (coframeM (y k)) z,
        pc (fun x => coframeM (y k) (x + unitVec (n k) lam)) z)) (s k z))
      (fun z => B (Φ (H.e₀ z, H.e₀ z)) (s₀ z)) :=
  lpTendsto_chart_gen hp (H.hKe.prod H.hKe) hΦ
    (fun k => (stronglyMeasurable_pc (fun x => Φ (coframeM (y k) x,
      coframeM (y k) (x + unitVec (n k) lam)))).aestronglyMeasurable)
    (tendstoInMeasure_prod H.tendstoInMeasure_e
      (tendstoInMeasure_of_lpTendsto two_ne_zero (lpTendsto_eP H lam)))
    (fun k z => ⟨H.hval k _, H.hval k _⟩)
    (H.e₀_mem.mono fun z hz => ⟨hz, hz⟩) B hs

theorem DεL_apply (e : M4) (eP q : Fin 4 → M4) (lam : Fin 4) (t : Jet 𝔄 𝓗 𝓢 W') :
    DεL e eP q lam t = liftL (eP lam) (t.2.1 lam) + dqLiftL e (eP lam) (q lam) t.1 := rfl

/-- **`R^0 δω_{μ,h}[t] → δω_μ[t]` strongly in `L²`**: the metric variation of the coframe-derived
spin connection along a fixed jet vector converges to the variation of the Levi-Civita
connection. -/
theorem lpTendsto_δω (H : CoHyp n y) (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    LpTendsto volume 2
      (fun k => pc (fun x => δωL (coframeM (y k) x)
        (fun lam => coframeM (y k) (x + unitVec (n k) lam)) (fun lam => qM (y k) lam x) μ t))
      (fun z => δωL (H.e₀ z) (fun _ => H.e₀ z) (fun lam => H.p lam z) μ t) := by
  have key : LpTendsto volume 2
      (fun k z => ∑ lam, ∑ i, ∑ j,
        ((liftL (pc (fun x => coframeM (y k) (x + unitVec (n k) lam)) z) (t.2.1 lam)) i j •
            omegaCoef μ lam i j (pc (coframeM (y k)) z) +
          (CoHyp.entryL i j (dqLiftL (pc (coframeM (y k)) z)
            (pc (fun x => coframeM (y k) (x + unitVec (n k) lam)) z) (pc (qM (y k) lam) z) t.1)) •
            omegaCoef μ lam i j (pc (coframeM (y k)) z) +
          pc (qM (y k) lam) z i j • fderiv ℝ (omegaCoef μ lam i j) (pc (coframeM (y k)) z)
            (liftL (pc (coframeM (y k)) z) t.1)))
      (fun z => ∑ lam, ∑ i, ∑ j,
        ((liftL (H.e₀ z) (t.2.1 lam)) i j • omegaCoef μ lam i j (H.e₀ z) +
          (CoHyp.entryL i j (dqLiftL (H.e₀ z) (H.e₀ z) (H.p lam z) t.1)) •
            omegaCoef μ lam i j (H.e₀ z) +
          H.p lam z i j • fderiv ℝ (omegaCoef μ lam i j) (H.e₀ z) (liftL (H.e₀ z) t.1))) := by
    refine lpTendsto_finset_sum _ fun lam _ => lpTendsto_finset_sum _ fun i _ =>
      lpTendsto_finset_sum _ fun j _ => ?_
    refine LpTendsto.add (LpTendsto.add ?_ ?_) ?_
    · -- the lifted test differences against the connection coefficients
      have hΦ : ContinuousOn (fun q : M4 × M4 => (liftL q.2 (t.2.1 lam)) i j •
          omegaCoef μ lam i j q.1) (H.Ke ×ˢ H.Ke) := by
        refine ContinuousOn.smul (f := fun q : M4 × M4 => (liftL q.2 (t.2.1 lam)) i j)
          (g := fun q : M4 × M4 => omegaCoef μ lam i j q.1) ?_ ?_
        · exact ((continuous_apply j).comp ((continuous_apply i).comp
            ((NativeGravityFirstJet.continuous_liftL.comp continuous_snd).clm_apply
              continuous_const))).continuousOn
        · exact (continuousOn_omegaCoef μ lam i j H.hKdet).comp continuous_fst.continuousOn
            fun q hq => hq.1
      have := pair_bilin H lam (p := 2) (by norm_num) hΦ
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] M4 →L[ℝ] M4).flip
        (LpTendsto.const (memLp_const (1 : ℝ)))
      simpa using this
    · -- the divided difference of the lift against the connection coefficients
      set Φ : M4 × M4 → M4 →L[ℝ] M4 := fun q => ContinuousLinearMap.smulRightL ℝ M4 M4
        ((CoHyp.entryL i j).comp ((ContinuousLinearMap.apply ℝ M4 t.1).comp (dqLiftL q.1 q.2)))
        (omegaCoef μ lam i j q.1) with hΦdef
      have hΦ : ContinuousOn Φ (H.Ke ×ˢ H.Ke) := by
        refine ContinuousOn.clm_apply ?_ ?_
        · refine ((ContinuousLinearMap.smulRightL ℝ M4 M4).continuous.comp ?_).continuousOn
          exact continuous_const.clm_comp (continuous_const.clm_comp
            NativeGravityFirstJet.continuous_dqLiftL)
        · exact (continuousOn_omegaCoef μ lam i j H.hKdet).comp continuous_fst.continuousOn
            fun q hq => hq.1
      have := pair_bilin H lam (p := 2) (by norm_num) hΦ
        (ContinuousLinearMap.id ℝ (M4 →L[ℝ] M4)) (H.hp lam)
      exact this
    · -- the connection coefficients' variation along the lifted test
      have hΦ : ContinuousOn (fun e : M4 => fderiv ℝ (omegaCoef μ lam i j) e (liftL e t.1))
          H.Ke := fun e he =>
        (continuousAt_fderiv_apply (contDiffAt_omegaCoef μ lam i j (H.hKdet e he))
          ((NativeGravityFirstJet.continuous_liftL.clm_apply continuous_const).continuousAt)
          ).continuousWithinAt
      exact chart_bilin H (p := 2) (by norm_num) hΦ
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] M4 →L[ℝ] M4).flip (H.lpTendsto_q_coord lam i j)
  refine key.congr (fun k => Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · simp only [pc, δωL_apply, DεL_apply, εL, ContinuousLinearMap.coe_comp',
      Function.comp_apply, πk_apply, Pi.add_apply, add_smul, CoHyp.entryL]
    rfl
  · simp only [δωL_apply, DεL_apply, εL, ContinuousLinearMap.coe_comp',
      Function.comp_apply, πk_apply, Pi.add_apply, add_smul, CoHyp.entryL]
    rfl

end DeltaOmega

/-! ### Convergence of the link-quotient variations `δW`, `δW'` -/

section DeltaW

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)
open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat readerOmega omegaLink)
open NativeGravityFirstJet (M4 asM4 coframeM liftM liftL dqLift dqLiftL)
open NativeDensity NativeDirac NativeDiracConv NativeDiracLimit

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

theorem contDiff_exp' {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [CompleteSpace 𝔅] :
    ContDiff ℝ ⊤ (exp : 𝔅 → 𝔅) := by
  have : AnalyticOnNhd ℝ (exp : 𝔅 → 𝔅) Set.univ := fun x _ => exp_analytic x
  exact contDiffOn_univ.1 this.contDiffOn_of_completeSpace

theorem continuous_fderiv_exp {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [CompleteSpace 𝔅] :
    Continuous (fderiv ℝ (exp : 𝔅 → 𝔅)) :=
  contDiff_exp'.continuous_fderiv (by simp)

theorem fderiv_exp_zero {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [CompleteSpace 𝔅] :
    fderiv ℝ (exp : 𝔅 → 𝔅) 0 = ContinuousLinearMap.id ℝ 𝔅 :=
  (hasFDerivAt_exp_zero (𝕂 := ℝ)).fderiv

theorem continuous_mulRight : Continuous (mulRight : Spin 𝓢 → Spin 𝓢 →L[ℝ] Spin 𝓢) :=
  (ContinuousLinearMap.mul ℝ (Spin 𝓢)).flip.continuous

theorem continuous_mulLeft : Continuous (mulLeft : Spin 𝓢 → Spin 𝓢 →L[ℝ] Spin 𝓢) :=
  (ContinuousLinearMap.mul ℝ (Spin 𝓢)).continuous

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢)

/-- The coefficient of `σ(δω)` in `δW`, as a function of `(hσ(ω), hA)`. -/
def Γ1 (q : Spin 𝓢 × 𝔄) : M4 →L[ℝ] Spin 𝓢 :=
  (mulRight (exp (D.ρSL q.2))).comp ((fderiv ℝ exp q.1).comp (σL D))

/-- The internal part of `δW`, as a function of `(hσ(ω), hA)`. -/
def Γ2 (a : 𝔄) (q : Spin 𝓢 × 𝔄) : Spin 𝓢 := exp q.1 * D.ρSL (fderiv ℝ exp q.2 a)

/-- The internal part of `δW'`. -/
def Γ3 (a : 𝔄) (q : Spin 𝓢 × 𝔄) : Spin 𝓢 := D.ρSL (fderiv ℝ exp (-q.2) (-a)) * exp (-q.1)

/-- The coefficient of `σ(δω)` in `δW'`. -/
def Γ4 (q : Spin 𝓢 × 𝔄) : M4 →L[ℝ] Spin 𝓢 :=
  (mulLeft (D.ρSL (exp (-q.2)))).comp ((fderiv ℝ exp (-q.1)).comp (-σL D))

theorem continuous_Γ1 : Continuous (Γ1 D) :=
  (continuous_mulRight.comp ((NormedSpace.exp_continuous).comp
    (D.ρSL.continuous.comp continuous_snd))).clm_comp
    ((continuous_fderiv_exp.comp continuous_fst).clm_comp continuous_const)

theorem continuous_Γ2 (a : 𝔄) : Continuous (Γ2 D a) :=
  (NormedSpace.exp_continuous.comp continuous_fst).mul
    (D.ρSL.continuous.comp ((continuous_fderiv_exp.comp continuous_snd).clm_apply
      continuous_const))

theorem continuous_Γ3 (a : 𝔄) : Continuous (Γ3 D a) :=
  (D.ρSL.continuous.comp ((continuous_fderiv_exp.comp continuous_snd.neg).clm_apply
      continuous_const)).mul (NormedSpace.exp_continuous.comp continuous_fst.neg)

theorem continuous_Γ4 : Continuous (Γ4 D) :=
  (continuous_mulLeft.comp (D.ρSL.continuous.comp
    (NormedSpace.exp_continuous.comp continuous_snd.neg))).clm_comp
    ((continuous_fderiv_exp.comp continuous_fst.neg).clm_comp continuous_const)

theorem Γ1_zero : Γ1 D 0 = σL D := by
  ext1 M
  simp [Γ1, fderiv_exp_zero]

theorem Γ2_zero (a : 𝔄) : Γ2 D a 0 = D.ρSL a := by
  simp [Γ2, fderiv_exp_zero]

theorem Γ3_zero (a : 𝔄) : Γ3 D a 0 = -D.ρSL a := by
  simp [Γ3, fderiv_exp_zero]

theorem Γ4_zero : Γ4 D 0 = -σL D := by
  ext1 M
  simp [Γ4, fderiv_exp_zero]

/-- `δW_μ[t] = Γ1(hσω, hA)(δω[t]) + Γ2(a_μ)(hσω, hA)` at every node. -/
theorem dWl_eq {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) (μ : Fin 4)
    (t : Jet 𝔄 𝓗 𝓢 W') :
    (gridSlots (W' := W') D y x).dWl μ t =
      Γ1 D ((N : ℝ)⁻¹ • σL D (ωM y μ x), (N : ℝ)⁻¹ • gauge y μ x)
        (δωL (coframeM y x) (fun lam => coframeM y (x + unitVec N lam)) (fun lam => qM y lam x) μ t) +
      Γ2 D (t.2.2.1 μ) ((N : ℝ)⁻¹ • σL D (ωM y μ x), (N : ℝ)⁻¹ • gauge y μ x) := by
  simp only [gridSlots, δWL, Γ1, Γ2, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, map_smul, mulLeft_apply, ContinuousLinearMap.proj_apply, πa_apply]

/-- `δW'_μ[t] = Γ3(a_μ)(hσω, hA) + Γ4(hσω, hA)(δω[t])` at every node. -/
theorem dWr_eq {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) (μ : Fin 4)
    (t : Jet 𝔄 𝓗 𝓢 W') :
    (gridSlots (W' := W') D y x).dWr μ t =
      Γ3 D (t.2.2.1 μ) ((N : ℝ)⁻¹ • σL D (ωM y μ x), (N : ℝ)⁻¹ • gauge y μ x) +
      Γ4 D ((N : ℝ)⁻¹ • σL D (ωM y μ x), (N : ℝ)⁻¹ • gauge y μ x)
        (δωL (coframeM y x) (fun lam => coframeM y (x + unitVec N lam)) (fun lam => qM y lam x) μ t) := by
  simp only [gridSlots, δWRL, Γ3, Γ4, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, map_smul, mulLeft_apply, mulRight_apply, ContinuousLinearMap.proj_apply,
    πa_apply, ContinuousLinearMap.neg_apply, map_neg, Data.ρSL_apply]

/-- The scaled link arguments `(hσ(ω_{μ,h}), hA_{μ,h})` tend to `0` in measure and are
uniformly bounded. -/
theorem linkArgs (H : CoHyp n y) (μ : Fin 4) :
    TendstoInMeasure volume (fun k => pc (fun x => ((n k : ℝ)⁻¹ • σL D (ωM (y k) μ x),
      (n k : ℝ)⁻¹ • gauge (y k) μ x))) atTop 0 ∧
    ∃ R, ∀ k z, ‖pc (fun x => ((n k : ℝ)⁻¹ • σL D (ωM (y k) μ x),
      (n k : ℝ)⁻¹ • gauge (y k) μ x)) z‖ ≤ R := by
  have hms := NativeCriticalGrid.tendsto_meshSup H.hn (A := fun k => gauge (y k) μ)
    (H.hA μ).memLp_lim (H.hA μ).tendsto
  obtain ⟨MA, hMA⟩ := hms.bddAbove_range
  have hZb : ∀ k (x : Grid (n k)), ‖(n k : ℝ)⁻¹ • gauge (y k) μ x‖ ≤
      NativeCriticalGrid.meshSup (gauge (y k) μ) := fun k x => by
    rw [norm_smul, Real.norm_of_nonneg (hpos_inv (n k)).le]
    exact NativeCriticalGrid.le_meshSup (N := n k) _ x
  have hZ : TendstoInMeasure volume (fun k => pc (fun x => (n k : ℝ)⁻¹ • gauge (y k) μ x))
      atTop 0 := tendstoInMeasure_zero_of_norm_le hms fun k z => hZb k _
  have hpair := tendstoInMeasure_prod (H.tendstoInMeasure_hσω D μ) hZ
  refine ⟨hpair.congr_right (Eventually.of_forall fun z => rfl), max (‖σL D‖ * H.c) MA,
    fun k z => ?_⟩
  refine norm_prod_le_iff.2 ⟨(H.norm_hσω_le D k _ μ).trans (le_max_left _ _), ?_⟩
  exact (hZb k _).trans ((hMA (Set.mem_range_self k)).trans (le_max_right _ _))

/-- **`R^0 δW_{μ,h}[t] → σ(δω_μ[t]) + ρ_S(a_μ)` strongly in `L²`.** -/
theorem lpTendsto_dWl (H : CoHyp n y) (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => (gridSlots (W' := W') D (y k) x).dWl μ t))
      (fun z => contdB D (H.e₀ z) (fun lam => H.p lam z) μ t) := by
  obtain ⟨hf, R, hR⟩ := linkArgs D H μ
  obtain ⟨h1, M1, hM1⟩ := tendstoInMeasure_comp_ball hf hR
    ((continuous_Γ1 D).continuousOn (s := closedBall 0 R))
  obtain ⟨h2, M2, hM2⟩ := tendstoInMeasure_comp_ball hf hR
    ((continuous_Γ2 D (t.2.2.1 μ)).continuousOn (s := closedBall 0 R))
  have hA := LpProductContinuity.LpTendsto.coeff (p := 2) (by norm_num)
    (fun k => (stronglyMeasurable_pc (fun x => Γ1 D ((n k : ℝ)⁻¹ • σL D (ωM (y k) μ x),
      (n k : ℝ)⁻¹ • gauge (y k) μ x))).aestronglyMeasurable) h1
    (fun k => Eventually.of_forall fun z => hM1 k z) (lpTendsto_δω H t μ)
  have hB := lpTendsto_of_bdd_tendstoInMeasure (p := 2) (by norm_num)
    (fun k => (stronglyMeasurable_pc (fun x => Γ2 D (t.2.2.1 μ) ((n k : ℝ)⁻¹ • σL D (ωM (y k) μ x),
      (n k : ℝ)⁻¹ • gauge (y k) μ x))).aestronglyMeasurable) h2
    (fun k => Eventually.of_forall fun z => hM2 k z)
  refine (hA.add hB).congr (fun k => Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · simp only [Pi.add_apply, pc]
    rw [dWl_eq]
    rfl
  · simp only [Pi.add_apply, Pi.zero_apply, Γ1_zero, Γ2_zero]
    rfl

/-- **`R^0 δW'_{μ,h}[t] → -(σ(δω_μ[t]) + ρ_S(a_μ))` strongly in `L²`.** -/
theorem lpTendsto_dWr (H : CoHyp n y) (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => (gridSlots (W' := W') D (y k) x).dWr μ t))
      (fun z => -contdB D (H.e₀ z) (fun lam => H.p lam z) μ t) := by
  obtain ⟨hf, R, hR⟩ := linkArgs D H μ
  obtain ⟨h3, M3, hM3⟩ := tendstoInMeasure_comp_ball hf hR
    ((continuous_Γ3 D (t.2.2.1 μ)).continuousOn (s := closedBall 0 R))
  obtain ⟨h4, M4', hM4⟩ := tendstoInMeasure_comp_ball hf hR
    ((continuous_Γ4 D).continuousOn (s := closedBall 0 R))
  have hA := lpTendsto_of_bdd_tendstoInMeasure (p := 2) (by norm_num)
    (fun k => (stronglyMeasurable_pc (fun x => Γ3 D (t.2.2.1 μ) ((n k : ℝ)⁻¹ • σL D (ωM (y k) μ x),
      (n k : ℝ)⁻¹ • gauge (y k) μ x))).aestronglyMeasurable) h3
    (fun k => Eventually.of_forall fun z => hM3 k z)
  have hB := LpProductContinuity.LpTendsto.coeff (p := 2) (by norm_num)
    (fun k => (stronglyMeasurable_pc (fun x => Γ4 D ((n k : ℝ)⁻¹ • σL D (ωM (y k) μ x),
      (n k : ℝ)⁻¹ • gauge (y k) μ x))).aestronglyMeasurable) h4
    (fun k => Eventually.of_forall fun z => hM4 k z) (lpTendsto_δω H t μ)
  refine (hA.add hB).congr (fun k => Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · simp only [Pi.add_apply, pc]
    rw [dWr_eq]
    rfl
  · simp only [Pi.add_apply, Pi.zero_apply, Γ3_zero, Γ4_zero, contdB,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearMap.proj_apply, πa_apply]
    abel

end DeltaW

end

end RenewalGeometry.NativeDiracConvergence
