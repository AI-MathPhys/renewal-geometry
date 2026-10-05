/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeBankContinuity

/-!
# Consistency relative to the reconstructed fields
  (`thm:native-firstvariation-no-band`, final paragraph)

Einstein–SM action-closure manuscript, `thm:native-firstvariation-no-band`, last paragraph: *if
the complete unfiltered reconstructed coframes stay in the same compact nondegenerate chart and the
ordinary connection first differences converge strongly to `∂A`, then the sectorwise consistency
errors relative to the complete unfiltered reconstructed fields tend to zero*.  The gravitational
row is `NativeGravityFirstJet.native_gravity_firstjet_reconstructed`; this file supplies the
Yang–Mills, Higgs and Dirac–Yukawa rows and assembles all four.

## Rendering (as in the sector files)

Unit torus `𝕋⁴` (the side-`2π` box is the dilation `x ↦ 2πx`), grid `(ℤ/N)⁴`, `h = 1/N`, raw
reconstruction `R_h^0 = pc`, trivialised bundles, fixed coefficient bank `D` (sectorwise).  The
"complete unfiltered reconstructed fields" are continuum fields on `𝕋⁴` with first-jet arrays:
coframes `f_h` with jets `g_h`, connections `A_h^rec` with jets `∂A_h^rec`, Higgs fields
`H_h^rec` with jets `∂H_h^rec`, spinors `Ψ_h^rec`, `χ_h^rec` with jets `u_h^rec`.  Their hypotheses
are the comparison estimates `eq:native-reconstruction-comparison` with the raw reconstructions of
the records — `‖f_h - R^0e_h‖_{L²} → 0`, `‖g_h - R^0D⁺e_h‖_{L²} → 0`, `‖A_h^rec - R^0A_h‖_{L⁴} → 0`,
`‖∂A_h^rec - R^0D⁺A_h‖_{L²} → 0`, the same for the Higgs field, `‖Ψ_h^rec - R^0Ψ_h‖_{L²} → 0` with
uniform `L⁴` bounds and `u_h^rec - R^0D⁺Ψ_h ⇀ 0` weakly and boundedly in `L²` — which the
trigonometric interpolant `𝓘_h^trig` satisfies (`TorusTrigReconstruction`:
`eLpNorm_trigInterp_sub_pc_le_grad`, `tendsto_sobSq_trigLp_sub`); the coframe chart condition is
the paper's own hypothesis.

## Main results

* `firstVarCont_unif` (continuity of the continuum Yang–Mills covector, uniform on bounded tests):
  `e_k → e` in `L²` in a compact nondegenerate chart, `A_k → A` in `L⁴`, `F_k → F` in `L²`.
* `curvature_identification`: if the ordinary first differences `R^0 D⁺_μ A_ν → P_{μν}` strongly,
  then `F_{μν} = P_{μν} - P_{νμ} + [A_μ, A_ν]` a.e. (the literal curvature limit is the complete
  curvature of the strong first jet).
* `native_YM_reconstructed`, `native_Higgs_reconstructed`, `native_Dirac_reconstructed`: the
  sectorwise consistency errors relative to the reconstructed fields tend to zero uniformly on
  `C²` test balls.
* `native_reconstructed_closure` (**the final paragraph of `thm:native-firstvariation-no-band`**,
  from `(N1)–(N4)`): after the extraction of `NativeAllSectorGraph.native_all_sector_closure`, all
  four sectorwise errors relative to the reconstructed fields tend to zero.
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace RenewalGeometry.NativeReconstructed

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

local instance fact_one_le_two_nr : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_nr : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance holder221_nr : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
local instance holder442_nr : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)
open NativeGravityFirstJet (M4 asM4 coframeM liftL)

/-! ### Generic tools -/

section Generic

variable {Z' E W : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Chart coefficients of continuum coframes** (`lem:products`): if `f_k → e₀` in `L²` with values
in a compact chart `K` and `Φ` is continuous on `K`, then `B(Φ(f_k), s_k) → B(Φ(e₀), s)` in `L^p`
whenever `s_k → s` in `L^p`. -/
theorem chart {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {K : Set M4} (hK : IsCompact K)
    {f : ℕ → 𝕋 → M4} {e₀ : 𝕋 → M4} (hf : LpTendsto volume 2 f e₀) (hfK : ∀ k z, f k z ∈ K)
    {Φ : M4 → Z'} (hΦ : ContinuousOn Φ K) (B : Z' →L[ℝ] E →L[ℝ] W) {s : ℕ → 𝕋 → E}
    {s₀ : 𝕋 → E} (hs : LpTendsto volume p s s₀) :
    LpTendsto volume p (fun k z => B (Φ (f k z)) (s k z)) (fun z => B (Φ (e₀ z)) (s₀ z)) :=
  NativeDiracConvergence.lpTendsto_chart_gen hp hK hΦ
    (fun k => HomogeneousJetVariation.aestronglyMeasurable_comp_continuousOn hK.isClosed hΦ
      (hf.memLp k).1 (Eventually.of_forall (hfK k)))
    (NativeDiracConv.tendstoInMeasure_of_lpTendsto two_ne_zero hf) hfK
    (NativeDiracConv.ae_mem_of_lpTendsto two_ne_zero hK.isClosed hf hfK) B hs

/-- A chart coefficient alone. -/
theorem chart₀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {K : Set M4} (hK : IsCompact K)
    {f : ℕ → 𝕋 → M4} {e₀ : 𝕋 → M4} (hf : LpTendsto volume 2 f e₀) (hfK : ∀ k z, f k z ∈ K)
    {Φ : M4 → Z'} (hΦ : ContinuousOn Φ K) :
    LpTendsto volume p (fun k z => Φ (f k z)) (fun z => Φ (e₀ z)) := by
  have := chart hp hK hf hfK hΦ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Z' →L[ℝ] Z').flip
    (LpTendsto.const (memLp_const (1 : ℝ)))
  simpa using this

/-- `∫ ‖G_k - G‖ → 0` along strong `L¹` convergence. -/
theorem integral_norm_sub_tendsto {G : ℕ → 𝕋 → E} {G₀ : 𝕋 → E}
    (hG : LpTendsto volume 1 G G₀) :
    Tendsto (fun k => ∫ z, ‖G k z - G₀ z‖) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG.tendsto
  rw [ENNReal.toReal_zero] at h
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [eLpNorm_one_eq_lintegral_enorm]
  change _ = ∫ z, ‖(G k - G₀) z‖
  rw [integral_norm_eq_lintegral_enorm (((hG.memLp k).sub hG.memLp_lim).1)]

/-- `|∫ G_k(J) - ∫ G(J)| ≤ (∫ ‖G_k - G‖) c` for covector fields in `L¹` and jets bounded by `c`. -/
theorem abs_integral_apply_sub_le {G G₀ : 𝕋 → E →L[ℝ] ℝ} (hG : Integrable G volume)
    (hG₀ : Integrable G₀ volume) {J : 𝕋 → E} (hJ : Continuous J) {c : ℝ}
    (hJc : ∀ z, ‖J z‖ ≤ c) :
    |(∫ z, G z (J z)) - ∫ z, G₀ z (J z)| ≤ (∫ z, ‖G z - G₀ z‖) * c := by
  have hm : ∀ {L : 𝕋 → E →L[ℝ] ℝ}, Integrable L volume → Integrable (fun z => L z (J z)) volume :=
    fun {L} hL => Integrable.mono' (hL.norm.mul_const c)
      (LpProductContinuity.aestronglyMeasurable_apply hL.1 hJ.aestronglyMeasurable)
      (Eventually.of_forall fun z => ((L z).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hJc z) (norm_nonneg _)))
  rw [← integral_sub (hm hG) (hm hG₀), ← Real.norm_eq_abs, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((hG.sub hG₀).norm.mul_const c)
    (Eventually.of_forall fun z => ?_)
  rw [← ContinuousLinearMap.sub_apply']
  exact ((G z - G₀ z).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hJc z) (norm_nonneg _))

end Generic

/-! ### The Yang–Mills row -/

section YM

open NativeYMMetric NativeYMVariation

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The complete curvature of a continuum connection with first jets**
`F_{μν} = ∂_μA_ν - ∂_νA_μ + [A_μ, A_ν]`, where `dA μ ν` is the jet `∂_μA_ν`. -/
def recCurv (A : Fin 4 → 𝕋 → 𝔸) (dA : Fin 4 → Fin 4 → 𝕋 → 𝔸) (μ ν : Fin 4) (z : 𝕋) : 𝔸 :=
  dA μ ν z - dA ν μ z + (A μ z * A ν z - A ν z * A μ z)

/-- Strong first-jet convergence of the connections gives strong `L²` convergence of the complete
curvature (`L⁴ × L⁴ → L²` for the commutator). -/
theorem lpTendsto_recCurv {A : ℕ → Fin 4 → 𝕋 → 𝔸} {A₀ : Fin 4 → 𝕋 → 𝔸}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => A k μ) (A₀ μ)) {dA : ℕ → Fin 4 → Fin 4 → 𝕋 → 𝔸}
    {P : Fin 4 → Fin 4 → 𝕋 → 𝔸} (hdA : ∀ μ ν, LpTendsto volume 2 (fun k => dA k μ ν) (P μ ν))
    (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => recCurv (A k) (dA k) μ ν) (recCurv A₀ P μ ν) := by
  have h1 := LpTendsto.bilin (p := 4) (q := 4) (r := 2) (ContinuousLinearMap.mul ℝ 𝔸) (hA μ) (hA ν)
  have h2 := LpTendsto.bilin (p := 4) (q := 4) (r := 2) (ContinuousLinearMap.mul ℝ 𝔸) (hA ν) (hA μ)
  exact (((hdA μ ν).sub (hdA ν μ)).add (h1.sub h2)).congr
    (fun k => Eventually.of_forall fun z => by simp [recCurv])
    (Eventually.of_forall fun z => by simp [recCurv])

/-- The antisymmetric extension of strongly convergent two-forms converges strongly. -/
theorem lpTendsto_FextC {F : ℕ → Fin 4 → Fin 4 → 𝕋 → 𝔸} {F₀ : Fin 4 → Fin 4 → 𝕋 → 𝔸}
    (hF : ∀ μ ν, μ < ν → LpTendsto volume 2 (fun k => F k μ ν) (F₀ μ ν)) (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k y => FextC (F k) y μ ν) (fun y => FextC F₀ y μ ν) := by
  by_cases h1 : μ < ν
  · exact (hF μ ν h1).congr (fun k => Eventually.of_forall fun y => by simp [FextC, h1])
      (Eventually.of_forall fun y => by simp [FextC, h1])
  · by_cases h2 : ν < μ
    · exact (hF ν μ h2).neg.congr (fun k => Eventually.of_forall fun y => by simp [FextC, h1, h2])
        (Eventually.of_forall fun y => by simp [FextC, h1, h2])
    · exact (LpTendsto.const (p := 2) (ν := (volume : Measure 𝕋))
        (MemLp.zero : MemLp (0 : 𝕋 → 𝔸) 2 volume)).congr
        (fun k => Eventually.of_forall fun y => by simp [FextC, h1, h2])
        (Eventually.of_forall fun y => by simp [FextC, h1, h2])

/-- Pointwise Lipschitz dependence of `d_A a` on the connection. -/
theorem norm_DaT_sub_le {M : NNReal} (A A' : Fin 4 → 𝕋 → 𝔸) (a : C1Test 𝔸) (ha : GaugeBound M a)
    (y : 𝕋) (ρ σ : Fin 4) :
    ‖DaT A a y ρ σ - DaT A' a y ρ σ‖ ≤ M * (2 * (‖A ρ y - A' ρ y‖ + ‖A σ y - A' σ y‖)) := by
  have e : DaT A a y ρ σ - DaT A' a y ρ σ =
      ((A ρ y - A' ρ y) * a.a σ y - a.a σ y * (A ρ y - A' ρ y)) +
        (a.a ρ y * (A σ y - A' σ y) - (A σ y - A' σ y) * a.a ρ y) := by
    simp only [DaT, sub_mul, mul_sub]; abel
  rw [e]
  have h3 := ha.a_le σ y
  have h4 := ha.a_le ρ y
  have n1 := norm_mul_le (A ρ y - A' ρ y) (a.a σ y)
  have n2 := norm_mul_le (a.a σ y) (A ρ y - A' ρ y)
  have n3 := norm_mul_le (a.a ρ y) (A σ y - A' σ y)
  have n4 := norm_mul_le (A σ y - A' σ y) (a.a ρ y)
  have hA1 := norm_nonneg (A ρ y - A' ρ y)
  have hA2 := norm_nonneg (A σ y - A' σ y)
  calc _ ≤ (‖(A ρ y - A' ρ y) * a.a σ y‖ + ‖a.a σ y * (A ρ y - A' ρ y)‖) +
        (‖a.a ρ y * (A σ y - A' σ y)‖ + ‖(A σ y - A' σ y) * a.a ρ y‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))
    _ ≤ M * (2 * (‖A ρ y - A' ρ y‖ + ‖A σ y - A' σ y‖)) := by nlinarith

/-- The `L²` distance of the gauge-test covariant derivatives along two connections. -/
theorem toReal_eLpNorm_DaT_sub_le {M : NNReal} {A A' : Fin 4 → 𝕋 → 𝔸}
    (hA : ∀ μ, MemLp (A μ) 2 volume) (hA' : ∀ μ, MemLp (A' μ) 2 volume) (a : C1Test 𝔸)
    (ha : GaugeBound M a) (ρ σ : Fin 4) :
    (eLpNorm ((fun y => DaT A a y ρ σ) - fun y => DaT A' a y ρ σ) 2 volume).toReal ≤
      M * (2 * ((eLpNorm (A ρ - A' ρ) 2 volume).toReal +
        (eLpNorm (A σ - A' σ) 2 volume).toReal)) := by
  have hg : MemLp (fun y => (M : ℝ) * (2 * (‖A ρ y - A' ρ y‖ + ‖A σ y - A' σ y‖))) 2 volume :=
    ((((hA ρ).sub (hA' ρ)).norm.add ((hA σ).sub (hA' σ)).norm).const_mul 2).const_mul M
  refine (toReal_eLpNorm_mono hg fun y => ?_).trans ?_
  · rw [Real.norm_of_nonneg (by positivity)]
    exact norm_DaT_sub_le A A' a ha y ρ σ
  · rw [toReal_eLpNorm_const_mul (f := fun y => 2 * (‖A ρ y - A' ρ y‖ + ‖A σ y - A' σ y‖))
      M.coe_nonneg, toReal_eLpNorm_const_mul (f := fun y => ‖A ρ y - A' ρ y‖ + ‖A σ y - A' σ y‖)
      (by norm_num : (0 : ℝ) ≤ 2)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num)) M.coe_nonneg
    have h1 := toReal_eLpNorm_add_le ((hA ρ).sub (hA' ρ)).norm ((hA σ).sub (hA' σ)).norm
    have e1 : eLpNorm (fun y => ‖A ρ y - A' ρ y‖) 2 volume = eLpNorm (A ρ - A' ρ) 2 volume :=
      eLpNorm_norm _
    have e2 : eLpNorm (fun y => ‖A σ y - A' σ y‖) 2 volume = eLpNorm (A σ - A' σ) 2 volume :=
      eLpNorm_norm _
    exact (le_of_eq (by rfl)).trans (h1.trans (le_of_eq (by rw [← e1, ← e2]; rfl)))

/-- The metric-row term `|∫ k_{αβ} g_k - ∫ k_{αβ} g| ≤ M ‖g_k - g‖_{L¹}`. -/
theorem abs_integral_kt_mul_sub_le {M : NNReal} (kt : C(𝕋, Cof)) (hkt : MetricBound M kt)
    {g g' : 𝕋 → ℝ} (hg : Integrable g volume) (hg' : Integrable g' volume) (α β : Fin 4) :
    |(∫ y, kt y α β * g y) - ∫ y, kt y α β * g' y| ≤
      (M : ℝ) * (eLpNorm (g - g') 1 volume).toReal := by
  have i1 := integrable_kt_mul kt hkt hg α β
  have i2 := integrable_kt_mul kt hkt hg' α β
  refine (abs_integral_sub_le i1 i2).trans ?_
  have hb : eLpNorm ((fun y => kt y α β * g y) - fun y => kt y α β * g' y) 1 volume ≤
      ENNReal.ofReal M * eLpNorm (g - g') 1 volume := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun y => ?_) 1
    simp only [Pi.sub_apply, ← mul_sub, norm_mul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have h1 := norm_le_pi_norm (kt y α) β
    have h2 := norm_le_pi_norm (kt y) α
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (h2.trans (hkt.k_le y))
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ((memLp_one_iff_integrable.2 hg).sub (memLp_one_iff_integrable.2 hg')).2.ne) hb
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal M.coe_nonneg] at this

set_option maxHeartbeats 1600000 in
-- the bound is a sum of `4⁶ + 2·4⁴` explicit terms
/-- **Continuity of the continuum Yang–Mills first variation, uniformly on bounded tests**
(`prop:reduced-continuity`, Yang–Mills sector, torus rendering).  If continuum coframes
`e_k → e₀` in `L²` with values in a compact set `K` of nondegenerate coframes, connections
`A_k → A₀` in `L⁴` and curvatures `F_k → F₀` in `L²` (components `μ < ν`), then there are
`β_k → 0` with `|D𝒮_{YM}(e_k, A_k, F_k)[k, a] - D𝒮_{YM}(e₀, A₀, F₀)[k, a]| ≤ β_k` for all metric
tests `‖k‖_{C^{0,1}} ≤ M` and gauge tests `‖a‖_{C^{1,1}} ≤ M`. -/
theorem firstVarCont_unif (T : 𝔸 →L[ℝ] E) {K : Set Cof} (hK : IsCompact K) (hKGL : K ⊆ GLc)
    {e : ℕ → 𝕋 → Cof} {e₀ : 𝕋 → Cof} (he : LpTendsto volume 2 e e₀) (heK : ∀ k y, e k y ∈ K)
    {A : ℕ → Fin 4 → 𝕋 → 𝔸} {A₀ : Fin 4 → 𝕋 → 𝔸}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => A k μ) (A₀ μ))
    {F : ℕ → Fin 4 → Fin 4 → 𝕋 → 𝔸} {F₀ : Fin 4 → Fin 4 → 𝕋 → 𝔸}
    (hF : ∀ μ ν, μ < ν → LpTendsto volume 2 (fun k => F k μ ν) (F₀ μ ν)) (M : NNReal) :
    ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧ ∀ k (kt : C(𝕋, Cof)) (a : C1Test 𝔸),
      MetricBound M kt → GaugeBound M a →
        |firstVarCont T (e k) (A k) (F k) kt a - firstVarCont T e₀ A₀ F₀ kt a| ≤ β k := by
  have hA2 : ∀ μ, LpTendsto volume 2 (fun k => A k μ) (A₀ μ) := fun μ =>
    (hA μ).mono two_ne_zero (by norm_num)
  have hFF : ∀ μ ν, LpTendsto volume 2 (fun k y => FextC (F k) y μ ν) (fun y => FextC F₀ y μ ν) :=
    lpTendsto_FextC hF
  have hip : ∀ μ ν ρ σ, LpTendsto volume 1
      (fun k y => ⟪T (FextC (F k) y μ ν), T (FextC (F k) y ρ σ)⟫)
      (fun y => ⟪T (FextC F₀ y μ ν), T (FextC F₀ y ρ σ)⟫) := fun μ ν ρ σ =>
    LpTendsto.bilin (p := 2) (q := 2) (r := 1) (innerSL ℝ (E := E)) ((hFF μ ν).clm T)
      ((hFF ρ σ).clm T)
  have hG1 : ∀ μ ν ρ σ α β, LpTendsto volume 1
      (fun k y => dCoef (e k y) (Eab α β) μ ν ρ σ * ⟪T (FextC (F k) y μ ν), T (FextC (F k) y ρ σ)⟫)
      (fun y => dCoef (e₀ y) (Eab α β) μ ν ρ σ * ⟪T (FextC F₀ y μ ν), T (FextC F₀ y ρ σ)⟫) :=
    fun μ ν ρ σ α β => chart (p := 1) ENNReal.one_ne_top hK he heK
      (continuousOn_dCoef_eval hKGL α β μ ν ρ σ) (ContinuousLinearMap.mul ℝ ℝ) (hip μ ν ρ σ)
  have hU : ∀ μ ν ρ σ μ' ν', LpTendsto volume 2
      (fun k y => ymCoef (e k y) μ ν ρ σ • T (FextC (F k) y μ' ν'))
      (fun y => ymCoef (e₀ y) μ ν ρ σ • T (FextC F₀ y μ' ν')) := fun μ ν ρ σ μ' ν' =>
    chart (p := 2) (by norm_num) hK he heK (continuousOn_ymCoef_eval hKGL μ ν ρ σ)
      (ContinuousLinearMap.lsmul ℝ ℝ) ((hFF μ' ν').clm T)
  set dA : ℕ → Fin 4 → Fin 4 → ℝ := fun k ρ σ =>
    (eLpNorm (A k ρ - A₀ ρ) 2 volume).toReal + (eLpNorm (A k σ - A₀ σ) 2 volume).toReal
    with hdA
  have hdA0 : ∀ ρ σ, Tendsto (fun k => dA k ρ σ) atTop (𝓝 0) := fun ρ σ => by
    simpa using (tendsto_toReal_sub (hA2 ρ)).add (tendsto_toReal_sub (hA2 σ))
  refine ⟨fun k => 1 / 4 * (
    (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ α, ∑ β, (M : ℝ) * (eLpNorm ((fun y =>
        dCoef (e k y) (Eab α β) μ ν ρ σ * ⟪T (FextC (F k) y μ ν), T (FextC (F k) y ρ σ)⟫) -
        fun y => dCoef (e₀ y) (Eab α β) μ ν ρ σ * ⟪T (FextC F₀ y μ ν), T (FextC F₀ y ρ σ)⟫) 1
          volume).toReal) +
    (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ((eLpNorm ((fun y => ymCoef (e k y) μ ν ρ σ •
        T (FextC (F k) y μ ν)) - fun y => ymCoef (e₀ y) μ ν ρ σ • T (FextC F₀ y μ ν)) 2
          volume).toReal * (‖T‖ * ((M : ℝ) * (2 * dA k ρ σ)) + ‖T‖ * ((M : ℝ) * CA A₀ ρ σ)) +
      (eLpNorm (fun y => ymCoef (e₀ y) μ ν ρ σ • T (FextC F₀ y μ ν)) 2 volume).toReal *
        (‖T‖ * ((M : ℝ) * (2 * dA k ρ σ))))) +
    (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ((eLpNorm ((fun y => ymCoef (e k y) μ ν ρ σ •
        T (FextC (F k) y ρ σ)) - fun y => ymCoef (e₀ y) μ ν ρ σ • T (FextC F₀ y ρ σ)) 2
          volume).toReal * (‖T‖ * ((M : ℝ) * (2 * dA k μ ν)) + ‖T‖ * ((M : ℝ) * CA A₀ μ ν)) +
      (eLpNorm (fun y => ymCoef (e₀ y) μ ν ρ σ • T (FextC F₀ y ρ σ)) 2 volume).toReal *
        (‖T‖ * ((M : ℝ) * (2 * dA k μ ν)))))), ?_, ?_⟩
  · have s1 := tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun μ _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun ν _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun ρ _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun σ _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun α _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun β _ =>
        (tendsto_toReal_sub (hG1 μ ν ρ σ α β)).const_mul (M : ℝ)
    have hδ : ∀ ρ σ, Tendsto (fun k => (M : ℝ) * (2 * dA k ρ σ)) atTop (𝓝 0) := fun ρ σ => by
      simpa using ((hdA0 ρ σ).const_mul 2).const_mul (M : ℝ)
    have s2 := tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun μ _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun ν _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun ρ _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun σ _ =>
        tendsto_b2 T (hδ ρ σ) ((M : ℝ) * CA A₀ ρ σ) (hU μ ν ρ σ μ ν)
    have s3 := tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun μ _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun ν _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun ρ _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun σ _ =>
        tendsto_b2 T (hδ μ ν) ((M : ℝ) * CA A₀ μ ν) (hU μ ν ρ σ ρ σ)
    simp only [mul_zero, Finset.sum_const_zero] at s1 s2 s3
    have h := ((s1.add s2).add s3).const_mul (1 / 4 : ℝ)
    rw [add_zero, add_zero, mul_zero] at h
    exact h
  · intro k kt a hkt ha
    have hAk4 : ∀ μ, MemLp (A k μ) 4 volume := fun μ => (hA μ).memLp k
    have hA₀4 : ∀ μ, MemLp (A₀ μ) 4 volume := fun μ => (hA μ).memLp_lim
    have hV : ∀ ρ σ, MemLp (fun y => T (DaT (A k) a y ρ σ)) 2 volume ∧
        MemLp (fun y => T (DaT A₀ a y ρ σ)) 2 volume ∧
        (eLpNorm ((fun y => T (DaT (A k) a y ρ σ)) - fun y => T (DaT A₀ a y ρ σ)) 2
          volume).toReal ≤ ‖T‖ * ((M : ℝ) * (2 * dA k ρ σ)) ∧
        (eLpNorm (fun y => T (DaT A₀ a y ρ σ)) 2 volume).toReal ≤
          ‖T‖ * ((M : ℝ) * CA A₀ ρ σ) := by
      intro ρ σ
      obtain ⟨hDk, -⟩ := memLp_DaT hAk4 a ha ρ σ
      obtain ⟨hD0, hD0b⟩ := memLp_DaT hA₀4 a ha ρ σ
      refine ⟨T.comp_memLp' hDk, T.comp_memLp' hD0, ?_, ?_⟩
      · have he' : ((fun y => T (DaT (A k) a y ρ σ)) - fun y => T (DaT A₀ a y ρ σ)) =
            fun y => T (((fun y => DaT (A k) a y ρ σ) - fun y => DaT A₀ a y ρ σ) y) := by
          funext y; simp [map_sub]
        rw [he']
        exact (toReal_eLpNorm_clm_le T (hDk.sub hD0)).trans (mul_le_mul_of_nonneg_left
          (toReal_eLpNorm_DaT_sub_le (fun μ => (hA2 μ).memLp k) (fun μ => (hA2 μ).memLp_lim) a ha
            ρ σ) (norm_nonneg T))
      · exact (toReal_eLpNorm_clm_le T hD0).trans (mul_le_mul_of_nonneg_left hD0b (norm_nonneg T))
    have hgk : ∀ μ ν ρ σ α β, Integrable (fun y => dCoef (e k y) (Eab α β) μ ν ρ σ *
        ⟪T (FextC (F k) y μ ν), T (FextC (F k) y ρ σ)⟫) volume :=
      fun μ ν ρ σ α β => ((hG1 μ ν ρ σ α β).memLp k).integrable le_rfl
    have hg0 : ∀ μ ν ρ σ α β, Integrable (fun y => dCoef (e₀ y) (Eab α β) μ ν ρ σ *
        ⟪T (FextC F₀ y μ ν), T (FextC F₀ y ρ σ)⟫) volume :=
      fun μ ν ρ σ α β => (hG1 μ ν ρ σ α β).memLp_lim.integrable le_rfl
    rw [firstVarCont_eq T (e k) (A k) (F k) kt a
        (fun μ ν ρ σ α β => integrable_kt_mul kt hkt (hgk μ ν ρ σ α β) α β)
        (fun μ ν ρ σ => integrable_inner_of_memLp ((hU μ ν ρ σ μ ν).memLp k) (hV ρ σ).1)
        (fun μ ν ρ σ => integrable_inner_of_memLp ((hU μ ν ρ σ ρ σ).memLp k) (hV μ ν).1),
      firstVarCont_eq T e₀ A₀ F₀ kt a
        (fun μ ν ρ σ α β => integrable_kt_mul kt hkt (hg0 μ ν ρ σ α β) α β)
        (fun μ ν ρ σ => integrable_inner_of_memLp (hU μ ν ρ σ μ ν).memLp_lim (hV ρ σ).2.1)
        (fun μ ν ρ σ => integrable_inner_of_memLp (hU μ ν ρ σ ρ σ).memLp_lim (hV μ ν).2.1)]
    refine abs_combo_le ?_ ?_ ?_
    · refine abs_sum6_sub_le _ _ _ fun μ ν ρ σ α β => ?_
      exact abs_integral_kt_mul_sub_le kt hkt (hgk μ ν ρ σ α β) (hg0 μ ν ρ σ α β) α β
    · refine abs_sum4_sub_le _ _ _ fun μ ν ρ σ => ?_
      exact term2_le ((hU μ ν ρ σ μ ν).memLp k) (hU μ ν ρ σ μ ν).memLp_lim (hV ρ σ).1
        (hV ρ σ).2.1 (hV ρ σ).2.2.1 (hV ρ σ).2.2.2
    · refine abs_sum4_sub_le _ _ _ fun μ ν ρ σ => ?_
      exact term2_le ((hU μ ν ρ σ ρ σ).memLp k) (hU μ ν ρ σ ρ σ).memLp_lim (hV μ ν).1
        (hV μ ν).2.1 (hV μ ν).2.2.1 (hV μ ν).2.2.2

end YM

/-! ### The Yang–Mills row relative to the reconstructed fields -/

section YMSector

open NativeDensity
open ShiftedJetAction (Grid)
open NativeDiracLimit (DTest testRec)
open NativeDiracConv (CoHyp)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (D : Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢) (T : 𝔄 →L[ℝ] E)
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- **Identification of the reconstructed curvature** (`thm:native-firstvariation-no-band`, last
paragraph: "strong ordinary connection first-jet convergence identifies the complete reconstructed
curvature").  If the literal curvature `R^0 F_h → F` strongly in `L²` (`(N2)`), the connections
converge strongly in `L⁴` and the ordinary connection first differences `R^0 D⁺_μ A_{ν,h} → P_{μν}`
strongly in `L²`, then `F_{μν} = P_{μν} - P_{νμ} + [A_μ, A_ν]` a.e. -/
theorem curvature_identification (H : CoHyp n y) {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    {P : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hP : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y k) ν))) (P μ ν))
    (μ ν : Fin 4) : F μ ν =ᵐ[MeasureTheory.volume] recCurv H.A₀ P μ ν := by
  have hA : ∀ μ, LpTendsto volume 4
      (fun k => pc (fun x => NativeYMBridge.gaugeArr (y k) x μ)) (H.A₀ μ) := H.hA
  have hcl : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      NativeYMIdentification.curvLog (n k) (NativeYMBridge.gaugeArr (y k)) x μ ν)) (F μ ν) := by
    intro μ ν
    obtain ⟨δ, -, hev⟩ := NativeYMMetric.unif_FextV H.hn hA 1
    refine NativeYMBridge.lpTendsto_of_eventually_eq (hF μ ν)
      (fun k => NativeYMIdentification.memLp_pc_gen _ 2) (hev.mono fun k hk => ?_)
    funext z
    simp only [pc]
    exact NativeYMBridge.fieldStrength_eq_curvLog (gauge (y k)) _ μ ν
      (NativeYMBridge.gaugePlaquette_lt_of_chart (gauge (y k)) _ μ ν (hk.1 _ μ ν))
  have h1 := (NativeYMIdentification.native_YM_curvature_identification H.hn hA hcl μ ν).1
  have h2 : LpTendsto volume 2 (fun k => pc (fun x =>
      NativeYMIdentification.linCurl (NativeYMBridge.gaugeArr (y k)) x μ ν))
      (P μ ν - P ν μ) :=
    ((hP μ ν).sub (hP ν μ)).congr (fun k => Eventually.of_forall fun z => rfl)
      (Eventually.of_forall fun z => rfl)
  filter_upwards [h1.ae_eq_of_lpTendsto h2] with z hz
  simp only [Pi.sub_apply] at hz
  simp only [recCurv]
  rw [← hz]
  abel

/-- **Yang–Mills row relative to the reconstructed fields** (`thm:native-firstvariation-no-band`,
last paragraph, Yang–Mills sector).  Under `(N1)` (`CoHyp`) and `(N2)` (literal curvature
`R^0 F_h → F` in `L²`), let the ordinary connection first differences converge strongly,
`R^0 D⁺_μ A_{ν,h} → P_{μν}` in `L²`, and let continuum reconstructions `f_h` (coframes, values in
the same compact chart), `A_h^rec` (connections) and `∂A_h^rec` (their first jets) converge with
`f_h → e` in `L²`, `A_h^rec → A` in `L⁴`, `∂A_h^rec → P` in `L²` (the strong reconstruction
comparison).  Then the Yang–Mills consistency error **relative to the reconstructed fields**, with
the complete reconstructed curvature `F(A_h^rec) = ∂A^rec - ∂A^rec + [A^rec, A^rec]`
(`recCurv`), tends to zero uniformly on every `C²` test ball. -/
theorem native_YM_reconstructed (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫) (H : CoHyp n y)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    {P : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hP : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y k) ν))) (P μ ν))
    {f : ℕ → 𝕋 → M4} (hfK : ∀ k z, f k z ∈ H.Ke) (hf : LpTendsto volume 2 f H.e₀)
    {Ar : ℕ → Fin 4 → 𝕋 → 𝔄} (hAr : ∀ μ, LpTendsto volume 4 (fun k => Ar k μ) (H.A₀ μ))
    {dAr : ℕ → Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hdAr : ∀ μ ν, LpTendsto volume 2 (fun k => dAr k μ ν) (P μ ν)) (M : NNReal) :
    ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧ ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ M →
      |NativeYMBridge.ymVar D (n k) (y k) (testRec κ (n k) (y k) τ) -
        NativeYMMetric.firstVarCont T (f k) (Ar k) (recCurv (Ar k) (dAr k)) τ.k.f
          (NativeYMBridge.toC1 τ.a)| ≤ β k := by
  obtain ⟨β₁, hβ₁, hev⟩ := NativeYMBridge.native_YM_sector D κ T hip H hF M
  have hFr : ∀ μ ν, μ < ν → LpTendsto volume 2 (fun k => recCurv (Ar k) (dAr k) μ ν) (F μ ν) :=
    fun μ ν _ => (lpTendsto_recCurv hAr hdAr μ ν).congr (fun k => Eventually.of_forall fun z => rfl)
      (curvature_identification H hF hP μ ν).symm
  obtain ⟨β₂, hβ₂, hcont⟩ := firstVarCont_unif T H.hKe (fun M hM => H.hKdet M hM) hf hfK hAr hFr M
  refine ⟨fun k => β₁ k + β₂ k, by simpa using hβ₁.add hβ₂, ?_⟩
  filter_upwards [hev] with k hk τ hτ
  have h2 := hcont k τ.k.f (NativeYMBridge.toC1 τ.a)
    (NativeYMBridge.metricBound_of_C2 τ.k (τ.k_le.trans hτ))
    (NativeYMBridge.gaugeBound_toC1 τ.a (τ.a_le.trans hτ))
  rw [abs_sub_comm] at h2
  calc _ ≤ |NativeYMBridge.ymVar D (n k) (y k) (testRec κ (n k) (y k) τ) -
          NativeYMMetric.firstVarCont T H.e₀ H.A₀ F τ.k.f (NativeYMBridge.toC1 τ.a)| +
        |NativeYMMetric.firstVarCont T H.e₀ H.A₀ F τ.k.f (NativeYMBridge.toC1 τ.a) -
          NativeYMMetric.firstVarCont T (f k) (Ar k) (recCurv (Ar k) (dAr k)) τ.k.f
            (NativeYMBridge.toC1 τ.a)| := abs_sub_le _ _ _
    _ ≤ β₁ k + β₂ k := add_le_add (hk τ hτ) h2

end YMSector

/-! ### The Higgs row relative to the reconstructed fields -/

section HiggsSector

open NativeDensity NativeHiggsVar
open ShiftedJetAction (Grid)
open NativeDiracLimit (DTest testRec)
open NativeDiracConv (CoHyp)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable (D : Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

/-- **The continuum Higgs covector at continuum fields** `(e, A, H, ∂H)`:
`∫ hcov(slots(e, A, H, ∂H))[J_v]` (`slotsOf`, with covariant gradient `K = ∂H + ρ_H(A)H`); by
`NativeHiggsVar.hasDerivAt_contHiggsDens` it is the integrated first variation of the continuum
Higgs density at these fields. -/
def higgsRecVar (f : 𝕋 → M4) (A : Fin 4 → 𝕋 → 𝔄) (Hr : 𝕋 → 𝓗) (dH : Fin 4 → 𝕋 → 𝓗)
    (τ : DTest 𝔄 𝓗 𝓢 W') : ℝ :=
  ∫ z, hcov D (slotsOf D (f z) (fun μ => A μ z) (Hr z) (fun μ => dH μ z)) (contHJet τ z)

theorem continuousOn_dc0' {Ke : Set M4} (hKdet : ∀ M ∈ Ke, Matrix.det (show NativeScaling.Mat from M) ≠ 0)
    (t : HJet 𝔄 𝓗) (μ ν : Fin 4) :
    ContinuousOn (fun M : M4 => fderiv ℝ (c0 μ ν) M (liftL M t.1)) Ke := fun M hM =>
  (NativeDiracConvergence.continuousAt_fderiv_apply (contDiffAt_c0 μ ν (hKdet M hM))
    ((NativeGravityFirstJet.continuous_liftL.clm_apply continuous_const).continuousAt)
    ).continuousWithinAt

theorem continuousOn_dvol' {Ke : Set M4}
    (hKdet : ∀ M ∈ Ke, Matrix.det (show NativeScaling.Mat from M) ≠ 0) (t : HJet 𝔄 𝓗) :
    ContinuousOn (fun M : M4 => fderiv ℝ NativeGravityFirstJet.volM M (liftL M t.1)) Ke :=
  fun M hM => (NativeDiracConvergence.continuousAt_fderiv_apply
    (NativeGravityFirstJet.contDiffAt_volM (hKdet M hM))
    ((NativeGravityFirstJet.continuous_liftL.clm_apply continuous_const).continuousAt)
    ).continuousWithinAt

/-- **Continuity of the continuum Higgs covector field** (`prop:reduced-continuity`, Higgs
sector): coframes `f_k → e₀` in `L²` in a compact nondegenerate chart, connections `A_k → A₀` in
`L⁴`, Higgs fields `H_k → H₀` in `L⁴` and first jets `∂H_k → q` in `L²` give strong `L¹`
convergence of the covector fields `hcov(slots(f_k, A_k, H_k, ∂H_k))`. -/
theorem lpTendsto_hcov_rec {Ke : Set M4} (hKe : IsCompact Ke)
    (hKdet : ∀ M ∈ Ke, Matrix.det (show NativeScaling.Mat from M) ≠ 0)
    {f : ℕ → 𝕋 → M4} {e₀ : 𝕋 → M4} (hf : LpTendsto volume 2 f e₀) (hfK : ∀ k z, f k z ∈ Ke)
    {A : ℕ → Fin 4 → 𝕋 → 𝔄} {A₀ : Fin 4 → 𝕋 → 𝔄}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => A k μ) (A₀ μ))
    {Hr : ℕ → 𝕋 → 𝓗} {H₀ : 𝕋 → 𝓗} (hH : LpTendsto volume 4 Hr H₀)
    {dH : ℕ → Fin 4 → 𝕋 → 𝓗} {q : Fin 4 → 𝕋 → 𝓗}
    (hdH : ∀ μ, LpTendsto volume 2 (fun k => dH k μ) (q μ)) :
    LpTendsto volume 1
      (fun k z => hcov D (slotsOf D (f k z) (fun μ => A k μ z) (Hr k z) (fun μ => dH k μ z)))
      (fun z => hcov D (slotsOf D (e₀ z) (fun μ => A₀ μ z) (H₀ z) (fun μ => q μ z))) := by
  have hH2 : LpTendsto volume 2 Hr H₀ := hH.mono two_ne_zero (by norm_num)
  have hK : ∀ μ, LpTendsto volume 2 (fun k z => dH k μ z + D.ρHL (A k μ z) (Hr k z))
      (fun z => q μ z + D.ρHL (A₀ μ z) (H₀ z)) := fun μ =>
    ((hdH μ).add (LpTendsto.bilin (p := 4) (q := 4) (r := 2) D.ρHL (hA μ) hH)).congr
      (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)
  have hQ : ∀ (t : HJet 𝔄 𝓗) (μ : Fin 4), LpTendsto volume 2
      (fun k z => Qop (slotsOf D (f k z) (fun μ => A k μ z) (Hr k z) (fun μ => dH k μ z)) μ t)
      (fun z => Qop (slotsOf D (e₀ z) (fun μ => A₀ μ z) (H₀ z) (fun μ => q μ z)) μ t) := by
    intro t μ
    have T1 := hH2.clm (D.ρHL (t.2.1 μ))
    have T2 := LpTendsto.const (p := 2) (ν := (volume : Measure 𝕋))
      (memLp_const (t.2.2.2 μ) : MemLp (fun _ : 𝕋 => t.2.2.2 μ) 2 volume)
    have T3 := ((hA μ).clm ((ContinuousLinearMap.apply ℝ 𝓗 t.2.2.1).comp D.ρHL)).mono
      two_ne_zero (by norm_num)
    refine ((T1.add T2).add T3).congr (fun k => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => ?_)
    · simp [Qop_apply, slotsOf]
    · simp [Qop_apply, slotsOf]
  have hpot : LpTendsto volume 1 (fun k z => potential D (Hr k z)) (fun z => potential D (H₀ z)) := by
    have hq := LpTendsto.bilin (p := 4) (q := 4) (r := 2) D.hermH hH hH
    have hr := hq.sub (LpTendsto.const (memLp_const (D.vH ^ 2)))
    have hs := (LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.mul ℝ ℝ) hr
      hr).const_smul D.lamH
    refine hs.congr (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · simp only [potential, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        ContinuousLinearMap.mul_apply', sq]
    · simp only [potential, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        ContinuousLinearMap.mul_apply', sq]
  have hdpot : ∀ η : 𝓗, LpTendsto volume 1 (fun k z => dpotL D (Hr k z) η)
      (fun z => dpotL D (H₀ z) η) := by
    intro η
    have hq := LpTendsto.bilin (p := 4) (q := 4) (r := 2) D.hermH hH hH
    have hr := hq.sub (LpTendsto.const (memLp_const (D.vH ^ 2)))
    have hw := (hH2.clm (D.hermH η)).add (hH2.clm (D.hermH.flip η))
    have hs := (LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.mul ℝ ℝ) hr
      hw).const_smul (D.lamH * 2)
    refine hs.congr (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · simp only [dpotL_apply, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul,
        ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply]
      ring
    · simp only [dpotL_apply, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul,
        ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply]
      ring
  refine WeakJetPairing.lpTendsto_clm_of_apply fun t => ?_
  have T1 : ∀ μ ν, LpTendsto volume 1
      (fun k z => fderiv ℝ (c0 μ ν) (f k z) (liftL (f k z) t.1) *
        D.hermH (dH k μ z + D.ρHL (A k μ z) (Hr k z)) (dH k ν z + D.ρHL (A k ν z) (Hr k z)))
      (fun z => fderiv ℝ (c0 μ ν) (e₀ z) (liftL (e₀ z) t.1) *
        D.hermH (q μ z + D.ρHL (A₀ μ z) (H₀ z)) (q ν z + D.ρHL (A₀ ν z) (H₀ z))) := fun μ ν =>
    chart (p := 1) ENNReal.one_ne_top hKe hf hfK (continuousOn_dc0' hKdet t μ ν)
      (ContinuousLinearMap.mul ℝ ℝ)
      (LpTendsto.bilin (p := 2) (q := 2) (r := 1) D.hermH (hK μ) (hK ν))
  have T2 : ∀ μ ν, LpTendsto volume 1
      (fun k z => c0 μ ν (f k z) *
        (D.hermH (Qop (slotsOf D (f k z) (fun μ => A k μ z) (Hr k z) (fun μ => dH k μ z)) μ t)
            (dH k ν z + D.ρHL (A k ν z) (Hr k z)) +
          D.hermH (dH k μ z + D.ρHL (A k μ z) (Hr k z))
            (Qop (slotsOf D (f k z) (fun μ => A k μ z) (Hr k z) (fun μ => dH k μ z)) ν t)))
      (fun z => c0 μ ν (e₀ z) *
        (D.hermH (Qop (slotsOf D (e₀ z) (fun μ => A₀ μ z) (H₀ z) (fun μ => q μ z)) μ t)
            (q ν z + D.ρHL (A₀ ν z) (H₀ z)) +
          D.hermH (q μ z + D.ρHL (A₀ μ z) (H₀ z))
            (Qop (slotsOf D (e₀ z) (fun μ => A₀ μ z) (H₀ z) (fun μ => q μ z)) ν t))) :=
    fun μ ν => chart (p := 1) ENNReal.one_ne_top hKe hf hfK
      (fun M hM => (contDiffAt_c0 μ ν (hKdet M hM)).continuousAt.continuousWithinAt)
      (ContinuousLinearMap.mul ℝ ℝ)
      ((LpTendsto.bilin (p := 2) (q := 2) (r := 1) D.hermH (hQ t μ) (hK ν)).add
        (LpTendsto.bilin (p := 2) (q := 2) (r := 1) D.hermH (hK μ) (hQ t ν)))
  have T3 := chart (p := 1) ENNReal.one_ne_top hKe hf hfK (continuousOn_dvol' hKdet t)
    (ContinuousLinearMap.mul ℝ ℝ) hpot
  have T4 := chart (p := 1) ENNReal.one_ne_top hKe hf hfK
    (fun M hM => (NativeGravityFirstJet.contDiffAt_volM (hKdet M hM)).continuousAt.continuousWithinAt)
    (ContinuousLinearMap.mul ℝ ℝ) (hdpot t.2.2.1)
  have hsum := NativeDiracConv.lpTendsto_finset_sum (p := 1) Finset.univ fun μ _ =>
    NativeDiracConv.lpTendsto_finset_sum (p := 1) Finset.univ fun ν _ => (T1 μ ν).add (T2 μ ν)
  refine (hsum.neg.sub (T3.add T4)).congr (fun k => Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, hcov_apply,
      ContinuousLinearMap.mul_apply']
    rfl
  · simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, hcov_apply,
      ContinuousLinearMap.mul_apply']
    rfl

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- The continuum slots of the limit are the slots of the limit fields once `K = D_A H`. -/
theorem contSlots_eq_slotsOf (H : CoHyp n y) (P : HiggsHyp D y) (z : 𝕋) :
    contSlots D H P z = slotsOf D (H.e₀ z) (fun μ => H.A₀ μ z) (P.H₀ z)
      (fun μ => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z)) := by
  simp only [contSlots, slotsOf, sub_add_cancel]

/-- **Higgs row relative to the reconstructed fields** (`thm:native-firstvariation-no-band`,
last paragraph, Higgs sector).  Under `(N1)` (`CoHyp`) and the Higgs conclusions (`HiggsHyp`:
`R^0 H_h → H` in `L⁴`, `R^0 K_h → K` in `L²`), let continuum reconstructions converge:
coframes `f_h → e` in `L²` in the same compact chart, connections `A_h^rec → A` in `L⁴`, Higgs
fields `H_h^rec → H` in `L⁴` and their first jets `∂H_h^rec → K - ρ_H(A)H` in `L²` (the limit of
the ordinary Higgs first differences, `prop:native-Higgs-compactness`).  Then the Higgs consistency
error relative to the reconstructed fields tends to zero uniformly on the `C²` test ball:
eventually `|D S_{H,h}(y_h)[𝓘_h v] - 𝒟_H(rec_h)[v]| ≤ ε ‖v‖_{C²}`. -/
theorem native_Higgs_reconstructed (H : CoHyp n y) (P : HiggsHyp D y)
    {f : ℕ → 𝕋 → M4} (hfK : ∀ k z, f k z ∈ H.Ke) (hf : LpTendsto volume 2 f H.e₀)
    {Ar : ℕ → Fin 4 → 𝕋 → 𝔄} (hAr : ∀ μ, LpTendsto volume 4 (fun k => Ar k μ) (H.A₀ μ))
    {Hr : ℕ → 𝕋 → 𝓗} (hHr : LpTendsto volume 4 Hr P.H₀)
    {dH : ℕ → Fin 4 → 𝕋 → 𝓗}
    (hdH : ∀ μ, LpTendsto volume 2 (fun k => dH k μ)
      (fun z => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z))) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W',
      |higgsVar D (n k) (y k) (testRec κ (n k) (y k) τ) -
        higgsRecVar D (f k) (Ar k) (Hr k) (dH k) τ| ≤ ε * τ.norm := by
  intro ε hε
  have h1 := native_Higgs_sector D κ H P (ε / 2) (by positivity)
  have hL := lpTendsto_hcov_rec D H.hKe H.hKdet hf hfK hAr hHr hdH
  have hev : ∀ᶠ k in atTop, ∫ z, ‖hcov D (slotsOf D (f k z) (fun μ => Ar k μ z) (Hr k z)
      (fun μ => dH k μ z)) - hcov D (slotsOf D (H.e₀ z) (fun μ => H.A₀ μ z) (P.H₀ z)
        (fun μ => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z)))‖ ≤ ε / 2 :=
    (tendsto_order.1 (integral_norm_sub_tendsto hL)).2 (ε / 2) (by positivity) |>.mono
      fun k hk => hk.le
  filter_upwards [h1, hev] with k hk1 hk2 τ
  have hτ := τ.norm_nonneg
  have hc0 : contHiggsVar D H P τ = ∫ z, hcov D (slotsOf D (H.e₀ z) (fun μ => H.A₀ μ z) (P.H₀ z)
      (fun μ => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z))) (contHJet τ z) := by
    simp only [contHiggsVar, contSlots_eq_slotsOf]
  have hd := abs_integral_apply_sub_le (memLp_one_iff_integrable.1 hL.memLp_lim)
    (memLp_one_iff_integrable.1 (hL.memLp k)) (continuous_contHJet τ) (norm_contHJet_le τ)
  have hd' : |contHiggsVar D H P τ - higgsRecVar D (f k) (Ar k) (Hr k) (dH k) τ| ≤
      ε / 2 * τ.norm := by
    rw [hc0]
    refine hd.trans (mul_le_mul_of_nonneg_right ?_ hτ)
    refine le_of_eq_of_le ?_ hk2
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    exact norm_sub_rev _ _
  calc _ ≤ |higgsVar D (n k) (y k) (testRec κ (n k) (y k) τ) - contHiggsVar D H P τ| +
        |contHiggsVar D H P τ - higgsRecVar D (f k) (Ar k) (Hr k) (dH k) τ| := abs_sub_le _ _ _
    _ ≤ ε / 2 * τ.norm + ε / 2 * τ.norm := add_le_add (hk1 τ) hd'
    _ = ε * τ.norm := by ring

end HiggsSector

/-! ### The Dirac–Yukawa row relative to the reconstructed fields -/

section DiracRec

open NativeScaling (Mat readerOmega)
open NativeGravityFirstJet (dqLiftL)
open NativeDensity NativeDirac NativeDiracConv NativeDiracLimit NativeDiracConvergence

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']

/-- **Continuum reconstructions for the Dirac–Yukawa row**: coframes `f_k` (values in a compact
nondegenerate chart `K_e`) with first jets `g_k`, connections `A_k`, Higgs fields `H_k`, spinors
`Ψ_k` and co-spinor frame fields `χ_k`, converging to `(e₀, p, A₀, H₀, Ψ₀, χ₀)` — coframe values and
jets and Higgs fields strongly in `L²`, connections in `L⁴`, spinors strongly in `L²` with uniform
`L⁴` bounds. -/
structure RecDirac (Ke : Set M4) (e₀ : 𝕋 → M4) (p : Fin 4 → 𝕋 → M4) (A₀ : Fin 4 → 𝕋 → 𝔄)
    (H₀ : 𝕋 → 𝓗) (Ψ₀ : 𝕋 → 𝓢) (χ₀ : 𝕋 → W') where
  hKe : IsCompact Ke
  hKdet : ∀ M ∈ Ke, Matrix.det (show Mat from M) ≠ 0
  f : ℕ → 𝕋 → M4
  hfK : ∀ k z, f k z ∈ Ke
  hf : LpTendsto volume 2 f e₀
  g : ℕ → Fin 4 → 𝕋 → M4
  hg : ∀ lam, LpTendsto volume 2 (fun k => g k lam) (p lam)
  A : ℕ → Fin 4 → 𝕋 → 𝔄
  hA : ∀ μ, LpTendsto volume 4 (fun k => A k μ) (A₀ μ)
  Hr : ℕ → 𝕋 → 𝓗
  hH : LpTendsto volume 2 Hr H₀
  Ψ : ℕ → 𝕋 → 𝓢
  hΨ : LpTendsto volume 2 Ψ Ψ₀
  χ : ℕ → 𝕋 → W'
  hχ : LpTendsto volume 2 χ χ₀
  B4 : ℝ≥0∞
  hB4 : B4 ≠ ∞
  hΨ4 : ∀ k, eLpNorm (Ψ k) 4 volume ≤ B4
  hχ4 : ∀ k, eLpNorm (χ k) 4 volume ≤ B4

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)
variable {Ke : Set M4} {e₀ : 𝕋 → M4} {p : Fin 4 → 𝕋 → M4} {A₀ : Fin 4 → 𝕋 → 𝔄}
  {H₀ : 𝕋 → 𝓗} {Ψ₀ : 𝕋 → 𝓢} {χ₀ : 𝕋 → W'}

namespace RecDirac

variable (R : RecDirac (W' := W') Ke e₀ p A₀ H₀ Ψ₀ χ₀)

/-- The continuum slots of the reconstructed fields. -/
def SR (k : ℕ) (z : 𝕋) : Slots 𝔄 𝓗 𝓢 W' :=
  contSlots D κ (R.f k z) (fun lam => R.g k lam z) (fun μ => R.A k μ z) (R.Hr k z) (R.Ψ k z)
    (R.χ k z)

variable (e₀ p A₀ H₀ Ψ₀ χ₀) in
/-- The continuum slots of the limit fields. -/
def SL (z : 𝕋) : Slots 𝔄 𝓗 𝓢 W' :=
  contSlots D κ (e₀ z) (fun lam => p lam z) (fun μ => A₀ μ z) (H₀ z) (Ψ₀ z) (χ₀ z)

variable {D κ}

theorem chartR {Z' E W : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≠ ∞) {Φ : M4 → Z'} (hΦ : ContinuousOn Φ Ke) (B : Z' →L[ℝ] E →L[ℝ] W)
    {s : ℕ → 𝕋 → E} {s₀ : 𝕋 → E} (hs : LpTendsto volume q s s₀) :
    LpTendsto volume q (fun k z => B (Φ (R.f k z)) (s k z)) (fun z => B (Φ (e₀ z)) (s₀ z)) :=
  chart hq R.hKe R.hf R.hfK hΦ B hs

theorem chartR₀ {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : q ≠ ∞) {Φ : M4 → Z'} (hΦ : ContinuousOn Φ Ke) :
    LpTendsto volume q (fun k z => Φ (R.f k z)) (fun z => Φ (e₀ z)) :=
  chart₀ hq R.hKe R.hf R.hfK hΦ

theorem g_coord (lam i j : Fin 4) :
    LpTendsto volume 2 (fun k z => R.g k lam z i j) (fun z => p lam z i j) :=
  (R.hg lam).clm (CoHyp.entryL i j)

/-- `Ω_μ(f_k, g_k) → Ω_μ(e₀, p)` strongly in `L²`. -/
theorem lpTendsto_omega (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => asM4 (readerOmega (R.f k z) (fun lam => R.g k lam z) μ))
      (fun z => asM4 (readerOmega (e₀ z) (fun lam => p lam z) μ)) := by
  have key : LpTendsto volume 2
      (fun k z => ∑ lam, ∑ i, ∑ j, R.g k lam z i j • omegaCoef μ lam i j (R.f k z))
      (fun z => ∑ lam, ∑ i, ∑ j, p lam z i j • omegaCoef μ lam i j (e₀ z)) := by
    refine lpTendsto_finset_sum _ fun lam _ => lpTendsto_finset_sum _ fun i _ =>
      lpTendsto_finset_sum _ fun j _ => ?_
    exact R.chartR (q := 2) (by norm_num) (continuousOn_omegaCoef μ lam i j R.hKdet)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] M4 →L[ℝ] M4).flip (R.g_coord lam i j)
  exact key.congr (fun k => Eventually.of_forall fun z => (readerOmega_expand _ _ _).symm)
    (Eventually.of_forall fun z => (readerOmega_expand _ _ _).symm)

/-- The continuum spin–gauge connections converge strongly in `L²`. -/
theorem fWl (μ : Fin 4) : LpTendsto volume 2 (fun k z => (SR D κ R k z).Wl μ)
    (fun z => (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z).Wl μ) :=
  ((R.lpTendsto_omega μ).clm (σL D)).add (((R.hA μ).clm D.ρSL).mono two_ne_zero (by norm_num))
    |>.congr (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)

theorem fWr (μ : Fin 4) : LpTendsto volume 2 (fun k z => (SR D κ R k z).Wr μ)
    (fun z => (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z).Wr μ) :=
  (R.fWl (D := D) (κ := κ) μ).neg.congr (fun k => Eventually.of_forall fun z => rfl)
    (Eventually.of_forall fun z => rfl)

/-- First chart term of the spin-connection variation. -/
def dωT1 (μ lam i j : Fin 4) (t : Jet 𝔄 𝓗 𝓢 W') (M : M4) : M4 :=
  (liftL M (t.2.1 lam)) i j • omegaCoef μ lam i j M

/-- Second chart term (linear in the coframe jet). -/
def dωT2 (μ lam i j : Fin 4) (t : Jet 𝔄 𝓗 𝓢 W') (M : M4) : M4 →L[ℝ] M4 :=
  ContinuousLinearMap.smulRightL ℝ M4 M4
    ((CoHyp.entryL i j).comp ((ContinuousLinearMap.apply ℝ M4 t.1).comp (dqLiftL M M)))
    (omegaCoef μ lam i j M)

/-- Third chart term. -/
def dωT3 (μ lam i j : Fin 4) (t : Jet 𝔄 𝓗 𝓢 W') (M : M4) : M4 :=
  fderiv ℝ (omegaCoef μ lam i j) M (liftL M t.1)

theorem dωT2_apply (μ lam i j : Fin 4) (t : Jet 𝔄 𝓗 𝓢 W') (M q : M4) :
    dωT2 μ lam i j t M q = (dqLiftL M M q t.1) i j • omegaCoef μ lam i j M := rfl

theorem δωL_const_eq (e : M4) (q : Fin 4 → M4) (μ : Fin 4) (t : Jet 𝔄 𝓗 𝓢 W') :
    δωL e (fun _ => e) q μ t = ∑ lam, ∑ i, ∑ j,
      (dωT1 μ lam i j t e + dωT2 μ lam i j t e (q lam) + q lam i j • dωT3 μ lam i j t e) := by
  simp only [δωL_apply, DεL_apply, εL, ContinuousLinearMap.coe_comp',
    Function.comp_apply, πk_apply, Pi.add_apply, add_smul, dωT1, dωT2_apply, dωT3]

include R in
theorem continuousOn_dωT1 (μ lam i j : Fin 4) (t : Jet 𝔄 𝓗 𝓢 W') :
    ContinuousOn (dωT1 μ lam i j t) Ke := by
  refine ContinuousOn.smul (f := fun M : M4 => (liftL M (t.2.1 lam)) i j)
    (g := fun M : M4 => omegaCoef μ lam i j M) ?_ (continuousOn_omegaCoef μ lam i j R.hKdet)
  exact ((continuous_apply j).comp ((continuous_apply i).comp
    (NativeGravityFirstJet.continuous_liftL.clm_apply continuous_const))).continuousOn

theorem continuous_dqLiftL_diag : Continuous fun M : M4 => dqLiftL M M :=
  continuous_clm_apply.2 fun q => continuous_clm_apply.2 fun k => by
    change Continuous fun M : M4 => NativeGravityFirstJet.dqLift M M q k
    unfold NativeGravityFirstJet.dqLift NativeScaling.metric; fun_prop

include R in
theorem continuousOn_dωT2 (μ lam i j : Fin 4) (t : Jet 𝔄 𝓗 𝓢 W') :
    ContinuousOn (dωT2 μ lam i j t) Ke := by
  have h1 : Continuous fun M : M4 =>
      (CoHyp.entryL i j).comp ((ContinuousLinearMap.apply ℝ M4 t.1).comp (dqLiftL M M)) :=
    continuous_const.clm_comp (continuous_const.clm_comp continuous_dqLiftL_diag)
  exact ((ContinuousLinearMap.smulRightL ℝ M4 M4).continuous.comp h1).continuousOn.clm_apply
    (continuousOn_omegaCoef μ lam i j R.hKdet)

include R in
theorem continuousOn_dωT3 (μ lam i j : Fin 4) (t : Jet 𝔄 𝓗 𝓢 W') :
    ContinuousOn (dωT3 μ lam i j t) Ke := fun e he =>
  (continuousAt_fderiv_apply (contDiffAt_omegaCoef μ lam i j (R.hKdet e he))
    ((NativeGravityFirstJet.continuous_liftL.clm_apply continuous_const).continuousAt)
    ).continuousWithinAt

/-- The metric variation of the Levi-Civita spin connection along a fixed jet converges. -/
theorem lpTendsto_δω (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    LpTendsto volume 2
      (fun k z => δωL (R.f k z) (fun _ => R.f k z) (fun lam => R.g k lam z) μ t)
      (fun z => δωL (e₀ z) (fun _ => e₀ z) (fun lam => p lam z) μ t) := by
  have key : LpTendsto volume 2
      (fun k z => ∑ lam, ∑ i, ∑ j, (dωT1 μ lam i j t (R.f k z) +
        dωT2 μ lam i j t (R.f k z) (R.g k lam z) + R.g k lam z i j • dωT3 μ lam i j t (R.f k z)))
      (fun z => ∑ lam, ∑ i, ∑ j, (dωT1 μ lam i j t (e₀ z) +
        dωT2 μ lam i j t (e₀ z) (p lam z) + p lam z i j • dωT3 μ lam i j t (e₀ z))) := by
    refine lpTendsto_finset_sum _ fun lam _ => lpTendsto_finset_sum _ fun i _ =>
      lpTendsto_finset_sum _ fun j _ => ?_
    have T1 := R.chartR₀ (q := 2) (by norm_num) (R.continuousOn_dωT1 μ lam i j t)
    have T2 := R.chartR (q := 2) (by norm_num) (R.continuousOn_dωT2 μ lam i j t)
      (ContinuousLinearMap.id ℝ (M4 →L[ℝ] M4)) (R.hg lam)
    have T3 := R.chartR (q := 2) (by norm_num) (R.continuousOn_dωT3 μ lam i j t)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] M4 →L[ℝ] M4).flip (R.g_coord lam i j)
    exact ((T1.add T2).add T3).congr (fun k => Eventually.of_forall fun z => rfl)
      (Eventually.of_forall fun z => rfl)
  exact key.congr (fun k => Eventually.of_forall fun z => (δωL_const_eq _ _ μ t).symm)
    (Eventually.of_forall fun z => (δωL_const_eq _ _ μ t).symm)

theorem fdWl (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => (SR D κ R k z).dWl μ t)
      (fun z => (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z).dWl μ t) :=
  (((R.lpTendsto_δω t μ).clm (σL D)).add (LpTendsto.const (p := 2)
    (memLp_const (D.ρSL (t.2.2.1 μ)) : MemLp (fun _ : 𝕋 => D.ρSL (t.2.2.1 μ)) 2 volume))).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)

theorem fdWr (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => (SR D κ R k z).dWr μ t)
      (fun z => (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z).dWr μ t) :=
  (R.fdWl (D := D) (κ := κ) t μ).neg.congr (fun k => Eventually.of_forall fun z => rfl)
    (Eventually.of_forall fun z => rfl)

theorem fYH : LpTendsto volume 2 (fun k z => (SR D κ R k z).YH)
    (fun z => (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z).YH) :=
  R.hH.clm D.yukawa

theorem fΨ : LpTendsto volume 2 (fun k z => (SR D κ R k z).Ψ)
    (fun z => (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z).Ψ) := R.hΨ

theorem fΨp (μ : Fin 4) : LpTendsto volume 2 (fun k z => (SR D κ R k z).Ψp μ)
    (fun z => (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z).Ψp μ) := R.hΨ

theorem fΨb : LpTendsto volume 2 (fun k z => (SR D κ R k z).Ψb)
    (fun z => (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z).Ψb) := R.hχ.clm κ

theorem fΨbp (μ : Fin 4) : LpTendsto volume 2 (fun k z => (SR D κ R k z).Ψbp μ)
    (fun z => (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z).Ψbp μ) := R.hχ.clm κ

theorem bΨ (k : ℕ) : eLpNorm (fun z => (SR D κ R k z).Ψ) 4 volume ≤ R.B4 := R.hΨ4 k

theorem bΨp (k : ℕ) (μ : Fin 4) : eLpNorm (fun z => (SR D κ R k z).Ψp μ) 4 volume ≤ R.B4 :=
  R.hΨ4 k

theorem bΨb (k : ℕ) :
    eLpNorm (fun z => (SR D κ R k z).Ψb) 4 volume ≤ ENNReal.ofReal ‖κ‖ * R.B4 :=
  (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := R.χ k)
    (Eventually.of_forall fun z => κ.le_opNorm _) 4).trans
    (mul_le_mul_of_nonneg_left (R.hχ4 k) zero_le)

theorem bΨbp (k : ℕ) (μ : Fin 4) :
    eLpNorm (fun z => (SR D κ R k z).Ψbp μ) 4 volume ≤ ENNReal.ofReal ‖κ‖ * R.B4 :=
  R.bΨb (D := D) (κ := κ) k

theorem hBb : ENNReal.ofReal ‖κ‖ * R.B4 ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top R.hB4

/-! #### Coefficients -/

include R in
theorem cVG (μ : Fin 4) : ContinuousOn (fun M : M4 => chV M • chG D μ M) Ke :=
  (continuousOn_chV R.hKdet).smul (continuousOn_chG D R.hKdet μ)

include R in
theorem cDVG (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    ContinuousOn (fun M : M4 => chDV t M • chG D μ M) Ke :=
  (continuousOn_chDV R.hKdet t).smul (continuousOn_chG D R.hKdet μ)

include R in
theorem cVDG (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    ContinuousOn (fun M : M4 => chV M • chDG D t μ M) Ke :=
  (continuousOn_chV R.hKdet).smul (continuousOn_chDG D R.hKdet t μ)

theorem cc1 (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => c1 (SR D κ R k z) t μ)
      (fun z => c1 (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) t μ) :=
  (((R.chartR (q := 2) (by norm_num) (R.cDVG (D := D) t μ) (ContinuousLinearMap.mul ℝ (Spin 𝓢))
    (R.fWl (D := D) (κ := κ) μ)).add (R.chartR (q := 2) (by norm_num) (R.cVDG (D := D) t μ)
      (ContinuousLinearMap.mul ℝ (Spin 𝓢)) (R.fWl (D := D) (κ := κ) μ))).add
    (R.chartR (q := 2) (by norm_num) (R.cVG (D := D) μ) (ContinuousLinearMap.mul ℝ (Spin 𝓢))
      (R.fdWl (D := D) (κ := κ) t μ))).congr (fun k => Eventually.of_forall fun z => rfl)
    (Eventually.of_forall fun z => rfl)

theorem cc2 (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => c2 (SR D κ R k z) t μ)
      (fun z => c2 (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) t μ) :=
  (((R.chartR (q := 2) (by norm_num) (R.cDVG (D := D) t μ)
    (ContinuousLinearMap.mul ℝ (Spin 𝓢)).flip (R.fWr (D := D) (κ := κ) μ)).add
    (R.chartR (q := 2) (by norm_num) (R.cVG (D := D) μ) (ContinuousLinearMap.mul ℝ (Spin 𝓢)).flip
      (R.fdWr (D := D) (κ := κ) t μ))).add
    (R.chartR (q := 2) (by norm_num) (R.cVDG (D := D) t μ)
      (ContinuousLinearMap.mul ℝ (Spin 𝓢)).flip (R.fWr (D := D) (κ := κ) μ))).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)

theorem cc3 (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => c3 (SR D κ R k z) μ)
      (fun z => c3 (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) μ) :=
  (R.chartR (q := 2) (by norm_num) (R.cVG (D := D) μ) (ContinuousLinearMap.mul ℝ (Spin 𝓢))
    (R.fWl (D := D) (κ := κ) μ)).congr (fun k => Eventually.of_forall fun z => rfl)
    (Eventually.of_forall fun z => rfl)

theorem cc5 (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => c5 (SR D κ R k z) μ)
      (fun z => c5 (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) μ) :=
  (R.chartR (q := 2) (by norm_num) (R.cVG (D := D) μ) (ContinuousLinearMap.mul ℝ (Spin 𝓢)).flip
    (R.fWr (D := D) (κ := κ) μ)).congr (fun k => Eventually.of_forall fun z => rfl)
    (Eventually.of_forall fun z => rfl)

theorem chartVG (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => (SR D κ R k z).v • (SR D κ R k z).γ μ)
      (fun z => (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z).v • (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z).γ μ) :=
  R.chartR₀ (q := 2) (by norm_num) (R.cVG (D := D) μ)

theorem cc4 (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => c4 (SR D κ R k z) μ)
      (fun z => c4 (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) μ) :=
  (R.chartVG (D := D) (κ := κ) μ).congr (fun k => Eventually.of_forall fun z => by simp [c4, SR, contSlots])
    (Eventually.of_forall fun z => by simp [c4, SL, contSlots])

theorem cc6 (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => c6 (SR D κ R k z) μ)
      (fun z => c6 (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) μ) :=
  (R.chartVG (D := D) (κ := κ) μ).congr (fun k => Eventually.of_forall fun z => by simp [c6, SR, contSlots])
    (Eventually.of_forall fun z => by simp [c6, SL, contSlots])

theorem cc9 (t : Jet 𝔄 𝓗 𝓢 W') :
    LpTendsto volume 2 (fun k z => c9 D (SR D κ R k z) t)
      (fun z => c9 D (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) t) :=
  ((R.chartR (q := 2) (by norm_num) (continuousOn_chDV R.hKdet t)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Spin 𝓢 →L[ℝ] Spin 𝓢) (R.fYH (D := D) (κ := κ))).add
    (R.chartR₀ (q := 2) (by norm_num)
      ((continuousOn_chV R.hKdet).smul continuousOn_const (g := fun _ => D.yukawa t.2.2.2.1)))).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)

theorem cc10 :
    LpTendsto volume 2 (fun k z => c10 (SR D κ R k z))
      (fun z => c10 (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z)) :=
  (R.chartR (q := 2) (by norm_num) (continuousOn_chV R.hKdet)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Spin 𝓢 →L[ℝ] Spin 𝓢) (R.fYH (D := D) (κ := κ))).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)

/-! #### The operator fields -/

theorem lpTendsto_Gμ (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    LpTendsto volume 1 (fun k z => Gμ κ (SR D κ R k z) t μ)
      (fun z => Gμ κ (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) t μ) := by
  set c : ℂ := Complex.I / 2
  have T1 := lpTendsto_triB (bForm c) (norm_bForm_le c) (R.fΨb (D := D) (κ := κ)) R.hBb (R.bΨb (D := D) (κ := κ))
    (R.cc1 (D := D) (κ := κ) t μ) (R.fΨp (D := D) (κ := κ) μ) R.hB4 (fun k => R.bΨp (D := D) (κ := κ) k μ)
  have T2 := lpTendsto_triB (bForm c) (norm_bForm_le c) (R.fΨbp (D := D) (κ := κ) μ) R.hBb
    (fun k => R.bΨbp (D := D) (κ := κ) k μ) (R.cc2 (D := D) (κ := κ) t μ) (R.fΨ (D := D) (κ := κ)) R.hB4 (R.bΨ (D := D) (κ := κ))
  have T3 := lpTendsto_triB (bForm c) (norm_bForm_le c) (lpTendsto_const' (κ t.2.2.2.2.2.2.1))
    enorm_ne_top (fun k => eLpNorm_const_le _) (R.cc3 (D := D) (κ := κ) μ) (R.fΨp (D := D) (κ := κ) μ) R.hB4
    (fun k => R.bΨp (D := D) (κ := κ) k μ)
  have T4 := lpTendsto_triB (bForm c) (norm_bForm_le c) (lpTendsto_const' (κ (t.2.2.2.2.2.2.2 μ)))
    enorm_ne_top (fun k => eLpNorm_const_le _) (R.cc4 (D := D) (κ := κ) μ) (R.fΨ (D := D) (κ := κ)) R.hB4 (R.bΨ (D := D) (κ := κ))
  have T5 := lpTendsto_triB (bForm c) (norm_bForm_le c) (lpTendsto_const' (κ t.2.2.2.2.2.2.1))
    enorm_ne_top (fun k => eLpNorm_const_le _) (R.cc5 (D := D) (κ := κ) μ) (R.fΨ (D := D) (κ := κ)) R.hB4 (R.bΨ (D := D) (κ := κ))
  have T6 := lpTendsto_triB (bForm c) (norm_bForm_le c) (R.fΨb (D := D) (κ := κ)) R.hBb (R.bΨb (D := D) (κ := κ))
    (R.cc6 (D := D) (κ := κ) μ) (lpTendsto_const' (t.2.2.2.2.2.1 μ)) enorm_ne_top (fun k => eLpNorm_const_le _)
  have T7 := lpTendsto_triB (bForm c) (norm_bForm_le c) (R.fΨb (D := D) (κ := κ)) R.hBb (R.bΨb (D := D) (κ := κ))
    (R.cc3 (D := D) (κ := κ) μ) (lpTendsto_const' t.2.2.2.2.1) enorm_ne_top (fun k => eLpNorm_const_le _)
  have T8 := lpTendsto_triB (bForm c) (norm_bForm_le c) (R.fΨbp (D := D) (κ := κ) μ) R.hBb
    (fun k => R.bΨbp (D := D) (κ := κ) k μ) (R.cc5 (D := D) (κ := κ) μ) (lpTendsto_const' t.2.2.2.2.1) enorm_ne_top
    (fun k => eLpNorm_const_le _)
  refine ((((((((T1.sub T2).add T3).sub T4).sub T5).add T6).add T7).sub T8)).congr
    (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · simp only [Pi.add_apply, Pi.sub_apply]
    exact (Gμ_eq_tri κ (SR D κ R k z) t μ).symm
  · simp only [Pi.add_apply, Pi.sub_apply]
    exact (Gμ_eq_tri κ (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) t μ).symm

theorem lpTendsto_G0 (t : Jet 𝔄 𝓗 𝓢 W') :
    LpTendsto volume 1 (fun k z => G0 D κ (SR D κ R k z) t)
      (fun z => G0 D κ (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) t) := by
  have T1 := lpTendsto_triB (bForm 1) (norm_bForm_le 1) (R.fΨb (D := D) (κ := κ)) R.hBb (R.bΨb (D := D) (κ := κ))
    (R.cc9 (D := D) (κ := κ) t) (R.fΨ (D := D) (κ := κ)) R.hB4 (R.bΨ (D := D) (κ := κ))
  have T2 := lpTendsto_triB (bForm 1) (norm_bForm_le 1) (lpTendsto_const' (κ t.2.2.2.2.2.2.1))
    enorm_ne_top (fun k => eLpNorm_const_le _) (R.cc10 (D := D) (κ := κ)) (R.fΨ (D := D) (κ := κ)) R.hB4 (R.bΨ (D := D) (κ := κ))
  have T3 := lpTendsto_triB (bForm 1) (norm_bForm_le 1) (R.fΨb (D := D) (κ := κ)) R.hBb (R.bΨb (D := D) (κ := κ))
    (R.cc10 (D := D) (κ := κ)) (lpTendsto_const' t.2.2.2.2.1) enorm_ne_top (fun k => eLpNorm_const_le _)
  refine ((T1.add T2).add T3).congr
    (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · simp only [Pi.add_apply]
    exact (G0_eq_tri D κ (SR D κ R k z) t).symm
  · simp only [Pi.add_apply]
    exact (G0_eq_tri D κ (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) t).symm

/-- **`Gop` at the reconstructed slots converges strongly in `L¹`.** -/
theorem lpTendsto_Gop :
    LpTendsto volume 1 (fun k z => Gop D κ (SR D κ R k z))
      (fun z => Gop D κ (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z)) := by
  refine WeakJetPairing.lpTendsto_clm_of_apply fun t => ?_
  exact (WeakJetPairing.lpTendsto_finset_sum_aux Finset.univ
    fun μ _ => R.lpTendsto_Gμ (D := D) (κ := κ) t μ).sub (R.lpTendsto_G0 (D := D) (κ := κ) t)

include R in
theorem cK (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    ContinuousOn (fun M : M4 => chDV t M • chG D μ M + chV M • chDG D t μ M) Ke :=
  (R.cDVG (D := D) t μ).add (R.cVDG (D := D) t μ)

theorem lpTendsto_Λμ (t : Jet 𝔄 𝓗 𝓢 W') (u : Dif 𝓢 W') (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => Λμ κ (SR D κ R k z) t u μ)
      (fun z => Λμ κ (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z) t u μ) := by
  set c : ℂ := Complex.I / 2
  have T1 := R.chartR (q := 2) (by norm_num)
    (Φ := fun M : M4 => (bForm c).flip ((chDV t M • chG D μ M + chV M • chDG D t μ M) (u.1 μ)))
    ((bForm c).flip.continuous.comp_continuousOn ((R.cK (D := D) t μ).clm_apply continuousOn_const))
    (ContinuousLinearMap.id ℝ (CoSpinor 𝓢 →L[ℝ] ℝ)) (R.fΨb (D := D) (κ := κ))
  have T2 := R.chartR (q := 2) (by norm_num)
    (Φ := fun M : M4 => (bForm c (κ (u.2 μ))).comp (chDV t M • chG D μ M + chV M • chDG D t μ M))
    ((continuous_const.clm_comp continuous_id).comp_continuousOn (R.cK (D := D) t μ))
    (ContinuousLinearMap.id ℝ (𝓢 →L[ℝ] ℝ)) (R.fΨ (D := D) (κ := κ))
  have T3 := R.chartR₀ (q := 2) (by norm_num)
    (Φ := fun M : M4 => bForm c (κ t.2.2.2.2.2.2.1) ((chV M • chG D μ M) (u.1 μ)))
    ((bForm c (κ t.2.2.2.2.2.2.1)).continuous.comp_continuousOn
      ((R.cVG (D := D) μ).clm_apply continuousOn_const))
  have T4 := R.chartR₀ (q := 2) (by norm_num)
    (Φ := fun M : M4 => bForm c (κ (u.2 μ)) ((chV M • chG D μ M) t.2.2.2.2.1))
    ((bForm c (κ (u.2 μ))).continuous.comp_continuousOn
      ((R.cVG (D := D) μ).clm_apply continuousOn_const))
  refine (((T1.sub T2).add T3).sub T4).congr
    (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · simp only [Pi.add_apply, Pi.sub_apply]
    rw [Λμ_eq_tri]; rfl
  · simp only [Pi.add_apply, Pi.sub_apply]
    rw [Λμ_eq_tri]; rfl

/-- **`Λop` at the reconstructed slots converges strongly in `L²`.** -/
theorem lpTendsto_Λop :
    LpTendsto volume 2 (fun k z => Λop κ (SR D κ R k z))
      (fun z => Λop κ (SL D κ e₀ p A₀ H₀ Ψ₀ χ₀ z)) := by
  refine WeakJetPairing.lpTendsto_clm_of_apply fun t => ?_
  refine WeakJetPairing.lpTendsto_clm_of_apply fun u => ?_
  exact WeakJetPairing.lpTendsto_finset_sum_aux Finset.univ fun μ _ => R.lpTendsto_Λμ (D := D) (κ := κ) t u μ

end RecDirac

/-- **The continuum Dirac–Yukawa covector at continuum fields**
`(e, ∂e, A, H, Ψ, χ)` with derivative slots `u = (∂Ψ, ∂χ)`:
`∫ (G(J_v) + Λ(J_v)(u))` at the continuum slots; by
`NativeSpinorVariation.hasDerivAt_contDens` it is the integrated first variation of the continuum
Dirac–Yukawa density at these fields. -/
def diracRecVar (f : 𝕋 → M4) (g : Fin 4 → 𝕋 → M4) (A : Fin 4 → 𝕋 → 𝔄) (Hr : 𝕋 → 𝓗)
    (Ψ : 𝕋 → 𝓢) (χ : 𝕋 → W') (u : 𝕋 → Dif 𝓢 W') (τ : DTest 𝔄 𝓗 𝓢 W') : ℝ :=
  ∫ z, (Gop D κ (contSlots D κ (f z) (fun lam => g lam z) (fun μ => A μ z) (Hr z) (Ψ z) (χ z))
      (NativeSpinorVariation.contJet τ z) +
    Λop κ (contSlots D κ (f z) (fun lam => g lam z) (fun μ => A μ z) (Hr z) (Ψ z) (χ z))
      (NativeSpinorVariation.contJet τ z) (u z))

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, ShiftedJetAction.Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- **Dirac–Yukawa row relative to the reconstructed fields** (`thm:native-firstvariation-no-band`,
last paragraph, Dirac sector).  Under the hypotheses of `prop:native-spinor-variation`
(`CoHyp`, `SpinHyp`, weak bounded `L²` convergence of the spinor first differences to
`u₀ = (∂Ψ, ∂χ)`), let continuum reconstructions converge to the same limits (`RecDirac`: coframes in
the same compact chart with strongly convergent first jets, connections in `L⁴`, Higgs fields in
`L²`, spinors strongly in `L²` with uniform `L⁴` bounds) and let their first jets `u_h^rec`
converge weakly and boundedly in `L²` to the same `u₀`.  Then the complete Dirac–Yukawa
consistency error relative to the reconstructed fields tends to zero uniformly on the `C²` test
ball. -/
theorem native_Dirac_reconstructed (H : CoHyp n y) (S : SpinHyp κ y)
    {u₀ : 𝕋 → Dif 𝓢 W'} (hu₀ : MemLp u₀ 2 volume) {C : ℝ}
    (hub : ∀ k, (eLpNorm (pc (difs (y k) (S.χ k))) 2 volume).toReal ≤ C)
    (hw : ∀ g : 𝕋 → Dif 𝓢 W' →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (pc (difs (y k) (S.χ k)) z)) atTop (𝓝 (∫ z, g z (u₀ z))))
    (R : RecDirac (W' := W') H.Ke H.e₀ H.p H.A₀ S.H₀ S.Ψ₀ S.χ₀)
    {ur : ℕ → 𝕋 → Dif 𝓢 W'} (hur : ∀ k, MemLp (ur k) 2 volume) {Cr : ℝ}
    (hurb : ∀ k, (eLpNorm (ur k) 2 volume).toReal ≤ Cr)
    (hurw : ∀ g : 𝕋 → Dif 𝓢 W' →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (ur k z)) atTop (𝓝 (∫ z, g z (u₀ z)))) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W',
      |dVar D (n k : ℝ)⁻¹ (y k) (testRec κ (n k) (y k) τ) -
        diracRecVar D κ (R.f k) (R.g k) (R.A k) (R.Hr k) (R.Ψ k) (R.χ k) (ur k) τ| ≤
          ε * τ.norm := by
  intro ε hε
  have h1 := NativeSpinorVariation.native_spinor_variation D κ H S hu₀ hub hw (ε / 2)
    (by positivity)
  have h2 := WeakJetPairing.weak_jet_variation (R.lpTendsto_Gop (D := D) (κ := κ))
    (R.lpTendsto_Λop (D := D) (κ := κ)) hur hu₀ hurb hurw DTest.norm
    NativeSpinorVariation.contJet NativeSpinorVariation.continuous_contJet
    NativeSpinorVariation.norm_contJet_le NativeSpinorVariation.norm_contJet_sub_le
    (fun _ τ => NativeSpinorVariation.contJet τ)
    (fun _ τ => (NativeSpinorVariation.continuous_contJet τ).aestronglyMeasurable)
    (δ := fun _ => 0) tendsto_const_nhds (fun _ => le_rfl) (fun k τ z => by simp) (ε / 2)
    (by positivity)
  filter_upwards [h1, h2] with k hk1 hk2 τ
  have e0 : NativeSpinorVariation.contDiracVar D κ H S u₀ τ =
      ∫ z, (Gop D κ (RecDirac.SL D κ H.e₀ H.p H.A₀ S.H₀ S.Ψ₀ S.χ₀ z)
          (NativeSpinorVariation.contJet τ z) +
        Λop κ (RecDirac.SL D κ H.e₀ H.p H.A₀ S.H₀ S.Ψ₀ S.χ₀ z)
          (NativeSpinorVariation.contJet τ z) (u₀ z)) := rfl
  have hk2' := hk2 τ
  rw [abs_sub_comm] at hk2'
  calc _ ≤ |dVar D (n k : ℝ)⁻¹ (y k) (testRec κ (n k) (y k) τ) -
          NativeSpinorVariation.contDiracVar D κ H S u₀ τ| +
        |NativeSpinorVariation.contDiracVar D κ H S u₀ τ -
          diracRecVar D κ (R.f k) (R.g k) (R.A k) (R.Hr k) (R.Ψ k) (R.χ k) (ur k) τ| :=
        abs_sub_le _ _ _
    _ ≤ ε / 2 * τ.norm + ε / 2 * τ.norm := add_le_add (hk1 τ) (by rw [e0]; exact hk2')
    _ = ε * τ.norm := by ring

end DiracRec

/-! ### Continuity of the limit covectors along the reconstructions, sector by sector -/

section Close

open NativeDensity NativeHiggsVar NativeDiracLimit NativeDiracConvergence
open ShiftedJetAction (Grid)
open NativeDiracConv (CoHyp)
open NativeScaling (Mat)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (D : Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢) (T : 𝔄 →L[ℝ] E)
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- **Gravity**: the first-order Palatini covector is continuous along coframes in a compact
oriented chart converging with their first jets strongly in `L²`, uniformly on `C²` tests. -/
theorem grav_rec_close (κg Λ : ℝ) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hKdet : ∀ M ∈ Ke, 0 < M.det) {f : ℕ → 𝕋 → M4} {e₀ : 𝕋 → M4}
    {g : ℕ → Fin 4 → 𝕋 → M4} {p : Fin 4 → 𝕋 → M4}
    (hfK : ∀ k y', (f k y' : Mat) ∈ Ke) (hf : LpTendsto volume 2 f e₀)
    (hg : ∀ μ, LpTendsto volume 2 (fun k => g k μ) (p μ)) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : TorusC2Tests.C2Test M4,
      |NativeGravityFirstJet.contGravVariation κg Λ e₀ p τ -
        NativeGravityFirstJet.contGravVariation κg Λ (f k) (g k) τ| ≤ ε * τ.norm := by
  intro ε hε
  have hL := NativeGravityFirstJet.lpTendsto_limitCov κg Λ hKe hKdet hfK hf hg
  let Ke4 : Set M4 := Ke
  have he0K : ∀ᵐ y', e₀ y' ∈ Ke4 :=
    NativeDiracConv.ae_mem_of_lpTendsto two_ne_zero (Ke := Ke4) hKe.isClosed hf hfK
  have hev : ∀ᶠ k in atTop, ∫ y', ‖NativeGravityFirstJet.limitCov κg Λ (f k y')
      (fun μ => g k μ y') - NativeGravityFirstJet.limitCov κg Λ (e₀ y') (fun μ => p μ y')‖ ≤ ε :=
    (tendsto_order.1 (integral_norm_sub_tendsto hL)).2 ε hε |>.mono fun k hk => hk.le
  filter_upwards [hev] with k hk τ
  have hJc : Continuous fun y' => NativeGravityFirstJet.limitJet (τ.f y') (fun lam => τ.df lam y') :=
    continuous_prodMk.2 ⟨continuous_pi fun _ => (τ.f).continuous,
      continuous_pi fun sl => (τ.df sl.2).continuous⟩
  have hck : NativeGravityFirstJet.contGravVariation κg Λ (f k) (g k) τ =
      ∫ y', NativeGravityFirstJet.limitCov κg Λ (f k y') (fun μ => g k μ y')
        (NativeGravityFirstJet.limitJet (τ.f y') (fun lam => τ.df lam y')) :=
    integral_congr_ae (Eventually.of_forall fun y' => (NativeGravityFirstJet.limitCov_apply κg Λ
      (hKdet _ (hfK k y')).ne' (fun μ => g k μ y') (τ.f y') (fun lam => τ.df lam y')).symm)
  have hc0 : NativeGravityFirstJet.contGravVariation κg Λ e₀ p τ =
      ∫ y', NativeGravityFirstJet.limitCov κg Λ (e₀ y') (fun μ => p μ y')
        (NativeGravityFirstJet.limitJet (τ.f y') (fun lam => τ.df lam y')) := by
    refine integral_congr_ae ?_
    filter_upwards [he0K] with y' hy'
    exact (NativeGravityFirstJet.limitCov_apply κg Λ (hKdet _ hy').ne' (fun μ => p μ y') (τ.f y')
      (fun lam => τ.df lam y')).symm
  rw [hck, hc0]
  refine (abs_integral_apply_sub_le (memLp_one_iff_integrable.1 hL.memLp_lim)
    (memLp_one_iff_integrable.1 (hL.memLp k)) hJc (NativeGravityFirstJet.norm_limitJet_le τ)).trans
    (mul_le_mul_of_nonneg_right ?_ τ.norm_nonneg)
  refine (integral_congr_ae (Eventually.of_forall fun y' => norm_sub_rev _ _)).trans_le hk

/-- **Yang–Mills**: the continuum Yang–Mills covector at the limit fields `(e, A, F)` and at the
reconstructed fields `(f_h, A_h^rec, F(A_h^rec))` differ by `β_h → 0` uniformly on the `C²` ball of
radius `M`, once the curvature limit is identified (`curvature_identification`). -/
theorem ym_rec_close (H : CoHyp n y) {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    {P : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hP : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y k) ν))) (P μ ν))
    {f : ℕ → 𝕋 → M4} (hfK : ∀ k z, f k z ∈ H.Ke) (hf : LpTendsto volume 2 f H.e₀)
    {Ar : ℕ → Fin 4 → 𝕋 → 𝔄} (hAr : ∀ μ, LpTendsto volume 4 (fun k => Ar k μ) (H.A₀ μ))
    {dAr : ℕ → Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hdAr : ∀ μ ν, LpTendsto volume 2 (fun k => dAr k μ ν) (P μ ν)) (M : NNReal) :
    ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧ ∀ k, ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ M →
      |NativeYMMetric.firstVarCont T H.e₀ H.A₀ F τ.k.f (NativeYMBridge.toC1 τ.a) -
        NativeYMMetric.firstVarCont T (f k) (Ar k) (recCurv (Ar k) (dAr k)) τ.k.f
          (NativeYMBridge.toC1 τ.a)| ≤ β k := by
  have hFr : ∀ μ ν, μ < ν → LpTendsto volume 2 (fun k => recCurv (Ar k) (dAr k) μ ν) (F μ ν) :=
    fun μ ν _ => (lpTendsto_recCurv hAr hdAr μ ν).congr (fun k => Eventually.of_forall fun z => rfl)
      (curvature_identification H hF hP μ ν).symm
  obtain ⟨β, hβ, hcont⟩ := firstVarCont_unif T H.hKe (fun M hM => H.hKdet M hM) hf hfK hAr hFr M
  refine ⟨β, hβ, fun k τ hτ => ?_⟩
  have h2 := hcont k τ.k.f (NativeYMBridge.toC1 τ.a)
    (NativeYMBridge.metricBound_of_C2 τ.k (τ.k_le.trans hτ))
    (NativeYMBridge.gaugeBound_toC1 τ.a (τ.a_le.trans hτ))
  rwa [abs_sub_comm] at h2

/-- **Higgs**: the continuum Higgs covector at the limit fields and at the reconstructed fields
differ by at most `ε ‖v‖_{C²}` eventually. -/
theorem higgs_rec_close (H : CoHyp n y) (P : HiggsHyp D y)
    {f : ℕ → 𝕋 → M4} (hfK : ∀ k z, f k z ∈ H.Ke) (hf : LpTendsto volume 2 f H.e₀)
    {Ar : ℕ → Fin 4 → 𝕋 → 𝔄} (hAr : ∀ μ, LpTendsto volume 4 (fun k => Ar k μ) (H.A₀ μ))
    {Hr : ℕ → 𝕋 → 𝓗} (hHr : LpTendsto volume 4 Hr P.H₀)
    {dH : ℕ → Fin 4 → 𝕋 → 𝓗}
    (hdH : ∀ μ, LpTendsto volume 2 (fun k => dH k μ)
      (fun z => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z))) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W',
      |contHiggsVar D H P τ - higgsRecVar D (f k) (Ar k) (Hr k) (dH k) τ| ≤ ε * τ.norm := by
  intro ε hε
  have hL := lpTendsto_hcov_rec D H.hKe H.hKdet hf hfK hAr hHr hdH
  have hev : ∀ᶠ k in atTop, ∫ z, ‖hcov D (slotsOf D (f k z) (fun μ => Ar k μ z) (Hr k z)
      (fun μ => dH k μ z)) - hcov D (slotsOf D (H.e₀ z) (fun μ => H.A₀ μ z) (P.H₀ z)
        (fun μ => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z)))‖ ≤ ε :=
    (tendsto_order.1 (integral_norm_sub_tendsto hL)).2 ε hε |>.mono fun k hk => hk.le
  filter_upwards [hev] with k hk τ
  have hc0 : contHiggsVar D H P τ = ∫ z, hcov D (slotsOf D (H.e₀ z) (fun μ => H.A₀ μ z) (P.H₀ z)
      (fun μ => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z))) (contHJet τ z) := by
    simp only [contHiggsVar, contSlots_eq_slotsOf]
  rw [hc0]
  refine (abs_integral_apply_sub_le (memLp_one_iff_integrable.1 hL.memLp_lim)
    (memLp_one_iff_integrable.1 (hL.memLp k)) (continuous_contHJet τ) (norm_contHJet_le τ)).trans
    (mul_le_mul_of_nonneg_right ?_ τ.norm_nonneg)
  exact (integral_congr_ae (Eventually.of_forall fun z => norm_sub_rev _ _)).trans_le hk

/-- **Dirac–Yukawa**: the continuum Dirac–Yukawa covector at the limit fields (with `u₀`) and at
the reconstructed fields (with their first jets `u_h^rec ⇀ u₀`) differ by at most `ε ‖v‖_{C²}`
eventually. -/
theorem dirac_rec_close (H : CoHyp n y) (S : SpinHyp κ y) {u₀ : 𝕋 → Dif 𝓢 W'}
    (hu₀ : MemLp u₀ 2 volume) (R : RecDirac (W' := W') H.Ke H.e₀ H.p H.A₀ S.H₀ S.Ψ₀ S.χ₀)
    {ur : ℕ → 𝕋 → Dif 𝓢 W'} (hur : ∀ k, MemLp (ur k) 2 volume) {Cr : ℝ}
    (hurb : ∀ k, (eLpNorm (ur k) 2 volume).toReal ≤ Cr)
    (hurw : ∀ g : 𝕋 → Dif 𝓢 W' →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (ur k z)) atTop (𝓝 (∫ z, g z (u₀ z)))) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W',
      |NativeSpinorVariation.contDiracVar D κ H S u₀ τ -
        diracRecVar D κ (R.f k) (R.g k) (R.A k) (R.Hr k) (R.Ψ k) (R.χ k) (ur k) τ| ≤
          ε * τ.norm := by
  intro ε hε
  have h2 := WeakJetPairing.weak_jet_variation (R.lpTendsto_Gop (D := D) (κ := κ))
    (R.lpTendsto_Λop (D := D) (κ := κ)) hur hu₀ hurb hurw DTest.norm
    NativeSpinorVariation.contJet NativeSpinorVariation.continuous_contJet
    NativeSpinorVariation.norm_contJet_le NativeSpinorVariation.norm_contJet_sub_le
    (fun _ τ => NativeSpinorVariation.contJet τ)
    (fun _ τ => (NativeSpinorVariation.continuous_contJet τ).aestronglyMeasurable)
    (δ := fun _ => 0) tendsto_const_nhds (fun _ => le_rfl) (fun k τ z => by simp) ε hε
  filter_upwards [h2] with k hk τ
  have hk' := hk τ
  rw [abs_sub_comm] at hk'
  exact hk'

/-- **The continuum Einstein–SM first variation at the reconstructed fields**: Palatini at
`(f, g)`, Yang–Mills at `(f, A, F(A))` (`recCurv`), Higgs at `(f, A, H, ∂H)`, Dirac–Yukawa at
`(f, g, A, H, Ψ, χ)` with derivative slots `u`. -/
def recAllVar (f : 𝕋 → M4) (g : Fin 4 → 𝕋 → M4) (A : Fin 4 → 𝕋 → 𝔄)
    (dA : Fin 4 → Fin 4 → 𝕋 → 𝔄) (Hr : 𝕋 → 𝓗) (dH : Fin 4 → 𝕋 → 𝓗) (Ψ : 𝕋 → 𝓢) (χ : 𝕋 → W')
    (u : 𝕋 → Dif 𝓢 W') (τ : DTest 𝔄 𝓗 𝓢 W') : ℝ :=
  NativeGravityFirstJet.contGravVariation D.κ D.Λ f g τ.k +
    NativeYMMetric.firstVarCont T f A (recCurv A dA) τ.k.f (NativeYMBridge.toC1 τ.a) +
    higgsRecVar D f A Hr dH τ + diracRecVar D κ f g A Hr Ψ χ u τ

/-- **All sectors**: the continuum Einstein–SM first variation at the limit fields
(`NativeAllSector.contAllVar`) and at the reconstructed fields (`recAllVar`) differ by at most `ε`
eventually, uniformly on the `C²` ball of radius `M`. -/
theorem all_rec_close (H : CoHyp n y) (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M))
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    {Pc : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hPc : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y k) ν))) (Pc μ ν))
    (P : HiggsHyp D y) (S : SpinHyp κ y) {u₀ : 𝕋 → Dif 𝓢 W'} (hu₀ : MemLp u₀ 2 volume)
    (R : RecDirac (W' := W') H.Ke H.e₀ H.p H.A₀ S.H₀ S.Ψ₀ S.χ₀)
    (hH4 : LpTendsto volume 4 R.Hr P.H₀)
    {dAr : ℕ → Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hdAr : ∀ μ ν, LpTendsto volume 2 (fun k => dAr k μ ν) (Pc μ ν))
    {dH : ℕ → Fin 4 → 𝕋 → 𝓗}
    (hdH : ∀ μ, LpTendsto volume 2 (fun k => dH k μ)
      (fun z => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z)))
    {ur : ℕ → 𝕋 → Dif 𝓢 W'} (hur : ∀ k, MemLp (ur k) 2 volume) {Cr : ℝ}
    (hurb : ∀ k, (eLpNorm (ur k) 2 volume).toReal ≤ Cr)
    (hurw : ∀ g : 𝕋 → Dif 𝓢 W' →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (ur k z)) atTop (𝓝 (∫ z, g z (u₀ z)))) (M : NNReal) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ M →
      |NativeAllSector.contAllVar D κ T H F P S u₀ τ -
        recAllVar D κ T (R.f k) (R.g k) (R.A k) (dAr k) (R.Hr k) (dH k) (R.Ψ k) (R.χ k) (ur k) τ|
          ≤ ε := by
  intro ε hε
  have hM0 : (0 : ℝ) ≤ M := M.2
  set ε' : ℝ := ε / (4 * ((M : ℝ) + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'M : ε' * M ≤ ε / 4 := by
    rw [hε', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hG := grav_rec_close D.κ D.Λ (Ke := (H.Ke : Set Mat)) H.hKe hpos R.hfK R.hf R.hg ε' hε'0
  obtain ⟨β, hβ, hYM⟩ := ym_rec_close (W' := W') T H hF hPc R.hfK R.hf R.hA hdAr M
  have hβε : ∀ᶠ k in atTop, β k ≤ ε / 4 :=
    (tendsto_order.1 hβ).2 (ε / 4) (by positivity) |>.mono fun k hk => hk.le
  have hHi := higgs_rec_close D (W' := W') H P R.hfK R.hf R.hA hH4 hdH ε' hε'0
  have hDi := dirac_rec_close D κ H S hu₀ R hur hurb hurw ε' hε'0
  filter_upwards [hG, hβε, hHi, hDi] with k hg hb hh hd τ hτ
  have hk : τ.k.norm ≤ M := τ.k_le.trans hτ
  have hτ' : ε' * τ.norm ≤ ε / 4 := (mul_le_mul_of_nonneg_left hτ hε'0.le).trans hε'M
  have hk' : ε' * τ.k.norm ≤ ε / 4 := (mul_le_mul_of_nonneg_left hk hε'0.le).trans hε'M
  have h1 := hg τ.k
  have h2 := hYM k τ hτ
  have h3 := hh τ
  have h4 := hd τ
  unfold NativeAllSector.contAllVar recAllVar
  set a1 := NativeGravityFirstJet.contGravVariation D.κ D.Λ H.e₀ H.p τ.k
  set b1 := NativeGravityFirstJet.contGravVariation D.κ D.Λ (R.f k) (R.g k) τ.k
  set a2 := NativeYMMetric.firstVarCont T H.e₀ H.A₀ F τ.k.f (NativeYMBridge.toC1 τ.a)
  set b2 := NativeYMMetric.firstVarCont T (R.f k) (R.A k) (recCurv (R.A k) (dAr k)) τ.k.f
    (NativeYMBridge.toC1 τ.a)
  set a3 := contHiggsVar D H P τ
  set b3 := higgsRecVar D (R.f k) (R.A k) (R.Hr k) (dH k) τ
  set a4 := NativeSpinorVariation.contDiracVar D κ H S u₀ τ
  set b4 := diracRecVar D κ (R.f k) (R.g k) (R.A k) (R.Hr k) (R.Ψ k) (R.χ k) (ur k) τ
  have e : a1 + a2 + a3 + a4 - (b1 + b2 + b3 + b4) =
      (a1 - b1) + (a2 - b2) + (a3 - b3) + (a4 - b4) := by ring
  rw [e]
  calc _ ≤ |a1 - b1| + |a2 - b2| + |a3 - b3| + |a4 - b4| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_three _ _ _) le_rfl)
    _ ≤ ε / 4 + ε / 4 + ε / 4 + ε / 4 := by
        gcongr
        · exact h1.trans hk'
        · exact h2.trans hb
        · exact h3.trans hτ'
        · exact h4.trans hτ'
    _ = ε := by ring

end Close

/-! ### Comparison hypotheses -/

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A reconstruction compared with a strongly convergent raw reconstruction converges to the same
limit: `u_k - v_k → 0` and `v_k → v` give `u_k → v`. -/
theorem lpTendsto_of_sub {p : ℝ≥0∞} [Fact (1 ≤ p)] {u v : ℕ → 𝕋 → E} {v₀ : 𝕋 → E}
    (huv : LpTendsto volume p (fun k => u k - v k) 0) (hv : LpTendsto volume p v v₀) :
    LpTendsto volume p u v₀ :=
  (huv.add hv).congr (fun k => Eventually.of_forall fun z => by simp)
    (Eventually.of_forall fun z => by simp)

/-- The weak form: if `v_k ⇀ u₀` weakly in `L²` and `u_k - v_k ⇀ 0`, then `u_k ⇀ u₀`. -/
theorem weak_of_sub {u v : ℕ → 𝕋 → E} {u₀ : 𝕋 → E} (hu : ∀ k, MemLp (u k) 2 volume)
    (hv : ∀ k, MemLp (v k) 2 volume)
    (hvw : ∀ g : 𝕋 → E →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (v k z)) atTop (𝓝 (∫ z, g z (u₀ z))))
    (huv : ∀ g : 𝕋 → E →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (u k z - v k z)) atTop (𝓝 0)) :
    ∀ g : 𝕋 → E →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (u k z)) atTop (𝓝 (∫ z, g z (u₀ z))) := by
  intro g hg
  have h := (huv g hg).add (hvw g hg)
  rw [zero_add] at h
  refine h.congr fun k => ?_
  have i1 : Integrable (fun z => g z (u k z - v k z)) volume :=
    WeakJetPairing.integrable_bilin_two_two (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)) hg
      ((hu k).sub (hv k))
  have i2 : Integrable (fun z => g z (v k z)) volume :=
    WeakJetPairing.integrable_bilin_two_two (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)) hg (hv k)
  rw [← integral_add i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [map_sub]

end Comparison

/-! ### The final paragraph of `thm:native-firstvariation-no-band` from `(N1)–(N4)` -/

section Closure

open NativeDensity NativeHiggsVar NativeDiracLimit NativeDiracConvergence
open ShiftedJetAction (Grid)
open NativeDiracConv (CoHyp qM)
open NativeScaling (Mat)
open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)
open TorusPiecewiseConstantTranslation (gridNorm)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {r r' : ℕ} [NeZero r] [NeZero r']
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

set_option maxHeartbeats 3200000 in
-- the statement assembles the four sector theorems along one extraction
/-- **`thm:native-firstvariation-no-band`, final paragraph, from `(N1)–(N4)`** (fixed coefficient
bank; unit-torus rendering; Higgs fibre `ℝ^{r_H}` in an orthonormal frame; co-spinors read with
`κ = id`).  Under the hypotheses of `NativeAllSectorGraph.native_all_sector_closure`, assume in
addition that the **ordinary connection first differences converge strongly**,
`R^0 D⁺_μ A_{ν,h} → P_{μν}` in `L²`, and let the complete unfiltered reconstructed fields
(coframes `f_h` **in the same compact chart**, coframe jets `g_h`, connections `A_h^rec`, connection
jets `∂A_h^rec`, Higgs fields `H_h^rec`, Higgs jets `∂H_h^rec`, spinors `Ψ_h^rec`, co-spinors
`χ_h^rec` and spinor jets `u_h^rec`) obey the comparison estimates with the raw reconstructions
(`eq:native-reconstruction-comparison`): `f_h - R^0e_h → 0`, `g_h - R^0D⁺e_h → 0`,
`∂A_h^rec - R^0D⁺A_h → 0`, `∂H_h^rec - R^0D⁺H_h → 0`, `Ψ_h^rec - R^0Ψ_h → 0`,
`χ_h^rec - R^0Ψ̄_h → 0` in `L²`, `A_h^rec - R^0A_h → 0`, `H_h^rec - R^0H_h → 0` in `L⁴`, uniform
`L⁴` bounds of the reconstructed spinors, and `u_h^rec - R^0D⁺(Ψ_h, Ψ̄_h) ⇀ 0` weakly and
boundedly in `L²`.  Then, along one extraction:
* the all-sector limit `eq:native-all-sector-limit` holds;
* `F_{μν} = P_{μν} - P_{νμ} + [A_μ, A_ν]` a.e. (strong ordinary connection first-jet convergence
  identifies the complete reconstructed curvature);
* **the sectorwise consistency errors relative to the reconstructed fields tend to zero**:
  gravity (Palatini at `(f_h, g_h)`), Yang–Mills (at `(f_h, A_h^rec, F(A_h^rec))`), Higgs (at
  `(f_h, A_h^rec, H_h^rec, ∂H_h^rec)`), Dirac–Yukawa (at the reconstructed spinors with jets
  `u_h^rec`), uniformly on `C²` test balls, and so does the total error. -/
theorem native_reconstructed_closure (D : Data 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (T : 𝔄 →L[ℝ] E) (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r'))
    {y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢} (H : CoHyp n y)
    (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M)) (hc : H.c ≤ 1 / 64)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    (hUH : ∀ k x μ (v : EuclideanSpace ℝ (Fin rH)),
      ‖exp ((n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)) v‖ = ‖v‖)
    {BH : ℝ} (hHb : ∀ k, gridNorm (higgs (y k)) ≤ BH)
    {K₀ : Fin 4 → 𝕋 → EuclideanSpace ℝ (Fin rH)}
    (hK : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => higgsLink D (n k : ℝ)⁻¹ (y k) x μ))
      (K₀ μ))
    (hU : ∀ k x μ (v : 𝓢), ‖D.ρS (exp ((n k : ℝ)⁻¹ • gauge (y k) μ x)) v‖ = ‖v‖)
    {B : ℝ} (hΨ : ∀ k, gridNorm (psi (y k)) ≤ B)
    (hKs : ∀ k μ, gridNorm (fun x => spinGraph D (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    (hΨb : ∀ k, gridNorm (psiBar (y k)) ≤ B)
    (hKb : ∀ k μ, gridNorm (fun x => dualGraph D (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    -- the ordinary connection first differences converge strongly
    {Pc : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hPc : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y k) ν))) (Pc μ ν))
    -- the reconstructed fields and their comparison with the raw reconstructions
    (f : ℕ → 𝕋 → M4) (hfK : ∀ k z, f k z ∈ H.Ke)
    (hfc : LpTendsto volume 2 (fun k => f k - pc (coframeM (y k))) 0)
    (g : ℕ → Fin 4 → 𝕋 → M4)
    (hgc : ∀ lam, LpTendsto volume 2 (fun k => g k lam - pc (qM (y k) lam)) 0)
    (Ar : ℕ → Fin 4 → 𝕋 → 𝔄)
    (hAc : ∀ μ, LpTendsto volume 4 (fun k => Ar k μ - pc (gauge (y k) μ)) 0)
    (dAr : ℕ → Fin 4 → Fin 4 → 𝕋 → 𝔄)
    (hdAc : ∀ μ ν, LpTendsto volume 2
      (fun k => dAr k μ ν - pc (NativeHiggs.DpV μ (gauge (y k) ν))) 0)
    (Hr : ℕ → 𝕋 → EuclideanSpace ℝ (Fin rH))
    (hHc : LpTendsto volume 4 (fun k => Hr k - pc (higgs (y k))) 0)
    (dH : ℕ → Fin 4 → 𝕋 → EuclideanSpace ℝ (Fin rH))
    (hdHc : ∀ μ, LpTendsto volume 2 (fun k => dH k μ - pc (NativeHiggs.DpV μ (higgs (y k)))) 0)
    (Ψr : ℕ → 𝕋 → 𝓢) (hΨc : LpTendsto volume 2 (fun k => Ψr k - pc (psi (y k))) 0)
    (χr : ℕ → 𝕋 → CoSpinor 𝓢) (hχc : LpTendsto volume 2 (fun k => χr k - pc (psiBar (y k))) 0)
    {B4 : ℝ≥0∞} (hB4 : B4 ≠ ∞) (hΨ4 : ∀ k, eLpNorm (Ψr k) 4 volume ≤ B4)
    (hχ4 : ∀ k, eLpNorm (χr k) 4 volume ≤ B4)
    (ur : ℕ → 𝕋 → Dif 𝓢 (CoSpinor 𝓢)) (hur : ∀ k, MemLp (ur k) 2 volume) {Cr : ℝ}
    (hurb : ∀ k, (eLpNorm (ur k) 2 volume).toReal ≤ Cr)
    (hurw : ∀ G : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) →L[ℝ] ℝ, MemLp G 2 volume →
      Tendsto (fun k => ∫ z, G z (ur k z - pc (difs (y k) (psiBar (y k))) z)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ, ∃ P : HiggsHyp D (fun k => y (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:native-all-sector-limit`
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar D (n (φ k)) (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeAllSector.contAllVar D (κid 𝓢) T (coHypSubseq H hφ) F P S u₀ τ| ≤ ε) ∧
      -- the reconstructed curvature identification
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] recCurv H.A₀ Pc μ ν) ∧
      -- gravity relative to the reconstructed coframes
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τk : TorusC2Tests.C2Test M4,
        |NativeGravityFirstJet.gravVariation D (n (φ k)) (y (φ k)) τk -
          NativeGravityFirstJet.contGravVariation D.κ D.Λ (f (φ k)) (g (φ k)) τk| ≤
            ε * τk.norm) ∧
      -- Yang–Mills relative to the reconstructed fields
      (∀ M : NNReal, ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧ ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeYMBridge.ymVar D (n (φ k)) (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeYMMetric.firstVarCont T (f (φ k)) (Ar (φ k)) (recCurv (Ar (φ k)) (dAr (φ k)))
            τ.k.f (NativeYMBridge.toC1 τ.a)| ≤ β k) ∧
      -- Higgs relative to the reconstructed fields
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        |higgsVar D (n (φ k)) (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          higgsRecVar D (f (φ k)) (Ar (φ k)) (Hr (φ k)) (dH (φ k)) τ| ≤ ε * τ.norm) ∧
      -- Dirac–Yukawa relative to the reconstructed fields
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        |NativeDirac.dVar D (n (φ k) : ℝ)⁻¹ (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          diracRecVar D (κid 𝓢) (f (φ k)) (g (φ k)) (Ar (φ k)) (Hr (φ k)) (Ψr (φ k)) (χr (φ k))
            (ur (φ k)) τ| ≤ ε * τ.norm) ∧
      -- the total error relative to the reconstructed fields
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar D (n (φ k)) (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          recAllVar D (κid 𝓢) T (f (φ k)) (g (φ k)) (Ar (φ k)) (dAr (φ k)) (Hr (φ k)) (dH (φ k))
            (Ψr (φ k)) (χr (φ k)) (ur (φ k)) τ| ≤ ε) := by
  -- the extraction of `native_all_sector_closure`
  obtain ⟨φ₁, hφ₁, P₁, hP₁, hDH⟩ := NativeHiggsVar.exists_higgsHyp D H.hn H.hA hUH hHb hK
  have hn₁ : Tendsto (fun k => n (φ₁ k)) atTop atTop := H.hn.comp hφ₁.tendsto_atTop
  obtain ⟨φ₂, hφ₂, S, u₀, hSH, hu₀, ⟨C, hub⟩, hw, -, -⟩ :=
    NativeSpinorGraph.native_spinor_extraction D Θ Θ' hn₁
      (fun μ => (H.hA μ).comp_strictMono hφ₁) (P₁.hH.mono (by norm_num) (by norm_num))
      (fun k => hU (φ₁ k)) (fun k => hΨ (φ₁ k)) (fun k => hKs (φ₁ k)) (fun k => hΨb (φ₁ k))
      (fun k => hKb (φ₁ k))
  have hφ : StrictMono (fun k => φ₁ (φ₂ k)) := hφ₁.comp hφ₂
  set φ : ℕ → ℕ := fun k => φ₁ (φ₂ k) with hφdef
  set P := NativeAllSectorGraph.higgsHypSubseq P₁ hφ₂ with hPdef
  set H' := coHypSubseq H hφ with hH'
  have hF' : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (gauge (y (φ k))) x μ ν)) (F μ ν) :=
    fun μ ν => (hF μ ν).comp_strictMono hφ
  have hPc' : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (NativeHiggs.DpV μ (gauge (y (φ k)) ν))) (Pc μ ν) :=
    fun μ ν => (hPc μ ν).comp_strictMono hφ
  have hlim := NativeAllSector.native_all_sector_limit D (κid 𝓢) T hip H' hpos hc hF' P S hu₀
    hub hw
  -- the reconstructions along the extraction
  have hf' : LpTendsto volume 2 (fun k => f (φ k)) H.e₀ :=
    lpTendsto_of_sub (hfc.comp_strictMono hφ) H'.he
  have hg' : ∀ lam, LpTendsto volume 2 (fun k => g (φ k) lam) (H.p lam) := fun lam =>
    lpTendsto_of_sub ((hgc lam).comp_strictMono hφ) (H'.hp lam)
  have hAr' : ∀ μ, LpTendsto volume 4 (fun k => Ar (φ k) μ) (H.A₀ μ) := fun μ =>
    lpTendsto_of_sub ((hAc μ).comp_strictMono hφ) (H'.hA μ)
  have hdAr' : ∀ μ ν, LpTendsto volume 2 (fun k => dAr (φ k) μ ν) (Pc μ ν) := fun μ ν =>
    lpTendsto_of_sub ((hdAc μ ν).comp_strictMono hφ) (hPc' μ ν)
  have hHr4 : LpTendsto volume 4 (fun k => Hr (φ k)) P.H₀ :=
    lpTendsto_of_sub (hHc.comp_strictMono hφ) P.hH
  have hHr2 : LpTendsto volume 2 (fun k => Hr (φ k)) S.H₀ := by
    rw [hSH]; exact hHr4.mono two_ne_zero (by norm_num)
  have hdH' : ∀ μ, LpTendsto volume 2 (fun k => dH (φ k) μ)
      (fun z => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z)) := by
    intro μ
    have h2 := (hDH μ).comp_strictMono hφ₂
    have hK₀ : P.K₀ = K₀ := hP₁
    rw [hK₀]
    exact lpTendsto_of_sub ((hdHc μ).comp_strictMono hφ) h2
  have hχeq : ∀ k, S.χ k = psiBar (y (φ k)) := fun k =>
    funext fun x => (congrFun (S.hχ k) x).symm
  have hΨr' : LpTendsto volume 2 (fun k => Ψr (φ k)) S.Ψ₀ :=
    lpTendsto_of_sub (hΨc.comp_strictMono hφ) S.hΨ
  have hχr' : LpTendsto volume 2 (fun k => χr (φ k)) S.χ₀ := by
    refine lpTendsto_of_sub (hχc.comp_strictMono hφ) ?_
    refine S.hχ₀.congr (fun k => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => rfl)
    rw [hχeq k]
  let R : RecDirac (W' := CoSpinor 𝓢) H'.Ke H'.e₀ H'.p H'.A₀ S.H₀ S.Ψ₀ S.χ₀ :=
    { hKe := H.hKe, hKdet := H.hKdet, f := fun k => f (φ k), hfK := fun k => hfK (φ k),
      hf := hf', g := fun k => g (φ k), hg := hg', A := fun k => Ar (φ k), hA := hAr',
      Hr := fun k => Hr (φ k), hH := hHr2, Ψ := fun k => Ψr (φ k), hΨ := hΨr',
      χ := fun k => χr (φ k), hχ := hχr', B4 := B4, hB4 := hB4, hΨ4 := fun k => hΨ4 (φ k),
      hχ4 := fun k => hχ4 (φ k) }
  have hurw' : ∀ G : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) →L[ℝ] ℝ, MemLp G 2 volume →
      Tendsto (fun k => ∫ z, G z (ur (φ k) z)) atTop (𝓝 (∫ z, G z (u₀ z))) := by
    refine weak_of_sub (fun k => hur (φ k))
      (fun k => TorusPiecewiseConstantTranslation.memLp_pc _) hw fun G hG => ?_
    refine ((hurw G hG).comp hφ.tendsto_atTop).congr fun k => ?_
    simp only [Function.comp_apply, hχeq k]
    rfl
  refine ⟨φ, hφ, P, S, u₀, hlim, curvature_identification H hF hPc, ?_, ?_, ?_, ?_, ?_⟩
  · exact NativeGravityFirstJet.native_gravity_firstjet_reconstructed D H'.hn (fun k => y (φ k))
      H.e₀ H.p (Ke := (H.Ke : Set Mat)) H.hKe hpos H'.hval hc H'.hmar H'.he H'.hp
      (fun k => f (φ k)) (fun k => g (φ k)) (fun k => hfK (φ k)) hf' hg'
  · exact fun M => native_YM_reconstructed D (κid 𝓢) T hip H' hF' hPc' (fun k => hfK (φ k)) hf'
      hAr' hdAr' M
  · exact native_Higgs_reconstructed D (κid 𝓢) H' P (fun k => hfK (φ k)) hf' hAr' hHr4 hdH'
  · exact native_Dirac_reconstructed D (κid 𝓢) H' S hu₀ hub hw R (fun k => hur (φ k))
      (fun k => hurb (φ k)) hurw'
  · intro M ε hε
    have h1 := hlim M (ε / 2) (by positivity)
    have h2 := all_rec_close D (κid 𝓢) T H' hpos hF' hPc' P S hu₀ R hHr4 hdAr' hdH'
      (fun k => hur (φ k)) (fun k => hurb (φ k)) hurw' M (ε / 2) (by positivity)
    filter_upwards [h1, h2] with k hk1 hk2 τ hτ
    have := abs_sub_le (NativeAllSector.nativeVar D (n (φ k)) (y (φ k))
      (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ))
      (NativeAllSector.contAllVar D (κid 𝓢) T H' F P S u₀ τ)
      (recAllVar D (κid 𝓢) T (f (φ k)) (g (φ k)) (Ar (φ k)) (dAr (φ k)) (Hr (φ k)) (dH (φ k))
        (Ψr (φ k)) (χr (φ k)) (ur (φ k)) τ)
    linarith [hk1 τ hτ, hk2 τ hτ]

end Closure

/-! ### Varying coefficient banks `(N5)` -/

section ClosureBank

open NativeDensity NativeHiggsVar NativeDiracLimit NativeDiracConvergence NativeBank
open ShiftedJetAction (Grid)
open NativeDiracConv (CoHyp qM)
open NativeScaling (Mat)
open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)
open TorusPiecewiseConstantTranslation (gridNorm)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {r r' : ℕ} [NeZero r] [NeZero r']
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {J : ℕ}

set_option maxHeartbeats 3200000 in
-- the statement assembles the bank limit and the reconstructed continuity along one extraction
/-- **`thm:native-firstvariation-no-band`, final paragraph, with varying coefficient banks
`(N5)`.**  Hypotheses of `NativeBank.native_all_sector_closure_bank` (cutoff banks `θ_h → θ`,
`κ ≠ 0`, nonnegative limit gauge weights), the strong convergence of the ordinary connection first
differences, and the reconstruction comparison hypotheses of `native_reconstructed_closure`.  Then
along one extraction: the all-sector limit with the cutoff banks, the reconstructed curvature
identification, **the complete consistency error of the finite action at the cutoff banks
relative to the continuum first variation at the limit bank evaluated at the reconstructed
fields** tends to zero uniformly on every `C²` ball, and so do the sectorwise differences between
the limit-field and the reconstructed-field continuum covectors (gravity, Yang–Mills, Higgs,
Dirac–Yukawa). -/
theorem native_reconstructed_closure_bank (D₀ : Data 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (Tj : Fin J → 𝔄 →L[ℝ] E) {θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢}
    {θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢} (hθ : BankConv θs θ) (hκ : θ.κ ≠ 0)
    (hwθ : ∀ j, 0 ≤ θ.w j)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r'))
    {y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢} (H : CoHyp n y)
    (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M)) (hc : H.c ≤ 1 / 64)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    (hUH : ∀ k x μ (v : EuclideanSpace ℝ (Fin rH)),
      ‖exp ((n k : ℝ)⁻¹ • D₀.ρHL (gauge (y k) μ x)) v‖ = ‖v‖)
    {BH : ℝ} (hHb : ∀ k, gridNorm (higgs (y k)) ≤ BH)
    {K₀ : Fin 4 → 𝕋 → EuclideanSpace ℝ (Fin rH)}
    (hK : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => higgsLink D₀ (n k : ℝ)⁻¹ (y k) x μ))
      (K₀ μ))
    (hU : ∀ k x μ (v : 𝓢), ‖D₀.ρS (exp ((n k : ℝ)⁻¹ • gauge (y k) μ x)) v‖ = ‖v‖)
    {B : ℝ} (hΨ : ∀ k, gridNorm (psi (y k)) ≤ B)
    (hKs : ∀ k μ, gridNorm (fun x => spinGraph D₀ (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    (hΨb : ∀ k, gridNorm (psiBar (y k)) ≤ B)
    (hKb : ∀ k μ, gridNorm (fun x => dualGraph D₀ (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    {Pc : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hPc : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y k) ν))) (Pc μ ν))
    (f : ℕ → 𝕋 → M4) (hfK : ∀ k z, f k z ∈ H.Ke)
    (hfc : LpTendsto volume 2 (fun k => f k - pc (coframeM (y k))) 0)
    (g : ℕ → Fin 4 → 𝕋 → M4)
    (hgc : ∀ lam, LpTendsto volume 2 (fun k => g k lam - pc (qM (y k) lam)) 0)
    (Ar : ℕ → Fin 4 → 𝕋 → 𝔄)
    (hAc : ∀ μ, LpTendsto volume 4 (fun k => Ar k μ - pc (gauge (y k) μ)) 0)
    (dAr : ℕ → Fin 4 → Fin 4 → 𝕋 → 𝔄)
    (hdAc : ∀ μ ν, LpTendsto volume 2
      (fun k => dAr k μ ν - pc (NativeHiggs.DpV μ (gauge (y k) ν))) 0)
    (Hr : ℕ → 𝕋 → EuclideanSpace ℝ (Fin rH))
    (hHc : LpTendsto volume 4 (fun k => Hr k - pc (higgs (y k))) 0)
    (dH : ℕ → Fin 4 → 𝕋 → EuclideanSpace ℝ (Fin rH))
    (hdHc : ∀ μ, LpTendsto volume 2 (fun k => dH k μ - pc (NativeHiggs.DpV μ (higgs (y k)))) 0)
    (Ψr : ℕ → 𝕋 → 𝓢) (hΨc : LpTendsto volume 2 (fun k => Ψr k - pc (psi (y k))) 0)
    (χr : ℕ → 𝕋 → CoSpinor 𝓢) (hχc : LpTendsto volume 2 (fun k => χr k - pc (psiBar (y k))) 0)
    {B4 : ℝ≥0∞} (hB4 : B4 ≠ ∞) (hΨ4 : ∀ k, eLpNorm (Ψr k) 4 volume ≤ B4)
    (hχ4 : ∀ k, eLpNorm (χr k) 4 volume ≤ B4)
    (ur : ℕ → 𝕋 → Dif 𝓢 (CoSpinor 𝓢)) (hur : ∀ k, MemLp (ur k) 2 volume) {Cr : ℝ}
    (hurb : ∀ k, (eLpNorm (ur k) 2 volume).toReal ≤ Cr)
    (hurw : ∀ G : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) →L[ℝ] ℝ, MemLp G 2 volume →
      Tendsto (fun k => ∫ z, G z (ur k z - pc (difs (y k) (psiBar (y k))) z)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ,
      ∃ P : HiggsHyp (bankData D₀ Tj θ) (fun k => y (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData D₀ Tj (θs (φ k))) (n (φ k)) (y (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeAllSector.contAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (coHypSubseq H hφ) F P S u₀ τ| ≤ ε) ∧
      -- the reconstructed curvature identification
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] recCurv H.A₀ Pc μ ν) ∧
      -- `K = D_A H`
      P.K₀ = K₀ ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y (φ k)))))
        (fun z => K₀ μ z - D₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      -- `u₀ = (∂Ψ, ∂Ψ̄)`: the spinors converge weakly in `H¹`
      (∀ j, ∃ f : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      (∀ j, ∃ f : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ' (S.χ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ' ((u₀ z).2 μ) j : ℝ) : ℂ)) ∧
      -- the complete error relative to the reconstructed fields, cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData D₀ Tj (θs (φ k))) (n (φ k)) (y (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          recAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w) (f (φ k)) (g (φ k)) (Ar (φ k))
            (dAr (φ k)) (Hr (φ k)) (dH (φ k)) (Ψr (φ k)) (χr (φ k)) (ur (φ k)) τ| ≤ ε) ∧
      -- sectorwise: limit-field versus reconstructed-field covectors at the limit bank
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τk : TorusC2Tests.C2Test M4,
        |NativeGravityFirstJet.contGravVariation θ.κ θ.Λ H.e₀ H.p τk -
          NativeGravityFirstJet.contGravVariation θ.κ θ.Λ (f (φ k)) (g (φ k)) τk| ≤
            ε * τk.norm) ∧
      (∀ M : NNReal, ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧ ∀ k,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeYMMetric.firstVarCont (bankT Tj θ.w) H.e₀ H.A₀ F τ.k.f (NativeYMBridge.toC1 τ.a) -
          NativeYMMetric.firstVarCont (bankT Tj θ.w) (f (φ k)) (Ar (φ k))
            (recCurv (Ar (φ k)) (dAr (φ k))) τ.k.f (NativeYMBridge.toC1 τ.a)| ≤ β k) ∧
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        |contHiggsVar (bankData D₀ Tj θ) (coHypSubseq H hφ) P τ -
          higgsRecVar (bankData D₀ Tj θ) (f (φ k)) (Ar (φ k)) (Hr (φ k)) (dH (φ k)) τ| ≤
            ε * τ.norm) ∧
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        |NativeSpinorVariation.contDiracVar (bankData D₀ Tj θ) (κid 𝓢) (coHypSubseq H hφ) S u₀ τ -
          diracRecVar (bankData D₀ Tj θ) (κid 𝓢) (f (φ k)) (g (φ k)) (Ar (φ k)) (Hr (φ k))
            (Ψr (φ k)) (χr (φ k)) (ur (φ k)) τ| ≤ ε * τ.norm) := by
  set D := bankData D₀ Tj θ with hD
  obtain ⟨φ₁, hφ₁, P₁, hP₁, hDH⟩ := NativeHiggsVar.exists_higgsHyp D H.hn H.hA hUH hHb hK
  have hn₁ : Tendsto (fun k => n (φ₁ k)) atTop atTop := H.hn.comp hφ₁.tendsto_atTop
  obtain ⟨φ₂, hφ₂, S, u₀, hSH, hu₀, ⟨C, hub⟩, hw, hid1, hid2⟩ :=
    NativeSpinorGraph.native_spinor_extraction D Θ Θ' hn₁
      (fun μ => (H.hA μ).comp_strictMono hφ₁) (P₁.hH.mono (by norm_num) (by norm_num))
      (fun k => hU (φ₁ k)) (fun k => hΨ (φ₁ k)) (fun k => hKs (φ₁ k)) (fun k => hΨb (φ₁ k))
      (fun k => hKb (φ₁ k))
  have hφ : StrictMono (fun k => φ₁ (φ₂ k)) := hφ₁.comp hφ₂
  set φ : ℕ → ℕ := fun k => φ₁ (φ₂ k) with hφdef
  set P := NativeAllSectorGraph.higgsHypSubseq P₁ hφ₂ with hPdef
  set H' := coHypSubseq H hφ with hH'
  have hF' : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (gauge (y (φ k))) x μ ν)) (F μ ν) :=
    fun μ ν => (hF μ ν).comp_strictMono hφ
  have hPc' : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (NativeHiggs.DpV μ (gauge (y (φ k)) ν))) (Pc μ ν) :=
    fun μ ν => (hPc μ ν).comp_strictMono hφ
  have hθ' : BankConv (fun k => θs (φ k)) θ :=
    ⟨hθ.κ.comp hφ.tendsto_atTop, hθ.Λ.comp hφ.tendsto_atTop, hθ.lamH.comp hφ.tendsto_atTop,
      hθ.vH.comp hφ.tendsto_atTop, fun j => (hθ.w j).comp hφ.tendsto_atTop,
      hθ.Y.comp hφ.tendsto_atTop⟩
  have hlim := native_all_sector_limit_bank D₀ Tj (κid 𝓢) hθ' hκ hwθ H' hpos hc hF' P S hu₀ hub hw
  -- the reconstructions along the extraction
  have hf' : LpTendsto volume 2 (fun k => f (φ k)) H.e₀ :=
    lpTendsto_of_sub (hfc.comp_strictMono hφ) H'.he
  have hg' : ∀ lam, LpTendsto volume 2 (fun k => g (φ k) lam) (H.p lam) := fun lam =>
    lpTendsto_of_sub ((hgc lam).comp_strictMono hφ) (H'.hp lam)
  have hAr' : ∀ μ, LpTendsto volume 4 (fun k => Ar (φ k) μ) (H.A₀ μ) := fun μ =>
    lpTendsto_of_sub ((hAc μ).comp_strictMono hφ) (H'.hA μ)
  have hdAr' : ∀ μ ν, LpTendsto volume 2 (fun k => dAr (φ k) μ ν) (Pc μ ν) := fun μ ν =>
    lpTendsto_of_sub ((hdAc μ ν).comp_strictMono hφ) (hPc' μ ν)
  have hHr4 : LpTendsto volume 4 (fun k => Hr (φ k)) P.H₀ :=
    lpTendsto_of_sub (hHc.comp_strictMono hφ) P.hH
  have hHr2 : LpTendsto volume 2 (fun k => Hr (φ k)) S.H₀ := by
    rw [hSH]; exact hHr4.mono two_ne_zero (by norm_num)
  have hdH' : ∀ μ, LpTendsto volume 2 (fun k => dH (φ k) μ)
      (fun z => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z)) := by
    intro μ
    have h2 := (hDH μ).comp_strictMono hφ₂
    have hK₀ : P.K₀ = K₀ := hP₁
    rw [hK₀]
    exact lpTendsto_of_sub ((hdHc μ).comp_strictMono hφ) h2
  have hχeq : ∀ k, S.χ k = psiBar (y (φ k)) := fun k =>
    funext fun x => (congrFun (S.hχ k) x).symm
  have hΨr' : LpTendsto volume 2 (fun k => Ψr (φ k)) S.Ψ₀ :=
    lpTendsto_of_sub (hΨc.comp_strictMono hφ) S.hΨ
  have hχr' : LpTendsto volume 2 (fun k => χr (φ k)) S.χ₀ := by
    refine lpTendsto_of_sub (hχc.comp_strictMono hφ) ?_
    refine S.hχ₀.congr (fun k => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => rfl)
    rw [hχeq k]
  let R : RecDirac (W' := CoSpinor 𝓢) H'.Ke H'.e₀ H'.p H'.A₀ S.H₀ S.Ψ₀ S.χ₀ :=
    { hKe := H.hKe, hKdet := H.hKdet, f := fun k => f (φ k), hfK := fun k => hfK (φ k),
      hf := hf', g := fun k => g (φ k), hg := hg', A := fun k => Ar (φ k), hA := hAr',
      Hr := fun k => Hr (φ k), hH := hHr2, Ψ := fun k => Ψr (φ k), hΨ := hΨr',
      χ := fun k => χr (φ k), hχ := hχr', B4 := B4, hB4 := hB4, hΨ4 := fun k => hΨ4 (φ k),
      hχ4 := fun k => hχ4 (φ k) }
  have hurw' : ∀ G : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) →L[ℝ] ℝ, MemLp G 2 volume →
      Tendsto (fun k => ∫ z, G z (ur (φ k) z)) atTop (𝓝 (∫ z, G z (u₀ z))) := by
    refine weak_of_sub (fun k => hur (φ k))
      (fun k => TorusPiecewiseConstantTranslation.memLp_pc _) hw fun G hG => ?_
    refine ((hurw G hG).comp hφ.tendsto_atTop).congr fun k => ?_
    simp only [Function.comp_apply, hχeq k]
    rfl
  refine ⟨φ, hφ, P, S, u₀, hlim, curvature_identification H hF hPc, hP₁,
    fun μ => (hDH μ).comp_strictMono hφ₂, hid1, hid2, ?_, ?_, ?_, ?_, ?_⟩
  · intro M ε hε
    have h1 := hlim M (ε / 2) (by positivity)
    have h2 := all_rec_close D (κid 𝓢) (bankT Tj θ.w) H' hpos hF' hPc' P S hu₀ R hHr4 hdAr' hdH'
      (fun k => hur (φ k)) (fun k => hurb (φ k)) hurw' M (ε / 2) (by positivity)
    filter_upwards [h1, h2] with k hk1 hk2 τ hτ
    have := abs_sub_le (NativeAllSector.nativeVar (bankData D₀ Tj (θs (φ k))) (n (φ k)) (y (φ k))
      (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ))
      (NativeAllSector.contAllVar D (κid 𝓢) (bankT Tj θ.w) H' F P S u₀ τ)
      (recAllVar D (κid 𝓢) (bankT Tj θ.w) (f (φ k)) (g (φ k)) (Ar (φ k)) (dAr (φ k)) (Hr (φ k))
        (dH (φ k)) (Ψr (φ k)) (χr (φ k)) (ur (φ k)) τ)
    linarith [hk1 τ hτ, hk2 τ hτ]
  · exact grav_rec_close θ.κ θ.Λ (Ke := (H.Ke : Set Mat)) H.hKe hpos (fun k => hfK (φ k)) hf' hg'
  · exact fun M => ym_rec_close (bankT Tj θ.w) H' hF' hPc' (fun k => hfK (φ k)) hf' hAr' hdAr' M
  · exact higgs_rec_close D H' P (fun k => hfK (φ k)) hf' hAr' hHr4 hdH'
  · exact dirac_rec_close D (κid 𝓢) H' S hu₀ R (fun k => hur (φ k)) (fun k => hurb (φ k)) hurw'

end ClosureBank

/-! ### Non-vacuity -/

section NonVacuity

open NativeDensity NativeDiracLimit
open NativeAllSectorGraph (exData2 exData2_hip exCoHyp2 exCoHyp2_pos flat2 frameC frameCo
  gauge_flat2)
open NativeGravityFirstJet (flatRecord)
open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)
open NativeScaling (Mat)

local instance : Nontrivial (CoSpinor ℂ) :=
  ⟨⟨0, ContinuousLinearMap.id ℝ ℂ, fun h => by
    have := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) h
    simp at this⟩⟩

local instance : NeZero (Module.finrank ℝ (CoSpinor ℂ)) := ⟨Module.finrank_pos.ne'⟩

theorem lpTendsto_zero_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞}
    {u : ℕ → 𝕋 → E} (hu : ∀ k z, u k z = 0) : LpTendsto volume p u 0 :=
  (LpTendsto.const (p := p) (ν := (volume : Measure 𝕋)) (MemLp.zero : MemLp (0 : 𝕋 → E) p
    volume)).congr (fun k => Eventually.of_forall fun z => (hu k z).symm)
    (Eventually.of_forall fun _ => rfl)

/-- **Non-vacuity of `native_reconstructed_closure`**: the flat records of the abelian
Einstein–Higgs–Dirac packet, with reconstructions equal to the (constant) raw reconstructions and
zero spinor jets, satisfy all hypotheses; the theorem yields the complete error relative to the
reconstructed fields. -/
example : ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ,
    ∃ P : NativeHiggsVar.HiggsHyp exData2 (fun k => flat2 (φ k + 1)),
    ∃ S : NativeDiracConvergence.SpinHyp (κid ℂ) (fun k => flat2 (φ k + 1)),
    ∃ u₀ : 𝕋 → Dif ℂ (CoSpinor ℂ),
      ∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest ℂ (EuclideanSpace ℝ (Fin 2)) ℂ (CoSpinor ℂ), τ.norm ≤ M →
        |NativeAllSector.nativeVar exData2 (φ k + 1) (flat2 (φ k + 1))
            (testRec (κid ℂ) (φ k + 1) (flat2 (φ k + 1)) τ) -
          recAllVar exData2 (κid ℂ) (ContinuousLinearMap.id ℝ ℂ) (fun _ => asM4 1)
            (fun lam => pc (NativeDiracConv.qM (flat2 (φ k + 1)) lam)) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ => 0) (fun _ => 0) τ| ≤ ε := by
  have hgz : ∀ k μ, gauge (flat2 (k + 1)) μ = fun _ => (0 : ℂ) := fun k μ => rfl
  obtain ⟨φ, hφ, P, S, u₀, -, -, -, -, -, -, htot⟩ := native_reconstructed_closure exData2
    (ContinuousLinearMap.id ℝ ℂ) exData2_hip frameC frameCo exCoHyp2 exCoHyp2_pos
    (by norm_num [exCoHyp2]) (F := fun _ _ _ => 0)
    (fun μ ν => (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
      (fun k => Eventually.of_forall fun z => by
        rw [gauge_flat2]
        simp [pc, NativeScaling.fieldStrength, NativeScaling.gaugePlaquette,
          ShiftedPlaquette.logOneAdd])
      (Eventually.of_forall fun _ => rfl))
    (fun k x μ v => by rw [gauge_flat2]; simp)
    (BH := 0) (fun k => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, higgs, flat2, flatRecord])
    (K₀ := fun _ _ => 0)
    (fun μ => (LpTendsto.const (u := fun _ : 𝕋 => (0 : EuclideanSpace ℝ (Fin 2)))
      (memLp_const _)).congr (fun k => Eventually.of_forall fun z => by
        simp [pc, higgsLink, NativeScaling.higgsLink, higgs, flat2, flatRecord])
      (Eventually.of_forall fun _ => rfl))
    (fun k x μ v => by rw [gauge_flat2]; simp)
    (B := 0) (fun k => by simp [TorusPiecewiseConstantTranslation.gridNorm, psi, flat2, flatRecord])
    (fun k μ => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, spinGraph, psi, flat2, flatRecord])
    (fun k => by simp [TorusPiecewiseConstantTranslation.gridNorm, psiBar, flat2, flatRecord])
    (fun k μ => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, dualGraph, psiBar, flat2, flatRecord])
    (Pc := fun _ _ _ => 0)
    (fun μ ν => (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
      (fun k => Eventually.of_forall fun z => by
        simp [pc, NativeHiggs.DpV, hgz]) (Eventually.of_forall fun _ => rfl))
    (fun _ _ => asM4 1) (fun _ _ => rfl)
    (lpTendsto_zero_of_eq fun k z => by
      change asM4 (1 : Mat) - asM4 (1 : Mat) = 0
      exact sub_self _)
    (fun k lam => pc (NativeDiracConv.qM (flat2 (k + 1)) lam))
    (fun lam => lpTendsto_zero_of_eq fun k z => sub_self _)
    (fun _ _ _ => 0)
    (fun μ => lpTendsto_zero_of_eq fun k z => by simp [pc, hgz])
    (fun _ _ _ _ => 0)
    (fun μ ν => lpTendsto_zero_of_eq fun k z => by simp [pc, NativeHiggs.DpV, hgz])
    (fun _ _ => 0)
    (lpTendsto_zero_of_eq fun k z => by simp [pc, higgs, flat2, flatRecord])
    (fun _ _ _ => 0)
    (fun μ => lpTendsto_zero_of_eq fun k z => by
      simp [pc, NativeHiggs.DpV, higgs, flat2, flatRecord])
    (fun _ _ => 0) (lpTendsto_zero_of_eq fun k z => by simp [pc, psi, flat2, flatRecord])
    (fun _ _ => 0) (lpTendsto_zero_of_eq fun k z => by simp [pc, psiBar, flat2, flatRecord])
    (B4 := 1) ENNReal.one_ne_top (fun k => by simp) (fun k => by simp)
    (fun _ _ => 0) (fun k => MemLp.zero) (Cr := 0) (fun k => by simp)
    (fun G hG => by
      refine tendsto_const_nhds.congr fun k => ?_
      have : ∀ z, pc (difs (flat2 (k + 1)) (psiBar (flat2 (k + 1)))) z =
          (0 : Dif ℂ (CoSpinor ℂ)) := fun z => by
        simp [pc, difs, ShiftedJetAction.fwdDiff, psi, psiBar, flat2, flatRecord]
        exact ⟨rfl, rfl⟩
      simp [this])
  exact ⟨φ, hφ, P, S, u₀, htot⟩

end NonVacuity

end

end RenewalGeometry.NativeReconstructed
