/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeCoulombFourier

/-!
# Critical discrete Coulomb compactness (`thm:native-discrete-Coulomb`)

Einstein–SM action-closure manuscript, Appendix `app:native-critical-closure`, in the unit-torus
rendering of `Continuum/TorusTrigReconstruction.lean` (grid `(ℤ/N)⁴`, mesh `h = 1/N`, side `1`;
the paper's box of side `2π` is its dilation).  Connections take values in a finite-dimensional
complete normed complex algebra `𝔸` with `‖1‖ = 1` (e.g. `M_n(ℂ)` with the operator norm, which
contains the compact gauge algebras); the Lie-algebra norms are read in a real inner product space
`E` through `T : 𝔸 →L[ℝ] E` with `‖X‖ ≤ c ‖T X‖` (`Continuum/NativeCoulombAbsorption.lean`).

* `native_discrete_Coulomb` (**`thm:native-discrete-Coulomb`**): there is `ε* > 0` (explicit,
  depending only on `‖T‖` and `c`) such that if `δ_h T A_h = 0`, `‖T A_{h,μ}‖_{4,h} ≤ ε*` and the
  literal curvatures satisfy `R_h^0 F_h(A_h) → F` strongly in `L²`, then after extraction
  `R_h^0 A_h → A` strongly in `L⁴`, `R_h^0 D⁺_μ A_{h,ν} → G_{μν}` strongly in `L²` with
  `G_{μν} = ∂_μ A_ν` (Fourier side, every frequency), the trigonometric reconstructions of every
  coordinate converge strongly in `H¹`, `F = F_A` (`F_{μν} = ∂_μA_ν - ∂_νA_μ + [A_μ, A_ν]` a.e.)
  and `δA = 0` (`Σ_μ ∂_μ A_μ = 0` a.e.).

The proof follows the manuscript: the absorption inequality with `B = 0` gives the uniform discrete
`H¹` bound; discrete Rellich extracts `R_h^0 A_h → A` in `L²`; the exact Fourier multipliers of the
grid differences and the `L¹` convergence of the nonlinear plaquette term identify
`F = dA + A ∧ A` and `δA = 0` on the Fourier side; the comparison fields are the Fourier
truncations `P_R A` (divergence free, `P_R A → A` in `H¹` and, by the critical embedding, in `L⁴`)
sampled on the grids; the absorption inequality for `A_h - 𝒮_h P_R A` and fixed-smooth-field
consistency give `limsup_h ‖D⁺A_h - ∂P_R A‖_{L²} ≤ δ_R → 0`, so the forward differences are Cauchy
in `L²`; finally `lem:native-reconstruction-identification` gives the `L⁴` and trigonometric `H¹`
statements and `prop:native-YM-identification` (first assertion) gives `F = F_A`.
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.NativeCoulomb

open TorusTrigReconstruction NativeCriticalGrid TorusPiecewiseConstantTranslation LogBCH
  NativeYMIdentification PlaquetteLogDerivative NativeYMVariation NativeGridLp NativeHiggs
  TorusSobolev

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

local instance fact_one_le_four_k : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_two_k : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance holder442_k : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two
local instance holder221_k : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

/-! ### Generic `L^p` facts -/

section LpFacts

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
variable {F : Type*} [NormedAddCommGroup F]

/-- Norms converge along strongly convergent sequences. -/
theorem _root_.RenewalGeometry.LpTendsto.tendsto_toReal_eLpNorm {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : ℕ → X → F} {u' : X → F}
    (hu : LpTendsto ν p u u') :
    Tendsto (fun k => (eLpNorm (u k) p ν).toReal) atTop (𝓝 (eLpNorm u' p ν).toReal) := by
  have hL : Tendsto (fun k => (hu.memLp k).toLp (u k)) atTop (𝓝 (hu.memLp_lim.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hu.tendsto
  have := hL.norm
  simpa only [Lp.norm_toLp] using this

/-- Strong limits are unique a.e. -/
theorem _root_.RenewalGeometry.LpTendsto.ae_eq_of_lpTendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : ℕ → X → F} {a b : X → F}
    (ha : LpTendsto ν p u a) (hb : LpTendsto ν p u b) : a =ᵐ[ν] b := by
  have hL1 : Tendsto (fun k => (ha.memLp k).toLp (u k)) atTop (𝓝 (ha.memLp_lim.toLp a)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 ha.tendsto
  have hL2 : Tendsto (fun k => (hb.memLp k).toLp (u k)) atTop (𝓝 (hb.memLp_lim.toLp b)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hb.tendsto
  have huniq := tendsto_nhds_unique hL1 hL2
  have := (MemLp.toLp_eq_toLp_iff ha.memLp_lim hb.memLp_lim).1 huniq
  exact this

end LpFacts

/-! ### Backward shifts of raw reconstructions -/

section BackShift

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem tendsto_coordPt_neg (hn : Tendsto n atTop atTop) (μ : Fin 4) :
    Tendsto (fun k => KolmogorovRieszTorus.coordPt μ (((-1 : ℤ) : ℝ) / (n k : ℝ))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun k => (((-1 : ℤ) : ℝ) / (n k : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hn)
  have hc : Continuous fun s : ℝ => (Pi.single μ (s : UnitAddCircle) : UnitAddTorus (Fin 4)) :=
    continuous_pi fun i => by
      by_cases h : i = μ
      · subst h; simpa using QuotientAddGroup.continuous_mk
      · simp only [Pi.single_eq_of_ne h]; exact continuous_const
  have := (hc.tendsto 0).comp h0
  have h1 : (Pi.single μ ((0 : ℝ) : UnitAddCircle) : UnitAddTorus (Fin 4)) = 0 := by simp
  rw [h1] at this
  exact this

/-- One-step backward shifts of an `L^p`-convergent sequence of raw reconstructions have the same
limit. -/
theorem _root_.RenewalGeometry.LpTendsto.shift_neg (hn : Tendsto n atTop atTop) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {v : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → E'}
    {g : UnitAddTorus (Fin 4) → E'} (hv : LpTendsto volume p (fun k => pc (v k)) g) (μ : Fin 4) :
    LpTendsto volume p (fun k => pc (fun x => v k (x - Pi.single μ 1))) g := by
  refine ⟨fun k => memLp_pc_gen _ p, hv.memLp_lim, ?_⟩
  have htr := (transl_tendsto hp hv.memLp_lim).comp (tendsto_coordPt_neg hn μ)
  have hup := hv.tendsto.add htr
  rw [zero_add] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => zero_le)
    fun k => ?_
  set z := KolmogorovRieszTorus.coordPt μ (((-1 : ℤ) : ℝ) / (n k : ℝ))
  have hpc : ∀ y, pc (fun x => v k (x - Pi.single μ 1)) y = pc (v k) (y + z) := by
    intro y
    rw [pc_add_coordPt_int (v k) y μ (-1)]
    simp [pc, TorusPiecewiseConstantTranslation.shift, sub_eq_add_neg, Pi.single_neg]
  have hsplit : pc (fun x => v k (x - Pi.single μ 1)) - g = (fun y => (pc (v k) - g) (y + z)) +
      fun y => g (y + z) - g y := by
    funext y; simp only [Pi.sub_apply, Pi.add_apply, hpc]; abel
  rw [hsplit]
  have hm := (hv.memLp k).1.sub hv.memLp_lim.1
  refine (eLpNorm_add_le (hm.comp_measurePreserving (measurePreserving_add_right volume z))
    ((hv.memLp_lim.1.comp_measurePreserving (measurePreserving_add_right volume z)).sub
      hv.memLp_lim.1) Fact.out).trans (le_of_eq ?_)
  congr 1
  exact eLpNorm_comp_measurePreserving hm (measurePreserving_add_right volume z)

end BackShift

/-! ### Coordinates in a finite-dimensional complex algebra -/

section Coordinates

variable (𝔸 : Type*) [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] [FiniteDimensional ℂ 𝔸]

/-- A fixed complex basis of `𝔸` (the fixed frame of the compactness argument). -/
def bas : Module.Basis (Fin (Module.finrank ℂ 𝔸)) ℂ 𝔸 := Module.finBasis ℂ 𝔸

/-- The coordinate functionals of `bas`. -/
def coordL (i : Fin (Module.finrank ℂ 𝔸)) : 𝔸 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((bas 𝔸).coord i)

variable {𝔸}

theorem sum_coordL (X : 𝔸) : ∑ i, coordL 𝔸 i X • bas 𝔸 i = X := by
  simp only [coordL, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  exact (bas 𝔸).sum_repr X

theorem coordL_sum_smul (c : Fin (Module.finrank ℂ 𝔸) → ℂ) (i : Fin (Module.finrank ℂ 𝔸)) :
    coordL 𝔸 i (∑ j, c j • bas 𝔸 j) = c i := by
  simp only [coordL, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, map_sum,
    map_smul, Module.Basis.repr_self, Finset.sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem norm_le_sum_coordL (X : 𝔸) : ‖X‖ ≤ ∑ i, ‖bas 𝔸 i‖ * ‖coordL 𝔸 i X‖ := by
  conv_lhs => rw [← sum_coordL X]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, mul_comm]

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- Strong convergence of all coordinates gives strong convergence of the vectors. -/
theorem lpTendsto_of_coordL {p : ℝ≥0∞} [Fact (1 ≤ p)] {g : ℕ → X → 𝔸} {g₀ : X → 𝔸}
    (hg : ∀ k, MemLp (g k) p ν) (hg₀ : MemLp g₀ p ν)
    (hc : ∀ i, LpTendsto ν p (fun k y => coordL 𝔸 i (g k y)) (fun y => coordL 𝔸 i (g₀ y))) :
    LpTendsto ν p g g₀ := by
  refine ⟨hg, hg₀, ?_⟩
  have hsum : Tendsto (fun k => ∑ i, (‖bas 𝔸 i‖₊ : ℝ≥0∞) *
      eLpNorm ((fun y => coordL 𝔸 i (g k y)) - fun y => coordL 𝔸 i (g₀ y)) p ν) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℂ 𝔸))) fun i _ =>
      ENNReal.Tendsto.const_mul (hc i).tendsto (Or.inr ENNReal.coe_ne_top) (a := (‖bas 𝔸 i‖₊ : ℝ≥0∞))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun k => zero_le)
    fun k => ?_
  have hm : ∀ i, AEStronglyMeasurable (fun y => ‖bas 𝔸 i‖ *
      ‖((fun y => coordL 𝔸 i (g k y)) - fun y => coordL 𝔸 i (g₀ y)) y‖) ν := fun i =>
    (((hc i).memLp k).1.sub (hc i).memLp_lim.1).norm.const_mul _
  calc eLpNorm (g k - g₀) p ν ≤ eLpNorm (∑ i, fun y => ‖bas 𝔸 i‖ *
        ‖((fun y => coordL 𝔸 i (g k y)) - fun y => coordL 𝔸 i (g₀ y)) y‖) p ν := by
        refine eLpNorm_mono fun y => ?_
        rw [Finset.sum_apply, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
        refine (norm_le_sum_coordL _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.sub_apply, map_sub]
    _ ≤ ∑ i, eLpNorm (fun y => ‖bas 𝔸 i‖ *
        ‖((fun y => coordL 𝔸 i (g k y)) - fun y => coordL 𝔸 i (g₀ y)) y‖) p ν :=
        eLpNorm_sum_le (fun i _ => hm i) Fact.out
    _ = ∑ i, (‖bas 𝔸 i‖₊ : ℝ≥0∞) *
        eLpNorm ((fun y => coordL 𝔸 i (g k y)) - fun y => coordL 𝔸 i (g₀ y)) p ν := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have e : (fun y => ‖bas 𝔸 i‖ *
            ‖((fun y => coordL 𝔸 i (g k y)) - fun y => coordL 𝔸 i (g₀ y)) y‖) =
            ‖bas 𝔸 i‖ • fun y => ‖((fun y => coordL 𝔸 i (g k y)) - fun y => coordL 𝔸 i (g₀ y)) y‖ := by
          funext y; simp [smul_eq_mul]
        rw [e, eLpNorm_const_smul, eLpNorm_norm, enorm_norm]
        rfl

end Coordinates

/-! ### The a priori estimate and the small-data chart -/

section Apriori

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : ℕ} [NeZero N]

theorem curvLog_zero' (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) :
    curvLog N (0 : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) x μ ν = 0 := by
  simp [curvLog, slots, expProd, logOnePlus, logTerm]

theorem slotFn_zero (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) :
    slotFn (0 : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) μ ν x = 0 := by
  simp [slotFn, slots, normSum]

theorem g4_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    g4 (fun _ : LatticeTorusPlancherel.Grid 4 N => (0 : F)) = 0 := by
  unfold g4 GridSobolev.gridL4Norm
  simp

/-- The explicit smallness threshold `ε* = 1/(69120 (‖T‖ + 1)(c + 1)²)`. -/
def epsStar (T : 𝔸 →L[ℝ] E) (c : ℝ) : ℝ := 1 / (69120 * (‖T‖ + 1) * (c + 1) ^ 2)

theorem epsStar_pos (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c) : 0 < epsStar T c := by
  unfold epsStar; positivity

theorem epsStar_chart (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c) : 128 * c * epsStar T c ≤ 1 := by
  unfold epsStar
  rw [mul_one_div, div_le_one (by positivity)]
  have h1 : 1 ≤ ‖T‖ + 1 := by linarith [norm_nonneg T]
  nlinarith [sq_nonneg c, mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (c + 1) ^ 2)]

theorem epsStar_absorb (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c) :
    23040 * ‖T‖ * c * (3 * (c * epsStar T c)) ≤ 1 := by
  unfold epsStar
  have hp : 0 < 69120 * (‖T‖ + 1) * (c + 1) ^ 2 := by positivity
  rw [show 23040 * ‖T‖ * c * (3 * (c * (1 / (69120 * (‖T‖ + 1) * (c + 1) ^ 2)))) =
      (69120 * ‖T‖ * c ^ 2) / (69120 * (‖T‖ + 1) * (c + 1) ^ 2) by field_simp; ring]
  rw [div_le_one hp]
  have h1 : ‖T‖ ≤ ‖T‖ + 1 := by linarith
  have h2 : c ^ 2 ≤ (c + 1) ^ 2 := by nlinarith
  have := mul_le_mul h1 h2 (sq_nonneg c) (by linarith [norm_nonneg T])
  nlinarith [norm_nonneg T]

/-- Small `L⁴_h` norms put the scaled slots in the chart `h |W| ≤ 1/32`. -/
theorem chart_of_small (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖)
    {ε : ℝ} (hε : 128 * c * ε ≤ 1) (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (hs : ∀ μ, g4 (fun x => T (A x μ)) ≤ ε) (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) :
    (N : ℝ)⁻¹ * slotFn A μ ν x ≤ 1 / 32 := by
  have hpt : ∀ y κ, (N : ℝ)⁻¹ * ‖A y κ‖ ≤ c * ε := by
    intro y κ
    calc (N : ℝ)⁻¹ * ‖A y κ‖ ≤ (N : ℝ)⁻¹ * (c * ‖T (A y κ)‖) :=
          mul_le_mul_of_nonneg_left (hc _) (by positivity)
      _ = c * ((N : ℝ)⁻¹ * ‖(fun x => T (A x κ)) y‖) := by ring
      _ ≤ c * ε := mul_le_mul_of_nonneg_left ((le_g4 _ y).trans (hs κ)) hc0
  rw [slotFn, normSum_slots]
  have h1 := hpt x μ
  have h2 := hpt (x + Pi.single μ 1) ν
  have h3 := hpt (x + Pi.single ν 1) μ
  have h4 := hpt x ν
  nlinarith

/-- **The a priori estimate** (first display of the proof of `thm:native-discrete-Coulomb`):
`Σ_{μ,ν} ‖D⁺_μ T A_ν‖_{2,h} ≤ 8 ‖T‖ Σ_{μ<ν} ‖F_h(A)_{μν}‖_{2,h} + 3 Σ_ν ‖T A_ν‖_{2,h}` in Coulomb
gauge under the small-data condition. -/
theorem coulomb_apriori' (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖)
    (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) (hδ : codiffT T A = 0)
    (hs : ∀ μ, g4 (fun x => T (A x μ)) ≤ epsStar T c) :
    ∑ μ, ∑ ν, gridNorm (DpV μ (fun x => T (A x ν))) ≤
      8 * ‖T‖ * ∑ p ∈ pairs4, gridNorm (fun x => curvLog N A x p.1 p.2) +
        3 * ∑ ν, gridNorm (fun x => T (A x ν)) := by
  have hch := chart_of_small T hc0 hc (epsStar_chart T hc0) A hs
  have hA4 : ∀ μ, g4 (fun x => A x μ) ≤ 3 * (c * epsStar T c) := by
    intro μ
    refine (g4_le_mul hc0 fun x => hc (A x μ)).trans ?_
    have := mul_le_mul_of_nonneg_left (hs μ) hc0
    have h0 : 0 ≤ c * epsStar T c := mul_nonneg hc0 (epsStar_pos T hc0).le
    linarith
  have h := coulomb_absorption T hc0 hc A 0 hch (fun x μ ν => by rw [slotFn_zero]; norm_num) hδ
    hA4 (fun μ => by
      simp only [Pi.zero_apply]; rw [g4_zero]
      exact mul_nonneg zero_le_three (mul_nonneg hc0 (epsStar_pos T hc0).le)) (epsStar_absorb T hc0)
  simp only [sub_zero, codiffT_zero] at h
  have e1 : ∀ p : Fin 4 × Fin 4, (fun x => curvLog N A x p.1 p.2 -
      curvLog N (0 : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) x p.1 p.2) =
      fun x => curvLog N A x p.1 p.2 := fun p => by funext x; rw [curvLog_zero', sub_zero]
  simp only [e1] at h
  have e2 : gridNorm (0 : LatticeTorusPlancherel.Grid 4 N → E) = 0 := gridNorm_zero
  rw [e2, add_zero] at h
  linarith

end Apriori

/-! ### Extraction, the nonlinear term in `L¹`, and the Fourier-side identification -/

section Extraction

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
  [FiniteDimensional ℂ 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem gridNorm_le_mul_gridNorm {N : ℕ} [NeZero N] {F G : Type*} [NormedAddCommGroup F]
    [NormedAddCommGroup G] {u : LatticeTorusPlancherel.Grid 4 N → F}
    {v : LatticeTorusPlancherel.Grid 4 N → G} {K : ℝ} (hK : 0 ≤ K) (h : ∀ x, ‖u x‖ ≤ K * ‖v x‖) :
    gridNorm u ≤ K * gridNorm v := by
  refine (gridNorm_mono (v := fun x => K * ‖v x‖) fun x => ?_).trans (le_of_eq ?_)
  · rw [Real.norm_of_nonneg (mul_nonneg hK (norm_nonneg _))]; exact h x
  · rw [gridNorm_const_mul (d := Fin 4) (N := N) (fun x => ‖v x‖) hK]
    congr 1; unfold gridNorm; simp only [norm_norm]

/-- Coordinates of a grid connection, as complex grid functions. -/
def coordGridA {N : ℕ} (i : Fin (Module.finrank ℂ 𝔸)) (ν : Fin 4)
    (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) : LatticeTorusPlancherel.Grid 4 N → ℂ :=
  fun x => coordL 𝔸 i (A x ν)

theorem Dp_coordGridA {N : ℕ} [NeZero N] (i : Fin (Module.finrank ℂ 𝔸)) (μ ν : Fin 4)
    (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) :
    Dp μ (coordGridA i ν A) = fun x => coordL 𝔸 i (DpV μ (fun y => A y ν) x) := by
  funext x
  simp only [Dp_apply, coordGridA, DpV]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_sub, smul_eq_mul]
  norm_cast

/-- **Discrete Rellich for the connections** (componentwise in the fixed complex frame). -/
theorem exists_subseq_connection (hn : Tendsto n atTop atTop) (T : 𝔸 →L[ℝ] E) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖) (A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸)
    {B : ℝ} (hB : ∀ k ν, gridNorm (fun x => T (A k x ν)) ≤ B)
    (hD : ∀ k μ ν, gridNorm (DpV μ (fun x => T (A k x ν))) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸)
      (fc : Fin (Module.finrank ℂ 𝔸) → Fin 4 → L²(UnitAddTorus (Fin 4))),
      (∀ ν, LpTendsto volume 2 (fun k => pc (fun x => A (φ k) x ν)) (A₀ ν)) ∧
      (∀ i ν y, coordL 𝔸 i (A₀ ν y) = fc i ν y) ∧ (∀ i ν, MemH 1 (fc i ν)) ∧
      (∀ i ν, Tendsto (fun k => ‖pcLp (coordGridA i ν (A (φ k))) - fc i ν‖) atTop (𝓝 0)) := by
  set r := Module.finrank ℂ 𝔸
  set e : Fin (r * 4) ≃ Fin r × Fin 4 := finProdFinEquiv.symm
  set K : ℝ := ∑ i, ‖coordL 𝔸 i‖
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hKi : ∀ i, ‖coordL 𝔸 i‖ ≤ K := fun i => Finset.single_le_sum (f := fun i => ‖coordL 𝔸 i‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hB0 : 0 ≤ B := (gridNorm_nonneg _).trans (hB 0 0)
  set u : Fin (r * 4) → ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → ℂ :=
    fun j k => coordGridA (e j).1 (e j).2 (A k)
  have hpt : ∀ i (X : 𝔸), ‖coordL 𝔸 i X‖ ≤ (K * c) * ‖T X‖ := by
    intro i X
    calc ‖coordL 𝔸 i X‖ ≤ ‖coordL 𝔸 i‖ * ‖X‖ := (coordL 𝔸 i).le_opNorm X
      _ ≤ K * (c * ‖T X‖) := mul_le_mul (hKi i) (hc X) (norm_nonneg _) hK0
      _ = (K * c) * ‖T X‖ := by ring
  have hu : ∀ j k, gridNorm (u j k) ≤ K * c * B := by
    intro j k
    refine (gridNorm_le_mul_gridNorm (mul_nonneg hK0 hc0) (fun x => hpt _ _)).trans ?_
    exact mul_le_mul_of_nonneg_left (hB k _) (mul_nonneg hK0 hc0)
  have hDu : ∀ j k μ, gridNorm (Dp μ (u j k)) ≤ K * c * B := by
    intro j k μ
    simp only [u]
    rw [Dp_coordGridA]
    refine (gridNorm_le_mul_gridNorm (mul_nonneg hK0 hc0) (fun x => hpt _ _)).trans ?_
    have e1 : (fun x => T (DpV μ (fun y => A k y (e j).2) x)) = DpV μ (fun x => T (A k x (e j).2)) := by
      funext x; simp [DpV, map_smul, map_sub]
    rw [e1]
    exact mul_le_mul_of_nonneg_left (hD k μ _) (mul_nonneg hK0 hc0)
  obtain ⟨φ, hφ, f, hf⟩ := exists_subseq_tendsto_pcLp_family (r * 4) hn u hu hDu
  have hnφ : Tendsto (fun k => n (φ k)) atTop atTop := hn.comp hφ.tendsto_atTop
  set fc : Fin r → Fin 4 → L²(UnitAddTorus (Fin 4)) := fun i ν => f (e.symm (i, ν))
  have hfc : ∀ i ν, Tendsto (fun k => ‖pcLp (coordGridA i ν (A (φ k))) - fc i ν‖) atTop (𝓝 0) := by
    intro i ν
    have := hf (e.symm (i, ν))
    simpa [u, fc] using this
  set A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸 := fun ν y => ∑ i, (fc i ν y) • bas 𝔸 i
  have hcoord : ∀ i ν y, coordL 𝔸 i (A₀ ν y) = fc i ν y := fun i ν y => coordL_sum_smul _ i
  have hmem : ∀ ν, MemLp (A₀ ν) 2 volume := by
    intro ν
    have : A₀ ν = ∑ i, fun y => (fc i ν y) • bas 𝔸 i := by
      funext y; simp [A₀, Finset.sum_apply]
    rw [this]
    exact memLp_finset_sum' _ fun i _ =>
      ((ContinuousLinearMap.id ℂ ℂ).smulRight (bas 𝔸 i)).comp_memLp' (Lp.memLp (fc i ν))
  refine ⟨φ, hφ, A₀, fc, fun ν => ?_, hcoord, fun i ν => ?_, hfc⟩
  · refine lpTendsto_of_coordL (fun k => memLp_pc_gen _ 2) (hmem ν) fun i => ?_
    refine (lpTendsto_of_norm_pcLp (n := fun k => n (φ k)) (hfc i ν)).congr
      (fun k => Eventually.of_forall fun y => rfl) (Eventually.of_forall fun y => (hcoord i ν y).symm)
  · have hb : ∀ k, gridNorm (coordGridA i ν (A (φ k))) ≤ K * c * B := fun k => hu (e.symm (i, ν)) (φ k)
      |>.trans_eq' (by simp [u])
    have hdb : ∀ k μ, gridNorm (Dp μ (coordGridA i ν (A (φ k)))) ≤ K * c * B := fun k μ =>
      (hDu (e.symm (i, ν)) (φ k) μ).trans_eq' (by simp [u])
    exact (weak_limit_of_bounded hnφ hb hdb (hfc i ν)).1

end Extraction

/-! ### The nonlinear term in `L¹` and the Fourier-side identification -/

section Identification

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem eLpNorm_pc_one {N : ℕ} [NeZero N] {F : Type*} [NormedAddCommGroup F]
    (u : LatticeTorusPlancherel.Grid 4 N → F) :
    eLpNorm (pc u) 1 (volume : Measure (UnitAddTorus (Fin 4))) =
      ENNReal.ofReal ((N : ℝ)⁻¹ ^ 4 * ∑ x, ‖u x‖) := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have h := lintegral_comp_index (d := Fin 4) (N := N) fun g => ‖u g‖ₑ
  change ∫⁻ y, ‖u (TorusPiecewiseConstantTranslation.index N y)‖ₑ = _
  rw [h, Fintype.card_fin]
  have hS : ∑ g, ‖u g‖ₑ = ENNReal.ofReal (∑ g, ‖u g‖) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun g _ => norm_nonneg _)]
    exact Finset.sum_congr rfl fun g _ => (ofReal_norm (u g)).symm
  rw [hS, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity), one_div]

theorem g4_pow_four {N : ℕ} [NeZero N] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : LatticeTorusPlancherel.Grid 4 N → F) : g4 u ^ 4 = (N : ℝ)⁻¹ ^ 4 * ∑ x, ‖u x‖ ^ 4 := by
  unfold g4 GridSobolev.gridL4Norm
  rw [Fintype.card_fin, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem card_grid4 (N : ℕ) [NeZero N] :
    (Fintype.card (LatticeTorusPlancherel.Grid 4 N) : ℝ) = (N : ℝ) ^ 4 := by
  simp [LatticeTorusPlancherel.Grid, Fintype.card_fun, ZMod.card]

/-- The commutator term of the four slots converges to `[A_μ, A_ν]` strongly in `L¹` when the
connections converge strongly in `L²` only. -/
theorem tendsto_commTerm_L1 (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => A k x μ)) (A₀ μ)) (μ ν : Fin 4) :
    LpTendsto volume 1 (fun k => pc (fun x => commTerm (slots (A k) x μ ν)))
      (fun y => A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y) := by
  set M := ContinuousLinearMap.mul ℝ 𝔸
  have ha := hA μ
  have hb := (hA ν).shift hn (by norm_num) μ
  have hc := ((hA μ).shift hn (by norm_num) ν).neg
  have he := (hA ν).neg
  have hbce := (hb.add hc).add he
  have hce := hc.add he
  have h1 := (LpTendsto.bilin (p := 2) (q := 2) (r := 1) M ha hbce).sub
    (LpTendsto.bilin (p := 2) (q := 2) (r := 1) M hbce ha)
  have h2 := (LpTendsto.bilin (p := 2) (q := 2) (r := 1) M hb hce).sub
    (LpTendsto.bilin (p := 2) (q := 2) (r := 1) M hce hb)
  have h3 := (LpTendsto.bilin (p := 2) (q := 2) (r := 1) M hc he).sub
    (LpTendsto.bilin (p := 2) (q := 2) (r := 1) M he hc)
  have hsum := (h1.const_smul (1 / 2)).add ((h2.const_smul (1 / 2)).add (h3.const_smul (1 / 2)))
  refine hsum.congr (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, M,
      ContinuousLinearMap.mul_apply']
    rw [show pc (fun x => commTerm (slots (A k) x μ ν)) y =
        commTerm (slots (A k) (TorusPiecewiseConstantTranslation.index (n k) y) μ ν) from rfl,
      slots, commTerm_four]
    rfl
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, M,
      ContinuousLinearMap.mul_apply']
    simp only [mul_add, add_mul, mul_neg, neg_mul, neg_neg, smul_sub, smul_add, smul_neg]
    module

theorem cube_le_four_add_one (s : ℝ) : s ^ 3 ≤ s ^ 4 + 1 := by
  nlinarith [sq_nonneg (s ^ 2 - s / 2), sq_nonneg (s - 1), sq_nonneg s, sq_nonneg (s ^ 2 - 1)]

/-- **`R_h^0 𝒩_h(A_h) → A ∧ A` strongly in `L¹`** from strong `L²` convergence and uniform `L⁴_h`
bounds on the chart (the step "its slot products converge strongly in `L¹`" of the proof). -/
theorem tendsto_nonlin_L1 (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => A k x μ)) (A₀ μ))
    (hch : ∀ k x μ ν, ((n k : ℝ))⁻¹ * slotFn (A k) μ ν x ≤ 1 / 32) {a : ℝ}
    (ha : ∀ k μ, g4 (fun x => A k x μ) ≤ a) (μ ν : Fin 4) :
    LpTendsto volume 1 (fun k => pc (fun x => nonlin (n k) (A k) x μ ν))
      (fun y => A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y) := by
  set rem : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → 𝔸 := fun k x =>
    nonlin (n k) (A k) x μ ν - commTerm (slots (A k) x μ ν)
  have ha0 : 0 ≤ a := (g4_nonneg _).trans (ha 0 0)
  -- pointwise bound on the remainder
  have hpt : ∀ k x, ‖rem k x‖ ≤ 6 * ((n k : ℝ))⁻¹ * (slotFn (A k) μ ν x ^ 4 + 1) := by
    intro k x
    have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
    set L := (slots (A k) x μ ν).map fun v => ((n k : ℝ))⁻¹ • v
    have hL : normSum L = ((n k : ℝ))⁻¹ * slotFn (A k) μ ν x := by
      rw [normSum_map_smul, abs_of_pos (inv_pos.2 hN)]; rfl
    have hb := norm_log_expProd_sub_bch_le L (by rw [hL]; linarith [hch k x μ ν])
    have e : rem k x = ((n k : ℝ) ^ 2) • bchRem L := by
      simp only [rem, nonlin_eq]; abel
    rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
    have hs0 : 0 ≤ slotFn (A k) μ ν x := slotFn_nonneg _ _ _ _
    calc ((n k : ℝ)) ^ 2 * ‖bchRem L‖ ≤ ((n k : ℝ)) ^ 2 * (6 * normSum L ^ 3) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 6 * ((n k : ℝ))⁻¹ * slotFn (A k) μ ν x ^ 3 := by rw [hL]; field_simp
      _ ≤ 6 * ((n k : ℝ))⁻¹ * (slotFn (A k) μ ν x ^ 4 + 1) :=
          mul_le_mul_of_nonneg_left (cube_le_four_add_one _) (by positivity)
  -- the `L¹` bound on the remainder
  have hrem : ∀ k, eLpNorm (pc (rem k)) 1 volume ≤
      ENNReal.ofReal (6 * ((n k : ℝ))⁻¹ * ((4 * a) ^ 4 + 1)) := by
    intro k
    have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
    rw [eLpNorm_pc_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs4 : g4 (slotFn (A k) μ ν) ≤ 4 * a := by
      have := g4_slotFn_le (A k) μ ν
      linarith [ha k μ, ha k ν]
    have hg4 := g4_pow_four (slotFn (A k) μ ν)
    have hg4' : g4 (slotFn (A k) μ ν) ^ 4 ≤ (4 * a) ^ 4 :=
      pow_le_pow_left₀ (g4_nonneg _) hs4 4
    calc ((n k : ℝ))⁻¹ ^ 4 * ∑ x, ‖rem k x‖
        ≤ ((n k : ℝ))⁻¹ ^ 4 * ∑ x, 6 * ((n k : ℝ))⁻¹ * (slotFn (A k) μ ν x ^ 4 + 1) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpt k x) (by positivity)
      _ = 6 * ((n k : ℝ))⁻¹ * (((n k : ℝ))⁻¹ ^ 4 * ∑ x, ‖slotFn (A k) μ ν x‖ ^ 4 +
            ((n k : ℝ))⁻¹ ^ 4 * (Fintype.card (LatticeTorusPlancherel.Grid 4 (n k)) : ℝ)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
            Finset.card_univ]
          simp only [Real.norm_of_nonneg (slotFn_nonneg _ _ _ _)]
          ring
      _ = 6 * ((n k : ℝ))⁻¹ * (g4 (slotFn (A k) μ ν) ^ 4 + 1) := by
          rw [hg4, card_grid4]
          field_simp
      _ ≤ 6 * ((n k : ℝ))⁻¹ * ((4 * a) ^ 4 + 1) := by gcongr
  have hremT : LpTendsto volume 1 (fun k => pc (rem k)) 0 := by
    refine ⟨fun k => memLp_pc_gen _ 1, MemLp.zero, ?_⟩
    have hup : Tendsto (fun k => ENNReal.ofReal (6 * ((n k : ℝ))⁻¹ * ((4 * a) ^ 4 + 1))) atTop
        (𝓝 0) := by
      have h0 := (tendsto_inv_n hn).const_mul 6 |>.mul_const ((4 * a) ^ 4 + 1)
      simpa using ENNReal.tendsto_ofReal h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => zero_le)
      fun k => ?_
    simpa using hrem k
  refine ((tendsto_commTerm_L1 hn hA μ ν).add hremT).congr
    (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · simp only [Pi.add_apply, pc, rem]; abel
  · simp

theorem sum_DmV_eq_zero (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖) {N : ℕ} [NeZero N]
    (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) (hδ : codiffT T A = 0)
    (x : LatticeTorusPlancherel.Grid 4 N) : ∑ μ, DmV μ (fun y => A y μ) x = 0 := by
  have h := congrFun hδ x
  have e : codiffT T A x = -T (∑ μ, DmV μ (fun y => A y μ) x) := by
    simp [codiffT, periodicHodgeCodiff, periodicHodgeBwd, DmV, GridSobolev.gridStep, map_sum,
      map_smul, map_sub]
  rw [e, Pi.zero_apply, neg_eq_zero] at h
  have := hc (∑ μ, DmV μ (fun y => A y μ) x)
  rw [h, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

theorem mFourierCoeff_finset_sum' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {ι : Type*} (s : Finset ι) (f : ι → UnitAddTorus (Fin 4) → F)
    (hf : ∀ i ∈ s, Integrable (f i) volume) (m : Fin 4 → ℤ) :
    mFourierCoeff (fun y => ∑ i ∈ s, f i y) m = ∑ i ∈ s, mFourierCoeff (f i) m := by
  simp only [mFourierCoeff, Finset.smul_sum]
  exact integral_finset_sum s fun i hi => (hf i hi).bdd_smul 1
    (mFourier (-m)).continuous.aestronglyMeasurable
    (Eventually.of_forall fun t => by rw [TorusSobolev.norm_mFourier_apply])

theorem mFourierCoeff_add' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f g : UnitAddTorus (Fin 4) → F} (hf : Integrable f volume) (hg : Integrable g volume)
    (m : Fin 4 → ℤ) : mFourierCoeff (f + g) m = mFourierCoeff f m + mFourierCoeff g m := by
  have hint : ∀ {u : UnitAddTorus (Fin 4) → F}, Integrable u volume →
      Integrable (fun t => mFourier (-m) t • u t) volume := fun hu =>
    hu.bdd_smul 1 (mFourier (-m)).continuous.aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [TorusSobolev.norm_mFourier_apply])
  simp only [mFourierCoeff, Pi.add_apply, smul_add]
  exact integral_add (hint hf) (hint hg)

/-- **`δA = 0` on the Fourier side**: `Σ_μ 2πi m_μ Â_μ(m) = 0` for every frequency. -/
theorem fourier_div_zero (hn : Tendsto n atTop atTop) (T : 𝔸 →L[ℝ] E) {c : ℝ}
    (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖) {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => A k x μ)) (A₀ μ))
    (hδ : ∀ k, codiffT T (A k) = 0) (m : Fin 4 → ℤ) :
    ∑ μ, (2 * π * Complex.I * m μ : ℂ) • mFourierCoeff (A₀ μ) m = 0 := by
  have hk : ∀ k, ∑ μ, symB (n k) μ m • mFourierCoeff (pc (fun x => A k x μ)) m = 0 := by
    intro k
    have h0 : (fun y => ∑ μ, pc (DmV μ (fun x => A k x μ)) y) = fun _ => 0 := by
      funext y
      simp only [pc]
      exact sum_DmV_eq_zero T hc (A k) (hδ k) _
    have := mFourierCoeff_finset_sum' Finset.univ (fun μ => pc (DmV μ (fun x => A k x μ)))
      (fun μ _ => integrable_pc _) m
    rw [h0] at this
    simp only [mFourierCoeff_pc_DmV] at this
    rw [← this]
    simp [mFourierCoeff]
  have hlim : Tendsto (fun k => ∑ μ, symB (n k) μ m • mFourierCoeff (pc (fun x => A k x μ)) m)
      atTop (𝓝 (∑ μ, (2 * π * Complex.I * m μ : ℂ) • mFourierCoeff (A₀ μ) m)) :=
    tendsto_finsetSum _ fun μ _ => (tendsto_symB hn μ m).smul
      (tendsto_mFourierCoeff_of_lpTendsto_one ((hA μ).mono (by norm_num) (by norm_num)) m)
  simp only [hk] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-- **`F = dA + A ∧ A` on the Fourier side** (before any strong convergence of the differences). -/
theorem fourier_curv (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => A k x μ)) (A₀ μ))
    {F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hF : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x => curvLog (n k) (A k) x μ ν)) (F μ ν))
    (hch : ∀ k x μ ν, ((n k : ℝ))⁻¹ * slotFn (A k) μ ν x ≤ 1 / 32) {a : ℝ}
    (ha : ∀ k μ, g4 (fun x => A k x μ) ≤ a) (μ ν : Fin 4) (m : Fin 4 → ℤ) :
    mFourierCoeff (F μ ν) m - mFourierCoeff (fun y => A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y) m =
      (2 * π * Complex.I * m μ : ℂ) • mFourierCoeff (A₀ ν) m -
        (2 * π * Complex.I * m ν : ℂ) • mFourierCoeff (A₀ μ) m := by
  have hN := tendsto_nonlin_L1 hn hA hch ha μ ν
  have hk : ∀ k, mFourierCoeff (pc (fun x => curvLog (n k) (A k) x μ ν)) m =
      (sym (n k) μ m • mFourierCoeff (pc (fun x => A k x ν)) m -
        sym (n k) ν m • mFourierCoeff (pc (fun x => A k x μ)) m) +
        mFourierCoeff (pc (fun x => nonlin (n k) (A k) x μ ν)) m := by
    intro k
    have e : pc (fun x => curvLog (n k) (A k) x μ ν) =
        (pc (DpV μ (fun x => A k x ν)) - pc (DpV ν (fun x => A k x μ))) +
          pc (fun x => nonlin (n k) (A k) x μ ν) := by
      funext y; simp only [pc, Pi.add_apply, Pi.sub_apply, nonlin, linCurl, DpA, DpV]
      abel
    rw [e, mFourierCoeff_add' ((integrable_pc _).sub (integrable_pc _)) (integrable_pc _),
      mFourierCoeff_sub' (integrable_pc _) (integrable_pc _), mFourierCoeff_pc_DpV,
      mFourierCoeff_pc_DpV]
  have hL : Tendsto (fun k => mFourierCoeff (pc (fun x => curvLog (n k) (A k) x μ ν)) m) atTop
      (𝓝 (mFourierCoeff (F μ ν) m)) :=
    tendsto_mFourierCoeff_of_lpTendsto_one ((hF μ ν).mono (by norm_num) (by norm_num)) m
  have hR : Tendsto (fun k => (sym (n k) μ m • mFourierCoeff (pc (fun x => A k x ν)) m -
        sym (n k) ν m • mFourierCoeff (pc (fun x => A k x μ)) m) +
        mFourierCoeff (pc (fun x => nonlin (n k) (A k) x μ ν)) m) atTop
      (𝓝 (((2 * π * Complex.I * m μ : ℂ) • mFourierCoeff (A₀ ν) m -
        (2 * π * Complex.I * m ν : ℂ) • mFourierCoeff (A₀ μ) m) +
        mFourierCoeff (fun y => A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y) m)) := by
    refine Tendsto.add (Tendsto.sub ?_ ?_) (tendsto_mFourierCoeff_of_lpTendsto_one hN m)
    · exact (tendsto_sym hn μ m).smul
        (tendsto_mFourierCoeff_of_lpTendsto_one ((hA ν).mono (by norm_num) (by norm_num)) m)
    · exact (tendsto_sym hn ν m).smul
        (tendsto_mFourierCoeff_of_lpTendsto_one ((hA μ).mono (by norm_num) (by norm_num)) m)
  simp only [hk] at hL
  have := tendsto_nhds_unique hL hR
  rw [this]
  abel

end Identification

/-! ### The comparison fields: Fourier truncations of the limit -/

section Comparison

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
  [FiniteDimensional ℂ 𝔸]

theorem coordL_vtrig (i : Fin (Module.finrank ℂ 𝔸)) (S : Finset (Fin 4 → ℤ))
    (a : (Fin 4 → ℤ) → 𝔸) (y : UnitAddTorus (Fin 4)) :
    coordL 𝔸 i (vtrig S a y) = trigPoly S (fun m => coordL 𝔸 i (a m)) y := by
  rw [vtrig_apply, trigPoly_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem coordL_mFourierCoeff (i : Fin (Module.finrank ℂ 𝔸)) {f : UnitAddTorus (Fin 4) → 𝔸}
    (hf : Integrable f volume) (m : Fin 4 → ℤ) :
    coordL 𝔸 i (mFourierCoeff f m) = mFourierCoeff (fun y => coordL 𝔸 i (f y)) m := by
  simp only [mFourierCoeff]
  have hint : Integrable (fun t => mFourier (-m) t • f t) volume :=
    hf.bdd_smul 1 (mFourier (-m)).continuous.aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [TorusSobolev.norm_mFourier_apply])
  rw [← (coordL 𝔸 i).integral_comp_comm hint]
  congr 1; funext t
  rw [map_smul]

/-- The comparison field `P_R A = Σ_{m ∈ box R} Â(m) e_m` as a `C¹` gauge test. -/
def truncTest (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸) (R : ℕ) : C1Test 𝔸 :=
  vtrigTest (TorusSobolev.box R) (fun ν => mFourierCoeff (A₀ ν))

/-- The continuum curvature `F_P = dP + [P, P]` of a test. -/
def curvTest (P : C1Test 𝔸) (μ ν : Fin 4) (y : UnitAddTorus (Fin 4)) : 𝔸 :=
  P.da μ ν y - P.da ν μ y + (P.a μ y * P.a ν y - P.a ν y * P.a μ y)

theorem truncTest_div (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸)
    (hdiv : ∀ m, ∑ μ, (2 * π * Complex.I * m μ : ℂ) • mFourierCoeff (A₀ μ) m = 0) (R : ℕ)
    (y : UnitAddTorus (Fin 4)) : ∑ μ, (truncTest A₀ R).da μ μ y = 0 := by
  simp only [truncTest, vtrigTest, vtrig_apply, dco]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [← Finset.smul_sum, hdiv m, smul_zero]

/-- Coordinates of the comparison fields are scalar Fourier truncations. -/
theorem coordL_truncTest_a {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA₀ : ∀ ν, Integrable (A₀ ν) volume) (i : Fin (Module.finrank ℂ 𝔸)) (R : ℕ) (ν : Fin 4)
    (y : UnitAddTorus (Fin 4)) :
    coordL 𝔸 i ((truncTest A₀ R).a ν y) =
      trigPoly (TorusSobolev.box R) (mFourierCoeff (fun y => coordL 𝔸 i (A₀ ν y))) y := by
  simp only [truncTest, vtrigTest]
  rw [coordL_vtrig]
  have e : (fun m => coordL 𝔸 i (mFourierCoeff (A₀ ν) m)) =
      mFourierCoeff (fun y => coordL 𝔸 i (A₀ ν y)) :=
    funext fun m => coordL_mFourierCoeff i (hA₀ ν) m
  rw [e]

end Comparison

section ComparisonLimits

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
  [FiniteDimensional ℂ 𝔸]

theorem memLp_of_coordL {p : ℝ≥0∞} {f : UnitAddTorus (Fin 4) → 𝔸}
    (hf : ∀ i, MemLp (fun y => coordL 𝔸 i (f y)) p volume) : MemLp f p volume := by
  have e : f = ∑ i, fun y => coordL 𝔸 i (f y) • bas 𝔸 i := by
    funext y; rw [Finset.sum_apply]; exact (sum_coordL (f y)).symm
  rw [e]
  exact memLp_finset_sum' _ fun i _ =>
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (bas 𝔸 i)).comp_memLp' (hf i)

/-- Scalar Fourier truncations converge strongly in `L²`. -/
theorem lpTendsto_trunc_two (f : L²(UnitAddTorus (Fin 4))) :
    LpTendsto volume 2 (fun R : ℕ => ⇑(trigPoly (TorusSobolev.box R) (mFourierCoeff f)))
      (f : UnitAddTorus (Fin 4) → ℂ) := by
  refine ⟨fun R => memLp_continuousMap _ 2, Lp.memLp f, ?_⟩
  have e : ∀ R : ℕ, eLpNorm (⇑(trigPoly (TorusSobolev.box R) (mFourierCoeff f)) - ⇑f) 2 volume =
      ENNReal.ofReal ‖f - ContinuousMap.toLp 2 volume ℂ
        (trigPoly (TorusSobolev.box R) (mFourierCoeff f))‖ := by
    intro R
    rw [← TorusSobolev.eLpNorm_coe_sub_eq, ← eLpNorm_neg]
    refine eLpNorm_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (trigPoly (TorusSobolev.box R) (mFourierCoeff f))] with y hy
    simp only [Pi.sub_apply, Pi.neg_apply, hy, neg_sub]
  simp only [e]
  simpa using ENNReal.tendsto_ofReal (tendsto_norm_sub_trigPoly_box f)

/-- **The comparison fields converge** in `L²` and (critical embedding) in `L⁴`. -/
theorem truncTest_tendsto {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA₀ : ∀ ν, MemLp (A₀ ν) 2 volume)
    {fc : Fin (Module.finrank ℂ 𝔸) → Fin 4 → L²(UnitAddTorus (Fin 4))}
    (hcoord : ∀ i ν y, coordL 𝔸 i (A₀ ν y) = fc i ν y) (hH : ∀ i ν, MemH 1 (fc i ν)) (ν : Fin 4) :
    LpTendsto volume 2 (fun R => ⇑((truncTest A₀ R).a ν)) (A₀ ν) ∧ MemLp (A₀ ν) 4 volume ∧
      LpTendsto volume 4 (fun R => ⇑((truncTest A₀ R).a ν)) (A₀ ν) := by
  have hint : ∀ ν, Integrable (A₀ ν) volume := fun ν => (hA₀ ν).integrable (by norm_num)
  have hfun : ∀ i, (fun y => coordL 𝔸 i (A₀ ν y)) = ⇑(fc i ν) := fun i => funext (hcoord i ν)
  have hc : ∀ i R y, coordL 𝔸 i ((truncTest A₀ R).a ν y) =
      trigPoly (TorusSobolev.box R) (mFourierCoeff (fc i ν)) y := by
    intro i R y
    rw [coordL_truncTest_a hint, hfun]
  have h4 : ∀ i, MemLp (fc i ν : UnitAddTorus (Fin 4) → ℂ) 4 volume :=
    fun i => (tendsto_eLpNorm_four_trunc (hH i ν)).1
  have hA4 : MemLp (A₀ ν) 4 volume := memLp_of_coordL fun i => by rw [hfun]; exact h4 i
  refine ⟨?_, hA4, ?_⟩
  · refine lpTendsto_of_coordL (fun R => memLp_continuousMap _ 2) (hA₀ ν) fun i => ?_
    refine (lpTendsto_trunc_two (fc i ν)).congr (fun R => Eventually.of_forall fun y => (hc i R y).symm)
      (Eventually.of_forall fun y => (hcoord i ν y).symm)
  · refine lpTendsto_of_coordL (fun R => memLp_continuousMap _ 4) hA4 fun i => ?_
    have hL : LpTendsto volume 4 (fun R : ℕ => ⇑(trigPoly (TorusSobolev.box R) (mFourierCoeff (fc i ν))))
        (fc i ν : UnitAddTorus (Fin 4) → ℂ) :=
      ⟨fun R => memLp_continuousMap _ 4, h4 i, (tendsto_eLpNorm_four_trunc (hH i ν)).2⟩
    exact hL.congr (fun R => Eventually.of_forall fun y => (hc i R y).symm)
      (Eventually.of_forall fun y => (hcoord i ν y).symm)

end ComparisonLimits

section CurvTrunc

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
  [FiniteDimensional ℂ 𝔸]

/-- **The curvatures of the comparison fields converge**: `F_{P_R A} → F` strongly in `L²`,
given the Fourier-side identification `F = dA + A ∧ A` (`fourier_curv`). -/
theorem curvTest_trunc_tendsto {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA₀ : ∀ ν, MemLp (A₀ ν) 2 volume)
    {fc : Fin (Module.finrank ℂ 𝔸) → Fin 4 → L²(UnitAddTorus (Fin 4))}
    (hcoord : ∀ i ν y, coordL 𝔸 i (A₀ ν y) = fc i ν y) (hH : ∀ i ν, MemH 1 (fc i ν))
    {F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸} (hF2 : ∀ μ ν, MemLp (F μ ν) 2 volume)
    (hcurv : ∀ μ ν m, mFourierCoeff (F μ ν) m -
      mFourierCoeff (fun y => A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y) m =
      (2 * π * Complex.I * m μ : ℂ) • mFourierCoeff (A₀ ν) m -
        (2 * π * Complex.I * m ν : ℂ) • mFourierCoeff (A₀ μ) m) (μ ν : Fin 4) :
    LpTendsto volume 2 (fun R => curvTest (truncTest A₀ R) μ ν) (F μ ν) := by
  have hT := fun ν => truncTest_tendsto hA₀ hcoord hH ν
  set M := ContinuousLinearMap.mul ℝ 𝔸
  -- the quadratic part
  have hQ := (LpTendsto.bilin (r := 2) M (hT μ).2.2 (hT ν).2.2).sub
    (LpTendsto.bilin (r := 2) M (hT ν).2.2 (hT μ).2.2)
  -- the linear part, componentwise
  set G : UnitAddTorus (Fin 4) → 𝔸 := fun y => F μ ν y - (A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y)
  have hG2 : MemLp G 2 volume := (hF2 μ ν).sub hQ.memLp_lim
  have hGint : Integrable G volume := hG2.integrable (by norm_num)
  have hint : ∀ ν, Integrable (A₀ ν) volume := fun ν => (hA₀ ν).integrable (by norm_num)
  have hlin : LpTendsto volume 2 (fun R y => (truncTest A₀ R).da μ ν y - (truncTest A₀ R).da ν μ y)
      G := by
    refine lpTendsto_of_coordL (fun R => memLp_continuousMap ((truncTest A₀ R).da μ ν -
      (truncTest A₀ R).da ν μ) 2) hG2 fun i => ?_
    set g : UnitAddTorus (Fin 4) → ℂ := fun y => coordL 𝔸 i (G y)
    have hg2 : MemLp g 2 volume := (coordL 𝔸 i).restrictScalars ℝ |>.comp_memLp' hG2
    have hcoef : ∀ m, coordL 𝔸 i ((2 * π * Complex.I * m μ : ℂ) • mFourierCoeff (A₀ ν) m -
        (2 * π * Complex.I * m ν : ℂ) • mFourierCoeff (A₀ μ) m) = mFourierCoeff g m := by
      intro m
      have hQint : Integrable (fun y => A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y) volume :=
        (hQ.memLp_lim.integrable (by norm_num)).congr (Eventually.of_forall fun y => rfl)
      rw [← hcurv μ ν m, ← mFourierCoeff_sub' (f := F μ ν)
        (g := fun y => A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y) ((hF2 μ ν).integrable (by norm_num)) hQint]
      show coordL 𝔸 i (mFourierCoeff G m) = _
      rw [coordL_mFourierCoeff i hGint]
    have hc : ∀ R y, coordL 𝔸 i ((truncTest A₀ R).da μ ν y - (truncTest A₀ R).da ν μ y) =
        trigPoly (TorusSobolev.box R) (mFourierCoeff (hg2.toLp g)) y := by
      intro R y
      simp only [truncTest, vtrigTest, map_sub, coordL_vtrig, trigPoly_apply, dco]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mFourierCoeff_toLp_eq, ← hcoef m, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    refine (lpTendsto_trunc_two (hg2.toLp g)).congr
      (fun R => Eventually.of_forall fun y => (hc R y).symm) ?_
    filter_upwards [hg2.coeFn_toLp] with y hy
    rw [hy]
  refine (hlin.add hQ).congr (fun R => Eventually.of_forall fun y => ?_)
    (Eventually.of_forall fun y => ?_)
  · simp only [curvTest, Pi.add_apply, Pi.sub_apply, M, ContinuousLinearMap.mul_apply']
  · simp only [G, Pi.add_apply, Pi.sub_apply, M, ContinuousLinearMap.mul_apply']
    abel

end CurvTrunc

/-! ### Fixed-smooth-field consistency -/

section Consistency

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- `R_h^0 F_h(𝒮_h P) → F_P = dP + [P, P]` strongly in `L²` for every `C¹` test `P`. -/
theorem curvLog_sample_tendsto (hn : Tendsto n atTop atTop) (P : C1Test 𝔸) (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => curvLog (n k) (sampleTest (n k) P) x μ ν))
      (curvTest P μ ν) := by
  have h1 := lpTendsto_linCurl_sample hn P μ ν
  have h2 := tendsto_nonlinear hn (A := fun k => sampleTest (n k) P) (A₀ := fun κ => ⇑(P.a κ))
    (fun κ => lpTendsto_sample hn P κ 4) μ ν
  refine (h1.add h2).congr (fun k => Eventually.of_forall fun y => ?_)
    (Eventually.of_forall fun y => ?_)
  · simp only [Pi.add_apply, pc]; abel
  · simp only [curvTest, Pi.add_apply]

theorem codiffT_eq (T : 𝔸 →L[ℝ] E) {N : ℕ} [NeZero N] (B : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) :
    codiffT T B x = -T (∑ μ, DmV μ (fun y => B y μ) x) := by
  simp [codiffT, periodicHodgeCodiff, periodicHodgeBwd, DmV, GridSobolev.gridStep, map_sum,
    map_smul, map_sub]

theorem DmV_eq_DpV_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ}
    (μ : Fin 4) (v : LatticeTorusPlancherel.Grid 4 N → F) (x : LatticeTorusPlancherel.Grid 4 N) :
    DmV μ v x = DpV μ v (x - Pi.single μ 1) := by
  simp [DmV, DpV, sub_add_cancel]

/-- `δ_h T(𝒮_h P) → T(δP) = 0` for a divergence-free `C¹` test. -/
theorem codiff_sample_tendsto (hn : Tendsto n atTop atTop) (T : 𝔸 →L[ℝ] E) (P : C1Test 𝔸)
    (hdiv : ∀ y, ∑ μ, P.da μ μ y = 0) :
    Tendsto (fun k => gridNorm (codiffT T (sampleTest (n k) P))) atTop (𝓝 0) := by
  have hμ : ∀ μ, LpTendsto volume 2 (fun k => pc (DmV μ (fun x => sampleTest (n k) P x μ)))
      (P.da μ μ) := by
    intro μ
    have h := (lpTendsto_Dp_sample hn P μ μ 2).shift_neg hn (by norm_num) μ
    refine h.congr (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => rfl)
    simp only [pc]; rw [DmV_eq_DpV_shift]; rfl
  have hsum : LpTendsto volume 2 (fun k => pc (fun x => ∑ μ, DmV μ (fun y => sampleTest (n k) P y μ) x))
      (fun y => ∑ μ, P.da μ μ y) := by
    have := ((hμ 0).add (hμ 1)).add ((hμ 2).add (hμ 3))
    refine this.congr (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · simp only [Pi.add_apply, pc, Fin.sum_univ_four]; abel
    · simp only [Pi.add_apply, Fin.sum_univ_four]; abel
  have hT := (hsum.clm T).neg
  have hlim := hT.tendsto_toReal_eLpNorm
  have e0 : (eLpNorm (-fun y => T (∑ μ, P.da μ μ y)) 2 volume).toReal = 0 := by
    simp [hdiv]
  rw [e0] at hlim
  refine hlim.congr fun k => ?_
  rw [gridNorm_eq_toReal]
  congr 2
  funext y
  simp only [Pi.neg_apply, pc, codiffT_eq]

/-- The samples of a fixed test eventually lie in the chart `h |W| ≤ 1/32`. -/
theorem eventually_chart_sample (hn : Tendsto n atTop atTop) (P : C1Test 𝔸) :
    ∀ᶠ k in atTop, ∀ x μ ν, ((n k : ℝ))⁻¹ * slotFn (sampleTest (n k) P) μ ν x ≤ 1 / 32 := by
  set M := ∑ κ, ‖P.a κ‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h0 : Tendsto (fun k => ((n k : ℝ))⁻¹ * (4 * M)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_n hn).mul_const (4 * M)
  filter_upwards [(tendsto_order.1 h0).2 (1 / 32) (by norm_num)] with k hk x μ ν
  have hs := normSum_slots_sample_le (N := n k) P x μ ν
  have : ((n k : ℝ))⁻¹ * slotFn (sampleTest (n k) P) μ ν x ≤ ((n k : ℝ))⁻¹ * (4 * M) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  linarith

/-- The nodal `L⁴` norms of the samples converge to the continuum `L⁴` norm. -/
theorem g4_sample_tendsto (hn : Tendsto n atTop atTop) (T : 𝔸 →L[ℝ] E) (P : C1Test 𝔸) (ν : Fin 4) :
    Tendsto (fun k => g4 (fun x => T (sampleTest (n k) P x ν))) atTop
      (𝓝 (eLpNorm (fun y => T (P.a ν y)) 4 volume).toReal) := by
  have h := ((lpTendsto_sample hn P ν 4).clm T).tendsto_toReal_eLpNorm
  refine h.congr fun k => ?_
  rw [g4_eq_toReal]
  rfl

end Consistency

/-! ### The comparison argument: strong convergence of the forward differences -/

section Cauchy

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
  [FiniteDimensional ℂ 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem gridNorm_DpV_le (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖)
    {N : ℕ} [NeZero N] (w : LatticeTorusPlancherel.Grid 4 N → 𝔸) (μ : Fin 4) :
    gridNorm (DpV μ w) ≤ c * gridNorm (DpV μ (fun x => T (w x))) := by
  refine gridNorm_le_mul_gridNorm hc0 fun x => ?_
  have e : T (DpV μ w x) = DpV μ (fun x => T (w x)) x := by simp [DpV, map_smul, map_sub]
  rw [← e]; exact hc _

/-- **One comparison step**: for a divergence-free `C¹` test `P` whose samples are small,
`limsup_h ‖R_h^0 D⁺_μ A_{h,ν} - ∂_μ P_ν‖_{L²} ≤ c δ`, where
`δ = 8 ‖T‖ Σ_{μ<ν} ‖F_{μν} - F_{P,μν}‖_{L²} + 3 Σ_ν ‖T(A_ν - P_ν)‖_{L²}`
(absorption inequality + fixed-smooth-field consistency). -/
theorem eventually_comparison (hn : Tendsto n atTop atTop) (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖) {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    (hδ : ∀ k, codiffT T (A k) = 0) (hs : ∀ k μ, g4 (fun x => T (A k x μ)) ≤ epsStar T c)
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA2 : ∀ ν, LpTendsto volume 2 (fun k => pc (fun x => A k x ν)) (A₀ ν))
    {F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hF : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x => curvLog (n k) (A k) x μ ν)) (F μ ν))
    (P : C1Test 𝔸) (hdiv : ∀ y, ∑ μ, P.da μ μ y = 0)
    (hP4 : ∀ ν, (eLpNorm (fun y => T (P.a ν y)) 4 volume).toReal < 3 * epsStar T c)
    (μ ν : Fin 4) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, (eLpNorm (pc (DpV μ (fun x => A k x ν)) - ⇑(P.da μ ν)) 2 volume).toReal ≤
      c * (8 * (‖T‖ * ∑ p ∈ pairs4, (eLpNorm (F p.1 p.2 - curvTest P p.1 p.2) 2 volume).toReal) +
        3 * ∑ κ, (eLpNorm ((fun y => T (A₀ κ y)) - fun y => T (P.a κ y)) 2 volume).toReal) + η := by
  set ε := epsStar T c
  have hε : 0 < ε := epsStar_pos T hc0
  set B : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸 := fun k => sampleTest (n k) P
  set δ := 8 * (‖T‖ * ∑ p ∈ pairs4, (eLpNorm (F p.1 p.2 - curvTest P p.1 p.2) 2 volume).toReal) +
    3 * ∑ κ, (eLpNorm ((fun y => T (A₀ κ y)) - fun y => T (P.a κ y)) 2 volume).toReal
  -- the right-hand side of the absorption inequality converges to `δ`
  set RHS : ℕ → ℝ := fun k => 8 * (‖T‖ * ∑ p ∈ pairs4,
      gridNorm (fun x => curvLog (n k) (A k) x p.1 p.2 - curvLog (n k) (B k) x p.1 p.2) +
      gridNorm (codiffT T (B k))) + 3 * ∑ κ, gridNorm (fun x => T ((A k - B k) x κ))
  have hRHS : Tendsto RHS atTop (𝓝 δ) := by
    have h1 : ∀ p : Fin 4 × Fin 4, Tendsto (fun k => gridNorm (fun x => curvLog (n k) (A k) x p.1 p.2 -
        curvLog (n k) (B k) x p.1 p.2)) atTop
        (𝓝 (eLpNorm (F p.1 p.2 - curvTest P p.1 p.2) 2 volume).toReal) := by
      intro p
      have := ((hF p.1 p.2).sub (curvLog_sample_tendsto hn P p.1 p.2)).tendsto_toReal_eLpNorm
      refine this.congr fun k => ?_
      rw [gridNorm_eq_toReal]; rfl
    have h2 := codiff_sample_tendsto hn T P hdiv
    have h3 : ∀ κ, Tendsto (fun k => gridNorm (fun x => T ((A k - B k) x κ))) atTop
        (𝓝 (eLpNorm ((fun y => T (A₀ κ y)) - fun y => T (P.a κ y)) 2 volume).toReal) := by
      intro κ
      have := (((hA2 κ).clm T).sub ((lpTendsto_sample hn P κ 2).clm T)).tendsto_toReal_eLpNorm
      refine this.congr fun k => ?_
      rw [gridNorm_eq_toReal]
      congr 2; funext y; simp [pc, B, map_sub]
    have hs1 := tendsto_finsetSum pairs4 fun p _ => h1 p
    have hs3 := tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun κ _ => h3 κ
    have := (((hs1.const_mul ‖T‖).add h2).const_mul 8).add (hs3.const_mul 3)
    simpa [RHS, δ] using this
  -- the samples' derivatives converge
  have hDB : Tendsto (fun k => (eLpNorm (pc (DpV μ (fun x => B k x ν)) - ⇑(P.da μ ν)) 2 volume).toReal)
      atTop (𝓝 0) := by
    have := (lpTendsto_Dp_sample hn P μ ν 2)
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp this.tendsto
    rw [ENNReal.toReal_zero] at h
    exact h
  -- eventually the absorption inequality applies
  have hgB : ∀ κ, ∀ᶠ k in atTop, g4 (fun x => T (B k x κ)) ≤ 3 * ε := fun κ =>
    (g4_sample_tendsto hn T P κ).eventually (ge_mem_nhds (hP4 κ))
  have hgB' : ∀ᶠ k in atTop, ∀ κ, g4 (fun x => T (B k x κ)) ≤ 3 * ε :=
    Filter.eventually_all.2 hgB
  have hfin := (hRHS.const_mul c).add hDB
  rw [add_zero] at hfin
  filter_upwards [hgB', eventually_chart_sample hn P,
    (tendsto_order.1 hfin).2 (c * δ + η) (by linarith)] with k hk hch hlt
  have hchA := chart_of_small T hc0 hc (epsStar_chart T hc0) (A k) (hs k)
  have hA4 : ∀ κ, g4 (fun x => A k x κ) ≤ 3 * (c * ε) := by
    intro κ
    refine (g4_le_mul hc0 fun x => hc (A k x κ)).trans ?_
    have := mul_le_mul_of_nonneg_left (hs k κ) hc0
    have h0 : 0 ≤ c * ε := mul_nonneg hc0 hε.le
    linarith
  have hB4 : ∀ κ, g4 (fun x => B k x κ) ≤ 3 * (c * ε) := by
    intro κ
    refine (g4_le_mul hc0 fun x => hc (B k x κ)).trans ?_
    have := mul_le_mul_of_nonneg_left (hk κ) hc0
    linarith
  have habs := coulomb_absorption T hc0 hc (A k) (B k) hchA hch (hδ k) hA4 hB4
    (epsStar_absorb T hc0)
  -- comparing the forward differences
  have hsplit : (eLpNorm (pc (DpV μ (fun x => A k x ν)) - ⇑(P.da μ ν)) 2 volume).toReal ≤
      gridNorm (DpV μ (fun x => (A k - B k) x ν)) +
        (eLpNorm (pc (DpV μ (fun x => B k x ν)) - ⇑(P.da μ ν)) 2 volume).toReal := by
    rw [gridNorm_eq_toReal]
    have e : pc (DpV μ (fun x => A k x ν)) - ⇑(P.da μ ν) = pc (DpV μ (fun x => (A k - B k) x ν)) +
        (pc (DpV μ (fun x => B k x ν)) - ⇑(P.da μ ν)) := by
      funext y; simp only [pc, Pi.add_apply, Pi.sub_apply, DpV, smul_sub]; abel
    rw [e]
    refine (ENNReal.toReal_mono ?_ (eLpNorm_add_le (stronglyMeasurable_pc _).aestronglyMeasurable
      ((stronglyMeasurable_pc _).aestronglyMeasurable.sub (P.da μ ν).continuous.aestronglyMeasurable)
      (by norm_num))).trans ?_
    · exact ENNReal.add_ne_top.2 ⟨(memLp_pc_gen _ 2).2.ne,
        ((memLp_pc_gen _ 2).sub (memLp_continuousMap _ 2)).2.ne⟩
    · exact (ENNReal.toReal_add (memLp_pc_gen _ 2).2.ne
        ((memLp_pc_gen _ 2).sub (memLp_continuousMap _ 2)).2.ne).le
  have hG : gridNorm (DpV μ (fun x => (A k - B k) x ν)) ≤ c * RHS k := by
    refine (gridNorm_DpV_le T hc0 hc _ μ).trans (mul_le_mul_of_nonneg_left ?_ hc0)
    refine le_trans ?_ habs
    exact Finset.single_le_sum (f := fun μ => ∑ ν, gridNorm (DpV μ (fun x => T ((A k - B k) x ν))))
      (fun _ _ => Finset.sum_nonneg fun _ _ => gridNorm_nonneg _) (Finset.mem_univ μ) |>.trans'
      (Finset.single_le_sum (f := fun ν => gridNorm (DpV μ (fun x => T ((A k - B k) x ν))))
        (fun _ _ => gridNorm_nonneg _) (Finset.mem_univ ν))
  have : c * RHS k + (eLpNorm (pc (DpV μ (fun x => B k x ν)) - ⇑(P.da μ ν)) 2 volume).toReal <
      c * δ + η := hlt
  linarith

end Cauchy

section Cauchy2

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
  [FiniteDimensional ℂ 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem dist_toLp_eq {F : Type*} [NormedAddCommGroup F] {f g : UnitAddTorus (Fin 4) → F}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    dist (hf.toLp f) (hg.toLp g) = (eLpNorm (f - g) 2 volume).toReal := by
  rw [Lp.dist_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [Pi.sub_apply, Pi.sub_apply, h1, h2]

/-- **Strong convergence of the forward differences** (`R_h^0 D⁺_h A_h → ∂A` in `L²`): the
sequence is Cauchy, by the comparison with the sampled Fourier truncations of the limit. -/
theorem exists_tendsto_differences (hn : Tendsto n atTop atTop) (T : 𝔸 →L[ℝ] E) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    (hδ : ∀ k, codiffT T (A k) = 0) (hs : ∀ k μ, g4 (fun x => T (A k x μ)) ≤ epsStar T c)
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA2 : ∀ ν, LpTendsto volume 2 (fun k => pc (fun x => A k x ν)) (A₀ ν))
    {fc : Fin (Module.finrank ℂ 𝔸) → Fin 4 → L²(UnitAddTorus (Fin 4))}
    (hcoord : ∀ i ν y, coordL 𝔸 i (A₀ ν y) = fc i ν y) (hH : ∀ i ν, MemH 1 (fc i ν))
    {F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hF : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x => curvLog (n k) (A k) x μ ν)) (F μ ν))
    (hdiv : ∀ m, ∑ μ, (2 * π * Complex.I * m μ : ℂ) • mFourierCoeff (A₀ μ) m = 0)
    (hcurv : ∀ μ ν m, mFourierCoeff (F μ ν) m -
      mFourierCoeff (fun y => A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y) m =
      (2 * π * Complex.I * m μ : ℂ) • mFourierCoeff (A₀ ν) m -
        (2 * π * Complex.I * m ν : ℂ) • mFourierCoeff (A₀ μ) m) (μ ν : Fin 4) :
    ∃ G : UnitAddTorus (Fin 4) → 𝔸,
      LpTendsto volume 2 (fun k => pc (DpV μ (fun x => A k x ν))) G := by
  set ε := epsStar T c
  have hε : 0 < ε := epsStar_pos T hc0
  set P : ℕ → C1Test 𝔸 := fun R => truncTest A₀ R
  have hA₀2 : ∀ ν, MemLp (A₀ ν) 2 volume := fun ν => (hA2 ν).memLp_lim
  have hTr := fun κ => truncTest_tendsto hA₀2 hcoord hH κ
  have hCv := fun μ ν => curvTest_trunc_tendsto hA₀2 hcoord hH (fun μ ν => (hF μ ν).memLp_lim)
    hcurv μ ν
  have hdivP : ∀ R y, ∑ μ, (P R).da μ μ y = 0 := fun R y => truncTest_div A₀ hdiv R y
  -- the limit is small in `L⁴` (Fatou)
  have hTA₀ : ∀ κ, (eLpNorm (fun y => T (A₀ κ y)) 4 volume).toReal ≤ ε := by
    intro κ
    have hb : ∀ k, eLpNorm (fun y => T (pc (fun x => A k x κ) y)) 4 volume ≤ ENNReal.ofReal ε := by
      intro k
      rw [show (fun y => T (pc (fun x => A k x κ) y)) = pc (fun x => T (A k x κ)) from rfl,
        eLpNorm_pc_four_g4]
      exact ENNReal.ofReal_le_ofReal (hs k κ)
    have := ((hA2 κ).clm T).eLpNorm_le_of_bound (by norm_num) hb
    exact ENNReal.toReal_le_of_le_ofReal hε.le this
  -- good radii
  have hgood : ∀ᶠ R in atTop, ∀ κ, (eLpNorm (fun y => T ((P R).a κ y)) 4 volume).toReal < 3 * ε := by
    refine Filter.eventually_all.2 fun κ => ?_
    have h := ((hTr κ).2.2.clm T).tendsto_toReal_eLpNorm
    exact h.eventually (gt_mem_nhds (by linarith [hTA₀ κ]))
  -- the comparison errors tend to zero
  set δ : ℕ → ℝ := fun R => 8 * (‖T‖ * ∑ p ∈ pairs4,
      (eLpNorm (F p.1 p.2 - curvTest (P R) p.1 p.2) 2 volume).toReal) +
    3 * ∑ κ, (eLpNorm ((fun y => T (A₀ κ y)) - fun y => T ((P R).a κ y)) 2 volume).toReal
  have hδR : Tendsto δ atTop (𝓝 0) := by
    have h1 : ∀ p : Fin 4 × Fin 4, Tendsto (fun R =>
        (eLpNorm (F p.1 p.2 - curvTest (P R) p.1 p.2) 2 volume).toReal) atTop (𝓝 0) := by
      intro p
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hCv p.1 p.2).tendsto
      rw [ENNReal.toReal_zero] at this
      refine this.congr fun R => ?_
      simp only [Function.comp_apply]
      rw [eLpNorm_sub_comm]
    have h3 : ∀ κ, Tendsto (fun R =>
        (eLpNorm ((fun y => T (A₀ κ y)) - fun y => T ((P R).a κ y)) 2 volume).toReal) atTop
        (𝓝 0) := by
      intro κ
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ((hTr κ).1.clm T).tendsto
      rw [ENNReal.toReal_zero] at this
      refine this.congr fun R => ?_
      simp only [Function.comp_apply]
      rw [eLpNorm_sub_comm]
    have hs1 := tendsto_finsetSum pairs4 fun p _ => h1 p
    have hs3 := tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun κ _ => h3 κ
    have := ((hs1.const_mul ‖T‖).const_mul 8).add (hs3.const_mul 3)
    simpa [δ] using this
  -- the Cauchy property in `L²(𝕋⁴; 𝔸)`
  set D : ℕ → Lp 𝔸 2 (volume : Measure (UnitAddTorus (Fin 4))) := fun k =>
    (memLp_pc_gen (DpV μ (fun x => A k x ν)) 2).toLp _
  set Q : ℕ → Lp 𝔸 2 (volume : Measure (UnitAddTorus (Fin 4))) := fun R =>
    (memLp_continuousMap ((P R).da μ ν) 2).toLp _
  have hdist : ∀ k R, dist (D k) (Q R) =
      (eLpNorm (pc (DpV μ (fun x => A k x ν)) - ⇑((P R).da μ ν)) 2 volume).toReal :=
    fun k R => dist_toLp_eq _ _
  have hcauchy : CauchySeq D := by
    rw [Metric.cauchySeq_iff']
    intro ε' hε'
    have hcδ : Tendsto (fun R => c * δ R) atTop (𝓝 0) := by simpa using hδR.const_mul c
    obtain ⟨R, hRgood, hRδ⟩ := (hgood.and ((tendsto_order.1 hcδ).2 (ε' / 4) (by positivity))).exists
    have hev := eventually_comparison hn T hc0 hc hδ hs hA2 hF (P R) (hdivP R) hRgood μ ν
      (η := ε' / 4) (by positivity)
    obtain ⟨K, hK⟩ := eventually_atTop.1 hev
    refine ⟨K, fun k hk => ?_⟩
    have h1 := hK k hk
    have h2 := hK K le_rfl
    rw [← hdist] at h1 h2
    calc dist (D k) (D K) ≤ dist (D k) (Q R) + dist (D K) (Q R) := dist_triangle_right _ _ _
      _ < ε' := by linarith
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨G, fun k => memLp_pc_gen _ 2, Lp.memLp G, ?_⟩
  have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (f := D) (f_lim := G)).1 hG
  refine this.congr fun k => eLpNorm_congr_ae ?_
  filter_upwards [(memLp_pc_gen (DpV μ (fun x => A k x ν)) 2).coeFn_toLp] with y hy
  simp only [Pi.sub_apply, D, hy]

end Cauchy2

/-! ### `thm:native-discrete-Coulomb` -/

section Main

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
  [FiniteDimensional ℂ 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem Dp_comp_clm {N : ℕ} [NeZero N] (ℓ : 𝔸 →L[ℂ] ℂ) (μ : Fin 4)
    (v : LatticeTorusPlancherel.Grid 4 N → 𝔸) :
    Dp μ (fun x => ℓ (v x)) = fun x => ℓ (DpV μ v x) := by
  funext x
  simp only [Dp_apply, DpV]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_sub, smul_eq_mul]
  norm_cast

/-- **`thm:native-discrete-Coulomb` (critical discrete Coulomb compactness)**, unit-torus
rendering.  There is `ε* > 0` (explicitly `ε* = 1/(69120 (‖T‖+1)(c+1)²)`) such that, for every
sequence of grids `N_k → ∞` and nodal connections `A_k` with
`δ_h T A_k = 0`, `‖T A_{k,μ}‖_{4,h} ≤ ε*` and `R_h^0 F_h(A_k) → F` strongly in `L²`, after
extraction there are `A` and `G` with
* `R_h^0 A_k → A` strongly in `L⁴`;
* `R_h^0 D⁺_μ A_{k,ν} → G_{μν}` strongly in `L²`, where `G_{μν} = ∂_μ A_ν` (Fourier side:
  `Ĝ_{μν}(m) = 2πi m_μ Â_ν(m)` for every `m`);
* for every complex-linear coordinate `ℓ` of `𝔸`, `ℓ A_ν ∈ H¹` and the trigonometric
  reconstructions `𝓘_h^trig (ℓ A_{k,ν})` converge to it strongly in `H¹`;
* **`F = F_A`**: `F_{μν} = ∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν]` a.e.;
* **`δA = 0`**: `Σ_μ ∂_μ A_μ = 0` a.e. -/
theorem native_discrete_Coulomb (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖) :
    ∃ ε > 0, ∀ (n : ℕ → ℕ) [∀ k, NeZero (n k)], Tendsto n atTop atTop →
      ∀ (A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸)
        (F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸),
      (∀ k, codiffT T (A k) = 0) → (∀ k μ, g4 (fun x => T (A k x μ)) ≤ ε) →
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x => curvLog (n k) (A k) x μ ν)) (F μ ν)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸)
        (G : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸),
        (∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A (φ k) x μ)) (A₀ μ)) ∧
        (∀ μ ν, LpTendsto volume 2 (fun k => pc (DpV μ (fun x => A (φ k) x ν))) (G μ ν)) ∧
        (∀ μ ν m, mFourierCoeff (G μ ν) m =
          (2 * π * Complex.I * m μ : ℂ) • mFourierCoeff (A₀ ν) m) ∧
        (∀ (ℓ : 𝔸 →L[ℂ] ℂ) ν, ∃ f : L²(UnitAddTorus (Fin 4)),
          ((f : UnitAddTorus (Fin 4) → ℂ) =ᵐ[volume] fun y => ℓ (A₀ ν y)) ∧ MemH 1 f ∧
          Tendsto (fun k => sobSq 1 ⇑(trigLp (fun x => ℓ (A (φ k) x ν)) - f)) atTop (𝓝 0)) ∧
        (∀ μ ν, F μ ν =ᵐ[volume]
          fun y => G μ ν y - G ν μ y + (A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y)) ∧
        ((fun y => ∑ μ, G μ μ y) =ᵐ[volume] 0) := by
  refine ⟨epsStar T c, epsStar_pos T hc0, fun n _ hn A F hδ hs hF => ?_⟩
  set ε := epsStar T c
  have hε : 0 < ε := epsStar_pos T hc0
  have hch : ∀ k x μ ν, ((n k : ℝ))⁻¹ * slotFn (A k) μ ν x ≤ 1 / 32 := fun k =>
    chart_of_small T hc0 hc (epsStar_chart T hc0) (A k) (hs k)
  have hA4 : ∀ k μ, g4 (fun x => A k x μ) ≤ c * ε := fun k μ =>
    (g4_le_mul hc0 fun x => hc (A k x μ)).trans (mul_le_mul_of_nonneg_left (hs k μ) hc0)
  -- uniform discrete `H¹` bound
  have hFb : ∀ p : Fin 4 × Fin 4, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ k,
      eLpNorm (pc (fun x => curvLog (n k) (A k) x p.1 p.2)) 2 volume ≤ C :=
    fun p => exists_bound_of_lpTendsto (hF p.1 p.2)
  choose CF hCF hCFb using hFb
  set SF : ℝ := ∑ p ∈ pairs4, (CF p).toReal
  set M : ℝ := 8 * ‖T‖ * SF + 3 * (4 * ε)
  have hM : ∀ k μ ν, gridNorm (DpV μ (fun x => T (A k x ν))) ≤ M := by
    intro k μ ν
    have hap := coulomb_apriori' T hc0 hc (A k) (hδ k) (hs k)
    have h1 : ∑ p ∈ pairs4, gridNorm (fun x => curvLog (n k) (A k) x p.1 p.2) ≤ SF := by
      refine Finset.sum_le_sum fun p _ => ?_
      have := hCFb p k
      rw [eLpNorm_pc_two_eq] at this
      have := ENNReal.toReal_mono (hCF p) this
      rwa [ENNReal.toReal_ofReal (gridNorm_nonneg _)] at this
    have h2 : ∑ ν, gridNorm (fun x => T (A k x ν)) ≤ 4 * ε := by
      calc ∑ ν, gridNorm (fun x => T (A k x ν)) ≤ ∑ _ν : Fin 4, ε :=
            Finset.sum_le_sum fun ν _ => (gridNorm_le_g4 _).trans (hs k ν)
        _ = 4 * ε := by simp
    have h3 : gridNorm (DpV μ (fun x => T (A k x ν))) ≤
        ∑ μ, ∑ ν, gridNorm (DpV μ (fun x => T (A k x ν))) :=
      (Finset.single_le_sum (f := fun ν => gridNorm (DpV μ (fun x => T (A k x ν))))
        (fun _ _ => gridNorm_nonneg _) (Finset.mem_univ ν)).trans
      (Finset.single_le_sum (f := fun μ => ∑ ν, gridNorm (DpV μ (fun x => T (A k x ν))))
        (fun _ _ => Finset.sum_nonneg fun _ _ => gridNorm_nonneg _) (Finset.mem_univ μ))
    have hT0 := norm_nonneg T
    nlinarith
  -- extraction
  obtain ⟨φ, hφ, A₀, fc, hA2, hcoord, hH, hfc⟩ := exists_subseq_connection hn T hc0 hc A
    (B := max ε M) (fun k ν => ((gridNorm_le_g4 _).trans (hs k ν)).trans (le_max_left _ _))
    (fun k μ ν => (hM k μ ν).trans (le_max_right _ _))
  have hn' : Tendsto (fun k => n (φ k)) atTop atTop := hn.comp hφ.tendsto_atTop
  have hF' : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => curvLog (n (φ k)) (A (φ k)) x μ ν)) (F μ ν) :=
    fun μ ν => (hF μ ν).comp_strictMono hφ
  -- Fourier-side identification
  have hdiv := fourier_div_zero hn' T hc (A := fun k => A (φ k)) hA2 (fun k => hδ (φ k))
  have hcurv := fourier_curv hn' (A := fun k => A (φ k)) hA2 hF' (fun k => hch (φ k))
    (fun k => hA4 (φ k))
  -- strong convergence of the forward differences
  have hGex := fun μ ν => exists_tendsto_differences hn' T hc0 hc (A := fun k => A (φ k))
    (fun k => hδ (φ k)) (fun k => hs (φ k)) hA2 hcoord hH hF' hdiv hcurv μ ν
  choose G hG using hGex
  -- `lem:native-reconstruction-identification` for every complex coordinate
  have hid : ∀ (ℓ : 𝔸 →L[ℂ] ℂ) ν, ∃ hm : MemLp (fun y => ℓ (A₀ ν y)) 2 volume,
      (∀ μ, weakDeriv μ (hm.toLp _) = (((hG μ ν).clm (ℓ.restrictScalars ℝ)).memLp_lim).toLp _) ∧
      MemH 1 (hm.toLp _) ∧
      Tendsto (fun k => sobSq 1 ⇑(trigLp (fun x => ℓ (A (φ k) x ν)) - hm.toLp _)) atTop (𝓝 0) ∧
      MemLp (hm.toLp _ : UnitAddTorus (Fin 4) → ℂ) 4 volume ∧
      Tendsto (fun k => eLpNorm (fun y => pc (fun x => ℓ (A (φ k) x ν)) y - (hm.toLp _) y) 4 volume)
        atTop (𝓝 0) := by
    intro ℓ ν
    have hℓA := (hA2 ν).clm (ℓ.restrictScalars ℝ)
    refine ⟨hℓA.memLp_lim, ?_⟩
    have hu : Tendsto (fun k => ‖pcLp (fun x => ℓ (A (φ k) x ν)) - hℓA.memLp_lim.toLp _‖) atTop
        (𝓝 0) := norm_pcLp_of_lpTendsto (n := fun k => n (φ k)) hℓA
    have hv : ∀ μ, Tendsto (fun k => ‖pcLp (Dp μ (fun x => ℓ (A (φ k) x ν))) -
        (((hG μ ν).clm (ℓ.restrictScalars ℝ)).memLp_lim).toLp _‖) atTop (𝓝 0) := by
      intro μ
      have h := norm_pcLp_of_lpTendsto (n := fun k => n (φ k))
        (u := fun k => Dp μ (fun x => ℓ (A (φ k) x ν)))
        (((hG μ ν).clm (ℓ.restrictScalars ℝ)).congr (fun k => Eventually.of_forall fun y => by
          simp only [Dp_comp_clm]; rfl) (Eventually.of_forall fun y => rfl))
      exact h
    exact native_reconstruction_identification hn' hu hv
  -- the `L⁴` convergence of the connections (coordinates)
  have hA₀4 : ∀ ν, MemLp (A₀ ν) 4 volume := fun ν => memLp_of_coordL fun i => by
    obtain ⟨hm, -, -, -, h4, -⟩ := hid (coordL 𝔸 i) ν
    exact h4.ae_eq hm.coeFn_toLp
  have hL4 : ∀ ν, LpTendsto volume 4 (fun k => pc (fun x => A (φ k) x ν)) (A₀ ν) := by
    intro ν
    refine lpTendsto_of_coordL (fun k => memLp_pc_gen _ 4) (hA₀4 ν) fun i => ?_
    obtain ⟨hm, -, -, -, h4, ht⟩ := hid (coordL 𝔸 i) ν
    have hL : LpTendsto volume 4 (fun k => pc (fun x => coordL 𝔸 i (A (φ k) x ν)))
        (hm.toLp _ : UnitAddTorus (Fin 4) → ℂ) := ⟨fun k => memLp_pc_gen _ 4, h4, ht⟩
    exact hL.congr (fun k => Eventually.of_forall fun y => rfl) hm.coeFn_toLp
  refine ⟨φ, hφ, A₀, G, hL4, hG, ?_, ?_, ?_, ?_⟩
  · -- `G = ∂A` on the Fourier side
    intro μ ν m
    have h1 : Tendsto (fun k => mFourierCoeff (pc (DpV μ (fun x => A (φ k) x ν))) m) atTop
        (𝓝 (mFourierCoeff (G μ ν) m)) :=
      tendsto_mFourierCoeff_of_lpTendsto_one ((hG μ ν).mono (by norm_num) (by norm_num)) m
    have h2 : Tendsto (fun k => mFourierCoeff (pc (DpV μ (fun x => A (φ k) x ν))) m) atTop
        (𝓝 ((2 * π * Complex.I * m μ : ℂ) • mFourierCoeff (A₀ ν) m)) := by
      simp only [mFourierCoeff_pc_DpV]
      exact (tendsto_sym hn' μ m).smul
        (tendsto_mFourierCoeff_of_lpTendsto_one ((hA2 ν).mono (by norm_num) (by norm_num)) m)
    exact tendsto_nhds_unique h1 h2
  · -- trigonometric `H¹`
    intro ℓ ν
    obtain ⟨hm, -, hH1, hS, -, -⟩ := hid ℓ ν
    exact ⟨hm.toLp _, hm.coeFn_toLp, hH1, hS⟩
  · -- `F = F_A`
    intro μ ν
    have hYM := (native_YM_curvature_identification hn' hL4 hF' μ ν).1
    have hlin : LpTendsto volume 2 (fun k => pc (fun x => linCurl (A (φ k)) x μ ν))
        (fun y => G μ ν y - G ν μ y) :=
      ((hG μ ν).sub (hG ν μ)).congr (fun k => Eventually.of_forall fun y => rfl)
        (Eventually.of_forall fun y => rfl)
    have := hYM.ae_eq_of_lpTendsto hlin
    filter_upwards [this] with y hy
    rw [← hy]; abel
  · -- `δA = 0`
    have hμ : ∀ μ, LpTendsto volume 2 (fun k => pc (DmV μ (fun x => A (φ k) x μ))) (G μ μ) := by
      intro μ
      refine ((hG μ μ).shift_neg hn' (by norm_num) μ).congr
        (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => rfl)
      simp only [pc]; rw [DmV_eq_DpV_shift]
    have hsum : LpTendsto volume 2 (fun k => pc (fun x => ∑ μ, DmV μ (fun y => A (φ k) y μ) x))
        (fun y => ∑ μ, G μ μ y) := by
      have := ((hμ 0).add (hμ 1)).add ((hμ 2).add (hμ 3))
      refine this.congr (fun k => Eventually.of_forall fun y => ?_)
        (Eventually.of_forall fun y => ?_)
      · simp only [Pi.add_apply, pc, Fin.sum_univ_four]; abel
      · simp only [Pi.add_apply, Fin.sum_univ_four]; abel
    have hz : (fun k => pc (fun x => ∑ μ, DmV μ (fun y => A (φ k) y μ) x)) =
        fun _ => (0 : UnitAddTorus (Fin 4) → 𝔸) := by
      funext k y
      exact sum_DmV_eq_zero T hc (A (φ k)) (hδ (φ k)) _
    rw [hz] at hsum
    exact hsum.ae_eq_of_lpTendsto (LpTendsto.const MemLp.zero)

end Main

/-! ### Non-vacuity -/

section NonVacuity

/-- Non-vacuity of `native_discrete_Coulomb`: in `𝔸 = ℂ` (read in `E = ℂ` by the identity), the
zero connections on the grids `N = k + 1` satisfy all its hypotheses. -/
example : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ A₀ : Fin 4 → UnitAddTorus (Fin 4) → ℂ,
    ∀ μ, LpTendsto volume 4 (fun k => pc (fun _ : LatticeTorusPlancherel.Grid 4 (φ k + 1) =>
      (0 : ℂ))) (A₀ μ) := by
  obtain ⟨ε, hε, h⟩ := native_discrete_Coulomb (𝔸 := ℂ) (E := ℂ) (ContinuousLinearMap.id ℝ ℂ)
    zero_le_one (fun X => by simp)
  have hF : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      curvLog (k + 1) (fun _ _ => (0 : ℂ)) x μ ν)) (fun _ => (0 : ℂ)) := by
    intro μ ν
    have e : (fun k => pc (fun x => curvLog (k + 1) (fun _ _ => (0 : ℂ)) x μ ν)) =
        fun _ => (0 : UnitAddTorus (Fin 4) → ℂ) := by
      funext k y
      exact curvLog_zero' (𝔸 := ℂ) (N := k + 1) _ μ ν
    rw [e]
    exact LpTendsto.const MemLp.zero
  obtain ⟨φ, hφ, A₀, G, h1, -⟩ := h (fun k => k + 1) (tendsto_add_atTop_nat 1)
    (fun k _ _ => 0) (fun _ _ _ => 0) (fun k => codiffT_zero _)
    (fun k μ => by rw [show (fun x : LatticeTorusPlancherel.Grid 4 (k + 1) =>
      (ContinuousLinearMap.id ℝ ℂ) ((fun _ _ => (0 : ℂ)) x μ)) = fun _ => (0 : ℂ) by
        funext x; simp, g4_zero]; exact hε.le) hF
  exact ⟨φ, hφ, A₀, h1⟩

end NonVacuity

end

end RenewalGeometry.NativeCoulomb
