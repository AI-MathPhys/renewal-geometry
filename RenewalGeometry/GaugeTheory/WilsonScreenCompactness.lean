/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.LocalKolmogorovRieszTorus
import RenewalGeometry.Continuum.CompactMagnitudeUniformIntegrabilityExact
import RenewalGeometry.GaugeTheory.TranslationKatoInequalityExact
import RenewalGeometry.GaugeTheory.WilsonTransportConsistency

/-!
# Covariant screen compactness at the critical endpoint (`prop:Wilson-screen-compactness`)

Einstein–SM action-closure manuscript, "Finite Wilson packets and continuum covariant
translations", `prop:Wilson-screen-compactness`: "Let `Y_h` be bounded in `L²(B)` and satisfy
`eq:Wilson-continuum-screen`.  Then `|Y_h|` is relatively compact in `L²_loc` and `|Y_h|²` is
uniformly integrable locally.  If, in addition, after local gauge normalization
`sup_h ‖A_h‖_{L⁴(B)} ≤ M_A`, then `Y_h` itself is precompact in `L²_loc(B)`."

## Rendering

* The chart `B` is an open subset of the periodic comparison box, rendered (as for
  `thm:native-Wilson-compactness`) as the unit torus `𝕋^d = UnitAddTorus d` with its Haar
  probability measure; coordinate displacements are `t ↦ t + coordPt μ s`.
* The fibre `F` is a finite-dimensional real normed space (complex fibres are included); the
  represented transports `ρ(P^{A_h}_{μ,s}(t))` are linear isometries (unitary representation).
* `eq:Wilson-continuum-screen` is used on every compact `K ⊆ B` and for positive displacements
  `0 ≤ s ≤ δ` only, cofinitely in the family index (the `limsup_{h↓0}` form); this is implied by
  the manuscript's hypothesis.
* "Relatively compact in `L²_loc(B)`" is rendered as: on every compact `K ⊆ B`, for every `ε`, a
  finite `ε`-net in `L²(K)` drawn from the family (`…_nets`), equivalently total boundedness of
  the `L²(K)` classes (`LocalKRTorus.totallyBounded_of_nets`).
* For the vector part, `ρ(P_{μ,s}(t))` is the inverse of the forward parallel transport of the
  represented reconstructed connection `a = ρ(A_μ)` along the line, which is unitary, and the
  connection is continuous with `sup_h ‖a_h‖_{L⁴(B)} ≤ M_A`.

## Main results

* `wilson_screen_magnitude_nets`: `|Y_h|` relatively compact in `L²_loc(B)` (translation Kato
  `translation_kato_of_isometry` + local Kolmogorov–Riesz).
* `wilson_screen_magnitude_ui`: `|Y_h|²` uniformly integrable on every compact `K ⊆ B`
  (`lem:compact-magnitude-ui`, `compactMagnitude_ui`).
* `norm_inverse_transport_sub_one_le` (**`eq:short-line-integral`**):
  `‖ρ(P_{μ,s}(t)) - I‖ ≤ ∫_0^s |a(t + τe_μ)| dτ` for unitary transports (and `≤ 2` always).
* `wilson_screen_vector_nets`: under the `L⁴` connection bound, `Y_h` itself is relatively
  compact in `L²_loc(B)` (`eq:short-transport-harmless` via Chebyshev and uniform integrability).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.WilsonScreen

open LocalKRTorus KolmogorovRieszTorus PathOrderedExp

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The continuum covariant translation `𝒯_{μ,s}Y(t) = ρ(P_{μ,s}(t)) Y(t + s e_μ)`
(`eq:continuum-covariant-translation`). -/
def covTransl (P : d → ℝ → UnitAddTorus d → F →L[ℝ] F) (Y : UnitAddTorus d → F) (μ : d)
    (s : ℝ) (t : UnitAddTorus d) : F :=
  P μ s t (Y (t + coordPt μ s))

/-- The covariant screen `eq:Wilson-continuum-screen` on the chart `B` (every compact `K ⊆ B`,
positive displacements, cofinitely in the index). -/
def CovScreen {α : Type*} (P : α → d → ℝ → UnitAddTorus d → F →L[ℝ] F)
    (Y : α → UnitAddTorus d → F) (B : Set (UnitAddTorus d)) : Prop :=
  ∀ K, IsCompact K → K ⊆ B → ∀ ε > 0, ∃ δ > 0, ∃ T : Set α, T.Finite ∧ ∀ i ∉ T, ∀ μ,
    ∀ s ∈ Icc (0 : ℝ) δ,
      eLpNorm (fun t => covTransl (P i) (Y i) μ s t - Y i t) 2 (volume.restrict K) ≤
        ENNReal.ofReal ε

/-! ### The scalar assertion -/

/-- **`prop:Wilson-screen-compactness`, scalar assertion (compactness).**  If `Y_h` is bounded in
`L²(B)`, the transports are unitary and the covariant screen holds on `B`, then the magnitudes
`|Y_h|` are relatively compact in `L²_loc(B)`: on every compact `K ⊆ B` they have finite `ε`-nets
in `L²(K)` drawn from the family. -/
theorem wilson_screen_magnitude_nets {α : Type*} (P : α → d → ℝ → UnitAddTorus d → F →L[ℝ] F)
    (Y : α → UnitAddTorus d → F) {B : Set (UnitAddTorus d)} (hB : IsOpen B)
    (hiso : ∀ i μ s t (v : F), 0 ≤ s → ‖P i μ s t v‖ = ‖v‖)
    (hmeas : ∀ i, AEStronglyMeasurable (Y i) volume) (M : ℝ)
    (hbdd : ∀ i, eLpNorm (Y i) 2 (volume.restrict B) ≤ ENNReal.ofReal M)
    (hscr : CovScreen P Y B) {K : Set (UnitAddTorus d)} (hK : IsCompact K) (hKB : K ⊆ B) :
    ∀ ε > 0, ∃ J : Finset α, ∀ i, ∃ j ∈ J,
      eLpNorm (fun t => ‖Y i t‖ - ‖Y j t‖) 2 (volume.restrict K) ≤ ENNReal.ofReal ε :=
  exists_net_of_local_modulus (V := ℝ) (fun i t => ‖Y i t‖) hB (fun i => (hmeas i).norm) M
    (fun i => by rw [eLpNorm_norm]; exact hbdd i)
    (fun K' hK' hK'B ε hε => by
      obtain ⟨δ, hδ, T, hT, h⟩ := hscr K' hK' hK'B ε hε
      refine ⟨δ, hδ, T, hT, fun i hi μ s hs => ((eLpNorm_mono fun t => ?_).trans
        (h i hi μ s hs))⟩
      rw [Real.norm_eq_abs]
      exact translation_kato_of_isometry (P i μ s t) (fun v => hiso i μ s t v hs.1) _ _) hK hKB

/-- From an energy bound to an `L²` bound: `∫⁻_E ‖f‖² ≤ ε²` gives `‖f‖_{L²(E)} ≤ ε`. -/
theorem eLpNorm_restrict_le_of_lintegral {X : Type*} [MeasurableSpace X] {μ' : Measure X}
    {f : X → F} {E : Set X} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∫⁻ x in E, ‖f x‖ₑ ^ 2 ∂μ' ≤ ENNReal.ofReal (ε ^ 2)) :
    eLpNorm f 2 (μ'.restrict E) ≤ ENNReal.ofReal ε := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have h' : ∫⁻ x in E, ‖f x‖ₑ ^ (2 : ℝ) ∂μ' ≤ ENNReal.ofReal (ε ^ 2) := by
    simpa only [ENNReal.rpow_two] using h
  calc (∫⁻ x in E, ‖f x‖ₑ ^ (2 : ℝ) ∂μ') ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (ε ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h' (by norm_num)
    _ = ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 1
        rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast hε (by norm_num)

/-- **`prop:Wilson-screen-compactness`, scalar assertion (uniform integrability).**  Under the
hypotheses of `wilson_screen_magnitude_nets`, `|Y_h|²` is uniformly integrable on every compact
`K ⊆ B`: for every `ε > 0` there is `δ > 0` with `‖Y_h‖_{L²(E)} ≤ ε` for all `h` and all
measurable `E ⊆ K` with `|E| ≤ δ` (equivalently `∫_E |Y_h|² ≤ ε²`). -/
theorem wilson_screen_magnitude_ui {α : Type*} (P : α → d → ℝ → UnitAddTorus d → F →L[ℝ] F)
    (Y : α → UnitAddTorus d → F) {B : Set (UnitAddTorus d)} (hB : IsOpen B)
    (hiso : ∀ i μ s t (v : F), 0 ≤ s → ‖P i μ s t v‖ = ‖v‖)
    (hmeas : ∀ i, AEStronglyMeasurable (Y i) volume) (M : ℝ)
    (hbdd : ∀ i, eLpNorm (Y i) 2 (volume.restrict B) ≤ ENNReal.ofReal M)
    (hscr : CovScreen P Y B) {K : Set (UnitAddTorus d)} (hK : IsCompact K) (hKB : K ⊆ B) :
    ∀ ε > 0, ∃ δ > 0, ∀ i (E : Set (UnitAddTorus d)), MeasurableSet E → E ⊆ K →
      volume E ≤ ENNReal.ofReal δ → eLpNorm (Y i) 2 (volume.restrict E) ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hmem : ∀ i, MemLp (fun t => ‖Y i t‖) 2 (volume.restrict K) := fun i =>
    memLp_restrict_of_le (hmeas i).norm hKB (by rw [eLpNorm_norm]; exact hbdd i)
  have hTB := totallyBounded_of_nets (fun i t => ‖Y i t‖) hmem
    (wilson_screen_magnitude_nets P Y hB hiso hmeas M hbdd hscr hK hKB)
  have hUI := (criticalCurvatureUI_iff volume K _).1 (compactMagnitude_ui volume K _ hTB)
  obtain ⟨δ, hδ, h⟩ := hUI (ENNReal.ofReal (ε ^ 2)) (by positivity)
  refine ⟨δ, hδ, fun i E hE hEK hvol => eLpNorm_restrict_le_of_lintegral hε.le ?_⟩
  refine le_of_eq_of_le ?_ (h i E hE hEK hvol)
  refine setLIntegral_congr_fun_ae hE ?_
  have hae : ∀ᵐ t ∂(volume.restrict E), (hmem i).toLp _ t = ‖Y i t‖ :=
    ae_restrict_of_ae_restrict_of_subset hEK (hmem i).coeFn_toLp
  filter_upwards [(ae_restrict_iff' hE).1 hae] with t ht htE
  rw [ht htE, Real.enorm_of_nonneg (norm_nonneg _), ofReal_norm_eq_enorm]

/-! ### The short line integral -/

section ShortLine

variable [Nontrivial F] [CompleteSpace F]

/-- **`eq:short-line-integral`** for a unitary transport: if `Q` is the transport of a continuous
coefficient `ω` on `[0,s]` with `Q(0) = 1` and `‖Q(τ)‖ ≤ 1`, then
`‖Q(s) - 1‖ ≤ ∫_0^s ‖ω‖`; if moreover `P Q(s) = 1` with `‖P‖ ≤ 1`, then
`‖P - 1‖ ≤ ∫_0^s ‖ω‖`. -/
theorem norm_inverse_transport_sub_one_le {ω : ℝ → F →L[ℝ] F} {s : ℝ} (hs : 0 ≤ s)
    (hω : ContinuousOn ω (Icc 0 s)) {Q : ℝ → F →L[ℝ] F} (hQ : IsTransport ω 0 s Q) (hQ0 : Q 0 = 1)
    (hQn : ∀ τ ∈ Icc 0 s, ‖Q τ‖ ≤ 1) {P : F →L[ℝ] F} (hP : ‖P‖ ≤ 1) (hPQ : P * Q s = 1) :
    ‖P - 1‖ ≤ ∫ τ in (0 : ℝ)..s, ‖ω τ‖ := by
  have hint := transport_integral_eq hω hQ ⟨hs, le_rfl⟩
  rw [hQ0] at hint
  have hQs : ‖Q s - 1‖ ≤ ∫ τ in (0 : ℝ)..s, ‖ω τ‖ := by
    rw [hint, sub_sub_cancel_left, norm_neg]
    refine intervalIntegral.norm_integral_le_of_norm_le hs (Eventually.of_forall fun τ hτ => ?_)
      ((hω.norm).intervalIntegrable_of_Icc hs)
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
      (hQn τ ⟨hτ.1.le, hτ.2⟩))
  have e : P - 1 = P * (1 - Q s) := by rw [mul_sub, mul_one, hPQ]
  rw [e]
  refine (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hP).trans ?_)
  rw [norm_sub_rev]; exact hQs

theorem opNorm_le_one_of_isometry {P : F →L[ℝ] F} (hP : ∀ v, ‖P v‖ = ‖v‖) : ‖P‖ ≤ 1 :=
  P.opNorm_le_bound zero_le_one fun v => by rw [hP, one_mul]

end ShortLine

/-! ### Translations of restricted norms -/

theorem continuous_coordPt (μ : d) : Continuous fun τ : ℝ => coordPt μ τ := by
  refine continuous_pi fun i => ?_
  by_cases hi : i = μ
  · subst hi
    simp only [coordPt, Pi.single_eq_same]
    exact AddCircle.continuous_mk' 1
  · simp only [coordPt, Pi.single_apply, hi, if_false]
    exact continuous_const

/-- The translated set `S + y = {t | t - y ∈ S}`. -/
def shiftSet (S : Set (UnitAddTorus d)) (y : UnitAddTorus d) : Set (UnitAddTorus d) :=
  (fun t => t - y) ⁻¹' S

theorem measurableSet_shiftSet {S : Set (UnitAddTorus d)} (hS : MeasurableSet S)
    (y : UnitAddTorus d) : MeasurableSet (shiftSet S y) :=
  (continuous_id.sub continuous_const).measurable hS

theorem volume_shiftSet {S : Set (UnitAddTorus d)} (hS : MeasurableSet S) (y : UnitAddTorus d) :
    volume (shiftSet S y) = volume S :=
  (measurePreserving_sub_right volume y).measure_preimage hS.nullMeasurableSet

theorem shiftSet_subset_cthickening {S K : Set (UnitAddTorus d)} (hSK : S ⊆ K) {y : UnitAddTorus d}
    {r : ℝ} (hy : ‖y‖ ≤ r) : shiftSet S y ⊆ cthickening r K := by
  intro t ht
  exact mem_cthickening_of_dist_le t (t - y) r K (hSK ht)
    (by rw [dist_eq_norm, sub_sub_cancel]; exact hy)

/-- Translation of a restricted `L²` norm: `‖g(· + y)‖_{L²(S)} = ‖g‖_{L²(S + y)}`. -/
theorem eLpNorm_comp_add_restrict {g : UnitAddTorus d → F} (hg : AEStronglyMeasurable g volume)
    {S : Set (UnitAddTorus d)} (hS : MeasurableSet S) (y : UnitAddTorus d) (p : ℝ≥0∞) :
    eLpNorm (fun t => g (t + y)) p (volume.restrict S) =
      eLpNorm g p (volume.restrict (shiftSet S y)) := by
  have hmp := (measurePreserving_add_right (volume : Measure (UnitAddTorus d)) y).restrict_preimage
    (measurableSet_shiftSet hS y)
  have e : (fun t => t + y) ⁻¹' shiftSet S y = S := by
    ext t; simp [shiftSet]
  rw [e] at hmp
  exact eLpNorm_comp_measurePreserving hg.restrict hmp

/-- Translation of a restricted lower integral. -/
theorem setLIntegral_comp_add (g : UnitAddTorus d → ℝ≥0∞) {S : Set (UnitAddTorus d)}
    (hS : MeasurableSet S) (y : UnitAddTorus d) :
    ∫⁻ t in S, g (t + y) = ∫⁻ t in shiftSet S y, g t := by
  have hmp := (measurePreserving_add_right (volume : Measure (UnitAddTorus d)) y).restrict_preimage
    (measurableSet_shiftSet hS y)
  have e : (fun t => t + y) ⁻¹' shiftSet S y = S := by
    ext t; simp [shiftSet]
  rw [e] at hmp
  exact hmp.lintegral_comp_emb (measurableEmbedding_addRight y) g

/-! ### Continuity of transports in the base point -/

section Transports

variable [Nontrivial F] [CompleteSpace F]

/-- The transport data of the vector part: `ρ(P_{μ,s}(t))` is the two-sided inverse of the forward
parallel transport `Q` of the represented connection `a_μ` along `τ ↦ t + τe_μ`, `Q` unitary. -/
def IsUnitaryTransport (a : UnitAddTorus d → F →L[ℝ] F) (μ : d) (s : ℝ) (t : UnitAddTorus d)
    (P : F →L[ℝ] F) : Prop :=
  ∃ Q : ℝ → F →L[ℝ] F, Q 0 = 1 ∧ IsTransport (fun τ => a (t + coordPt μ τ)) 0 s Q ∧
    (∀ τ ∈ Icc (0 : ℝ) s, ∀ v, ‖Q τ v‖ = ‖v‖) ∧ P * Q s = 1 ∧ Q s * P = 1

theorem IsUnitaryTransport.norm_apply {a : UnitAddTorus d → F →L[ℝ] F} {μ : d} {s : ℝ}
    (hs : 0 ≤ s) {t : UnitAddTorus d} {P : F →L[ℝ] F} (h : IsUnitaryTransport a μ s t P) (v : F) :
    ‖P v‖ = ‖v‖ := by
  obtain ⟨Q, -, -, hQi, -, hQP⟩ := h
  have := hQi s ⟨hs, le_rfl⟩ (P v)
  rw [← ContinuousLinearMap.mul_apply, hQP, ContinuousLinearMap.one_apply] at this
  exact this.symm


/-- **`eq:short-line-integral`** for the unitary transports of the vector part:
`‖ρ(P_{μ,s}(t)) - I‖ ≤ ∫_0^s ‖a(t + τe_μ)‖ dτ`. -/
theorem IsUnitaryTransport.norm_sub_one_le {a : UnitAddTorus d → F →L[ℝ] F} (ha : Continuous a)
    {μ : d} {s : ℝ} (hs : 0 ≤ s) {t : UnitAddTorus d} {P : F →L[ℝ] F}
    (h : IsUnitaryTransport a μ s t P) :
    ‖P - 1‖ ≤ ∫ τ in (0 : ℝ)..s, ‖a (t + coordPt μ τ)‖ := by
  have hPn : ‖P‖ ≤ 1 := opNorm_le_one_of_isometry (h.norm_apply hs)
  obtain ⟨Q, hQ0, hQ, hQi, hPQ, -⟩ := h
  exact norm_inverse_transport_sub_one_le hs
    ((ha.comp (continuous_const.add (continuous_coordPt μ))).continuousOn) hQ hQ0
    (fun τ hτ => opNorm_le_one_of_isometry (hQi τ hτ)) hPn hPQ

/-- `‖ρ(P) - I‖ ≤ 2` for a unitary transport. -/
theorem IsUnitaryTransport.norm_sub_one_le_two {a : UnitAddTorus d → F →L[ℝ] F} {μ : d} {s : ℝ}
    (hs : 0 ≤ s) {t : UnitAddTorus d} {P : F →L[ℝ] F} (h : IsUnitaryTransport a μ s t P) :
    ‖P - 1‖ ≤ 2 := by
  have hPn : ‖P‖ ≤ 1 := opNorm_le_one_of_isometry (h.norm_apply hs)
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]; linarith

/-- **Continuity of the transports in the base point**: unitary transports of a continuous
connection on the compact torus depend continuously on the base point. -/
theorem continuous_of_isUnitaryTransport {a : UnitAddTorus d → F →L[ℝ] F} (ha : Continuous a)
    {μ : d} {s : ℝ} (hs : 0 ≤ s) {P : UnitAddTorus d → F →L[ℝ] F}
    (hP : ∀ t, IsUnitaryTransport a μ s t (P t)) : Continuous P := by
  obtain ⟨K, hK⟩ : ∃ K, ∀ t, ‖a t‖ ≤ K := by
    obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
    exact ⟨K, fun t => hK t (mem_univ t)⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have huc := CompactSpace.uniformContinuous_of_continuous ha
  rw [Metric.continuous_iff]
  intro t ε hε
  set C := s * Real.exp (2 * K * s) + 1
  have hC : 0 < C := by positivity
  obtain ⟨η, hη, hηc⟩ := Metric.uniformContinuous_iff.1 huc (ε / C) (by positivity)
  refine ⟨η, hη, fun t' ht' => ?_⟩
  have hPn : ‖P t‖ ≤ 1 := opNorm_le_one_of_isometry ((hP t).norm_apply hs)
  have hPn' : ‖P t'‖ ≤ 1 := opNorm_le_one_of_isometry ((hP t').norm_apply hs)
  obtain ⟨Q, hQ0, hQ, -, -, hQP⟩ := hP t
  obtain ⟨Q', hQ0', hQ', -, hPQ', -⟩ := hP t'
  have hδ : ∀ τ ∈ Icc (0 : ℝ) s, ‖a (t' + coordPt μ τ) - a (t + coordPt μ τ)‖ ≤ ε / C := by
    intro τ _
    have := @hηc (t' + coordPt μ τ) (t + coordPt μ τ) (by rw [dist_add_right]; exact ht')
    rw [dist_eq_norm] at this
    exact this.le
  have hdiff := norm_transport_sub_transport_le (K := K) (fun _ _ => hK _) (fun _ _ => hK _) hδ hQ'
    hQ (by rw [hQ0, hQ0']) s ⟨hs, le_rfl⟩
  rw [hQ0', norm_one, one_mul, sub_zero] at hdiff
  have hgr := WilsonTransport.gronwallBound_zero_le (ε := ε / C * Real.exp (K * s)) hK0
    (by positivity) hs
  have hQQ : ‖Q' s - Q s‖ ≤ ε / C * (s * Real.exp (2 * K * s)) := by
    refine hdiff.trans (hgr.trans (le_of_eq ?_))
    rw [show 2 * K * s = K * s + K * s by ring, Real.exp_add]; ring
  have e : P t' - P t = P t' * (Q s - Q' s) * P t := by
    calc P t' - P t = P t' * (Q s * P t) - (P t' * Q' s) * P t := by rw [hQP, hPQ', mul_one, one_mul]
      _ = P t' * (Q s - Q' s) * P t := by noncomm_ring
  rw [dist_eq_norm, e]
  calc ‖P t' * (Q s - Q' s) * P t‖ ≤ ‖P t'‖ * ‖Q s - Q' s‖ * ‖P t‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * (ε / C * (s * Real.exp (2 * K * s))) * 1 := by
        rw [norm_sub_rev] at hQQ; gcongr
    _ < ε := by
        rw [one_mul, mul_one, div_mul_eq_mul_div, div_lt_iff₀ hC]
        nlinarith

end Transports

/-! ### Line integrals of the connection: Fubini and Chebyshev -/

section LineIntegral

/-- The (extended) short line integral `L_s(t) = ∫_0^s ‖a(t + τe_μ)‖ dτ`. -/
def lineInt {G : Type*} [NormedAddCommGroup G] (a : UnitAddTorus d → G) (μ : d) (s : ℝ)
    (t : UnitAddTorus d) : ℝ≥0∞ :=
  ∫⁻ τ in Icc (0 : ℝ) s, ‖a (t + coordPt μ τ)‖ₑ

variable {G : Type*} [NormedAddCommGroup G]

theorem measurable_uncurry_line {a : UnitAddTorus d → G} (ha : Continuous a) (μ : d) :
    Measurable fun p : UnitAddTorus d × ℝ => ‖a (p.1 + coordPt μ p.2)‖ₑ :=
  (ha.comp (continuous_fst.add ((continuous_coordPt μ).comp continuous_snd))).enorm.measurable

theorem measurable_lineInt {a : UnitAddTorus d → G} (ha : Continuous a) (μ : d) (s : ℝ) :
    Measurable (lineInt a μ s) :=
  (measurable_uncurry_line ha μ).lintegral_prod_right'

theorem ofReal_intervalIntegral_eq_lineInt {a : UnitAddTorus d → G} (ha : Continuous a) (μ : d)
    {s : ℝ} (hs : 0 ≤ s) (t : UnitAddTorus d) :
    ENNReal.ofReal (∫ τ in (0 : ℝ)..s, ‖a (t + coordPt μ τ)‖) = lineInt a μ s t := by
  have hc : Continuous fun τ : ℝ => ‖a (t + coordPt μ τ)‖ :=
    (ha.comp (continuous_const.add (continuous_coordPt μ))).norm
  rw [intervalIntegral.integral_of_le hs, ofReal_integral_eq_lintegral_ofReal
    ((hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self) (Eventually.of_forall fun _ => norm_nonneg _),
    lineInt, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  simp only [ofReal_norm_eq_enorm]

/-- **Fubini for the short line integral**: if every translate `K' + τe_μ` (`0 ≤ τ ≤ s`) lies in
`K''`, then `∫_{K'} L_s ≤ s ∫_{K''} ‖a‖`. -/
theorem setLIntegral_lineInt_le {a : UnitAddTorus d → G} (ha : Continuous a) (μ : d) {s r : ℝ}
    (hs : 0 ≤ s) (hsr : s ≤ r) {K' : Set (UnitAddTorus d)} (hK' : MeasurableSet K') :
    ∫⁻ t in K', lineInt a μ s t ≤
      ENNReal.ofReal s * ∫⁻ t in cthickening r K', ‖a t‖ₑ := by
  unfold lineInt
  rw [lintegral_lintegral_swap ((measurable_uncurry_line ha μ).aemeasurable)]
  calc ∫⁻ τ in Icc (0 : ℝ) s, ∫⁻ t in K', ‖a (t + coordPt μ τ)‖ₑ
      ≤ ∫⁻ τ in Icc (0 : ℝ) s, ∫⁻ t in cthickening r K', ‖a t‖ₑ := by
        refine setLIntegral_mono' measurableSet_Icc fun τ hτ => ?_
        rw [setLIntegral_comp_add (fun t => ‖a t‖ₑ) hK' (coordPt μ τ)]
        refine lintegral_mono_set (shiftSet_subset_cthickening subset_rfl ?_)
        have := dist_add_coordPt_le 0 μ τ
        rw [zero_add, dist_zero_right, abs_of_nonneg hτ.1] at this
        linarith [hτ.2]
    _ = ENNReal.ofReal s * ∫⁻ t in cthickening r K', ‖a t‖ₑ := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]

/-- `∫_{K''} ‖a‖ ≤ ‖a‖_{L⁴(B)}` for `K'' ⊆ B` (the torus has total mass one). -/
theorem setLIntegral_enorm_le_eLpNorm_four {a : UnitAddTorus d → G}
    (ha : AEStronglyMeasurable a volume) {K'' B : Set (UnitAddTorus d)} (hKB : K'' ⊆ B) :
    ∫⁻ t in K'', ‖a t‖ₑ ≤ eLpNorm a 4 (volume.restrict B) := by
  rw [← eLpNorm_one_eq_lintegral_enorm]
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 4) (by norm_num)
    ha.restrict).trans ?_
  have hvol : (volume.restrict K'') univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (4 : ℝ≥0∞).toReal) ≤ 1 := by
    refine ENNReal.rpow_le_one ?_ (by norm_num)
    rw [Measure.restrict_apply_univ]; exact prob_le_one
  calc eLpNorm a 4 (volume.restrict K'') *
        (volume.restrict K'') univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (4 : ℝ≥0∞).toReal)
      ≤ eLpNorm a 4 (volume.restrict K'') * 1 := by gcongr
    _ ≤ eLpNorm a 4 (volume.restrict B) := by
        rw [mul_one]; exact eLpNorm_mono_measure _ (Measure.restrict_mono hKB le_rfl)

/-- **Chebyshev for the exceptional set** `{L_s > δ}`. -/
theorem volume_lineInt_gt_inter_le {a : UnitAddTorus d → G} (ha : Continuous a) (μ : d) (s : ℝ)
    {δ : ℝ} (hδ : 0 < δ) {K' : Set (UnitAddTorus d)} (hK' : MeasurableSet K') :
    volume ({t | ENNReal.ofReal δ < lineInt a μ s t} ∩ K') ≤
      (∫⁻ t in K', lineInt a μ s t) / ENNReal.ofReal δ := by
  have hE : MeasurableSet {t | ENNReal.ofReal δ < lineInt a μ s t} :=
    measurableSet_lt measurable_const (measurable_lineInt ha μ s)
  rw [← Measure.restrict_apply hE]
  refine (measure_mono fun t ht => le_of_lt (show ENNReal.ofReal δ < lineInt a μ s t from ht)).trans
    (meas_ge_le_lintegral_div (measurable_lineInt ha μ s).aemeasurable
      (by simpa using hδ) ENNReal.ofReal_ne_top)

end LineIntegral

/-! ### The vector assertion -/

/-- **`prop:Wilson-screen-compactness`, vector assertion.**  In addition to the hypotheses of the
scalar assertion, let the transports be the unitary parallel transports of continuous represented
connections `a_h` (`IsUnitaryTransport`) with `sup_h ‖a_h‖_{L⁴(B)} ≤ M_A`
(`eq:critical-A4-bound`).  Then `Y_h` itself is relatively compact in `L²_loc(B)`: on every
compact `K ⊆ B` it has finite `ε`-nets in `L²(K)` drawn from the family.  Proof as in the
manuscript: `eq:short-line-integral`, Chebyshev on `{L_s > δ}` (whose measure is `O(s M_A/δ)`),
the uniform integrability of `|Y_h|²` on the exceptional set, the covariant screen, and local
Kolmogorov–Riesz. -/
theorem wilson_screen_vector_nets [FiniteDimensional ℝ F] [Nontrivial F] {α : Type*}
    (P : α → d → ℝ → UnitAddTorus d → F →L[ℝ] F) (Y : α → UnitAddTorus d → F)
    (a : α → d → UnitAddTorus d → F →L[ℝ] F) {B : Set (UnitAddTorus d)} (hB : IsOpen B)
    (hmeas : ∀ i, AEStronglyMeasurable (Y i) volume) (M : ℝ)
    (hbdd : ∀ i, eLpNorm (Y i) 2 (volume.restrict B) ≤ ENNReal.ofReal M)
    (hscr : CovScreen P Y B) (ha : ∀ i μ, Continuous (a i μ)) (MA : ℝ)
    (hA : ∀ i μ, eLpNorm (a i μ) 4 (volume.restrict B) ≤ ENNReal.ofReal MA)
    (htr : ∀ i μ s t, 0 ≤ s → IsUnitaryTransport (a i μ) μ s t (P i μ s t))
    {K : Set (UnitAddTorus d)} (hK : IsCompact K) (hKB : K ⊆ B) :
    ∀ ε > 0, ∃ J : Finset α, ∀ i, ∃ j ∈ J,
      eLpNorm (fun t => Y i t - Y j t) 2 (volume.restrict K) ≤ ENNReal.ofReal ε := by
  have hiso : ∀ i μ s t (v : F), 0 ≤ s → ‖P i μ s t v‖ = ‖v‖ := fun i μ s t v hs =>
    (htr i μ s t hs).norm_apply hs v
  refine exists_net_of_local_modulus Y hB hmeas M hbdd ?_ hK hKB
  intro K' hK'c hK'B ε hε
  have hK'm : MeasurableSet K' := hK'c.isClosed.measurableSet
  obtain ⟨r, hr, hrB⟩ := hK'c.exists_cthickening_subset_open hB hK'B
  set K'' := cthickening r K'
  have hK''c : IsCompact K'' := isClosed_cthickening.isCompact
  have hK''m : MeasurableSet K'' := isClosed_cthickening.measurableSet
  set Mp := max M 0
  set MAp := max MA 0
  have hMp : 0 ≤ Mp := le_max_right _ _
  have hMAp : 0 ≤ MAp := le_max_right _ _
  set δL := ε / (4 * (Mp + 1))
  have hδL : 0 < δL := by positivity
  obtain ⟨δU, hδU, hUI⟩ := wilson_screen_magnitude_ui P Y hB hiso hmeas M hbdd hscr hK''c hrB
    (ε / 4) (by positivity)
  obtain ⟨δc, hδc, T, hT, hscrK'⟩ := hscr K' hK'c hK'B (ε / 4) (by positivity)
  refine ⟨min (min r δc) (δU * δL / (MAp + 1)), by positivity, T, hT, fun i hi μ s hs => ?_⟩
  have hs0 : 0 ≤ s := hs.1
  have hsr : s ≤ r := hs.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hsc : s ≤ δc := hs.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsU : s ≤ δU * δL / (MAp + 1) := hs.2.trans (min_le_right _ _)
  set y := coordPt μ s
  have hy : ‖y‖ ≤ r := by
    have := dist_add_coordPt_le 0 μ s
    rw [zero_add, dist_zero_right, abs_of_nonneg hs0] at this
    linarith
  set E := {t | ENNReal.ofReal δL < lineInt (a i μ) μ s t}
  have hEm : MeasurableSet E := measurableSet_lt measurable_const (measurable_lineInt (ha i μ) μ s)
  have hPc : Continuous (P i μ s) :=
    continuous_of_isUnitaryTransport (ha i μ) hs0 fun t => htr i μ s t hs0
  have hYy : AEStronglyMeasurable (fun t => Y i (t + y)) volume :=
    (hmeas i).comp_measurePreserving (measurePreserving_add_right volume y)
  have hcov : AEStronglyMeasurable (fun t => covTransl (P i) (Y i) μ s t - Y i t) volume := by
    have : AEStronglyMeasurable (fun t => P i μ s t (Y i (t + y))) volume :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hPc.aestronglyMeasurable.prodMk hYy)
    exact this.sub (hmeas i)
  -- the pointwise decomposition
  have hpt : ∀ t, ‖Y i (t + y) - Y i t‖ ≤ ‖covTransl (P i) (Y i) μ s t - Y i t‖ +
      δL * ‖Y i (t + y)‖ + E.indicator (fun t => 2 * ‖Y i (t + y)‖) t := by
    intro t
    have e : Y i (t + y) - Y i t = (covTransl (P i) (Y i) μ s t - Y i t) -
        (P i μ s t - 1) (Y i (t + y)) := by
      simp only [covTransl, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
      abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have hop := ((P i μ s t - 1).le_opNorm (Y i (t + y)))
    by_cases ht : t ∈ E
    · rw [indicator_of_mem ht]
      have h2 := (htr i μ s t hs0).norm_sub_one_le_two hs0
      have : ‖(P i μ s t - 1) (Y i (t + y))‖ ≤ 2 * ‖Y i (t + y)‖ :=
        hop.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
      nlinarith [norm_nonneg (Y i (t + y)), hδL]
    · rw [indicator_of_notMem ht, add_zero]
      have hL : lineInt (a i μ) μ s t ≤ ENNReal.ofReal δL := not_lt.1 ht
      rw [← ofReal_intervalIntegral_eq_lineInt (ha i μ) μ hs0 t,
        ENNReal.ofReal_le_ofReal_iff hδL.le] at hL
      have h1 := ((htr i μ s t hs0).norm_sub_one_le (ha i μ) hs0).trans hL
      have : ‖(P i μ s t - 1) (Y i (t + y))‖ ≤ δL * ‖Y i (t + y)‖ :=
        hop.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
      linarith
  have hg2 : AEStronglyMeasurable (fun t => δL * ‖Y i (t + y)‖) volume :=
    aestronglyMeasurable_const.mul hYy.norm
  have hg3 : AEStronglyMeasurable (E.indicator fun t => 2 * ‖Y i (t + y)‖) volume :=
    (aestronglyMeasurable_const.mul hYy.norm).indicator hEm
  -- the three bounds
  have b1 : eLpNorm (fun t => ‖covTransl (P i) (Y i) μ s t - Y i t‖) 2 (volume.restrict K') ≤
      ENNReal.ofReal (ε / 4) := by
    rw [eLpNorm_norm]; exact hscrK' i hi μ s ⟨hs0, hsc⟩
  have b2 : eLpNorm (fun t => δL * ‖Y i (t + y)‖) 2 (volume.restrict K') ≤
      ENNReal.ofReal (ε / 4) := by
    rw [show (fun t => δL * ‖Y i (t + y)‖) = δL • fun t => ‖Y i (t + y)‖ by funext; simp,
      eLpNorm_const_smul, eLpNorm_norm, eLpNorm_comp_add_restrict (hmeas i) hK'm y,
      Real.enorm_of_nonneg hδL.le]
    have hsub : eLpNorm (Y i) 2 (volume.restrict (shiftSet K' y)) ≤ ENNReal.ofReal Mp :=
      (eLpNorm_mono_measure _ (Measure.restrict_mono
        ((shiftSet_subset_cthickening subset_rfl hy).trans hrB) le_rfl)).trans
        ((hbdd i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    calc ENNReal.ofReal δL * eLpNorm (Y i) 2 (volume.restrict (shiftSet K' y))
        ≤ ENNReal.ofReal δL * ENNReal.ofReal Mp := by gcongr
      _ = ENNReal.ofReal (δL * Mp) := (ENNReal.ofReal_mul hδL.le).symm
      _ ≤ ENNReal.ofReal (ε / 4) := by
          refine ENNReal.ofReal_le_ofReal ?_
          simp only [δL]
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have b3 : eLpNorm (E.indicator fun t => 2 * ‖Y i (t + y)‖) 2 (volume.restrict K') ≤
      ENNReal.ofReal (ε / 2) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hEm, Measure.restrict_restrict hEm,
      show (fun t => 2 * ‖Y i (t + y)‖) = (2 : ℝ) • fun t => ‖Y i (t + y)‖ by funext; simp,
      eLpNorm_const_smul, eLpNorm_norm, eLpNorm_comp_add_restrict (hmeas i) (hEm.inter hK'm) y]
    have hvol : volume (shiftSet (E ∩ K') y) ≤ ENNReal.ofReal δU := by
      rw [volume_shiftSet (hEm.inter hK'm)]
      refine (volume_lineInt_gt_inter_le (ha i μ) μ s hδL hK'm).trans ?_
      have hfub := setLIntegral_lineInt_le (ha i μ) μ hs0 hsr hK'm
      have hL1 := setLIntegral_enorm_le_eLpNorm_four (ha i μ).aestronglyMeasurable hrB
      have hnum : ∫⁻ t in K', lineInt (a i μ) μ s t ≤ ENNReal.ofReal (s * MAp) := by
        refine hfub.trans ?_
        rw [ENNReal.ofReal_mul hs0]
        gcongr
        exact hL1.trans ((hA i μ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      refine (ENNReal.div_le_div_right hnum _).trans ?_
      rw [← ENNReal.ofReal_div_of_pos hδL]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ hδL]
      have := mul_le_mul_of_nonneg_right hsU (by positivity : (0 : ℝ) ≤ MAp)
      have h2 : δU * δL / (MAp + 1) * MAp ≤ δU * δL := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_pos hδU hδL]
      linarith
    have hUIb := hUI i (shiftSet (E ∩ K') y) (measurableSet_shiftSet (hEm.inter hK'm) y)
      (shiftSet_subset_cthickening inter_subset_right hy) hvol
    calc ‖(2 : ℝ)‖ₑ * eLpNorm (Y i) 2 (volume.restrict (shiftSet (E ∩ K') y))
        ≤ ‖(2 : ℝ)‖ₑ * ENNReal.ofReal (ε / 4) := by gcongr
      _ = ENNReal.ofReal (ε / 2) := by
          rw [Real.enorm_of_nonneg (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
          ring_nf
  calc eLpNorm (fun t => Y i (t + coordPt μ s) - Y i t) 2 (volume.restrict K')
      ≤ eLpNorm (fun t => ‖covTransl (P i) (Y i) μ s t - Y i t‖ + δL * ‖Y i (t + y)‖ +
          E.indicator (fun t => 2 * ‖Y i (t + y)‖) t) 2 (volume.restrict K') :=
        eLpNorm_mono_real fun t => hpt t
    _ ≤ eLpNorm (fun t => ‖covTransl (P i) (Y i) μ s t - Y i t‖ + δL * ‖Y i (t + y)‖) 2
          (volume.restrict K') +
        eLpNorm (E.indicator fun t => 2 * ‖Y i (t + y)‖) 2 (volume.restrict K') :=
        eLpNorm_add_le (hcov.norm.add hg2).restrict hg3.restrict (by norm_num)
    _ ≤ (eLpNorm (fun t => ‖covTransl (P i) (Y i) μ s t - Y i t‖) 2 (volume.restrict K') +
          eLpNorm (fun t => δL * ‖Y i (t + y)‖) 2 (volume.restrict K')) +
        eLpNorm (E.indicator fun t => 2 * ‖Y i (t + y)‖) 2 (volume.restrict K') := by
        gcongr
        exact eLpNorm_add_le hcov.norm.restrict hg2.restrict (by norm_num)
    _ ≤ (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) + ENNReal.ofReal (ε / 2) := by
        gcongr
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-! ### Non-vacuity -/

/-- The flat connection `a = 0` has the trivial unitary transports `ρ(P) = 1`. -/
theorem isUnitaryTransport_zero (μ : d) (s : ℝ) (t : UnitAddTorus d) :
    IsUnitaryTransport (fun _ : UnitAddTorus d => (0 : ℝ →L[ℝ] ℝ)) μ s t 1 := by
  refine ⟨fun _ => 1, rfl, fun τ _ => ?_, fun τ _ v => by simp, by simp, by simp⟩
  simpa using hasDerivWithinAt_const τ (Icc 0 s) (1 : ℝ →L[ℝ] ℝ)

/-- Non-vacuity of the vector assertion: the flat connection, its trivial transports and the
vanishing packet on the chart `B = 𝕋¹` satisfy every hypothesis. -/
example : ∀ ε > 0, ∃ J : Finset ℕ, ∀ i, ∃ j ∈ J,
    eLpNorm (fun t => (fun _ : ℕ => fun _ : UnitAddTorus (Fin 1) => (0 : ℝ)) i t -
      (fun _ : ℕ => fun _ : UnitAddTorus (Fin 1) => (0 : ℝ)) j t) 2 (volume.restrict univ) ≤
      ENNReal.ofReal ε :=
  wilson_screen_vector_nets (fun _ _ _ _ => (1 : ℝ →L[ℝ] ℝ)) (fun _ _ => 0) (fun _ _ _ => 0)
    isOpen_univ (fun _ => aestronglyMeasurable_const) 0 (fun _ => by simp)
    (fun _ _ _ ε hε => ⟨1, one_pos, ∅, finite_empty, fun _ _ _ _ _ => by simp [covTransl]⟩)
    (fun _ _ => continuous_const) 0 (fun _ _ => by simp)
    (fun _ μ s t _ => isUnitaryTransport_zero μ s t) isCompact_univ subset_rfl

end RenewalGeometry.WilsonScreen
