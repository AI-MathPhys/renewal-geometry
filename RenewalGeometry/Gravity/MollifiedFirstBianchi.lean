/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.MollifierLpConvergence
import RenewalGeometry.Gravity.DistributionalFirstBianchi
import RenewalGeometry.Gravity.LimitEinsteinInsertion

/-!
# The first Bianchi identity at limit regularity, by mollification
  (Bianchi / Holst-inert step of `thm:supp-renewal-palatini`; emergent-spacetime manuscript,
  supplement)

`Gravity/DistributionalFirstBianchi.lean` proves `R ∧ e = 0` for weak–strong limits of `C¹`
approximants with `L²`-vanishing torsion.  Here the identity is proved directly for a limit
pair, by mollification (`Analysis/MollifierLpConvergence.lean`), under an anisotropic
integrability packet (`AnisotropicIntegrability`):
`R ∈ L²_loc`, `e ∈ L⁶_loc`, `ω ∈ L²_loc`, and every connection coefficient except one
(temporal) coefficient `ω_t` in `L³_loc`.

* `mollify`, `reflectedTest`, `mollify_eq_integral`, `integral_pderiv_reflectedTest`: the
  mollification of the truncated field `𝟙_K F` and its derivatives are tested pairings of `F`
  against the reflected kernel `y ↦ ρ(x - y) ∈ 𝓓(Ω)`;
* `classicalTorsion_mollify`: for a distributionally torsion-free pair, the classical torsion of
  the mollified pair is a difference of commutators `act(ω^ρ_b) e^ρ_c - (act(ω_b) e_c)^ρ`;
* `classicalCurvature_mollify`: if `R = dω + ω ∧ ω` in distributions, the classical curvature of
  the mollified connection is `R^ρ + Ξ_{ab} - Ξ_{ba}`, `Ξ_{ab} = ω^ρ_a ω^ρ_b - (ω_a ω_b)^ρ`;
* `lpTendsto_mollify`: mollified truncations converge strongly in `L^p` on compacts;
* `bianchiPairing_eq_zero_of_ne`, `isDistributionalBianchi_of_isTorsionFree`:
  **the first Bianchi identity `R ∧ e = 0` in distributions** for a torsion-free pair with
  `R = dω + ω ∧ ω` at the anisotropic regularity.  The commutator terms vanish in `L¹` by
  Hölder (exponent pairs `(2,6)`, `(3,6)`, `(2,3)`, `(6/5,6)`, `(2,2)`, `(3,3/2)`); the only
  product that would fail (`ω_t · (ω_t ∧ e)`, exponents `2` and `3/2`) never occurs because
  `dt ∧ dt = 0`.  Repeated form indices are handled by the almost-everywhere antisymmetry of a
  distributional curvature (`ae_curvature_add_swap_eq_zero`);
* `isDistributionalBianchi_of_regulator_limit`: the same for strong regulator limits with a
  uniform `L⁶` coframe bound and a uniform `L³` bound on the spatial connection coefficients
  (the bounds pass to the limit by `LpTendsto.memLp_of_bound`);
* `integral_classifiedMetricVariation_of_isTorsionFree`: **Einstein insertion for the limit
  pair at limit regularity**: on every compact `K ⊆ Ω`,
  `∫_K δ(α L_H + β L_P + λ L_vol)[k] = β ∫_K √(-g) k^{γb}(G + Λ g)_{bγ}`, the Holst variation
  dropping out by the Bianchi identity (no approximants needed);
* `ae_map_curvature_eq_zero`, `so13Defect_commutator`: linear constraints satisfied by the
  connection and its commutators pass to the distributional curvature; in particular the
  curvature of an `so(1,3)`-valued (metric-compatible) `L²_loc` connection is `so(1,3)`-valued;
* `integral_classifiedMetricVariation_of_metricCompatible`: the Einstein insertion for a
  torsion-free, metric-compatible limit connection, with the internal antisymmetry of the
  curvature derived rather than assumed.

Disclosed scope.  The regularity used is strictly more than the manuscript's full-connection
route provides: `thm:supp-curvature-compactness` gives only strong `L²_loc` convergence of the
whole connection, and at `ω ∈ L²_loc`, `e ∈ L⁶_loc` the product rule behind `d(de) = 0` is not
available (the commutator `ω^ρ_t (ω_t e)^ρ` is only in `L^{6/7}`).  The uniform spatial `L³`
bound is supplied by the Hodge–temporal realization (`L⁴` part of
`eq:main-connection-hodge-budget`) and by the literal-link route (`L^{10/3}`,
`eq:supp-literal-integrability`).
-/

open MeasureTheory Filter Topology ENNReal Set Metric TopologicalSpace
open scoped NNReal Distributions Convolution

noncomputable section

namespace RenewalGeometry.MollifiedBianchi

open DistributionalBianchi DistributionalTorsion DistributionalCurvature Mollifier

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-! ### Local mollification identities -/

section Local

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Mollification of the truncation `𝟙_K F` of a field by a kernel `ρ`. -/
def mollify (ρ : (Fin d → ℝ) → ℝ) (K : Set (Fin d → ℝ)) (F : (Fin d → ℝ) → W) :
    (Fin d → ℝ) → W :=
  ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K.indicator F

theorem mem_of_sub_mem_closedBall {ρ : (Fin d → ℝ) → ℝ} {r : ℝ} {K : Set (Fin d → ℝ)}
    {x y : Fin d → ℝ} (hρs : tsupport ρ ⊆ closedBall 0 r) (hball : closedBall x r ⊆ K)
    (hy : x - y ∈ tsupport ρ) : y ∈ K := by
  apply hball
  have := hρs hy
  rw [mem_closedBall, dist_zero_right, ← dist_eq_norm] at this
  rw [mem_closedBall, dist_comm]; exact this

/-- Near a point whose `r`-ball lies in `K`, the mollification is the integral against the
reflected kernel `y ↦ ρ(x - y)`. -/
theorem mollify_eq_integral {ρ : (Fin d → ℝ) → ℝ} {r : ℝ} {K : Set (Fin d → ℝ)}
    (hρs : tsupport ρ ⊆ closedBall 0 r) {x : Fin d → ℝ} (hball : closedBall x r ⊆ K)
    (F : (Fin d → ℝ) → W) :
    mollify ρ K F x = ∫ y, ρ (x - y) • F y := by
  unfold mollify
  rw [convolution_def]
  have h := integral_sub_left_eq_self (fun y => ρ (x - y) • K.indicator F y) volume x
  have hxx : ∀ t : Fin d → ℝ, x - (x - t) = t := fun t => sub_sub_cancel x t
  simp only [hxx] at h
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hρ : ρ (x - y) = 0
  · simp [hρ]
  · have hy : y ∈ K := mem_of_sub_mem_closedBall hρs hball (subset_tsupport ρ hρ)
    simp [Set.indicator_of_mem hy]

/-- Near a point whose `r`-ball lies in `K`, the partial derivative of the mollification is the
integral against the derivative of the kernel. -/
theorem vpd_mollify_eq_integral {ρ : (Fin d → ℝ) → ℝ} {r : ℝ} {K : Set (Fin d → ℝ)}
    (hρ : ContDiff ℝ 1 ρ) (hρs : tsupport ρ ⊆ closedBall 0 r) {F : (Fin d → ℝ) → W}
    (hF : LocallyIntegrable (K.indicator F) volume) {x : Fin d → ℝ} (hball : closedBall x r ⊆ K)
    (b : Fin d) :
    vpd (mollify ρ K F) b x = ∫ y, fderiv ℝ ρ (x - y) (Pi.single b 1) • F y := by
  have hcs : HasCompactSupport ρ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 r)
      ((subset_tsupport ρ).trans hρs)
  unfold vpd mollify
  rw [fderiv_convolution_apply hρ hcs hF]
  have h := integral_sub_left_eq_self
    (fun y => fderiv ℝ ρ (x - y) (Pi.single b 1) • K.indicator F y) volume x
  have hxx : ∀ t : Fin d → ℝ, x - (x - t) = t := fun t => sub_sub_cancel x t
  simp only [hxx] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hρ' : fderiv ℝ ρ (x - y) = 0
  · simp [hρ']
  · have hy : y ∈ K := mem_of_sub_mem_closedBall hρs hball (support_fderiv_subset ℝ hρ')
    simp [Set.indicator_of_mem hy]

/-- The reflected kernel `y ↦ ρ(x - y)` as a test function on `Ω`. -/
def reflectedTest {Ω : Opens (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ} {r : ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρs : tsupport ρ ⊆ closedBall 0 r) (x : Fin d → ℝ) (hΩ : closedBall x r ⊆ Ω) :
    𝓓(Ω, ℝ) where
  toFun y := ρ (x - y)
  contDiff' := hρ.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x r) ?_
    intro y hy
    exact mem_of_sub_mem_closedBall hρs le_rfl (subset_tsupport ρ hy)
  tsupport_subset' := by
    refine (closure_minimal ?_ isClosed_closedBall).trans hΩ
    intro y hy
    exact mem_of_sub_mem_closedBall hρs le_rfl (subset_tsupport ρ hy)

theorem reflectedTest_apply {Ω : Opens (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ} {r : ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρs : tsupport ρ ⊆ closedBall 0 r) (x : Fin d → ℝ)
    (hΩ : closedBall x r ⊆ Ω) (y : Fin d → ℝ) :
    reflectedTest hρ hρs x hΩ y = ρ (x - y) := rfl

theorem pderiv_reflectedTest {Ω : Opens (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ} {r : ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρs : tsupport ρ ⊆ closedBall 0 r) (x : Fin d → ℝ)
    (hΩ : closedBall x r ⊆ Ω) (b : Fin d) (y : Fin d → ℝ) :
    pderiv b (reflectedTest hρ hρs x hΩ) y = -fderiv ℝ ρ (x - y) (Pi.single b 1) := by
  have hd : HasFDerivAt (fun y => ρ (x - y))
      ((fderiv ℝ ρ (x - y)).comp (-ContinuousLinearMap.id ℝ (Fin d → ℝ))) y :=
    ((hρ.differentiable (by simp)) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)
  unfold pderiv
  change fderiv ℝ (fun y => ρ (x - y)) y (Pi.single b 1) = _
  rw [hd.fderiv]
  simp

/-- Distributional derivative against the reflected kernel = derivative of the mollification. -/
theorem integral_pderiv_reflectedTest {Ω : Opens (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ} {r : ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρs : tsupport ρ ⊆ closedBall 0 r) {K : Set (Fin d → ℝ)}
    {F : (Fin d → ℝ) → W} (hF : LocallyIntegrable (K.indicator F) volume) (x : Fin d → ℝ)
    (hball : closedBall x r ⊆ K) (hΩ : closedBall x r ⊆ Ω) (b : Fin d) :
    ∫ y, pderiv b (reflectedTest hρ hρs x hΩ) y • F y = -vpd (mollify ρ K F) b x := by
  rw [vpd_mollify_eq_integral (hρ.of_le (by simp)) hρs hF hball b, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [pderiv_reflectedTest, neg_smul]

theorem integral_reflectedTest {Ω : Opens (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ} {r : ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρs : tsupport ρ ⊆ closedBall 0 r) {K : Set (Fin d → ℝ)}
    (F : (Fin d → ℝ) → W) (x : Fin d → ℝ) (hball : closedBall x r ⊆ K)
    (hΩ : closedBall x r ⊆ Ω) :
    ∫ y, reflectedTest hρ hρs x hΩ y • F y = mollify ρ K F x := by
  rw [mollify_eq_integral hρs hball]; rfl

end Local

/-! ### Torsion and curvature of the mollified fields -/

section Identities

variable {A V : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **Torsion of the mollified pair.**  If `ω` is torsion-free for `e` in distributions on `Ω`,
then at every point whose `r`-ball lies in `K ⊆ Ω` the classical torsion of the mollified pair is
the difference of two commutators `act(ω^ρ_b) e^ρ_c - (act(ω_b) e_c)^ρ`. -/
theorem classicalTorsion_mollify (act : A →L[ℝ] V →L[ℝ] V) {Ω : Opens (Fin d → ℝ)}
    {e : Fin d → (Fin d → ℝ) → V} {ω : Fin d → (Fin d → ℝ) → A} (hT : IsTorsionFree act Ω e ω)
    {ρ : (Fin d → ℝ) → ℝ} {r : ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρs : tsupport ρ ⊆ closedBall 0 r)
    {K : Set (Fin d → ℝ)} (he : ∀ c, LocallyIntegrable (K.indicator (e c)) volume)
    {x : Fin d → ℝ} (hball : closedBall x r ⊆ K) (hΩ : closedBall x r ⊆ Ω) (b c : Fin d) :
    classicalTorsion act (fun c => mollify ρ K (e c)) (fun a => mollify ρ K (ω a)) b c x =
      (act (mollify ρ K (ω b) x) (mollify ρ K (e c) x) -
          mollify ρ K (fun y => act (ω b y) (e c y)) x) -
        (act (mollify ρ K (ω c) x) (mollify ρ K (e b) x) -
          mollify ρ K (fun y => act (ω c y) (e b y)) x) := by
  have h := hT (reflectedTest hρ hρs x hΩ) b c
  unfold torsionPairing at h
  rw [integral_pderiv_reflectedTest hρ hρs (he c) x hball hΩ b,
    integral_pderiv_reflectedTest hρ hρs (he b) x hball hΩ c,
    integral_reflectedTest hρ hρs _ x hball hΩ, integral_reflectedTest hρ hρs _ x hball hΩ] at h
  rw [← sub_eq_zero, ← h]
  unfold classicalTorsion
  abel

/-- **Curvature of the mollified connection.**  If `R = dω + ω ∧ ω` in distributions on `Ω`,
then at every point whose `r`-ball lies in `K ⊆ Ω` the classical curvature of the mollified
connection is `R^ρ + Ξ_{ab} - Ξ_{ba}` with the commutators `Ξ_{ab} = ω^ρ_a ω^ρ_b - (ω_a ω_b)^ρ`. -/
theorem classicalCurvature_mollify {Ω : Opens (Fin d → ℝ)} {ω : Fin d → (Fin d → ℝ) → A}
    {R : Fin d → Fin d → (Fin d → ℝ) → A} (hC : IsDistributionalCurvature Ω ω R)
    {ρ : (Fin d → ℝ) → ℝ} {r : ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρs : tsupport ρ ⊆ closedBall 0 r)
    {K : Set (Fin d → ℝ)} (hω : ∀ a, LocallyIntegrable (K.indicator (ω a)) volume)
    {x : Fin d → ℝ} (hball : closedBall x r ⊆ K) (hΩ : closedBall x r ⊆ Ω) (a b : Fin d) :
    classicalCurvature (fun a => mollify ρ K (ω a)) a b x =
      mollify ρ K (R a b) x +
        (mollify ρ K (ω a) x * mollify ρ K (ω b) x - mollify ρ K (fun y => ω a y * ω b y) x) -
        (mollify ρ K (ω b) x * mollify ρ K (ω a) x - mollify ρ K (fun y => ω b y * ω a y) x) := by
  have h := hC (reflectedTest hρ hρs x hΩ) a b
  unfold curvaturePairing at h
  rw [integral_pderiv_reflectedTest hρ hρs (hω b) x hball hΩ a,
    integral_pderiv_reflectedTest hρ hρs (hω a) x hball hΩ b,
    integral_reflectedTest hρ hρs _ x hball hΩ, integral_reflectedTest hρ hρs _ x hball hΩ,
    integral_reflectedTest hρ hρs _ x hball hΩ] at h
  rw [h]
  unfold classicalCurvature
  abel

end Identities

/-! ### Strong convergence of the mollified truncations -/

section Convergence

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- If `F ∈ L^p(K)` (`1 ≤ p < ∞`) and `C ⊆ K`, the mollifications of `𝟙_K F` by continuous
probability kernels with shrinking supports converge to `F` strongly in `L^p(C)`. -/
theorem lpTendsto_mollify {K C : Set (Fin d → ℝ)} (hK : MeasurableSet K) (hC : MeasurableSet C)
    (hCK : C ⊆ K) {ρ : ℕ → (Fin d → ℝ) → ℝ} {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (hρc : ∀ n, Continuous (ρ n)) (hρ0 : ∀ n x, 0 ≤ ρ n x) (hρ1 : ∀ n, ∫ x, ρ n x = 1)
    (hρs : ∀ n, Function.support (ρ n) ⊆ ball 0 (r n)) {F : (Fin d → ℝ) → W} {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hF : MemLp F p (volume.restrict K)) :
    LpTendsto (volume.restrict C) p (fun n => mollify (ρ n) K F) F := by
  have hFi : MemLp (K.indicator F) p volume := (memLp_indicator_iff_restrict hK).2 hF
  have hloc : LocallyIntegrable (K.indicator F) volume := hFi.locallyIntegrable hp1
  have hm : ∀ n, MemLp (mollify (ρ n) K F) p volume := fun n =>
    ⟨((hasCompactSupport_of_support_subset_ball (hρs n)).continuous_convolution_left _ (hρc n)
        hloc).aestronglyMeasurable,
      (eLpNorm_convolution_le (hρc n).measurable (hρ0 n) (hρ1 n) hFi.1 hp1 hp).trans_lt hFi.2⟩
  have hg : LpTendsto volume p (fun n => mollify (ρ n) K F) (K.indicator F) :=
    ⟨hm, hFi, tendsto_eLpNorm_convolution_sub hr hρc hρ0 hρ1 hρs hp1 hp hFi⟩
  refine (hg.restrict C).congr (fun n => EventuallyEq.rfl) ?_
  filter_upwards [ae_restrict_mem hC] with x hx
  exact Set.indicator_of_mem (hCK hx) F

end Convergence

/-! ### Exponent bookkeeping -/

section Exponents

theorem fact_one_le_three : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
theorem fact_one_le_six : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩
theorem fact_one_le_three_halves : Fact ((1 : ℝ≥0∞) ≤ 3 / 2) :=
  ⟨by rw [ENNReal.le_div_iff_mul_le (by simp) (by simp)]; norm_num⟩
theorem fact_one_le_six_fifths : Fact ((1 : ℝ≥0∞) ≤ 6 / 5) :=
  ⟨by rw [ENNReal.le_div_iff_mul_le (by simp) (by simp)]; norm_num⟩

theorem ofReal_three_halves : ENNReal.ofReal (3 / 2) = 3 / 2 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
theorem ofReal_six_fifths : ENNReal.ofReal (6 / 5) = 6 / 5 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

theorem holderTriple_two_six : HolderTriple 2 6 (3 / 2) := by
  have := holderTriple_ofReal (p := 2) (q := 6) (r := 3 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa [ofReal_three_halves] using this
theorem holderTriple_three_six : HolderTriple 3 6 2 := by
  have := holderTriple_ofReal (p := 3) (q := 6) (r := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa using this
theorem holderTriple_two_three : HolderTriple 2 3 (6 / 5) := by
  have := holderTriple_ofReal (p := 2) (q := 3) (r := 6 / 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa [ofReal_six_fifths] using this
theorem holderTriple_six_fifths_six : HolderTriple (6 / 5) 6 1 := by
  have := holderTriple_ofReal (p := 6 / 5) (q := 6) (r := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa [ofReal_six_fifths] using this
theorem holderTriple_three_three_halves : HolderTriple 3 (3 / 2) 1 := by
  have := holderTriple_ofReal (p := 3) (q := 3 / 2) (r := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa [ofReal_three_halves] using this

attribute [local instance] fact_one_le_three fact_one_le_six fact_one_le_three_halves
  fact_one_le_six_fifths holderTriple_two_six holderTriple_three_six holderTriple_two_three
  holderTriple_six_fifths_six holderTriple_three_three_halves

example : HolderTriple 3 2 (6 / 5) := inferInstance
example : HolderTriple ∞ 1 1 := inferInstance
example : HolderTriple 2 2 1 := inferInstance

end Exponents

/-! ### The first Bianchi identity for a torsion-free limit pair -/

section Main

attribute [local instance] fact_one_le_three fact_one_le_six fact_one_le_three_halves
  fact_one_le_six_fifths holderTriple_two_six holderTriple_three_six holderTriple_two_three
  holderTriple_six_fifths_six holderTriple_three_three_halves

variable {A V : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The anisotropic integrability packet of a limit coframe/connection/curvature triple on `Ω`:
curvature in `L²_loc`, coframe in `L⁶_loc`, every connection coefficient in `L²_loc`, and the
connection coefficients other than the temporal one `t` in `L³_loc`. -/
structure AnisotropicIntegrability (Ω : Opens (Fin d → ℝ)) (t : Fin d)
    (e : Fin d → (Fin d → ℝ) → V) (ω : Fin d → (Fin d → ℝ) → A)
    (R : Fin d → Fin d → (Fin d → ℝ) → A) : Prop where
  curvature : ∀ a b (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (R a b) 2 (volume.restrict C)
  coframe : ∀ c (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (e c) 6 (volume.restrict C)
  connection : ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (ω a) 2 (volume.restrict C)
  spatial : ∀ a, a ≠ t → ∀ (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (ω a) 3 (volume.restrict C)

theorem memLp_top_of_test {ψ : (Fin d → ℝ) → ℝ} (hψ : Continuous ψ)
    {C : Set (Fin d → ℝ)} (hC : IsCompact C) (hz : ∀ x, x ∉ C → ψ x = 0) :
    MemLp ψ ∞ (volume.restrict C) := by
  obtain ⟨M, hM⟩ := exists_bound_of_eq_zero_off hψ hC hz
  exact memLp_top_of_bound hψ.aestronglyMeasurable M (Eventually.of_forall hM)

/-- **First Bianchi identity for distinct form indices.**  Let `ω` be torsion-free for `e` and
`R = dω + ω ∧ ω`, both in distributions on `Ω`, with the anisotropic integrability packet
(`R ∈ L²_loc`, `e ∈ L⁶_loc`, `ω ∈ L²_loc`, spatial `ω_a ∈ L³_loc`).  Then
`⟨R ∧ e, φ⟩_{abc} = 0` for distinct `a, b, c`.  Proof: mollify, apply the `C¹` Bianchi identity
`bianchi_integral_identity`, and pass to the limit; the commutator terms vanish in `L¹` by
Hölder's inequality because a product of two temporal coefficients never occurs. -/
theorem bianchiPairing_eq_zero_of_ne (act : A →L[ℝ] V →L[ℝ] V)
    (hact : ∀ (x y : A) (v : V), act (x * y) v = act x (act y v)) {Ω : Opens (Fin d → ℝ)}
    {e : Fin d → (Fin d → ℝ) → V} {ω : Fin d → (Fin d → ℝ) → A}
    {R : Fin d → Fin d → (Fin d → ℝ) → A} {t : Fin d} (hT : IsTorsionFree act Ω e ω)
    (hC : IsDistributionalCurvature Ω ω R) (hI : AnisotropicIntegrability Ω t e ω R)
    (φ : 𝓓(Ω, ℝ)) {a b c : Fin d} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    bianchiPairing act R e φ a b c = 0 := by
  set C := tsupport (φ : (Fin d → ℝ) → ℝ) with hCdef
  have hCc : IsCompact C := φ.hasCompactSupport
  have hCΩ : C ⊆ Ω := φ.tsupport_subset
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  obtain ⟨δ, hδ, hKΩ⟩ := hCc.exists_cthickening_subset_open Ω.isOpen hCΩ
  set K := cthickening δ C with hKdef
  have hKc : IsCompact K := hCc.cthickening
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hCK : C ⊆ K := self_subset_cthickening C
  -- the mollifiers
  set r : ℕ → ℝ := fun n => δ / ((n : ℝ) + 2) with hrdef
  have hrpos : ∀ n, 0 < r n := fun n => by positivity
  have hrδ : ∀ n, r n ≤ δ := fun n => div_le_self hδ.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hr : Tendsto r atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  let bump : ℕ → ContDiffBump (0 : Fin d → ℝ) := fun n =>
    ⟨r n / 2, r n, half_pos (hrpos n), half_lt_self (hrpos n)⟩
  set ρ : ℕ → (Fin d → ℝ) → ℝ := fun n => (bump n).normed volume with hρdef
  have hρ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ρ n) := fun n => (bump n).contDiff_normed
  have hρs : ∀ n, tsupport (ρ n) ⊆ closedBall 0 (r n) := fun n =>
    ((bump n).tsupport_normed_eq (μ := volume)).le
  have hρc : ∀ n, Continuous (ρ n) := fun n => (bump n).continuous_normed
  have hρ0 : ∀ n x, 0 ≤ ρ n x := fun n x => (bump n).nonneg_normed x
  have hρ1 : ∀ n, ∫ x, ρ n x = 1 := fun n => (bump n).integral_normed
  have hρb : ∀ n, Function.support (ρ n) ⊆ ball 0 (r n) := fun n =>
    ((bump n).support_normed_eq (μ := volume)).le
  have hball : ∀ n, ∀ x ∈ C, closedBall x (r n) ⊆ K := fun n x hx =>
    (closedBall_subset_cthickening hx (r n)).trans (cthickening_mono (hrδ n) C)
  have hballΩ : ∀ n, ∀ x ∈ C, closedBall x (r n) ⊆ Ω := fun n x hx => (hball n x hx).trans hKΩ
  -- integrability on `K`
  have heK : ∀ c, MemLp (e c) 6 (volume.restrict K) := fun c => hI.coframe c K hKc hKΩ
  have hωK : ∀ a, MemLp (ω a) 2 (volume.restrict K) := fun a => hI.connection a K hKc hKΩ
  have hω3K : ∀ a, a ≠ t → MemLp (ω a) 3 (volume.restrict K) := fun a ha =>
    hI.spatial a ha K hKc hKΩ
  have hRK : ∀ a b, MemLp (R a b) 2 (volume.restrict K) := fun a b => hI.curvature a b K hKc hKΩ
  have heL : ∀ c, LocallyIntegrable (K.indicator (e c)) volume := fun c =>
    ((memLp_indicator_iff_restrict hKm).2 (heK c)).locallyIntegrable (by norm_num)
  have hωL : ∀ a, LocallyIntegrable (K.indicator (ω a)) volume := fun a =>
    ((memLp_indicator_iff_restrict hKm).2 (hωK a)).locallyIntegrable (by norm_num)
  -- the mollified fields
  set E : ℕ → Fin d → (Fin d → ℝ) → V := fun n c => mollify (ρ n) K (e c) with hEdef
  set Wn : ℕ → Fin d → (Fin d → ℝ) → A := fun n a => mollify (ρ n) K (ω a) with hWdef
  have hE1 : ∀ n c, ContDiff ℝ 1 (E n c) := fun n c =>
    ((bump n).hasCompactSupport_normed).contDiff_convolution_left _
      ((hρ n).of_le (by simp)) (heL c)
  have hW1 : ∀ n a, ContDiff ℝ 1 (Wn n a) := fun n a =>
    ((bump n).hasCompactSupport_normed).contDiff_convolution_left _
      ((hρ n).of_le (by simp)) (hωL a)
  set ν := volume.restrict C with hνdef
  have : IsFiniteMeasure ν := ⟨by rw [Measure.restrict_apply_univ]; exact hCc.measure_lt_top⟩
  have hconvV : ∀ {F : (Fin d → ℝ) → V} {p : ℝ≥0∞}, 1 ≤ p → p ≠ ∞ →
      MemLp F p (volume.restrict K) → LpTendsto ν p (fun n => mollify (ρ n) K F) F :=
    fun hp1 hp hF => lpTendsto_mollify hKm hCm hCK hr hρc hρ0 hρ1 hρb hp1 hp hF
  have hconvA : ∀ {F : (Fin d → ℝ) → A} {p : ℝ≥0∞}, 1 ≤ p → p ≠ ∞ →
      MemLp F p (volume.restrict K) → LpTendsto ν p (fun n => mollify (ρ n) K F) F :=
    fun hp1 hp hF => lpTendsto_mollify hKm hCm hCK hr hρc hρ0 hρ1 hρb hp1 hp hF
  -- convergence of the mollified fields on `C`
  have h6 : (1 : ℝ≥0∞) ≤ 6 := by norm_num
  have h3 : (1 : ℝ≥0∞) ≤ 3 := by norm_num
  have h2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h32 : (1 : ℝ≥0∞) ≤ 3 / 2 := fact_one_le_three_halves.out
  have h65 : (1 : ℝ≥0∞) ≤ 6 / 5 := fact_one_le_six_fifths.out
  have h32t : (3 / 2 : ℝ≥0∞) ≠ ∞ := ENNReal.div_ne_top (by simp) (by simp)
  have h65t : (6 / 5 : ℝ≥0∞) ≠ ∞ := ENNReal.div_ne_top (by simp) (by simp)
  have hE6 : ∀ c, LpTendsto ν 6 (fun n => E n c) (e c) := fun c =>
    hconvV h6 (by simp) (heK c)
  have hE2 : ∀ c, LpTendsto ν 2 (fun n => E n c) (e c) := fun c =>
    (hE6 c).mono two_ne_zero (by norm_num)
  have hW2 : ∀ a, LpTendsto ν 2 (fun n => Wn n a) (ω a) := fun a =>
    hconvA h2 (by simp) (hωK a)
  have hW3 : ∀ a, a ≠ t → LpTendsto ν 3 (fun n => Wn n a) (ω a) := fun a ha =>
    hconvA h3 (by simp) (hω3K a ha)
  have hRm : ∀ a b, LpTendsto ν 2 (fun n => mollify (ρ n) K (R a b)) (R a b) := fun a b =>
    hconvA h2 (by simp) (hRK a b)
  have hM : ∀ b c, LpTendsto ν (3 / 2) (fun n => mollify (ρ n) K (fun y => act (ω b y) (e c y)))
      (fun y => act (ω b y) (e c y)) := fun b c =>
    hconvV h32 h32t (act.memLp_of_bilin (3 / 2) (hωK b) (heK c))
  have hM2 : ∀ b c, b ≠ t → LpTendsto ν 2
      (fun n => mollify (ρ n) K (fun y => act (ω b y) (e c y))) (fun y => act (ω b y) (e c y)) :=
    fun b c hb => hconvV h2 (by simp) (act.memLp_of_bilin 2 (hω3K b hb) (heK c))
  have hmulK : ∀ a b, a ≠ b → MemLp (fun y => ω a y * ω b y) (6 / 5) (volume.restrict K) := by
    intro a b hab'
    by_cases hb : b = t
    · have ha : a ≠ t := hb ▸ hab'
      simpa using (ContinuousLinearMap.mul ℝ A).memLp_of_bilin (6 / 5) (hω3K a ha) (hωK b)
    · simpa using (ContinuousLinearMap.mul ℝ A).memLp_of_bilin (6 / 5) (hωK a) (hω3K b hb)
  have hN : ∀ a b, a ≠ b → LpTendsto ν (6 / 5)
      (fun n => mollify (ρ n) K (fun y => ω a y * ω b y)) (fun y => ω a y * ω b y) :=
    fun a b hab' => hconvA h65 h65t (hmulK a b hab')
  -- products of mollified connection coefficients
  have hWW : ∀ a b, a ≠ b → LpTendsto ν (6 / 5) (fun n x => Wn n a x * Wn n b x)
      (fun x => ω a x * ω b x) := by
    intro a b hab'
    by_cases hb : b = t
    · have ha : a ≠ t := hb ▸ hab'
      simpa using (LpTendsto.bilin (r := 6 / 5) (ContinuousLinearMap.mul ℝ A) (hW3 a ha) (hW2 b))
    · simpa using (LpTendsto.bilin (r := 6 / 5) (ContinuousLinearMap.mul ℝ A) (hW2 a) (hW3 b hb))
  -- the commutators
  set Γ : ℕ → Fin d → Fin d → (Fin d → ℝ) → V := fun n b c x =>
    act (Wn n b x) (E n c x) - mollify (ρ n) K (fun y => act (ω b y) (e c y)) x with hΓdef
  set Ξ : ℕ → Fin d → Fin d → (Fin d → ℝ) → A := fun n a b x =>
    Wn n a x * Wn n b x - mollify (ρ n) K (fun y => ω a y * ω b y) x with hΞdef
  have hΓ : ∀ b c, LpTendsto ν (3 / 2) (fun n => Γ n b c) 0 := by
    intro b c
    refine ((LpTendsto.bilin (r := 3 / 2) act (hW2 b) (hE6 c)).sub (hM b c)).congr
      (fun n => EventuallyEq.rfl) (Eventually.of_forall fun x => ?_)
    simp
  have hΓ2 : ∀ b c, b ≠ t → LpTendsto ν 2 (fun n => Γ n b c) 0 := by
    intro b c hb
    refine ((LpTendsto.bilin (r := 2) act (hW3 b hb) (hE6 c)).sub (hM2 b c hb)).congr
      (fun n => EventuallyEq.rfl) (Eventually.of_forall fun x => ?_)
    simp
  have hΞ : ∀ a b, a ≠ b → LpTendsto ν (6 / 5) (fun n => Ξ n a b) 0 := by
    intro a b hab'
    refine ((hWW a b hab').sub (hN a b hab')).congr
      (fun n => EventuallyEq.rfl) (Eventually.of_forall fun x => ?_)
    simp
  -- pointwise identities on `C`
  have hPT : ∀ n b c, ∀ᵐ x ∂ν, classicalTorsion act (E n) (Wn n) b c x = Γ n b c x - Γ n c b x := by
    intro n b c
    filter_upwards [ae_restrict_mem hCm] with x hx
    exact classicalTorsion_mollify act hT (hρ n) (hρs n) heL (hball n x hx) (hballΩ n x hx) b c
  have hPR : ∀ n a b, ∀ᵐ x ∂ν, classicalCurvature (Wn n) a b x =
      mollify (ρ n) K (R a b) x + Ξ n a b x - Ξ n b a x := by
    intro n a b
    filter_upwards [ae_restrict_mem hCm] with x hx
    rw [classicalCurvature_mollify hC (hρ n) (hρs n) hωL (hball n x hx) (hballΩ n x hx) a b]
  -- the test function and its derivatives as `L^∞` weights
  have hz0 : ∀ x, x ∉ C → (φ : (Fin d → ℝ) → ℝ) x = 0 := fun x hx => test_eq_zero_off φ hx
  have hzd : ∀ i x, x ∉ C → vpd (φ : (Fin d → ℝ) → ℝ) i x = 0 := fun i x hx =>
    vpd_test_eq_zero_off φ i hx
  have hφinf : MemLp (φ : (Fin d → ℝ) → ℝ) ∞ ν := memLp_top_of_test φ.continuous hCc hz0
  have hψinf : ∀ i, MemLp (vpd (φ : (Fin d → ℝ) → ℝ) i) ∞ ν := fun i =>
    memLp_top_of_test (contDiff_vpd_test φ i).continuous hCc (hzd i)
  -- left-hand side: the Bianchi three-form of the mollified pair
  have hL : ∀ a b c, a ≠ b → LpTendsto ν 1
      (fun n x => act (classicalCurvature (Wn n) a b x) (E n c x))
      (fun x => act (R a b x) (e c x)) := by
    intro a b c hab'
    have h1 := LpTendsto.bilin (r := 1) act (hRm a b) (hE2 c)
    have h2 := LpTendsto.bilin (r := 1) act (hΞ a b hab') (hE6 c)
    have h3 := LpTendsto.bilin (r := 1) act (hΞ b a hab'.symm) (hE6 c)
    refine (h1.add (h2.sub h3)).congr (fun n => ?_) (Eventually.of_forall fun x => by simp)
    filter_upwards [hPR n a b] with x hx
    simp only [Pi.add_apply, Pi.sub_apply, hx, map_add, map_sub]
    simp only [FunLike.coe_add, FunLike.coe_sub, Pi.add_apply,
      Pi.sub_apply]
    abel
  have hB : LpTendsto ν 1
      (fun n x => (φ : (Fin d → ℝ) → ℝ) x • bianchiForm act (classicalCurvature (Wn n)) (E n) a b c x)
      (fun x => (φ : (Fin d → ℝ) → ℝ) x • bianchiForm act R e a b c x) := by
    have hsum := ((hL a b c hab).add (hL b c a hbc)).add (hL c a b hca)
    have := LpTendsto.bilin (r := 1) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)
      (LpTendsto.const hφinf) hsum
    refine this.congr (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_) <;> simp [bianchiForm]
  have hLHS : Tendsto (fun n => bianchiPairing act (classicalCurvature (Wn n)) (E n) φ a b c)
      atTop (𝓝 (bianchiPairing act R e φ a b c)) := by
    simp only [bianchiPairing, integral_test_eq_setIntegral hz0]
    exact hB.tendsto_integral
  -- right-hand side: the covariant derivative of the vanishing torsion
  have hTo : ∀ b c, LpTendsto ν 1 (fun n => classicalTorsion act (E n) (Wn n) b c) 0 := by
    intro b c
    refine (((hΓ b c).sub (hΓ c b)).mono one_ne_zero h32).congr (fun n => ?_)
      (Eventually.of_forall fun x => by simp)
    filter_upwards [hPT n b c] with x hx
    simp [hx]
  have term1 : ∀ i b c, Tendsto (fun n => ∫ x, vpd (φ : (Fin d → ℝ) → ℝ) i x •
      classicalTorsion act (E n) (Wn n) b c x) atTop (𝓝 0) := by
    intro i b c
    simp only [integral_test_eq_setIntegral (hzd i)]
    have := (LpTendsto.bilin (r := 1) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)
      (LpTendsto.const (hψinf i)) (hTo b c)).tendsto_integral
    simpa using this
  have hAΓ : ∀ a b c, a ≠ b → LpTendsto ν 1 (fun n x => act (Wn n a x) (Γ n b c x)) 0 := by
    intro a b c hab'
    by_cases hb : b = t
    · have ha : a ≠ t := hb ▸ hab'
      exact (LpTendsto.bilin (r := 1) act (hW3 a ha) (hΓ b c)).congr
        (fun n => EventuallyEq.rfl) (Eventually.of_forall fun x => by simp)
    · exact (LpTendsto.bilin (r := 1) act (hW2 a) (hΓ2 b c hb)).congr
        (fun n => EventuallyEq.rfl) (Eventually.of_forall fun x => by simp)
  have term2 : ∀ a b c, a ≠ b → a ≠ c → Tendsto (fun n => ∫ x, (φ : (Fin d → ℝ) → ℝ) x •
      act (Wn n a x) (classicalTorsion act (E n) (Wn n) b c x)) atTop (𝓝 0) := by
    intro a b c hab' hac'
    have h' : LpTendsto ν 1 (fun n x => act (Wn n a x) (classicalTorsion act (E n) (Wn n) b c x))
        0 := by
      refine ((hAΓ a b c hab').sub (hAΓ a c b hac')).congr (fun n => ?_)
        (Eventually.of_forall fun x => by simp)
      filter_upwards [hPT n b c] with x hx
      simp [hx, map_sub]
    simp only [integral_test_eq_setIntegral hz0]
    have := (LpTendsto.bilin (r := 1) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)
      (LpTendsto.const hφinf) h').tendsto_integral
    simpa using this
  have hRHS : Tendsto (fun n => torsionDerivPairing act (Wn n)
      (classicalTorsion act (E n) (Wn n)) φ a b c) atTop (𝓝 0) := by
    have h := (((term1 a b c).neg.add (term2 a b c hab hca.symm)).add
      ((term1 b c a).neg.add (term2 b c a hbc hab.symm))).add
      ((term1 c a b).neg.add (term2 c a b hca hbc.symm))
    simp only [neg_zero, add_zero] at h
    exact h
  refine tendsto_nhds_unique hLHS (hRHS.congr fun n => ?_)
  exact (bianchi_integral_identity act hact (hE1 n) (hW1 n) φ a b c).symm

/-- A distributional curvature is antisymmetric in its form indices almost everywhere on `Ω`. -/
theorem ae_curvature_add_swap_eq_zero {Ω : Opens (Fin d → ℝ)} {ω : Fin d → (Fin d → ℝ) → A}
    {R : Fin d → Fin d → (Fin d → ℝ) → A} (hC : IsDistributionalCurvature Ω ω R)
    (hR : ∀ a b (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (R a b) 2 (volume.restrict C))
    (a b : Fin d) : ∀ᵐ x, x ∈ Ω → R a b x + R b a x = 0 := by
  have hint : ∀ a b (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
      IntegrableOn (R a b) C volume := fun a b C hC hCΩ => by
    have : IsFiniteMeasure (volume.restrict C) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
    exact (hR a b C hC hCΩ).integrable (by norm_num)
  have hloc : LocallyIntegrableOn (fun x => R a b x + R b a x) Ω := by
    rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed]
    intro K hKΩ hK
    exact (hint a b K hK hKΩ).add (hint b a K hK hKΩ)
  refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgs => ?_
  set ψ : 𝓓(Ω, ℝ) := ⟨g, hg, hgc, hgs⟩
  have hz : ∀ x, x ∉ tsupport g → g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  obtain ⟨M, hM⟩ := exists_bound_of_eq_zero_off hg.continuous hgc hz
  have hi : ∀ a b, Integrable (fun x => g x • R a b x) := by
    intro a b
    have h1 : IntegrableOn (fun x => g x • R a b x) (tsupport g) volume :=
      (hint a b _ hgc hgs).bdd_smul M hg.continuous.aestronglyMeasurable.restrict
        (Eventually.of_forall hM)
    exact (integrableOn_iff_integrable_of_support_subset fun x hx => by
      by_contra h; exact hx (by simp [hz x h])).1 h1
  have h1 : ∫ x, g x • R a b x = curvaturePairing ω g a b := hC ψ a b
  have h2 : ∫ x, g x • R b a x = curvaturePairing ω g b a := hC ψ b a
  simp only [smul_add]
  rw [integral_add (hi a b) (hi b a), h1, h2]
  unfold curvaturePairing
  abel

/-- **First Bianchi identity at limit regularity.**  If the connection `ω` is torsion-free for
the coframe `e` and `R = dω + ω ∧ ω`, both in distributions on `Ω ⊆ ℝ^d`, with `R ∈ L²_loc`,
`e ∈ L⁶_loc`, `ω ∈ L²_loc` and every connection coefficient except one (temporal) coefficient in
`L³_loc`, then `R ∧ e = 0` in distributions on `Ω` (for connection values acting
multiplicatively on the coframe fibre). -/
theorem isDistributionalBianchi_of_isTorsionFree (act : A →L[ℝ] V →L[ℝ] V)
    (hact : ∀ (x y : A) (v : V), act (x * y) v = act x (act y v)) {Ω : Opens (Fin d → ℝ)}
    {e : Fin d → (Fin d → ℝ) → V} {ω : Fin d → (Fin d → ℝ) → A}
    {R : Fin d → Fin d → (Fin d → ℝ) → A} {t : Fin d} (hT : IsTorsionFree act Ω e ω)
    (hC : IsDistributionalCurvature Ω ω R) (hI : AnisotropicIntegrability Ω t e ω R) :
    IsDistributionalBianchi act Ω R e := by
  intro φ a b c
  by_cases hd : a ≠ b ∧ b ≠ c ∧ c ≠ a
  · exact bianchiPairing_eq_zero_of_ne act hact hT hC hI φ hd.1 hd.2.1 hd.2.2
  -- repeated indices: the integrand vanishes almost everywhere by antisymmetry
  have hanti := fun a b => ae_curvature_add_swap_eq_zero hC hI.curvature a b
  have hself : ∀ a, ∀ᵐ x, x ∈ Ω → R a a x = 0 := fun a => by
    filter_upwards [hanti a a] with x hx hxΩ
    have h2 : (2 : ℝ) • R a a x = 0 := by rw [two_smul]; exact hx hxΩ
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  unfold bianchiPairing
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hanti a b, hanti b c, hanti c a, hself a, hself b, hself c] with x
    h1 h2 h3 h4 h5 h6
  by_cases hxΩ : x ∈ Ω
  · have hR : ∀ u v, R u v x + R v u x = 0 → R v u x = -R u v x := fun u v h =>
      eq_neg_of_add_eq_zero_right h
    simp only [not_and_or, not_not] at hd
    simp only [Pi.zero_apply, bianchiForm]
    rcases hd with h | h | h
    · subst h
      rw [h4 hxΩ, hR c a (h3 hxΩ)]
      simp
    · subst h
      rw [h5 hxΩ, hR a b (h1 hxΩ)]
      simp
    · subst h
      rw [h6 hxΩ, hR b c (h2 hxΩ)]
      simp
  · have : (φ : (Fin d → ℝ) → ℝ) x = 0 := test_eq_zero_off φ fun h => hxΩ (φ.tsupport_subset h)
    simp [this]

/-- **First Bianchi identity for regulator limits with a uniform spatial `L³` bound.**  Let
`e_X → e` strongly in `L²_loc(Ω)` with a uniform `L⁶_loc` bound (condition (E4)), let the
spatial connection coefficients `ω_{X,a}` (`a ≠ t`) converge strongly in `L²_loc(Ω)` with a
uniform `L³_loc` bound, and let the limit connection lie in `L²_loc` (the temporal coefficient
may be only a weak limit).  If the limit connection is torsion-free for `e`
(`isTorsionFree_of_tendsto`, `isTorsionFree_of_tendsto_weak`) and `R = dω + ω ∧ ω ∈ L²_loc`
(`curvature_weak_compactness`), then `R ∧ e = 0` in distributions on `Ω`.  The uniform spatial
`L³` bound holds on the Hodge–temporal realization (`‖A_h‖_{L⁴}` is part of
`eq:main-connection-hodge-budget`) and on the literal-link route (the `L^{10/3}` bound
`eq:supp-literal-integrability`); it is not implied by strong `L²` connection compactness alone. -/
theorem isDistributionalBianchi_of_regulator_limit (act : A →L[ℝ] V →L[ℝ] V)
    (hact : ∀ (x y : A) (v : V), act (x * y) v = act x (act y v)) {Ω : Opens (Fin d → ℝ)}
    {e : Fin d → (Fin d → ℝ) → V} {ω : Fin d → (Fin d → ℝ) → A}
    {R : Fin d → Fin d → (Fin d → ℝ) → A} {t : Fin d} (hT : IsTorsionFree act Ω e ω)
    (hC : IsDistributionalCurvature Ω ω R)
    (hR : ∀ a b (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (R a b) 2 (volume.restrict C))
    {eX : ℕ → Fin d → (Fin d → ℝ) → V} (he : L2LocTendsto Ω eX e)
    (he6 : ∀ c (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
      ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (eX n c) 6 (volume.restrict C) ≤ M)
    (hω : ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (ω a) 2 (volume.restrict C))
    {ωX : ℕ → Fin d → (Fin d → ℝ) → A}
    (hωs : ∀ a, a ≠ t → ∀ (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
      LpTendsto (volume.restrict C) 2 (fun n => ωX n a) (ω a))
    (hω3 : ∀ a, a ≠ t → ∀ (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
      ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (ωX n a) 3 (volume.restrict C) ≤ M) :
    IsDistributionalBianchi act Ω R e := by
  refine isDistributionalBianchi_of_isTorsionFree act hact hT hC
    (t := t) ⟨hR, fun c C hC' hCΩ => ?_, hω, fun a ha C hC' hCΩ => ?_⟩
  · obtain ⟨M, hM, hb⟩ := he6 c C hC' hCΩ
    exact LpTendsto.memLp_of_bound two_ne_zero
      ⟨fun n => he.memLp n c C hC' hCΩ, he.memLp_lim c C hC' hCΩ, he.tendsto c C hC' hCΩ⟩ hM hb
  · obtain ⟨M, hM, hb⟩ := hω3 a ha C hC' hCΩ
    exact (hωs a ha C hC' hCΩ).memLp_of_bound two_ne_zero hM hb

theorem integrable_smul_of_memLp_on {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {C : Set (Fin d → ℝ)} (hC : IsCompact C)
    (hz : ∀ x, x ∉ C → f x = 0) {F : (Fin d → ℝ) → W} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hF : MemLp F p (volume.restrict C)) : Integrable (fun x => f x • F x) := by
  have : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  obtain ⟨M, hM⟩ := exists_bound_of_eq_zero_off hf hC hz
  have h1 : IntegrableOn (fun x => f x • F x) C volume :=
    (hF.integrable hp).bdd_smul M hf.aestronglyMeasurable.restrict (Eventually.of_forall hM)
  exact (integrableOn_iff_integrable_of_support_subset fun x hx => by
    by_contra h; exact hx (by simp [hz x h])).1 h1

/-- **Linear constraints pass from the connection to its distributional curvature.**  If a
continuous linear map `L` kills the `L²_loc` connection coefficients and their commutators
almost everywhere on `Ω` (e.g. `L` = the `so(1,3)` defect for a metric-compatible connection),
then `L` kills `R = dω + ω ∧ ω ∈ L²_loc` almost everywhere on `Ω`. -/
theorem ae_map_curvature_eq_zero {Ω : Opens (Fin d → ℝ)} {ω : Fin d → (Fin d → ℝ) → A}
    {R : Fin d → Fin d → (Fin d → ℝ) → A} (hC : IsDistributionalCurvature Ω ω R)
    (hR : ∀ a b (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (R a b) 2 (volume.restrict C))
    (hω : ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (ω a) 2 (volume.restrict C))
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] (L : A →L[ℝ] B)
    (hL1 : ∀ᵐ x, x ∈ Ω → ∀ a, L (ω a x) = 0)
    (hL2 : ∀ᵐ x, x ∈ Ω → ∀ a b, L (ω a x * ω b x - ω b x * ω a x) = 0) (a b : Fin d) :
    ∀ᵐ x, x ∈ Ω → L (R a b x) = 0 := by
  have hint : ∀ a b (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
      IntegrableOn (R a b) C volume := fun a b C hC' hCΩ => by
    have : IsFiniteMeasure (volume.restrict C) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hC'.measure_lt_top⟩
    exact (hR a b C hC' hCΩ).integrable (by norm_num)
  have hloc : LocallyIntegrableOn (fun x => L (R a b x)) Ω := by
    rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed]
    intro K hKΩ hK
    exact L.integrable_comp (hint a b K hK hKΩ)
  refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgs => ?_
  set ψ : 𝓓(Ω, ℝ) := ⟨g, hg, hgc, hgs⟩
  have hz : ∀ x, x ∉ tsupport g → g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hzd : ∀ i x, x ∉ tsupport g → pderiv i g x = 0 := fun i x hx => pderiv_eq_zero_off ψ i hx
  have hzΩ : ∀ x, x ∉ Ω → g x = 0 := fun x hx => hz x fun h => hx (hgs h)
  have hzdΩ : ∀ i x, x ∉ Ω → pderiv i g x = 0 := fun i x hx => hzd i x fun h => hx (hgs h)
  have hgd : ∀ i, Continuous (pderiv i g) := fun i => continuous_pderiv ψ i
  have : IsFiniteMeasure (volume.restrict (tsupport g)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hgc.measure_lt_top⟩
  have iR := integrable_smul_of_memLp_on hg.continuous hgc hz le_rfl
    ((hR a b _ hgc hgs).mono_exponent (by norm_num))
  have iω : ∀ i j, Integrable (fun x => pderiv i g x • ω j x) := fun i j =>
    integrable_smul_of_memLp_on (hgd i) hgc (hzd i) le_rfl
      ((hω j _ hgc hgs).mono_exponent (by norm_num))
  have iωω : ∀ i j, Integrable (fun x => g x • (ω i x * ω j x)) := fun i j =>
    integrable_smul_of_memLp_on hg.continuous hgc hz le_rfl
      ((ContinuousLinearMap.mul ℝ A).memLp_of_bilin 1 (hω i _ hgc hgs) (hω j _ hgc hgs))
  have hcurv : ∫ x, g x • R a b x = curvaturePairing ω g a b := hC ψ a b
  have step : ∫ x, g x • L (R a b x) = L (curvaturePairing ω g a b) := by
    rw [← hcurv, ← L.integral_comp_comm iR]
    simp only [map_smul]
  rw [step]
  unfold curvaturePairing
  rw [map_sub, map_add, map_add, map_neg, ← L.integral_comp_comm (iω a b),
    ← L.integral_comp_comm (iω b a), ← L.integral_comp_comm (iωω a b),
    ← L.integral_comp_comm (iωω b a)]
  simp only [map_smul]
  have z1 : ∀ i j, ∫ x, pderiv i g x • L (ω j x) = 0 := fun i j => by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hL1] with x hx
    by_cases hxΩ : x ∈ Ω
    · simp [hx hxΩ j]
    · simp [hzdΩ i x hxΩ]
  have i1 : Integrable fun x => g x • L (ω a x * ω b x) := by
    simpa only [map_smul] using L.integrable_comp (iωω a b)
  have i2 : Integrable fun x => g x • L (ω b x * ω a x) := by
    simpa only [map_smul] using L.integrable_comp (iωω b a)
  rw [z1, z1, neg_zero, zero_add, add_sub_assoc, ← integral_sub i1 i2, zero_add]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hL2] with x hx
  by_cases hxΩ : x ∈ Ω
  · rw [← smul_sub, ← map_sub, hx hxΩ a b, smul_zero]; rfl
  · simp [hzΩ x hxΩ]

end Main

/-! ### Einstein insertion for the limit pair at limit regularity -/

section Einstein

open LimitEinsteinInsertion PalatiniEinsteinAlgebra
open scoped Matrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Einstein insertion for a torsion-free limit pair at limit regularity**
(`eq:supp-einstein-insertion`, Holst-inert step of `thm:supp-renewal-palatini`, without
approximants).  Let `ω` be a `4 × 4`-matrix connection on `Ω ⊆ ℝ⁴`, torsion-free for the coframe
`e` and with curvature `R = dω + ω ∧ ω`, both in distributions, with `R ∈ L²_loc`, `e ∈ L⁶_loc`,
`ω ∈ L²_loc` and the three connection coefficients other than the temporal one in `L³_loc`.
If the coframe is oriented and the raised curvature internally antisymmetric almost everywhere,
then on every compact `K ⊆ Ω` the integrated classified metric first variation is the Einstein
insertion `β ∫_K √(-g) k^{γb}(G_{bγ} + Λ g_{bγ})`, `Λ = -λ/(2β)`: the Holst variation drops out
by the first Bianchi identity (`isDistributionalBianchi_of_isTorsionFree`).  The form-index
antisymmetry of `R` is derived from the distributional curvature identity. -/
theorem integral_classifiedMetricVariation_of_isTorsionFree {Ω : Opens (Fin 4 → ℝ)}
    {e : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {ω : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {t : Fin 4}
    (hT : IsTorsionFree matAct Ω e ω) (hC : IsDistributionalCurvature Ω ω R)
    (hI : AnisotropicIntegrability Ω t e ω R)
    (hdet : ∀ᵐ x, x ∈ Ω → 0 < (coframeMatrix fun μ => e μ x).det)
    (hanti : ∀ᵐ x, x ∈ Ω → ∀ K L ρ σ,
      raisedCurvature (fun ρ σ => R ρ σ x) L K ρ σ = -raisedCurvature (fun ρ σ => R ρ σ x) K L ρ σ)
    (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (k : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (α β lam : ℝ) (hβ : β ≠ 0) :
    ∫ x in K, classifiedMetricVariation α β lam minkowski (coframeMatrix fun μ => e μ x) (k x)
        (raisedCurvature fun ρ σ => R ρ σ x) =
      ∫ x in K, einsteinInsertionDensity β lam (coframeMatrix fun μ => e μ x) (k x)
        (raisedCurvature fun ρ σ => R ρ σ x) := by
  have hB := isDistributionalBianchi_of_isTorsionFree matAct matAct_mul hT hC hI
  have he2 : ∀ c (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
      MemLp (e c) 2 (volume.restrict C) := fun c C hC' hCΩ => by
    have : IsFiniteMeasure (volume.restrict C) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hC'.measure_lt_top⟩
    exact (hI.coframe c C hC' hCΩ).mono_exponent (by norm_num)
  have hae : ∀ a b c, ∀ᵐ x, x ∈ Ω → bianchiForm matAct R e a b c x = 0 := fun a b c =>
    ae_bianchi_of_isDistributionalBianchi matAct hI.curvature he2 hB a b c
  have hall : ∀ᵐ x, x ∈ Ω → ∀ a b c, bianchiForm matAct R e a b c x = 0 := by
    have : ∀ᵐ x, ∀ a b c : Fin 4, x ∈ Ω → bianchiForm matAct R e a b c x = 0 := by
      simp only [ae_all_iff]; exact hae
    filter_upwards [this] with x hx hxΩ a b c using hx a b c hxΩ
  have hswap : ∀ᵐ x, x ∈ Ω → ∀ a b, R a b x + R b a x = 0 := by
    have : ∀ᵐ x, ∀ a b : Fin 4, x ∈ Ω → R a b x + R b a x = 0 := by
      simp only [ae_all_iff]; exact fun a b => ae_curvature_add_swap_eq_zero hC hI.curvature a b
    filter_upwards [this] with x hx hxΩ a b using hx a b hxΩ
  refine setIntegral_congr_ae hK.isClosed.measurableSet ?_
  filter_upwards [hall, hdet, hanti, hswap] with x h1 h2 h3 h4 hxK
  have hxΩ := hKΩ hxK
  refine classifiedMetricVariation_eq_einstein _ _ (h2 hxΩ) _ (h3 hxΩ) (fun K L ρ σ => ?_)
    (satisfiesFirstBianchi_of_bianchiForm_eq_zero _ _ fun a b c => h1 hxΩ a b c) α β lam hβ
  have hR : R σ ρ x = -R ρ σ x := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h4 hxΩ ρ σ)
  simp only [raisedCurvature, hR, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- The integral of a partial derivative of a test function vanishes. -/
theorem integral_pderiv_test {Ω : Opens (Fin 4 → ℝ)} (φ : 𝓓(Ω, ℝ)) (a : Fin 4) :
    ∫ x, pderiv a φ x = 0 :=
  integral_vpd_eq_zero (φ.contDiff.of_le (by simp)) φ.hasCompactSupport a

/-- Non-vacuity of `integral_classifiedMetricVariation_of_isTorsionFree`: the constant basis
coframe with the zero connection and zero curvature satisfies every hypothesis (torsion-free,
curvature identity, anisotropic integrability with temporal index `0`, orientation, internal
antisymmetry). -/
example (Ω : Opens (Fin 4 → ℝ)) :
    IsTorsionFree matAct Ω (fun μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun _ _ => 0) ∧
    IsDistributionalCurvature Ω (fun _ _ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) (fun _ _ _ => 0) ∧
    AnisotropicIntegrability Ω 0 (fun μ _ => (Pi.single μ 1 : Fin 4 → ℝ))
      (fun _ _ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) (fun _ _ _ => 0) ∧
    (∀ᵐ x, x ∈ Ω → 0 < (coframeMatrix fun μ => (fun μ (_ : Fin 4 → ℝ) =>
      (Pi.single μ 1 : Fin 4 → ℝ)) μ x).det) ∧
    (∀ᵐ x, x ∈ Ω → ∀ K L ρ σ,
      raisedCurvature (fun ρ σ => (fun _ _ _ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) ρ σ x) L K ρ σ =
        -raisedCurvature (fun ρ σ => (fun _ _ _ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) ρ σ x)
          K L ρ σ) := by
  refine ⟨fun φ a b => ?_, fun φ a b => ?_, ⟨fun _ _ _ _ _ => MemLp.zero',
    fun _ C hC _ => by
      have : IsFiniteMeasure (volume.restrict C) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
      exact memLp_const _, fun _ _ _ _ => MemLp.zero',
    fun _ _ _ _ _ => MemLp.zero'⟩, Eventually.of_forall fun x _ => ?_,
    Eventually.of_forall fun x _ K L ρ σ => by simp [raisedCurvature]⟩
  · unfold torsionPairing
    have h1 : ∀ v : Fin 4 → ℝ, ∫ x : Fin 4 → ℝ, (φ : (Fin 4 → ℝ) → ℝ) x •
        (matAct (0 : Matrix (Fin 4) (Fin 4) ℝ)) v = 0 := fun v => by simp
    erw [h1, h1]
    simp only [sub_zero, add_zero]
    rw [integral_smul_const, integral_smul_const, integral_pderiv_test, integral_pderiv_test]
    simp
  · simp [curvaturePairing]
  · simp only
    rw [coframeMatrix_basis]; simp

/-! ### Metric compatibility of the curvature of a metric-compatible connection -/

/-- The `so(1,3)` defect `M η + (M η)ᵀ` of a matrix (zero iff `M η` is antisymmetric). -/
def so13Defect (M : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  M * minkowski + (M * minkowski)ᵀ

theorem minkowski_transpose : minkowskiᵀ = minkowski := by
  simp [minkowski, Matrix.diagonal_transpose]

/-- `η ω` antisymmetric implies `ω η` antisymmetric (`η² = 1`). -/
theorem so13Defect_eq_zero_of_compat {M : Matrix (Fin 4) (Fin 4) ℝ}
    (h : (minkowski * M)ᵀ = -(minkowski * M)) : so13Defect M = 0 := by
  have h' : Mᵀ * minkowski = -(minkowski * M) := by
    rw [← h, Matrix.transpose_mul, minkowski_transpose]
  have : (M * minkowski)ᵀ = -(M * minkowski) := by
    rw [Matrix.transpose_mul, minkowski_transpose]
    calc minkowski * Mᵀ = minkowski * (Mᵀ * minkowski) * minkowski := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, minkowski_mul_self, Matrix.mul_one]
      _ = -(M * minkowski) := by
          rw [h', Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, minkowski_mul_self,
            Matrix.one_mul]
  rw [so13Defect, this, add_neg_cancel]

/-- The commutator of two `so(1,3)` matrices is in `so(1,3)`. -/
theorem so13Defect_commutator {M N : Matrix (Fin 4) (Fin 4) ℝ} (hM : so13Defect M = 0)
    (hN : so13Defect N = 0) : so13Defect (M * N - N * M) = 0 := by
  have hP : (M * minkowski)ᵀ = -(M * minkowski) := eq_neg_of_add_eq_zero_right hM
  have hQ : (N * minkowski)ᵀ = -(N * minkowski) := eq_neg_of_add_eq_zero_right hN
  have key : ∀ (X Y : Matrix (Fin 4) (Fin 4) ℝ), (X * minkowski)ᵀ = -(X * minkowski) →
      (Y * minkowski)ᵀ = -(Y * minkowski) →
      (X * Y * minkowski)ᵀ = (Y * minkowski) * minkowski * (X * minkowski) := by
    intro X Y hX hY
    have : X * Y * minkowski = (X * minkowski) * minkowski * (Y * minkowski) := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc minkowski minkowski, minkowski_mul_self,
        Matrix.one_mul]
    rw [this, Matrix.transpose_mul, hY, Matrix.transpose_mul, hX, minkowski_transpose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  have hMN := key M N hP hQ
  have hNM := key N M hQ hP
  have e1 : M * N * minkowski = (M * minkowski) * minkowski * (N * minkowski) := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc minkowski minkowski, minkowski_mul_self,
      Matrix.one_mul]
  have e2 : N * M * minkowski = (N * minkowski) * minkowski * (M * minkowski) := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc minkowski minkowski, minkowski_mul_self,
      Matrix.one_mul]
  rw [so13Defect, Matrix.sub_mul, Matrix.transpose_sub, hMN, hNM, e1, e2]
  abel

/-- The `(I, J)` entry of the `so(1,3)` defect, as a continuous linear functional. -/
def so13Entry (I J : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => so13Defect M I J
      map_add' := fun M N => by
        simp only [so13Defect, Matrix.add_mul, Matrix.transpose_add, Matrix.add_apply]; ring
      map_smul' := fun c M => by
        simp only [so13Defect, Matrix.smul_mul, Matrix.transpose_smul, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

theorem so13Entry_apply (I J : Fin 4) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    so13Entry I J M = so13Defect M I J := rfl

/-- **Einstein insertion for a metric-compatible torsion-free limit pair.**  As
`integral_classifiedMetricVariation_of_isTorsionFree`, with the internal antisymmetry of the
curvature derived from the metric compatibility of the connection (`η ω_a` antisymmetric
almost everywhere): the limit connection is a torsion-free, metric-compatible represented
connection with `R = dω + ω ∧ ω` and the anisotropic integrability packet, and the coframe is
oriented.  Then for every compact `K ⊆ Ω`,
`∫_K δ(α L_H + β L_P + λ L_vol)[k] = β ∫_K √(-g) k^{γb}(G_{bγ} + Λ g_{bγ})`. -/
theorem integral_classifiedMetricVariation_of_metricCompatible {Ω : Opens (Fin 4 → ℝ)}
    {e : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {ω : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {t : Fin 4}
    (hT : IsTorsionFree matAct Ω e ω) (hC : IsDistributionalCurvature Ω ω R)
    (hI : AnisotropicIntegrability Ω t e ω R)
    (hc : ∀ᵐ x, x ∈ Ω → ∀ a, (minkowski * ω a x)ᵀ = -(minkowski * ω a x))
    (hdet : ∀ᵐ x, x ∈ Ω → 0 < (coframeMatrix fun μ => e μ x).det)
    (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (k : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (α β lam : ℝ) (hβ : β ≠ 0) :
    ∫ x in K, classifiedMetricVariation α β lam minkowski (coframeMatrix fun μ => e μ x) (k x)
        (raisedCurvature fun ρ σ => R ρ σ x) =
      ∫ x in K, einsteinInsertionDensity β lam (coframeMatrix fun μ => e μ x) (k x)
        (raisedCurvature fun ρ σ => R ρ σ x) := by
  have hsingle : ∀ I J a b, ∀ᵐ x, x ∈ Ω → so13Entry I J (R a b x) = 0 := by
    intro I J a b
    refine ae_map_curvature_eq_zero hC hI.curvature hI.connection (so13Entry I J) ?_ ?_ a b
    · filter_upwards [hc] with x hx hxΩ a
      show so13Defect (ω a x) I J = 0
      rw [so13Defect_eq_zero_of_compat (hx hxΩ a)]; rfl
    · filter_upwards [hc] with x hx hxΩ a b
      show so13Defect (ω a x * ω b x - ω b x * ω a x) I J = 0
      rw [so13Defect_commutator (so13Defect_eq_zero_of_compat (hx hxΩ a))
        (so13Defect_eq_zero_of_compat (hx hxΩ b))]; rfl
  have hall : ∀ᵐ x, x ∈ Ω → ∀ I J a b, so13Entry I J (R a b x) = 0 := by
    have : ∀ᵐ x, ∀ I J a b : Fin 4, x ∈ Ω → so13Entry I J (R a b x) = 0 := by
      simp only [ae_all_iff]; exact hsingle
    filter_upwards [this] with x hx hxΩ I J a b using hx I J a b hxΩ
  refine integral_classifiedMetricVariation_of_isTorsionFree hT hC hI hdet ?_ K hK hKΩ k α β lam
    hβ
  filter_upwards [hall] with x hx hxΩ K' L ρ σ
  have h : so13Defect (R ρ σ x) K' L = 0 := hx hxΩ K' L ρ σ
  simp only [so13Defect, Matrix.add_apply, Matrix.transpose_apply, Matrix.mul_apply] at h
  simp only [raisedCurvature]
  linarith

/-- Non-vacuity of the extra hypothesis of `integral_classifiedMetricVariation_of_metricCompatible`
(the other hypotheses are checked in the example above): the zero connection is
metric-compatible. -/
example (Ω : Opens (Fin 4 → ℝ)) : ∀ᵐ x : Fin 4 → ℝ, x ∈ Ω → ∀ a : Fin 4,
    (minkowski * (fun _ _ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) a x)ᵀ =
      -(minkowski * (fun _ _ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) a x) :=
  Eventually.of_forall fun _ _ _ => by simp

end Einstein

end RenewalGeometry.MollifiedBianchi
