/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.LpDualityWeakCompactness

/-!
# Distributional curvature `R = dω + ω ∧ ω` and weak curvature compactness
  (`thm:supp-curvature-compactness`; emergent-spacetime manuscript, supplement)

For an `A`-valued one-form `ω = Σ_a ω_a dx^a` on an open set `Ω ⊆ ℝ^d` (`A` a real normed
algebra, e.g. a matrix Lie algebra) with locally square-integrable coefficients, the
distributional curvature `d_dist ω + ω ∧ ω` is tested against Mathlib's smooth compactly
supported test functions `𝓓(Ω, ℝ)`:
`⟨dω + ω ∧ ω, φ⟩_{ab} = -∫ ∂_a φ ω_b + ∫ ∂_b φ ω_a + ∫ φ (ω_a ω_b - ω_b ω_a)`
(`curvaturePairing`).  The distributional derivative includes every interface contribution of a
piecewise connection automatically.

Main results:
* `tendsto_integral_smul_of_L2`, `tendsto_integral_smul_mul_of_L2`: bounded weights against
  strongly `L²`-convergent sequences and products (strong `L²` × strong `L²` → strong `L¹`);
* `tendsto_curvaturePairing`: strong `L²_loc` convergence `ωₙ → ω` passes to the limit in the
  distributional curvature pairing;
* `integral_eq_curvaturePairing_of_tendsto`, `isDistributionalCurvature_of_tendsto`:
  identification `R = dω + ω ∧ ω` from a vanishing distributional residual;
* `FiniteWriterCertificate`, `isDistributionalCurvature_of_finiteWriter`: the finite-writer route
  (Cartan curvature residual `eq:main-cartan-curvature-residual`, incidence discrepancy
  `eq:main-cartan-incidence`, exhaustive determining test banks with interpolation control);
* `curvature_weak_compactness`: **`thm:supp-curvature-compactness`** — on a compact `K ⊆ ℝ^d`
  and for `1 < p < ∞`, uniformly `Lᵖ(K)`-bounded curvatures have a weakly convergent subsequence
  (via `LpDuality.exists_subseq_tendsto_weak_family_vec`), whose limit equals `dω + ω ∧ ω` in
  distributions on `int K` under either identification route.
-/

open MeasureTheory Filter Topology ENNReal TopologicalSpace
open scoped NNReal Distributions

noncomputable section

namespace RenewalGeometry.DistributionalCurvature

set_option linter.unusedSectionVars false

/-! ### Weak–strong limits of bounded-weight integrals on a finite measure space -/

section L2Limits

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- A bounded weight integrated against an `L²`-convergent sequence converges. -/
theorem tendsto_integral_smul_of_L2 {ψ : X → ℝ} (hψ : AEStronglyMeasurable ψ ν) {M : ℝ}
    (hM : ∀ x, ‖ψ x‖ ≤ M) {u : ℕ → X → A} {u' : X → A} (hu : ∀ n, MemLp (u n) 2 ν)
    (hu' : MemLp u' 2 ν) (hlim : Tendsto (fun n => eLpNorm (u n - u') 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ψ x • u n x ∂ν) atTop (𝓝 (∫ x, ψ x • u' x ∂ν)) := by
  have hψ2 : MemLp ψ 2 ν := MemLp.of_bound hψ M (Eventually.of_forall hM)
  let L := ContinuousLinearMap.lpPairing ν 2 2 (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] A →L[ℝ] A)
  have hU : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hu'.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hlim
  have h := ((L (hψ2.toLp ψ)).continuous.tendsto _).comp hU
  have heq : ∀ (v : X → A) (hv : MemLp v 2 ν), L (hψ2.toLp ψ) (hv.toLp v) = ∫ x, ψ x • v x ∂ν := by
    intro v hv
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hψ2.coeFn_toLp, hv.coeFn_toLp] with x h1 h2
    simp [h1, h2]
  rw [heq] at h
  exact h.congr fun n => heq _ _

/-- A bounded weight integrated against a product of two `L²`-convergent sequences converges
(strong `L²` × strong `L²` → strong `L¹`). -/
theorem tendsto_integral_smul_mul_of_L2 {ψ : X → ℝ} (hψ : AEStronglyMeasurable ψ ν) {M : ℝ}
    (hM : ∀ x, ‖ψ x‖ ≤ M) {u v : ℕ → X → A} {u' v' : X → A} (hu : ∀ n, MemLp (u n) 2 ν)
    (hv : ∀ n, MemLp (v n) 2 ν) (hu' : MemLp u' 2 ν) (hv' : MemLp v' 2 ν)
    (hulim : Tendsto (fun n => eLpNorm (u n - u') 2 ν) atTop (𝓝 0))
    (hvlim : Tendsto (fun n => eLpNorm (v n - v') 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ψ x • (u n x * v n x) ∂ν) atTop
      (𝓝 (∫ x, ψ x • (u' x * v' x) ∂ν)) := by
  have hψ : MemLp ψ ∞ ν := memLp_top_of_bound hψ M (Eventually.of_forall hM)
  let H := ContinuousLinearMap.holderL ν 2 2 1 (ContinuousLinearMap.mul ℝ A)
  let L := ContinuousLinearMap.lpPairing ν ∞ 1 (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] A →L[ℝ] A)
  have hU : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hu'.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hulim
  have hV : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hv'.toLp v')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hvlim
  have hW := (H.continuous₂.tendsto (hu'.toLp u', hv'.toLp v')).comp (hU.prodMk_nhds hV)
  have h := ((L (hψ.toLp ψ)).continuous.tendsto _).comp hW
  have heq : ∀ (a b : X → A) (ha : MemLp a 2 ν) (hb : MemLp b 2 ν),
      L (hψ.toLp ψ) (H (ha.toLp a) (hb.toLp b)) = ∫ x, ψ x • (a x * b x) ∂ν := by
    intro a b ha hb
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp, ha.coeFn_toLp, hb.coeFn_toLp,
      ContinuousLinearMap.coeFn_holder (r := 1) (ContinuousLinearMap.mul ℝ A) (ha.toLp a)
        (hb.toLp b)] with x h1 h2 h3 h4
    simp only [H, ContinuousLinearMap.holderL_apply_apply] at *
    rw [h4, h1, h2, h3]
    simp
  simp only [Function.comp_def, Function.uncurry_apply_pair] at h
  rw [heq] at h
  exact h.congr fun n => heq _ _ _ _

end L2Limits


/-! ### Test functions, distributional derivatives and the curvature pairing -/

section Distributions

variable {d : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The partial derivative `∂_a φ = Dφ(x) e_a` of a function on `ℝ^d`. -/
def pderiv (a : Fin d) (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  fderiv ℝ φ x (Pi.single a 1)

/-- The distributional pairing `⟨dω + ω ∧ ω, φ⟩_{ab}` of an `A`-valued one-form
`ω = Σ_a ω_a dx^a` (locally square integrable) with a scalar test function `φ`:
`(dω)_{ab} = ∂_a ω_b - ∂_b ω_a` acts by `-∫ ∂_a φ ω_b + ∫ ∂_b φ ω_a`, and
`(ω ∧ ω)_{ab} = ω_a ω_b - ω_b ω_a`. -/
def curvaturePairing (ω : Fin d → (Fin d → ℝ) → A) (φ : (Fin d → ℝ) → ℝ) (a b : Fin d) : A :=
  -(∫ x, pderiv a φ x • ω b x) + (∫ x, pderiv b φ x • ω a x) +
    (∫ x, φ x • (ω a x * ω b x)) - ∫ x, φ x • (ω b x * ω a x)

/-- `R = dω + ω ∧ ω` in the sense of distributions on the open set `Ω`: for every smooth
compactly supported test function `φ ∈ 𝓓(Ω, ℝ)` and every pair of form indices,
`∫ φ R_{ab} = ⟨dω + ω ∧ ω, φ⟩_{ab}`. -/
def IsDistributionalCurvature (Ω : Opens (Fin d → ℝ)) (ω : Fin d → (Fin d → ℝ) → A)
    (R : Fin d → Fin d → (Fin d → ℝ) → A) : Prop :=
  ∀ φ : 𝓓(Ω, ℝ), ∀ a b, ∫ x, φ x • R a b x = curvaturePairing ω φ a b

/-- Strong `L²_loc(Ω)` convergence of one-forms: every component is square integrable on every
compact subset of `Ω`, and converges there in `L²`. -/
structure StrongL2LocTendsto (Ω : Opens (Fin d → ℝ)) (ω : ℕ → Fin d → (Fin d → ℝ) → A)
    (ω' : Fin d → (Fin d → ℝ) → A) : Prop where
  memLp : ∀ n a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (ω n a) 2 (volume.restrict C)
  memLp_lim : ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (ω' a) 2 (volume.restrict C)
  tendsto : ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
    Tendsto (fun n => eLpNorm (ω n a - ω' a) 2 (volume.restrict C)) atTop (𝓝 0)

theorem StrongL2LocTendsto.comp {Ω : Opens (Fin d → ℝ)} {ω : ℕ → Fin d → (Fin d → ℝ) → A}
    {ω' : Fin d → (Fin d → ℝ) → A} (h : StrongL2LocTendsto Ω ω ω') {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : StrongL2LocTendsto Ω (fun n => ω (φ n)) ω' where
  memLp n a C hC hCΩ := h.memLp (φ n) a C hC hCΩ
  memLp_lim := h.memLp_lim
  tendsto a C hC hCΩ := (h.tendsto a C hC hCΩ).comp hφ.tendsto_atTop

theorem exists_bound_of_eq_zero_off {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    {C : Set (Fin d → ℝ)} (hC : IsCompact C) (hz : ∀ x, x ∉ C → f x = 0) :
    ∃ M, ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, fun x => ?_⟩
  by_cases hx : x ∈ C
  · exact (hM x hx).trans (le_max_left _ _)
  · rw [hz x hx, norm_zero]; exact le_max_right _ _

theorem test_eq_zero_off {Ω : Opens (Fin d → ℝ)} (φ : 𝓓(Ω, ℝ)) {x : Fin d → ℝ}
    (hx : x ∉ tsupport φ) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport hx

theorem pderiv_eq_zero_off {Ω : Opens (Fin d → ℝ)} (φ : 𝓓(Ω, ℝ)) (a : Fin d)
    {x : Fin d → ℝ} (hx : x ∉ tsupport φ) : pderiv a φ x = 0 := by
  have : fderiv ℝ φ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_fderiv_subset ℝ h)
  simp [pderiv, this]

theorem continuous_pderiv {Ω : Opens (Fin d → ℝ)} (φ : 𝓓(Ω, ℝ)) (a : Fin d) :
    Continuous (pderiv a φ) := by
  have h1 : Continuous (fderiv ℝ φ) :=
    φ.contDiff.continuous_fderiv (by simp)
  exact h1.clm_apply continuous_const

/-- **Weak–strong passage in the curvature pairing.**  If `ωₙ → ω'` strongly in `L²_loc(Ω)`,
then `⟨dωₙ + ωₙ ∧ ωₙ, φ⟩ → ⟨dω' + ω' ∧ ω', φ⟩` for every test function `φ ∈ 𝓓(Ω, ℝ)`. -/
theorem tendsto_curvaturePairing {Ω : Opens (Fin d → ℝ)} {ω : ℕ → Fin d → (Fin d → ℝ) → A}
    {ω' : Fin d → (Fin d → ℝ) → A} (h : StrongL2LocTendsto Ω ω ω') (φ : 𝓓(Ω, ℝ))
    (a b : Fin d) :
    Tendsto (fun n => curvaturePairing (ω n) φ a b) atTop (𝓝 (curvaturePairing ω' φ a b)) := by
  set C := tsupport (φ : (Fin d → ℝ) → ℝ)
  have hC : IsCompact C := φ.hasCompactSupport
  have hCΩ : C ⊆ Ω := φ.tsupport_subset
  have : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hloc : ∀ (ψ : (Fin d → ℝ) → ℝ) (F : (Fin d → ℝ) → A), (∀ x, x ∉ C → ψ x = 0) →
      ∫ x, ψ x • F x = ∫ x in C, ψ x • F x := fun ψ F hψ =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hψ x hx, zero_smul]).symm
  obtain ⟨M0, hM0⟩ := exists_bound_of_eq_zero_off φ.continuous hC fun x hx =>
    test_eq_zero_off φ hx
  have hd : ∀ c, ∃ M, ∀ x, ‖pderiv c φ x‖ ≤ M := fun c =>
    exists_bound_of_eq_zero_off (continuous_pderiv φ c) hC fun x hx => pderiv_eq_zero_off φ c hx
  obtain ⟨Ma, hMa⟩ := hd a
  obtain ⟨Mb, hMb⟩ := hd b
  have hω := fun c n => h.memLp n c C hC hCΩ
  have hω' := fun c => h.memLp_lim c C hC hCΩ
  have hlim := fun c => h.tendsto c C hC hCΩ
  have t1 := tendsto_integral_smul_of_L2 (continuous_pderiv φ a).aestronglyMeasurable hMa
    (hω b) (hω' b) (hlim b)
  have t2 := tendsto_integral_smul_of_L2 (continuous_pderiv φ b).aestronglyMeasurable hMb
    (hω a) (hω' a) (hlim a)
  have t3 := tendsto_integral_smul_mul_of_L2 φ.continuous.aestronglyMeasurable hM0
    (hω a) (hω b) (hω' a) (hω' b) (hlim a) (hlim b)
  have t4 := tendsto_integral_smul_mul_of_L2 φ.continuous.aestronglyMeasurable hM0
    (hω b) (hω a) (hω' b) (hω' a) (hlim b) (hlim a)
  have hza : ∀ c, ∀ x, x ∉ C → pderiv c φ x = 0 := fun c x hx => pderiv_eq_zero_off φ c hx
  have hz0 : ∀ x, x ∉ C → φ x = 0 := fun x hx => test_eq_zero_off φ hx
  unfold curvaturePairing
  simp only [hloc _ _ (hza a), hloc _ _ (hza b), hloc _ _ hz0]
  exact ((t1.neg.add t2).add t3).sub t4

/-- **Identification of the distributional curvature from a vanishing residual.**  Suppose
`∫ φ Rₙ → ∫ φ R` for a test function `φ`, `ωₙ → ω'` strongly in `L²_loc(Ω)`, and the tested
residual `∫ φ Rₙ - ⟨dωₙ + ωₙ ∧ ωₙ, φ⟩` tends to zero.  Then `∫ φ R = ⟨dω' + ω' ∧ ω', φ⟩`. -/
theorem integral_eq_curvaturePairing_of_tendsto {Ω : Opens (Fin d → ℝ)}
    {ω : ℕ → Fin d → (Fin d → ℝ) → A} {ω' : Fin d → (Fin d → ℝ) → A}
    (h : StrongL2LocTendsto Ω ω ω') (R : ℕ → Fin d → Fin d → (Fin d → ℝ) → A)
    (Rlim : Fin d → Fin d → (Fin d → ℝ) → A) (φ : 𝓓(Ω, ℝ)) (a b : Fin d)
    (hR : Tendsto (fun n => ∫ x, φ x • R n a b x) atTop (𝓝 (∫ x, φ x • Rlim a b x)))
    (hres : Tendsto (fun n => (∫ x, φ x • R n a b x) - curvaturePairing (ω n) φ a b) atTop
      (𝓝 0)) :
    ∫ x, φ x • Rlim a b x = curvaturePairing ω' φ a b := by
  have := hres.add (tendsto_curvaturePairing h φ a b)
  simp only [zero_add] at this
  have h2 : Tendsto (fun n => ∫ x, φ x • R n a b x) atTop (𝓝 (curvaturePairing ω' φ a b)) :=
    this.congr fun n => sub_add_cancel _ _
  exact tendsto_nhds_unique hR h2

/-- Distributional form of `integral_eq_curvaturePairing_of_tendsto`. -/
theorem isDistributionalCurvature_of_tendsto {Ω : Opens (Fin d → ℝ)}
    {ω : ℕ → Fin d → (Fin d → ℝ) → A} {ω' : Fin d → (Fin d → ℝ) → A}
    (h : StrongL2LocTendsto Ω ω ω') (R : ℕ → Fin d → Fin d → (Fin d → ℝ) → A)
    (Rlim : Fin d → Fin d → (Fin d → ℝ) → A)
    (hR : ∀ φ : 𝓓(Ω, ℝ), ∀ a b,
      Tendsto (fun n => ∫ x, φ x • R n a b x) atTop (𝓝 (∫ x, φ x • Rlim a b x)))
    (hres : ∀ φ : 𝓓(Ω, ℝ), ∀ a b,
      Tendsto (fun n => (∫ x, φ x • R n a b x) - curvaturePairing (ω n) φ a b) atTop (𝓝 0)) :
    IsDistributionalCurvature Ω ω' Rlim := fun φ a b =>
  integral_eq_curvaturePairing_of_tendsto h R Rlim φ a b (hR φ a b) (hres φ a b)

end Distributions




/-! ### The finite-writer route (`eq:main-cartan-curvature-residual`, `eq:main-cartan-incidence`) -/

section FiniteWriter

variable {d : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Uniform convergence of weights supported in a fixed compact set passes through integrals
against a function integrable on that set. -/
theorem tendsto_integral_smul_of_tendstoUniformly {C : Set (Fin d → ℝ)}
    {f : ℕ → (Fin d → ℝ) → ℝ} {g : (Fin d → ℝ) → ℝ} (hf : TendstoUniformly f g atTop)
    (hfc : ∀ k, Continuous (f k)) {M : ℝ} (hg : ∀ x, ‖g x‖ ≤ M)
    (hfC : ∀ k x, x ∉ C → f k x = 0) (hgC : ∀ x, x ∉ C → g x = 0)
    (F : (Fin d → ℝ) → A) (hF : IntegrableOn F C) :
    Tendsto (fun k => ∫ x, f k x • F x) atTop (𝓝 (∫ x, g x • F x)) := by
  have hloc : ∀ (ψ : (Fin d → ℝ) → ℝ), (∀ x, x ∉ C → ψ x = 0) →
      ∫ x, ψ x • F x = ∫ x in C, ψ x • F x := fun ψ hψ =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hψ x hx, zero_smul]).symm
  simp only [hloc _ (hfC _), hloc _ hgC]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => (M + 1) * ‖F x‖)
    (Eventually.of_forall fun k => (hfc k).aestronglyMeasurable.smul hF.1)
    ?_ (hF.norm.const_mul _) (Eventually.of_forall fun x => ((hf.tendsto_at x).smul_const _))
  filter_upwards [(Metric.tendstoUniformly_iff.1 hf) 1 one_pos] with k hk
  refine Eventually.of_forall fun x => ?_
  rw [norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h1 := hk x
  rw [Real.dist_eq] at h1
  have h2 := hg x
  rw [Real.norm_eq_abs] at h2 ⊢
  have : |f k x| ≤ |g x| + |g x - f k x| := by
    calc |f k x| = |g x - (g x - f k x)| := by ring_nf
      _ ≤ |g x| + |g x - f k x| := abs_sub _ _
  linarith

theorem tendsto_curvaturePairing_of_C1 {Ω : Opens (Fin d → ℝ)} {ω' : Fin d → (Fin d → ℝ) → A}
    (hω' : ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (ω' a) 2 (volume.restrict C))
    {C : Set (Fin d → ℝ)} (hC : IsCompact C) (hCΩ : C ⊆ Ω) (θ : ℕ → 𝓓(Ω, ℝ)) (ψ : 𝓓(Ω, ℝ))
    (hθC : ∀ k, tsupport (θ k : (Fin d → ℝ) → ℝ) ⊆ C)
    (hθ : TendstoUniformly (fun k => ⇑(θ k)) ψ atTop)
    (hθd : ∀ a, TendstoUniformly (fun k => pderiv a (θ k)) (pderiv a ψ) atTop) (a b : Fin d) :
    Tendsto (fun k => curvaturePairing ω' (θ k) a b) atTop (𝓝 (curvaturePairing ω' ψ a b)) := by
  have : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hθz : ∀ k x, x ∉ C → θ k x = 0 := fun k x hx =>
    test_eq_zero_off (θ k) fun h => hx (hθC k h)
  have hψz : ∀ x, x ∉ C → ψ x = 0 := fun x hx =>
    tendsto_nhds_unique (hθ.tendsto_at x) (by simp [hθz _ x hx])
  have hθdz : ∀ c k x, x ∉ C → pderiv c (θ k) x = 0 := fun c k x hx =>
    pderiv_eq_zero_off (θ k) c fun h => hx (hθC k h)
  have hψdz : ∀ c x, x ∉ C → pderiv c ψ x = 0 := fun c x hx =>
    tendsto_nhds_unique ((hθd c).tendsto_at x) (by simp [hθdz c _ x hx])
  have hL1 : ∀ c, IntegrableOn (ω' c) C := fun c =>
    (hω' c C hC hCΩ).integrable (by norm_num)
  have hL1mul : ∀ c e, IntegrableOn (fun x => ω' c x * ω' e x) C := fun c e =>
    ((hω' e C hC hCΩ).mul (hω' c C hC hCΩ) (r := 1)).integrable le_rfl
  obtain ⟨M0, hM0⟩ := exists_bound_of_eq_zero_off ψ.continuous ψ.hasCompactSupport
    fun x hx => test_eq_zero_off ψ hx
  have hd : ∀ c, ∃ M, ∀ x, ‖pderiv c ψ x‖ ≤ M := fun c =>
    exists_bound_of_eq_zero_off (continuous_pderiv ψ c) ψ.hasCompactSupport
      fun x hx => pderiv_eq_zero_off ψ c hx
  obtain ⟨Ma, hMa⟩ := hd a
  obtain ⟨Mb, hMb⟩ := hd b
  have t1 := tendsto_integral_smul_of_tendstoUniformly (hθd a)
    (fun k => continuous_pderiv (θ k) a) hMa (hθdz a) (hψdz a) (ω' b) (hL1 b)
  have t2 := tendsto_integral_smul_of_tendstoUniformly (hθd b)
    (fun k => continuous_pderiv (θ k) b) hMb (hθdz b) (hψdz b) (ω' a) (hL1 a)
  have t3 := tendsto_integral_smul_of_tendstoUniformly hθ (fun k => (θ k).continuous) hM0
    hθz hψz (fun x => ω' a x * ω' b x) (hL1mul a b)
  have t4 := tendsto_integral_smul_of_tendstoUniformly hθ (fun k => (θ k).continuous) hM0
    hθz hψz (fun x => ω' b x * ω' a x) (hL1mul b a)
  unfold curvaturePairing
  exact ((t1.neg.add t2).add t3).sub t4

/-- **Finite-writer certificate** (`eq:main-cartan-curvature-residual`,
`eq:main-cartan-incidence`) for a sequence of curvatures `Rₙ` and connections `ωₙ` on `Ω`:
* `W n = 𝓡ₙ(ωₙ)` is the finite Cartan writer and `T n` the finite test bank;
* the Cartan curvature residual `𝔠ₙ` tends to zero: `‖∫ Φ • (Rₙ - Wₙ)‖ ≤ 𝔠ₙ ‖Φ‖_{L²}` for
  `Φ ∈ Tₙ`, `𝔠ₙ → 0`;
* the banks exhaust a determining core `D ⊆ 𝓓(Ω, ℝ)` with vanishing test-interpolation errors:
  every `ψ ∈ D` is represented by bank tests `Φₙ ∈ Tₙ` (eventually) of bounded `L²` norm whose
  tested residuals differ from that of `ψ` by a vanishing amount;
* the incidence discrepancy `𝔍ₙ(ψ) = ∫ ψ • Wₙ - ⟨d_dist ωₙ + ωₙ ∧ ωₙ, ψ⟩` tends to zero on `D`;
* `D` is determining: every test function is a `C¹`-uniform limit of elements of `D` supported
  in a fixed compact subset of `Ω`. -/
structure FiniteWriterCertificate (Ω : Opens (Fin d → ℝ)) (ω : ℕ → Fin d → (Fin d → ℝ) → A)
    (R : ℕ → Fin d → Fin d → (Fin d → ℝ) → A) where
  /-- The finite Cartan writer `𝓡ₙ(ωₙ)`. -/
  W : ℕ → Fin d → Fin d → (Fin d → ℝ) → A
  /-- The finite test banks. -/
  T : ℕ → Set ((Fin d → ℝ) → ℝ)
  /-- The Cartan curvature residual `𝔠ₙ`. -/
  c : ℕ → ℝ
  tendsto_c : Tendsto c atTop (𝓝 0)
  cartan : ∀ n, ∀ Φ ∈ T n, ∀ a b,
    ‖(∫ x, Φ x • R n a b x) - ∫ x, Φ x • W n a b x‖ ≤ c n * (eLpNorm Φ 2 volume).toReal
  /-- The determining smooth core. -/
  D : Set 𝓓(Ω, ℝ)
  interp : ∀ ψ ∈ D, ∃ Φ : ℕ → (Fin d → ℝ) → ℝ, (∀ᶠ n in atTop, Φ n ∈ T n) ∧
    (∃ L, ∀ n, (eLpNorm (Φ n) 2 volume).toReal ≤ L) ∧ ∀ a b,
      Tendsto (fun n => ((∫ x, ψ x • R n a b x) - ∫ x, ψ x • W n a b x) -
        ((∫ x, Φ n x • R n a b x) - ∫ x, Φ n x • W n a b x)) atTop (𝓝 0)
  incidence : ∀ ψ ∈ D, ∀ a b,
    Tendsto (fun n => (∫ x, ψ x • W n a b x) - curvaturePairing (ω n) ψ a b) atTop (𝓝 0)
  dense : ∀ ψ : 𝓓(Ω, ℝ), ∃ C : Set (Fin d → ℝ), IsCompact C ∧ C ⊆ Ω ∧
    ∃ θ : ℕ → 𝓓(Ω, ℝ), (∀ k, θ k ∈ D ∧ tsupport (θ k : (Fin d → ℝ) → ℝ) ⊆ C) ∧
      TendstoUniformly (fun k => ⇑(θ k)) ψ atTop ∧
      ∀ a, TendstoUniformly (fun k => pderiv a (θ k)) (pderiv a ψ) atTop

/-- A finite-writer certificate restricts to every subsequence. -/
def FiniteWriterCertificate.comp {Ω : Opens (Fin d → ℝ)} {ω : ℕ → Fin d → (Fin d → ℝ) → A}
    {R : ℕ → Fin d → Fin d → (Fin d → ℝ) → A} (H : FiniteWriterCertificate Ω ω R)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    FiniteWriterCertificate Ω (fun n => ω (φ n)) (fun n => R (φ n)) where
  W n := H.W (φ n)
  T n := H.T (φ n)
  c n := H.c (φ n)
  tendsto_c := H.tendsto_c.comp hφ.tendsto_atTop
  cartan n := H.cartan (φ n)
  D := H.D
  interp ψ hψ := by
    obtain ⟨Φ, hΦ, hL, he⟩ := H.interp ψ hψ
    exact ⟨fun n => Φ (φ n), hφ.tendsto_atTop.eventually hΦ,
      hL.imp fun L hL n => hL (φ n), fun a b => (he a b).comp hφ.tendsto_atTop⟩
  incidence ψ hψ a b := (H.incidence ψ hψ a b).comp hφ.tendsto_atTop
  dense := H.dense

/-- **Finite-writer identification** (last clause of `thm:supp-curvature-compactness`): a
finite-writer certificate, distributional convergence `Rₙ → R` with `R ∈ L¹_loc(Ω)`, and strong
`L²_loc(Ω)` convergence `ωₙ → ω` give `R = dω + ω ∧ ω` in distributions on `Ω`. -/
theorem isDistributionalCurvature_of_finiteWriter {Ω : Opens (Fin d → ℝ)}
    {ω : ℕ → Fin d → (Fin d → ℝ) → A} {ω' : Fin d → (Fin d → ℝ) → A}
    (hω : StrongL2LocTendsto Ω ω ω') (R : ℕ → Fin d → Fin d → (Fin d → ℝ) → A)
    (Rlim : Fin d → Fin d → (Fin d → ℝ) → A)
    (hR : ∀ ψ : 𝓓(Ω, ℝ), ∀ a b,
      Tendsto (fun n => ∫ x, ψ x • R n a b x) atTop (𝓝 (∫ x, ψ x • Rlim a b x)))
    (hRlim : ∀ a b (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → IntegrableOn (Rlim a b) C)
    (H : FiniteWriterCertificate Ω ω R) :
    IsDistributionalCurvature Ω ω' Rlim := by
  -- Step 1: the identity on the determining core.
  have hcore : ∀ ψ ∈ H.D, ∀ a b, ∫ x, ψ x • Rlim a b x = curvaturePairing ω' ψ a b := by
    intro ψ hψ a b
    apply integral_eq_curvaturePairing_of_tendsto hω R Rlim ψ a b (hR ψ a b)
    obtain ⟨Φ, hΦT, ⟨L, hL⟩, he⟩ := H.interp ψ hψ
    have hbank : Tendsto (fun n => (∫ x, Φ n x • R n a b x) - ∫ x, Φ n x • H.W n a b x) atTop
        (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hcL : Tendsto (fun n => |H.c n| * L) atTop (𝓝 0) := by
        simpa using (H.tendsto_c.abs.mul_const L)
      refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hcL
      filter_upwards [hΦT] with n hn
      refine (H.cartan n (Φ n) hn a b).trans ?_
      calc H.c n * (eLpNorm (Φ n) 2 volume).toReal
          ≤ |H.c n| * (eLpNorm (Φ n) 2 volume).toReal :=
            mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg
        _ ≤ |H.c n| * L := mul_le_mul_of_nonneg_left (hL n) (abs_nonneg _)
    have := ((he a b).add hbank).add (H.incidence ψ hψ a b)
    simp only [add_zero] at this
    exact this.congr fun n => by abel
  -- Step 2: extension by `C¹`-uniform density.
  intro ψ a b
  obtain ⟨C, hC, hCΩ, θ, hθ, hθu, hθd⟩ := H.dense ψ
  have hθz : ∀ k x, x ∉ C → θ k x = 0 := fun k x hx =>
    test_eq_zero_off (θ k) fun h => hx ((hθ k).2 h)
  have hψz : ∀ x, x ∉ C → ψ x = 0 := fun x hx =>
    tendsto_nhds_unique (hθu.tendsto_at x) (by simp [hθz _ x hx])
  obtain ⟨M0, hM0⟩ := exists_bound_of_eq_zero_off ψ.continuous ψ.hasCompactSupport
    fun x hx => test_eq_zero_off ψ hx
  have hl := tendsto_integral_smul_of_tendstoUniformly hθu (fun k => (θ k).continuous) hM0
    hθz hψz (Rlim a b) (hRlim a b C hC hCΩ)
  have hr := tendsto_curvaturePairing_of_C1 hω.memLp_lim hC hCΩ θ ψ (fun k => (hθ k).2) hθu hθd a b
  have heq : (fun k => ∫ x, θ k x • Rlim a b x) = fun k => curvaturePairing ω' (θ k) a b :=
    funext fun k => hcore (θ k) (hθ k).1 a b
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr

end FiniteWriter

/-! ### Weak curvature compactness on a compact cylinder (`thm:supp-curvature-compactness`) -/

section Compactness

variable {d : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

/-- The interior of a set, as an open set. -/
def interiorOpens (K : Set (Fin d → ℝ)) : Opens (Fin d → ℝ) := ⟨interior K, isOpen_interior⟩

theorem test_integral_eq_setIntegral {K : Set (Fin d → ℝ)} (ψ : 𝓓(interiorOpens K, ℝ))
    (F : (Fin d → ℝ) → A) : ∫ x, ψ x • F x = ∫ x in K, ψ x • F x := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  have : x ∉ tsupport ψ := fun h => hx (interior_subset (ψ.tsupport_subset h))
  rw [test_eq_zero_off ψ this, zero_smul]

theorem test_memLp {K : Set (Fin d → ℝ)} (ψ : 𝓓(interiorOpens K, ℝ)) (q : ℝ≥0∞)
    [IsFiniteMeasure (volume.restrict K)] : MemLp ψ q (volume.restrict K) := by
  obtain ⟨M, hM⟩ := exists_bound_of_eq_zero_off ψ.continuous ψ.hasCompactSupport
    fun x hx => test_eq_zero_off ψ hx
  exact MemLp.of_bound ψ.continuous.aestronglyMeasurable M (Eventually.of_forall hM)

/-- **Weak curvature compactness with an identified connection limit**
(`thm:supp-curvature-compactness`, clauses `eq:supp-curvature-lp-bound`,
`eq:supp-curvature-reflexive-limit`, `eq:supp-curvature-identification`).

Let `K ⊆ ℝ^d` be compact, `1 < p < ∞`, and let `Rₙ` be `A`-valued two-forms (components
`R_{ab}`, `A` a finite-dimensional real normed algebra, e.g. a matrix Lie algebra) uniformly
bounded in `Lᵖ(K)`.  Then along a subsequence `Rₙ ⇀ R` weakly in `Lᵖ(K)` (tested against every
`h ∈ L^q(K)`), and for every sequence of one-forms `ωₙ → ω` strongly in `L²_loc(int K)` whose
tested residual `Rₙ - [d_dist ωₙ + ωₙ ∧ ωₙ]` tends to zero in distributions on `int K`,
`R = dω + ω ∧ ω` in distributions on `int K`. -/
theorem curvature_weak_compactness
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] (hp : p ≠ ∞) (hq : q ≠ ∞)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (R : ℕ → Fin d → Fin d → (Fin d → ℝ) → A)
    (hRmem : ∀ n a b, MemLp (R n a b) p (volume.restrict K)) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hRbd : ∀ n a b, eLpNorm (R n a b) p (volume.restrict K) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Rlim : Fin d → Fin d → (Fin d → ℝ) → A,
      (∀ a b, MemLp (Rlim a b) p (volume.restrict K)) ∧
      (∀ a b (h : (Fin d → ℝ) → ℝ), MemLp h q (volume.restrict K) →
        Tendsto (fun n => ∫ x in K, h x • R (φ n) a b x) atTop
          (𝓝 (∫ x in K, h x • Rlim a b x))) ∧
      (∀ (ω : ℕ → Fin d → (Fin d → ℝ) → A) (ω' : Fin d → (Fin d → ℝ) → A),
        StrongL2LocTendsto (interiorOpens K) ω ω' →
        (∀ ψ : 𝓓(interiorOpens K, ℝ), ∀ a b,
          Tendsto (fun n => (∫ x, ψ x • R n a b x) - curvaturePairing (ω n) ψ a b) atTop
            (𝓝 0)) →
        IsDistributionalCurvature (interiorOpens K) ω' Rlim) ∧
      ∀ (ω : ℕ → Fin d → (Fin d → ℝ) → A) (ω' : Fin d → (Fin d → ℝ) → A),
        StrongL2LocTendsto (interiorOpens K) ω ω' →
        FiniteWriterCertificate (interiorOpens K) ω R →
        IsDistributionalCurvature (interiorOpens K) ω' Rlim := by
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  obtain ⟨φ, hφ, G, hG⟩ := LpDuality.exists_subseq_tendsto_weak_family_vec (μ := volume.restrict K)
    hp hq (ι := Fin d × Fin d) (fun ab n => R n ab.1 ab.2) (fun ab n => hRmem n ab.1 ab.2) hB
    (fun ab n => hRbd n ab.1 ab.2)
  have hRw : ∀ ψ : 𝓓(interiorOpens K, ℝ), ∀ a b, Tendsto (fun n => ∫ x, ψ x • R (φ n) a b x)
      atTop (𝓝 (∫ x, ψ x • G (a, b) x)) := by
    intro ψ a b
    simp only [test_integral_eq_setIntegral ψ]
    exact (hG (a, b)).2 ψ (test_memLp ψ q)
  refine ⟨φ, hφ, fun a b => G (a, b), fun a b => (hG (a, b)).1,
    fun a b h hh => (hG (a, b)).2 h hh, fun ω ω' hω hres => ?_, fun ω ω' hω H => ?_⟩
  · exact isDistributionalCurvature_of_tendsto (hω.comp hφ) (fun n => R (φ n))
      (fun a b => G (a, b)) hRw (fun ψ a b => (hres ψ a b).comp hφ.tendsto_atTop)
  · refine isDistributionalCurvature_of_finiteWriter (hω.comp hφ) (fun n => R (φ n))
      (fun a b => G (a, b)) hRw (fun a b C _ hCΩ => ?_) (H.comp hφ)
    have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
    exact IntegrableOn.mono_set ((hG (a, b)).1.integrable hp1) (hCΩ.trans interior_subset)

/-- Zero one-forms converge strongly in `L²_loc` (used in the non-vacuity check). -/
theorem strongL2LocTendsto_zero (Ω : Opens (Fin d → ℝ)) :
    StrongL2LocTendsto Ω (fun _ _ _ => (0 : A)) (fun _ _ => 0) where
  memLp _ _ _ _ _ := MemLp.zero'
  memLp_lim _ _ _ _ := MemLp.zero'
  tendsto _ _ _ _ := by simp

/-- Non-vacuity of `curvature_weak_compactness`: the zero curvature sequence on the unit cube in
`ℝ⁴`, with `p = q = 2`, satisfies all hypotheses, and the zero connection identifies the limit. -/
example : ∃ Rlim : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℝ,
    IsDistributionalCurvature (interiorOpens (Set.Icc (0 : Fin 4 → ℝ) 1)) (fun _ _ => 0) Rlim := by
  obtain ⟨φ, -, Rlim, -, -, hid, -⟩ := curvature_weak_compactness (A := ℝ) (p := 2) (q := 2)
    (by norm_num) (by norm_num) (isCompact_Icc) (fun _ _ _ _ => 0) (fun _ _ _ => MemLp.zero')
    (B := 0) (by norm_num) (fun _ _ _ => by simp)
  refine ⟨Rlim, hid _ _ (strongL2LocTendsto_zero _) fun ψ a b => ?_⟩
  simp [curvaturePairing]

end Compactness

end RenewalGeometry.DistributionalCurvature
