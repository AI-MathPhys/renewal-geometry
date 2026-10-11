/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientMatterEquations
import RenewalGeometry.Gravity.BosonicStressDefectBox

/-!
# `thm:critical-quotient-defect`: the metric equation with the bosonic stress defects
  (Einstein–Standard-Model action-closure manuscript)

On a Coulomb cube `Q = box lo hi` (closed cube `Q̄ = Icc lo hi`, reference measure `V0`: Lebesgue
measure of `Q` pulled back), the gauge-transformed critical fields have three weak quadratic packets:
the curvature `F_h`, the covariant Higgs gradient `K_h = D_{A_h}H_h` and the quartic packet
`|H_h|² - v_h²`.  By `lem:positive-packet-defect` (`QuadraticPacketDefect.exists_isDefect`) they
have, after extraction, matrix covariance measures `𝖰_F`, `𝖰_K`, `𝖰_Y` (`IsDefect`).

**`cube_einstein_equation`**: if the coframes converge uniformly (the `L^∞` part of (Q1)) and the
first variations along every fixed test tend to zero (pulled-back equivariant budgets), then for
every smooth test `v` supported in `Q` (metric tests included)
`∫_Q Cov_{θ₀}(j L)(j¹ v) + 𝖰_F(B^{YM}[k]) + 𝖰_K(B^H[k]) + 𝖰_Y(B^V[k]) = 0`,
the coefficient fields `B[k]` being the metric variations of the Yang–Mills (with the gauge
couplings), Higgs-kinetic and potential (with `λ`) densities at the continuous representative of
the limit coframe in the direction of the metric lift of `k`: this is
`eq:critical-quotient-einstein` in the first-variation (Hilbert) normalisation, with
`𝔖_YM = B^{YM} : 𝖰_F` and `𝔖_H = B^H : 𝖰_K + B^V : 𝖰_Y` (the last term is `-λ g ν_H`, `ν_H = 𝖰_Y`
the quartic concentration measure).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.CriticalQuotientRows

open SobolevOpen CriticalGauge CriticalQuotient CriticalQuotientClosure
  BallAnalysis.SMGaugeStructure SMGaugeLie EinsteinSM SMGaugeJet FirstVariationCalculus
  QuadraticPacketDefect BosonicStressDefectBox

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ### Packets of finite-dimensional fields in basis coordinates -/

section Packets

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Index set of the coordinates of `V` in its standard finite basis. -/
abbrev PIdx (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :=
  Fin (Module.finrank ℝ V)

/-- The `i`-th coordinate functional. -/
def coordL (i : PIdx V) : V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℝ V).coord i)

theorem coordL_apply (i : PIdx V) (w : V) : coordL i w = (Module.finBasis ℝ V).repr w i := by
  simp [coordL]

/-- The coefficient matrix of a bilinear form in the basis. -/
def coefMat (β : V →L[ℝ] V →L[ℝ] ℝ) : PIdx V → PIdx V → ℝ :=
  fun i j => β (Module.finBasis ℝ V i) (Module.finBasis ℝ V j)

theorem qf_coefMat (β : V →L[ℝ] V →L[ℝ] ℝ) (w : V) :
    qf (coefMat β) (fun i => coordL i w) = β w w := by
  rw [bilin_basis_expand β w w]
  simp only [qf, coefMat, coordL_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem continuous_coefMat : Continuous (coefMat (V := V)) :=
  continuous_pi fun i => continuous_pi fun j =>
    (ContinuousLinearMap.apply ℝ ℝ (Module.finBasis ℝ V j)).continuous.comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (Module.finBasis ℝ V i)).continuous

/-- `coefMat` as a continuous map. -/
def coefMatC : C(V →L[ℝ] V →L[ℝ] ℝ, PIdx V → PIdx V → ℝ) := ⟨coefMat, continuous_coefMat⟩

/-- The coefficient field of a continuous field of bilinear forms. -/
def coefField {K : Type*} [TopologicalSpace K] (β : C(K, V →L[ℝ] V →L[ℝ] ℝ)) :
    C(K, PIdx V → PIdx V → ℝ) :=
  coefMatC.comp β

theorem coefField_apply {K : Type*} [TopologicalSpace K] (β : C(K, V →L[ℝ] V →L[ℝ] ℝ)) (y : K) :
    coefField β y = coefMat (β y) := rfl

theorem tendsto_coefField {K : Type*} [TopologicalSpace K] {β : ℕ → C(K, V →L[ℝ] V →L[ℝ] ℝ)}
    {β₀ : C(K, V →L[ℝ] V →L[ℝ] ℝ)} (h : Tendsto β atTop (𝓝 β₀)) :
    Tendsto (fun n => coefField (β n)) atTop (𝓝 (coefField β₀)) :=
  ((ContinuousMap.continuous_postcomp (coefMatC (V := V))).tendsto β₀).comp h

variable {lo hi : E4}

/-- The coordinate packet of a field `W : Q → V`, pulled back to the closed cube. -/
def pk (lo hi : E4) (W : E4 → V) : PIdx V → Icc lo hi → ℝ := fun i y => coordL i (W y.val)

/-- Weak `L²(Q)` convergence of a `V`-valued field gives weak `L²(V0)` convergence of its
coordinate packet on the closed cube. -/
theorem weakL2_pk {W : ℕ → E4 → V} {W₀ : E4 → V} (h : WeakL2Data lo hi W W₀) :
    WeakL2 (V0 lo hi) (fun n => pk lo hi (W n)) (pk lo hi W₀) := by
  obtain ⟨h1, h2, -, h4⟩ := h
  exact weakL2_comp (emb lo hi) (map_V0 lo hi) (Y := fun n i x => coordL i (W n x))
    (Y₀ := fun i x => coordL i (W₀ x)) (fun n i => (coordL i).comp_memLp' (h1 n))
    (fun i => (coordL i).comp_memLp' h2) (fun i v hv => h4 (coordL i) v hv)

/-- **The packet pairing is the box integral of the bilinear density.** -/
theorem quadCLM_pk {W : E4 → V} (hW : ∀ i, MemLp (pk lo hi W i) 2 (V0 lo hi))
    (β : C(Icc lo hi, V →L[ℝ] V →L[ℝ] ℝ)) (βE : E4 → V →L[ℝ] V →L[ℝ] ℝ)
    (hβ : ∀ y, β y = βE y.val) :
    quadCLM (V0 lo hi) (pk lo hi W) (coefField β) =
      ∫ x, βE x (W x) (W x) ∂(volume.restrict (box lo hi)) := by
  rw [quadCLM_apply hW]
  have e : ∀ y : Icc lo hi, qf (coefField β y) (fun i => pk lo hi W i y) =
      (fun x => βE x (W x) (W x)) y.val := fun y => by
    rw [coefField_apply, hβ y]
    exact qf_coefMat _ _
  simp only [e]
  exact integral_comp (emb lo hi) (map_V0 lo hi) (fun x => βE x (W x) (W x))

/-- Integrability of the bilinear density on the box. -/
theorem integrable_pk {W : E4 → V} (hW : ∀ i, MemLp (pk lo hi W i) 2 (V0 lo hi))
    (β : C(Icc lo hi, V →L[ℝ] V →L[ℝ] ℝ)) (βE : E4 → V →L[ℝ] V →L[ℝ] ℝ)
    (hβ : ∀ y, β y = βE y.val) :
    Integrable (fun x => βE x (W x) (W x)) (volume.restrict (box lo hi)) := by
  have hint := integrable_qf (V₀ := V0 lo hi) (coefField β) hW
  have e : (fun y : Icc lo hi => qf (coefField β y) (fun i => pk lo hi W i y)) =
      (fun x => βE x (W x) (W x)) ∘ Subtype.val := funext fun y => by
    rw [Function.comp_apply, coefField_apply, hβ y]
    exact qf_coefMat _ _
  rw [e, ← memLp_one_iff_integrable] at hint
  rw [← memLp_one_iff_integrable]
  exact (memLp_comp_iff (emb lo hi) (map_V0 lo hi)).1 hint

end Packets

/-! ### Uniform convergence of the coframes on the closed cube -/

section Uniform

/-- A continuous function is pointwise bounded on the closure of an open set by its essential
supremum there. -/
theorem ofReal_abs_le_eLpNorm_top {U : Set E4} (hU : IsOpen U) {φ : E4 → ℝ} (hφ : Continuous φ)
    {x : E4} (hx : x ∈ closure U) :
    ENNReal.ofReal |φ x| ≤ eLpNorm φ ⊤ (volume.restrict U) := by
  by_contra h
  push_neg at h
  set M := eLpNorm φ ⊤ (volume.restrict U)
  set S := {y : E4 | M < ENNReal.ofReal |φ y|}
  have hMt : M ≠ ⊤ := ne_top_of_lt h
  have hSo : IsOpen S := by
    have : S = {y : E4 | M.toReal < |φ y|} := by
      ext y
      simp only [S, mem_setOf_eq]
      rw [← ENNReal.ofReal_toReal hMt]
      rw [ENNReal.ofReal_toReal hMt]
      constructor
      · intro hy
        have := (ENNReal.ofReal_toReal hMt).symm ▸ hy
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).1 this
      · intro hy
        rw [← ENNReal.ofReal_toReal hMt]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hy
    rw [this]
    exact isOpen_lt continuous_const (continuous_abs.comp hφ)
  obtain ⟨y, hyS, hyU⟩ := mem_closure_iff.1 hx S hSo h
  have hpos : 0 < volume (S ∩ U) := (hSo.inter hU).measure_pos volume ⟨y, hyS, hyU⟩
  have hae : ∀ᵐ y ∂(volume.restrict U), ‖φ y‖ₑ ≤ M := by
    have := ae_le_eLpNormEssSup (μ := volume.restrict U) (f := φ)
    simpa [M, eLpNorm_exponent_top] using this
  have hz : (volume.restrict U) S = 0 := by
    refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hae)
    simp only [mem_setOf_eq, not_le]
    rw [Real.enorm_eq_ofReal_abs]
    exact hy
  rw [Measure.restrict_apply hSo.measurableSet] at hz
  exact hpos.ne' hz

theorem Icc_subset_closure_box {lo hi : E4} (hlh : ∀ i, lo i < hi i) :
    Icc lo hi ⊆ closure (box lo hi) := by
  simp only [box]
  rw [closure_pi_set, ← pi_univ_Icc]
  exact (Set.pi_congr rfl fun i _ => closure_Ioo (hlh i).ne).symm.subset

variable {a b lo hi : E4}

/-- The `L^∞` budget of a coframe sequence. -/
def linfBudget (f : ℕ → E4 → CoframeFibre) (f₀ : E4 → CoframeFibre) (S : Set E4) (n : ℕ) :
    ℝ≥0∞ :=
  ∑ i, ∑ ν, eLpNorm (fun y => f n y i ν - f₀ y i ν) ⊤ (volume.restrict S)

theorem edist_le_linfBudget {f : ℕ → E4 → CoframeFibre} {f₀ : E4 → CoframeFibre}
    (hf : ∀ n, Continuous (f n)) {x : E4} (hx : x ∈ closure (box a b)) (n m : ℕ) :
    edist (f n x) (f m x) ≤ linfBudget f f₀ (box a b) n + linfBudget f f₀ (box a b) m := by
  refine edist_pi_le_iff.2 fun i => edist_pi_le_iff.2 fun ν => ?_
  have hc : Continuous fun y => f n y i ν - f m y i ν :=
    ((continuous_apply ν).comp ((continuous_apply i).comp (hf n))).sub
      ((continuous_apply ν).comp ((continuous_apply i).comp (hf m)))
  calc edist (f n x i ν) (f m x i ν) = ENNReal.ofReal |f n x i ν - f m x i ν| := by
        rw [edist_dist, Real.dist_eq]
    _ ≤ eLpNorm (fun y => f n y i ν - f m y i ν) ⊤ (volume.restrict (box a b)) :=
        ofReal_abs_le_eLpNorm_top (isOpen_box a b) hc hx
    _ ≤ eLpNorm (fun y => f n y i ν - f₀ y i ν) ⊤ (volume.restrict (box a b)) +
          eLpNorm (fun y => f m y i ν - f₀ y i ν) ⊤ (volume.restrict (box a b)) := by
        have e : (fun y => f n y i ν - f m y i ν) =
            (fun y => f n y i ν - f₀ y i ν) + fun y => -(f m y i ν - f₀ y i ν) := by
          funext y; simp only [Pi.add_apply]; ring
        rw [e, eLpNorm_exponent_top, eLpNorm_exponent_top, eLpNorm_exponent_top]
        refine (eLpNormEssSup_add_le).trans (add_le_add le_rfl (le_of_eq ?_))
        rw [← eLpNorm_exponent_top, ← eLpNorm_exponent_top]
        exact eLpNorm_neg (f := fun y => f m y i ν - f₀ y i ν) (p := ⊤)
          (μ := volume.restrict (box a b))
    _ ≤ _ := add_le_add
        ((Finset.single_le_sum (f := fun ν => eLpNorm (fun y => f n y i ν - f₀ y i ν) ⊤
            (volume.restrict (box a b))) (fun _ _ => bot_le) (Finset.mem_univ ν)).trans
          (Finset.single_le_sum (f := fun i => ∑ ν, eLpNorm (fun y => f n y i ν - f₀ y i ν) ⊤
            (volume.restrict (box a b))) (fun _ _ => bot_le) (Finset.mem_univ i)))
        ((Finset.single_le_sum (f := fun ν => eLpNorm (fun y => f m y i ν - f₀ y i ν) ⊤
            (volume.restrict (box a b))) (fun _ _ => bot_le) (Finset.mem_univ ν)).trans
          (Finset.single_le_sum (f := fun i => ∑ ν, eLpNorm (fun y => f m y i ν - f₀ y i ν) ⊤
            (volume.restrict (box a b))) (fun _ _ => bot_le) (Finset.mem_univ i)))

end Uniform


section UniformLimit

variable {a b lo hi : E4}

theorem tendsto_linfBudget {f : ℕ → E4 → CoframeFibre} {f₀ : E4 → CoframeFibre} {S : Set E4}
    (h : ∀ i ν, Tendsto (fun n => eLpNorm (fun y => f n y i ν - f₀ y i ν) ⊤ (volume.restrict S))
      atTop (𝓝 0)) : Tendsto (linfBudget f f₀ S) atTop (𝓝 0) := by
  have := tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun i _ =>
    tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun ν _ => h i ν
  simp only [Finset.sum_const_zero] at this
  exact this

/-- The restriction of a continuous coframe field to the closed cube. -/
def restrC (lo hi : E4) (f : E4 → CoframeFibre) (hf : Continuous f) : C(Icc lo hi, CoframeFibre) :=
  (⟨f, hf⟩ : C(E4, CoframeFibre)).restrict (Icc lo hi)

@[simp] theorem restrC_apply (f : E4 → CoframeFibre) (hf : Continuous f) (y : Icc lo hi) :
    restrC lo hi f hf y = f y.val := rfl

/-- **Uniform coframe limit on the closed cube**: continuous coframes converging in `L^∞` of a box
converge uniformly on every closed sub-cube to a continuous field equal a.e. to the `L^∞` limit. -/
theorem exists_uniform_coframe (hlh : ∀ i, lo i < hi i) (hQK : box lo hi ⊆ box a b)
    {f : ℕ → E4 → CoframeFibre} (hf : ∀ n, Continuous (f n)) {f₀ : E4 → CoframeFibre}
    (hlim : ∀ i ν, Tendsto (fun n => eLpNorm (fun y => f n y i ν - f₀ y i ν) ⊤
      (volume.restrict (box a b))) atTop (𝓝 0)) :
    ∃ ec : C(Icc lo hi, CoframeFibre), Tendsto (fun n => restrC lo hi (f n) (hf n)) atTop (𝓝 ec) ∧
      ∀ᵐ y ∂(V0 lo hi), ec y = f₀ y.val := by
  have hB := tendsto_linfBudget hlim
  have hcl : Icc lo hi ⊆ closure (box a b) :=
    (Icc_subset_closure_box hlh).trans (closure_mono hQK)
  have hcauchy : CauchySeq fun n => restrC lo hi (f n) (hf n) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hε3 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 3) := ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hB.eventually (gt_mem_nhds hε3))
    refine ⟨N, fun n hn => ?_⟩
    have hle : dist (restrC lo hi (f n) (hf n)) (restrC lo hi (f N) (hf N)) ≤ 2 * (ε / 3) := by
      refine (ContinuousMap.dist_le (by positivity)).2 fun y => ?_
      rw [restrC_apply, restrC_apply, ← edist_le_ofReal (by positivity)]
      refine (edist_le_linfBudget (f₀ := f₀) hf (hcl y.2) n N).trans ?_
      rw [two_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
      exact add_le_add (hN n hn).le (hN N le_rfl).le
    linarith
  obtain ⟨ec, hec⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨ec, hec, ?_⟩
  -- a.e. convergence to `f₀`
  have hae : ∀ᵐ x ∂(volume.restrict (box a b)), ∀ n i ν,
      ‖f n x i ν - f₀ x i ν‖ₑ ≤ eLpNorm (fun y => f n y i ν - f₀ y i ν) ⊤
        (volume.restrict (box a b)) := by
    refine ae_all_iff.2 fun n => ae_all_iff.2 fun i => ae_all_iff.2 fun ν => ?_
    have := ae_le_eLpNormEssSup (μ := volume.restrict (box a b))
      (f := fun y => f n y i ν - f₀ y i ν)
    simpa [eLpNorm_exponent_top] using this
  have hae' : ∀ᵐ x ∂(volume.restrict (box lo hi)), ∀ n i ν,
      ‖f n x i ν - f₀ x i ν‖ₑ ≤ eLpNorm (fun y => f n y i ν - f₀ y i ν) ⊤
        (volume.restrict (box a b)) :=
    ae_restrict_of_ae_restrict_of_subset hQK hae
  filter_upwards [ae_comp (emb lo hi) (map_V0 lo hi) hae'] with y hy
  have h1 : Tendsto (fun n => f n y.val) atTop (𝓝 (ec y)) :=
    ((continuous_eval_const y).tendsto ec).comp hec
  have h2 : Tendsto (fun n => f n y.val) atTop (𝓝 (f₀ y.val)) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB (fun _ => bot_le)
      fun n => ?_
    refine edist_pi_le_iff.2 fun i => edist_pi_le_iff.2 fun ν => ?_
    rw [edist_eq_enorm_sub]
    refine (hy n i ν).trans ?_
    exact (Finset.single_le_sum (f := fun ν => eLpNorm (fun y => f n y i ν - f₀ y i ν) ⊤
        (volume.restrict (box a b))) (fun _ _ => bot_le) (Finset.mem_univ ν)).trans
      (Finset.single_le_sum (f := fun i => ∑ ν, eLpNorm (fun y => f n y i ν - f₀ y i ν) ⊤
        (volume.restrict (box a b))) (fun _ _ => bot_le) (Finset.mem_univ i))
  exact tendsto_nhds_unique h1 h2

end UniformLimit


/-! ### The quadratic metric coefficients as continuous bilinear-form fields -/

section Coefficients

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Evaluation of a covector-valued bilinear form on a test jet. -/
def evalB (Φ : V →L[ℝ] V →L[ℝ] (RJet (Fin 5) →L[ℝ] ℝ)) (T : RJet (Fin 5)) : V →L[ℝ] V →L[ℝ] ℝ :=
  mkBilinL (fun w w' => Φ w w' T) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)

@[simp] theorem evalB_apply (Φ : V →L[ℝ] V →L[ℝ] (RJet (Fin 5) →L[ℝ] ℝ)) (T : RJet (Fin 5))
    (w w' : V) : evalB Φ T w w' = Φ w w' T := rfl

theorem continuousOn_evalB {Φ : CoframeFibre → V →L[ℝ] V →L[ℝ] (RJet (Fin 5) →L[ℝ] ℝ)}
    (hΦ : ContinuousOn Φ coframeGL) :
    ContinuousOn (fun q : CoframeFibre × RJet (Fin 5) => evalB (Φ q.1) q.2)
      (coframeGL ×ˢ univ) := by
  have h1 : ContinuousOn (fun q : CoframeFibre × RJet (Fin 5) => Φ q.1) (coframeGL ×ˢ univ) :=
    hΦ.comp continuousOn_fst fun q hq => hq.1
  refine continuousOn_clm_apply.2 fun w => continuousOn_clm_apply.2 fun w' => ?_
  simp only [evalB_apply]
  exact ((h1.clm_apply continuousOn_const).clm_apply continuousOn_const).clm_apply continuousOn_snd

/-- The potential coefficient as a covector-valued bilinear form `(s, s') ↦ potVCoeff e (s s')`. -/
def potBil (e : CoframeFibre) : ℝ →L[ℝ] ℝ →L[ℝ] (RJet (Fin 5) →L[ℝ] ℝ) :=
  mkBilinL (fun s s' => potVCoeff e (s * s'))
    (fun x x' y => by rw [add_mul, map_add])
    (fun c x y => by rw [smul_eq_mul, mul_assoc, ← smul_eq_mul, map_smul])
    (fun x y y' => by rw [mul_add, map_add])
    (fun c x y => by rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul, map_smul])

@[simp] theorem potBil_apply (e : CoframeFibre) (s s' : ℝ) : potBil e s s' = potVCoeff e (s * s') :=
  rfl

theorem continuousOn_potBil : ContinuousOn potBil coframeGL :=
  continuousOn_cov2 fun s s' T => by
    simp only [potBil_apply]
    exact (continuousOn_potVCoeff.clm_apply continuousOn_const).clm_apply continuousOn_const

/-- The quartic packet `|H|² - v²` of a jet. -/
def quartY {Ysec : Type} (θ : CoefficientBank Ysec) (J : RJet (Fin 5)) : ℝ :=
  higgsQuad J.H - θ.vH ^ 2

/-- **The quadratic metric part as three bilinear packets**: Yang–Mills `(F, F)`, Higgs-kinetic
`(K, K)` and quartic `(|H|² - v², |H|² - v²)`. -/
theorem quadMet_eq_packets {Ysec : Type} (θ : CoefficientBank Ysec) (J T : RJet (Fin 5)) :
    quadMet θ J T = (∑ j, gaugeScalars θ j • evalB (ymMetCoeff j J.e) T) J.F J.F +
      evalB (higgsMetCoeff J.e) T J.K J.K + (θ.lambdaH • evalB (potBil J.e) T) (quartY θ J)
        (quartY θ J) := by
  simp only [quadMet, quartY, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, evalB_apply, potBil_apply, smul_eq_mul, sq]

variable {K : Type*} [TopologicalSpace K]

/-- A coefficient field `y ↦ G(e(y), τ(y))` for `G` continuous on the nondegenerate chart. -/
def gField {W : Type*} [TopologicalSpace W] (G : CoframeFibre × RJet (Fin 5) → W)
    (hG : ContinuousOn G (coframeGL ×ˢ univ)) (ec : C(K, CoframeFibre))
    (hec : ∀ y, ec y ∈ coframeGL) (τ : C(K, RJet (Fin 5))) : C(K, W) :=
  ⟨fun y => G (ec y, τ y), hG.comp_continuous (ec.continuous.prodMk τ.continuous)
    fun y => ⟨hec y, mem_univ _⟩⟩

@[simp] theorem gField_apply {W : Type*} [TopologicalSpace W] (G : CoframeFibre × RJet (Fin 5) → W)
    (hG : ContinuousOn G (coframeGL ×ˢ univ)) (ec : C(K, CoframeFibre))
    (hec : ∀ y, ec y ∈ coframeGL) (τ : C(K, RJet (Fin 5))) (y : K) :
    gField G hG ec hec τ y = G (ec y, τ y) := rfl

/-- **Uniform convergence of the coefficient fields** along uniformly convergent coframes with
values in a compact subset of the nondegenerate chart. -/
theorem tendsto_gField [CompactSpace K] {W : Type*} [NormedAddCommGroup W]
    (G : CoframeFibre × RJet (Fin 5) → W) (hG : ContinuousOn G (coframeGL ×ˢ univ))
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL)
    {ec : ℕ → C(K, CoframeFibre)} {ec₀ : C(K, CoframeFibre)} (hn : ∀ n y, ec n y ∈ Ke)
    (h0 : ∀ y, ec₀ y ∈ Ke) (hconv : Tendsto ec atTop (𝓝 ec₀)) (τ : C(K, RJet (Fin 5))) :
    Tendsto (fun n => gField G hG (ec n) (fun y => hKeGL (hn n y)) τ) atTop
      (𝓝 (gField G hG ec₀ (fun y => hKeGL (h0 y)) τ)) := by
  rw [ContinuousMap.tendsto_iff_tendstoUniformly]
  have hT : IsCompact (range τ) := isCompact_range τ.continuous
  have hU : UniformContinuousOn G (Ke ×ˢ range τ) :=
    (hKe.prod hT).uniformContinuousOn_of_continuous
      (hG.mono (prod_mono hKeGL (subset_univ _)))
  have hconv' := (ContinuousMap.tendsto_iff_tendstoUniformly).1 hconv
  have hpair : TendstoUniformly (fun n y => (ec n y, τ y)) (fun y => (ec₀ y, τ y)) atTop := by
    rw [Metric.tendstoUniformly_iff] at hconv' ⊢
    intro ε hε
    filter_upwards [hconv' ε hε] with n hn y
    rw [Prod.dist_eq, dist_self]
    simpa using hn y
  exact hU.comp_tendstoUniformly (F := fun n y => (ec n y, τ y)) (f := fun y => (ec₀ y, τ y))
    (fun n y => mk_mem_prod (hn n y) (mem_range_self y))
    (fun y => mk_mem_prod (h0 y) (mem_range_self y)) hpair

end Coefficients


/-! ### Weak `L²` convergence of the quartic packet `|H_h|² - v_h²` -/

section Quartic

variable {lo hi : E4}

/-- Real weak `L²` data from `L¹` convergence and a uniform `L²` bound. -/
theorem weakL2Data_of_L1 {Y : ℕ → E4 → ℝ} {Y₀ : E4 → ℝ}
    (hY : ∀ n, MemLp (Y n) 2 (volume.restrict (box lo hi)))
    (hY₀ : MemLp Y₀ 2 (volume.restrict (box lo hi))) {B : ℝ}
    (hB : ∀ n, (eLpNorm (Y n) 2 (volume.restrict (box lo hi))).toReal ≤ B)
    (h1 : Tendsto (fun n => eLpNorm (Y n - Y₀) 1 (volume.restrict (box lo hi))) atTop (𝓝 0)) :
    WeakL2Data lo hi Y Y₀ := by
  set μ := volume.restrict (box lo hi)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (volume_box_ne_top lo hi)
  set W : ℕ → E4 → ℂ := fun n x => (Y n x : ℂ)
  set W₀ : E4 → ℂ := fun x => (Y₀ x : ℂ)
  have hWm : ∀ n, MemLp (W n) 2 μ := fun n => Complex.ofRealCLM.comp_memLp' (hY n)
  have hW₀m : MemLp W₀ 2 μ := Complex.ofRealCLM.comp_memLp' hY₀
  have hWn : ∀ n, eLpNorm (W n) 2 μ = eLpNorm (Y n) 2 μ := fun n =>
    eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp only [W, Complex.norm_real])
  -- convergence against bounded weights, from the `L¹` convergence
  have hreal : ∀ w : E4 → ℝ, MemLp w ⊤ μ →
      Tendsto (fun n => ∫ x, w x * Y n x ∂μ) atTop (𝓝 (∫ x, w x * Y₀ x ∂μ)) := by
    intro w hw
    have hd : ∀ n, MemLp (Y n - Y₀) 1 μ := fun n =>
      ((hY n).sub hY₀).mono_exponent (by norm_num)
    have hbd : ∀ n, ‖∫ x, w x * Y n x ∂μ - ∫ x, w x * Y₀ x ∂μ‖ ≤
        (eLpNorm w ⊤ μ * eLpNorm (Y n - Y₀) 1 μ).toReal := by
      intro n
      have hi : ∀ Z : E4 → ℝ, MemLp Z 2 μ → Integrable (fun x => w x * Z x) μ := fun Z hZ =>
        (memLp_one_iff_integrable.1 ((hZ.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).smul hw))
      rw [← integral_sub (hi _ (hY n)) (hi _ hY₀)]
      have e : (fun x => w x * Y n x - w x * Y₀ x) = w • (Y n - Y₀) := by
        funext x; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.mul_apply]; ring
      rw [e]
      have hws : MemLp (w • (Y n - Y₀)) 1 μ := (hd n).smul hw
      calc ‖∫ x, (w • (Y n - Y₀)) x ∂μ‖ ≤ ∫ x, ‖(w • (Y n - Y₀)) x‖ ∂μ :=
            norm_integral_le_integral_norm _
        _ = (eLpNorm (w • (Y n - Y₀)) 1 μ).toReal := by
            rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm hws.1]
        _ ≤ _ := ENNReal.toReal_mono (ENNReal.mul_ne_top hw.eLpNorm_ne_top (hd n).eLpNorm_ne_top)
            (eLpNorm_smul_le_mul_eLpNorm (hd n).1 hw.1)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) hbd ?_
    have := ENNReal.Tendsto.const_mul h1 (Or.inr hw.eLpNorm_ne_top)
    rw [mul_zero] at this
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp this
    rw [ENNReal.toReal_zero] at h2
    exact h2
  have hcx : ∀ w : E4 → ℝ, MemLp w ⊤ μ →
      Tendsto (fun n => ∫ x, w x • W n x ∂μ) atTop (𝓝 (∫ x, w x • W₀ x ∂μ)) := by
    intro w hw
    have e : ∀ Z : E4 → ℝ, ∫ x, w x • (Z x : ℂ) ∂μ = ((∫ x, w x * Z x ∂μ : ℝ) : ℂ) := by
      intro Z
      rw [← integral_complex_ofReal]
      congr 1; funext x; simp [Complex.real_smul]
    simp only [W, W₀, e]
    exact (Complex.continuous_ofReal.tendsto _).comp (hreal w hw)
  have hweak := weakL2_of_real_weights hWm hW₀m fun w hw =>
    tendsto_L2_weights hWm hW₀m (B := B) (fun n => by rw [hWn]; exact hB n) hcx hw
  refine ⟨hY, hY₀, ⟨B, hB⟩, fun ℓ g hg => ?_⟩
  have := hweak (ℓ.comp Complex.reCLM) g hg
  simpa [W, W₀] using this

/-- **Weak `L²` data of the quartic packet** `|H_h|² - v_h²` from strong `L²` convergence of the
Higgs fields, a uniform `L⁴` bound and convergent vacuum values. -/
theorem weakL2Data_quart {H : ℕ → E4 → HiggsFibre} {H₀ : E4 → HiggsFibre}
    (hH : RenewalGeometry.LpTendsto (volume.restrict (box lo hi)) 2 H H₀) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hH4 : ∀ n, eLpNorm (H n) 4 (volume.restrict (box lo hi)) ≤ M)
    (hH₀4 : MemLp H₀ 4 (volume.restrict (box lo hi))) {v : ℕ → ℝ} {v₀ : ℝ}
    (hv : Tendsto v atTop (𝓝 v₀)) :
    WeakL2Data lo hi (fun n x => higgsQuad (H n x) - v n ^ 2)
      (fun x => higgsQuad (H₀ x) - v₀ ^ 2) := by
  set μ := volume.restrict (box lo hi)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (volume_box_ne_top lo hi)
  have hq : ∀ u, higgsQuad u = hInnerReL u u := fun u => rfl
  haveI : ENNReal.HolderTriple 4 4 2 := FirstVariationCalculus.holderTriple_four_four_two
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  -- `L²` bounds of `|H|²` from `L⁴` bounds
  have hq2 : ∀ G : E4 → HiggsFibre, AEStronglyMeasurable G μ →
      eLpNorm (fun x => higgsQuad (G x)) 2 μ ≤
        ‖(hInnerReL : HiggsFibre →L[ℝ] HiggsFibre →L[ℝ] ℝ)‖₊ * eLpNorm G 4 μ * eLpNorm G 4 μ :=
    fun G hG => eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hG hG (fun u u' => hInnerReL u u') _
      (Eventually.of_forall fun x => by
        rw [← NNReal.coe_le_coe]; push_cast
        exact ContinuousLinearMap.le_opNorm₂ _ _ _)
  obtain ⟨R, hR⟩ : ∃ R, ∀ n, |v n| ≤ R := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto v hv).subset_closedBall 0
    exact ⟨R, fun n => by simpa [Real.dist_eq] using hR (mem_range_self n)⟩
  have hconst : ∀ (c : ℝ) (p : ℝ≥0∞), eLpNorm (fun _ : E4 => c) p μ ≤
      μ Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal |c| := fun c p =>
    eLpNorm_le_of_ae_bound (Eventually.of_forall fun x => by rw [Real.norm_eq_abs])
  have hfin : ∀ (c : ℝ) (p : ℝ≥0∞), μ Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal |c| ≠ ⊤ :=
    fun c p => ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg
      (inv_nonneg.2 ENNReal.toReal_nonneg) (measure_ne_top _ _)) ENNReal.ofReal_ne_top
  have hm : ∀ G : E4 → HiggsFibre, AEStronglyMeasurable G μ → ∀ c : ℝ,
      AEStronglyMeasurable (fun x => higgsQuad (G x) - c) μ := fun G hG c =>
    ((hInnerReL.continuous₂.comp (continuous_id.prodMk continuous_id)).comp_aestronglyMeasurable
      hG).sub aestronglyMeasurable_const
  set Bt : ℝ≥0∞ := ‖(hInnerReL : HiggsFibre →L[ℝ] HiggsFibre →L[ℝ] ℝ)‖₊ * M * M +
    μ Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal |R ^ 2|
  have hBt : Bt ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.coe_ne_top hM) hM, hfin _ _⟩
  have hYb : ∀ n, eLpNorm (fun x => higgsQuad (H n x) - v n ^ 2) 2 μ ≤ Bt := by
    intro n
    have hHm := (hH.memLp n).1
    calc _ ≤ eLpNorm (fun x => higgsQuad (H n x)) 2 μ + eLpNorm (fun _ : E4 => v n ^ 2) 2 μ :=
          eLpNorm_sub_le ((hm _ hHm 0).congr (Eventually.of_forall fun x => by simp))
            aestronglyMeasurable_const (by norm_num)
      _ ≤ Bt := by
          refine add_le_add ((hq2 _ hHm).trans (by gcongr <;> exact hH4 n)) ?_
          refine (hconst _ _).trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_)
            bot_le)
          rw [abs_pow, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) ((hR n).trans (le_abs_self R)) 2
  have hYm : ∀ n, MemLp (fun x => higgsQuad (H n x) - v n ^ 2) 2 μ := fun n =>
    ⟨hm _ (hH.memLp n).1 _, (hYb n).trans_lt hBt.lt_top⟩
  have hY₀m : MemLp (fun x => higgsQuad (H₀ x) - v₀ ^ 2) 2 μ := by
    refine ⟨hm _ hH.memLp_lim.1 _, ?_⟩
    calc _ ≤ eLpNorm (fun x => higgsQuad (H₀ x)) 2 μ + eLpNorm (fun _ : E4 => v₀ ^ 2) 2 μ :=
          eLpNorm_sub_le ((hm _ hH.memLp_lim.1 0).congr (Eventually.of_forall fun x => by simp))
            aestronglyMeasurable_const (by norm_num)
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨(hq2 _ hH.memLp_lim.1).trans_lt (ENNReal.mul_lt_top
          (ENNReal.mul_lt_top ENNReal.coe_lt_top hH₀4.2) hH₀4.2),
          (hconst _ _).trans_lt (hfin _ _).lt_top⟩
  refine weakL2Data_of_L1 hYm hY₀m (B := Bt.toReal) (fun n => ENNReal.toReal_mono hBt (hYb n)) ?_
  -- `L¹` convergence
  have hb := RenewalGeometry.LpTendsto.bilin (p := 2) (q := 2) (r := 1)
    (hInnerReL : HiggsFibre →L[ℝ] HiggsFibre →L[ℝ] ℝ) hH hH
  have hvc : Tendsto (fun n => v n ^ 2 - v₀ ^ 2) atTop (𝓝 0) := by
    have := (hv.pow 2).sub_const (v₀ ^ 2)
    simpa using this
  have hcst : Tendsto (fun n => μ Set.univ ^ (1 : ℝ≥0∞).toReal⁻¹ *
      ENNReal.ofReal |v n ^ 2 - v₀ ^ 2|) atTop (𝓝 0) := by
    have ha : Tendsto (fun n => |v n ^ 2 - v₀ ^ 2|) atTop (𝓝 0) := by
      have := (continuous_abs.tendsto 0).comp hvc
      rw [abs_zero] at this
      exact this
    have h1 : Tendsto (fun n => ENNReal.ofReal |v n ^ 2 - v₀ ^ 2|) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp ha
      rw [ENNReal.ofReal_zero] at this
      exact this
    have := ENNReal.Tendsto.const_mul (a := μ Set.univ ^ (1 : ℝ≥0∞).toReal⁻¹) h1
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
        (measure_ne_top μ Set.univ)))
    rwa [mul_zero] at this
  have hup := hb.tendsto.add hcst
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ => bot_le) fun n => ?_
  have e : (fun x => higgsQuad (H n x) - v n ^ 2) - (fun x => higgsQuad (H₀ x) - v₀ ^ 2) =
      ((fun x => hInnerReL (H n x) (H n x)) - fun x => hInnerReL (H₀ x) (H₀ x)) -
        fun _ => v n ^ 2 - v₀ ^ 2 := by
    funext x; simp only [Pi.sub_apply, hq]; ring
  rw [e]
  exact (eLpNorm_sub_le ((hb.memLp n).1.sub hb.memLp_lim.1) aestronglyMeasurable_const
    le_rfl).trans (add_le_add le_rfl (hconst _ _))

end Quartic


/-! ### The defect contraction and the metric identity on a cube -/

section MetricIdentity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {lo hi : E4}

theorem quadCLM_pk_ae {W : E4 → V} (hW : ∀ i, MemLp (pk lo hi W i) 2 (V0 lo hi))
    (β : C(Icc lo hi, V →L[ℝ] V →L[ℝ] ℝ)) (βE : E4 → V →L[ℝ] V →L[ℝ] ℝ)
    (hβ : ∀ᵐ y ∂(V0 lo hi), β y = βE y.val) :
    quadCLM (V0 lo hi) (pk lo hi W) (coefField β) =
      ∫ x, βE x (W x) (W x) ∂(volume.restrict (box lo hi)) := by
  rw [quadCLM_apply hW]
  have e : ∀ᵐ y ∂(V0 lo hi), qf (coefField β y) (fun i => pk lo hi W i y) =
      (fun x => βE x (W x) (W x)) y.val := hβ.mono fun y hy => by
    rw [coefField_apply, hy]
    exact qf_coefMat _ _
  rw [integral_congr_ae e]
  exact integral_comp (emb lo hi) (map_V0 lo hi) (fun x => βE x (W x) (W x))

theorem integrable_pk_ae {W : E4 → V} (hW : ∀ i, MemLp (pk lo hi W i) 2 (V0 lo hi))
    (β : C(Icc lo hi, V →L[ℝ] V →L[ℝ] ℝ)) (βE : E4 → V →L[ℝ] V →L[ℝ] ℝ)
    (hβ : ∀ᵐ y ∂(V0 lo hi), β y = βE y.val) :
    Integrable (fun x => βE x (W x) (W x)) (volume.restrict (box lo hi)) := by
  have hint := integrable_qf (V₀ := V0 lo hi) (coefField β) hW
  have e : (fun y : Icc lo hi => qf (coefField β y) (fun i => pk lo hi W i y)) =ᵐ[V0 lo hi]
      (fun x => βE x (W x) (W x)) ∘ Subtype.val := hβ.mono fun y hy => by
    show qf (coefField β y) (fun i => pk lo hi W i y) = βE y.val (W y.val) (W y.val)
    rw [coefField_apply, hy]
    exact qf_coefMat _ _
  have hint' := hint.congr e
  rw [← memLp_one_iff_integrable] at hint'
  rw [← memLp_one_iff_integrable]
  exact (memLp_comp_iff (emb lo hi) (map_V0 lo hi)).1 hint'

variable {K : Type*} [TopologicalSpace K]

/-- The Yang–Mills metric-variation coefficient field `Σ_j g_j D(YM_j)(e)[ė(k)]`. -/
def ymField {Ysec : Type} (θ : CoefficientBank Ysec) (ec : C(K, CoframeFibre))
    (hec : ∀ y, ec y ∈ coframeGL) (τ : C(K, RJet (Fin 5))) :
    C(K, (Fin 4 → ConnFibre) →L[ℝ] (Fin 4 → ConnFibre) →L[ℝ] ℝ) :=
  ∑ j, gaugeScalars θ j • gField (fun q => evalB (ymMetCoeff (C := Fin 5) j q.1) q.2)
    (continuousOn_evalB (continuousOn_ymMetCoeff j)) ec hec τ

/-- The Higgs-kinetic metric-variation coefficient field. -/
def higField (ec : C(K, CoframeFibre)) (hec : ∀ y, ec y ∈ coframeGL) (τ : C(K, RJet (Fin 5))) :
    C(K, (Fin 4 → HiggsFibre) →L[ℝ] (Fin 4 → HiggsFibre) →L[ℝ] ℝ) :=
  gField (fun q => evalB (higgsMetCoeff (C := Fin 5) q.1) q.2)
    (continuousOn_evalB continuousOn_higgsMetCoeff) ec hec τ

/-- The potential (volume-factor) metric-variation coefficient field, with `λ`. -/
def potField {Ysec : Type} (θ : CoefficientBank Ysec) (ec : C(K, CoframeFibre))
    (hec : ∀ y, ec y ∈ coframeGL) (τ : C(K, RJet (Fin 5))) : C(K, ℝ →L[ℝ] ℝ →L[ℝ] ℝ) :=
  θ.lambdaH • gField (fun q => evalB (potBil q.1) q.2) (continuousOn_evalB continuousOn_potBil)
    ec hec τ

theorem ymField_apply {Ysec : Type} (θ : CoefficientBank Ysec) (ec : C(K, CoframeFibre))
    (hec : ∀ y, ec y ∈ coframeGL) (τ : C(K, RJet (Fin 5))) (y : K) :
    ymField θ ec hec τ y = ∑ j, gaugeScalars θ j • evalB (ymMetCoeff j (ec y)) (τ y) := by
  simp [ymField, ContinuousMap.coe_sum, Finset.sum_apply]

theorem higField_apply (ec : C(K, CoframeFibre)) (hec : ∀ y, ec y ∈ coframeGL)
    (τ : C(K, RJet (Fin 5))) (y : K) :
    higField ec hec τ y = evalB (higgsMetCoeff (ec y)) (τ y) := rfl

theorem potField_apply {Ysec : Type} (θ : CoefficientBank Ysec) (ec : C(K, CoframeFibre))
    (hec : ∀ y, ec y ∈ coframeGL) (τ : C(K, RJet (Fin 5))) (y : K) :
    potField θ ec hec τ y = θ.lambdaH • evalB (potBil (ec y)) (τ y) := rfl

/-- **The bosonic stress-defect contraction** `𝔖_YM + 𝔖_H` tested on `τ`:
`𝖰_F(B^{YM}[τ]) + 𝖰_K(B^H[τ]) + 𝖰_Y(B^V[τ])`, the coefficient fields being taken at the coframe
`ec`. -/
def smDefect {Ysec : Type} [CompactSpace K] [MetricSpace K]
    (QF : StrongDual ℝ C(K, PIdx (Fin 4 → ConnFibre) → PIdx (Fin 4 → ConnFibre) → ℝ))
    (QK : StrongDual ℝ C(K, PIdx (Fin 4 → HiggsFibre) → PIdx (Fin 4 → HiggsFibre) → ℝ))
    (QY : StrongDual ℝ C(K, PIdx ℝ → PIdx ℝ → ℝ)) (θ : CoefficientBank Ysec)
    (ec : C(K, CoframeFibre)) (hec : ∀ y, ec y ∈ coframeGL) (τ : C(K, RJet (Fin 5))) : ℝ :=
  QF (coefField (ymField θ ec hec τ)) + QK (coefField (higField ec hec τ)) +
    QY (coefField (potField θ ec hec τ))

end MetricIdentity


section MetricIdentity2

variable {lo hi : E4}

/-- Splitting of the quadratic metric integral into the three packet integrals. -/
theorem integral_quadMet_split {Ysec : Type} (θ' : CoefficientBank Ysec) (J : E4 → RJet (Fin 5))
    (τE : E4 → RJet (Fin 5)) {μ : Measure E4}
    (h1 : Integrable (fun x => (∑ j, gaugeScalars θ' j • evalB (ymMetCoeff j (J x).e) (τE x))
      (J x).F (J x).F) μ)
    (h2 : Integrable (fun x => evalB (higgsMetCoeff (J x).e) (τE x) (J x).K (J x).K) μ)
    (h3 : Integrable (fun x => (θ'.lambdaH • evalB (potBil (J x).e) (τE x)) (quartY θ' (J x))
      (quartY θ' (J x))) μ) :
    Integrable (fun x => quadMet θ' (J x) (τE x)) μ ∧
      ∫ x, quadMet θ' (J x) (τE x) ∂μ =
        ∫ x, (∑ j, gaugeScalars θ' j • evalB (ymMetCoeff j (J x).e) (τE x)) (J x).F (J x).F ∂μ +
        ∫ x, evalB (higgsMetCoeff (J x).e) (τE x) (J x).K (J x).K ∂μ +
        ∫ x, (θ'.lambdaH • evalB (potBil (J x).e) (τE x)) (quartY θ' (J x)) (quartY θ' (J x))
          ∂μ := by
  have e : (fun x => quadMet θ' (J x) (τE x)) = fun x =>
      (∑ j, gaugeScalars θ' j • evalB (ymMetCoeff j (J x).e) (τE x)) (J x).F (J x).F +
        evalB (higgsMetCoeff (J x).e) (τE x) (J x).K (J x).K +
        (θ'.lambdaH • evalB (potBil (J x).e) (τE x)) (quartY θ' (J x)) (quartY θ' (J x)) :=
    funext fun x => quadMet_eq_packets θ' (J x) (τE x)
  rw [e]
  refine ⟨(h1.add h2).add h3, ?_⟩
  have e1 : ∫ x, ((∑ j, gaugeScalars θ' j • evalB (ymMetCoeff j (J x).e) (τE x)) (J x).F (J x).F +
        evalB (higgsMetCoeff (J x).e) (τE x) (J x).K (J x).K +
        (θ'.lambdaH • evalB (potBil (J x).e) (τE x)) (quartY θ' (J x)) (quartY θ' (J x))) ∂μ =
      ∫ x, ((∑ j, gaugeScalars θ' j • evalB (ymMetCoeff j (J x).e) (τE x)) (J x).F (J x).F +
        evalB (higgsMetCoeff (J x).e) (τE x) (J x).K (J x).K) ∂μ +
      ∫ x, (θ'.lambdaH • evalB (potBil (J x).e) (τE x)) (quartY θ' (J x)) (quartY θ' (J x)) ∂μ :=
    integral_add (h1.add h2) h3
  have e2 : ∫ x, ((∑ j, gaugeScalars θ' j • evalB (ymMetCoeff j (J x).e) (τE x)) (J x).F (J x).F +
        evalB (higgsMetCoeff (J x).e) (τE x) (J x).K (J x).K) ∂μ =
      ∫ x, (∑ j, gaugeScalars θ' j • evalB (ymMetCoeff j (J x).e) (τE x)) (J x).F (J x).F ∂μ +
      ∫ x, evalB (higgsMetCoeff (J x).e) (τE x) (J x).K (J x).K ∂μ :=
    integral_add h1 h2
  rw [e1, e2]

set_option maxHeartbeats 1000000 in
/-- **The metric identity on a cube** (abstract form): if the complete rows minus their quadratic
metric part converge, the complete first variations tend to zero, the coframes converge uniformly
on the closed cube and the three packets have covariance measures `𝖰_F, 𝖰_K, 𝖰_Y`, then
`∫_Q Cov_{θ₀}(J₀)(τ) + 𝔖(τ) = 0`. -/
theorem metric_identity {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    {Jn : ℕ → E4 → RJet (Fin 5)} {J₀ : E4 → RJet (Fin 5)}
    {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hs : ∀ j, Tendsto (fun n => gaugeScalars (θ n) j) atTop (𝓝 (gaugeScalars θ₀ j)))
    (hl : Tendsto (fun n => (θ n).lambdaH) atTop (𝓝 θ₀.lambdaH))
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL)
    {ecn : ℕ → C(Icc lo hi, CoframeFibre)} {ec₀ : C(Icc lo hi, CoframeFibre)}
    (hn : ∀ n y, ecn n y ∈ Ke) (h0 : ∀ y, ec₀ y ∈ Ke) (hconv : Tendsto ecn atTop (𝓝 ec₀))
    (hecn : ∀ n (y : Icc lo hi), ecn n y = (Jn n y.val).e)
    (hec₀ : ∀ᵐ y ∂(V0 lo hi), ec₀ y = (J₀ y.val).e)
    (hF : WeakL2Data lo hi (fun n x => (Jn n x).F) (fun x => (J₀ x).F))
    (hK : WeakL2Data lo hi (fun n x => (Jn n x).K) (fun x => (J₀ x).K))
    (hY : WeakL2Data lo hi (fun n x => quartY (θ n) (Jn n x)) (fun x => quartY θ₀ (J₀ x)))
    {QF : StrongDual ℝ C(Icc lo hi, PIdx (Fin 4 → ConnFibre) → PIdx (Fin 4 → ConnFibre) → ℝ)}
    {QK : StrongDual ℝ C(Icc lo hi, PIdx (Fin 4 → HiggsFibre) → PIdx (Fin 4 → HiggsFibre) → ℝ)}
    {QY : StrongDual ℝ C(Icc lo hi, PIdx ℝ → PIdx ℝ → ℝ)}
    (hQF : IsDefect (V0 lo hi) (fun n => pk lo hi (fun x => (Jn n x).F))
      (pk lo hi (fun x => (J₀ x).F)) QF)
    (hQK : IsDefect (V0 lo hi) (fun n => pk lo hi (fun x => (Jn n x).K))
      (pk lo hi (fun x => (J₀ x).K)) QK)
    (hQY : IsDefect (V0 lo hi) (fun n => pk lo hi (fun x => quartY (θ n) (Jn n x)))
      (pk lo hi (fun x => quartY θ₀ (J₀ x))) QY)
    {τE : E4 → RJet (Fin 5)} (τ : C(Icc lo hi, RJet (Fin 5))) (hτ : ∀ y, τ y = τE y.val)
    (hrows : (∀ n, Integrable (fun x => fullCov mY (θ n) (Jn n x) (τE x) -
        quadMet (θ n) (Jn n x) (τE x)) (volume.restrict (box lo hi))) ∧
      Integrable (fun x => fullCov mY θ₀ (J₀ x) (τE x) - quadMet θ₀ (J₀ x) (τE x))
        (volume.restrict (box lo hi)) ∧
      Tendsto (fun n => ∫ x, (fullCov mY (θ n) (Jn n x) (τE x) - quadMet (θ n) (Jn n x) (τE x))
        ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, (fullCov mY θ₀ (J₀ x) (τE x) - quadMet θ₀ (J₀ x) (τE x))
          ∂(volume.restrict (box lo hi)))))
    (hzero : Tendsto (fun n => ∫ x, fullCov mY (θ n) (Jn n x) (τE x)
      ∂(volume.restrict (box lo hi))) atTop (𝓝 0)) :
    ∫ x, fullCov mY θ₀ (J₀ x) (τE x) ∂(volume.restrict (box lo hi)) +
      smDefect QF QK QY θ₀ ec₀ (fun y => hKeGL (h0 y)) τ = 0 := by
  set μ := volume.restrict (box lo hi)
  obtain ⟨hDn, hD0, hDt⟩ := hrows
  have hWF := weakL2_pk hF
  have hWK := weakL2_pk hK
  have hWY := weakL2_pk hY
  -- the coefficient fields converge uniformly
  have tF : Tendsto (fun n => ymField (θ n) (ecn n) (fun y => hKeGL (hn n y)) τ) atTop
      (𝓝 (ymField θ₀ ec₀ (fun y => hKeGL (h0 y)) τ)) :=
    tendsto_finset_sum _ fun j _ => (hs j).smul (tendsto_gField _ _ hKe hKeGL hn h0 hconv τ)
  have tK : Tendsto (fun n => higField (ecn n) (fun y => hKeGL (hn n y)) τ) atTop
      (𝓝 (higField ec₀ (fun y => hKeGL (h0 y)) τ)) :=
    tendsto_gField _ _ hKe hKeGL hn h0 hconv τ
  have tY : Tendsto (fun n => potField (θ n) (ecn n) (fun y => hKeGL (hn n y)) τ) atTop
      (𝓝 (potField θ₀ ec₀ (fun y => hKeGL (h0 y)) τ)) :=
    hl.smul (tendsto_gField _ _ hKe hKeGL hn h0 hconv τ)
  have cF := hQF.tendsto_coef hWF (tendsto_coefField tF)
  have cK := hQK.tendsto_coef hWK (tendsto_coefField tK)
  have cY := hQY.tendsto_coef hWY (tendsto_coefField tY)
  -- the coefficient fields at the jets
  have aF : ∀ n, ∀ᵐ y ∂(V0 lo hi), ymField (θ n) (ecn n) (fun y => hKeGL (hn n y)) τ y =
      (fun x => ∑ j, gaugeScalars (θ n) j • evalB (ymMetCoeff j (Jn n x).e) (τE x)) y.val :=
    fun n => Eventually.of_forall fun y => by rw [ymField_apply, hecn, hτ]
  have aK : ∀ n, ∀ᵐ y ∂(V0 lo hi), higField (ecn n) (fun y => hKeGL (hn n y)) τ y =
      (fun x => evalB (higgsMetCoeff (Jn n x).e) (τE x)) y.val :=
    fun n => Eventually.of_forall fun y => by rw [higField_apply, hecn, hτ]
  have aY : ∀ n, ∀ᵐ y ∂(V0 lo hi), potField (θ n) (ecn n) (fun y => hKeGL (hn n y)) τ y =
      (fun x => (θ n).lambdaH • evalB (potBil (Jn n x).e) (τE x)) y.val :=
    fun n => Eventually.of_forall fun y => by rw [potField_apply, hecn, hτ]
  have aF0 : ∀ᵐ y ∂(V0 lo hi), ymField θ₀ ec₀ (fun y => hKeGL (h0 y)) τ y =
      (fun x => ∑ j, gaugeScalars θ₀ j • evalB (ymMetCoeff j (J₀ x).e) (τE x)) y.val :=
    hec₀.mono fun y hy => by rw [ymField_apply, hy, hτ]
  have aK0 : ∀ᵐ y ∂(V0 lo hi), higField ec₀ (fun y => hKeGL (h0 y)) τ y =
      (fun x => evalB (higgsMetCoeff (J₀ x).e) (τE x)) y.val :=
    hec₀.mono fun y hy => by rw [higField_apply, hy, hτ]
  have aY0 : ∀ᵐ y ∂(V0 lo hi), potField θ₀ ec₀ (fun y => hKeGL (h0 y)) τ y =
      (fun x => θ₀.lambdaH • evalB (potBil (J₀ x).e) (τE x)) y.val :=
    hec₀.mono fun y hy => by rw [potField_apply, hy, hτ]
  -- the quadratic metric integrals along the sequence and in the limit
  have sn := fun n => integral_quadMet_split (θ n) (Jn n) τE (μ := μ)
    (integrable_pk_ae (hWF.memLp n) _ (fun x => ∑ j, gaugeScalars (θ n) j • evalB (ymMetCoeff j (Jn n x).e) (τE x)) (aF n)) (integrable_pk_ae (hWK.memLp n) _ (fun x => evalB (higgsMetCoeff (Jn n x).e) (τE x)) (aK n))
    (integrable_pk_ae (hWY.memLp n) _ (fun x => (θ n).lambdaH • evalB (potBil (Jn n x).e) (τE x)) (aY n))
  have s0 := integral_quadMet_split θ₀ J₀ τE (μ := μ)
    (integrable_pk_ae hWF.memLp_lim _ (fun x => ∑ j, gaugeScalars θ₀ j • evalB (ymMetCoeff j (J₀ x).e) (τE x)) aF0) (integrable_pk_ae hWK.memLp_lim _ (fun x => evalB (higgsMetCoeff (J₀ x).e) (τE x)) aK0)
    (integrable_pk_ae hWY.memLp_lim _ (fun x => θ₀.lambdaH • evalB (potBil (J₀ x).e) (τE x)) aY0)
  have hQn : ∀ n, ∫ x, quadMet (θ n) (Jn n x) (τE x) ∂μ =
      quadCLM (V0 lo hi) (pk lo hi (fun x => (Jn n x).F))
          (coefField (ymField (θ n) (ecn n) (fun y => hKeGL (hn n y)) τ)) +
        quadCLM (V0 lo hi) (pk lo hi (fun x => (Jn n x).K))
          (coefField (higField (ecn n) (fun y => hKeGL (hn n y)) τ)) +
        quadCLM (V0 lo hi) (pk lo hi (fun x => quartY (θ n) (Jn n x)))
          (coefField (potField (θ n) (ecn n) (fun y => hKeGL (hn n y)) τ)) := by
    intro n
    rw [(sn n).2, quadCLM_pk_ae (hWF.memLp n) _ (fun x => ∑ j, gaugeScalars (θ n) j • evalB (ymMetCoeff j (Jn n x).e) (τE x)) (aF n), quadCLM_pk_ae (hWK.memLp n) _ (fun x => evalB (higgsMetCoeff (Jn n x).e) (τE x)) (aK n),
      quadCLM_pk_ae (hWY.memLp n) _ (fun x => (θ n).lambdaH • evalB (potBil (Jn n x).e) (τE x)) (aY n)]
  have hQ0 : ∫ x, quadMet θ₀ (J₀ x) (τE x) ∂μ =
      quadCLM (V0 lo hi) (pk lo hi (fun x => (J₀ x).F))
          (coefField (ymField θ₀ ec₀ (fun y => hKeGL (h0 y)) τ)) +
        quadCLM (V0 lo hi) (pk lo hi (fun x => (J₀ x).K))
          (coefField (higField ec₀ (fun y => hKeGL (h0 y)) τ)) +
        quadCLM (V0 lo hi) (pk lo hi (fun x => quartY θ₀ (J₀ x)))
          (coefField (potField θ₀ ec₀ (fun y => hKeGL (h0 y)) τ)) := by
    rw [s0.2, quadCLM_pk_ae hWF.memLp_lim _ (fun x => ∑ j, gaugeScalars θ₀ j • evalB (ymMetCoeff j (J₀ x).e) (τE x)) aF0, quadCLM_pk_ae hWK.memLp_lim _ (fun x => evalB (higgsMetCoeff (J₀ x).e) (τE x)) aK0,
      quadCLM_pk_ae hWY.memLp_lim _ (fun x => θ₀.lambdaH • evalB (potBil (J₀ x).e) (τE x)) aY0]
  have hQt : Tendsto (fun n => ∫ x, quadMet (θ n) (Jn n x) (τE x) ∂μ) atTop
      (𝓝 (∫ x, quadMet θ₀ (J₀ x) (τE x) ∂μ + smDefect QF QK QY θ₀ ec₀ (fun y => hKeGL (h0 y)) τ))
      := by
    simp only [hQn, hQ0, smDefect]
    convert (cF.add cK).add cY using 2
    ring
  -- the complete rows
  have hsplit : ∀ (θ' : CoefficientBank Ysec) (J : E4 → RJet (Fin 5)),
      Integrable (fun x => fullCov mY θ' (J x) (τE x) - quadMet θ' (J x) (τE x)) μ →
      Integrable (fun x => quadMet θ' (J x) (τE x)) μ →
      ∫ x, fullCov mY θ' (J x) (τE x) ∂μ =
        ∫ x, (fullCov mY θ' (J x) (τE x) - quadMet θ' (J x) (τE x)) ∂μ +
          ∫ x, quadMet θ' (J x) (τE x) ∂μ := by
    intro θ' J h1 h2
    rw [← integral_add h1 h2]
    simp only [sub_add_cancel]
  have hlim := hDt.add hQt
  simp only [← hsplit _ _ (hDn _) (sn _).1] at hlim
  rw [← add_assoc, ← hsplit _ _ hD0 s0.1] at hlim
  exact tendsto_nhds_unique hlim hzero

end MetricIdentity2


/-! ### The metric equation on a Coulomb cube -/

section Cube

variable {lo hi a b : E4}

/-- Values of a continuous coframe at points of the closed cube stay in the closed chart set. -/
theorem mem_Ke_of_closure {Ke : Set CoframeFibre} (hKe : IsCompact Ke) {f : E4 → CoframeFibre}
    (hf : Continuous f) (hfK : ∀ x ∈ box a b, f x ∈ Ke) (hlh : ∀ i, lo i < hi i)
    (hQK : box lo hi ⊆ box a b) (y : Icc lo hi) : f y.val ∈ Ke := by
  have hy : y.val ∈ closure (box a b) := closure_mono hQK (Icc_subset_closure_box hlh y.2)
  have := map_mem_closure hf hy (fun x hx => hfK x hx)
  rwa [hKe.isClosed.closure_eq] at this

/-- The `L⁴` integrability of the limit Higgs field on a cube. -/
theorem memLp_four_limit_higgs (hlh : ∀ i, lo i < hi i) {uinf : MIdx → Fin 5 → E4 → ℂ}
    {Gu : MIdx → Fin 5 → Fin 4 → E4 → ℂ} (q5 : ∀ s c, MemW12 (box lo hi) (uinf s c) (Gu s c)) :
    MemLp (fun x (i : Fin 2) => uinf none (Fin.natAdd 3 i) x) 4 (volume.restrict (box lo hi)) :=
  memLp_pi_iff.2 fun i => memLp_four_of_memW12_box hlh (q5 none (Fin.natAdd 3 i))

set_option maxHeartbeats 1000000 in
/-- **The metric equation `eq:critical-quotient-einstein` on a Coulomb cube.**  Under the
hypotheses of `cube_matter_equations`, with in addition the uniform (`L^∞`) coframe convergence of
(Q1) and covariance measures `𝖰_F, 𝖰_K, 𝖰_Y` of the curvature, covariant-Higgs-gradient and
quartic packets of the gauge-transformed fields (`IsDefect`, `lem:positive-packet-defect`), there is
a continuous representative `ec` of the limit coframe on the closed cube (values in the chart set)
such that for every smooth test `v` supported in the cube (metric tests included)
`∫_Q Cov_{θ₀}(j L)(j¹ v) + 𝔖(j¹ v) = 0`, `𝔖 = smDefect 𝖰_F 𝖰_K 𝖰_Y θ₀ ec`. -/
theorem cube_einstein_equation {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    (hlh : ∀ i, lo i < hi i) (hQK : box lo hi ⊆ box a b) {z : ℕ → FieldTuple (Fin 5)}
    {R : ℕ → E4 → M5}
    (hzA : ∀ n, ContDiff ℝ ∞ (z n).A) (hzH : ∀ n, ContDiff ℝ ∞ (z n).H)
    (hze : ∀ n, ContDiff ℝ ∞ (z n).e) (hz : ∀ n x, DiffAt (z n) x)
    (hlie : ∀ n x μ, (z n).A x μ ∈ smLie) (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x)
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL)
    (heK : ∀ n, ∀ x ∈ box a b, (z n).e x ∈ Ke)
    {e₀ : E4 → CoframeFibre} {de₀ : Fin 4 → Fin 4 → Fin 4 → E4 → ℝ}
    (he₀ : ∀ i ν, MemLp (fun y => e₀ y i ν) ⊤ (volume.restrict (box a b)))
    (hde₀ : ∀ i ν μ, MemLp (de₀ i ν μ) 2 (volume.restrict (box a b)))
    (hLinf : ∀ i ν, Tendsto (fun k => eLpNorm (fun y => (z k).e y i ν - e₀ y i ν) ⊤
      (volume.restrict (box a b))) atTop (𝓝 0))
    (hL2 : ∀ i ν, Tendsto (fun k => eLpNorm (fun y => (z k).e y i ν - e₀ y i ν) 2
      (volume.restrict (box a b))) atTop (𝓝 0))
    (hd : ∀ i ν μ, Tendsto (fun k => eLpNorm (fun y => pd (fun y => (z k).e y i ν) μ y -
      de₀ i ν μ y) 2 (volume.restrict (box a b))) atTop (𝓝 0))
    (hWA : ∀ n ν c e, MemW12 (box lo hi) (entries (gaugeConn (R n) (connM (z n).A)) ν c e)
      (entryGrad (gaugeConn (R n) (connM (z n).A)) ν c e))
    (hWu : ∀ n s c, MemW12 (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c))
    {Bu : ℝ≥0∞} (hBu : Bu ≠ ⊤)
    (hBu' : ∀ n s c, w12Norm (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c) ≤ Bu)
    {Ainf : Fin 4 → Fin 5 → Fin 5 → E4 → ℂ} {GA : Fin 4 → Fin 5 → Fin 5 → Fin 4 → E4 → ℂ}
    {uinf : MIdx → Fin 5 → E4 → ℂ} {Gu : MIdx → Fin 5 → Fin 4 → E4 → ℂ}
    (q1 : ∀ ν c e, MemW12 (box lo hi) (Ainf ν c e) (GA ν c e))
    (q2 : ∀ ν c e, Tendsto (fun n => eLpNorm (entries (gaugeConn (R n) (connM (z n).A)) ν c e -
      Ainf ν c e) 2 (volume.restrict (box lo hi))) atTop (𝓝 0))
    (q4 : ∀ μ ν c e (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • curvatureW (entries (gaugeConn (R n) (connM (z n).A)))
        (entryGrad (gaugeConn (R n) (connM (z n).A))) μ ν c e x ∂(volume.restrict (box lo hi)))
        atTop (𝓝 (∫ x, w x • curvatureW Ainf GA μ ν c e x ∂(volume.restrict (box lo hi)))))
    (q5 : ∀ s c, MemW12 (box lo hi) (uinf s c) (Gu s c))
    (q6 : ∀ s c, Tendsto (fun n => eLpNorm (transp (R n) (matterSec (z n) s) c - uinf s c) 2
      (volume.restrict (box lo hi))) atTop (𝓝 0))
    (q7 : ∀ s c μ (w : E4 → ℝ), MemLp w 2 (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • tgrad (R n) (matterSec (z n) s) c μ x
        ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • Gu s c μ x ∂(volume.restrict (box lo hi)))))
    (q8 : ∀ s c μ (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • (tgrad (R n) (matterSec (z n) s) c μ x +
          ∑ e, entries (gaugeConn (R n) (connM (z n).A)) μ c e x *
            transp (R n) (matterSec (z n) s) e x) ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • (Gu s c μ x + ∑ e, Ainf μ c e x * uinf s e x)
          ∂(volume.restrict (box lo hi)))))
    {MF : ℝ≥0∞} (hMF : MF ≠ ⊤)
    (hE : ∀ n, curvEnergy (gaugeConn (R n) (connM (z n).A)) (box lo hi) ≤ MF)
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hQ3c : ∀ n, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM (z n).A) (matterSec (z n) none) μ y e)
      2 (volume.restrict (box lo hi)) ≤ B)
    {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hs : ∀ j, Tendsto (fun n => gaugeScalars (θ n) j) atTop (𝓝 (gaugeScalars θ₀ j)))
    (hl : Tendsto (fun n => (θ n).lambdaH) atTop (𝓝 θ₀.lambdaH))
    (hv : Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH))
    (hk : Tendsto (fun n => (2 * (θ n).kappa)⁻¹) atTop (𝓝 (2 * θ₀.kappa)⁻¹))
    (hΛ : Tendsto (fun n => -(2 * (θ n).Lambda)) atTop (𝓝 (-(2 * θ₀.Lambda))))
    (hm : Tendsto (fun n => mY (θ n)) atTop (𝓝 (mY θ₀)))
    (hzero : ∀ v, IsSetTest (box lo hi) v → Tendsto (fun n => ∫ x in box lo hi,
      fullCov mY (θ n) (redJet (gaugeTuple (R n) (z n)) x) (testJet v x)) atTop (𝓝 0))
    {QF : StrongDual ℝ C(Icc lo hi, PIdx (Fin 4 → ConnFibre) → PIdx (Fin 4 → ConnFibre) → ℝ)}
    {QK : StrongDual ℝ C(Icc lo hi, PIdx (Fin 4 → HiggsFibre) → PIdx (Fin 4 → HiggsFibre) → ℝ)}
    {QY : StrongDual ℝ C(Icc lo hi, PIdx ℝ → PIdx ℝ → ℝ)}
    (dF : IsDefect (V0 lo hi) (fun n => pk lo hi (fun x => (redJet (gaugeTuple (R n) (z n)) x).F))
      (pk lo hi (fun x => (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x).F)) QF)
    (dK : IsDefect (V0 lo hi) (fun n => pk lo hi (fun x => (redJet (gaugeTuple (R n) (z n)) x).K))
      (pk lo hi (fun x => (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x).K)) QK)
    (dY : IsDefect (V0 lo hi)
      (fun n => pk lo hi (fun x => quartY (θ n) (redJet (gaugeTuple (R n) (z n)) x)))
      (pk lo hi (fun x => quartY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x))) QY) :
    ∃ (ec : C(Icc lo hi, CoframeFibre)) (hec : ∀ y, ec y ∈ Ke),
      (∀ᵐ y ∂(V0 lo hi), ec y = e₀ y.val) ∧
      ∀ v, IsSetTest (box lo hi) v → ∀ hc : Continuous (testJet v),
        (∫ x in box lo hi, fullCov mY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x)
            (testJet v x)) +
          smDefect QF QK QY θ₀ ec (fun y => hKeGL (hec y))
            ⟨fun y => testJet v y.val, hc.comp continuous_subtype_val⟩ = 0 := by
  have hzc : ∀ n, Continuous (z n).e := fun n => (hze n).continuous
  obtain ⟨ec, hconv, hae⟩ := exists_uniform_coframe hlh hQK hzc hLinf
  have hn : ∀ n (y : Icc lo hi), restrC lo hi (z n).e (hzc n) y ∈ Ke := fun n y =>
    mem_Ke_of_closure hKe (hzc n) (heK n) hlh hQK y
  have h0 : ∀ y, ec y ∈ Ke := fun y => by
    have h1 : Tendsto (fun n => restrC lo hi (z n).e (hzc n) y) atTop (𝓝 (ec y)) :=
      ((continuous_eval_const y).tendsto ec).comp hconv
    exact hKe.isClosed.mem_of_tendsto h1 (Eventually.of_forall fun n => hn n y)
  refine ⟨ec, h0, hae, fun v hvt hc => ?_⟩
  obtain ⟨hτc, ⟨C, hC⟩, L, hL⟩ := testJet_regular hvt
  have hrows := cube_limit_tendsto mY hlh hQK hzA hzH hze hz hlie hR hKe hKeGL heK he₀ hde₀ hL2 hd
    hWA hWu hBu hBu' q1 q2 q4 q5 q6 q7 q8 hMF hE hB hQ3c hs hl hv hk hΛ hm hτc hC hL
  have hF := weak_F_cube hlh hR (fun n x => (hz n x).A) hWA q1 q4 hMF hE
  have hK := weak_K_cube hlh hR hz hzA hzH hlie hWA hWu q1 q5 q8 hB hQ3c
  obtain ⟨-, hH, -, -, M, hM, hM4⟩ := strong_fields_cube hlh hWA hWu hBu hBu' q1 q2 q5 q6
  have hY := weakL2Data_quart hH hM (fun n => (hM4 n).1) (memLp_four_limit_higgs hlh q5) hv
  exact metric_identity mY (Jn := fun n x => redJet (gaugeTuple (R n) (z n)) x)
    (J₀ := fun x => limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x) hs hl hKe hKeGL hn h0 hconv
    (fun n y => rfl) hae hF hK hY dF dK dY (τE := testJet v)
    ⟨fun y => testJet v y.val, hc.comp continuous_subtype_val⟩ (fun y => rfl) hrows (hzero v hvt)

end Cube

end RenewalGeometry.CriticalQuotientRows
