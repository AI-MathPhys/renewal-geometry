/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMGravityFirstOrder
import RenewalGeometry.Analysis.ScreenSubsequenceExtraction
import RenewalGeometry.Analysis.W12CompactnessBox

/-!
# Extraction of reduced action convergence from the reduced compactness certificate
  (compactness step of `thm:reduced-closure`, Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMCompactnessCertificates.lean` (one compact chart rendered as a chart
box `Q`, trivialised bundles, `H¹(Q) = W^{1,2}(Q)` with weak gradients as data).  The proof of
`thm:reduced-closure` begins: "On a compact chart, the bounded `H¹` coframes are precompact in
`L²`.  The common screen lemma gives, after extraction, strong convergence of their first
derivatives. [...] The same screen argument gives strong `L²` convergence of the curvature and
covariant Higgs-gradient packets, while the assumed zeroth-order compactness gives `A_h → A` in
`L⁴`.  The identity `dA_h = F_{A_h} - A_h ∧ A_h` identifies the curvature limit with `F_A` in
distributions.  By `prop:covariant-higgs-endpoint` [...]  The two spinor families have weakly
convergent `H¹` subsequences [...] Extract the finite parameter bank as well."

This file carries out exactly these extractions on one chart box:

* geometry of chart boxes (`ChartBox.isOpen`, `ChartBox.closure_subset_cylSlab`,
  `ChartBox.isCompact_closure`);
* `LpPrecompact.exists_subseq_tendsto`: a precompact sequence in `L^p` has an `L^p`-convergent
  subsequence;
* `HasCommonCompactScreen.exists_subseq_tendsto`: an `L²`-bounded packet with a common compact
  screen has, along every subsequence, a further subsequence converging strongly in `L²(Q)`
  (`lem:screen` + weak compactness + complete continuity of compact operators);
* `memH1_of_smooth`: smooth multi-component fields lie in `H¹(Q)` with their classical gradients;
* `hasWeakCurvature_of_tendsto`: the curvature identity `F = dA + A ∧ A` passes to the limit
  (`A_h → A` in `L⁴`, `F_{A_h} → F` in `L²`);
* **`ReducedCertificate.exists_reducedConvergence`**: (R1)–(R5) on a chart box give a
  subsequence and limit fields with `ReducedConvergence` (`def:reduced-topology`) on that box;
* `ReducedCertificate.comp`: the certificate passes to subsequences.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Chart-box geometry -/

namespace ChartBox

variable {T : ℝ} (Q : ChartBox T)

theorem isOpen : IsOpen Q.set := SobolevOpen.isOpen_box Q.a Q.b

theorem volume_ne_top : volume Q.set ≠ ⊤ := SobolevOpen.volume_box_ne_top Q.a Q.b

theorem closure_subset_Icc : closure Q.set ⊆ univ.pi fun i => Icc (Q.a i) (Q.b i) :=
  closure_minimal (fun x hx i _ => Ioo_subset_Icc_self (hx i (mem_univ i)))
    (isClosed_set_pi fun _ _ => isClosed_Icc)

theorem isCompact_closure : IsCompact (closure Q.set) :=
  (isCompact_univ_pi fun i => isCompact_Icc (a := Q.a i) (b := Q.b i)).of_isClosed_subset
    isClosed_closure Q.closure_subset_Icc

theorem closure_subset_cylSlab : closure Q.set ⊆ cylSlab T := fun x hx => by
  have h := Q.closure_subset_Icc hx 0 (mem_univ 0)
  exact ⟨Q.time_pos.trans_le h.1, h.2.trans_lt Q.time_lt⟩

end ChartBox

/-! ### Precompact sequences in `L^p` -/

section LpPrecompactSec

variable {F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {μ : Measure E4}

/-- **A precompact sequence in `L^p` has convergent subsequences**: along every subsequence
there is a further `L^p`-convergent subsequence (`1 ≤ p < ∞`; `L^p` is complete). -/
theorem LpPrecompact.exists_subseq_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : ℕ → E4 → F}
    (hu : LpPrecompact p μ u) (ns : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ u₀ : E4 → F, MemLp u₀ p μ ∧
      LpTendsto p μ (fun k => u (ns (ψ k))) u₀ := by
  obtain ⟨hmem, hnet⟩ := hu
  set U : ℕ → Lp F p μ := fun n => (hmem n).toLp (u n)
  have htb : TotallyBounded (range U) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨s, hs⟩ := hnet ε hε
    refine ⟨U '' (s : Set ℕ), (s.finite_toSet.image U), ?_⟩
    rintro _ ⟨n, rfl⟩
    obtain ⟨m, hm, hnm⟩ := hs n
    refine mem_iUnion₂.mpr ⟨U m, mem_image_of_mem U hm, ?_⟩
    rw [Metric.mem_ball, dist_edist, Lp.edist_toLp_toLp]
    exact (ENNReal.toReal_lt_of_lt_ofReal hnm)
  obtain ⟨f, -, ψ, hψ, hlim⟩ := (isCompact_iff_totallyBounded_isComplete.2
    ⟨htb.closure, isClosed_closure.isComplete⟩).tendsto_subseq
    (fun n => subset_closure (mem_range_self (ns n)))
  refine ⟨ψ, hψ, f, Lp.memLp f, ?_⟩
  have h := (tendsto_iff_edist_tendsto_0.mp hlim)
  refine h.congr fun k => ?_
  simp only [Function.comp_apply, U, Lp.edist_def]
  exact eLpNorm_congr_ae ((MemLp.coeFn_toLp (hmem (ns (ψ k)))).mono fun x hx => by
    simp only [Pi.sub_apply, hx])

end LpPrecompactSec

/-! ### Flattened packets and sup norms -/

section Flatten

theorem norm_curry_eq {α β E : Type*} [Fintype α] [Fintype β] [SeminormedAddCommGroup E]
    (v : α → β → E) : ‖(fun q : α × β => v q.1 q.2)‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun q =>
    (norm_le_pi_norm (v q.1) q.2).trans (norm_le_pi_norm v q.1))
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun a =>
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun b =>
        norm_le_pi_norm (fun q : α × β => v q.1 q.2) (a, b))

theorem norm_pi_congr {α : Type*} [Fintype α] {E E' : α → Type*}
    [∀ a, SeminormedAddCommGroup (E a)] [∀ a, SeminormedAddCommGroup (E' a)]
    {v : ∀ a, E a} {w : ∀ a, E' a} (h : ∀ a, ‖v a‖ = ‖w a‖) : ‖v‖ = ‖w‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun a =>
    (h a).le.trans (norm_le_pi_norm w a))
    ((pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun a =>
      (h a).symm.le.trans (norm_le_pi_norm v a))

/-- Flattening `Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ` to the curvature-packet index is isometric. -/
theorem norm_curvature_flat (F : Fin 4 → Fin 4 → LieFibre) :
    ‖(fun q : Fin 4 × Fin 4 × Fin 5 × Fin 5 => F q.1 q.2.1 q.2.2.1 q.2.2.2)‖ = ‖F‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg F)).mpr fun q => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun μ =>
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun ν =>
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i =>
          (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_)
  · exact (norm_le_pi_norm (F q.1 q.2.1 q.2.2.1) q.2.2.2).trans
      ((norm_le_pi_norm (F q.1 q.2.1) q.2.2.1).trans
        ((norm_le_pi_norm (F q.1) q.2.1).trans (norm_le_pi_norm F q.1)))
  · exact norm_le_pi_norm (fun q : Fin 4 × Fin 4 × Fin 5 × Fin 5 =>
      F q.1 q.2.1 q.2.2.1 q.2.2.2) (μ, ν, i, j)

end Flatten

/-! ### Screens in `L²(Q)`: extraction at the level of functions -/

section ScreenFun

variable {T : ℝ} {ι' : Type} [Fintype ι']

instance (Q : ChartBox T) : SecondCountableTopology (L2Hilbert Q ι') := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  exact MeasureTheory.Lp.SecondCountableTopology

theorem norm_toLp_le_card (v : ι' → ℂ) :
    ‖WithLp.toLp 2 v‖ ≤ ((Fintype.card ι' : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal : ℝ≥0) * ‖v‖ := by
  have h := (PiLp.lipschitzWith_toLp 2 (fun _ : ι' => ℂ)).dist_le_mul v 0
  simpa [dist_zero_right] using h

theorem norm_ofLp_le (w : EuclideanSpace ℂ ι') : ‖WithLp.ofLp w‖ ≤ ‖w‖ := by
  have h := (PiLp.lipschitzWith_ofLp 2 (fun _ : ι' => ℂ)).dist_le_mul w 0
  simpa [dist_zero_right] using h

/-- **Strong `L²(Q)` subsequences from a common compact screen**: if a packet `P_h` is bounded in
`L²(Q)` and has a common compact screen there, every subsequence has a further subsequence
converging strongly in `L²(Q)` to some `P₀ ∈ L²(Q)`. -/
theorem HasCommonCompactScreen.exists_subseq_tendsto (Q : ChartBox T) {P : ℕ → E4 → ι' → ℂ}
    (hS : HasCommonCompactScreen Q P) (hB : LpBounded 2 Q.μ P) (ns : ℕ → ℕ)
    (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ P₀ : E4 → ι' → ℂ, MemLp P₀ 2 Q.μ ∧
      LpTendsto 2 Q.μ (fun k => P (ns (ψ k))) P₀ := by
  obtain ⟨Y, hY, Sh, S, hSc, hconv, htail, hlimit⟩ := hS
  obtain ⟨B, hBt, hBn⟩ := hB
  set c : ℝ≥0 := (Fintype.card ι' : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal
  have hb : ∀ n, ‖Y n‖ ≤ (c * B).toReal := by
    intro n
    rw [Lp.norm_def]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hBt) ?_
    rw [eLpNorm_congr_ae (hY n)]
    refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x =>
      norm_toLp_le_card (P n x)) 2).trans ?_
    rw [ENNReal.smul_def, smul_eq_mul]
    exact mul_le_mul_right (hBn n) _
  obtain ⟨ψ, hψ, Ylim, hlim⟩ := ScreenExtraction.exists_subseq_tendsto_of_screen Y hb Sh S hSc
    hconv htail hlimit ns hns
  refine ⟨ψ, hψ, fun x => WithLp.ofLp (Ylim x), ?_, ?_⟩
  · refine MemLp.of_le (Lp.memLp Ylim) ?_ (Eventually.of_forall fun x => norm_ofLp_le (Ylim x))
    exact (PiLp.continuous_ofLp 2 _).comp_aestronglyMeasurable (Lp.aestronglyMeasurable Ylim)
  · have h := tendsto_iff_edist_tendsto_0.mp hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
      fun k => ?_
    simp only [Lp.edist_def]
    refine eLpNorm_mono_ae ?_
    filter_upwards [hY (ns (ψ k))] with x hx
    simp only [Pi.sub_apply, hx]
    refine le_trans (le_of_eq ?_) (norm_ofLp_le (WithLp.toLp 2 (P (ns (ψ k)) x) - Ylim x))
    simp

end ScreenFun

/-! ### Component bookkeeping for `H¹(Q)` -/

section H1Comp

variable {T : ℝ} {ι' : Type} [Fintype ι']

/-- Component `W^{1,2}` norms are controlled by the multi-component `H¹` norm. -/
theorem w12Norm_comp_le (Q : ChartBox T) (u : E4 → ι' → ℂ) (g : E4 → Fin 4 → ι' → ℂ) (c : ι') :
    SobolevOpen.w12Norm Q.set (fun x => u x c) (fun i x => g x i c) ≤ 5 * h1Norm Q u g := by
  unfold SobolevOpen.w12Norm h1Norm
  have h1 : eLpNorm (fun x => u x c) 2 Q.μ ≤ eLpNorm u 2 Q.μ := eLpNorm_apply_le u c 2
  have h2 : ∀ i, eLpNorm (fun x => g x i c) 2 Q.μ ≤ eLpNorm g 2 Q.μ := fun i =>
    (eLpNorm_apply_le (fun x => g x i) c 2).trans (eLpNorm_apply_le g i 2)
  calc eLpNorm (fun x => u x c) 2 Q.μ + ∑ i, eLpNorm (fun x => g x i c) 2 Q.μ
      ≤ (eLpNorm u 2 Q.μ + eLpNorm g 2 Q.μ) + ∑ _i : Fin 4, (eLpNorm u 2 Q.μ + eLpNorm g 2 Q.μ) :=
        add_le_add (h1.trans le_self_add) (Finset.sum_le_sum fun i _ => (h2 i).trans le_add_self)
    _ = 5 * (eLpNorm u 2 Q.μ + eLpNorm g 2 Q.μ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Component bounds from a uniform `H¹` bound. -/
theorem H1Bounded.comp_bound {Q : ChartBox T} {u : ℕ → E4 → ι' → ℂ}
    {g : ℕ → E4 → Fin 4 → ι' → ℂ} (h : H1Bounded Q u g) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n c, SobolevOpen.w12Norm Q.set (fun x => u n x c)
      (fun i x => g n x i c) ≤ B := by
  obtain ⟨B, hBt, hB⟩ := h
  exact ⟨5 * B, ENNReal.mul_ne_top (by norm_num) hBt, fun n c =>
    (w12Norm_comp_le Q (u n) (g n) c).trans (mul_le_mul_right (hB n) _)⟩

/-- The gradient part of an `H¹` bound is an `L²` bound. -/
theorem H1Bounded.grad {Q : ChartBox T} {u : ℕ → E4 → ι' → ℂ}
    {g : ℕ → E4 → Fin 4 → ι' → ℂ} (h : H1Bounded Q u g) : LpBounded 2 Q.μ g := by
  obtain ⟨B, hBt, hB⟩ := h
  exact ⟨B, hBt, fun n => le_add_self.trans (hB n)⟩

/-- `L²` convergence of every component gives `L²` convergence of a multi-component field. -/
theorem lpTendsto_of_comp {Q : ChartBox T} {u : ℕ → E4 → ι' → ℂ} {u₀ : E4 → ι' → ℂ}
    (hm : ∀ n c, AEStronglyMeasurable (fun x => u n x c - u₀ x c) Q.μ)
    (h : ∀ c, Tendsto (fun n => eLpNorm (fun x => u n x c - u₀ x c) 2 Q.μ) atTop (𝓝 0)) :
    LpTendsto 2 Q.μ u u₀ :=
  tendsto_eLpNorm_of_apply (by norm_num) hm h

end H1Comp

/-! ### Smooth fields on chart boxes -/

section SmoothBox

variable {T : ℝ}

/-- **Smooth multi-component fields lie in `H¹(Q)`** with their classical gradients. -/
theorem memH1_of_smooth {ι' : Type} [Fintype ι'] (Q : ChartBox T) {u : E4 → ι' → ℂ}
    (hu : ContDiffOn ℝ ∞ u (cylSlab T)) : MemH1 Q u (fun x i c => pd u i x c) := by
  intro c
  have hc : ContDiffOn ℝ 1 (fun x => u x c) (cylSlab T) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι' => ℂ) c).contDiff.comp_contDiffOn
      (hu.of_le (by simp))
  refine memW12_congr_grad Q.isOpen.measurableSet
    (memW12_of_contDiffOn Q.isOpen (isOpen_cylSlab T) Q.isCompact_closure
      Q.closure_subset_cylSlab hc) fun i x hx => ?_
  exact pd_clm_comp (differentiableAt_of_contDiffOn_slab hu
    (Q.closure_subset_cylSlab (subset_closure hx)))
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι' => ℂ) c) i

/-- The spinor reshaping `Ψ ↦ ((s, c) ↦ Ψ_{s c})` as a continuous linear map. -/
def spinorFlatL (C : Type) [Fintype C] : SpinorFibre C →L[ℝ] (Fin 4 × C → ℂ) :=
  ContinuousLinearMap.pi fun p =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : C => ℂ) p.2).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => C → ℂ) p.1)

/-- **Smooth spinors lie in `H¹(Q)`** with the classical first-jet packet. -/
theorem memH1_spinor_of_smooth {C : Type} [Fintype C] (Q : ChartBox T) {Ψ : E4 → SpinorFibre C}
    (hΨ : ContDiffOn ℝ ∞ Ψ (cylSlab T)) : MemH1 Q (spinorC Ψ) (spinorGrad Ψ) := by
  have hs : ContDiffOn ℝ ∞ (spinorC Ψ) (cylSlab T) :=
    (spinorFlatL C).contDiff.comp_contDiffOn hΨ
  have h := memH1_of_smooth Q hs
  intro c
  refine memW12_congr_grad Q.isOpen.measurableSet (h c) fun i x hx => ?_
  have hd := differentiableAt_of_contDiffOn_slab hΨ (Q.closure_subset_cylSlab (subset_closure hx))
  have := pd_clm_comp hd (spinorFlatL C) i
  exact congrFun this c

end SmoothBox

/-! ### Step 1: the coframes (Rellich + the coframe screen) -/

section CoframeStep

variable {T : ℝ}

theorem norm_ofReal_sub_re_le (r : ℝ) (w : ℂ) : ‖(r : ℂ) - ((w.re : ℝ) : ℂ)‖ ≤ ‖(r : ℂ) - w‖ := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have := Complex.abs_re_le_norm ((r : ℂ) - w)
  simpa using this

/-- **Coframe extraction** (`thm:reduced-closure`, first step): coframes bounded in `H¹(Q)` with a
common compact screen for their first-derivative packet, with values a.e. in a closed set `𝒦_e`,
have (along any subsequence) a further subsequence converging strongly in `H¹(Q)` to an `H¹(Q)`
coframe with values a.e. in `𝒦_e`. -/
theorem coframe_extract (Q : ChartBox T) {e : ℕ → E4 → CoframeFibre}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (e n) (cylSlab T)) {Ke : Set CoframeFibre} (hKe : IsClosed Ke)
    (hKn : ∀ n, ∀ᵐ x ∂Q.μ, e n x ∈ Ke)
    (hB : H1Bounded Q (fun n => coframeC (e n)) (fun n => coframeGrad (e n)))
    (hS : HasCommonCompactScreen Q (fun n => coframeJetPacket (e n)))
    (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (e₀ : E4 → CoframeFibre) (de₀ : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ),
      (∀ᵐ x ∂Q.μ, e₀ x ∈ Ke) ∧ MemH1 Q (coframeC e₀) de₀ ∧
      H1Tendsto Q (fun k => coframeC (e (ns (ψ k)))) (fun k => coframeGrad (e (ns (ψ k))))
        (coframeC e₀) de₀ := by
  have hmem : ∀ n, MemH1 Q (coframeC (e n)) (coframeGrad (e n)) := fun n =>
    memH1_coframe_of_smooth Q Q.isCompact_closure Q.closure_subset_cylSlab (hsm n)
  obtain ⟨B, hBt, hBc⟩ := hB.comp_bound
  -- Rellich for the coframe components
  obtain ⟨φ₁, hφ₁, v, G, hvW, hvconv, -⟩ := SobolevOpen.w12_compactness_box (ι := Fin 4)
    (by simp) Q.lt (P := Fin 4 × Fin 4) (fun k p x => coframeC (e (ns k)) x p)
    (fun k p i x => coframeGrad (e (ns k)) x i p) (fun k p => hmem (ns k) p) hBt
    (fun k p => hBc (ns k) p)
  -- the screen for the first-derivative packet
  have hJB : LpBounded 2 Q.μ (fun n => coframeJetPacket (e n)) := by
    obtain ⟨B', hB't, hB'⟩ := hB.grad
    refine ⟨B', hB't, fun n => le_of_eq_of_le ?_ (hB' n)⟩
    exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => norm_curry_eq _)
  obtain ⟨ψ₂, hψ₂, P₀, hP₀, hPt⟩ := hS.exists_subseq_tendsto Q hJB (ns ∘ φ₁) (hns.comp hφ₁)
  set ψ := φ₁ ∘ ψ₂ with hψdef
  set e₀ : E4 → CoframeFibre := fun x a μ => (v (a, μ) x).re with he₀
  set de₀ : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ := fun x i p => P₀ x (i, p) with hde₀
  have hvL : ∀ p, MemLp (v p) 2 Q.μ := fun p => (hvW p).memLp
  have hcomp_meas : ∀ p, AEStronglyMeasurable (fun x => coframeC e₀ x p) Q.μ := fun p =>
    (Complex.continuous_ofReal.comp Complex.continuous_re).comp_aestronglyMeasurable (hvL p).1
  have hcL : ∀ p, MemLp (fun x => coframeC e₀ x p) 2 Q.μ := fun p =>
    MemLp.of_le (hvL p) (hcomp_meas p) (Eventually.of_forall fun x => by
      simp only [coframeC, he₀, Complex.norm_real, Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _)
  -- convergence of the values
  have hval : ∀ p, Tendsto (fun k => eLpNorm (fun x => coframeC (e (ns (ψ k))) x p -
      coframeC e₀ x p) 2 Q.μ) atTop (𝓝 0) := by
    intro p
    have h := (hvconv p 2 (by norm_num) (by norm_num)).comp hψ₂.tendsto_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
      fun k => eLpNorm_mono fun x => ?_
    simp only [Function.comp_apply, coframeC, he₀, Pi.sub_apply, hψdef]
    exact norm_ofReal_sub_re_le _ _
  have hvalv : LpTendsto 2 Q.μ (fun k => coframeC (e (ns (ψ k)))) (coframeC e₀) :=
    lpTendsto_of_comp (fun n p => ((hmem _ p).memLp.1).sub (hcomp_meas p)) hval
  -- convergence of the gradients
  have hgrad : LpTendsto 2 Q.μ (fun k => coframeGrad (e (ns (ψ k)))) de₀ := by
    refine hPt.congr fun k => ?_
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    have := norm_curry_eq (fun (i : Fin 4) (p : Fin 4 × Fin 4) =>
      coframeGrad (e (ns (φ₁ (ψ₂ k)))) x i p - P₀ x (i, p))
    exact this
  have hdeL : MemLp de₀ 2 Q.μ := by
    refine memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun p => ?_
    exact memLp_pi_iff.mp hP₀ (i, p)
  -- the limit lies in `H¹(Q)`
  have hmem₀ : MemH1 Q (coframeC e₀) de₀ := by
    intro p
    refine ⟨hcL p, fun i => memLp_pi_iff.mp (memLp_pi_iff.mp hdeL i) p, fun i => ?_⟩
    exact SobolevOpen.hasWeakPartial_of_tendsto Q.isOpen.measurableSet Q.volume_ne_top
      (fun k => (hmem (ns (ψ k)) p).weak i) (fun k => (hmem (ns (ψ k)) p).memLp)
      (fun k => (hmem (ns (ψ k)) p).memLp_grad i) (hcL p)
      (memLp_pi_iff.mp (memLp_pi_iff.mp hdeL i) p) (hval p)
      (tendsto_eLpNorm_apply (u := fun k x => coframeGrad (e (ns (ψ k))) x i)
        (tendsto_eLpNorm_apply hgrad i) p)
  have hconv : H1Tendsto Q (fun k => coframeC (e (ns (ψ k))))
      (fun k => coframeGrad (e (ns (ψ k)))) (coframeC e₀) de₀ := by
    have := hvalv.add hgrad
    simpa [H1Tendsto, h1Norm] using this
  refine ⟨ψ, hφ₁.comp hψ₂, e₀, de₀, ?_, hmem₀, hconv⟩
  -- the values of the limit stay in `𝒦_e`
  have hmeas := coframe_tendstoInMeasure (fun k => hmem (ns (ψ k))) hmem₀ hconv
  obtain ⟨σ, hσ, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂Q.μ, ∀ k, e (ns (ψ (σ k))) x ∈ Ke := ae_all_iff.mpr fun k => hKn _
  filter_upwards [hae, hall] with x hx hxK
  exact hKe.mem_of_tendsto hx (Eventually.of_forall hxK)

end CoframeStep

/-! ### Test pairings of strongly convergent sequences -/

section Pairings

variable {T : ℝ}

/-- Strong `L²(Q)` convergence of a vector field passes, through any fixed linear read-out, to
the pairings with test functions of `Q`. -/
theorem tendsto_test_clm (Q : ChartBox T) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℂ) {f : ℕ → E4 → V} {f₀ : E4 → V}
    (hf : RenewalGeometry.LpTendsto Q.μ 2 f f₀) {φ : E4 → ℝ} (hφ : IsTest Q.set φ) :
    Tendsto (fun n => ∫ x, ((φ x : ℝ) : ℂ) * L (f n x)) atTop
      (𝓝 (∫ x, ((φ x : ℝ) : ℂ) * L (f₀ x))) := by
  have h := FirstVariationCalculus.LpTendsto.clm_comp (μ := Q.μ) (p := 2) (by norm_num) L hf
  exact SobolevOpen.tendsto_integral_test_of_L2 Q.isOpen.measurableSet Q.volume_ne_top hφ
    h.memLp h.memLp_lim h.tendsto

/-- The entry `A ↦ (A_ν)_{ij}` of a connection value. -/
def connEntryL (ν : Fin 4) (i j : Fin 5) : ConnFibre →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℂ) j).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => Fin 5 → ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => LieFibre) ν))

/-- The commutator entry `(A, A') ↦ [A_μ, A'_ν]_{ij}` as a continuous bilinear map. -/
def commEntryL (μ ν : Fin 4) (i j : Fin 5) : ConnFibre →L[ℝ] ConnFibre →L[ℝ] ℂ :=
  addBilinL (fun A A' => comm (A μ) (A' ν) i j)
    (fun A A₂ A' => by simp only [comm, mmul, Pi.add_apply, Pi.sub_apply, add_mul,
      Finset.sum_add_distrib, mul_add]; ring)
    (fun A A' A₂ => by simp only [comm, mmul, Pi.add_apply, Pi.sub_apply, add_mul,
      Finset.sum_add_distrib, mul_add]; ring)
    (by unfold comm mmul; fun_prop)

/-- **Smooth connections satisfy the weak curvature identity** `F_A - A ∧ A = dA` on `Q`. -/
theorem hasWeakCurvature_smooth (Q : ChartBox T) {A : E4 → ConnFibre}
    (hA : ContDiffOn ℝ ∞ A (cylSlab T)) : HasWeakCurvature Q A (curvatureF A) := by
  intro μ ν i j φ hφ
  have hW : ∀ σ, MemW12 Q.set (fun x => connEntryL σ i j (A x))
      (fun τ => pd (fun x => connEntryL σ i j (A x)) τ) := fun σ =>
    memW12_of_contDiffOn Q.isOpen (isOpen_cylSlab T) Q.isCompact_closure
      Q.closure_subset_cylSlab ((connEntryL σ i j).contDiff.comp_contDiffOn (hA.of_le (by simp)))
  have hpd : ∀ σ τ, ∀ x ∈ Q.set, pd (fun x => connEntryL σ i j (A x)) τ x =
      pd (fun y => A y σ) τ x i j := by
    intro σ τ x hx
    have hd := differentiableAt_of_contDiffOn_slab hA (Q.closure_subset_cylSlab (subset_closure hx))
    rw [pd_clm_comp hd, pd_apply hd]
    rfl
  have hφ0 : ∀ x, x ∉ Q.set → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφ.subset h)
  have hint : ∀ σ τ, Integrable fun x => ((φ x : ℝ) : ℂ) * pd (fun x => connEntryL σ i j (A x)) τ x :=
    fun σ τ => hφ.integrable_mul hφ.continuous subset_rfl
      (SobolevOpen.locallyIntegrableOn_of_memLp ((hW σ).memLp_grad τ))
  have hint' : ∀ σ τ, Integrable fun x => ((pd φ τ x : ℝ) : ℂ) * connEntryL σ i j (A x) :=
    fun σ τ => hφ.integrable_mul (SobolevOpen.continuous_pd (hφ.smooth.of_le (by simp)) τ)
      (SobolevOpen.tsupport_pd_subset φ τ) (SobolevOpen.locallyIntegrableOn_of_memLp (hW σ).memLp)
  have e1 : ∀ x, ((φ x : ℝ) : ℂ) * (curvatureF A x μ ν i j - comm (A x μ) (A x ν) i j) =
      ((φ x : ℝ) : ℂ) * pd (fun x => connEntryL ν i j (A x)) μ x -
        ((φ x : ℝ) : ℂ) * pd (fun x => connEntryL μ i j (A x)) ν x := by
    intro x
    by_cases hx : x ∈ Q.set
    · rw [hpd ν μ x hx, hpd μ ν x hx, ← mul_sub]
      simp [curvatureF]
    · simp [hφ0 x hx]
  have w1 := (hW ν).weak μ φ hφ
  have w2 := (hW μ).weak ν φ hφ
  beta_reduce at w1 w2
  have r : (∫ x, (((pd φ μ x : ℝ) : ℂ) * A x ν i j - ((pd φ ν x : ℝ) : ℂ) * A x μ i j)) =
      (∫ x, ((pd φ μ x : ℝ) : ℂ) * connEntryL ν i j (A x)) -
        ∫ x, ((pd φ ν x : ℝ) : ℂ) * connEntryL μ i j (A x) :=
    integral_sub (hint' ν μ) (hint' μ ν)
  simp only [e1]
  rw [integral_sub (hint ν μ) (hint μ ν), r, w1, w2]
  ring

end Pairings

/-! ### Step 2: the connections -/

section ConnStep

variable {T : ℝ}

theorem isClosed_smLie : IsClosed (smLie : Set LieFibre) := smLie.closed_of_finiteDimensional

/-- **Connection extraction**: connections precompact in `L⁴(Q)` with values in `smLie` have, along
every subsequence, a further subsequence converging in `L⁴(Q)` to an `smLie`-valued limit. -/
theorem conn_extract (Q : ChartBox T) {A : ℕ → E4 → ConnFibre} (hlie : ∀ n x μ, A n x μ ∈ smLie)
    (hP : LpPrecompact 4 Q.μ A) (ns : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ A₀ : E4 → ConnFibre, MemLp A₀ 4 Q.μ ∧
      (∀ᵐ x ∂Q.μ, ∀ μ, A₀ x μ ∈ smLie) ∧ LpTendsto 4 Q.μ (fun k => A (ns (ψ k))) A₀ := by
  have : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ, A₀, hA₀, ht⟩ := hP.exists_subseq_tendsto ns
  refine ⟨ψ, hψ, A₀, hA₀, ?_, ht⟩
  have hm : TendstoInMeasure Q.μ (fun k => A (ns (ψ k))) atTop A₀ :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (fun k => (hP.1 _).1) hA₀.1 ht
  obtain ⟨σ, -, hae⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [hae] with x hx μ
  exact isClosed_smLie.mem_of_tendsto ((continuous_apply μ).continuousAt.tendsto.comp hx)
    (Eventually.of_forall fun k => hlie _ x μ)

end ConnStep

/-! ### Step 3: the curvatures -/

section CurvStep

variable {T : ℝ}

/-- **Weak curvature identity in the limit**: if `F_A - A ∧ A = dA` holds weakly along a sequence,
`A_h → A` in `L⁴(Q)` and `F_h → F` in `L²(Q)`, it holds for `(A, F)`. -/
theorem hasWeakCurvature_of_tendsto (Q : ChartBox T) {A : ℕ → E4 → ConnFibre}
    {F : ℕ → E4 → Fin 4 → Fin 4 → LieFibre} {A₀ : E4 → ConnFibre}
    {F₀ : E4 → Fin 4 → Fin 4 → LieFibre} (hW : ∀ n, HasWeakCurvature Q (A n) (F n))
    (hA : RenewalGeometry.LpTendsto Q.μ 4 A A₀) (hF : RenewalGeometry.LpTendsto Q.μ 2 F F₀) :
    HasWeakCurvature Q A₀ F₀ := by
  have : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  intro μ ν i j φ hφ
  have hA2 : RenewalGeometry.LpTendsto Q.μ 2 A A₀ := hA.mono (by norm_num) (by norm_num)
  have hC : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => commEntryL μ ν i j (A n x) (A n x))
      (fun x => commEntryL μ ν i j (A₀ x) (A₀ x)) :=
    RenewalGeometry.LpTendsto.bilin (commEntryL μ ν i j) hA hA
  have hFe : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => F n x μ ν i j) (fun x => F₀ x μ ν i j) :=
    FirstVariationCalculus.LpTendsto.clm_comp (by norm_num)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℂ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => Fin 5 → ℂ) i).comp
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => LieFibre) ν).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → LieFibre) μ)))) hF
  have hL : Tendsto (fun n => ∫ x, ((φ x : ℝ) : ℂ) * (F n x μ ν i j - comm (A n x μ) (A n x ν) i j))
      atTop (𝓝 (∫ x, ((φ x : ℝ) : ℂ) * (F₀ x μ ν i j - comm (A₀ x μ) (A₀ x ν) i j))) := by
    have h := SobolevOpen.tendsto_integral_test_of_L2 Q.isOpen.measurableSet Q.volume_ne_top hφ
      (fun n => (hFe.sub hC).memLp n) (hFe.sub hC).memLp_lim (hFe.sub hC).tendsto
    simpa [commEntryL] using h
  have hR : Tendsto (fun n => -∫ x, (((pd φ μ x : ℝ) : ℂ) * A n x ν i j -
      ((pd φ ν x : ℝ) : ℂ) * A n x μ i j)) atTop
      (𝓝 (-∫ x, (((pd φ μ x : ℝ) : ℂ) * A₀ x ν i j - ((pd φ ν x : ℝ) : ℂ) * A₀ x μ i j))) := by
    have h1 := tendsto_test_clm Q (connEntryL ν i j) hA2 (hφ.pd μ)
    have h2 := tendsto_test_clm Q (connEntryL μ i j) hA2 (hφ.pd ν)
    have hi : ∀ (B : E4 → ConnFibre), MemLp B 2 Q.μ → ∀ σ τ,
        Integrable fun x => ((pd φ τ x : ℝ) : ℂ) * B x σ i j := fun B hB σ τ =>
      (hφ.pd τ).integrable_mul (hφ.pd τ).continuous subset_rfl
        (SobolevOpen.locallyIntegrableOn_of_memLp
          ((connEntryL σ i j).comp_memLp' hB))
    refine ((h1.sub h2).neg).congr' (Eventually.of_forall fun n => ?_) |>.trans ?_
    · simp only [connEntryL, ContinuousLinearMap.coe_comp, ContinuousLinearMap.proj_apply,
        Function.comp_apply]
      rw [integral_sub (hi _ (hA2.memLp n) ν μ) (hi _ (hA2.memLp n) μ ν)]
    · simp only [connEntryL, ContinuousLinearMap.coe_comp, ContinuousLinearMap.proj_apply,
        Function.comp_apply]
      rw [integral_sub (hi _ hA2.memLp_lim ν μ) (hi _ hA2.memLp_lim μ ν)]
  exact tendsto_nhds_unique (hL.congr fun n => hW n μ ν i j φ hφ) hR

/-- **Curvature extraction**: smooth connections converging in `L⁴(Q)` along `ns`, with curvature
bounded in `L²(Q)` and with a common compact screen, have a further subsequence along which
`F_{A_h} → F` strongly in `L²(Q)`, and `F = F_A` weakly. -/
theorem curv_extract (Q : ChartBox T) {A : ℕ → E4 → ConnFibre}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (A n) (cylSlab T)) (ns : ℕ → ℕ) (hns : StrictMono ns)
    {A₀ : E4 → ConnFibre} (hA₀ : MemLp A₀ 4 Q.μ) (hAt : LpTendsto 4 Q.μ (fun k => A (ns k)) A₀)
    (hB : LpBounded 2 Q.μ (fun n => curvatureF (A n)))
    (hS : HasCommonCompactScreen Q (fun n => curvaturePacket (A n))) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ F₀ : E4 → Fin 4 → Fin 4 → LieFibre, MemLp F₀ 2 Q.μ ∧
      HasWeakCurvature Q A₀ F₀ ∧ LpTendsto 2 Q.μ (fun k => curvatureF (A (ns (ψ k)))) F₀ := by
  have hPB : LpBounded 2 Q.μ (fun n => curvaturePacket (A n)) := by
    obtain ⟨B, hBt, hBn⟩ := hB
    exact ⟨B, hBt, fun n => le_of_eq_of_le (eLpNorm_congr_norm_ae
      (Eventually.of_forall fun x => norm_curvature_flat _)) (hBn n)⟩
  obtain ⟨ψ, hψ, P₀, hP₀, hPt⟩ := hS.exists_subseq_tendsto Q hPB ns hns
  set F₀ : E4 → Fin 4 → Fin 4 → LieFibre := fun x μ ν i j => P₀ x (μ, ν, i, j) with hF₀
  have hFt : LpTendsto 2 Q.μ (fun k => curvatureF (A (ns (ψ k)))) F₀ := by
    refine hPt.congr fun k => eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    exact norm_curvature_flat (curvatureF (A (ns (ψ k))) x - F₀ x)
  have hFL : MemLp F₀ 2 Q.μ := by
    refine memLp_pi_iff.mpr fun μ => memLp_pi_iff.mpr fun ν => memLp_pi_iff.mpr fun i =>
      memLp_pi_iff.mpr fun j => ?_
    exact memLp_pi_iff.mp hP₀ (μ, ν, i, j)
  have hmF : ∀ n, MemLp (curvatureF (A n)) 2 Q.μ := fun n =>
    memLp_of_continuousOn_closure Q.isOpen Q.isCompact_closure
      ((continuousOn_curvatureF (hsm n)).mono Q.closure_subset_cylSlab) 2
  have hmA : ∀ n, MemLp (A n) 4 Q.μ := fun n =>
    memLp_of_continuousOn_closure Q.isOpen Q.isCompact_closure
      ((hsm n).continuousOn.mono Q.closure_subset_cylSlab) 4
  refine ⟨ψ, hψ, F₀, hFL, ?_, hFt⟩
  exact hasWeakCurvature_of_tendsto Q (fun k => hasWeakCurvature_smooth Q (hsm (ns (ψ k))))
    ⟨fun k => hmA _, hA₀, hAt.comp hψ.tendsto_atTop⟩ ⟨fun k => hmF _, hFL, hFt⟩

end CurvStep

/-! ### Step 4: the covariant Higgs gradient and the Higgs fields -/

section HiggsStep

variable {T : ℝ}

/-- `H¹(Q)` limits with covariant weak gradient give the weak identity `K = D_AH`. -/
theorem hasWeakCovGrad_of_memW12 (Q : ChartBox T) {A₀ : E4 → ConnFibre} {H₀ : E4 → HiggsFibre}
    {K₀ : E4 → Fin 4 → HiggsFibre}
    (hW : ∀ c, MemW12 Q.set (fun x => H₀ x c) (SobolevOpen.covGrad (fun c μ x => K₀ x μ c)
      (fun μ c e x => A₀ x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) (fun c x => H₀ x c) c)) :
    HasWeakCovGrad Q A₀ H₀ K₀ := by
  intro μ c φ hφ
  have h := (hW c).weak μ φ hφ
  rw [h]
  simp [SobolevOpen.covGrad, higgsAct]

/-- **Higgs extraction** (`prop:covariant-higgs-endpoint` inside `thm:reduced-closure`): smooth
Higgs fields bounded in `L²(Q)` whose covariant gradients are bounded in `L²(Q)` with a common
compact screen, for connections converging in `L⁴(Q)` along `ns`, have a further subsequence with
`D_{A_h}H_h → K` strongly in `L²(Q)` and `H_h → H` strongly in `L²(Q)`, `K = D_AH` weakly. -/
theorem higgs_extract (Q : ChartBox T) {A : ℕ → E4 → ConnFibre} {H : ℕ → E4 → HiggsFibre}
    (hsmA : ∀ n, ContDiffOn ℝ ∞ (A n) (cylSlab T)) (hsmH : ∀ n, ContDiffOn ℝ ∞ (H n) (cylSlab T))
    (ns : ℕ → ℕ) (hns : StrictMono ns) {A₀ : E4 → ConnFibre} (hA₀ : MemLp A₀ 4 Q.μ)
    (hAt : LpTendsto 4 Q.μ (fun k => A (ns k)) A₀) (hHB : LpBounded 2 Q.μ H)
    (hKB : LpBounded 2 Q.μ (fun n => covDerivHiggs (A n) (H n)))
    (hS : HasCommonCompactScreen Q (fun n => covGradPacket (A n) (H n))) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (H₀ : E4 → HiggsFibre) (K₀ : E4 → Fin 4 → HiggsFibre),
      MemLp H₀ 2 Q.μ ∧ MemLp K₀ 2 Q.μ ∧ HasWeakCovGrad Q A₀ H₀ K₀ ∧
      LpTendsto 2 Q.μ (fun k => H (ns (ψ k))) H₀ ∧
      LpTendsto 2 Q.μ (fun k => covDerivHiggs (A (ns (ψ k))) (H (ns (ψ k)))) K₀ := by
  have hPB : LpBounded 2 Q.μ (fun n => covGradPacket (A n) (H n)) := by
    obtain ⟨B, hBt, hBn⟩ := hKB
    exact ⟨B, hBt, fun n => le_of_eq_of_le (eLpNorm_congr_norm_ae
      (Eventually.of_forall fun x => norm_curry_eq _)) (hBn n)⟩
  obtain ⟨ψ₁, hψ₁, P₀, hP₀, hPt⟩ := hS.exists_subseq_tendsto Q hPB ns hns
  set K₀ : E4 → Fin 4 → HiggsFibre := fun x μ c => P₀ x (μ, c) with hK₀
  have hKt : LpTendsto 2 Q.μ (fun k => covDerivHiggs (A (ns (ψ₁ k))) (H (ns (ψ₁ k)))) K₀ := by
    refine hPt.congr fun k => eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    exact norm_curry_eq (covDerivHiggs (A (ns (ψ₁ k))) (H (ns (ψ₁ k))) x - K₀ x)
  have hKL : MemLp K₀ 2 Q.μ := memLp_pi_iff.mpr fun μ => memLp_pi_iff.mpr fun c =>
    memLp_pi_iff.mp hP₀ (μ, c)
  -- `prop:covariant-higgs-endpoint` along the extracted subsequence
  set σ := ns ∘ ψ₁ with hσ
  have hσt : Tendsto σ atTop atTop := (hns.comp hψ₁).tendsto_atTop
  have hAm : ∀ n, MemLp (A n) 4 Q.μ := fun n =>
    memLp_of_continuousOn_closure Q.isOpen Q.isCompact_closure
      ((hsmA n).continuousOn.mono Q.closure_subset_cylSlab) 4
  have hAc : ∀ n μ (c e : Fin 2), MemLp (fun x => A n x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) 4
      Q.μ := fun n μ c e =>
    memLp_pi_iff.mp (memLp_pi_iff.mp (memLp_pi_iff.mp (hAm n) μ) (Fin.natAdd 3 c)) (Fin.natAdd 3 e)
  have hA₀c : ∀ μ (c e : Fin 2), MemLp (fun x => A₀ x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) 4
      Q.μ := fun μ c e =>
    memLp_pi_iff.mp (memLp_pi_iff.mp (memLp_pi_iff.mp hA₀ μ) (Fin.natAdd 3 c)) (Fin.natAdd 3 e)
  have hAlim : ∀ μ (c e : Fin 2), Tendsto (fun k => eLpNorm
      ((fun x => A (σ k) x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) -
        fun x => A₀ x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) 4 Q.μ) atTop (𝓝 0) := fun μ c e =>
    tendsto_eLpNorm_apply (u := fun k x => A (σ k) x μ (Fin.natAdd 3 c))
      (tendsto_eLpNorm_apply (u := fun k x => A (σ k) x μ)
        (tendsto_eLpNorm_apply (hAt.comp hψ₁.tendsto_atTop) μ) (Fin.natAdd 3 c)) (Fin.natAdd 3 e)
  obtain ⟨B, hBt, hB⟩ := hHB
  have hYlim : ∀ (c : Fin 2) μ, Tendsto (fun k => eLpNorm
      (SobolevOpen.covD (fun c μ x => pd (H (σ k)) μ x c)
        (fun μ c e x => A (σ k) x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) (fun c x => H (σ k) x c) c μ -
        fun x => K₀ x μ c) 2 Q.μ) atTop (𝓝 0) := by
    intro c μ
    have h := tendsto_eLpNorm_apply (u := fun k x => covDerivHiggs (A (σ k)) (H (σ k)) x μ)
      (tendsto_eLpNorm_apply hKt μ) c
    refine h.congr fun k => ?_
    congr 1
  obtain ⟨φ₂, Hc, hφ₂, hHW, -, hHt, -, -⟩ := SobolevOpen.covariant_higgs_endpoint_box (ι := Fin 4)
    (by simp) Q.lt (fun k c x => H (σ k) x c) (fun k c μ x => pd (H (σ k)) μ x c)
    (fun k μ c e x => A (σ k) x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e))
    (fun μ c e x => A₀ x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) (fun c μ x => K₀ x μ c)
    (fun k c => memW12_higgs_of_smooth Q Q.isCompact_closure Q.closure_subset_cylSlab
      (hsmH (σ k)) c) (fun k μ c e => hAc (σ k) μ c e) hA₀c hAlim hBt
    (fun k c => (eLpNorm_apply_le (H (σ k)) c 2).trans (hB _))
    (fun c μ => memLp_pi_iff.mp (memLp_pi_iff.mp hKL μ) c) hYlim
  set H₀ : E4 → HiggsFibre := fun x c => Hc c x with hH₀
  have hHL : MemLp H₀ 2 Q.μ := memLp_pi_iff.mpr fun c => (hHW c).memLp
  refine ⟨ψ₁ ∘ φ₂, hψ₁.comp hφ₂, H₀, K₀, hHL, hKL, hasWeakCovGrad_of_memW12 Q hHW, ?_,
    hKt.comp hφ₂.tendsto_atTop⟩
  exact lpTendsto_of_comp (fun k c => ((memW12_higgs_of_smooth Q Q.isCompact_closure
    Q.closure_subset_cylSlab (hsmH _) c).memLp.1).sub ((hHW c).memLp.1)) fun c => hHt c

end HiggsStep

/-! ### Step 5: the spinors (weak `H¹` compactness) -/

section SpinorStep

variable {T : ℝ} {C : Type} [Fintype C]

/-- **Spinor extraction**: smooth spinors bounded in `H¹(Q)` have, along every subsequence, a
further subsequence converging weakly in `H¹(Q)` (`WeakH1Tendsto`). -/
theorem spinor_extract (Q : ChartBox T) {Ψ : ℕ → E4 → SpinorFibre C}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (Ψ n) (cylSlab T))
    (hB : H1Bounded Q (fun n => spinorC (Ψ n)) (fun n => spinorGrad (Ψ n))) (ns : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (Ψ₀ : E4 → SpinorFibre C) (dΨ₀ : E4 → Fin 4 → Fin 4 × C → ℂ),
      WeakH1Tendsto Q (fun k => spinorC (Ψ (ns (ψ k)))) (fun k => spinorGrad (Ψ (ns (ψ k))))
        (spinorC Ψ₀) dΨ₀ := by
  have hmem : ∀ n, MemH1 Q (spinorC (Ψ n)) (spinorGrad (Ψ n)) := fun n =>
    memH1_spinor_of_smooth Q (hsm n)
  obtain ⟨B, hBt, hBc⟩ := hB.comp_bound
  obtain ⟨φ, hφ, v, G, hvW, hvconv, hweak⟩ := SobolevOpen.w12_compactness_box (ι := Fin 4)
    (by simp) Q.lt (P := Fin 4 × C) (fun k p x => spinorC (Ψ (ns k)) x p)
    (fun k p i x => spinorGrad (Ψ (ns k)) x i p) (fun k p => hmem (ns k) p) hBt
    (fun k p => hBc (ns k) p)
  set Ψ₀ : E4 → SpinorFibre C := fun x s c => v (s, c) x with hΨ₀
  set dΨ₀ : E4 → Fin 4 → Fin 4 × C → ℂ := fun x i p => G p i x with hdΨ₀
  refine ⟨φ, hφ, Ψ₀, dΨ₀, fun k => hmem _, fun p => hvW p, ?_, fun χ hχ p => ?_,
    fun χ hχ i p => ?_⟩
  · obtain ⟨B', hB't, hB'⟩ := hB
    exact ⟨B', hB't, fun k => hB' _⟩
  · exact SobolevOpen.tendsto_integral_test_of_L2 Q.isOpen.measurableSet Q.volume_ne_top hχ
      (fun k => (hmem _ p).memLp) (hvW p).memLp (hvconv p 2 (by norm_num) (by norm_num))
  · have hχ0 : ∀ x, x ∉ Q.set → χ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hχ.subset h)
    have hχL : MemLp χ 2 Q.μ := by
      obtain ⟨M, hM⟩ := SobolevOpen.IsTest.exists_bound hχ
      exact MemLp.of_bound hχ.continuous.aestronglyMeasurable M (Eventually.of_forall hM)
    have hset : ∀ w : E4 → ℂ, ∫ x, χ x • w x ∂Q.μ = ∫ x, ((χ x : ℝ) : ℂ) * w x := by
      intro w
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hχ0 x hx]]
      simp only [Complex.real_smul]
    have h := hweak p i χ hχL
    beta_reduce at h
    convert h using 2 <;> exact (hset _).symm

end SpinorStep

/-! ### Step 6: the coefficient banks -/

section BankStep

variable {Ysec : Type} [Fintype Ysec]

/-- **Bank extraction**: banks in a compact subset of the physical region have a convergent
subsequence, with limit in that subset. -/
theorem bank_extract {θ : ℕ → CoefficientBank Ysec} {P : Set (CoefficientBank Ysec)}
    (hP : IsCompactBankSet P) (hθ : ∀ n, θ n ∈ P) (ns : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ θ₀ ∈ P, BankTendsto (fun k => θ (ns (ψ k))) θ₀ := by
  have : FirstCountableTopology (Matrix (Fin 3) (Fin 3) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin 3 → Fin 3 → ℂ))
  obtain ⟨c, ⟨θ₀, hθ₀, rfl⟩, ψ, hψ, hlim⟩ :=
    hP.1.tendsto_subseq (fun k => mem_image_of_mem bankCoords (hθ (ns k)))
  exact ⟨ψ, hψ, θ₀, hθ₀, hlim⟩

end BankStep

/-! ### Subsequences -/

section Subseq

variable {T : ℝ} {ι' : Type} [Fintype ι']

theorem H1Bounded.comp {Q : ChartBox T} {u : ℕ → E4 → ι' → ℂ} {g : ℕ → E4 → Fin 4 → ι' → ℂ}
    (h : H1Bounded Q u g) (ψ : ℕ → ℕ) : H1Bounded Q (fun k => u (ψ k)) (fun k => g (ψ k)) := by
  obtain ⟨B, hBt, hB⟩ := h
  exact ⟨B, hBt, fun k => hB _⟩

theorem LpBounded.comp {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {μ : Measure E4}
    {u : ℕ → E4 → F} (h : LpBounded p μ u) (ψ : ℕ → ℕ) : LpBounded p μ (fun k => u (ψ k)) := by
  obtain ⟨B, hBt, hB⟩ := h
  exact ⟨B, hBt, fun k => hB _⟩

theorem WeakH1Tendsto.comp {Q : ChartBox T} {u : ℕ → E4 → ι' → ℂ}
    {g : ℕ → E4 → Fin 4 → ι' → ℂ} {u₀ : E4 → ι' → ℂ} {g₀ : E4 → Fin 4 → ι' → ℂ}
    (h : WeakH1Tendsto Q u g u₀ g₀) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    WeakH1Tendsto Q (fun k => u (ψ k)) (fun k => g (ψ k)) u₀ g₀ :=
  ⟨fun k => h.1 _, h.2.1, h.2.2.1.comp ψ, fun φ hφ c => (h.2.2.2.1 φ hφ c).comp hψ,
    fun φ hφ i c => (h.2.2.2.2 φ hφ i c).comp hψ⟩

theorem CommonCompactScreen.comp {𝒴 : Type} [NormedAddCommGroup 𝒴] [InnerProductSpace ℂ 𝒴]
    {Y : ℕ → 𝒴} (h : CommonCompactScreen Y) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    CommonCompactScreen (fun k => Y (ψ k)) := by
  obtain ⟨Sh, S, hS, hconv, htail, hlim⟩ := h
  refine ⟨fun k R => Sh (ψ k) R, S, hS, fun R => (hconv R).comp hψ.tendsto_atTop,
    fun ε hε => ?_, fun φ hφ Ylim hw => hlim (ψ ∘ φ) (hψ.comp hφ) Ylim hw⟩
  obtain ⟨R₀, hR₀⟩ := htail ε hε
  exact ⟨R₀, fun R hR k => hR₀ R hR _⟩

theorem HasCommonCompactScreen.comp {Q : ChartBox T} {P : ℕ → E4 → ι' → ℂ}
    (h : HasCommonCompactScreen Q P) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    HasCommonCompactScreen Q (fun k => P (ψ k)) := by
  obtain ⟨Y, hY, hS⟩ := h
  exact ⟨fun k => Y (ψ k), fun k => hY _, hS.comp hψ⟩

theorem LpPrecompact.comp {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {μ : Measure E4}
    {u : ℕ → E4 → F} (h : LpPrecompact p μ u) (ψ : ℕ → ℕ) (hp : 1 ≤ p) :
    LpPrecompact p μ (fun k => u (ψ k)) := by
  obtain ⟨hmem, hnet⟩ := h
  refine ⟨fun k => hmem _, fun ε hε => ?_⟩
  -- an `ε/2`-net of the full sequence, re-centred at members of the subsequence
  obtain ⟨s, hs⟩ := hnet (ε / 2) (half_pos hε)
  classical
  set good : Finset ℕ := s.filter fun m => ∃ k, eLpNorm (u (ψ k) - u m) p μ < ENNReal.ofReal (ε / 2)
  have hchoice : ∀ m ∈ good, ∃ k, eLpNorm (u (ψ k) - u m) p μ < ENNReal.ofReal (ε / 2) :=
    fun m hm => (Finset.mem_filter.mp hm).2
  choose! κ hκ using hchoice
  refine ⟨good.image κ, fun k => ?_⟩
  obtain ⟨m, hm, hkm⟩ := hs (ψ k)
  have hmg : m ∈ good := Finset.mem_filter.mpr ⟨hm, k, hkm⟩
  refine ⟨κ m, Finset.mem_image_of_mem κ hmg, ?_⟩
  have htri : eLpNorm (u (ψ k) - u (ψ (κ m))) p μ ≤
      eLpNorm (u (ψ k) - u m) p μ + eLpNorm (u (ψ (κ m)) - u m) p μ := by
    have e : u (ψ k) - u (ψ (κ m)) = (u (ψ k) - u m) - (u (ψ (κ m)) - u m) := by abel
    rw [e]
    exact eLpNorm_sub_le ((hmem _).1.sub (hmem _).1) ((hmem _).1.sub (hmem _).1) hp
  refine htri.trans_lt ?_
  calc eLpNorm (u (ψ k) - u m) p μ + eLpNorm (u (ψ (κ m)) - u m) p μ
      < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add hkm (hκ m hmg)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

end Subseq

/-- **The reduced certificate passes to subsequences.** -/
theorem ReducedCertificate.comp {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type}
    [Fintype Ysec] {Q : ChartBox T} {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec}
    (h : ReducedCertificate Q z θ) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    ReducedCertificate Q (fun k => z (ψ k)) (fun k => θ (ψ k)) := by
  obtain ⟨Ke, hKe, hKn⟩ := h.coframe_chart
  obtain ⟨P, hP, hθP⟩ := h.bank_compact
  exact ⟨⟨Ke, hKe, fun k => hKn _⟩, h.coframe_bounded.comp ψ, h.coframe_screen.comp hψ,
    h.conn_precompact.comp ψ (by norm_num), h.curv_bounded.comp ψ, h.curv_screen.comp hψ,
    h.higgs_bounded.comp ψ, h.covgrad_bounded.comp ψ, h.covgrad_screen.comp hψ,
    h.spinor_bounded.comp ψ, h.cospinor_bounded.comp ψ, ⟨P, hP, fun k => hθP _⟩⟩

/-! ### The extraction theorem -/

/-- **Compactness step of `thm:reduced-closure`.**  A sequence of smooth reconstructed fields
satisfying the reduced compactness certificate (R1)–(R5) on a chart box `Q` has, along every
subsequence, a further subsequence converging in the reduced action topology on `Q`
(`def:reduced-topology`): strong `H¹` coframes with values (terms and limit) a.e. in the
certificate's compact coframe chart set, `L⁴` connections, `L²` curvatures identified weakly with
`F_A`, `L²` Higgs fields and covariant gradients identified weakly with `D_AH`, weak `H¹`
spinors and convergent banks in the compact physical set. -/
theorem ReducedCertificate.exists_reducedConvergence {T : ℝ} {C : Type} [Fintype C]
    {left : C → Bool} {Ysec : Type} [Fintype Ysec] {Q : ChartBox T}
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec}
    (h : ReducedCertificate Q z θ) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec),
      ReducedConvergence Q (fun k => z (ns (ψ k))) (fun k => θ (ns (ψ k))) L θ₀ := by
  obtain ⟨Ke, hKe, hKn⟩ := h.coframe_chart
  obtain ⟨P, hP, hθP⟩ := h.bank_compact
  -- coframes
  obtain ⟨ψ₁, hψ₁, e₀, de₀, he₀K, he₀, het⟩ := coframe_extract Q (fun n => (z n).smooth_e)
    hKe.1.isClosed hKn h.coframe_bounded h.coframe_screen ns hns
  set s₁ := ns ∘ ψ₁
  have hs₁ : StrictMono s₁ := hns.comp hψ₁
  -- connections
  obtain ⟨ψ₂, hψ₂, A₀, hA₀, hA₀lie, hAt⟩ := conn_extract Q (fun n x μ => (z n).lie x μ)
    h.conn_precompact s₁
  set s₂ := s₁ ∘ ψ₂
  have hs₂ : StrictMono s₂ := hs₁.comp hψ₂
  -- curvatures
  obtain ⟨ψ₃, hψ₃, F₀, hF₀, hF₀w, hFt⟩ := curv_extract Q (fun n => (z n).smooth_A) s₂ hs₂ hA₀
    hAt h.curv_bounded h.curv_screen
  set s₃ := s₂ ∘ ψ₃
  have hs₃ : StrictMono s₃ := hs₂.comp hψ₃
  -- Higgs fields and covariant gradients
  obtain ⟨ψ₄, hψ₄, H₀, K₀, hH₀, hK₀, hK₀w, hHt, hKt⟩ := higgs_extract Q
    (fun n => (z n).smooth_A) (fun n => (z n).smooth_H) s₃ hs₃ hA₀
    (hAt.comp hψ₃.tendsto_atTop) h.higgs_bounded h.covgrad_bounded h.covgrad_screen
  set s₄ := s₃ ∘ ψ₄
  have hs₄ : StrictMono s₄ := hs₃.comp hψ₄
  -- spinors
  obtain ⟨ψ₅, hψ₅, Ψ₀, dΨ₀, hΨw⟩ := spinor_extract Q (fun n => (z n).smooth_Ψ) h.spinor_bounded s₄
  set s₅ := s₄ ∘ ψ₅
  have hs₅ : StrictMono s₅ := hs₄.comp hψ₅
  obtain ⟨ψ₆, hψ₆, Ψb₀, dΨb₀, hΨbw⟩ := spinor_extract Q (fun n => (z n).smooth_Ψb)
    h.cospinor_bounded s₅
  set s₆ := s₅ ∘ ψ₆
  have hs₆ : StrictMono s₆ := hs₅.comp hψ₆
  -- banks
  obtain ⟨ψ₇, hψ₇, θ₀, -, hθt⟩ := bank_extract hP hθP s₆
  -- assembly
  have t₂ : Tendsto (ψ₂ ∘ ψ₃ ∘ ψ₄ ∘ ψ₅ ∘ ψ₆ ∘ ψ₇) atTop atTop :=
    (hψ₂.comp (hψ₃.comp (hψ₄.comp (hψ₅.comp (hψ₆.comp hψ₇))))).tendsto_atTop
  have t₃ : Tendsto (ψ₃ ∘ ψ₄ ∘ ψ₅ ∘ ψ₆ ∘ ψ₇) atTop atTop :=
    (hψ₃.comp (hψ₄.comp (hψ₅.comp (hψ₆.comp hψ₇)))).tendsto_atTop
  have t₄ : Tendsto (ψ₄ ∘ ψ₅ ∘ ψ₆ ∘ ψ₇) atTop atTop :=
    (hψ₄.comp (hψ₅.comp (hψ₆.comp hψ₇))).tendsto_atTop
  have t₅ : Tendsto (ψ₅ ∘ ψ₆ ∘ ψ₇) atTop atTop := (hψ₅.comp (hψ₆.comp hψ₇)).tendsto_atTop
  have t₆ : Tendsto (ψ₆ ∘ ψ₇) atTop atTop := (hψ₆.comp hψ₇).tendsto_atTop
  have t₇ : Tendsto ψ₇ atTop atTop := hψ₇.tendsto_atTop
  refine ⟨ψ₁ ∘ ψ₂ ∘ ψ₃ ∘ ψ₄ ∘ ψ₅ ∘ ψ₆ ∘ ψ₇,
    hψ₁.comp (hψ₂.comp (hψ₃.comp (hψ₄.comp (hψ₅.comp (hψ₆.comp hψ₇))))),
    ⟨e₀, de₀, A₀, F₀, H₀, K₀, Ψ₀, dΨ₀, Ψb₀, dΨb₀⟩, θ₀, ?_⟩
  exact
    { coframe_chart := ⟨Ke, hKe, fun k => hKn _, he₀K⟩
      coframe_mem := he₀
      coframe_tendsto := het.comp t₂
      conn_lie := hA₀lie
      conn_mem := hA₀
      conn_tendsto := hAt.comp t₃
      curv_mem := hF₀
      curv_weak := hF₀w
      curv_tendsto := hFt.comp t₄
      higgs_mem := hH₀
      higgs_tendsto := hHt.comp t₅
      covgrad_mem := hK₀
      covgrad_weak := hK₀w
      covgrad_tendsto := hKt.comp t₅
      spinor_weak := hΨw.comp t₆
      cospinor_weak := hΨbw.comp t₇
      bank_compact := ⟨P, hP, fun k => hθP _⟩
      bank_tendsto := hθt }

end EinsteinSM
end RenewalGeometry
