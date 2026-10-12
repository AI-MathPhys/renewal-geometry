/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Continuum.EinsteinSMGravityFirstOrder
import MathPhys.Analysis.ScreenSubsequenceExtraction
import MathPhys.Analysis.W12CompactnessBox

/-!
# Chart boxes: geometry, `L^p` precompactness, screens, `H¹` components, smooth fields, banks

Generic tools for extraction on compact chart boxes: chart-box geometry (`ChartBox.isOpen`,
`ChartBox.isCompact_closure`, `ChartBox.closure_subset_cylSlab`), precompact sequences in `L^p`,
flattened packets and sup norms (`norm_pi_congr`, `norm_coframeC_eq`), screens in `L²(Q)`,
component bookkeeping for `H¹(Q)`, smooth fields on chart boxes (`memH1_spinor_of_smooth`), and
extraction of convergent coupling constants from a compact physical set (`bank_extract`).

Split out of `MathPhys.Continuum.EinsteinSMReducedExtraction` (`norm_coframeC_eq` out of
`MathPhys.Continuum.EinsteinSMCertificatePacket`); both re-export it; names are unchanged.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace MathPhys
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

/-! ### Coframe components -/

theorem norm_coframeC_eq (f : CoframeFibre) :
    ‖(fun p : Fin 4 × Fin 4 => ((f p.1 p.2 : ℝ) : ℂ))‖ = ‖f‖ := by
  refine (norm_curry_eq (fun a μ => ((f a μ : ℝ) : ℂ))).trans ?_
  exact norm_pi_congr fun a => norm_pi_congr fun μ => Complex.norm_real _

end EinsteinSM
end MathPhys
