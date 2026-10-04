/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.SMSTPositiveScreenExact

/-!
# Subsequence extraction through a common compact screen

Generic infrastructure (no renewal notions) for the compactness step of `thm:reduced-closure`
(Einstein–Standard-Model action-closure manuscript): the screen lemma `lem:screen`
(`SMSTChannel.screen_strong_convergence`) is stated for an already weakly convergent sequence and
with compactness rendered as complete continuity.  This file supplies the two missing links on a
separable complex Hilbert space:

* `exists_subseq_weakTendsto`: a norm-bounded sequence has a weakly convergent subsequence
  (sequential Banach–Alaoglu, `WeakDual.isSeqCompact_closedBall`, transported by the Riesz map);
* `IsCompactOperator.tendsto_of_weakTendsto` (**compact operators are completely continuous**):
  a compact operator maps bounded weakly convergent sequences to norm convergent ones;
* `exists_subseq_tendsto_of_screen`: a bounded sequence with screen data (bounded `S_{h,R}`,
  compact `S_R`, `‖S_{h,R} - S_R‖ → 0`, uniformly small tails, and `S_R Y → Y` on every weak
  subsequential limit) has, along every subsequence, a further **norm convergent** subsequence.
-/

open Filter Topology

noncomputable section

namespace RenewalGeometry
namespace ScreenExtraction

open SMSTChannel

variable {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

/-- **Weak sequential compactness of bounded sets** in a separable Hilbert space. -/
theorem exists_subseq_weakTendsto [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y]
    (x : ℕ → Y) (C : ℝ) (hbound : ∀ n, ‖x n‖ ≤ C) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ y : Y, WeakTendsto (fun k => x (ψ k)) y := by
  let φ : ℕ → WeakDual ℂ Y := fun n => StrongDual.toWeakDual (innerSL ℂ (x n))
  have hφmem : ∀ n,
      φ n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ Y) C := by
    intro n
    change dist (WeakDual.toStrongDual (φ n)) 0 ≤ C
    simpa [φ, dist_eq_norm, innerSL_apply_norm] using hbound n
  obtain ⟨φlim, -, ψ, hψ, hφlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℂ Y (0 : StrongDual ℂ Y) C) hφmem
  let y : Y := (InnerProductSpace.toDual ℂ Y).symm (WeakDual.toStrongDual φlim)
  refine ⟨ψ, hψ, y, fun z => ?_⟩
  have heval := (WeakDual.eval_continuous z).continuousAt.tendsto.comp hφlim
  have h1 : Tendsto (fun k => inner ℂ (x (ψ k)) z) atTop (𝓝 (inner ℂ y z)) := by
    simpa [φ, Function.comp_def, StrongDual.toWeakDual_apply, innerSL_apply_apply, y,
      InnerProductSpace.toDual_symm_apply, WeakDual.toStrongDual_apply] using heval
  have h2 := (Complex.continuous_conj.tendsto _).comp h1
  simpa [Function.comp_def, inner_conj_symm] using h2

/-- **Compact operators are completely continuous**: a compact operator on a Hilbert space maps
a bounded weakly convergent sequence to a norm convergent one. -/
theorem IsCompactOperator.tendsto_of_weakTendsto [CompleteSpace Y] {S : Y →L[ℂ] Y}
    (hS : IsCompactOperator S) {W : ℕ → Y} {Wlim : Y} {C : ℝ} (hb : ∀ n, ‖W n‖ ≤ C)
    (hw : WeakTendsto W Wlim) : Tendsto (fun n => S (W n)) atTop (𝓝 (S Wlim)) := by
  have hK : IsCompact (closure (S '' Metric.closedBall 0 C)) :=
    hS.isCompact_closure_image_closedBall C
  have hmem : ∀ n, S (W n) ∈ closure (S '' Metric.closedBall 0 C) := fun n =>
    subset_closure ⟨W n, by simpa [Metric.mem_closedBall, dist_zero_right] using hb n, rfl⟩
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨y, -, ψ, hψ, hlim⟩ := hK.tendsto_subseq fun k => hmem (ns k)
  refine ⟨ψ, ?_⟩
  have hweakS : ∀ z, Tendsto (fun k => inner ℂ z (S (W (ns (ψ k))))) atTop
      (𝓝 (inner ℂ z (S Wlim))) := by
    intro z
    have := (hw (ContinuousLinearMap.adjoint S z)).comp (hns.comp hψ.tendsto_atTop)
    simpa [Function.comp_def, ContinuousLinearMap.adjoint_inner_left] using this
  have hstr : ∀ z, Tendsto (fun k => inner ℂ z (S (W (ns (ψ k))))) atTop
      (𝓝 (inner ℂ z y)) := fun z =>
    ((continuous_const.inner continuous_id).tendsto y).comp hlim
  have hy : y = S Wlim := ext_inner_left ℂ fun z => tendsto_nhds_unique (hstr z) (hweakS z)
  rw [← hy]
  exact hlim

/-- **Subsequence extraction through a common compact screen.**  Let `Y_h` be bounded in a
separable Hilbert space, with bounded `S_{h,R}` and compact `S_R` such that
`‖S_{h,R} - S_R‖ → 0` for every `R`, the tails `‖Y_h - S_{h,R}Y_h‖` are uniformly small for
large `R`, and `S_R Y → Y` for every weak limit `Y` of a subsequence.  Then every subsequence of
`(Y_h)` has a further subsequence converging **in norm**. -/
theorem exists_subseq_tendsto_of_screen [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y]
    (Yh : ℕ → Y) {C : ℝ} (hb : ∀ n, ‖Yh n‖ ≤ C) (Sh : ℕ → ℕ → Y →L[ℂ] Y) (S : ℕ → Y →L[ℂ] Y)
    (hS : ∀ R, IsCompactOperator (S R))
    (hconv : ∀ R, Tendsto (fun h => ‖Sh h R - S R‖) atTop (𝓝 0))
    (htail : ∀ ε > (0 : ℝ), ∃ R₀, ∀ R ≥ R₀, ∀ h, ‖Yh h - Sh h R (Yh h)‖ ≤ ε)
    (hlimit : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ Ylim, WeakTendsto (Yh ∘ φ) Ylim →
      Tendsto (fun R => S R Ylim) atTop (𝓝 Ylim))
    (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ Ylim : Y, Tendsto (fun k => Yh (ns (ψ k))) atTop (𝓝 Ylim) := by
  obtain ⟨ψ, hψ, Ylim, hw⟩ := exists_subseq_weakTendsto (fun k => Yh (ns k)) C (fun k => hb _)
  refine ⟨ψ, hψ, Ylim, ?_⟩
  have hSR := hlimit (ns ∘ ψ) (hns.comp hψ) Ylim hw
  refine screen_strong_convergence (fun k => Yh (ns (ψ k))) Ylim C (fun k => hb _) hw S
    (fun R k => Sh (ns (ψ k)) R) (fun R => (hconv R).comp (hns.comp hψ).tendsto_atTop)
    (fun R W Wlim Cw hW hWw => IsCompactOperator.tendsto_of_weakTendsto (hS R) hW hWw)
    (fun ε hε => ?_) (fun ε hε => ?_)
  · obtain ⟨R₀, hR₀⟩ := htail ε hε
    exact ⟨R₀, fun R hR k => hR₀ R hR _⟩
  · obtain ⟨R₀, hR₀⟩ := (Metric.tendsto_atTop.mp hSR) ε hε
    refine ⟨R₀, fun R hR => ?_⟩
    have := hR₀ R hR
    rw [dist_eq_norm, norm_sub_rev] at this
    exact this.le

end ScreenExtraction
end RenewalGeometry
