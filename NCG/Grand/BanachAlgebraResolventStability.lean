/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Resolvent stability in Banach algebras

This file packages the spectral consequences of norm convergence which are repeatedly needed
after a collectively compact strong-to-norm upgrade.  A resolvent point of the limit remains a
resolvent point eventually, the corresponding resolvents converge in norm, and both conclusions
hold simultaneously on any finite set of contour nodes.  Consequently every finite Riesz
quadrature built from those nodes converges in norm.
-/

open Filter Topology
open scoped BigOperators

noncomputable section

namespace NCG.ResolventStability

universe u v w

variable {K : Type u} {A : Type v}
variable [NontriviallyNormedField K] [NormedRing A] [NormedAlgebra K A] [CompleteSpace A]

/-- A resolvent point of the norm limit is a resolvent point of all sufficiently late terms. -/
theorem eventually_mem_resolventSet_of_tendsto
    {I : Type w} {l : Filter I} {a : A} {aSeq : I → A}
    (ha : Tendsto aSeq l (𝓝 a)) {z : K} (hz : z ∈ resolventSet K a) :
    ∀ᶠ i in l, z ∈ resolventSet K (aSeq i) := by
  have hshift :
      Tendsto (fun i ↦ algebraMap K A z - aSeq i) l
        (𝓝 (algebraMap K A z - a)) :=
    tendsto_const_nhds.sub ha
  exact hshift.eventually (Units.isOpen.mem_nhds hz)

/-- Resolvents converge in Banach-algebra norm at every resolvent point of the limit. -/
theorem resolvent_tendsto_of_tendsto
    {I : Type w} {l : Filter I} {a : A} {aSeq : I → A}
    (ha : Tendsto aSeq l (𝓝 a)) {z : K} (hz : z ∈ resolventSet K a) :
    Tendsto (fun i ↦ resolvent (aSeq i) z) l (𝓝 (resolvent a z)) := by
  exact (spectrum.hasFDerivAt_resolvent hz).continuousAt.tendsto.comp ha

/-- Every node in a finite subset of the limit resolvent set remains a resolvent point
simultaneously at all sufficiently late stages. -/
theorem eventually_forall_mem_resolventSet_of_tendsto
    {I : Type w} {l : Filter I} {a : A} {aSeq : I → A}
    (ha : Tendsto aSeq l (𝓝 a)) (s : Finset K)
    (hs : ∀ z ∈ s, z ∈ resolventSet K a) :
    ∀ᶠ i in l, ∀ z ∈ s, z ∈ resolventSet K (aSeq i) := by
  rw [s.eventually_all]
  intro z hz
  exact eventually_mem_resolventSet_of_tendsto ha (hs z hz)

/-- A finite weighted Riesz-resolvent quadrature is continuous under norm convergence of its
operator argument, provided all quadrature nodes lie in the limit resolvent set. -/
theorem resolvent_finset_sum_tendsto
    {I : Type w} {l : Filter I} {a : A} {aSeq : I → A}
    (ha : Tendsto aSeq l (𝓝 a)) {J : Type*} (s : Finset J)
    (weight : J → K) (node : J → K)
    (hnode : ∀ j ∈ s, node j ∈ resolventSet K a) :
    Tendsto
      (fun i ↦ ∑ j ∈ s, weight j • resolvent (aSeq i) (node j)) l
      (𝓝 (∑ j ∈ s, weight j • resolvent a (node j))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds : Tendsto (fun _ : I ↦ (0 : A)) l (𝓝 0))
  | @insert j s hj ih =>
      have hjlim :=
        (resolvent_tendsto_of_tendsto ha (hnode j (Finset.mem_insert_self j s))).const_smul
          (weight j)
      have hslim := ih (fun k hk ↦ hnode k (Finset.mem_insert_of_mem hk))
      simpa [Finset.sum_insert, hj] using hjlim.add hslim
/-- Uniform resolvent bounds turn norm convergence of Banach-algebra elements into uniform
resolvent convergence on an arbitrary set of spectral parameters.  This is the quantitative
input used to pass from norm-resolvent convergence to contour-integral convergence. -/
theorem resolvent_tendstoUniformlyOn_of_uniform_bound
    {I : Type w} {l : Filter I} {a : A} {aSeq : I → A}
    (ha : Tendsto aSeq l (𝓝 a)) (s : Set K) (M N : ℝ)
    (hM : 0 ≤ M)
    (hlimit_unit : ∀ z ∈ s, z ∈ resolventSet K a)
    (hlimit_bound : ∀ z ∈ s, ‖resolvent a z‖ ≤ M)
    (hstage_unit : ∀ᶠ i in l, ∀ z ∈ s, z ∈ resolventSet K (aSeq i))
    (hstage_bound : ∀ᶠ i in l, ∀ z ∈ s, ‖resolvent (aSeq i) z‖ ≤ N) :
    TendstoUniformlyOn (fun i z ↦ resolvent (aSeq i) z) (resolvent a) l s := by
  have hnorm : Tendsto (fun i ↦ ‖aSeq i - a‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ha
  have herr : Tendsto (fun i ↦ (M * N) * ‖aSeq i - a‖) l (𝓝 0) := by
    simpa using hnorm.const_mul (M * N)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hstage_unit, hstage_bound, herr.eventually (gt_mem_nhds hε)]
    with i hiunit hibound hierr
  intro z hz
  have hid :
      resolvent a z - resolvent (aSeq i) z =
        resolvent a z *
          ((algebraMap K A z - aSeq i) - (algebraMap K A z - a)) *
            resolvent (aSeq i) z := by
    simpa [resolvent] using
      (Ring.inverse_sub_inverse
        (iff_of_true (hlimit_unit z hz) (hiunit z hz)))
  rw [dist_eq_norm, hid]
  calc
    ‖resolvent a z *
          ((algebraMap K A z - aSeq i) - (algebraMap K A z - a)) *
            resolvent (aSeq i) z‖
        ≤ (‖resolvent a z‖ *
            ‖(algebraMap K A z - aSeq i) - (algebraMap K A z - a)‖) *
              ‖resolvent (aSeq i) z‖ := by
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (M * ‖(algebraMap K A z - aSeq i) - (algebraMap K A z - a)‖) * N := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (hlimit_bound z hz) (norm_nonneg _)
          · exact hibound z hz
          · exact norm_nonneg _
          · exact mul_nonneg hM (norm_nonneg _)
    _ = (M * N) * ‖aSeq i - a‖ := by
          rw [show (algebraMap K A z - aSeq i) - (algebraMap K A z - a) =
            a - aSeq i by abel, norm_sub_rev]
          ring
    _ < ε := hierr

end NCG.ResolventStability
