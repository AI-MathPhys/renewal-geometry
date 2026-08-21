/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CollectivelyCompactLimit
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# From strong operator-and-adjoint convergence to norm convergence

This file removes the symmetry hypothesis from the collectively compact strong-to-norm upgrade.
For a bounded moving sequence, strong convergence of the adjoints forces the operator outputs to
converge weakly to zero.  Collective compactness then upgrades this weak information to norm
convergence.  Applied to differences, this proves operator-norm convergence from pointwise strong
convergence of both the operators and their adjoints.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]

/-- Pointwise strong convergence of the adjoints forces weak convergence of the outputs on every
bounded moving sequence. -/
theorem outputs_weakly_tendsto_zero_of_adjoint_strong
    (T : ℕ → H →L[K] H)
    (hadjoint : ∀ y : H, Tendsto (fun n ↦ ContinuousLinearMap.adjoint (T n) y) atTop (𝓝 0))
    (x : ℕ → H) (hx : ∀ n, ‖x n‖ ≤ 1) :
    ∀ y : H, Tendsto (fun n ↦ inner K (T n (x n)) y) atTop (𝓝 0) := by
  intro y
  refine squeeze_zero_norm (a := fun n ↦ ‖ContinuousLinearMap.adjoint (T n) y‖) ?_ ?_
  · intro n
    calc
      ‖inner K (T n (x n)) y‖ = ‖inner K (x n) (ContinuousLinearMap.adjoint (T n) y)‖ :=
        congrArg norm ((T n).adjoint_inner_right (x n) y).symm
      _ ≤ ‖x n‖ * ‖ContinuousLinearMap.adjoint (T n) y‖ :=
        norm_inner_le_norm (x n) (ContinuousLinearMap.adjoint (T n) y)
      _ ≤ ‖ContinuousLinearMap.adjoint (T n) y‖ := by
        simpa using mul_le_mul_of_nonneg_right (hx n)
          (norm_nonneg (ContinuousLinearMap.adjoint (T n) y))
  · simpa using (hadjoint y).norm

/-- A collectively compact family converges to zero in operator norm when both it and its
adjoints converge pointwise strongly to zero. -/
theorem norm_tendsto_zero_of_collectivelyCompact_of_adjointStrong
    (T : ℕ → H →L[K] H)
    (hcompact : (constantSystem K H).CollectivelyCompact T)
    (hadjoint : ∀ y : H, Tendsto (fun n ↦ ContinuousLinearMap.adjoint (T n) y) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ‖T n‖) atTop (𝓝 0) := by
  refine Filter.tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hnear (n : ℕ) :
      ∃ x : H, ‖x‖ < 1 ∧
        ‖T (ns n)‖ - 1 / ((n : ℝ) + 1) < ‖T (ns n) x‖ := by
    apply (T (ns n)).exists_lt_apply_of_lt_opNorm
    exact sub_lt_self _ (by positivity)
  choose x hx hTx using hnear
  obtain ⟨y, ψ, hψ, hout⟩ :=
    CollectivelyCompact.tendsto_reindexed_output_subseq
      (L := constantSystem K H) hcompact ns x (fun n ↦ (hx n).le)
  have hout' :
      Tendsto (fun k ↦ T (ns (ψ k)) (x (ψ k))) atTop (𝓝 y) := by
    simpa [constantSystem] using hout
  have hweak : ∀ z : H,
      Tendsto (fun n ↦ inner K (T (ns n) (x n)) z) atTop (𝓝 0) := by
    apply outputs_weakly_tendsto_zero_of_adjoint_strong
    · exact fun z ↦ (hadjoint z).comp hns
    · exact fun n ↦ (hx n).le
  have hy_inner (z : H) : inner K y z = 0 := by
    exact tendsto_nhds_unique (hout'.inner tendsto_const_nhds)
      ((hweak z).comp hψ.tendsto_atTop)
  have hy : y = 0 := inner_self_eq_zero.mp (hy_inner y)
  subst y
  have hout_norm :
      Tendsto (fun k ↦ ‖T (ns (ψ k)) (x (ψ k))‖) atTop (𝓝 0) := by
    simpa using hout'.norm
  have herr :
      Tendsto (fun k ↦ 1 / ((ψ k : ℝ) + 1)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop
  refine ⟨ψ, squeeze_zero
    (g := fun k ↦ ‖T (ns (ψ k)) (x (ψ k))‖ + 1 / ((ψ k : ℝ) + 1))
    (fun k ↦ norm_nonneg (T (ns (ψ k)))) ?_
    (by simpa using hout_norm.add herr)⟩
  intro k
  have hk := hTx (ψ k)
  linarith

/-- Strong convergence of a collectively compact family and its adjoints implies convergence in
the operator-norm topology.  Compactness of the limit follows automatically. -/
theorem tendsto_operatorNorm_of_collectivelyCompact_of_adjointStrong
    (T : ℕ → H →L[K] H) (Tlim : H →L[K] H)
    (hcompact : (constantSystem K H).CollectivelyCompact T)
    (hstrong : ∀ x : H, Tendsto (fun n ↦ T n x) atTop (𝓝 (Tlim x)))
    (hadjoint : ∀ y : H, Tendsto (fun n ↦ ContinuousLinearMap.adjoint (T n) y) atTop
      (𝓝 (ContinuousLinearMap.adjoint Tlim y))) :
    IsCompactOperator Tlim ∧ Tendsto T atTop (𝓝 Tlim) := by
  have hlim_compact := hcompact.isCompactOperator_limit T Tlim hstrong
  refine ⟨hlim_compact, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply norm_tendsto_zero_of_collectivelyCompact_of_adjointStrong
  · exact hcompact.sub (collectivelyCompact_const Tlim hlim_compact)
  · intro y
    simpa using (hadjoint y).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ContinuousLinearMap.adjoint Tlim y) atTop
        (𝓝 (ContinuousLinearMap.adjoint Tlim y)))

end NCG.VaryingHilbert.System
