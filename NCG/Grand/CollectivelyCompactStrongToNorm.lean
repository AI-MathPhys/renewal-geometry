/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCollectiveCompactness
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# From strong to norm convergence by collective compactness

This file proves the compactness upgrade used in norm-resolvent arguments.  On a fixed Hilbert
space, a collectively compact sequence of symmetric operators which converges strongly to zero
also converges to zero in operator norm.

The proof isolates the two genuinely analytic steps.  Symmetry and pointwise strong convergence
force the images of every bounded moving sequence to converge weakly to zero.  Collective
compactness supplies norm-convergent subsequences of those images, whose limits must therefore
vanish.  Near-maximizers for the operator norm then give norm convergence.
-/

open Filter Topology

noncomputable section

open scoped Pointwise
namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]

namespace System

/-- Symmetry turns pointwise strong convergence into weak convergence on every bounded moving
sequence.  This is the weak-limit step in collectively compact convergence arguments. -/
theorem symmetric_outputs_weakly_tendsto_zero
    (T : ℕ → H →L[K] H)
    (hsymm : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (hstrong : ∀ y : H, Tendsto (fun n ↦ T n y) atTop (𝓝 0))
    (x : ℕ → H) (hx : ∀ n, ‖x n‖ ≤ 1) :
    ∀ y : H, Tendsto (fun n ↦ inner K (T n (x n)) y) atTop (𝓝 0) := by
  intro y
  refine squeeze_zero_norm (a := fun n ↦ ‖T n y‖) ?_ ?_
  · intro n
    calc
      ‖inner K (T n (x n)) y‖ = ‖inner K (x n) (T n y)‖ :=
        congrArg norm (hsymm n (x n) y)
      _ ≤ ‖x n‖ * ‖T n y‖ := norm_inner_le_norm (x n) (T n y)
      _ ≤ ‖T n y‖ := by
        simpa using mul_le_mul_of_nonneg_right (hx n) (norm_nonneg (T n y))
  · simpa using (hstrong y).norm
/-- Collective compactness is stable under pointwise addition. -/
theorem CollectivelyCompact.add
    {T S : ℕ → H →L[K] H}
    (hT : (constantSystem K H).CollectivelyCompact T)
    (hS : (constantSystem K H).CollectivelyCompact S) :
    (constantSystem K H).CollectivelyCompact (fun n ↦ T n + S n) := by
  obtain ⟨C, hC, hTC⟩ := hT
  obtain ⟨D, hD, hSD⟩ := hS
  refine ⟨C + D, hC.add hD, ?_⟩
  intro n y hy
  obtain ⟨x, hx, rfl⟩ := hy
  change (T n + S n) x ∈ C + D
  rw [add_apply]
  exact Set.add_mem_add (hTC n ⟨x, hx, by rfl⟩) (hSD n ⟨x, hx, by rfl⟩)

/-- Collective compactness is stable under pointwise negation. -/
theorem CollectivelyCompact.neg
    {T : ℕ → H →L[K] H}
    (hT : (constantSystem K H).CollectivelyCompact T) :
    (constantSystem K H).CollectivelyCompact (fun n ↦ -T n) := by
  obtain ⟨C, hC, hTC⟩ := hT
  refine ⟨-C, hC.neg, ?_⟩
  intro n y hy
  obtain ⟨x, hx, rfl⟩ := hy
  change (-T n) x ∈ -C
  rw [neg_apply]
  exact Set.neg_mem_neg.mpr (hTC n ⟨x, hx, by rfl⟩)

/-- Collective compactness is stable under pointwise subtraction. -/
theorem CollectivelyCompact.sub
    {T S : ℕ → H →L[K] H}
    (hT : (constantSystem K H).CollectivelyCompact T)
    (hS : (constantSystem K H).CollectivelyCompact S) :
    (constantSystem K H).CollectivelyCompact (fun n ↦ T n - S n) := by
  simpa [sub_eq_add_neg] using hT.add hS.neg

/-- Repeating one compact operator gives a collectively compact constant family. -/
theorem collectivelyCompact_const
    (T : H →L[K] H) (hT : IsCompactOperator T) :
    (constantSystem K H).CollectivelyCompact (fun _ ↦ T) := by
  obtain ⟨C, hC, hsub⟩ := hT.image_closedBall_subset_compact 1
  refine ⟨C, hC, ?_⟩
  intro n
  simpa [embeddedOperator, constantSystem] using hsub
/-- A collectively compact sequence of symmetric operators which converges strongly to zero
converges to zero in operator norm.  This is the fixed-Hilbert-space compactness upgrade needed
to pass from strong resolvent convergence to norm resolvent convergence. -/
theorem norm_tendsto_zero_of_collectivelyCompact_of_symmetric
    (T : ℕ → H →L[K] H)
    (hcompact : (constantSystem K H).CollectivelyCompact T)
    (hsymm : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (hstrong : ∀ y : H, Tendsto (fun n ↦ T n y) atTop (𝓝 0)) :
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
    apply symmetric_outputs_weakly_tendsto_zero
    · exact fun n ↦ hsymm (ns n)
    · exact fun z ↦ (hstrong z).comp hns
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
/-- Strong convergence to a compact symmetric limit improves to convergence in the operator-norm
topology when the approximating family is collectively compact and symmetric. -/
theorem tendsto_operatorNorm_of_collectivelyCompact_of_symmetric
    (T : ℕ → H →L[K] H) (Tlim : H →L[K] H)
    (hcompact : (constantSystem K H).CollectivelyCompact T)
    (hlim_compact : IsCompactOperator Tlim)
    (hsymm : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (hlim_symm : LinearMap.IsSymmetric Tlim.toLinearMap)
    (hstrong : ∀ y : H, Tendsto (fun n ↦ T n y) atTop (𝓝 (Tlim y))) :
    Tendsto T atTop (𝓝 Tlim) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply norm_tendsto_zero_of_collectivelyCompact_of_symmetric
  · exact hcompact.sub (collectivelyCompact_const Tlim hlim_compact)
  · intro n
    exact (hsymm n).sub hlim_symm
  · intro y
    simpa using (hstrong y).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ Tlim y) atTop (𝓝 (Tlim y)))

end System

end NCG.VaryingHilbert
