/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact Fourier-output localization of the critical source

Machinery for `thm:NS-Fourier-output-localization`.  The donor carrier `E` and the output space
`H` carry finite orthogonal resolutions of the identity `R = (R_k)` and `P = (P_k)` indexed by
the output frequency `k`, and the critical source map `C : E →L[ℝ] H` intertwines them:
`P_k C = C R_k` (NS.F1).  Then

* `C = ∑_k (P_k C) R_k` (`block_decomp`);
* (NS.F2) the Gram is block diagonal: `C†C = ∑_k R_k C†C R_k` (`gram_block_diagonal`);
* (NS.F3) with `b_k = ‖R_k X‖²`, `c_k = ‖C R_k X‖²`, `‖X‖² = ∑ b_k`, `‖C X‖² = ∑ c_k`, and for
  `X ≠ 0` the influence ratio `‖C X‖² / ‖X‖²` is at most `max_{b_k > 0} c_k / b_k`
  (`influence_ratio_le`);
* every donor atom lying in one block is annihilated by every other block
  (`proj_apply_eq_zero_of_ne`).
-/

open ContinuousLinearMap
open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace FourierOutput

/-- A finite orthogonal resolution of the identity: self-adjoint idempotents summing to `I`
with pairwise zero products. -/
structure Resolution (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (κ : Type*) [Fintype κ] where
  /-- The block projections. -/
  proj : κ → V →L[ℝ] V
  selfAdjoint : ∀ k, IsSelfAdjoint (proj k)
  idem : ∀ k, proj k ∘L proj k = proj k
  orth : ∀ k j, k ≠ j → proj k ∘L proj j = 0
  sum_eq : ∑ k, proj k = 1

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {κ : Type*} [Fintype κ]

namespace Resolution

variable (R : Resolution V κ)

theorem sum_apply (x : V) : ∑ k, R.proj k x = x := by
  have h := congrArg (fun T : V →L[ℝ] V => T x) R.sum_eq
  simpa [_root_.sum_apply] using h

theorem proj_proj (k : κ) (x : V) : R.proj k (R.proj k x) = R.proj k x :=
  congrArg (fun T : V →L[ℝ] V => T x) (R.idem k)

theorem proj_proj_of_ne {k j : κ} (h : k ≠ j) (x : V) : R.proj k (R.proj j x) = 0 :=
  congrArg (fun T : V →L[ℝ] V => T x) (R.orth k j h)

theorem adjoint_proj (k : κ) : (R.proj k)† = R.proj k := isSelfAdjoint_iff'.mp (R.selfAdjoint k)

/-- Distinct blocks are orthogonal. -/
theorem inner_proj_of_ne {k j : κ} (h : k ≠ j) (x y : V) : ⟪R.proj k x, R.proj j y⟫ = 0 := by
  rw [← adjoint_proj R k, adjoint_inner_left, proj_proj_of_ne R h, inner_zero_right]

/-- Pythagoras along the resolution: `‖x‖² = ∑ₖ ‖R_k x‖²`. -/
theorem norm_sq_eq_sum (x : V) : ‖x‖ ^ 2 = ∑ k, ‖R.proj k x‖ ^ 2 := by
  classical
  conv_lhs => rw [← R.sum_apply x]
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_sum, ← real_inner_self_eq_norm_sq]
  rw [Finset.sum_eq_single k]
  · intro j _ hj
    exact R.inner_proj_of_ne (Ne.symm hj) x x
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- An atom lying in block `j` is annihilated by every other block. -/
theorem proj_apply_eq_zero_of_ne {j : κ} {x : V} (hx : R.proj j x = x) {k : κ} (hk : k ≠ j) :
    R.proj k x = 0 := by
  rw [← hx, proj_proj_of_ne R hk]

end Resolution

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (R : Resolution E κ) (P : Resolution H κ) (C : E →L[ℝ] H)
  (hC : ∀ k, P.proj k ∘L C = C ∘L R.proj k)
include hC

theorem proj_apply_comm (k : κ) (x : E) : P.proj k (C x) = C (R.proj k x) :=
  congrArg (fun T : E →L[ℝ] H => T x) (hC k)

/-- The adjoint intertwining `C† P_k = R_k C†`. -/
theorem adjoint_comm (k : κ) (y : H) : (C†) (P.proj k y) = R.proj k ((C†) y) := by
  have h := congrArg (fun T : E →L[ℝ] H => T†) (hC k)
  simp only [adjoint_comp, P.adjoint_proj, R.adjoint_proj] at h
  exact congrArg (fun T : H →L[ℝ] E => T y) h

/-- **(NS.F1)**: `C = ∑ₖ (P_k C) R_k`, the block decomposition by output frequency. -/
theorem block_decomp : C = ∑ k, (P.proj k ∘L C) ∘L R.proj k := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [_root_.sum_apply]
  conv_lhs => rw [← R.sum_apply x, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [comp_apply, comp_apply, proj_apply_comm R P C hC, R.proj_proj]

/-- **(NS.F2)**: the critical source Gram is block diagonal by output frequency. -/
theorem gram_block_diagonal : C† ∘L C = ∑ k, R.proj k ∘L (C† ∘L C) ∘L R.proj k := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [_root_.sum_apply]
  simp only [comp_apply]
  conv_lhs => rw [← P.sum_apply (C x), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [proj_apply_comm R P C hC, ← adjoint_comm R P C hC, ← proj_apply_comm R P C hC, P.proj_proj]

/-- The block energies `b_k = ‖R_k X‖²`. -/
noncomputable def donorEnergy (X : E) (k : κ) : ℝ := ‖R.proj k X‖ ^ 2

/-- The block influences `c_k = ‖C R_k X‖²`. -/
noncomputable def influence (X : E) (k : κ) : ℝ := ‖C (R.proj k X)‖ ^ 2

omit hC in
theorem norm_sq_donor (X : E) : ‖X‖ ^ 2 = ∑ k, donorEnergy R X k := R.norm_sq_eq_sum X

theorem norm_sq_image (X : E) : ‖C X‖ ^ 2 = ∑ k, influence R C X k := by
  rw [P.norm_sq_eq_sum (C X)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [influence, proj_apply_comm R P C hC]

omit hC in
theorem donorEnergy_nonneg (X : E) (k : κ) : 0 ≤ donorEnergy R X k := sq_nonneg _

omit [CompleteSpace H] hC in
theorem influence_eq_zero_of_donorEnergy_eq_zero (X : E) (k : κ)
    (h : donorEnergy R X k = 0) : influence R C X k = 0 := by
  have hx : R.proj k X = 0 := by
    rw [donorEnergy] at h
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
  rw [influence, hx, map_zero, norm_zero]
  ring

/-- **(NS.F3)**: the source-supported critical influence is a weighted average of the block
influence ratios, hence bounded by the largest one. -/
theorem influence_ratio_le (X : E) (hX : X ≠ 0) :
    ∃ hne : ((Finset.univ : Finset κ).filter fun k => 0 < donorEnergy R X k).Nonempty,
      ‖C X‖ ^ 2 / ‖X‖ ^ 2 = (∑ k, influence R C X k) / ∑ k, donorEnergy R X k ∧
      (∑ k, influence R C X k) / ∑ k, donorEnergy R X k
        ≤ ((Finset.univ : Finset κ).filter fun k => 0 < donorEnergy R X k).sup' hne
            fun k => influence R C X k / donorEnergy R X k := by
  classical
  have hsum : 0 < ∑ k, donorEnergy R X k := by
    rw [← norm_sq_donor]
    exact pow_pos (norm_pos_iff.mpr hX) 2
  have hne : ((Finset.univ : Finset κ).filter fun k => 0 < donorEnergy R X k).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
    have hzero : ∑ k, donorEnergy R X k = 0 :=
      Finset.sum_eq_zero fun k hk =>
        le_antisymm (not_lt.mp (hcon hk)) (donorEnergy_nonneg R X k)
    exact absurd hzero hsum.ne'
  refine ⟨hne, ?_, ?_⟩
  · rw [norm_sq_donor R X, norm_sq_image R P C hC X]
  · set M := ((Finset.univ : Finset κ).filter fun k => 0 < donorEnergy R X k).sup' hne
      fun k => influence R C X k / donorEnergy R X k with hM
    rw [div_le_iff₀ hsum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hb : 0 < donorEnergy R X k
    · have hle : influence R C X k / donorEnergy R X k ≤ M :=
        Finset.le_sup' (fun k => influence R C X k / donorEnergy R X k)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hb⟩)
      rw [div_le_iff₀ hb] at hle
      exact hle
    · have hb0 : donorEnergy R X k = 0 := le_antisymm (not_lt.mp hb) (donorEnergy_nonneg R X k)
      rw [influence_eq_zero_of_donorEnergy_eq_zero R C X k hb0, hb0, mul_zero]

/-- **`thm:NS-Fourier-output-localization`**: for a critical source map intertwining the donor
and output frequency resolutions, (NS.F1) the block decomposition, (NS.F2) the block-diagonal
Gram, (NS.F3) the block energies/influences sum to `‖X‖²`, `‖C X‖²` and the influence ratio is
bounded by the largest block ratio, and every donor atom in one block is annihilated by the
other blocks. -/
theorem ns_fourier_output_localization :
    C = ∑ k, (P.proj k ∘L C) ∘L R.proj k ∧
      C† ∘L C = ∑ k, R.proj k ∘L (C† ∘L C) ∘L R.proj k ∧
      (∀ X : E, ‖X‖ ^ 2 = ∑ k, donorEnergy R X k ∧ ‖C X‖ ^ 2 = ∑ k, influence R C X k) ∧
      (∀ X : E, X ≠ 0 →
        ∃ hne : ((Finset.univ : Finset κ).filter fun k => 0 < donorEnergy R X k).Nonempty,
          ‖C X‖ ^ 2 / ‖X‖ ^ 2 = (∑ k, influence R C X k) / ∑ k, donorEnergy R X k ∧
          (∑ k, influence R C X k) / ∑ k, donorEnergy R X k
            ≤ ((Finset.univ : Finset κ).filter fun k => 0 < donorEnergy R X k).sup' hne
                fun k => influence R C X k / donorEnergy R X k) ∧
      ∀ (j : κ) (x : E), R.proj j x = x → ∀ k : κ, k ≠ j → R.proj k x = 0 :=
  ⟨block_decomp R P C hC, gram_block_diagonal R P C hC,
    fun X => ⟨norm_sq_donor R X, norm_sq_image R P C hC X⟩,
    fun X hX => influence_ratio_le R P C hC X hX,
    fun _ _ hx _ hk => R.proj_apply_eq_zero_of_ne hx hk⟩

end FourierOutput
end NCG
