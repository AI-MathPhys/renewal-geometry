/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Depth-two common source-clock theorem
  (`thm:semantic-clock-depth-two-master`, flagship manuscript)

On the retained real carrier with self-adjoint score operator `A`
and loaded spectral components `z_j` (with commuting self-adjoint
block projections `P_j`, `P_j z_j = z_j`, `P_j z_i = 0` for
`i ≠ j` — the disclosed interface for `[𝒦, A] = 0`):

* the depth-two gap identity
  `‖(‖z‖²)Az - ⟨z,Az⟩z‖² = ‖z‖²(‖z‖²⟨z,A²z⟩ - ⟨z,Az⟩²)`
  (`depth_two_gap`, the Cauchy–Schwarz defect in exact form);
* blockwise (i)⇔(ii): `p_{j,1}² = w_j p_{j,2}` iff
  `A z_j = (p_{j,1}/w_j) z_j` (`semantic_block_depth_two`);
* boxed (iii): the common eigenvalue gives all moments
  `p_{j,n} = w_j aⁿ` (`semantic_depth_two_moments`);
* boxed (i)⇔(iv): with `Z = Σ z_j`, the global depth-two identity
  `p₀p₂ = p₁²` holds iff every loaded block satisfies
  `A z_j = a(q) z_j` with the common value `a(q) = p₁/p₀`
  (`semantic_global_flat_iff`) — one- and two-depth score
  successes prove the exact all-depth common source clock.
-/

open Finset
open scoped RealInnerProductSpace

namespace NCG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The depth-two Cauchy–Schwarz gap in exact form. -/
lemma depth_two_gap (A : E →L[ℝ] E) (z : E)
    (hsa : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) :
    ‖(‖z‖ ^ 2) • A z - ⟪z, A z⟫ • z‖ ^ 2
      = ‖z‖ ^ 2 * (‖z‖ ^ 2 * ⟪z, A (A z)⟫ - ⟪z, A z⟫ ^ 2) := by
  have hAz2 : ‖A z‖ ^ 2 = ⟪z, A (A z)⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    exact hsa z (A z)
  have hzz : ⟪z, z⟫ = ‖z‖ ^ 2 := real_inner_self_eq_norm_sq z
  have hcomm : ⟪A z, z⟫ = ⟪z, A z⟫ := real_inner_comm _ _
  rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right,
    hcomm, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, hAz2]
  ring_nf

/-- Blockwise depth-two theorem, (i)⇔(ii): the one-block
depth-two identity holds exactly on eigenvectors. -/
theorem semantic_block_depth_two (A : E →L[ℝ] E) (z : E)
    (hsa : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) (hz : z ≠ 0) :
    ⟪z, A z⟫ ^ 2 = ‖z‖ ^ 2 * ⟪z, A (A z)⟫
      ↔ A z = (⟪z, A z⟫ / ‖z‖ ^ 2) • z := by
  have hw : (0 : ℝ) < ‖z‖ ^ 2 := by positivity
  constructor
  · intro hflat
    have hgap := depth_two_gap A z hsa
    rw [show ‖z‖ ^ 2 * ⟪z, A (A z)⟫ - ⟪z, A z⟫ ^ 2 = 0 by
        linarith, mul_zero] at hgap
    have h0 : (‖z‖ ^ 2) • A z - ⟪z, A z⟫ • z = 0 := by
      rw [← norm_eq_zero]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hgap
    have h1 : (‖z‖ ^ 2) • A z = ⟪z, A z⟫ • z := sub_eq_zero.mp h0
    have h2 := congrArg (fun v => (‖z‖ ^ 2)⁻¹ • v) h1
    simp only [smul_smul] at h2
    rw [inv_mul_cancel₀ hw.ne', one_smul] at h2
    rw [div_eq_inv_mul]
    exact h2
  · intro heig
    rw [heig, map_smul, real_inner_smul_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp

/-- Eigenvalue powers. -/
lemma eig_pow (A : E →L[ℝ] E) (v : E) (a : ℝ)
    (h : A v = a • v) (n : ℕ) : (A ^ n) v = a ^ n • v := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    have happ : (A * A ^ m) v = A ((A ^ m) v) := rfl
    rw [happ, ih, map_smul, h, smul_smul, ← pow_succ]

/-- Boxed (iii): the common eigenvalue gives all moments
`p_{j,n} = w_j aⁿ`. -/
theorem semantic_depth_two_moments {s : ℕ} (A : E →L[ℝ] E)
    (z : Fin s → E) (a : ℝ) (heig : ∀ j, A (z j) = a • z j)
    (j : Fin s) (n : ℕ) :
    ⟪z j, (A ^ n) (z j)⟫ = a ^ n * ‖z j‖ ^ 2 := by
  rw [eig_pow A (z j) a (heig j) n, real_inner_smul_right,
    real_inner_self_eq_norm_sq]

/-- `thm:semantic-clock-depth-two-master`, boxed (i)⇔(iv): the
global depth-two identity `p₀p₂ = p₁²` holds iff every loaded
block carries the common clock eigenvalue `a(q) = p₁/p₀`. -/
theorem semantic_global_flat_iff {s : ℕ} (A : E →L[ℝ] E)
    (z : Fin s → E) (P : Fin s → E →L[ℝ] E)
    (hsa : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hPA : ∀ j x, P j (A x) = A (P j x))
    (hPsame : ∀ j, P j (z j) = z j)
    (hPdiff : ∀ i j, i ≠ j → P j (z i) = 0)
    (hZ : (∑ i, z i) ≠ 0) :
    ⟪∑ i, z i, A (∑ i, z i)⟫ ^ 2
        = ‖∑ i, z i‖ ^ 2 * ⟪∑ i, z i, A (A (∑ i, z i))⟫
      ↔ ∀ j, A (z j)
          = (⟪∑ i, z i, A (∑ i, z i)⟫ / ‖∑ i, z i‖ ^ 2) • z j := by
  have hPZ : ∀ j, P j (∑ i, z i) = z j := by
    intro j
    rw [map_sum]
    rw [Finset.sum_eq_single j (fun i _ hij => hPdiff i j hij)
      (fun h => absurd (mem_univ j) h)]
    exact hPsame j
  constructor
  · intro hflat
    have hglob := (semantic_block_depth_two A (∑ i, z i) hsa
      hZ).mp hflat
    intro j
    calc A (z j) = A (P j (∑ i, z i)) := by rw [hPZ j]
      _ = P j (A (∑ i, z i)) := (hPA j _).symm
      _ = P j ((⟪∑ i, z i, A (∑ i, z i)⟫ / ‖∑ i, z i‖ ^ 2)
            • (∑ i, z i)) := by conv_lhs => rw [hglob]
      _ = (⟪∑ i, z i, A (∑ i, z i)⟫ / ‖∑ i, z i‖ ^ 2)
            • z j := by rw [map_smul, hPZ j]
  · intro heig
    have hAZ : A (∑ i, z i)
        = (⟪∑ i, z i, A (∑ i, z i)⟫ / ‖∑ i, z i‖ ^ 2)
          • (∑ i, z i) := by
      conv_lhs => rw [map_sum]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => heig j
    exact (semantic_block_depth_two A (∑ i, z i) hsa hZ).mpr hAZ

end NCG
