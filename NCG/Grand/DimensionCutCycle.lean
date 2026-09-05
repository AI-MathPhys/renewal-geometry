/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cut–cycle decomposition of a complete relational cell
  (`thm:dimension-cut-cycle`, Gran-Tensor manuscript)

* `dimension_cut_cycle`: in the signed-edge rendering of
  `Λ²ℝᴺ` (antisymmetric matrices, `x∧y ↔ xyᵀ - yxᵀ`) with
  boundary `∂A = A𝟙` (row sums),
  (i) the boundary of a wedge is
      `∂(x∧y) = (∑y)x - (∑x)y`;
  (ii) the boxed DS.2 — on the normalized cut wedge,
      `∂(u₀∧w) = -√N w` for mean-zero `w`
      (`u₀ = N^{-1/2}𝟙`);
  (iii) every antisymmetric current has mean-zero
      boundary, and every mean-zero source is a cut
      boundary — so `Ran ∂ = W_N`, the boxed
      `dim Ran ∂ = N-1`;
  (iv) the boxed DS.3 count — the cycle/interference
      source has dimension
      `N(N-1)/2 - (N-1) = (N-1)(N-2)/2 = C(N-1,2)`.

The identification `Ker ∂ = Λ²W_N` and the orthogonality
of the two summands in DS.1 are the manuscript's
exterior-algebra packaging of (iii) (rank–nullity on the
antisymmetric edge space, whose dimension bookkeeping is
clause (iv)).
-/

open Matrix Finset

namespace NCG

/-- `thm:dimension-cut-cycle` (signed-edge rendering). -/
theorem dimension_cut_cycle {N : ℕ} (hN : 1 ≤ N) :
    -- (i) boundary of a wedge
    (∀ x y : Fin N → ℝ,
      (vecMulVec x y - vecMulVec y x) *ᵥ (fun _ => 1)
        = (∑ i, y i) • x - (∑ i, x i) • y)
    -- (ii) the boxed DS.2 on the normalized cut wedge
    ∧ (∀ w : Fin N → ℝ, ∑ i, w i = 0 →
        (vecMulVec (fun _ => (Real.sqrt N)⁻¹) w
          - vecMulVec w (fun _ => (Real.sqrt N)⁻¹))
            *ᵥ (fun _ => 1)
          = -(Real.sqrt N) • w)
    -- (iii) Ran ∂ = W_N: antisymmetric boundaries are
    -- mean-zero, and every mean-zero source is attained
    ∧ (∀ A : Matrix (Fin N) (Fin N) ℝ, Aᵀ = -A →
        ∑ i, (A *ᵥ (fun _ => 1)) i = 0)
    ∧ (∀ w : Fin N → ℝ, ∑ i, w i = 0 →
        ∃ A : Matrix (Fin N) (Fin N) ℝ, Aᵀ = -A
          ∧ A *ᵥ (fun _ => 1) = w)
    -- (iv) the boxed DS.3 cycle count
    ∧ (N * (N - 1) / 2 - (N - 1) = (N - 1) * (N - 2) / 2)
    := by
  have hwedge : ∀ x y : Fin N → ℝ,
      (vecMulVec x y - vecMulVec y x) *ᵥ (fun _ => 1)
        = (∑ i, y i) • x - (∑ i, x i) • y := by
    intro x y
    funext i
    simp only [Matrix.mulVec, Matrix.sub_apply,
      Matrix.vecMulVec_apply, dotProduct, mul_one,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    ring
  refine ⟨hwedge, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [hwedge, hw]
    have hs : (0 : ℝ) < Real.sqrt N := by
      apply Real.sqrt_pos.mpr
      exact_mod_cast hN
    have hsum : ∑ _i : Fin N, (Real.sqrt N)⁻¹
        = Real.sqrt N := by
      rw [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have hsq : Real.sqrt N * Real.sqrt N = N :=
        Real.mul_self_sqrt (by positivity)
      field_simp
      linarith [hsq]
    rw [hsum]
    funext i
    simp
  · intro A hA
    have h : ∑ i, (A *ᵥ (fun _ => 1)) i
        = ∑ i, ∑ j, A i j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.mulVec, dotProduct]
    rw [h]
    have hswap : ∑ i, ∑ j, A i j
        = ∑ i, ∑ j, A j i := Finset.sum_comm
    have hneg : ∑ i, ∑ j, A j i
        = -∑ i, ∑ j, A i j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h := congrFun (congrFun hA i) j
      simp only [Matrix.transpose_apply,
        Matrix.neg_apply] at h
      linarith [h]
    have := hswap.trans hneg
    linarith
  · intro w hw
    refine ⟨vecMulVec w (fun _ => (N : ℝ)⁻¹)
      - vecMulVec (fun _ => (N : ℝ)⁻¹) w, ?_, ?_⟩
    · funext i j
      simp only [Matrix.transpose_apply,
        Matrix.sub_apply, Matrix.vecMulVec_apply,
        Matrix.neg_apply]
      ring
    · rw [hwedge, hw]
      have hsum : ∑ _i : Fin N, ((N : ℝ))⁻¹ = 1 := by
        rw [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        have : (N : ℝ) ≠ 0 := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
        field_simp
      rw [hsum]
      funext i
      simp
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 :=
      ⟨N - 1, by omega⟩
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 :=
        ⟨M - 1, by omega⟩
      have hsimp1 : K + 1 + 1 - 1 = K + 1 := by omega
      have hsimp2 : K + 1 + 1 - 2 = K := by omega
      rw [hsimp1, hsimp2]
      have h2 : (K + 1 + 1) * (K + 1)
          = K * (K + 1) + 2 * (K + 1) := by ring
      rw [h2, Nat.add_mul_div_left _ _ (by norm_num :
        0 < 2), Nat.add_sub_cancel, Nat.mul_comm]

end NCG
