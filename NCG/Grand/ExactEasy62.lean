/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.OneWayLyapunov

/-!
# Exact EASY 62: one-way provenance block aggregation

This file supplies the missing Euclidean direct-sum norm estimate and uses
it to assemble the manuscript's exact constant
`M_R = max 1 (M_A + M_D + M_A M_D c / (r - max a d))`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Norms.L2Operator

namespace NCG

variable {l e : Type*} [Fintype l] [Fintype e]

def leftPart (x : EuclideanSpace ℂ (l ⊕ e)) : EuclideanSpace ℂ l :=
  WithLp.toLp 2 (fun i => WithLp.ofLp x (Sum.inl i))

def rightPart (x : EuclideanSpace ℂ (l ⊕ e)) : EuclideanSpace ℂ e :=
  WithLp.toLp 2 (fun i => WithLp.ofLp x (Sum.inr i))

lemma leftPart_norm_le (x : EuclideanSpace ℂ (l ⊕ e)) :
    ‖leftPart x‖ ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [EuclideanSpace.norm_sq_eq, leftPart]
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma rightPart_norm_le (x : EuclideanSpace ℂ (l ⊕ e)) :
    ‖rightPart x‖ ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [EuclideanSpace.norm_sq_eq, rightPart]
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma sumElim_norm_le_add (u : EuclideanSpace ℂ l) (v : EuclideanSpace ℂ e) :
    ‖WithLp.toLp 2 (Sum.elim (WithLp.ofLp u) (WithLp.ofLp v))‖ ≤ ‖u‖ + ‖v‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  rw [← EuclideanSpace.norm_sq_eq u, ← EuclideanSpace.norm_sq_eq v]
  nlinarith [norm_nonneg u, norm_nonneg v]

lemma l2_opNorm_fromBlocks_oneway_le
    [DecidableEq l] [DecidableEq e]
    (A : Matrix l l ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    ‖Matrix.fromBlocks A 0 C D‖ ≤ ‖A‖ + ‖C‖ + ‖D‖ := by
  rw [Matrix.cstar_norm_def]
  refine ((Matrix.toEuclideanCLM (n := l ⊕ e) (𝕜 := ℂ))
    (Matrix.fromBlocks A 0 C D)).opNorm_le_bound
    (by positivity) fun x => ?_
  let xL : EuclideanSpace ℂ l := leftPart x
  let xR : EuclideanSpace ℂ e := rightPart x
  let yA : EuclideanSpace ℂ l := WithLp.toLp 2 (A *ᵥ WithLp.ofLp xL)
  let yC : EuclideanSpace ℂ e := WithLp.toLp 2 (C *ᵥ WithLp.ofLp xL)
  let yD : EuclideanSpace ℂ e := WithLp.toLp 2 (D *ᵥ WithLp.ofLp xR)
  have hout : (Matrix.toEuclideanCLM (n := l ⊕ e) (𝕜 := ℂ))
      (Matrix.fromBlocks A 0 C D) x
      = WithLp.toLp 2 (Sum.elim (WithLp.ofLp yA)
          (WithLp.ofLp (yC + yD))) := by
    apply WithLp.ofLp_injective 2
    rw [Matrix.ofLp_toEuclideanCLM]
    funext i
    cases i with
    | inl i => simp [xL, xR, yA, yC, yD, leftPart, rightPart,
        Matrix.mulVec, dotProduct]
    | inr i => simp [xL, xR, yA, yC, yD, leftPart, rightPart,
        Matrix.mulVec, dotProduct]
  have hA := Matrix.l2_opNorm_mulVec A xL
  have hC := Matrix.l2_opNorm_mulVec C xL
  have hD := Matrix.l2_opNorm_mulVec D xR
  have hxL := leftPart_norm_le x
  have hxR := rightPart_norm_le x
  rw [hout]
  calc
    ‖WithLp.toLp 2 (Sum.elim (WithLp.ofLp yA)
        (WithLp.ofLp (yC + yD)))‖
        ≤ ‖yA‖ + ‖yC + yD‖ := sumElim_norm_le_add yA (yC + yD)
    _ ≤ ‖yA‖ + (‖yC‖ + ‖yD‖) :=
      add_le_add (le_refl _) (norm_add_le _ _)
    _ ≤ ‖A‖ * ‖xL‖ + (‖C‖ * ‖xL‖ + ‖D‖ * ‖xR‖) := by
      exact add_le_add hA (add_le_add hC hD)
    _ ≤ ‖A‖ * ‖x‖ + (‖C‖ * ‖x‖ + ‖D‖ * ‖x‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hxL (norm_nonneg A))
        (add_le_add
          (mul_le_mul_of_nonneg_left hxL (norm_nonneg C))
          (mul_le_mul_of_nonneg_left hxR (norm_nonneg D)))
    _ = (‖A‖ + ‖C‖ + ‖D‖) * ‖x‖ := by ring

theorem one_way_provenance_uniform_power {l e : Type*} [Fintype l]
    [Fintype e] [DecidableEq l] [DecidableEq e]
    (A : Matrix l l ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (MA MD c a d r : ℝ)
    (hA : ∀ n, ‖A ^ n‖ ≤ MA * a ^ n)
    (hD : ∀ n, ‖D ^ n‖ ≤ MD * d ^ n)
    (hC : ‖C‖ ≤ c)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hMA : 0 ≤ MA) (hMD : 0 ≤ MD)
    (hc0 : 0 ≤ c) (hq : max a d < r) (hr1 : r < 1) :
    ∀ n, ‖Matrix.fromBlocks A 0 C D ^ n‖ ≤
      max 1 (MA + MD + MA * MD * c / (r - max a d)) * r ^ n := by
  let K : ℝ := MA * MD * c / (r - max a d)
  let S : ℝ := MA + MD + K
  have hq0 : 0 ≤ max a d := le_trans ha (le_max_left _ _)
  have hr0 : 0 ≤ r := (lt_of_le_of_lt hq0 hq).le
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  rcases one_way_provenance_power A C D MA MD c a d r
      hA hD hC ha hd hMA hMD hc0 hq hr1 with ⟨hblock, _, hcorner⟩
  intro n
  rw [hblock n]
  calc
    ‖Matrix.fromBlocks (A ^ n) 0
        (∑ j ∈ Finset.range n, D ^ (n - 1 - j) * C * A ^ j) (D ^ n)‖
        ≤ ‖A ^ n‖ +
            ‖∑ j ∈ Finset.range n, D ^ (n - 1 - j) * C * A ^ j‖ +
            ‖D ^ n‖ := l2_opNorm_fromBlocks_oneway_le _ _ _
    _ ≤ MA * a ^ n + K * r ^ n + MD * d ^ n := by
      exact add_le_add (add_le_add (hA n) (by simpa [K] using hcorner n)) (hD n)
    _ ≤ MA * r ^ n + K * r ^ n + MD * r ^ n := by
      have har : a ≤ r := le_trans (le_max_left a d) hq.le
      have hdr : d ≤ r := le_trans (le_max_right a d) hq.le
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha har n) hMA)
          (le_refl _))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd hdr n) hMD)
    _ = S * r ^ n := by simp [S]; ring
    _ ≤ max 1 S * r ^ n :=
      mul_le_mul_of_nonneg_right (le_max_right 1 S) (pow_nonneg hr0 n)
    _ = max 1 (MA + MD + MA * MD * c / (r - max a d)) * r ^ n := by
      rfl

set_option maxHeartbeats 1000000 in
/-- Exact assembly of the manuscript's one-way provenance Lyapunov theorem,
with its stated block constant. -/
theorem one_way_provenance_Lyapunov_exact {l e : Type*} [Fintype l]
    [Fintype e] [DecidableEq l] [DecidableEq e]
    (A : Matrix l l ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (MA MD c a d r : ℝ)
    (hA : ∀ n, ‖A ^ n‖ ≤ MA * a ^ n)
    (hD : ∀ n, ‖D ^ n‖ ≤ MD * d ^ n)
    (hC : ‖C‖ ≤ c)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hMA : 0 ≤ MA) (hMD : 0 ≤ MD)
    (hc0 : 0 ≤ c) (hq : max a d < r) (hr1 : r < 1) :
    let R := Matrix.fromBlocks A 0 C D
    let MR := max 1 (MA + MD + MA * MD * c / (r - max a d))
    ∃ H : Matrix (l ⊕ e) (l ⊕ e) ℂ,
      HasSum (fun n => (R ^ n)ᴴ * R ^ n) H
      ∧ H - Rᴴ * H * R = 1
      ∧ (∀ H' : Matrix (l ⊕ e) (l ⊕ e) ℂ,
          H' - Rᴴ * H' * R = 1 → H' = H)
      ∧ (H - 1).PosSemidef
      ∧ (((MR ^ 2 / (1 - r ^ 2) : ℝ) : ℂ) • 1 - H).PosSemidef
      ∧ (((1 - (1 - r ^ 2) / MR ^ 2 : ℝ) : ℂ) • H
          - Rᴴ * H * R).PosSemidef
      ∧ (∀ N, ‖H - ∑ n ∈ Finset.range (N + 1),
            (R ^ n)ᴴ * R ^ n‖
          ≤ MR ^ 2 * r ^ (2 * N + 2) / (1 - r ^ 2)) := by
  let R : Matrix (l ⊕ e) (l ⊕ e) ℂ := Matrix.fromBlocks A 0 C D
  let MR : ℝ := max 1 (MA + MD + MA * MD * c / (r - max a d))
  have hq0 : 0 ≤ max a d := le_trans ha (le_max_left _ _)
  have hr0 : 0 ≤ r := (lt_of_le_of_lt hq0 hq).le
  have hMR : 1 ≤ MR := by exact le_max_left _ _
  have hpow : ∀ n, ‖R ^ n‖ ≤ MR * r ^ n := by
    simpa [R, MR] using
      one_way_provenance_uniform_power A C D MA MD c a d r
        hA hD hC ha hd hMA hMD hc0 hq hr1
  exact lyapunov_metric R MR r hMR hr0 hr1 hpow

end NCG
