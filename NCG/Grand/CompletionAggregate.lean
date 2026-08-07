/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact inversion and stability of the aggregated completion
  transfer
  (`thm:completion-aggregate-inversion` and
  `thm:completion-aggregate-stability`,
  Gran-Tensor manuscript)

* `completion_aggregate_inversion`: for the boxed aggregate
  `A_s = c·D₀(I - sD₀)⁻¹` (the sum over every private dwell
  length):
  (i) `D₀` commutes with the resolvent factor;
  (ii) the boxed resolvent identity
      `cI + sA_s = c(I - sD₀)⁻¹`;
  (iii) the boxed two-sided inverse
      `D₀ = A_s(cI + sA_s)⁻¹ = (cI + sA_s)⁻¹A_s`;
  (iv) the boxed kernel identity `Ker A_s = Ker D₀` and the
      rank identity `rank A_s = rank D₀` — the instantaneous
      provenance-Hankel dimension survives aggregation.

* `completion_aggregate_stability`: the boxed Lipschitz
  reconstruction `‖D₀ - D̃₀‖ ≤ L_s‖A_s - Ã_s‖` with
  `L_s = K + sK²`, `K = (1+s)/(1-s)`; at `s = 1/3` this is
  the boxed `L_{1/3} = 10/3`.

The norm convergence of the geometric series defining
`A_s` for a contraction `D₀` (which supplies the resolvent
factor assumed here) is the manuscript's summation step.
-/

open Matrix

set_option linter.unusedSimpArgs false

namespace NCG

/-- `thm:completion-aggregate-inversion`. -/
theorem completion_aggregate_inversion {n : Type*}
    [Fintype n] [DecidableEq n]
    (D Ri : Matrix n n ℂ) (s c : ℂ) (hc : c ≠ 0)
    (hRi1 : (1 - s • D) * Ri = 1)
    (hRi2 : Ri * (1 - s • D) = 1) :
    -- (i) commutation with the resolvent factor
    (D * Ri = Ri * D)
    -- (ii) the boxed resolvent identity `cI + sA = c·Ri`
    ∧ (c • (1 : Matrix n n ℂ) + s • (c • (D * Ri))
        = c • Ri)
    -- (iii) the boxed two-sided inverse
    ∧ ((c • (D * Ri)) * (c⁻¹ • (1 - s • D)) = D)
    ∧ ((c⁻¹ • (1 - s • D)) * (c • (D * Ri)) = D)
    -- (iv) kernel and rank identities
    ∧ (∀ {m : Type} [Fintype m] (X : Matrix n m ℂ),
        (c • (D * Ri)) * X = 0 ↔ D * X = 0)
    ∧ ((D * Ri).rank = D.rank) := by
  have hcomm : D * Ri = Ri * D := by
    calc D * Ri = (Ri * (1 - s • D)) * (D * Ri) := by
          rw [hRi2, Matrix.one_mul]
      _ = Ri * ((1 - s • D) * D) * Ri := by
          simp only [Matrix.mul_assoc]
      _ = Ri * (D * (1 - s • D)) * Ri := by
          congr 2
          simp only [Matrix.sub_mul, Matrix.mul_sub,
            Matrix.one_mul, Matrix.mul_one,
            Matrix.smul_mul, Matrix.mul_smul]
      _ = Ri * D * ((1 - s • D) * Ri) := by
          simp only [Matrix.mul_assoc]
      _ = Ri * D := by rw [hRi1, Matrix.mul_one]
  have hexpand : Ri = 1 + s • (D * Ri) := by
    have h := hRi1
    rw [Matrix.sub_mul, Matrix.one_mul,
      Matrix.smul_mul] at h
    rw [← h]
    abel
  have hunit : IsUnit Ri.det := by
    have hU : IsUnit Ri := ⟨⟨Ri, 1 - s • D, hRi2, hRi1⟩, rfl⟩
    rwa [Matrix.isUnit_iff_isUnit_det] at hU
  refine ⟨hcomm, ?_, ?_, ?_, ?_, ?_⟩
  · calc c • (1 : Matrix n n ℂ) + s • (c • (D * Ri))
        = c • (1 + s • (D * Ri)) := by
          rw [smul_add, smul_smul, smul_smul, mul_comm]
      _ = c • Ri := by rw [← hexpand]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hc, one_smul, Matrix.mul_assoc,
      hRi2, Matrix.mul_one]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
    calc (1 - s • D) * (D * Ri)
        = D * ((1 - s • D) * Ri) := by
          simp only [Matrix.sub_mul, Matrix.mul_sub,
            Matrix.one_mul, Matrix.mul_one,
            Matrix.smul_mul, Matrix.mul_smul,
            Matrix.mul_assoc]
      _ = D := by rw [hRi1, Matrix.mul_one]
  · intro m _ X
    constructor
    · intro h
      rw [Matrix.smul_mul] at h
      have h0 : D * Ri * X = 0 := by
        have := congrArg (fun M => c⁻¹ • M) h
        simpa [smul_smul, inv_mul_cancel₀ hc] using this
      rw [hcomm, Matrix.mul_assoc] at h0
      have := congrArg (fun M => (1 - s • D) * M) h0
      simpa [← Matrix.mul_assoc, hRi1] using this
    · intro h
      rw [Matrix.smul_mul, hcomm, Matrix.mul_assoc, h,
        Matrix.mul_zero, smul_zero]
  · exact Matrix.rank_mul_eq_left_of_isUnit_det Ri D hunit

/-- `thm:completion-aggregate-stability`. -/
theorem completion_aggregate_stability {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A]
    (D Dt Aa At Ri Rti RA RtA : A)
    (s K : ℝ) (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hD : D = Aa * Ri) (hDt : Dt = At * Rti)
    (h1 : RA * Ri = 1) (h2 : Rti * RtA = 1)
    (hdiff : RtA - RA = s • (At - Aa))
    (hRi : ‖Ri‖ ≤ K) (hRti : ‖Rti‖ ≤ K)
    (hAt : ‖At‖ ≤ 1) :
    -- the boxed Lipschitz reconstruction
    ‖D - Dt‖ ≤ (K + s * K ^ 2) * ‖Aa - At‖
    -- the boxed constant at `s = 1/3` (with `K = 2`)
    ∧ (s = 1 / 3 → K = 2 → K + s * K ^ 2 = 10 / 3) := by
  have hinvdiff : Ri - Rti = Rti * (s • (At - Aa)) * Ri := by
    have hcalc : Rti * (s • (At - Aa)) * Ri = Ri - Rti := by
      calc Rti * (s • (At - Aa)) * Ri
          = Rti * (RtA - RA) * Ri := by rw [hdiff]
        _ = (Rti * RtA) * Ri - Rti * (RA * Ri) := by
            simp only [mul_sub, sub_mul, mul_assoc]
        _ = Ri - Rti := by rw [h1, h2, one_mul, mul_one]
    exact hcalc.symm
  have hsplit : D - Dt
      = (Aa - At) * Ri + At * (Ri - Rti) := by
    rw [hD, hDt]
    simp only [sub_mul, mul_sub]
    abel
  constructor
  · have hb1 : ‖(Aa - At) * Ri‖ ≤ ‖Aa - At‖ * K := by
      calc ‖(Aa - At) * Ri‖ ≤ ‖Aa - At‖ * ‖Ri‖ :=
            norm_mul_le _ _
        _ ≤ ‖Aa - At‖ * K :=
            mul_le_mul_of_nonneg_left hRi (norm_nonneg _)
    have hb2 : ‖At * (Ri - Rti)‖
        ≤ s * K ^ 2 * ‖Aa - At‖ := by
      have hcomm : ‖(s : ℝ) • (At - Aa)‖
          = s * ‖Aa - At‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs,
          ← norm_neg (Aa - At)]
        congr 2
        abel
      calc ‖At * (Ri - Rti)‖
          ≤ ‖At‖ * ‖Ri - Rti‖ := norm_mul_le _ _
        _ ≤ 1 * ‖Ri - Rti‖ :=
            mul_le_mul_of_nonneg_right hAt (norm_nonneg _)
        _ = ‖Rti * (s • (At - Aa)) * Ri‖ := by
            rw [one_mul, hinvdiff]
        _ ≤ ‖Rti‖ * ‖(s : ℝ) • (At - Aa)‖ * ‖Ri‖ := by
            calc ‖Rti * (s • (At - Aa)) * Ri‖
                ≤ ‖Rti * (s • (At - Aa))‖ * ‖Ri‖ :=
                  norm_mul_le _ _
              _ ≤ ‖Rti‖ * ‖(s : ℝ) • (At - Aa)‖ * ‖Ri‖ :=
                  mul_le_mul_of_nonneg_right
                    (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ K * (s * ‖Aa - At‖) * K := by
            rw [hcomm]
            have hn : (0 : ℝ) ≤ s * ‖Aa - At‖ := by
              positivity
            exact mul_le_mul
              (mul_le_mul_of_nonneg_right hRti hn)
              hRi (norm_nonneg _)
              (mul_nonneg hK hn)
        _ = s * K ^ 2 * ‖Aa - At‖ := by ring
    calc ‖D - Dt‖ = ‖(Aa - At) * Ri + At * (Ri - Rti)‖ := by
          rw [hsplit]
      _ ≤ ‖(Aa - At) * Ri‖ + ‖At * (Ri - Rti)‖ :=
          norm_add_le _ _
      _ ≤ ‖Aa - At‖ * K + s * K ^ 2 * ‖Aa - At‖ :=
          add_le_add hb1 hb2
      _ = (K + s * K ^ 2) * ‖Aa - At‖ := by ring
  · intro hs3 hK2
    subst hs3
    subst hK2
    norm_num

end NCG
