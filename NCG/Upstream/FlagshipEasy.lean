/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Grand-core transfer and the regulated neutral mass criterion
  (`thm:grand-core-transfer`, `thm:YM-regulated-master`, flagship)

* `grand_core_transfer` — the positive transfer chain: if
  `G ⪰ g·D` and `Bᴴ·D·B ⪰ b·E` with `g, b ≥ 0` and `D ⪰ 0`, then
  `Bᴴ·G·B ⪰ gb·E`; the kernel firewall
  `Bx = 0 ⇒ (BᴴGB)x = 0`; and the upper bound
  `G ⪯ c·1 ⇒ BᴴGB ⪯ c·BᴴB`;
* `qReg_lt_one` / `qReg_root` / `qReg_form_bound` /
  `qReg_gap_positive` — the explicit regulated criterion: under
  `a < 1`, `μ_eff > 0`, `b² < (1-a)μ_eff` the larger eigenvalue
  `q_reg = (a+1-μ+√((a-1+μ)²+4b²))/2` of the scalar comparison
  block satisfies `q_reg < 1`, dominates the quadratic form
  `ax² + 2bxy + (1-μ)y²`, and yields the positive mass gap
  `Δ_reg ≥ -τ⁻¹ log q_reg > 0`.
-/

namespace NCG

open Matrix

open scoped ComplexOrder

/-- `thm:grand-core-transfer`: the positive transfer chain, the
kernel firewall, and the loading upper bound. -/
theorem grand_core_transfer {u p : Type*} [Fintype u] [Fintype p]
    [DecidableEq u]
    (G D : Matrix u u ℂ) (E : Matrix p p ℂ) (B : Matrix u p ℂ)
    (g b c : ℝ) (hg : 0 ≤ g) (_hb : 0 ≤ b)
    (h1 : (G - g • D).PosSemidef)
    (h2 : (Bᴴ * D * B - b • E).PosSemidef)
    (hup : (c • (1 : Matrix u u ℂ) - G).PosSemidef) :
    ((Bᴴ * G * B - (g * b) • E).PosSemidef)
      ∧ (∀ x : p → ℂ, B.mulVec x = 0 →
          (Bᴴ * G * B).mulVec x = 0)
      ∧ (c • (Bᴴ * B) - Bᴴ * G * B).PosSemidef := by
  refine ⟨?_, ?_, ?_⟩
  · have hconj1 : (Bᴴ * (G - g • D) * B).PosSemidef :=
      h1.conjTranspose_mul_mul_same B
    have hsm2 : (g • (Bᴴ * D * B - b • E)).PosSemidef :=
      h2.smul hg
    have hsum := hconj1.add hsm2
    have hrw : Bᴴ * (G - g • D) * B
        + g • (Bᴴ * D * B - b • E)
        = Bᴴ * G * B - (g * b) • E := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul]
      module
    rwa [hrw] at hsum
  · intro x hx
    rw [show Bᴴ * G * B = Bᴴ * G * B from rfl,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_zero, Matrix.mulVec_zero]
  · have hconj : (Bᴴ * (c • (1 : Matrix u u ℂ) - G)
        * B).PosSemidef :=
      hup.conjTranspose_mul_mul_same B
    have hrw : Bᴴ * (c • (1 : Matrix u u ℂ) - G) * B
        = c • (Bᴴ * B) - Bᴴ * G * B := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one]
    rwa [hrw] at hconj

/-- The regulated eigenvalue
`q_reg = (a+1-μ+√((a-1+μ)²+4b²))/2`. -/
noncomputable def qReg (a mu b : ℝ) : ℝ :=
  (a + 1 - mu + Real.sqrt ((a - 1 + mu) ^ 2 + 4 * b ^ 2)) / 2

/-- `thm:YM-regulated-master` (contraction): `q_reg < 1`. -/
theorem qReg_lt_one (a mu b : ℝ) (ha : a < 1) (hmu : 0 < mu)
    (hb : b ^ 2 < (1 - a) * mu) : qReg a mu b < 1 := by
  have hD : (a - 1 + mu) ^ 2 + 4 * b ^ 2 < (1 - a + mu) ^ 2 := by
    nlinarith
  have hy : (0 : ℝ) < 1 - a + mu := by linarith
  have hsq : Real.sqrt ((a - 1 + mu) ^ 2 + 4 * b ^ 2)
      < 1 - a + mu := by
    rw [show (1 - a + mu : ℝ)
      = Real.sqrt ((1 - a + mu) ^ 2) from
        (Real.sqrt_sq hy.le).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hD
  rw [qReg]
  linarith

/-- `q_reg` dominates both diagonal entries and satisfies the
characteristic-root identity `(q-a)(q-(1-μ)) = b²`. -/
theorem qReg_root (a mu b : ℝ) :
    a ≤ qReg a mu b ∧ 1 - mu ≤ qReg a mu b
      ∧ (qReg a mu b - a) * (qReg a mu b - (1 - mu)) = b ^ 2 := by
  have hD : (0 : ℝ) ≤ (a - 1 + mu) ^ 2 + 4 * b ^ 2 := by positivity
  have habs : |a - 1 + mu|
      ≤ Real.sqrt ((a - 1 + mu) ^ 2 + 4 * b ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
  have hge1 : (a - 1 + mu)
      ≤ Real.sqrt ((a - 1 + mu) ^ 2 + 4 * b ^ 2) :=
    le_trans (le_abs_self _) habs
  have hge2 : -(a - 1 + mu)
      ≤ Real.sqrt ((a - 1 + mu) ^ 2 + 4 * b ^ 2) :=
    le_trans (neg_le_abs _) habs
  have hsq : (Real.sqrt ((a - 1 + mu) ^ 2 + 4 * b ^ 2)) ^ 2
      = (a - 1 + mu) ^ 2 + 4 * b ^ 2 := Real.sq_sqrt hD
  refine ⟨?_, ?_, ?_⟩
  · rw [qReg]
    linarith
  · rw [qReg]
    linarith
  · rw [qReg]
    nlinarith [hsq]

/-- `thm:YM-regulated-master` (form bound): the scalar comparison
block is dominated, `ax² + 2bxy + (1-μ)y² ≤ q_reg(x² + y²)`. -/
theorem qReg_form_bound (a mu b : ℝ) (x y : ℝ) :
    a * x ^ 2 + 2 * b * x * y + (1 - mu) * y ^ 2
      ≤ qReg a mu b * (x ^ 2 + y ^ 2) := by
  obtain ⟨hqa, hqmu, hdet⟩ := qReg_root a mu b
  set q : ℝ := qReg a mu b with hq
  have key : (q - a) * ((q - a) * x ^ 2 - 2 * b * x * y
      + (q - (1 - mu)) * y ^ 2)
      = ((q - a) * x - b * y) ^ 2 := by
    linear_combination (y ^ 2) * hdet
  rcases eq_or_lt_of_le (sub_nonneg.mpr hqa) with h0 | hpos
  · have hb2 : b ^ 2 = 0 := by
      rw [← hdet, ← h0]
      ring
    have hb0 : b = 0 := by
      nlinarith [sq_nonneg b]
    rw [hb0]
    nlinarith [sq_nonneg x, sq_nonneg y,
      mul_nonneg (sub_nonneg.mpr hqmu) (sq_nonneg y),
      mul_nonneg (sub_nonneg.mpr hqa) (sq_nonneg x)]
  · nlinarith [key, sq_nonneg ((q - a) * x - b * y), hpos,
      mul_pos hpos hpos]

/-- `thm:YM-regulated-master` (mass gap): any transfer contraction
below `q_reg` yields the positive gap `Δ ≥ -τ⁻¹ log q_reg > 0`. -/
theorem qReg_gap_positive (a mu b tau t : ℝ) (ha : a < 1)
    (hmu : 0 < mu) (hb : b ^ 2 < (1 - a) * mu) (htau : 0 < tau)
    (ht : 0 < t) (htq : t ≤ qReg a mu b) :
    -Real.log (qReg a mu b) / tau ≤ -Real.log t / tau
      ∧ 0 < -Real.log (qReg a mu b) / tau := by
  have hq1 := qReg_lt_one a mu b ha hmu hb
  have hq0 : 0 < qReg a mu b := lt_of_lt_of_le ht htq
  have hlogq : Real.log (qReg a mu b) < 0 :=
    Real.log_neg hq0 hq1
  have hmono : Real.log t ≤ Real.log (qReg a mu b) :=
    Real.log_le_log ht htq
  constructor
  · gcongr
  · exact div_pos (by linarith) htau

end NCG
