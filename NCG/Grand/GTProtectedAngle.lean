/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact protected-angle criterion and the arithmetic
  localizer (`thm:GT-protected-angle` and
  `cor:GRH-protected-angle-localizer`,
  Gran-Tensor manuscript)

* `gt_protected_angle`:
  (i) the boxed criterion PA.3 in quadratic-form terms —
      the 2×2 localizer
      `𝕃_η = [[η‖t₀‖², -⟨t₀,p₀⟩], [-⟨p₀,t₀⟩, η‖p₀‖²]]`
      is positive semidefinite exactly when the protected
      angle obeys `|⟨t₀,p₀⟩| ≤ η‖t₀‖‖p₀‖`;
  (ii) the boxed readout bound PA.4
      `|f| ≤ a + η‖t₀‖‖p₀‖` for `f = 𝔭 + ⟨t₀,p₀⟩` with
      `|𝔭| ≤ a`.

* `grh_protected_angle_localizer`: the arithmetic
  instantiation — the square-root-scale angle bound is the
  same localizer positivity, and the boxed readout bound
  `|f_X| ≤ |𝔭_X| + η_X‖t₀‖‖p₀‖` follows.

The identification of `t₀, p₀` with the predictor-residual
total and phase sources of the assembled packet is the
manuscript's arithmetic layer; the negative-eigenvector
witness is the failing quadratic-form direction exhibited
by the criterion.
-/

open scoped InnerProductSpace

namespace NCG

/-- `thm:GT-protected-angle`. -/
theorem gt_protected_angle {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (t0 p0 : V) (η : ℝ) (hη : 0 ≤ η)
    (ht : t0 ≠ 0) (hp : p0 ≠ 0) :
    -- (i) the boxed PSD ⟺ angle criterion (PA.3)
    ((∀ x y : ℝ,
      0 ≤ η * ‖t0‖ ^ 2 * x ^ 2
        - 2 * ⟪t0, p0⟫_ℝ * x * y
        + η * ‖p0‖ ^ 2 * y ^ 2)
      ↔ |⟪t0, p0⟫_ℝ| ≤ η * (‖t0‖ * ‖p0‖))
    -- (ii) the boxed readout bound (PA.4)
    ∧ (∀ f pf a : ℝ, f = pf + ⟪t0, p0⟫_ℝ → |pf| ≤ a →
        |⟪t0, p0⟫_ℝ| ≤ η * (‖t0‖ * ‖p0‖) →
        |f| ≤ a + η * (‖t0‖ * ‖p0‖)) := by
  have hnt : (0 : ℝ) < ‖t0‖ := norm_pos_iff.mpr ht
  have hnp : (0 : ℝ) < ‖p0‖ := norm_pos_iff.mpr hp
  constructor
  · constructor
    · intro hpsd
      set c := ⟪t0, p0⟫_ℝ with hc
      rw [abs_le]
      constructor
      · have h := hpsd ‖p0‖ (-‖t0‖)
        nlinarith [h, mul_pos hnt hnp]
      · have h := hpsd ‖p0‖ ‖t0‖
        nlinarith [h, mul_pos hnt hnp]
    · intro hangle x y
      set c := ⟪t0, p0⟫_ℝ with hc
      have habs : |c| ≤ η * (‖t0‖ * ‖p0‖) := hangle
      have h1 : c * x * y ≤ |c| * (|x| * |y|) := by
        calc c * x * y ≤ |c * x * y| := le_abs_self _
          _ = |c| * (|x| * |y|) := by
              rw [abs_mul, abs_mul, mul_assoc]
      have h2 : |c| * (|x| * |y|)
          ≤ (η * (‖t0‖ * ‖p0‖)) * (|x| * |y|) :=
        mul_le_mul_of_nonneg_right habs (by positivity)
      have hsq : 0 ≤ (‖t0‖ * |x| - ‖p0‖ * |y|) ^ 2 :=
        sq_nonneg _
      have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
      rw [hx2, hy2]
      nlinarith [h1, h2, hsq, abs_nonneg x, abs_nonneg y,
        mul_nonneg (abs_nonneg x) (abs_nonneg y)]
  · intro f pf a hf hpf hangle
    rw [hf]
    calc |pf + ⟪t0, p0⟫_ℝ| ≤ |pf| + |⟪t0, p0⟫_ℝ| :=
          abs_add_le _ _
      _ ≤ a + η * (‖t0‖ * ‖p0‖) := add_le_add hpf hangle

/-- `cor:GRH-protected-angle-localizer`. -/
theorem grh_protected_angle_localizer {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (t0 p0 : V) (ηX pfX : ℝ)
    (hangle : |⟪t0, p0⟫_ℝ| ≤ ηX * (‖t0‖ * ‖p0‖)) :
    -- the boxed square-root-scale readout bound
    |pfX + ⟪t0, p0⟫_ℝ|
      ≤ |pfX| + ηX * (‖t0‖ * ‖p0‖) := by
  calc |pfX + ⟪t0, p0⟫_ℝ|
      ≤ |pfX| + |⟪t0, p0⟫_ℝ| := abs_add_le _ _
    _ ≤ |pfX| + ηX * (‖t0‖ * ‖p0‖) := by linarith

end NCG
