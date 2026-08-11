/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.WeakDoubletInvariantQuartic

/-!
# Local edge and affine face action rigidity

The weak-site invariant theory is proved in `WeakDoubletInvariantQuartic`.
Here the other two finite coefficient classifications in
`thm:SMST-action-rigidity` are derived from positivity and their exact zero
sets, rather than assumed as coefficient equations.
-/

namespace NCG
namespace LocalGaugeActionRigidity

/-- Scalar component of the simultaneously `U(2)`-invariant Hermitian edge
quadratic after conjugating by the actual transport. -/
def edgeQuadratic (a b : ℝ) (c x y : ℂ) : ℝ :=
  a * Complex.normSq x + b * Complex.normSq y -
    2 * ((star x) * c * y).re

/-- Positivity and exact diagonal kernel force the unique transported-distance
quadratic.  Applying this scalar identity to the two weak components gives
`w‖U phi_x-phi_y‖²`. -/
theorem edgeQuadratic_exactDiagonal_rigidity
    (a b : ℝ) (c : ℂ)
    (hnonneg : ∀ x y, 0 ≤ edgeQuadratic a b c x y)
    (hzero : ∀ x y, edgeQuadratic a b c x y = 0 ↔ x = y) :
    ∃! w : ℝ, 0 < w ∧
      ∀ x y, edgeQuadratic a b c x y = w * Complex.normSq (x - y) := by
  have hdiag : edgeQuadratic a b c 1 1 = 0 := (hzero 1 1).2 rfl
  have ha_nonneg : 0 ≤ a := by
    have h := hnonneg 1 0
    simpa [edgeQuadratic, Complex.normSq_ofReal] using h
  have ha_ne : a ≠ 0 := by
    intro ha
    have hz : edgeQuadratic a b c 1 0 = 0 := by
      simp [edgeQuadratic, ha]
    have := (hzero 1 0).1 hz
    norm_num at this
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (Ne.symm ha_ne)
  let f : ℝ → ℝ := fun t =>
    a * (1 + t) ^ 2 + b - c.re * ((1 + t) * 2)
  have hf (t : ℝ) : f t = edgeQuadratic a b c (1 + (t : ℂ)) 1 := by
    have hnorm : Complex.normSq (1 + (t : ℂ)) = (1 + t) ^ 2 := by
      simp [Complex.normSq]
      ring
    rw [edgeQuadratic, hnorm]
    simp [f, Complex.add_re, Complex.mul_re]
    ring
  have hf0 : f 0 = 0 := by rw [hf]; simpa using hdiag
  have hfpoly (t : ℝ) : f t =
      a * t ^ 2 + (2 * a - 2 * c.re) * t := by
    dsimp [f] at hf0 ⊢
    linarith [hf0]
  have hreal : a = c.re := by
    let d := 2 * a - 2 * c.re
    have hn : 0 ≤ f (-d / (2 * a)) := by
      rw [hf]
      exact hnonneg _ _
    have heval : f (-d / (2 * a)) = -(d ^ 2) / (4 * a) := by
      rw [hfpoly]
      dsimp [d]
      field_simp [ha_ne]
      ring
    rw [heval] at hn
    have hden : 0 < 4 * a := by positivity
    have hnum : 0 ≤ -(d ^ 2) := by
      rcases div_nonneg_iff.mp hn with h | h
      · exact h.1
      · linarith [h.2, hden]
    dsimp [d] at hnum
    nlinarith [sq_nonneg (2 * a - 2 * c.re)]
  let g : ℝ → ℝ := fun t =>
    a * (1 + t ^ 2) + b - (c.re + t * c.im) * 2
  have hg (t : ℝ) : g t =
      edgeQuadratic a b c (1 + (t : ℂ) * Complex.I) 1 := by
    have hnorm : Complex.normSq (1 + (t : ℂ) * Complex.I) =
        1 + t ^ 2 := by
      simp [Complex.normSq]
      ring
    have hcross :
        ((star (1 + (t : ℂ) * Complex.I)) * c * 1).re =
          c.re + t * c.im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [edgeQuadratic, hnorm, hcross]
    simp [g]
    ring
  have hg0 : g 0 = 0 := by rw [hg]; simpa using hdiag
  have hgpoly (t : ℝ) : g t = a * t ^ 2 + (-2 * c.im) * t := by
    dsimp [g] at hg0 ⊢
    linarith [hg0]
  have himag : c.im = 0 := by
    let d := -2 * c.im
    have hn : 0 ≤ g (-d / (2 * a)) := by
      rw [hg]
      exact hnonneg _ _
    have heval : g (-d / (2 * a)) = -(d ^ 2) / (4 * a) := by
      rw [hgpoly]
      dsimp [d]
      field_simp [ha_ne]
      ring
    rw [heval] at hn
    have hden : 0 < 4 * a := by positivity
    have hnum : 0 ≤ -(d ^ 2) := by
      rcases div_nonneg_iff.mp hn with h | h
      · exact h.1
      · linarith [h.2, hden]
    dsimp [d] at hnum
    nlinarith [sq_nonneg (-2 * c.im)]
  have hc : c = (a : ℂ) := by
    apply Complex.ext
    · simpa [hreal]
    · simpa [himag]
  have hb : b = a := by
    simp [edgeQuadratic, hc, Complex.normSq_ofReal] at hdiag
    linarith
  have hformula (x y : ℂ) :
      edgeQuadratic a b c x y = a * Complex.normSq (x - y) := by
    rw [hb, hc]
    simp [edgeQuadratic, Complex.normSq, Complex.mul_re,
      Complex.mul_im]
    ring
  refine ⟨a, ⟨ha_pos, hformula⟩, ?_⟩
  intro w hw
  have htest := hw.2 1 0
  simp [hformula] at htest
  exact htest.symm

/-- The affine fundamental-character branch is normalized and positive with a
unique zero at the identity only for a unique positive plaquette weight. -/
theorem affineFaceCharacter_positiveWeight
    (a b : ℝ) (n : ℕ) (hn : 0 < n)
    (hidentity : a - b * n = 0)
    (hminus_nonneg : 0 ≤ a + b * n)
    (hminus_nonzero : a + b * n ≠ 0) :
    ∃! w : ℝ, 0 < w ∧
      ∀ traceReal : ℝ, a - b * traceReal =
        w * ((n : ℝ) - traceReal) := by
  have ha : a = b * n := by linarith
  have hb_nonneg : 0 ≤ b := by
    rw [ha] at hminus_nonneg
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith
  have hb_ne : b ≠ 0 := by
    intro hb
    apply hminus_nonzero
    rw [hb] at ha
    simp [ha, hb]
  have hb_pos : 0 < b := lt_of_le_of_ne hb_nonneg (Ne.symm hb_ne)
  have hformula (t : ℝ) : a - b * t = b * ((n : ℝ) - t) := by
    rw [ha]
    push_cast
    ring
  refine ⟨b, ⟨hb_pos, hformula⟩, ?_⟩
  intro w hw
  have htest := hw.2 (-n)
  rw [hformula] at htest
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

end LocalGaugeActionRigidity
end NCG
