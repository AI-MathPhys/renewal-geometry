/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Sharp head–tail contraction bound

Machinery for `thm:universal-coercive-continuum` (branch H1).  For an operator `T` and an
orthogonal head projection `P` (with tail `Q = 1 - P`), block bounds
`‖P T P‖ ≤ a`, `‖Q T Q‖ ≤ d` and leakage `‖P T Q‖, ‖Q T P‖ ≤ b` give the sharp bound

`‖T‖ ≤ q* = (a + d + √((a-d)² + 4b²)) / 2`

(`norm_le_headTail`), the top eigenvalue of the comparison matrix `[[a,b],[b,d]]`; in
particular `q* < 1` whenever `a, d < 1` and `b² < (1-a)(1-d)` (`headTail_lt_one`), the
noncollapsing contraction certificate of the source-native head/tail/leakage bounds.
-/

open ContinuousLinearMap
open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace HeadTail

/-- The sharp two-block comparison value `q* = (a + d + √((a-d)² + 4b²)) / 2`. -/
noncomputable def qstar (a b d : ℝ) : ℝ := (a + d + Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2

theorem qstar_nonneg {a b d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) : 0 ≤ qstar a b d := by
  have := Real.sqrt_nonneg ((a - d) ^ 2 + 4 * b ^ 2)
  unfold qstar
  linarith

theorem le_qstar_left {a b d : ℝ} : a ≤ qstar a b d := by
  have h1 : |a - d| ≤ Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
  have h2 : a - d ≤ |a - d| := le_abs_self _
  unfold qstar
  linarith

theorem le_qstar_right {a b d : ℝ} : d ≤ qstar a b d := by
  have h1 : |a - d| ≤ Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
  have h2 : d - a ≤ |a - d| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  unfold qstar
  linarith

/-- `q*` is a root of the characteristic polynomial: `(q* - a)(q* - d) = b²`. -/
theorem qstar_det {a b d : ℝ} : (qstar a b d - a) * (qstar a b d - d) = b ^ 2 := by
  have hsq : Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2) ^ 2 = (a - d) ^ 2 + 4 * b ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold qstar
  nlinarith [hsq]

/-- The scalar comparison bound: `(as + bt)² + (bs + dt)² ≤ q*² (s² + t²)` for `s, t ≥ 0`. -/
theorem comparison_bound {a b d s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    (a * s + b * t) ^ 2 + (b * s + d * t) ^ 2 ≤ qstar a b d ^ 2 * (s ^ 2 + t ^ 2) := by
  set q := qstar a b d with hq
  have hqa : a ≤ q := le_qstar_left
  have hqd : d ≤ q := le_qstar_right
  have hdet : (q - a) * (q - d) = b ^ 2 := qstar_det
  have hsqrt : Real.sqrt (q - a) * Real.sqrt (q - d) = b := by
    rw [← Real.sqrt_mul (sub_nonneg.mpr hqa), hdet, Real.sqrt_sq hb]
  have hH : 0 ≤ (q - a) * s ^ 2 - 2 * b * s * t + (q - d) * t ^ 2 := by
    have hX := Real.sq_sqrt (sub_nonneg.mpr hqa)
    have hY := Real.sq_sqrt (sub_nonneg.mpr hqd)
    have hsq := sq_nonneg (Real.sqrt (q - a) * s - Real.sqrt (q - d) * t)
    have hexp : (Real.sqrt (q - a) * s - Real.sqrt (q - d) * t) ^ 2
        = (q - a) * s ^ 2 - 2 * b * s * t + (q - d) * t ^ 2 := by
      have e : (Real.sqrt (q - a) * s - Real.sqrt (q - d) * t) ^ 2
          = Real.sqrt (q - a) ^ 2 * s ^ 2
            - 2 * (Real.sqrt (q - a) * Real.sqrt (q - d)) * (s * t)
            + Real.sqrt (q - d) ^ 2 * t ^ 2 := by ring
      rw [e, hX, hY, hsqrt]
      ring
    rw [hexp] at hsq
    linarith
  have hkey : q ^ 2 * (s ^ 2 + t ^ 2) - ((a * s + b * t) ^ 2 + (b * s + d * t) ^ 2)
      = (a + d) * ((q - a) * s ^ 2 - 2 * b * s * t + (q - d) * t ^ 2) := by
    linear_combination (s ^ 2 + t ^ 2) * hdet
  have := mul_nonneg (add_nonneg ha hd) hH
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Pythagoras for an orthogonal projection: `‖u‖² = ‖P u‖² + ‖(1 - P) u‖²`. -/
theorem norm_sq_proj_add (P : E →L[ℝ] E) (hP : IsSelfAdjoint P) (hidem : P ∘L P = P) (u : E) :
    ‖u‖ ^ 2 = ‖P u‖ ^ 2 + ‖(1 - P) u‖ ^ 2 := by
  have horth : ⟪P u, (1 - P) u⟫ = 0 := by
    rw [sub_apply, one_apply_eq_self, inner_sub_right]
    have h2 : P (P u) = P u := congrArg (fun S : E →L[ℝ] E => S u) hidem
    have h1 : ⟪P u, P u⟫ = ⟪P u, u⟫ := by
      calc ⟪P u, P u⟫ = ⟪(P†) (P u), u⟫ := (adjoint_inner_left P u (P u)).symm
        _ = ⟪P (P u), u⟫ := by rw [isSelfAdjoint_iff'.mp hP]
        _ = ⟪P u, u⟫ := by rw [h2]
    rw [h1, sub_self]
  have hdecomp : u = P u + (1 - P) u := by
    rw [sub_apply, one_apply_eq_self]
    abel
  calc ‖u‖ ^ 2 = ‖P u + (1 - P) u‖ ^ 2 := by rw [← hdecomp]
    _ = ‖P u‖ ^ 2 + ‖(1 - P) u‖ ^ 2 := by
        rw [pow_two, pow_two, pow_two]
        exact norm_add_sq_eq_norm_sq_add_norm_sq_real horth

/-- **Sharp head–tail contraction (H1)**: block bounds `a`, `d` and leakage `b` give
`‖T x‖ ≤ q* ‖x‖`. -/
theorem norm_apply_le_headTail (P : E →L[ℝ] E) (hP : IsSelfAdjoint P) (hidem : P ∘L P = P)
    (T : E →L[ℝ] E) {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hPTP : ∀ x, ‖P (T (P x))‖ ≤ a * ‖P x‖)
    (hPTQ : ∀ x, ‖P (T ((1 - P) x))‖ ≤ b * ‖(1 - P) x‖)
    (hQTP : ∀ x, ‖(1 - P) (T (P x))‖ ≤ b * ‖P x‖)
    (hQTQ : ∀ x, ‖(1 - P) (T ((1 - P) x))‖ ≤ d * ‖(1 - P) x‖) (x : E) :
    ‖T x‖ ≤ qstar a b d * ‖x‖ := by
  set s := ‖P x‖ with hs
  set t := ‖(1 - P) x‖ with ht
  have hs0 : 0 ≤ s := norm_nonneg _
  have ht0 : 0 ≤ t := norm_nonneg _
  have hxdecomp : T x = T (P x) + T ((1 - P) x) := by
    rw [← map_add]
    congr 1
    rw [sub_apply, one_apply_eq_self]
    abel
  have hPT : ‖P (T x)‖ ≤ a * s + b * t := by
    rw [hxdecomp, map_add]
    exact (norm_add_le _ _).trans (add_le_add (hPTP x) (hPTQ x))
  have hQT : ‖(1 - P) (T x)‖ ≤ b * s + d * t := by
    rw [hxdecomp, map_add]
    exact (norm_add_le _ _).trans (add_le_add (hQTP x) (hQTQ x))
  have hTx : ‖T x‖ ^ 2 ≤ (a * s + b * t) ^ 2 + (b * s + d * t) ^ 2 := by
    rw [norm_sq_proj_add P hP hidem (T x)]
    have h1 : ‖P (T x)‖ ^ 2 ≤ (a * s + b * t) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hPT 2
    have h2 : ‖(1 - P) (T x)‖ ^ 2 ≤ (b * s + d * t) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hQT 2
    linarith
  have hx : ‖x‖ ^ 2 = s ^ 2 + t ^ 2 := norm_sq_proj_add P hP hidem x
  have hcomp := comparison_bound (s := s) (t := t) ha hb hd
  have hfinal : ‖T x‖ ^ 2 ≤ (qstar a b d * ‖x‖) ^ 2 := by
    rw [mul_pow, hx]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (qstar_nonneg ha hd) (norm_nonneg _)) two_ne_zero).mp hfinal

/-- Operator-norm form of the sharp head–tail bound. -/
theorem norm_le_headTail (P : E →L[ℝ] E) (hP : IsSelfAdjoint P) (hidem : P ∘L P = P)
    (T : E →L[ℝ] E) {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hPTP : ∀ x, ‖P (T (P x))‖ ≤ a * ‖P x‖)
    (hPTQ : ∀ x, ‖P (T ((1 - P) x))‖ ≤ b * ‖(1 - P) x‖)
    (hQTP : ∀ x, ‖(1 - P) (T (P x))‖ ≤ b * ‖P x‖)
    (hQTQ : ∀ x, ‖(1 - P) (T ((1 - P) x))‖ ≤ d * ‖(1 - P) x‖) :
    ‖T‖ ≤ qstar a b d :=
  opNorm_le_bound _ (qstar_nonneg ha hd)
    (norm_apply_le_headTail P hP hidem T ha hb hd hPTP hPTQ hQTP hQTQ)

/-- **Noncollapsing certificate**: `q* < 1` exactly under the uniform head/tail/leakage bounds
`a, d < 1`, `b² < (1-a)(1-d)`. -/
theorem headTail_lt_one {a b d : ℝ} (ha1 : a < 1) (hd1 : d < 1)
    (hbad : b ^ 2 < (1 - a) * (1 - d)) : qstar a b d < 1 := by
  have hsq : Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2) < 2 - a - d := by
    have h2 : (0 : ℝ) ≤ 2 - a - d := by linarith
    rw [show (2 : ℝ) - a - d = Real.sqrt ((2 - a - d) ^ 2) from (Real.sqrt_sq h2).symm]
    refine Real.sqrt_lt_sqrt (by positivity) ?_
    nlinarith
  unfold qstar
  linarith

end HeadTail
end NCG
