/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealConvexAffineMinorant
import NCG.Grand.ENNRealResolventEnvelopeDetermination
import NCG.Grand.RestrictedResolventObjectiveStrongConvexity

/-!
# ENNReal resolvent-envelope duality from closed convexity

For a lower-semicontinuous convex extended form with dense effective domain, Hahn--Banach and
Riesz representation construct every shifted dual witness.  A resolvent energy identity then
identifies the affine constant with a lower bound for the canonical resolvent envelope.
-/

open Function Set RCLike ContinuousLinearMap
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
  [InnerProductSpace ℝ E] [IsScalarTower ℝ K E] [CompleteSpace E]

/-- Add a finite quadratic penalty to an extended nonnegative form. -/
def ennrealQuadraticShift (q : E → ENNReal) (lam : ℝ) (x : E) : ENNReal :=
  q x + ENNReal.ofReal (lam * ‖x‖ ^ 2)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem ennrealQuadraticShift_ne_top_iff
    (q : E → ENNReal) (lam : ℝ) (x : E) :
    ennrealQuadraticShift q lam x ≠ ∞ ↔ q x ≠ ∞ := by
  simp [ennrealQuadraticShift]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem ennrealQuadraticShift_toReal
    (q : E → ENNReal) (lam : ℝ) (hlam : 0 ≤ lam)
    (x : E) (hx : q x ≠ ∞) :
    (ennrealQuadraticShift q lam x).toReal =
      (q x).toReal + lam * ‖x‖ ^ 2 := by
  rw [ennrealQuadraticShift, ENNReal.toReal_add hx ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal]
  exact mul_nonneg hlam (sq_nonneg ‖x‖)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A lower-semicontinuous extended form remains lower-semicontinuous after a nonnegative
quadratic shift. -/
theorem lowerSemicontinuous_ennrealQuadraticShift
    (q : E → ENNReal) (hls : LowerSemicontinuous q)
    (lam : ℝ) :
    LowerSemicontinuous (ennrealQuadraticShift q lam) := by
  have hcost : Continuous (fun x : E ↦ ENNReal.ofReal (lam * ‖x‖ ^ 2)) :=
    ENNReal.continuous_ofReal.comp
      (continuous_const.mul (continuous_norm.pow 2))
  exact hls.add hcost.lowerSemicontinuous

omit [CompleteSpace E] in
/-- Convexity on the effective domain is preserved by a nonnegative quadratic shift. -/
theorem convexOn_ennrealQuadraticShift
    (q : E → ENNReal)
    (hq : ConvexOn ℝ {x : E | q x ≠ ∞} (fun x ↦ (q x).toReal))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ConvexOn ℝ {x : E | ennrealQuadraticShift q lam x ≠ ∞}
      (fun x ↦ (ennrealQuadraticShift q lam x).toReal) := by
  let s : Set E := {x : E | q x ≠ ∞}
  have hstrong := resolventObjective_strongConvexOn_subset (K := ℝ)
    s (fun x ↦ (q x).toReal) hq lam 0
  have hreal : ConvexOn ℝ s (fun x ↦ (q x).toReal + lam * ‖x‖ ^ 2) := by
    have hobjective := hstrong.convexOn (by
      intro r
      positivity)
    apply hobjective.congr
    intro x hx
    simp [resolventObjective]
  rw [show {x : E | ennrealQuadraticShift q lam x ≠ ∞} = s by
    ext x; simp [s]]
  apply hreal.congr
  intro x hx
  exact (ennrealQuadraticShift_toReal q lam hlam x hx).symm

omit [IsScalarTower ℝ K E] in
/-- Closed convexity and a dense effective domain imply the shifted ENNReal envelope-duality
predicate used by the Mosco converse. -/
theorem hasENNRealResolventEnvelopeDuality_of_closedConvex
    (q : E → ENNReal) (T : ℝ → E →L[K] E)
    (hls : LowerSemicontinuous q)
    (hconvex : ConvexOn ℝ {z : E | q z ≠ ∞} (fun z ↦ (q z).toReal))
    (hdom : Dense {z : E | q z ≠ ∞})
    (hrealInner : ∀ x y : E,
      inner ℝ x y = RCLike.re (inner K x y))
    (hfinite : ∀ lam, 0 < lam → ∀ f : E, q (T lam f) ≠ ∞)
    (henergy : ∀ lam, 0 < lam → ∀ f : E,
      (q (T lam f)).toReal + lam * ‖T lam f‖ ^ 2 =
        RCLike.re (inner K (T lam f) f)) :
    HasENNRealResolventEnvelopeDuality (K := K) q
      (fun lam f ↦ resolventPairingEnvelope (K := K) (T lam) f) := by
  intro lam hlam x r hr
  let qs : E → ENNReal := ennrealQuadraticShift q lam
  have htarget : ENNReal.ofReal (r + lam * ‖x‖ ^ 2) < qs x := by
    change ENNReal.ofReal (r + lam * ‖x‖ ^ 2) < ennrealQuadraticShift q lam x
    by_cases hx : q x = ∞
    · simp [ennrealQuadraticShift, hx]
    · have hqpos : 0 < (q x).toReal := by
        apply ENNReal.toReal_pos
        · exact ne_of_gt (lt_of_le_of_lt bot_le hr)
        · exact hx
      have hreE := real_lt_toEReal_of_ofReal_lt hr
      rw [ENNReal.toEReal_eq_coe_toReal hx] at hreE
      have hre : r < (q x).toReal := by exact_mod_cast hreE
      have hcost : 0 ≤ lam * ‖x‖ ^ 2 := mul_nonneg hlam.le (sq_nonneg ‖x‖)
      have hsum : r + lam * ‖x‖ ^ 2 < (q x).toReal + lam * ‖x‖ ^ 2 :=
        by simpa [add_comm] using add_lt_add_right hre (lam * ‖x‖ ^ 2)
      rw [ennrealQuadraticShift, ← ENNReal.ofReal_toReal hx,
        ← ENNReal.ofReal_add ENNReal.toReal_nonneg hcost]
      exact (ENNReal.ofReal_lt_ofReal_iff (add_pos_of_pos_of_nonneg hqpos hcost)).2 hsum
  obtain ⟨l, c, hminor, hat⟩ := exists_continuousAffineMinorant_of_lt
    qs (lowerSemicontinuous_ennrealQuadraticShift q hls lam)
      (convexOn_ennrealQuadraticShift q hconvex lam hlam.le)
      (by simpa [qs] using hdom) x (r + lam * ‖x‖ ^ 2) htarget
  let y : E := (InnerProductSpace.toDual ℝ E).symm l
  let f : E := (2 : ℝ)⁻¹ • y
  have hlinear (z : E) : l z = 2 * RCLike.re (inner K z f) := by
    calc
      l z = inner ℝ y z := (InnerProductSpace.toDual_symm_apply (x := z) (y := l)).symm
      _ = inner ℝ z y := (real_inner_comm y z).symm
      _ = 2 * inner ℝ z f := by
        dsimp [f]
        rw [inner_smul_right]
        ring
      _ = 2 * RCLike.re (inner K z f) := by rw [hrealInner z f]
  have hfy : q (T lam f) ≠ ∞ := hfinite lam hlam f
  have hminorY := hminor (T lam f) (by simpa [qs] using hfy)
  rw [ennrealQuadraticShift_toReal q lam hlam.le (T lam f) hfy, hlinear] at hminorY
  have hc : c ≤ -RCLike.re (inner K (T lam f) f) := by
    nlinarith [henergy lam hlam f]
  rw [hlinear] at hat
  refine ⟨f, ?_⟩
  simp only [resolventPairingEnvelope]
  nlinarith

end NCG.VaryingHilbert
