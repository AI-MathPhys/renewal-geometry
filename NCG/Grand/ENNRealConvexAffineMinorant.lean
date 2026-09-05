/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Continuous affine minorants of extended nonnegative convex functions

A lower-semicontinuous convex `ENNReal`-valued function with dense effective domain admits a
global continuous affine minorant through every strict finite lower level.  The proof separates
the point from the closed extended epigraph.  Density rules out a vertical separating
hyperplane, including when the function value at the point is infinite.
-/

open Function Set RCLike ContinuousLinearMap
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real epigraph of an extended nonnegative function, embedded into `EReal` so that an
infinite value has no finite-height epigraph point. -/
def ennrealEpigraph (q : E → ENNReal) : Set (E × ℝ) :=
  {p | (q p.1).toEReal ≤ (p.2 : EReal)}

omit [InnerProductSpace ℝ E] in
/-- Lower semicontinuity of an `ENNReal` function makes its finite-height epigraph closed. -/
theorem isClosed_ennrealEpigraph
    (q : E → ENNReal) (hls : LowerSemicontinuous q) :
    IsClosed (ennrealEpigraph q) := by
  let A : Set (E × EReal) := {p | (q p.1).toEReal ≤ p.2}
  have hqE : LowerSemicontinuous (fun x ↦ (q x).toEReal) :=
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous hls
      EReal.coe_ennreal_strictMono.monotone
  have hA : IsClosed A := by
    simpa [A] using hqE.isClosed_epigraph
  have heq : ennrealEpigraph q =
      (Prod.map id (Real.toEReal : ℝ → EReal)) ⁻¹' A := by
    ext p
    rfl
  rw [heq]
  exact hA.preimage (continuous_id.prodMap continuous_coe_real_ereal)

/-- Convexity on the effective domain is exactly convexity of the finite-height extended
epigraph. -/
theorem convex_ennrealEpigraph
    (q : E → ENNReal)
    (hq : ConvexOn ℝ {x : E | q x ≠ ∞} (fun x ↦ (q x).toReal)) :
    Convex ℝ (ennrealEpigraph q) := by
  have heq : ennrealEpigraph q =
      {p : E × ℝ | p.1 ∈ {x : E | q x ≠ ∞} ∧ (q p.1).toReal ≤ p.2} := by
    ext p
    change (q p.1).toEReal ≤ (p.2 : EReal) ↔ q p.1 ≠ ∞ ∧ (q p.1).toReal ≤ p.2
    by_cases hp : q p.1 = ∞
    · simp [hp]
    · rw [← ENNReal.ofReal_toReal hp]
      simp
  rw [heq]
  exact hq.convex_epigraph

/-- A strict real lower level of an `ENNReal` value is also strict after embedding in `EReal`. -/
theorem real_lt_toEReal_of_ofReal_lt {r : ℝ} {a : ENNReal}
    (h : ENNReal.ofReal r < a) :
    (r : EReal) < a.toEReal := by
  by_cases hr : 0 ≤ r
  · calc
      (r : EReal) = (ENNReal.ofReal r : EReal) := by
        rw [EReal.coe_ennreal_ofReal, max_eq_left hr]
      _ < a.toEReal := EReal.coe_ennreal_lt_coe_ennreal_iff.2 h
  · have hr0 : r < 0 := lt_of_not_ge hr
    exact lt_of_lt_of_le (by exact_mod_cast hr0) (EReal.coe_ennreal_nonneg a)

/-- A finite extended nonnegative real has the same EReal value through either embedding. -/
theorem ENNReal.toEReal_eq_coe_toReal {a : ENNReal} (ha : a ≠ ∞) :
    a.toEReal = (a.toReal : EReal) := by
  calc
    a.toEReal = (ENNReal.ofReal a.toReal).toEReal :=
      congrArg ENNReal.toEReal (ENNReal.ofReal_toReal ha).symm
    _ = (a.toReal : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]

/-- Extended Fenchel support: every strict finite lower level is attained by a continuous real
affine minorant on the effective domain.  No finiteness of `q x` is required. -/
theorem exists_continuousAffineMinorant_of_lt
    (q : E → ENNReal)
    (hls : LowerSemicontinuous q)
    (hconvex : ConvexOn ℝ {z : E | q z ≠ ∞} (fun z ↦ (q z).toReal))
    (hdom : Dense {z : E | q z ≠ ∞})
    (x : E) (r : ℝ) (hr : ENNReal.ofReal r < q x) :
    ∃ (l : E →L[ℝ] ℝ) (c : ℝ),
      (∀ z : E, q z ≠ ∞ → l z + c ≤ (q z).toReal) ∧
        l x + c = r := by
  let A := ennrealEpigraph q
  have hxnot : (x, r) ∉ A := by
    change ¬ (q x).toEReal ≤ (r : EReal)
    exact not_le_of_gt (real_lt_toEReal_of_ofReal_lt hr)
  obtain ⟨L, u, hpoint, hA⟩ :=
    geometric_hahn_banach_point_closed (convex_ennrealEpigraph q hconvex)
      (isClosed_ennrealEpigraph q hls) hxnot
  let U : E →L[ℝ] ℝ := L.comp (.inl ℝ E ℝ)
  let d : ℝ := L (0, 1)
  have hvertical (z : E) (t : ℝ) :
      L (z, t) = U z + t * d := by
    calc
      L (z, t) = L ((z, 0) + t • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = L (z, 0) + t * L (0, 1) := by rw [map_add, map_smul]; rfl
      _ = U z + t * d := rfl
  have hd_nonneg : 0 ≤ d := by
    by_contra hd
    have hdneg : d < 0 := lt_of_not_ge hd
    obtain ⟨z, hz⟩ := hdom.nonempty_iff.mpr inferInstance
    let B : ℝ := L (z, (q z).toReal) - u
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (B / (-d))
    have hmem : (z, (q z).toReal + n) ∈ A := by
      dsimp [A]
      change (q z).toEReal ≤ ((q z).toReal + (n : ℝ) : EReal)
      rw [ENNReal.toEReal_eq_coe_toReal hz]
      exact_mod_cast le_add_of_nonneg_right (Nat.cast_nonneg n)
    have hsep := hA _ hmem
    rw [hvertical] at hsep
    have hn' : B < (n : ℝ) * (-d) := (div_lt_iff₀ (neg_pos.mpr hdneg)).1 hn
    dsimp [B] at hn'
    rw [hvertical] at hn'
    nlinarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hd_ne : d ≠ 0 := by
    intro hd0
    have hpoint' : U x < u := by
      rw [hvertical, hd0, mul_zero, add_zero] at hpoint
      exact hpoint
    let V : Set E := {z | U z < u}
    have hVopen : IsOpen V := isOpen_lt U.continuous continuous_const
    have hxV : x ∈ V := hpoint'
    obtain ⟨z, hzdom, hzV⟩ := hdom.exists_mem_open hVopen ⟨x, hxV⟩
    have hzmem : (z, (q z).toReal) ∈ A := by
      dsimp [A]
      change (q z).toEReal ≤ ((q z).toReal : EReal)
      rw [ENNReal.toEReal_eq_coe_toReal hzdom]
    have hsep := hA _ hzmem
    rw [hvertical, hd0, mul_zero, add_zero] at hsep
    exact (not_lt_of_ge hzV.le) hsep
  have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd_ne)
  let scale : ℝ := d⁻¹
  let l : E →L[ℝ] ℝ := -scale • U
  let c : ℝ := scale * U x + r
  refine ⟨l, c, ?_, ?_⟩
  · intro z hz
    have hzmem : (z, (q z).toReal) ∈ A := by
      dsimp [A]
      change (q z).toEReal ≤ ((q z).toReal : EReal)
      rw [ENNReal.toEReal_eq_coe_toReal hz]
    have hsep := (hpoint.trans (hA _ hzmem)).le
    rw [hvertical, hvertical] at hsep
    dsimp [l, c, scale]
    simp only [smul_apply, smul_eq_mul]
    change (-d⁻¹) * U z + (d⁻¹ * U x + r) ≤ (q z).toReal
    apply le_of_mul_le_mul_right _ hd_pos
    calc
      ((-d⁻¹) * U z + (d⁻¹ * U x + r)) * d =
          U x + r * d - U z := by field_simp; ring
      _ ≤ (q z).toReal * d := by linarith
  · dsimp [l, c, scale]
    simp

end NCG.VaryingHilbert
