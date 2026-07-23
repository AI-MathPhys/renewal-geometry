/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Spin factors: the rank-two Euclidean Jordan algebras

The first stone of the Euclidean Jordan layer (Mathlib has no
Euclidean Jordan algebras): the **spin factor** `JSpin(V) = ℝ ⊕ V`
over a real inner product space `V`, with product

`(s, v) ∘ (t, w) = (st + ⟪v, w⟫, s·w + t·v)`.

We prove from scratch:

* `spinMul_comm`, `spinMul_one` — commutative and unital;
* `spinMul_jordan` — the **Jordan identity**
  `(x ∘ y) ∘ x² = x ∘ (y ∘ x²)`;
* `spinMul_formally_real` — **formal reality**:
  `x² + y² = 0 → x = 0 ∧ y = 0`;
* `sq_eq_norm_smul_one_add` — the spin square law
  `x² = (s² + ‖v‖²)·1 + 2s·(0, v)`, the mechanism that makes every
  spin factor rank two;
* `spinIdem_iff` — the idempotents: `0`, `1`, and the points
  `(1/2, v)` with `‖v‖ = 1/2`;
* `frame_pair` — every such idempotent `p` pairs with `p' = 1 − p`
  into a Jordan frame: `p ∘ p' = 0`, `p + p' = 1` — rank two;
* `peirceHalf_mem_iff` — the Peirce-half space of the frame
  `(±v)`-pair is exactly `{(0, u) | u ⊥ v}`.

This is the algebra of the two-path face `J[i,j] = ℝp_i ⊕ ℝp_j ⊕
J_{ij}` of `thm:two-path-complex-face`: `ℝ(p_i+p_j) ⊕ (ℝ(p_i−p_j) ⊕
J_{ij}) = JSpin(ℝ ⊕ J_{ij})`.  The concrete identification
`JSpin(ℝ³) ≅ M₂(ℂ)_sa` is `NCG/Algebra/PauliJordan.lean`.
-/

namespace NCG.Jordan

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open RealInnerProductSpace

/-- The spin-factor Jordan product on `ℝ × V`. -/
noncomputable def spinMul (x y : ℝ × V) : ℝ × V :=
  (x.1 * y.1 + ⟪x.2, y.2⟫, x.1 • y.2 + y.1 • x.2)

/-- The spin unit. -/
def spinOne : ℝ × V := (1, 0)

theorem spinMul_comm (x y : ℝ × V) : spinMul x y = spinMul y x := by
  unfold spinMul
  refine Prod.ext ?_ ?_
  · simp only
    rw [real_inner_comm]
    ring
  · simp only
    abel

theorem spinMul_one (x : ℝ × V) : spinMul x spinOne = x := by
  unfold spinMul spinOne
  refine Prod.ext ?_ ?_
  · simp
  · simp

theorem one_spinMul (x : ℝ × V) : spinMul spinOne x = x := by
  rw [spinMul_comm]
  exact spinMul_one x

/-- Bilinearity in the left slot (addition). -/
theorem spinMul_add_left (x y z : ℝ × V) :
    spinMul (x + y) z = spinMul x z + spinMul y z := by
  unfold spinMul
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.snd_add, inner_add_left]
    ring
  · simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, add_smul]
    module

/-- Bilinearity in the left slot (scalars). -/
theorem spinMul_smul_left (c : ℝ) (x y : ℝ × V) :
    spinMul (c • x) y = c • spinMul x y := by
  unfold spinMul
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      real_inner_smul_left]
    ring
  · simp only [Prod.smul_fst, Prod.smul_snd, Prod.smul_mk,
      smul_smul, smul_eq_mul]
    module

/-- The spin square. -/
noncomputable def spinSq (x : ℝ × V) : ℝ × V := spinMul x x

/-- **The spin square law**: `x² = (s² + ‖v‖²)·1 + 2s·(0, v)` — the
square of any element lies in the plane spanned by the unit and the
element itself, which is why spin factors have rank two. -/
theorem sq_eq_norm_smul_one_add (x : ℝ × V) :
    spinSq x = (x.1 ^ 2 + ‖x.2‖ ^ 2) • spinOne
      + (2 * x.1) • ((0 : ℝ), x.2) := by
  unfold spinSq spinMul spinOne
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul,
      real_inner_self_eq_norm_sq]
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add,
      two_smul, smul_smul]
    module

/-- **The Jordan identity** `(x ∘ y) ∘ x² = x ∘ (y ∘ x²)`: spin
factors are Jordan algebras. -/
theorem spinMul_jordan (x y : ℝ × V) :
    spinMul (spinMul x y) (spinSq x)
      = spinMul x (spinMul y (spinSq x)) := by
  obtain ⟨s, v⟩ := x
  obtain ⟨t, w⟩ := y
  unfold spinSq spinMul
  simp only [real_inner_self_eq_norm_sq, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right,
    smul_add, smul_smul]
  refine Prod.ext ?_ ?_
  · simp only
    rw [real_inner_comm w v]
    ring
  · simp only
    have hwv : ⟪w, v⟫ = ⟪v, w⟫ := real_inner_comm v w
    rw [hwv]
    module

/-- **Formal reality**: a sum of two spin squares vanishes only if
both elements vanish — spin factors are Euclidean. -/
theorem spinMul_formally_real (x y : ℝ × V)
    (h : spinSq x + spinSq y = 0) : x = 0 ∧ y = 0 := by
  have h1 : (spinSq x + spinSq y).1 = 0 := by rw [h]; rfl
  unfold spinSq spinMul at h1
  simp only [Prod.fst_add, real_inner_self_eq_norm_sq] at h1
  have hx1 : x.1 = 0 ∧ ‖x.2‖ = 0 ∧ y.1 = 0 ∧ ‖y.2‖ = 0 := by
    constructor
    · nlinarith [norm_nonneg x.2, norm_nonneg y.2, sq_nonneg x.1,
        sq_nonneg y.1]
    constructor
    · nlinarith [norm_nonneg x.2, norm_nonneg y.2, sq_nonneg x.1,
        sq_nonneg y.1]
    constructor
    · nlinarith [norm_nonneg x.2, norm_nonneg y.2, sq_nonneg x.1,
        sq_nonneg y.1]
    · nlinarith [norm_nonneg x.2, norm_nonneg y.2, sq_nonneg x.1,
        sq_nonneg y.1]
  obtain ⟨hx, hnx, hy, hny⟩ := hx1
  constructor
  · refine Prod.ext hx ?_
    simpa using norm_eq_zero.mp hnx
  · refine Prod.ext hy ?_
    simpa using norm_eq_zero.mp hny

/-- **The idempotents of a spin factor**: `x ∘ x = x` iff `x = 0`,
`x = 1`, or `x = (1/2, v)` with `‖v‖ = 1/2` — the primitive
idempotents form the radius-`1/2` sphere at height `1/2`. -/
theorem spinIdem_iff (x : ℝ × V) :
    spinSq x = x ↔ x = 0 ∨ x = spinOne
      ∨ (x.1 = 1 / 2 ∧ ‖x.2‖ = 1 / 2) := by
  unfold spinSq spinMul spinOne
  constructor
  · intro h
    have h1 : x.1 * x.1 + ⟪x.2, x.2⟫ = x.1 := congrArg Prod.fst h
    have h2 : x.1 • x.2 + x.1 • x.2 = x.2 := congrArg Prod.snd h
    rw [real_inner_self_eq_norm_sq] at h1
    by_cases hv : x.2 = 0
    · rw [hv] at h1
      simp only [norm_zero] at h1
      have h3 : x.1 * (x.1 - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp h3 with h4 | h4
      · left
        exact Prod.ext h4 hv
      · right; left
        exact Prod.ext (by linarith) hv
    · right; right
      have h3 : (2 * x.1) • x.2 = x.2 := by
        rw [two_mul, add_smul]
        exact h2
      have h6 : (2 * x.1 - 1) • x.2 = 0 := by
        rw [sub_smul, one_smul, sub_eq_zero]
        exact h3
      have h4 : x.1 = 1 / 2 := by
        rcases smul_eq_zero.mp h6 with h7 | h7
        · have h8 : 2 * x.1 - 1 = 0 := h7
          linarith
        · exact absurd h7 hv
      refine ⟨h4, ?_⟩
      rw [h4] at h1
      nlinarith [norm_nonneg x.2]
  · rintro (rfl | rfl | ⟨h1, h2⟩)
    · refine Prod.ext ?_ ?_ <;> simp
    · refine Prod.ext ?_ ?_ <;> simp
    · refine Prod.ext ?_ ?_
      · simp only [real_inner_self_eq_norm_sq, h1, h2]
        norm_num
      · simp only [h1]
        module

/-- **Jordan frame pairs**: each primitive idempotent `p = (1/2, v)`
pairs with `1 − p = (1/2, −v)`: orthogonal idempotents summing to
the unit — the spin factor has rank two. -/
theorem frame_pair {v : V} (hv : ‖v‖ = 1 / 2) :
    spinMul ((1 / 2 : ℝ), v) ((1 / 2 : ℝ), -v) = 0
      ∧ ((1 / 2 : ℝ), v) + ((1 / 2 : ℝ), -v) = spinOne := by
  constructor
  · unfold spinMul
    refine Prod.ext ?_ ?_
    · simp only [inner_neg_right, real_inner_self_eq_norm_sq, hv]
      norm_num
    · simp only [Prod.snd_zero]
      module
  · unfold spinOne
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]
      norm_num
    · simp only [Prod.snd_add]
      module

/-- **The Peirce-half space** of the frame `p = (1/2, v)`,
`p' = (1/2, −v)`: the solutions of `p ∘ x = (1/2)·x` are exactly the
purely vectorial elements orthogonal to `v` — the coherence space
`J_{12}` of the two-path face. -/
theorem peirceHalf_mem_iff {v : V} (hv : ‖v‖ = 1 / 2) (x : ℝ × V) :
    spinMul ((1 / 2 : ℝ), v) x = (1 / 2 : ℝ) • x
      ↔ x.1 = 0 ∧ ⟪v, x.2⟫ = 0 := by
  unfold spinMul
  constructor
  · intro h
    have h1 : (1 / 2) * x.1 + ⟪v, x.2⟫ = (1 / 2) * x.1 :=
      congrArg Prod.fst h
    have h2 : (1 / 2 : ℝ) • x.2 + x.1 • v = (1 / 2 : ℝ) • x.2 :=
      congrArg Prod.snd h
    have h3 : ⟪v, x.2⟫ = 0 := by linarith
    have h4 : x.1 • v = 0 := by
      have h5 := congrArg (fun u => u - (1 / 2 : ℝ) • x.2) h2
      simpa [add_sub_cancel_left] using h5
    have h6 : x.1 = 0 := by
      rcases smul_eq_zero.mp h4 with h7 | h7
      · exact h7
      · exfalso
        rw [h7, norm_zero] at hv
        norm_num at hv
    exact ⟨h6, h3⟩
  · rintro ⟨h1, h2⟩
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, smul_eq_mul, h2]
      ring
    · simp only [Prod.smul_snd, h1]
      module

end NCG.Jordan
