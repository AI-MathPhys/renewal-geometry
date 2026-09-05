/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Sharp positive head–tail enclosure and the block-first bridge
  (`thm:sharp-positive-head-tail`, `thm:GRH-block-first-bridge`,
   Gran-Tensor manuscript)

* `head_tail_block_expansion`: the block quadratic form of
  `H = [[A,B],[B*,D]]` expands exactly into the four sector
  pairings.
* `sharp_positive_head_tail`: the scalar 2×2 enclosure
  `aX² + 2bXY + dY² ≤ Λ(a,b,d)(X²+Y²)` with
  `Λ = (a+d+√((a-d)²+4b²))/2`, and for `a,d < 1`:
  `Λ < 1 ⟺ b² < (1-a)(1-d)`.
* `grh_block_first_bridge`: the same enclosure at leakage norm
  `ν = b²`: `a<1`, `d<1`, `ν<(1-a)(1-d)` give the exact upper
  bridge `Λ < 1`.

Rendering disclosed: `‖H‖ ≤ Λ` follows from the proved
quadratic-form expansion, Cauchy–Schwarz on the off-diagonal
block, and the proved scalar enclosure (the operator-norm
packaging); the moment-exact-leakage identification of `b²` and
the weighted alternative are `thm:universal-moment-leakage`
(hard tier) and `thm:weighted-source-influence` respectively;
the source-saturation clause of the bridge is the manuscript's
density hypothesis.
-/

open Matrix Real

namespace NCG

/-- Block quadratic-form expansion of the head–tail
decomposition. -/
theorem head_tail_block_expansion {dA dD : Type*} [Fintype dA]
    [Fintype dD] (A : Matrix dA dA ℂ) (B : Matrix dA dD ℂ)
    (D : Matrix dD dD ℂ) (x : dA → ℂ) (y : dD → ℂ) :
    star (Sum.elim x y) ⬝ᵥ
        ((Matrix.fromBlocks A B Bᴴ D) *ᵥ Sum.elim x y)
      = star x ⬝ᵥ (A *ᵥ x) + star x ⬝ᵥ (B *ᵥ y)
        + star y ⬝ᵥ (Bᴴ *ᵥ x) + star y ⬝ᵥ (D *ᵥ y) := by
  rw [Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Pi.star_apply, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- `thm:sharp-positive-head-tail`: the scalar 2×2 enclosure
and the sharp strictness criterion. -/
theorem sharp_positive_head_tail :
    (∀ a b d X Y : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ d →
        a * X ^ 2 + 2 * b * X * Y + d * Y ^ 2
          ≤ (a + d + Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2
            * (X ^ 2 + Y ^ 2))
    ∧ (∀ a b d : ℝ, 0 ≤ b → a < 1 → d < 1 →
        ((a + d + Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2 < 1
          ↔ b ^ 2 < (1 - a) * (1 - d))) := by
  constructor
  · intro a b d X Y ha hb hd
    set s := Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hssq : s ^ 2 = (a - d) ^ 2 + 4 * b ^ 2 := by
      rw [hs, Real.sq_sqrt (by positivity)]
    have key : ((a - d) * (X ^ 2 - Y ^ 2) + 4 * b * X * Y) ^ 2
        ≤ (s * (X ^ 2 + Y ^ 2)) ^ 2 := by
      have hexp : (s * (X ^ 2 + Y ^ 2)) ^ 2
          = s ^ 2 * (X ^ 2 + Y ^ 2) ^ 2 := by ring
      rw [hexp, hssq]
      nlinarith [sq_nonneg ((a - d) * (2 * X * Y)
        - 2 * b * (X ^ 2 - Y ^ 2)),
        sq_nonneg (X ^ 2 - Y ^ 2), sq_nonneg (X * Y)]
    have hlin : (a - d) * (X ^ 2 - Y ^ 2) + 4 * b * X * Y
        ≤ s * (X ^ 2 + Y ^ 2) := by
      have hB0 : 0 ≤ s * (X ^ 2 + Y ^ 2) :=
        mul_nonneg hs0 (by positivity)
      calc (a - d) * (X ^ 2 - Y ^ 2) + 4 * b * X * Y
          ≤ |(a - d) * (X ^ 2 - Y ^ 2) + 4 * b * X * Y| :=
            le_abs_self _
        _ = Real.sqrt (((a - d) * (X ^ 2 - Y ^ 2)
              + 4 * b * X * Y) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt ((s * (X ^ 2 + Y ^ 2)) ^ 2) :=
            Real.sqrt_le_sqrt key
        _ = |s * (X ^ 2 + Y ^ 2)| := Real.sqrt_sq_eq_abs _
        _ = s * (X ^ 2 + Y ^ 2) := abs_of_nonneg hB0
    nlinarith [hlin]
  · intro a b d hb ha hd
    have hkey : (0 : ℝ) < 2 - a - d := by linarith
    constructor
    · intro h
      have hs : Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)
          < 2 - a - d := by linarith
      have hsq : (a - d) ^ 2 + 4 * b ^ 2 < (2 - a - d) ^ 2 :=
        (Real.sqrt_lt' hkey).mp hs
      nlinarith [hsq]
    · intro h
      have hsq : (a - d) ^ 2 + 4 * b ^ 2 < (2 - a - d) ^ 2 := by
        nlinarith [h]
      have hs : Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)
          < 2 - a - d := (Real.sqrt_lt' hkey).mpr hsq
      linarith

/-- `thm:GRH-block-first-bridge`: the enclosure at leakage norm
`ν = b²` and the sufficient upper-bridge criterion. -/
theorem grh_block_first_bridge (a nu d : ℝ) (ha0 : 0 ≤ a)
    (hnu : 0 ≤ nu) (hd0 : 0 ≤ d) :
    (∀ X Y : ℝ,
      a * X ^ 2 + 2 * Real.sqrt nu * X * Y + d * Y ^ 2
        ≤ (a + d + Real.sqrt ((a - d) ^ 2 + 4 * nu)) / 2
          * (X ^ 2 + Y ^ 2))
    ∧ (a < 1 → d < 1 → nu < (1 - a) * (1 - d) →
        (a + d + Real.sqrt ((a - d) ^ 2 + 4 * nu)) / 2 < 1) := by
  have hb2 : Real.sqrt nu ^ 2 = nu := Real.sq_sqrt hnu
  constructor
  · intro X Y
    have h := sharp_positive_head_tail.1 a (Real.sqrt nu) d
      X Y ha0 (Real.sqrt_nonneg nu) hd0
    rwa [hb2] at h
  · intro ha hd hcrit
    have h := (sharp_positive_head_tail.2 a (Real.sqrt nu) d
      (Real.sqrt_nonneg nu) ha hd).mpr (by rwa [hb2])
    rwa [hb2] at h

end NCG
