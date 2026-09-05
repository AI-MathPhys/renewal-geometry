/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The protected circulation carrier of the amplitude transfer
  (`thm:exact-amplitude-carrier`, SM_emergence)

For the symmetric amplitude nonbacktracking operator
`(B₀f)(i,j) = Σ_{k≠i,j} f(j,k)` on the oriented edges of `K₄`:

* `circulation_carrier_fixed` — the harmonic embedding is a fixed
  point: for an antisymmetric divergence-free one-cochain `α`,
  `(B₀Jα)(i,j) = Σ_{k≠i,j} α(j,k) = -α(j,i) = α(i,j)`;
* `triangle_cochain_*` — the three triangle circulations through
  `(0,1,2)`, `(0,1,3)`, `(0,2,3)` are antisymmetric,
  divergence-free, and linearly independent, so
  `dim Ker(B₀ - I) ≥ 3 = dim H¹(K₄;ℂ)`.

The exact characteristic polynomial
`(x-2)(x-1)³(x+1)²(x²+x+2)³` (hence `dim Ker(B₀-I) = 3` exactly)
is the remaining computational layer.
-/

namespace NCG

open Finset

/-- `thm:exact-amplitude-carrier` (harmonic fixed point): an
antisymmetric divergence-free one-cochain is a fixed point of the
amplitude nonbacktracking transfer,
`Σ_{k≠i,j} α(j,k) = α(i,j)`. -/
theorem circulation_carrier_fixed (α : Fin 4 → Fin 4 → ℂ)
    (hanti : ∀ i j, α i j = -α j i)
    (hdiv : ∀ j, ∑ k ∈ Finset.univ.filter (fun k => k ≠ j),
      α j k = 0)
    (i j : Fin 4) (hij : i ≠ j) :
    (∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), α j k)
      = α i j := by
  have hset : Finset.univ.filter (fun k : Fin 4 => k ≠ j)
      = insert i (Finset.univ.filter
        (fun k => k ≠ i ∧ k ≠ j)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hk
      by_cases hki : k = i
      · exact Or.inl hki
      · exact Or.inr ⟨hki, hk⟩
    · rintro (rfl | ⟨_, hk⟩)
      · exact hij
      · exact hk
  have hmem : i ∉ Finset.univ.filter
      (fun k : Fin 4 => k ≠ i ∧ k ≠ j) := by
    simp
  have h0 := hdiv j
  rw [hset, Finset.sum_insert hmem] at h0
  have hji := hanti i j
  linear_combination h0 - hji

/-- Integer core of a triangle circulation through `a → b → c`. -/
def triInt (a b c : Fin 4) (i j : Fin 4) : ℤ :=
  if (i = a ∧ j = b) ∨ (i = b ∧ j = c) ∨ (i = c ∧ j = a) then 1
  else if (i = b ∧ j = a) ∨ (i = c ∧ j = b) ∨ (i = a ∧ j = c)
    then -1 else 0

/-- The complex triangle circulation through `a → b → c`. -/
noncomputable def triCochain (a b c : Fin 4) :
    Fin 4 → Fin 4 → ℂ := fun i j => (triInt a b c i j : ℂ)

/-- The three triangle circulations `(0,1,2)`, `(0,1,3)`, `(0,2,3)`
are antisymmetric and divergence-free, hence fixed by the
amplitude transfer (`circulation_carrier_fixed`). -/
theorem tri_cochains_harmonic :
    (∀ i j, triCochain 0 1 2 i j = -triCochain 0 1 2 j i)
      ∧ (∀ j, ∑ k ∈ Finset.univ.filter (fun k => k ≠ j),
          triCochain 0 1 2 j k = 0)
      ∧ (∀ i j, triCochain 0 1 3 i j = -triCochain 0 1 3 j i)
      ∧ (∀ j, ∑ k ∈ Finset.univ.filter (fun k => k ≠ j),
          triCochain 0 1 3 j k = 0)
      ∧ (∀ i j, triCochain 0 2 3 i j = -triCochain 0 2 3 j i)
      ∧ (∀ j, ∑ k ∈ Finset.univ.filter (fun k => k ≠ j),
          triCochain 0 2 3 j k = 0) := by
  have hZa : ∀ (a b c : Fin 4), (a, b, c) = (0, 1, 2)
      ∨ (a, b, c) = (0, 1, 3) ∨ (a, b, c) = (0, 2, 3) →
      ∀ i j, triInt a b c i j = -triInt a b c j i := by
    decide
  have hZd : ∀ (a b c : Fin 4), (a, b, c) = (0, 1, 2)
      ∨ (a, b, c) = (0, 1, 3) ∨ (a, b, c) = (0, 2, 3) →
      ∀ j, ∑ k ∈ Finset.univ.filter (fun k => k ≠ j),
        triInt a b c j k = 0 := by
    decide
  refine ⟨fun i j => ?_, fun j => ?_, fun i j => ?_, fun j => ?_,
    fun i j => ?_, fun j => ?_⟩ <;>
    simp only [triCochain] <;>
    [exact_mod_cast hZa 0 1 2 (by decide) i j;
     exact_mod_cast hZd 0 1 2 (by decide) j;
     exact_mod_cast hZa 0 1 3 (by decide) i j;
     exact_mod_cast hZd 0 1 3 (by decide) j;
     exact_mod_cast hZa 0 2 3 (by decide) i j;
     exact_mod_cast hZd 0 2 3 (by decide) j]

/-- The three triangle circulations are linearly independent:
`dim Ker(B₀ - I) ≥ 3`. -/
theorem tri_cochains_independent (c1 c2 c3 : ℂ)
    (h : (fun i j => c1 * triCochain 0 1 2 i j
        + c2 * triCochain 0 1 3 i j + c3 * triCochain 0 2 3 i j)
      = fun _ _ => 0) :
    c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  have h12 := congrFun (congrFun h 1) 2
  have h13 := congrFun (congrFun h 1) 3
  have h23 := congrFun (congrFun h 2) 3
  have e1 : triInt 0 1 2 1 2 = 1 ∧ triInt 0 1 3 1 2 = 0
      ∧ triInt 0 2 3 1 2 = 0 := by decide
  have e2 : triInt 0 1 2 1 3 = 0 ∧ triInt 0 1 3 1 3 = 1
      ∧ triInt 0 2 3 1 3 = 0 := by decide
  have e3 : triInt 0 1 2 2 3 = 0 ∧ triInt 0 1 3 2 3 = 0
      ∧ triInt 0 2 3 2 3 = 1 := by decide
  simp only [triCochain, e1.1, e1.2.1, e1.2.2, e2.1, e2.2.1,
    e2.2.2, e3.1, e3.2.1, e3.2.2, Int.cast_one, Int.cast_zero,
    mul_one, mul_zero, add_zero, zero_add] at h12 h13 h23
  exact ⟨h12, h13, h23⟩

end NCG
