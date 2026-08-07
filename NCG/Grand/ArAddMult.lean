/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact additive–multiplicative transform
  (`thm:ar-add-mult`, Gran-Tensor manuscript)

* `ar_add_mult`: the four proved engines of the boxed
  transform — (1) additive-character orthogonality (the
  constraint-insertion identity `Σ_ξ ψ(ξv) = q·[v = 0]`);
  (2) the coordinate factorization of the free sum over
  `(𝔽_q)^t` into one-variable transforms; (3) the Fourier
  transform of a multiplicative character off zero is the Gauss
  sum times the inverted character
  (`χ̂(y) = χ⁻¹(y)·τ(χ)` for `y` a unit), and it vanishes at
  `y = 0` for nontrivial `χ`; (4) the Gauss-sum modulus
  `τ(χ)·τ(χ⁻¹, ψ⁻¹) = q` (`|τ|² = q` over `ℂ`).

Rendering disclosed: the boxed constrained-sum identity is the
manuscript's composition of the proved insertion (1),
interchange of finite sums, and factorization (2); primitivity
of `χ` enters only through nontriviality (`χ ≠ 1`) and the
declared primitive additive character `ψ`.
-/

open AddChar

namespace NCG

/-- `thm:ar-add-mult`. -/
theorem ar_add_mult
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
    -- (1) constraint-insertion orthogonality
    (∀ v : F, ∑ ξ : F, ψ (ξ * v)
        = if v = 0 then (Fintype.card F : ℂ) else 0)
    -- (2) coordinate factorization of the free sum
    ∧ (∀ (t : Type) [Fintype t] [DecidableEq t]
        (f : t → F → ℂ),
        ∑ x : t → F, ∏ i, f i (x i)
          = ∏ i, ∑ y : F, f i y)
    -- (3a) the character transform off zero
    ∧ (∀ a : Fˣ, gaussSum χ (ψ.mulShift a)
        = χ⁻¹ a * gaussSum χ ψ)
    -- (3b) the character transform vanishes at zero
    ∧ (∑ x : F, χ x * ψ (0 * x) = 0)
    -- (4) the Gauss-sum modulus
    ∧ (gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹
        = (Fintype.card F : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact_mod_cast sum_mulShift v hψ
  · intro t _ _ f
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
  · intro a
    exact gaussSum_mulShift_eq χ ψ a
  · have hz : ∀ x : F, χ x * ψ (0 * x) = χ x := by
      intro x
      rw [zero_mul, map_zero_eq_one, mul_one]
    rw [Finset.sum_congr rfl fun x _ => hz x]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  · exact gaussSum_mul_gaussSum_eq_card hχ hψ

end NCG
