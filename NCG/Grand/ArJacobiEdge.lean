/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Shifted Jacobi partial isometry
  (`thm:ar-jacobi-edge`, Gran-Tensor manuscript)

* `ar_jacobi_edge`: the Jacobi-sum engine of the boxed matrix
  formula:
  (1) the principal–principal value `J(1,1) = q − 2` (the
      `(q−2)/(q−1)` entry numerator);
  (2) the degenerate nonprincipal value `J(1,χ) = −1` for
      `χ ≠ 1` (modulus at most one);
  (3) the Gauss factorization
      `g(χφ)·J(χ,φ) = g(χ)·g(φ)` for `χφ ≠ 1`;
  (4) the modulus identity
      `J(χ,φ)·J(χ⁻¹,φ⁻¹) = q` for `χ, φ, χφ` all nontrivial
      (the `|J| = √q` entry bound).

Rendering disclosed: the identification of the shifted-edge
matrix coefficient with `(q−1)⁻¹·χ̄(h)ψ(h)ψ(−1)·J(χ̄,ψ)` is
the manuscript's substitution `x = −ht` (a unit-group
reindexing), and the rank-`(q−2)` partial-isometry structure
of `T_h` is the translation-bijection bookkeeping on
`G_q∖{−h} → G_q∖{h}`; the analytic content — the Jacobi
evaluations — is proved here through the Mathlib `jacobiSum`
theory.
-/

namespace NCG

/-- `thm:ar-jacobi-edge`. -/
theorem ar_jacobi_edge {F : Type*} [Field F] [Fintype F] :
    -- (1) principal–principal entry numerator
    (jacobiSum (1 : MulChar F ℂ) 1
      = Fintype.card F - 2)
    -- (2) degenerate nonprincipal value
    ∧ (∀ χ : MulChar F ℂ, χ ≠ 1 → jacobiSum 1 χ = -1)
    -- (3) the Gauss factorization behind the boxed formula
    ∧ (∀ (χ φ : MulChar F ℂ) (ψ : AddChar F ℂ),
        χ * φ ≠ 1 →
        gaussSum (χ * φ) ψ * jacobiSum χ φ
          = gaussSum χ ψ * gaussSum φ ψ)
    -- (4) the |J|² = q modulus identity
    ∧ (ringChar ℂ ≠ ringChar F →
        ∀ χ φ : MulChar F ℂ, χ ≠ 1 → φ ≠ 1 → χ * φ ≠ 1 →
        jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹
          = Fintype.card F) := by
  refine ⟨jacobiSum_one_one, ?_, ?_, ?_⟩
  · intro χ hχ
    exact jacobiSum_one_nontrivial hχ
  · intro χ φ ψ hχφ
    exact jacobiSum_mul_nontrivial hχφ ψ
  · intro hchar χ φ hχ hφ hχφ
    exact jacobiSum_mul_jacobiSum_inv hchar hχ hφ hχφ

end NCG
