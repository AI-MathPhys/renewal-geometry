/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Krein.CoverModel

/-!
# Compatible fundamental symmetries are signed data

The updated manuscript classifies *all* diagonal fundamental symmetries
compatible with the renewal shifts (**compatible fundamental symmetries are
signed data**, `thm:functorial-positive-obstruction`): if a diagonal
involution `J e_x = η(x) e_x` satisfies the exchange relations
`J Ŝ_σ = c(σ) Ŝ_σ J`, then along every generator edge

`η(σ·x) = c(σ) · η(x)`,

so the extra content of `J` is exactly a `ℤ/2`-valued edge sign — a sign
cocycle on the predictive graph (`NCG.Graph.SignCocycle`).  Nothing beyond
signed-cover data can be extracted from the positive quotient.

This file proves the operator core of that classification in the diagonal
model of `NCG.Operator.Diagonal`, in both directions:

* `NCG.diagOp_shiftOp_exchange_iff` — the exchange relation
  `D ∘ Ŝ = c • (Ŝ ∘ D)` holds **iff** the diagonal symbol transports as
  `d(s i) = c · d(i)` along the shift;
* `NCG.exchange_iff_step` — for `±1`-valued symbols `signValue ∘ η`, the
  transport law is exactly the sign-cocycle step
  `η(s i) = η(i) + χ` in additive `ℤ/2` notation, connecting to the
  holonomy theory of `NCG.Graph.SignCocycle` and the Krein exchange
  relation `NCG.krein_exchange`.
-/

namespace NCG

open Finsupp

variable {ι : Type*}

/-- Evaluating an equality of operators on a basis vector extracts the
coefficient identity. -/
private theorem single_coeff_eq {i : ι} {a b : ℂ}
    (h : Finsupp.single i a = Finsupp.single i b) : a = b := by
  have := congrArg (fun f : ι →₀ ℂ => f i) h
  simpa using this

/-- **Exchange relations classify diagonal transports**
(operator core of `thm:functorial-positive-obstruction`): a diagonal
operator `D = diagOp d` satisfies the exchange relation
`D ∘ Ŝ = c • (Ŝ ∘ D)` against the shift `Ŝ = shiftOp s` if and only if its
symbol transports by the constant `c` along the shift:

`∀ i, d (s i) = c * d i`.

With `d` a `±1`-valued sign this says a compatible diagonal fundamental
symmetry is precisely a vertex sign whose edge ratios are the constants
`c(σ)` — i.e. an added sign cocycle. -/
theorem diagOp_shiftOp_exchange_iff (d : ι → ℂ) (s : ι → ι) (c : ℂ) :
    diagOp d ∘ₗ shiftOp s = c • (shiftOp s ∘ₗ diagOp d)
      ↔ ∀ i, d (s i) = c * d i := by
  constructor
  · intro h i
    have hi := congrArg (fun T : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ) =>
      T (Finsupp.single i 1)) h
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, shiftOp_single,
      diagOp_single, mul_one, Finsupp.smul_single, smul_eq_mul] at hi
    exact single_coeff_eq hi
  · intro h
    apply Finsupp.lhom_ext
    intro i x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, shiftOp_single,
      diagOp_single, Finsupp.smul_single, smul_eq_mul, h i, mul_assoc]

/-- The `±1`-valued case: for sheet signs `d = signValue ∘ η` the exchange
constant is itself a sign `c = signValue χ`, and the transport law is the
additive **sign-cocycle step** `η(s i) = η(i) + χ`.  This identifies the
datum carried by a compatible diagonal fundamental symmetry with the edge
signs of `NCG.Graph.SignCocycle`, completing the classification
`thm:functorial-positive-obstruction` in the diagonal model. -/
theorem exchange_iff_step (η : ι → ZMod 2) (s : ι → ι) (χ : ZMod 2) :
    diagOp (fun i => signValue (η i)) ∘ₗ shiftOp s
        = signValue χ • (shiftOp s ∘ₗ diagOp fun i => signValue (η i))
      ↔ ∀ i, η (s i) = η i + χ := by
  rw [diagOp_shiftOp_exchange_iff]
  constructor
  · intro h i
    -- `signValue` is injective, so the multiplicative law descends to `ℤ/2`
    have hi := h i
    rw [← signValue_add] at hi
    have hinj : ∀ a b : ZMod 2, signValue a = signValue b → a = b := by
      have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      intro a b hab
      rcases hcases a with ha | ha <;> rcases hcases b with hb | hb <;>
        subst ha <;> subst hb <;> first
        | rfl
        | (exfalso
           simp only [signValue_zero, signValue_one] at hab
           norm_num at hab)
    have := hinj _ _ hi
    rw [this, add_comm]
  · intro h i
    rw [h i, signValue_add, mul_comm]

end NCG
