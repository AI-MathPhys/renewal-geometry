/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The causal-order skeleton

**Proposition `prop:causal-skeleton`**: under the aperiodicity assumption
(`ass:aperiodic`), the predictive condensation `(𝒫, ⪯)` with the descended
quotient length `T = Λ_𝒫` is a locally finite graded poset — a
causal-set-like order skeleton.  The assumption supplies (ii) strict
monotonicity, (iii) elementary Hasse covers `T(y) = T(x) + 1`, and
(iv) finite length balls; this file derives the two conclusions:

* **local finiteness** (`NCG.CausalSkeleton.interval_finite`): every
  order interval `[x, y]` embeds in the finite length ball of radius
  `T(y)`, hence is finite;
* **gradedness** (`NCG.CausalSkeleton.saturated_chain_rank`,
  `NCG.CausalSkeleton.saturated_chain_length_eq`): along any saturated
  chain (a `⋖`-chain in Mathlib's `CovBy` order), `T` increases by exactly
  the number of steps, so every saturated chain from `x` to `y` has the
  same length `T(y) − T(x)` — `T` is a rank function.

Everything is stated for an abstract partial order `P` with a time
function `T : P → ℕ`; the predictive poset `NCG.PredictivePoset` of
`NCG/Renewal/Order.lean` is the intended instance, with `T` the descended
quotient length `Λ` of `NCG/Renewal/PredictiveQuotient.lean`.
-/

namespace NCG.CausalSkeleton

variable {P : Type*} [PartialOrder P] (T : P → ℕ)

/-- **Local finiteness** (Proposition `prop:causal-skeleton`, last step):
if `T` is monotone and every length ball `{z : T z ≤ R}` is finite, then
every order interval `[x, y]` is finite — the skeleton is a locally
finite order, as a causal set requires. -/
theorem interval_finite (hmono : Monotone T)
    (hball : ∀ R : ℕ, {z : P | T z ≤ R}.Finite) (x y : P) :
    (Set.Icc x y).Finite :=
  (hball (T y)).subset fun _ hz => hmono hz.2

/-- Along a saturated chain (successive Hasse covers) with elementary
covers `T(b) = T(a) + 1`, the time function advances by exactly the chain
length (Proposition `prop:causal-skeleton`, gradedness). -/
theorem saturated_chain_rank
    (hcov : ∀ a b : P, a ⋖ b → T b = T a + 1) :
    ∀ (l : List P) (x : P), List.IsChain (· ⋖ ·) (x :: l) →
      T ((x :: l).getLast (List.cons_ne_nil x l)) = T x + l.length := by
  intro l
  induction l with
  | nil => intro x _; simp
  | cons b l ih =>
      intro x hchain
      cases hchain with
      | cons_cons hab htl =>
          rw [List.getLast_cons (List.cons_ne_nil b l), ih b htl,
            hcov x b hab, List.length_cons]
          omega

/-- **Gradedness** (Proposition `prop:causal-skeleton`): when every Hasse
cover is elementary, any two saturated chains between the same endpoints
have the same length — `T` is a genuine rank function and `(P, ≤)` is a
graded poset. -/
theorem saturated_chain_length_eq
    (hcov : ∀ a b : P, a ⋖ b → T b = T a + 1) {x y : P}
    {l₁ l₂ : List P}
    (h₁ : List.IsChain (· ⋖ ·) (x :: l₁))
    (h₂ : List.IsChain (· ⋖ ·) (x :: l₂))
    (hy₁ : (x :: l₁).getLast (List.cons_ne_nil x l₁) = y)
    (hy₂ : (x :: l₂).getLast (List.cons_ne_nil x l₂) = y) :
    l₁.length = l₂.length := by
  have e₁ := saturated_chain_rank T hcov l₁ x h₁
  have e₂ := saturated_chain_rank T hcov l₂ x h₂
  rw [hy₁] at e₁
  rw [hy₂] at e₂
  omega

/-- A strictly monotone integer time function forbids nontrivial cycles:
the skeleton order has no closed causal loops (automatic for a partial
order, but stated as the time-function separation property: comparable
distinct points have distinct times). -/
theorem time_separates (hstrict : ∀ a b : P, a < b → T a < T b)
    {x y : P} (hxy : x ≤ y) (hT : T x = T y) : x = y := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · rfl
  · exact absurd hT (hstrict x y hlt).ne

end NCG.CausalSkeleton
