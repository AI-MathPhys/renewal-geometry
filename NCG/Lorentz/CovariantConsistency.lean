/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Covariant central-difference consistency (genuine Taylor cancellation)

**Lemma `lem:covariant-consistency`**: the covariant central difference
of midpoint-transported spinors reproduces `∂ + Ω` to second order.

Unlike a formal cancellation with a shared free coefficient, this file
*derives* the bracket agreement.  The forward datum is the truncated
link exponential `T₊ = 1 + hΩ + (h²/2)Ω²` applied to the second-order
Taylor value `ψ + h·ψ' + (h²/2)·ψ''`; the backward datum is
`T₋ = 1 − hΩ + (h²/2)Ω²` applied to `ψ − h·ψ' + (h²/2)·ψ''`.  Expanding
both products through the linearity of `Ω` (`map_add`/`map_smul`), the
`h⁰`, `h²`, **and** `h⁴` brackets cancel *by computation* — because each
is an even-order product of the same data — and the difference is
**exactly**

`T₊·taylor₊ − T₋·taylor₋ = 2h·(ψ' + Ωψ) + h³·(Ωψ'' + Ω²ψ')`

(`NCG.covariant_central_difference`).  Dividing by `2h` gives the
covariant derivative plus an *explicit* `(h²/2)·(Ωψ'' + Ω²ψ')`
remainder (`NCG.covariant_central_difference_div`) — the
`∇_{i,R}ψ = (∂_i + Ω_i)ψ + O(h²)` statement with the `O(h²)`
coefficient computed, not postulated.  The `L²` packaging over compact
sets and the `γ_R → ω^{LC}` substitution (Theorem `thm:fundamental`)
are the remaining noted steps.
-/

namespace NCG

/-- The truncated link exponential `1 + hΩ + (h²/2)Ω²` applied to a
vector — the second-order parallel-transport operator. -/
noncomputable def linkTransport {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Ω : Module.End ℝ V) (h : ℝ) (v : V) : V :=
  v + h • Ω v + (h ^ 2 / 2) • Ω (Ω v)

/-- The second-order Taylor value `ψ + h·ψ' + (h²/2)·ψ''`. -/
noncomputable def taylorValue {V : Type*} [AddCommGroup V] [Module ℝ V]
    (h : ℝ) (ψ dψ ddψ : V) : V :=
  ψ + h • dψ + (h ^ 2 / 2) • ddψ

/-- **Lemma `lem:covariant-consistency` (derived cancellation)**: the
forward and backward transported Taylor data have *equal* `h⁰`, `h²`
and `h⁴` brackets — they cancel in the central difference by
computation — and the difference is exactly
`2h·(ψ' + Ωψ) + h³·(Ωψ'' + Ω²ψ')`. -/
theorem covariant_central_difference {V : Type*} [AddCommGroup V]
    [Module ℝ V] (Ω : Module.End ℝ V) (h : ℝ) (ψ dψ ddψ : V) :
    linkTransport Ω h (taylorValue h ψ dψ ddψ)
      - linkTransport Ω (-h) (taylorValue (-h) ψ dψ ddψ)
    = (2 * h) • (dψ + Ω ψ) + (h ^ 3) • (Ω ddψ + Ω (Ω dψ)) := by
  simp only [linkTransport, taylorValue, map_add, map_smul, map_neg,
    Even.neg_pow even_two, neg_neg, neg_smul, smul_neg]
  module

/-- **Lemma `lem:covariant-consistency` (division by `2h`)**: for
`h ≠ 0` the covariant central difference is *exactly* the covariant
derivative plus an explicit second-order remainder:

`(2h)⁻¹·(T₊taylor₊ − T₋taylor₋) = (ψ' + Ωψ) + (h²/2)·(Ωψ'' + Ω²ψ')`. -/
theorem covariant_central_difference_div {V : Type*} [AddCommGroup V]
    [Module ℝ V] (Ω : Module.End ℝ V) {h : ℝ} (hh : h ≠ 0)
    (ψ dψ ddψ : V) :
    (2 * h)⁻¹ • (linkTransport Ω h (taylorValue h ψ dψ ddψ)
      - linkTransport Ω (-h) (taylorValue (-h) ψ dψ ddψ))
    = (dψ + Ω ψ) + (h ^ 2 / 2) • (Ω ddψ + Ω (Ω dψ)) := by
  rw [covariant_central_difference, smul_add, smul_smul, smul_smul]
  have h2 : (2 * h) ≠ 0 := mul_ne_zero two_ne_zero hh
  rw [inv_mul_cancel₀ h2, one_smul,
    show (2 * h)⁻¹ * h ^ 3 = h ^ 2 / 2 from by
      field_simp <;> ring]

end NCG
