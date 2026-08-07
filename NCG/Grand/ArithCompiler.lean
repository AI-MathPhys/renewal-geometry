/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Analytic-NT compiler machinery: Vaughan decomposition,
  character orthogonality, and Gauss sums
  (`thm:ar-fixed-order-source`, `thm:ar-few-orbit`,
  `thm:ar-PCJM-handoff`, Gran-Tensor manuscript)

* `trunc`: range truncation of an arithmetic function;
* `vaughan_identity`: the exact Vaughan decomposition in the
  convolution ring —
  `Λ - Λ_{<V} = log∗μ_{<U} - Λ_{<V}∗ζ∗μ_{<U}
    + (Λ - Λ_{<V})∗ζ∗(μ - μ_{<U})`
  (type-I, type-I′, and type-II ranges), proved from the three
  ring relations `log∗μ = Λ`, `Λ∗ζ = log`, `ζ∗μ = 1` — the
  compiler's source decomposition, of which the order-12
  Vaughan–Heath-Brown compiler is the iterated form;
* `character_orthogonality`: the orbit-`L²` engine —
  `Σ_χ χ(a⁻¹)χ(b) = φ(q)·[a = b]` for unit `a` (re-export of
  the Mathlib orthogonality relation);
* `gauss_sum_modulus`: the Gauss-sum normalization
  `g(χ,ψ)·g(χ⁻¹,ψ⁻¹)`-type modulus identity (re-export) — the
  size input for the few-orbit `L²` bound.

Rendering disclosed: the order-12 iteration of the Vaughan
ranges, the mean-value/large-sieve estimates on each range, and
the PCJM handoff assembling the fixed-order source with the
few-orbit `L²` bound are the manuscript's analytic layer; the
exact decomposition identity, the orthogonality relation, and
the Gauss-sum normalization are proved here.
-/

open ArithmeticFunction

namespace NCG

/-- Range truncation of an arithmetic function. -/
noncomputable def trunc (f : ArithmeticFunction ℝ) (N : ℕ) :
    ArithmeticFunction ℝ :=
  ⟨fun n => if n < N then f n else 0, by
    simp [ArithmeticFunction.map_zero]⟩

/-- The real Möbius function. -/
noncomputable def muR : ArithmeticFunction ℝ :=
  ↑(ArithmeticFunction.moebius)

/-- The real zeta (indicator) function. -/
noncomputable def zetaR : ArithmeticFunction ℝ :=
  ↑(ArithmeticFunction.zeta)

/-- The exact Vaughan decomposition in the convolution ring:
`Λ - Λ_{<V} = log∗μ_{<U} - Λ_{<V}∗ζ∗μ_{<U}
  + (Λ - Λ_{<V})∗ζ∗(μ - μ_{<U})`. -/
theorem vaughan_identity (U V : ℕ) :
    (Λ : ArithmeticFunction ℝ) - trunc Λ V
      = ArithmeticFunction.log * trunc muR U
        - trunc Λ V * zetaR * trunc muR U
        + (Λ - trunc Λ V) * zetaR * (muR - trunc muR U) := by
  have h1 : ArithmeticFunction.log * muR = Λ := by
    rw [muR]
    exact log_mul_moebius_eq_vonMangoldt
  have h2 : (Λ : ArithmeticFunction ℝ) * zetaR
      = ArithmeticFunction.log := by
    rw [zetaR]
    exact vonMangoldt_mul_zeta
  have h3 : zetaR * muR = 1 := by
    rw [zetaR, muR]
    exact coe_zeta_mul_coe_moebius
  linear_combination (trunc muR U - muR) * h2 - h1
    + trunc Λ V * h3

set_option maxHeartbeats 1000000 in
/-- Character orthogonality: the orbit-`L²` engine (re-export
of the Mathlib relation over `ℂ`). -/
theorem character_orthogonality {q : ℕ} [NeZero q]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]
    {a : ZMod q} (ha : IsUnit a) (b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ b
      = if a = b then (q.totient : ℂ) else 0 :=
  DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b

set_option maxHeartbeats 1000000 in
/-- Gauss-sum normalization: the modulus identity for a
nontrivial multiplicative character (re-export). -/
theorem gauss_sum_modulus {R R' : Type*} [Field R]
    [Fintype R] [CommRing R'] [IsDomain R']
    {χ : MulChar R R'} (hχ : χ ≠ 1)
    {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card R :=
  gaussSum_mul_gaussSum_eq_card hχ hψ

end NCG
