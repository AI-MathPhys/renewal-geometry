/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Krein.OneLineSignedExtensionInertia

/-!
# Irreducible sign and Lorentzian inertia before Clifford realization
  (`thm:supp-signature-minimality`, `eq:supp-signature-inertia`;
  emergent-spacetime manuscript, supplement version of
  `prop:main-signature-minimality`)

The supplement theorem has three clauses.

* **The positive packet cannot supply a negative direction.**  The spatial
  form `g` reconstructed on `W₄` (a positive definite Hermitian matrix `D`)
  has no negative direction: its quadratic form is nonnegative everywhere and
  its negative inertia index vanishes (`positive_packet_no_negative_direction`).
  This is the content of `lem:supp-positive-krein-distinct` used by the proof.
* **One-line minimality with the opposite sign.**  The geometric extension
  retains the positive restriction `D` on `W` and adjoins exactly one
  independent nondegenerate signed line, i.e. the orthogonal block matrix
  `oneLineSignedExtension c D` on `Fin 1 ⊕ W` with `c ≠ 0`; "signed" (the
  protected orientation supplies the sign opposite to the positive spatial
  restriction) is `c < 0`, which is `c = -a²` for a unique `a > 0`
  (`exists_sq_of_neg`).  The quadratic form is then the boxed
  `q(τ t + w) = -a² τ² + g(w, w)` (`quadForm_supp_signature`).
* **Lorentzian inertia `(1, 3)`, up to overall sign, basis-independent.**
  For `dim W = 3` the inertia of `q` is `(neg, pos, null) = (1, 3, 0)`, that of
  `-q` is `(3, 1, 0)`, and Sylvester's law makes `(1, 3, 0)` invariant under
  every invertible change of basis `X ↦ Xᴴ q X`
  (`supp_signature_minimality`).

Nothing about Clifford representations is used: the inertia is computed
variationally through `posInertia` of `Krein/SignedHaynsworthInertia`.
The independence of the protected orientation row from the positive packet
(`thm:supp-relative-primitive-floor`) enters only through the hypothesis that
the signed line is adjoined orthogonally as an independent direction.
-/

open Matrix Module
open scoped ComplexOrder

namespace RenewalGeometry

section PositivePacket

variable {W : Type} [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
/-- The quadratic form of a positive definite matrix is nonnegative. -/
theorem quadForm_nonneg_of_posDef (D : Matrix W W ℂ) (hD : D.PosDef) (w : W → ℂ) :
    0 ≤ quadForm D w := by
  by_cases hw : w = 0
  · subst hw
    simp [quadForm]
  · exact (quadForm_pos_of_posDef D hD w hw).le

omit [DecidableEq W] in
/-- `thm:supp-signature-minimality`, first clause: the complete positive
packet (a positive definite spatial form `D`) cannot supply a negative
direction — its quadratic form is nonnegative on every vector and its
negative inertia index vanishes. -/
theorem positive_packet_no_negative_direction (D : Matrix W W ℂ) (hD : D.PosDef) :
    (∀ w : W → ℂ, 0 ≤ quadForm D w) ∧ negInertia D = 0 ∧
      posInertia D = Fintype.card W :=
  ⟨quadForm_nonneg_of_posDef D hD, negInertia_of_posDef D hD, posInertia_of_posDef D hD⟩

end PositivePacket

/-- A nondegenerate signed line with sign opposite to the positive spatial
restriction has coefficient `c = -a²` for a unique `a > 0`. -/
theorem exists_sq_of_neg (c : ℝ) (hc : c < 0) : ∃! a : ℝ, 0 < a ∧ c = -a ^ 2 := by
  refine ⟨Real.sqrt (-c), ⟨Real.sqrt_pos.mpr (by linarith), ?_⟩, ?_⟩
  · rw [Real.sq_sqrt (by linarith), neg_neg]
  · rintro b ⟨hb, hcb⟩
    have : Real.sqrt (-c) = Real.sqrt (b ^ 2) := by rw [hcb, neg_neg]
    rw [this, Real.sqrt_sq hb.le]

section OneLine

variable {W : Type} [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
/-- `eq:supp-signature-inertia`, the boxed form: on `τ t + w` the one-line
signed extension with coefficient `-a²` is `q(τ t + w) = -a² τ² + g(w, w)`. -/
theorem quadForm_supp_signature (a : ℝ) (D : Matrix W W ℂ) (τ : ℝ) (w : W → ℂ) :
    quadForm (oneLineSignedExtension (-a ^ 2) D)
        (Sum.elim (fun _ : Fin 1 => (τ : ℂ)) w)
      = -a ^ 2 * τ ^ 2 + quadForm D w :=
  quadForm_oneLineSignedExtension _ D τ w

/-- Inertia of the one-line signed extension on a spatial module of any finite
dimension: `(neg, pos, null) = (1, dim W, 0)`, its negative has
`(dim W, 1, 0)`, and the count is invariant under every invertible change of
basis. -/
theorem oneLineSignedExtension_inertia_full (a : ℝ) (ha : 0 < a)
    (D : Matrix W W ℂ) (hD : D.PosDef) :
    (negInertia (oneLineSignedExtension (-a ^ 2) D) = 1 ∧
      posInertia (oneLineSignedExtension (-a ^ 2) D) = Fintype.card W ∧
      nullInertia (oneLineSignedExtension (-a ^ 2) D) = 0) ∧
    (negInertia (-(oneLineSignedExtension (-a ^ 2) D)) = Fintype.card W ∧
      posInertia (-(oneLineSignedExtension (-a ^ 2) D)) = 1 ∧
      nullInertia (-(oneLineSignedExtension (-a ^ 2) D)) = 0) ∧
    (∀ X : Matrix (Fin 1 ⊕ W) (Fin 1 ⊕ W) ℂ, IsUnit X.det →
      negInertia (Xᴴ * oneLineSignedExtension (-a ^ 2) D * X) = 1 ∧
        posInertia (Xᴴ * oneLineSignedExtension (-a ^ 2) D * X) = Fintype.card W ∧
        nullInertia (Xᴴ * oneLineSignedExtension (-a ^ 2) D * X) = 0) := by
  have hc : -a ^ 2 < 0 := by
    have : 0 < a ^ 2 := by positivity
    linarith
  exact ⟨oneLineSignedExtension_inertia _ hc D hD,
    neg_oneLineSignedExtension_inertia _ hc D hD,
    fun X hX => oneLineSignedExtension_inertia_congruence _ hc D hD X hX⟩

end OneLine

/-- `thm:supp-signature-minimality` (`eq:supp-signature-inertia`): let the
positive spatial form `g` on `W₄ = Fin 3` be positive definite (matrix `D`),
and let the geometric extension retain `D` on `W` and adjoin exactly one
independent nondegenerate signed line with coefficient `c`, whose protected
orientation supplies the sign opposite to the positive spatial restriction
(`c < 0`).  Then `c = -a²` for a unique `a > 0`, the extension's quadratic
form is `q(τ t + w) = -a² τ² + g(w, w)`, its inertia is the Lorentzian
`(neg, pos, null) = (1, 3, 0)`, the overall-sign reversal `-q` has `(3, 1, 0)`,
and the count is invariant under every invertible change of basis.  The
positive packet itself supplies no negative direction. -/
theorem supp_signature_minimality (c : ℝ) (hc : c < 0)
    (D : Matrix (Fin 3) (Fin 3) ℂ) (hD : D.PosDef) :
    ((∀ w : Fin 3 → ℂ, 0 ≤ quadForm D w) ∧ negInertia D = 0) ∧
    ∃! a : ℝ, 0 < a ∧ c = -a ^ 2 ∧
      (∀ (τ : ℝ) (w : Fin 3 → ℂ),
        quadForm (oneLineSignedExtension c D) (Sum.elim (fun _ : Fin 1 => (τ : ℂ)) w)
          = -a ^ 2 * τ ^ 2 + quadForm D w) ∧
      (negInertia (oneLineSignedExtension c D) = 1 ∧
        posInertia (oneLineSignedExtension c D) = 3 ∧
        nullInertia (oneLineSignedExtension c D) = 0) ∧
      (negInertia (-(oneLineSignedExtension c D)) = 3 ∧
        posInertia (-(oneLineSignedExtension c D)) = 1 ∧
        nullInertia (-(oneLineSignedExtension c D)) = 0) ∧
      (∀ X : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ, IsUnit X.det →
        negInertia (Xᴴ * oneLineSignedExtension c D * X) = 1 ∧
          posInertia (Xᴴ * oneLineSignedExtension c D * X) = 3 ∧
          nullInertia (Xᴴ * oneLineSignedExtension c D * X) = 0) := by
  obtain ⟨hnn, hneg, _⟩ := positive_packet_no_negative_direction D hD
  refine ⟨⟨hnn, hneg⟩, ?_⟩
  obtain ⟨a, ⟨ha, hca⟩, huniq⟩ := exists_sq_of_neg c hc
  refine ⟨a, ⟨ha, hca, ?_⟩, ?_⟩
  · subst hca
    obtain ⟨h1, h2, h3⟩ := oneLineSignedExtension_inertia_full a ha D hD
    simp only [Fintype.card_fin] at h1 h2 h3
    exact ⟨fun τ w => quadForm_supp_signature a D τ w, h1, h2, h3⟩
  · rintro b ⟨hb, hcb, -⟩
    exact huniq b ⟨hb, hcb⟩

end RenewalGeometry
