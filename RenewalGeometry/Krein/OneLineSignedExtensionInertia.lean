/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Krein.SignedHaynsworthInertia

/-!
# Minimal one-sign extension has Lorentzian inertia
  (`prop:main-signature-minimality`, `eq:main-signature-inertia`,
  `thm:supp-signature-minimality`; emergent-spacetime manuscript)

Let `D` be the (Hermitian) matrix of the positive spatial form `g` on the
spatial module `W` (positive definite, as reconstructed from the `K₄/A₃` root
race), and adjoin one independent real line `ℝt` orthogonally with a real
coefficient `c`.  The orthogonal one-line extension is the block matrix
`oneLineSignedExtension c D = fromBlocks (diagonal c) 0 0 D` on `Fin 1 ⊕ W`,
whose quadratic form is `q(τ t + w) = c τ² + g(w, w)`
(`quadForm_oneLineSignedExtension`).

* Nondegeneracy of the adjoined line is `c ≠ 0`; the protected orientation
  supplying the sign *opposite* to the positive spatial restriction is
  `c < 0`, i.e. `c = -N⁻²` for a unique lapse normalization `N > 0`
  (`exists_lapse_of_neg`), giving the boxed form `-N⁻² τ² + g(w, w)`.
* `oneLineSignedExtension_inertia`: for `c < 0` and `D` positive definite the
  inertia is `(neg, pos, null) = (1, dim W, 0)`; for `dim W = 3` this is the
  Lorentzian inertia `(1, 3)` (`oneLineSignedExtension_inertia_lorentz`).
* The overall-sign clause: the negated form `-(oneLineSignedExtension c D)`
  has inertia `(dim W, 1, 0)`, i.e. `(3, 1)` for `dim W = 3`
  (`neg_oneLineSignedExtension_inertia`), and Sylvester's law
  (`sylvester_inertia`) makes the count invariant under every invertible
  change of basis (`oneLineSignedExtension_inertia_congruence`).

The inertia is computed variationally through `posInertia` of
`Krein/SignedHaynsworthInertia`; no Clifford representation enters.
-/

open Matrix Module
open scoped ComplexOrder

namespace RenewalGeometry

section DefiniteInertia

variable {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma quadForm_neg (M : Matrix n n ℂ) (v : n → ℂ) :
    quadForm (-M) v = -quadForm M v := by
  unfold quadForm
  rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]

omit [DecidableEq n] in
/-- The positive index is the full dimension when the form is positive on
every nonzero vector. -/
theorem posInertia_eq_card_of_forall_pos (M : Matrix n n ℂ)
    (hM : ∀ v : n → ℂ, v ≠ 0 → 0 < quadForm M v) :
    posInertia M = Fintype.card n := by
  apply le_antisymm
  · exact csSup_le ⟨0, zero_mem_dimSet M⟩ (fun d hd => dimSet_bddAbove M d hd)
  · apply le_csSup ⟨Fintype.card n, fun d hd => dimSet_bddAbove M d hd⟩
    exact ⟨⊤, fun v _ hv => hM v hv, by rw [finrank_top, finrank_pi]⟩

omit [DecidableEq n] in
/-- The positive index vanishes when the form is negative on every nonzero
vector. -/
theorem posInertia_eq_zero_of_forall_neg (M : Matrix n n ℂ)
    (hM : ∀ v : n → ℂ, v ≠ 0 → quadForm M v < 0) :
    posInertia M = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  apply csSup_le ⟨0, zero_mem_dimSet M⟩
  rintro d ⟨V, hV, rfl⟩
  have hbot : V = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra h0
    have h1 := hV v hv h0
    have h2 := hM v h0
    linarith
  rw [hbot, finrank_bot]

omit [DecidableEq n] in
/-- A positive definite matrix has positive quadratic form on nonzero
vectors. -/
theorem quadForm_pos_of_posDef (D : Matrix n n ℂ) (hD : D.PosDef)
    (v : n → ℂ) (hv : v ≠ 0) : 0 < quadForm D v :=
  (Complex.pos_iff.mp (hD.dotProduct_mulVec_pos hv)).1

omit [DecidableEq n] in
/-- Positive definite: positive index equal to the dimension. -/
theorem posInertia_of_posDef (D : Matrix n n ℂ) (hD : D.PosDef) :
    posInertia D = Fintype.card n :=
  posInertia_eq_card_of_forall_pos D (quadForm_pos_of_posDef D hD)

omit [DecidableEq n] in
/-- Negative definite (`-M` positive definite): positive index zero. -/
theorem posInertia_eq_zero_of_neg_posDef (M : Matrix n n ℂ)
    (hM : (-M).PosDef) : posInertia M = 0 := by
  apply posInertia_eq_zero_of_forall_neg
  intro v hv
  have := quadForm_pos_of_posDef (-M) hM v hv
  rw [quadForm_neg] at this
  linarith

omit [DecidableEq n] in
/-- Positive definite: negative index zero. -/
theorem negInertia_of_posDef (D : Matrix n n ℂ) (hD : D.PosDef) :
    negInertia D = 0 := by
  unfold negInertia
  apply posInertia_eq_zero_of_neg_posDef
  rw [neg_neg]
  exact hD

end DefiniteInertia

section OneLine

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The orthogonal one-line extension of the spatial form `D` on `W` by an
independent real line with coefficient `c` (`eq:main-signature-inertia`,
before normalization `c = -N⁻²`). -/
def oneLineSignedExtension (c : ℝ) (D : Matrix W W ℂ) :
    Matrix (Fin 1 ⊕ W) (Fin 1 ⊕ W) ℂ :=
  fromBlocks (diagonal fun _ : Fin 1 => (c : ℂ)) 0 0 D

omit [DecidableEq W] in
/-- The quadratic form of the extension on `τ t + w` is
`c τ² + g(w, w)`. -/
theorem quadForm_oneLineSignedExtension (c : ℝ) (D : Matrix W W ℂ)
    (τ : ℝ) (w : W → ℂ) :
    quadForm (oneLineSignedExtension c D)
        (Sum.elim (fun _ : Fin 1 => (τ : ℂ)) w)
      = c * τ ^ 2 + quadForm D w := by
  have hstar : ∀ (x₁ : Fin 1 → ℂ) (x₂ : W → ℂ),
      star (Sum.elim x₁ x₂) = Sum.elim (star x₁) (star x₂) := by
    intro x₁ x₂
    funext x
    cases x <;> rfl
  have hdot : ∀ (x₁ y₁ : Fin 1 → ℂ) (x₂ y₂ : W → ℂ),
      (Sum.elim x₁ x₂) ⬝ᵥ (Sum.elim y₁ y₂) = x₁ ⬝ᵥ y₁ + x₂ ⬝ᵥ y₂ := by
    intro x₁ y₁ x₂ y₂
    simp [dotProduct, Fintype.sum_sum_type]
  unfold quadForm oneLineSignedExtension
  rw [Matrix.fromBlocks_mulVec, hstar, hdot]
  simp only [Matrix.zero_mulVec, add_zero, zero_add, Complex.add_re]
  congr 1
  simp [dotProduct, Complex.conj_ofReal]
  ring

/-- The negative coefficient is `-N⁻²` for a unique lapse normalization
`N > 0`. -/
theorem exists_lapse_of_neg (c : ℝ) (hc : c < 0) :
    ∃ N : ℝ, 0 < N ∧ c = -(N⁻¹) ^ 2 := by
  refine ⟨(Real.sqrt (-c))⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr (by linarith)), ?_⟩
  rw [inv_inv, Real.sq_sqrt (by linarith), neg_neg]

/-- The one-line block is negative definite when `c < 0`. -/
theorem neg_diagonal_posDef (c : ℝ) (hc : c < 0) :
    (-(diagonal fun _ : Fin 1 => (c : ℂ))).PosDef := by
  have hdiag : -(diagonal fun _ : Fin 1 => (c : ℂ))
      = diagonal fun _ : Fin 1 => -(c : ℂ) := by
    rw [← Matrix.diagonal_neg]
  rw [hdiag, Matrix.posDef_diagonal_iff]
  intro _
  rw [neg_pos, ← Complex.ofReal_zero, Complex.real_lt_real]
  exact hc

/-- `prop:main-signature-minimality`, inertia clause: for `c < 0` and a
positive definite spatial form `D` on `W`, the one-line signed extension has
one negative, `dim W` positive and no null directions. -/
theorem oneLineSignedExtension_inertia (c : ℝ) (hc : c < 0)
    (D : Matrix W W ℂ) (hD : D.PosDef) :
    negInertia (oneLineSignedExtension c D) = 1 ∧
      posInertia (oneLineSignedExtension c D) = Fintype.card W ∧
      nullInertia (oneLineSignedExtension c D) = 0 := by
  set A : Matrix (Fin 1) (Fin 1) ℂ := diagonal fun _ : Fin 1 => (c : ℂ)
    with hAdef
  have hnegA : (-A).PosDef := neg_diagonal_posDef c hc
  have hA : A.IsHermitian := by
    have := hnegA.isHermitian.neg
    rwa [neg_neg] at this
  have hpos : posInertia (oneLineSignedExtension c D) = Fintype.card W := by
    unfold oneLineSignedExtension
    rw [posInertia_fromBlocks_diag A D hA hD.isHermitian,
      posInertia_eq_zero_of_neg_posDef A hnegA, posInertia_of_posDef D hD,
      zero_add]
  have hneg : negInertia (oneLineSignedExtension c D) = 1 := by
    unfold negInertia oneLineSignedExtension
    have hblocks : -(fromBlocks A 0 0 D) = fromBlocks (-A) 0 0 (-D) := by
      simp only [Matrix.fromBlocks_neg, neg_zero]
    rw [hblocks, posInertia_fromBlocks_diag (-A) (-D) hA.neg hD.isHermitian.neg,
      posInertia_of_posDef (-A) hnegA, Fintype.card_fin]
    have : posInertia (-D) = 0 := by
      apply posInertia_eq_zero_of_neg_posDef
      rw [neg_neg]
      exact hD
    rw [this]
  refine ⟨hneg, hpos, ?_⟩
  unfold nullInertia
  rw [hpos, hneg, Fintype.card_sum, Fintype.card_fin]
  omega

/-- The overall-sign clause of `prop:main-signature-minimality`: the negated
form `-(q)` has `dim W` negative, one positive and no null directions. -/
theorem neg_oneLineSignedExtension_inertia (c : ℝ) (hc : c < 0)
    (D : Matrix W W ℂ) (hD : D.PosDef) :
    negInertia (-(oneLineSignedExtension c D)) = Fintype.card W ∧
      posInertia (-(oneLineSignedExtension c D)) = 1 ∧
      nullInertia (-(oneLineSignedExtension c D)) = 0 := by
  obtain ⟨hneg, hpos, _⟩ := oneLineSignedExtension_inertia c hc D hD
  have h1 : posInertia (-(oneLineSignedExtension c D)) = 1 := hneg
  have h2 : negInertia (-(oneLineSignedExtension c D)) = Fintype.card W := by
    unfold negInertia
    rw [neg_neg]
    exact hpos
  refine ⟨h2, h1, ?_⟩
  unfold nullInertia
  rw [h1, h2, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Sylvester invariance: the inertia `(1, dim W, 0)` of the one-line signed
extension is invariant under every invertible change of basis `X`. -/
theorem oneLineSignedExtension_inertia_congruence (c : ℝ) (hc : c < 0)
    (D : Matrix W W ℂ) (hD : D.PosDef)
    (X : Matrix (Fin 1 ⊕ W) (Fin 1 ⊕ W) ℂ) (hX : IsUnit X.det) :
    negInertia (Xᴴ * oneLineSignedExtension c D * X) = 1 ∧
      posInertia (Xᴴ * oneLineSignedExtension c D * X) = Fintype.card W ∧
      nullInertia (Xᴴ * oneLineSignedExtension c D * X) = 0 := by
  obtain ⟨hp, hn, h0⟩ := sylvester_inertia (oneLineSignedExtension c D) X hX
  obtain ⟨hneg, hpos, hnull⟩ := oneLineSignedExtension_inertia c hc D hD
  exact ⟨by rw [hn, hneg], by rw [hp, hpos], by rw [h0, hnull]⟩

end OneLine

/-- `eq:main-signature-inertia`: on the three-dimensional spatial module
`W = Fin 3` the minimal one-sign extension `-N⁻² τ² + g(w, w)` has
Lorentzian inertia `(1, 3)`; its negative has inertia `(3, 1)`. -/
theorem oneLineSignedExtension_inertia_lorentz (N : ℝ) (hN : 0 < N)
    (D : Matrix (Fin 3) (Fin 3) ℂ) (hD : D.PosDef) :
    (negInertia (oneLineSignedExtension (-(N⁻¹) ^ 2) D) = 1 ∧
      posInertia (oneLineSignedExtension (-(N⁻¹) ^ 2) D) = 3 ∧
      nullInertia (oneLineSignedExtension (-(N⁻¹) ^ 2) D) = 0) ∧
    (negInertia (-(oneLineSignedExtension (-(N⁻¹) ^ 2) D)) = 3 ∧
      posInertia (-(oneLineSignedExtension (-(N⁻¹) ^ 2) D)) = 1 ∧
      nullInertia (-(oneLineSignedExtension (-(N⁻¹) ^ 2) D)) = 0) := by
  have hc : -(N⁻¹) ^ 2 < 0 := by
    have : 0 < (N⁻¹) ^ 2 := by positivity
    linarith
  have h1 := oneLineSignedExtension_inertia (-(N⁻¹) ^ 2) hc D hD
  have h2 := neg_oneLineSignedExtension_inertia (-(N⁻¹) ^ 2) hc D hD
  simp only [Fintype.card_fin] at h1 h2
  exact ⟨h1, h2⟩

/-- The boxed quadratic form `q(τ t + w) = -N⁻² τ² + g(w, w)` of
`eq:main-signature-inertia`. -/
theorem quadForm_lorentz_boxed (N : ℝ) (D : Matrix (Fin 3) (Fin 3) ℂ)
    (τ : ℝ) (w : Fin 3 → ℂ) :
    quadForm (oneLineSignedExtension (-(N⁻¹) ^ 2) D)
        (Sum.elim (fun _ : Fin 1 => (τ : ℂ)) w)
      = -(N⁻¹) ^ 2 * τ ^ 2 + quadForm D w :=
  quadForm_oneLineSignedExtension _ D τ w

end RenewalGeometry
