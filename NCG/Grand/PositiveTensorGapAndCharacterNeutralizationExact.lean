/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTPositiveUnitaryDichotomy

/-!
# Positive tensor gaps and exact character neutralization

This file completes `thm:GT-positive-unitary-tensor-dichotomy`.  The positive
branch uses the spectral-coordinate theorem already proved in
`GTPositiveUnitaryDichotomy`.  The unitary branch is no longer represented by
one scalar example: for an arbitrary finite character decomposition it
constructs the tensor-character operator and proves that its fixed kernel is
exactly the coordinate direct sum indexed by character tuples whose product is
one.  It also records preservation of finite order and the genuine degree-two
neutralization mechanism.
-/

open Finset Matrix
open scoped ComplexOrder

namespace NCG
namespace PositiveTensorGapAndCharacterNeutralization

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Product character on a pure tensor coordinate. -/
def tensorCharacterAmplitude (χ : ι → ℂ) {t : ℕ} (x : Fin t → ι) : ℂ :=
  ∏ j, χ (x j)

/-- Matrix of `U^{⊗t}` in a character-adapted tensor basis. -/
def characterTensorOperator (χ : ι → ℂ) (t : ℕ) :
    Matrix (Fin t → ι) (Fin t → ι) ℂ :=
  Matrix.diagonal (tensorCharacterAmplitude χ)

/-- The product-one character tuples indexing the invariant direct sum. -/
abbrev NeutralCharacterIndex (χ : ι → ℂ) (t : ℕ) :=
  {x : Fin t → ι // tensorCharacterAmplitude χ x = 1}

/-- Synthesis of the neutral-character coordinate direct sum. -/
noncomputable def neutralCharacterSynthesis (χ : ι → ℂ) (t : ℕ)
    (c : NeutralCharacterIndex χ t → ℂ) : (Fin t → ι) → ℂ :=
  fun x => if h : tensorCharacterAmplitude χ x = 1 then c ⟨x, h⟩ else 0

@[simp] theorem neutralCharacterSynthesis_apply_neutral
    (χ : ι → ℂ) (t : ℕ) (c : NeutralCharacterIndex χ t → ℂ)
    (x : NeutralCharacterIndex χ t) :
    neutralCharacterSynthesis χ t c x.1 = c x := by
  simp [neutralCharacterSynthesis, x.2]

/-- Exact fixed-kernel support formula for an arbitrary finite character
decomposition.  This is the coordinate form of
`Ker(I-U^{⊗t}) = ⨁_{χ₁⋯χₜ=1} H_{χ₁}⊗⋯⊗H_{χₜ}`. -/
theorem characterTensor_fixed_iff_supported_on_neutral
    (χ : ι → ℂ) (t : ℕ) (v : (Fin t → ι) → ℂ) :
    ((1 - characterTensorOperator χ t) *ᵥ v = 0) ↔
      ∀ x, tensorCharacterAmplitude χ x ≠ 1 → v x = 0 := by
  constructor
  · intro h x hx
    have hx0 := congrFun h x
    have hfactor : (1 - tensorCharacterAmplitude χ x) * v x = 0 := by
      calc
        (1 - tensorCharacterAmplitude χ x) * v x =
            v x - tensorCharacterAmplitude χ x * v x := by ring
        _ = 0 := by
          simpa [characterTensorOperator, Matrix.sub_mulVec,
            Matrix.mulVec_diagonal] using hx0
    exact (mul_eq_zero.mp hfactor).resolve_left
      (sub_ne_zero.mpr (Ne.symm hx))
  · intro h
    funext x
    by_cases hx : tensorCharacterAmplitude χ x = 1
    · simp [characterTensorOperator, Matrix.sub_mulVec,
        Matrix.mulVec_diagonal, hx]
    · simp [characterTensorOperator, Matrix.sub_mulVec,
        Matrix.mulVec_diagonal, h x hx]

/-- A fixed tensor has a unique family of coefficients on the neutral
character tuples, so the support description above is literally a direct-sum
decomposition rather than only a vanishing test. -/
theorem characterTensor_fixed_unique_neutral_coordinates
    (χ : ι → ℂ) (t : ℕ) (v : (Fin t → ι) → ℂ)
    (hv : (1 - characterTensorOperator χ t) *ᵥ v = 0) :
    ∃! c : NeutralCharacterIndex χ t → ℂ,
      v = neutralCharacterSynthesis χ t c := by
  have hsupp := (characterTensor_fixed_iff_supported_on_neutral χ t v).mp hv
  let c : NeutralCharacterIndex χ t → ℂ := fun x => v x.1
  refine ⟨c, ?_, ?_⟩
  · funext x
    by_cases hx : tensorCharacterAmplitude χ x = 1
    · simp [neutralCharacterSynthesis, hx, c]
    · simp [neutralCharacterSynthesis, hx, hsupp x hx]
  · intro c' hc'
    funext x
    have hx := congrFun hc' x.1
    simpa [neutralCharacterSynthesis, x.2, c] using hx.symm

/-- Tensor products of characters of common finite order retain that order. -/
theorem tensorCharacterAmplitude_pow_order
    (χ : ι → ℂ) (N t : ℕ) (hχ : ∀ i, χ i ^ N = 1)
    (x : Fin t → ι) :
    tensorCharacterAmplitude χ x ^ N = 1 := by
  rw [tensorCharacterAmplitude, ← Finset.prod_pow]
  simp [hχ]

/-- A nontrivial inverse pair gives a genuinely new invariant tensor at
degree two. -/
theorem inverse_characters_neutralize_in_degree_two
    (χ : ι → ℂ) (a b : ι) (ha : χ a ≠ 1) (hab : χ a * χ b = 1) :
    tensorCharacterAmplitude χ (![a, b] : Fin 2 → ι) = 1 ∧ χ a ≠ 1 := by
  constructor
  · simpa [tensorCharacterAmplitude, Fin.prod_univ_two] using hab
  · exact ha

/-- **`thm:GT-positive-unitary-tensor-dichotomy`.**  Complete finite spectral
coordinate theorem: positive contractions have the exact tensor fixed sector
and inherited gap, whereas arbitrary finite character decompositions have the
full product-one fixed direct sum and can acquire new neutral tensors. -/
theorem positive_tensor_gap_and_character_neutralization (q : ℝ) :
    (∀ (k : ℕ) (tv : ι → ℝ), 0 ≤ q → q < 1 →
      (∀ i, 0 ≤ tv i) → (∀ i, tv i ≤ 1) →
      (∀ i, tv i ≠ 1 → tv i ≤ q) →
      ∀ x : Fin k → ι,
        ((∏ i, tv (x i)) = 1 ↔ ∀ i, tv (x i) = 1) ∧
        (1 - ∏ i, tv (x i) ≥
          (1 - q) * (1 - if ∀ i, tv (x i) = 1 then 1 else 0))) ∧
      (∀ (χ : ι → ℂ) (t : ℕ) (v : (Fin t → ι) → ℂ),
        ((1 - characterTensorOperator χ t) *ᵥ v = 0) ↔
          ∀ x, tensorCharacterAmplitude χ x ≠ 1 → v x = 0) ∧
      (∀ (χ : ι → ℂ) (N t : ℕ), (∀ i, χ i ^ N = 1) →
        ∀ x : Fin t → ι, tensorCharacterAmplitude χ x ^ N = 1) := by
  exact ⟨(gt_positive_unitary_tensor_dichotomy (n := ι) q).1,
    characterTensor_fixed_iff_supported_on_neutral,
    tensorCharacterAmplitude_pow_order⟩

end PositiveTensorGapAndCharacterNeutralization
end NCG
