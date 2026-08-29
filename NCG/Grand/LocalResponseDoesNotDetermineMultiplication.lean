/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteNoGoCounterexamples
import NCG.Grand.FiniteWeightedSchurNorm

/-!
# Local response kernels do not determine multiplication

This module adds the locality and transfer rows to the existing exact
degree-one nonmonoidal witness.  The common four-dimensional Hilbert carrier
has one scalar transfer and one co-located physical site assignment.  Hence
all transfer moments are common and the selected first/pair response kernels
have arbitrarily strong exponential collars.  Nevertheless the pointwise
product is commutative while the transported `M₂(ℂ)` product is not.
-/

open Matrix Finset

namespace NCG
namespace LocalResponseDoesNotDetermineMultiplication

open FiniteWeightedSchurNorm

/-- Every carrier coordinate has the same physical site, so all physical
block distances vanish. -/
def coLocatedDistance (_ _ : Fin 4) : ℝ := 0

/-- Common scalar transfer on the shared four-dimensional carrier. -/
def scalarTransfer (z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := z • 1

theorem scalarTransfer_pow (z : ℂ) (k : ℕ) :
    scalarTransfer z ^ k = z ^ k • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  induction k with
  | zero => simp [scalarTransfer]
  | succ k ih =>
      rw [pow_succ, ih]
      simp [scalarTransfer]
      module

/-- All source-transfer moments are the common scalar diagonal moments. -/
theorem scalarTransfer_sourceMoment (z : ℂ) (k : ℕ) (i j : Fin 4) :
    (star (Pi.single i 1 : Fin 4 → ℂ)) ⬝ᵥ
        ((scalarTransfer z ^ k) *ᵥ Pi.single j 1) =
      if i = j then z ^ k else 0 := by
  rw [scalarTransfer_pow]
  by_cases hij : i = j
  · subst j
    simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  · simp [dotProduct, Matrix.mulVec, Pi.single_apply, hij]

/-- A selected first-response kernel with every block zero.  It is the same
for both algebra products and satisfies every exponential collar. -/
def firstResponseKernel : Matrix (Fin 4) (Fin 4) ℂ := 0

/-- A selected pair-response kernel with every block zero. -/
def pairResponseKernel : Matrix (Fin 4) (Fin 4) ℂ := 0

theorem firstResponseKernel_weightedSchur_zero (α : ℝ) :
    schurNorm α coLocatedDistance firstResponseKernel = 0 := by
  have hr : ∀ x : Fin 4,
      schurRow α coLocatedDistance firstResponseKernel x = 0 := by
    intro x
    simp [schurRow, firstResponseKernel]
  have hc : ∀ y : Fin 4,
      schurCol α coLocatedDistance firstResponseKernel y = 0 := by
    intro y
    simp [schurCol, firstResponseKernel]
  simp [schurNorm, hr, hc]

theorem pairResponseKernel_weightedSchur_zero (α : ℝ) :
    schurNorm α coLocatedDistance pairResponseKernel = 0 := by
  have hr : ∀ x : Fin 4,
      schurRow α coLocatedDistance pairResponseKernel x = 0 := by
    intro x
    simp [schurRow, pairResponseKernel]
  have hc : ∀ y : Fin 4,
      schurCol α coLocatedDistance pairResponseKernel y = 0 := by
    intro y
    simp [schurCol, pairResponseKernel]
  simp [schurNorm, hr, hc]

/-- The complete algebraic contrast already proved by the degree-one
nonmonoidal witness, packaged as a proposition for downstream theorems. -/
structure AlgebraContrast : Prop where
  sourceGram : ∀ i j : Fin 4,
    (star (Pi.single i 1 : Fin 4 → ℂ)) ⬝ᵥ Pi.single j 1 =
      if i = j then 1 else 0
  pointwise_comm : ∀ f g : Fin 4 → ℂ, f * g = g * f
  pointwise_star : ∀ f g : Fin 4 → ℂ,
    star (f * g) = star f * star g
  transported_assoc : ∀ f g h : Fin 4 → ℂ,
    mulM2 (mulM2 f g) h = mulM2 f (mulM2 g h)
  transported_unit : ∀ f : Fin 4 → ℂ,
    mulM2 (ofM2 1) f = f ∧ mulM2 f (ofM2 1) = f
  transported_star : ∀ f g : Fin 4 → ℂ,
    starM2 (mulM2 f g) = mulM2 (starM2 g) (starM2 f)
  transported_involutive : ∀ f : Fin 4 → ℂ,
    starM2 (starM2 f) = f
  transported_noncommutative : ∃ f g : Fin 4 → ℂ,
    mulM2 f g ≠ mulM2 g f
  transported_simple : ∀ f : Fin 4 → ℂ, f ≠ 0 →
    ∃ a b a' b' : Fin 4 → ℂ,
      mulM2 (mulM2 a f) b + mulM2 (mulM2 a' f) b' = ofM2 1

theorem algebraContrast : AlgebraContrast := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := pairwiseNotMonoidalExact
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Exact locality packaging of `cth:GTLOC-local-response-not-product`.

The first conjunct is the complete existing finite `*`-algebra witness:
identical orthonormal source Grams, a commutative pointwise product, and an
associative unital involutive transported `M₂` product which is
noncommutative and simple.  The new conjuncts show that the same carrier has
one literal scalar transfer at every order and identical exponentially
localized first/pair response kernels for every exponent. -/
theorem local_response_kernels_do_not_reconstruct_local_multiplication :
    AlgebraContrast ∧
    (∀ (z : ℂ) (k : ℕ) (i j : Fin 4),
      (star (Pi.single i 1 : Fin 4 → ℂ)) ⬝ᵥ
          ((scalarTransfer z ^ k) *ᵥ Pi.single j 1) =
        if i = j then z ^ k else 0) ∧
    (∀ α : ℝ, schurNorm α coLocatedDistance firstResponseKernel = 0) ∧
    (∀ α : ℝ, schurNorm α coLocatedDistance pairResponseKernel = 0) := by
  exact ⟨algebraContrast, scalarTransfer_sourceMoment,
    firstResponseKernel_weightedSchur_zero,
    pairResponseKernel_weightedSchur_zero⟩

end LocalResponseDoesNotDetermineMultiplication
end NCG
