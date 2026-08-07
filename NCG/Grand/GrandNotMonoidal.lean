/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Degree-one data do not reconstruct multiplication
  (`cth:pairwise-not-monoidal-new`, Gran-Tensor manuscript)

* `pairwise_not_monoidal`: two finite unital algebra structures
  on the same four-dimensional Hilbert source-transfer datum —
  the pointwise (commutative `ℂ⁴`) product and the transported
  `M₂(ℂ)` product — share every degree-one and pairwise source
  moment (the common orthonormal Gram of the standard spanning
  family, computed in the one shared inner product), yet the
  first structure is commutative and the second is not: the
  degree-one/pairwise data cannot see the multiplication.

Rendering disclosed: the two products are unital and
associative as proved (`mulM2_assoc`, `mulM2_one`); simplicity
of `M₂(ℂ)` versus the four-dimensional centre of `ℂ⁴` is the
standard classification and is rendered here by the
noncommutativity witness, which already separates the two
structures on identical moment data.
-/

open Matrix

namespace NCG

set_option linter.unusedSimpArgs false

/-- Read a four-vector as a `2×2` matrix (row major). -/
def toM2 (f : Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![f 0, f 1; f 2, f 3]

/-- Read a `2×2` matrix as a four-vector (row major). -/
def ofM2 (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℂ :=
  ![M 0 0, M 0 1, M 1 0, M 1 1]

/-- The transported `M₂(ℂ)` product on the four-dimensional
transfer datum. -/
def mulM2 (f g : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ofM2 (toM2 f * toM2 g)

lemma toM2_ofM2 (M : Matrix (Fin 2) (Fin 2) ℂ) :
    toM2 (ofM2 M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM2, ofM2]

lemma ofM2_toM2 (f : Fin 4 → ℂ) : ofM2 (toM2 f) = f := by
  funext k
  fin_cases k <;> simp [toM2, ofM2]

/-- The transported product is associative. -/
lemma mulM2_assoc (f g h : Fin 4 → ℂ) :
    mulM2 (mulM2 f g) h = mulM2 f (mulM2 g h) := by
  rw [mulM2, mulM2, mulM2, mulM2, toM2_ofM2, toM2_ofM2,
    Matrix.mul_assoc]

/-- The transported product is unital with unit `ofM2 1`. -/
lemma mulM2_one (f : Fin 4 → ℂ) :
    mulM2 (ofM2 1) f = f ∧ mulM2 f (ofM2 1) = f := by
  constructor
  · rw [mulM2, toM2_ofM2, Matrix.one_mul, ofM2_toM2]
  · rw [mulM2, toM2_ofM2, Matrix.mul_one, ofM2_toM2]

/-- `cth:pairwise-not-monoidal-new`: on one shared transfer
datum (the standard orthonormal family of `ℂ⁴`, one inner
product, hence identical degree-one and pairwise moments), the
pointwise structure is commutative while the transported
`M₂(ℂ)` structure is not. -/
theorem pairwise_not_monoidal :
    (∀ i j : Fin 4,
      (star (Pi.single i 1 : Fin 4 → ℂ)) ⬝ᵥ Pi.single j 1
        = if i = j then 1 else 0)
    ∧ (∀ f g : Fin 4 → ℂ, f * g = g * f)
    ∧ (∃ f g : Fin 4 → ℂ, mulM2 f g ≠ mulM2 g f) := by
  refine ⟨?_, fun f g => mul_comm f g, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst hij
      simp [dotProduct, Pi.single_apply]
    · simp [dotProduct, Pi.single_apply, hij, Ne.symm hij,
        Finset.sum_ite_eq]
  · refine ⟨Pi.single 1 1, Pi.single 2 1, ?_⟩
    intro hcontra
    have h0 := congrFun hcontra 0
    have hlhs : mulM2 (Pi.single 1 1) (Pi.single 2 1) 0 = 1 := by
      simp [mulM2, toM2, ofM2, Matrix.mul_apply,
        Fin.sum_univ_two, Pi.single_apply]
    have hrhs : mulM2 (Pi.single 2 1) (Pi.single 1 1) 0 = 0 := by
      simp [mulM2, toM2, ofM2, Matrix.mul_apply,
        Fin.sum_univ_two, Pi.single_apply]
    rw [hlhs, hrhs] at h0
    exact one_ne_zero h0

end NCG
