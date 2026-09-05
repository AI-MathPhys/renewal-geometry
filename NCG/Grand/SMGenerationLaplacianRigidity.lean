/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandGenerationLaplacian
import NCG.Grand.FiniteCommutantPoincareGap

/-!
# Generation-Laplacian rigidity margin

This file specializes the finite joint-commutator spectral gap to the two
Hermitian generation residues `A` and `B`.  Together with
`sm_generation_laplacian`, it supplies the quantitative clause of
`thm:SM-generation-Laplacian`: the least positive eigenvalue controls the
Hilbert--Schmidt distance from the common commutant.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- The two generation residues as the finite family used by the joint
commutator construction. -/
def generationResidues {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) : Fin 2 → Matrix n n ℂ :=
  ![A, B]

@[simp] theorem generationResidues_zero {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) : generationResidues A B 0 = A := rfl

@[simp] theorem generationResidues_one {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) : generationResidues A B 1 = B := rfl

/-- The quantitative rigidity margin for the two generation residues.  In the
nontrivial branch `lam` is an actual least eigenvalue of the restricted Gram
matrix; the final inequality is exactly the manuscript's two-commutator
Hilbert--Schmidt estimate. -/
theorem generation_laplacian_rigidity_margin {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) :
    let K : Submodule ℂ (EuclideanSpace ℂ (n × n)) :=
      (LinearMap.ker (jointCommutatorL2 (generationResidues A B)))ᗮ
    K = ⊥ ∨
      ∃ (r : ℕ) (G : Matrix (Fin r) (Fin r) ℂ)
        (hG : G.PosDef) (lam : ℝ),
        r = Module.finrank ℂ K
        ∧ 0 < lam
        ∧ (∃ i : Fin r, lam = hG.1.eigenvalues i)
        ∧ (∀ i : Fin r, lam ≤ hG.1.eigenvalues i)
        ∧ ∀ (X P : Matrix n n ℂ),
          (A * P = P * A ∧ B * P = P * B) →
          matrixL2 (X - P) ∈ K →
          lam * (((X - P)ᴴ * (X - P)).trace).re ≤
            (((A * X - X * A)ᴴ * (A * X - X * A)).trace).re
              + (((B * X - X * B)ᴴ * (B * X - X * B)).trace).re := by
  dsimp only
  obtain hzero | ⟨r, G, hG, lam, hr, hlam, heig, hleast, hgap⟩ :=
    matrix_commutant_least_eigenvalue_gap (generationResidues A B)
  · exact Or.inl hzero
  · right
    refine ⟨r, G, hG, lam, hr, hlam, heig, hleast, ?_⟩
    intro X P hP horth
    have hcomm : ∀ j, generationResidues A B j * P =
        P * generationResidues A B j := by
      intro j
      fin_cases j
      · exact hP.1
      · exact hP.2
    have h := hgap X P hcomm horth
    simpa only [Fin.sum_univ_two, generationResidues_zero,
      generationResidues_one] using h

end NCG
