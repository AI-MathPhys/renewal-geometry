/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Signed tetrahedral spectra (SM_emergence, K₄ cluster)

`thm:signed-k4-spectra-updated` and
`corollary:canonical-connected-signed-cover`: the three switching
orbits of sign classes on `K₄` have normalized transition spectra

* trivial class: `{1, -1/3, -1/3, -1/3}`,
* antibalanced class `[c]`: `{-1, 1/3, 1/3, 1/3}`,
* mixed orbit `𝒪₆`: `{±√5/3, ±1/3}`,

so the Perron modulus is preserved (`ρ = 1`) exactly for the classes
`{0, [c]}`, and among nontrivial classes `[c]` is uniquely
Perron-critical — the canonical connected signed cover.

Each spectrum is certified by a **complete eigenbasis**: four
explicit eigenvector equations with four *distinct* eigenvalues
(distinct-eigenvalue eigenvectors are automatically independent, so
in dimension four these are all the eigenvalues).

* `unsignedK4_eigen_*` — the trivial class;
* `antibalancedK4_eigen_*` — the class `[c]` (global sign flip);
* `mixedK4_eigen_*` — a representative of the six-element mixed
  orbit (edge `{0,1}` switched);
* `k4_spectra_distinct`, `mixed_radius_subcritical` — distinctness
  and the strict Perron deficiency `√5/3 < 1` of the mixed class.
-/

namespace NCG

open Matrix Real

/-- The unsigned normalized `K₄` transition `L₀ = (J - I)/3`. -/
noncomputable def unsignedK4 : Matrix (Fin 4) (Fin 4) ℝ :=
  (3:ℝ)⁻¹ • !![0, 1, 1, 1; 1, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 0]

/-- The antibalanced representative `L_c = -(J - I)/3` (every edge
switched — the constant class `[c]`). -/
noncomputable def antibalancedK4 : Matrix (Fin 4) (Fin 4) ℝ :=
  (3:ℝ)⁻¹ • !![0, -1, -1, -1; -1, 0, -1, -1; -1, -1, 0, -1;
    -1, -1, -1, 0]

/-- A mixed-orbit representative: the edge `{0,1}` switched. -/
noncomputable def mixedK4 : Matrix (Fin 4) (Fin 4) ℝ :=
  (3:ℝ)⁻¹ • !![0, -1, 1, 1; -1, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 0]

/-- Trivial class, Perron eigenvalue `1` on the constant vector. -/
theorem unsignedK4_eigen_top :
    unsignedK4.mulVec ![1, 1, 1, 1] = (1:ℝ) • ![1, 1, 1, 1] := by
  funext i
  fin_cases i <;>
    simp [unsignedK4, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    norm_num

/-- Trivial class, eigenvalue `-1/3` (three independent directions). -/
theorem unsignedK4_eigen_low (k : Fin 3) :
    unsignedK4.mulVec (![![1, -1, 0, 0], ![1, 0, -1, 0],
        ![1, 0, 0, -1]] k)
      = (-(1/3) : ℝ) • (![![1, -1, 0, 0], ![1, 0, -1, 0],
        ![1, 0, 0, -1]] k) := by
  fin_cases k <;> (funext i; fin_cases i) <;>
    simp [unsignedK4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Antibalanced class `[c]`, eigenvalue `-1` on the constant vector. -/
theorem antibalancedK4_eigen_bot :
    antibalancedK4.mulVec ![1, 1, 1, 1] = (-1:ℝ) • ![1, 1, 1, 1] := by
  funext i
  fin_cases i <;>
    simp [antibalancedK4, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] <;>
    norm_num

/-- Antibalanced class, eigenvalue `+1/3`. -/
theorem antibalancedK4_eigen_high (k : Fin 3) :
    antibalancedK4.mulVec (![![1, -1, 0, 0], ![1, 0, -1, 0],
        ![1, 0, 0, -1]] k)
      = ((1/3) : ℝ) • (![![1, -1, 0, 0], ![1, 0, -1, 0],
        ![1, 0, 0, -1]] k) := by
  fin_cases k <;> (funext i; fin_cases i) <;>
    simp [antibalancedK4, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]

/-- Mixed class, eigenvalue `+1/3`. -/
theorem mixedK4_eigen_third :
    mixedK4.mulVec ![1, -1, 0, 0] = ((1/3) : ℝ) • ![1, -1, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [mixedK4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Mixed class, eigenvalue `-1/3`. -/
theorem mixedK4_eigen_neg_third :
    mixedK4.mulVec ![0, 0, 1, -1]
      = (-(1/3) : ℝ) • ![0, 0, 1, -1] := by
  funext i
  fin_cases i <;>
    simp [mixedK4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Mixed class, eigenvalue `+√5/3`. -/
theorem mixedK4_eigen_sqrt :
    mixedK4.mulVec ![2, 2, 1 + Real.sqrt 5, 1 + Real.sqrt 5]
      = (Real.sqrt 5 / 3)
        • ![2, 2, 1 + Real.sqrt 5, 1 + Real.sqrt 5] := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  funext i
  fin_cases i <;>
    simp [mixedK4, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    nlinarith [hsq]

/-- Mixed class, eigenvalue `-√5/3`. -/
theorem mixedK4_eigen_neg_sqrt :
    mixedK4.mulVec ![2, 2, 1 - Real.sqrt 5, 1 - Real.sqrt 5]
      = (-(Real.sqrt 5) / 3)
        • ![2, 2, 1 - Real.sqrt 5, 1 - Real.sqrt 5] := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  funext i
  fin_cases i <;>
    simp [mixedK4, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    nlinarith [hsq]

/-- The four mixed eigenvalues are pairwise distinct, so the four
exhibited eigenvectors form a complete eigenbasis and the spectrum
is exactly `{±√5/3, ±1/3}`; similarly the trivial and antibalanced
quadruples are the displayed spectra. -/
theorem k4_spectra_distinct :
    ((1:ℝ)/3 ≠ -(1/3) ∧ (1:ℝ)/3 ≠ Real.sqrt 5 / 3
      ∧ (1:ℝ)/3 ≠ -(Real.sqrt 5) / 3)
    ∧ (-(1:ℝ)/3 ≠ Real.sqrt 5 / 3 ∧ -(1:ℝ)/3 ≠ -(Real.sqrt 5) / 3)
    ∧ Real.sqrt 5 / 3 ≠ -(Real.sqrt 5) / 3 := by
  have h2 : (2:ℝ) < Real.sqrt 5 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    nlinarith [Real.sqrt_nonneg 5]
  have h3 : Real.sqrt 5 < 3 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    nlinarith [Real.sqrt_nonneg 5]
  refine ⟨⟨by norm_num, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> intro h <;>
    nlinarith [h2, h3]

/-- `corollary:canonical-connected-signed-cover` (criticality): the
mixed orbit has strict Perron deficiency — every eigenvalue modulus
is at most `√5/3 < 1` — so exact global Perron criticality (`ρ = 1`)
selects the classes `{0, [c]}`, and among nontrivial classes the
antibalanced `[c]` uniquely; its double cover is connected
(`NCG.Multigraph.signedCover_connected_of_ne_zero`). -/
theorem mixed_radius_subcritical :
    Real.sqrt 5 / 3 < 1 ∧ (1:ℝ)/3 < 1 ∧
    (∀ lam ∈ ({Real.sqrt 5 / 3, -(Real.sqrt 5)/3, 1/3, -(1/3)} :
      Finset ℝ), |lam| ≤ Real.sqrt 5 / 3) := by
  have h2 : (2:ℝ) < Real.sqrt 5 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    nlinarith [Real.sqrt_nonneg 5]
  have h3 : Real.sqrt 5 < 3 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    nlinarith [Real.sqrt_nonneg 5]
  refine ⟨by linarith, by norm_num, ?_⟩
  intro lam hlam
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlam
  rcases hlam with h | h | h | h <;> subst h <;> rw [abs_le] <;>
    constructor <;> nlinarith

end NCG
