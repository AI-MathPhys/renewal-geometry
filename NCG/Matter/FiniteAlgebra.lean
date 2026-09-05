/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The minimal finite algebra `ℂ ⊕ ℍ ⊕ M₃(ℂ)`
  (`thm:finite-algebra`, SM_emergence)

The conditional classification of the minimal finite real algebra
carrying the assumed sector types.  Wedderburn–Artin data over `ℝ`
is a list of blocks `(D, n)` with `D ∈ {ℝ, ℂ, ℍ}` (the Frobenius
alternative, encoded in `DivType` exactly as the manuscript's
sector-type conditions encode it) and `n` the matrix size.

* `sector_lower_bounds` — any block list containing the scalar
  complex block `(ℂ,1)`, the pseudoreal block `(ℍ,1)`, and the
  genuinely complex rank-three block `(ℂ,3)` has at least three
  blocks and real dimension at least `24`;
* `minimal_block_data_unique` — a list realizing the three demanded
  sector types with the Pareto-minimal block number (three) is a
  permutation of the canonical data
  `[(ℂ,1), (ℍ,1), (ℂ,3)]`;
* `AF`, `AF_semisimple`, `finrank_AF` — the canonical realization
  `A_F = ℂ × ℍ × M₃(ℂ)`: a semisimple finite-dimensional real
  algebra of real dimension `2 + 4 + 18 = 24`.

Obtaining the Standard-Model charged bimodule additionally requires
the chirality/reality/incidence hypotheses of the bimodule, exactly
as the manuscript states; the classification here is of the algebra.
-/

namespace NCG

/-- The Frobenius alternative for finite-dimensional real division
algebras: `ℝ`, `ℂ`, or `ℍ`. -/
inductive DivType : Type
  | R : DivType
  | C : DivType
  | H : DivType
deriving DecidableEq

/-- Real dimension of the division algebra. -/
def DivType.dim : DivType → ℕ
  | .R => 1
  | .C => 2
  | .H => 4

/-- Real dimension of a Wedderburn block `M_n(D)`. -/
def blockDim (b : DivType × ℕ) : ℕ := b.2 ^ 2 * b.1.dim

/-- The canonical minimal block data: scalar `ℂ`, pseudoreal `ℍ`,
genuinely complex rank three `M₃(ℂ)`. -/
def canonicalBlocks : List (DivType × ℕ) :=
  [(DivType.C, 1), (DivType.H, 1), (DivType.C, 3)]

/-- The three demanded sector types. -/
def realizesSectors (L : List (DivType × ℕ)) : Prop :=
  (DivType.C, 1) ∈ L ∧ (DivType.H, 1) ∈ L ∧ (DivType.C, 3) ∈ L

theorem canonical_realizes : realizesSectors canonicalBlocks := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [canonicalBlocks]

/-- `thm:finite-algebra` (lower bounds): any Wedderburn data
realizing the three demanded sector types has at least three blocks,
and its total real dimension is at least
`dim ℂ + dim ℍ + dim M₃(ℂ) = 24`. -/
theorem sector_lower_bounds {L : List (DivType × ℕ)}
    (hL : realizesSectors L) :
    3 ≤ L.length ∧ 24 ≤ (L.map blockDim).sum := by
  obtain ⟨h1, h2, h3⟩ := hL
  have hsub : List.Subperm canonicalBlocks L := by
    apply List.subperm_of_subset
    · simp [canonicalBlocks]
    · intro x hx
      simp only [canonicalBlocks, List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | h
      · exact h1
      · exact h2
      · exact h3
      · simp at h
  constructor
  · have := hsub.length_le
    simpa [canonicalBlocks] using this
  · have hperm : (canonicalBlocks.map blockDim).sum ≤
        (L.map blockDim).sum := by
      obtain ⟨l', hl', hsl⟩ := hsub
      calc (canonicalBlocks.map blockDim).sum
          = (l'.map blockDim).sum := ((hl'.map blockDim).sum_eq).symm
      _ ≤ (L.map blockDim).sum := by
          apply List.Sublist.sum_le_sum (hsl.map blockDim)
          intro x hx
          positivity
    simpa [canonicalBlocks, blockDim, DivType.dim] using hperm

/-- `thm:finite-algebra` (uniqueness): Wedderburn data realizing the
three demanded sector types with the Pareto-minimal block number is
a permutation of the canonical data `[(ℂ,1), (ℍ,1), (ℂ,3)]`. -/
theorem minimal_block_data_unique {L : List (DivType × ℕ)}
    (hL : realizesSectors L) (hmin : L.length = 3) :
    L.Perm canonicalBlocks := by
  obtain ⟨h1, h2, h3⟩ := hL
  have hsub : List.Subperm canonicalBlocks L := by
    apply List.subperm_of_subset
    · simp [canonicalBlocks]
    · intro x hx
      simp only [canonicalBlocks, List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | h
      · exact h1
      · exact h2
      · exact h3
      · simp at h
  exact (hsub.perm_of_length_le (by simp [canonicalBlocks, hmin])).symm

/-- The canonical minimal finite algebra
`A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)`. -/
abbrev AF : Type := ℂ × Quaternion ℝ × Matrix (Fin 3) (Fin 3) ℂ

/-- `A_F` is a semisimple ring (product of the three simple
Wedderburn blocks). -/
theorem AF_semisimple : IsSemisimpleRing AF := inferInstance

/-- `A_F` is a finite-dimensional real algebra of dimension
`2 + 4 + 18 = 24` — the dimension floor of `sector_lower_bounds` is
attained. -/
theorem finrank_AF : Module.finrank ℝ AF = 24 := by
  have hC : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have hH : Module.finrank ℝ (Quaternion ℝ) = 4 :=
    Quaternion.finrank_eq_four
  have hM : Module.finrank ℝ (Matrix (Fin 3) (Fin 3) ℂ) = 18 := by
    have h1 : Module.finrank ℝ (Matrix (Fin 3) (Fin 3) ℂ) =
        Module.finrank ℝ ℂ * Module.finrank ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
      (Module.finrank_mul_finrank ℝ ℂ (Matrix (Fin 3) (Fin 3) ℂ)).symm
    rw [h1, hC, Module.finrank_matrix]
    simp
  rw [Module.finrank_prod, Module.finrank_prod, hC, hH, hM]

end NCG
