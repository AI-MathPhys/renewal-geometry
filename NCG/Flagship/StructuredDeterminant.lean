/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Structured chronology spectrum and determinant multiplicity
  (`thm:structured-determinant-source-master`, flagship
   manuscript)

* `chronoEigen`: the boxed exact one-Read eigenvalue formula
  `Λ_{s,λ} = α₀ + sα₁ + a_λ(β₀ + sβ₁) + p_λa_λ(γ₀ + sγ₁)` on the
  eight labels `(s,λ)`, with the table
  `(dim, p, a) = (1,1,5), (5,1,-1), (3,-1,√5), (3,-1,-√5)`
  (`dimRep`, `pRep`, `aRep`);
* `chronoEigen_trace`: the normalization check — the
  dimension-weighted sum over all eight labels collapses to
  `24α₀` (the parity sum kills `α₁,β₁,γ₁`, and the two column
  identities `Σ dim·a = 0 = Σ dim·p·a` kill the rest), so the
  native normalization `α₀ = 1/24` gives unit trace;
* `structured_positivity`: positivity of the block state is
  exactly the eight displayed inequalities `Λ_{s,λ} ≥ 0`
  (diagonal criterion on the label set);
* `rdet` and `rdet_instances`: the boxed determinant-character
  multiplicity `r_det = m₃³ + m₃'³ + 3(m₃+m₃')m₅²` with its four
  displayed values `1, 2, 8, 64` for the native coherent,
  complete sign-odd, full oriented-line, and completely Read
  pointer sources.

Rendering disclosed: the identification of the eight eigenvalue
labels with the icosahedral association scheme (permutation
module `1₊ ⊕ 5₊ ⊕ 3₋ ⊕ 3'₋`, depth Hadamard parity, antipodal
eigenvalue `p_λ`, positive-neighbour adjacency eigenvalue `a_λ`)
and the Schur-lemma block form of a general equivariant state are
the manuscript's representation-theoretic steps; the character
calculation locating one determinant copy in each of `3⊗³`,
`3'⊗³`, `3⊗5⊗5`, `3'⊗5⊗5` is the classical icosahedral character
table input feeding the polynomial `rdet`.
-/

open Finset

namespace NCG

noncomputable section

/-- The boxed one-Read eigenvalue
`Λ_{s,λ} = α₀ + sα₁ + a(β₀ + sβ₁) + p·a(γ₀ + sγ₁)`. -/
def chronoEigen (α0 α1 β0 β1 γ0 γ1 s p a : ℝ) : ℝ :=
  α0 + s * α1 + a * (β0 + s * β1) + p * a * (γ0 + s * γ1)

/-- Dimensions of `1, 5, 3, 3'`. -/
def dimRep : Fin 4 → ℝ := ![1, 5, 3, 3]

/-- Antipodal eigenvalues `p_λ`. -/
def pRep : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- Positive-neighbour adjacency eigenvalues `a_λ`. -/
def aRep : Fin 4 → ℝ :=
  ![5, -1, Real.sqrt 5, -Real.sqrt 5]

/-- Normalization: the dimension-weighted trace of the one-Read
spectrum is `24α₀`, so `α₀ = 1/24` gives a unit-trace source. -/
theorem chronoEigen_trace (α0 α1 β0 β1 γ0 γ1 : ℝ) :
    ∑ l : Fin 4, dimRep l
      * (chronoEigen α0 α1 β0 β1 γ0 γ1 1 (pRep l) (aRep l)
        + chronoEigen α0 α1 β0 β1 γ0 γ1 (-1) (pRep l) (aRep l))
      = 24 * α0 := by
  simp [chronoEigen, dimRep, pRep, aRep, Fin.sum_univ_four]
  ring

/-- Positivity of the structured one-Read source is exactly the
eight inequalities `Λ_{s,λ} ≥ 0`. -/
theorem structured_positivity (α0 α1 β0 β1 γ0 γ1 : ℝ) :
    (Matrix.diagonal fun q : Fin 2 × Fin 4 =>
        chronoEigen α0 α1 β0 β1 γ0 γ1 (![1, -1] q.1)
          (pRep q.2) (aRep q.2)).PosSemidef
      ↔ ∀ q : Fin 2 × Fin 4,
          0 ≤ chronoEigen α0 α1 β0 β1 γ0 γ1 (![1, -1] q.1)
            (pRep q.2) (aRep q.2) :=
  Matrix.posSemidef_diagonal_iff

/-- The boxed determinant-character multiplicity
`r_det = m₃³ + m₃'³ + 3(m₃ + m₃')m₅²`. -/
def rdet (m3 m3' m5 : ℕ) : ℕ :=
  m3 ^ 3 + m3' ^ 3 + 3 * (m3 + m3') * m5 ^ 2

/-- The four displayed instances: native coherent `1`, complete
sign-odd `2`, full oriented-line `8`, completely Read pointer
`64`. -/
theorem rdet_instances :
    rdet 1 0 0 = 1 ∧ rdet 1 1 0 = 2 ∧ rdet 1 1 1 = 8
      ∧ rdet 2 2 2 = 64 := by
  norm_num [rdet]

end

end NCG
