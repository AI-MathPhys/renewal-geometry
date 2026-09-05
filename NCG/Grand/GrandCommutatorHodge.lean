/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The tetrahedral commutator carrier and the `K₄` Hodge
  isomorphism (`thm:SM-commutator-Hodge`, Gran-Tensor
  manuscript)

For the concrete Pauli writer `F(v) = v·σ` on
`W₀ ≅ ℝ³` (traceless Hermitian image, tetrahedral covariance by
construction):

* clause (i): the writer pairing is the Euclidean form,
  `τ₂(F(v)F(w)) = ⟨v, w⟩` with `τ₂ = ½·Tr`;
* clause (ii): the commutator carrier is the cross-product
  writer, `-(i/2)[F(v), F(w)] = F(v × w)`;
* clause (iii): the boxed identity
  `τ₂(C_F(ξ)C_F(η)) = ⟨ξ, η⟩` on decomposable
  `ξ = v∧w, η = v'∧w'` — so `C_F` is an orthogonal isomorphism
  `H¹(K₄;ℝ) ≅ Herm₀(M₂(ℂ))` (normalization `λ = 1`).

Rendering disclosed: the identification
`H¹(K₄;ℝ) ≅ ⋀²W₀` and the covariant classification of
tetrahedral writers are the manuscript's frame; the six
commutator-edge histories arise from the proved identities by
evaluation on the edge frame.
-/

open Matrix

namespace NCG

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

/-- The concrete Pauli writer `F(v) = v·σ`. -/
noncomputable def pauliWriter (v : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 2 : ℂ), (v 0 : ℂ) - (v 1 : ℂ) * Complex.I;
     (v 0 : ℂ) + (v 1 : ℂ) * Complex.I, -(v 2 : ℂ)]

/-- The Euclidean cross product on `W₀ ≅ ℝ³`. -/
def crossVec (v w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2,
    v 0 * w 1 - v 1 * w 0]

set_option linter.flexible false in
/-- `thm:SM-commutator-Hodge`: writer pairing, commutator
carrier, and the boxed commutator Hodge pairing. -/
theorem commutator_hodge (v w v' w' : Fin 3 → ℝ) :
    ((pauliWriter v * pauliWriter w).trace / 2
      = ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 : ℝ) : ℂ))
    ∧ ((-(Complex.I / 2)) • (pauliWriter v * pauliWriter w
        - pauliWriter w * pauliWriter v)
      = pauliWriter (crossVec v w))
    ∧ ((pauliWriter (crossVec v w)
          * pauliWriter (crossVec v' w')).trace / 2
      = ((crossVec v w 0 * crossVec v' w' 0
          + crossVec v w 1 * crossVec v' w' 1
          + crossVec v w 2 * crossVec v' w' 2 : ℝ) : ℂ)) := by
  have hpair : ∀ a b : Fin 3 → ℝ,
      (pauliWriter a * pauliWriter b).trace / 2
        = ((a 0 * b 0 + a 1 * b 1 + a 2 * b 2 : ℝ) : ℂ) := by
    intro a b
    rw [Matrix.trace_fin_two, Matrix.mul_apply,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [pauliWriter]
    try push_cast
    try ring_nf
    try simp [Complex.I_sq]
    try ring_nf
    try ring
  refine ⟨hpair v w, ?_, hpair _ _⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliWriter, crossVec, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, Matrix.sub_apply] <;>
    push_cast <;>
    ring_nf <;>
    try (simp [Complex.I_sq]) <;>
    try ring_nf

end NCG
