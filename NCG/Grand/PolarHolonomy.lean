/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.Bicommutant
import NCG.Grand.SqrtPolar

/-!
# Polar metric–holonomy commutant theorem
  (`thm:SMST-polar-holonomy`, Gran-Tensor manuscript)

* `smst_polar_holonomy`:
  (A) on each edge `e : λ → μ` with invertible transport
      `F = U·P` (unitary–positive polar factors) and tree
      transports `Q_λ, Q_μ` unitary, the transported parallel
      family `R_λ = Q_λRQ_λᴴ`, `R_μ = Q_μRQ_μᴴ` satisfies the
      residual edge equations `R_μF = FR_λ`, `R_λFᴴ = FᴴR_μ`
      **iff** the root operator `R` commutes with the
      root-fibre generators `K_e = Q_λᴴP²Q_λ` and
      `W_e = Q_μᴴUQ_λ` — so a residual family is exactly one
      root operator in `𝒪_{F,X}' = C*(K_e, W_e)'`, transported
      by `R_λ = Q_λRQ_λᴴ`;
  (B) the finite bicommutant theorem: every matrix commuting
      with the commutant of the `*`-closed unital algebra
      `𝒪_{F,X}` lies in `𝒪_{F,X}`, giving
      `(𝒪_{F,X}')' = 𝒪_{F,X}` and hence the mutual
      reconstruction `M_type^{(o)} = 𝒪_{F,X}'`,
      `(M_type^{(o)})' = 𝒪_{F,X}` on the root fibre.

Rendering disclosed: the polar edge equivalence with the
functional-calculus commutation `[R,P²]=0 ⟹ [R,P]=0`
discharged is the proved `polar_edge_of_posDef`
(`lem:SMST-polar-edge`); the assembly over a connected typed
graph (choice of root, spanning tree, ordered products of
unitary factors) is the manuscript's finite induction along
tree paths, applied edge by edge to clause (A).
-/

open Matrix
open scoped ComplexOrder MatrixOrder

set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:SMST-polar-holonomy`. -/
theorem smst_polar_holonomy {g : Type*} [Fintype g]
    [DecidableEq g] :
    -- (A) transported family ↔ root-generator commutation
    (∀ (U P R Qs Qt : Matrix g g ℂ),
      U * Uᴴ = 1 → Uᴴ * U = 1 → P.PosDef →
      Qs * Qsᴴ = 1 → Qsᴴ * Qs = 1 →
      Qt * Qtᴴ = 1 → Qtᴴ * Qt = 1 →
      (((Qt * R * Qtᴴ) * (U * P) = (U * P) * (Qs * R * Qsᴴ)
        ∧ (Qs * R * Qsᴴ) * (U * P)ᴴ
            = (U * P)ᴴ * (Qt * R * Qtᴴ))
      ↔ (R * (Qsᴴ * (P * P) * Qs)
            = (Qsᴴ * (P * P) * Qs) * R
        ∧ R * (Qtᴴ * U * Qs) = (Qtᴴ * U * Qs) * R)))
    -- (B) bicommutant: `(𝒪')' = 𝒪` on the root fibre
    ∧ (∀ (O : Subalgebra ℂ (Matrix g g ℂ)),
        (∀ a ∈ O, aᴴ ∈ O) →
        ∀ T : Matrix g g ℂ,
        (∀ b ∈ matCommutant (O : Set (Matrix g g ℂ)),
          T * b = b * T) → T ∈ O) := by
  constructor
  · intro U P R Qs Qt hU hU' hP hQs hQs' hQt hQt'
    -- prefix cancellation helpers for the three unitaries
    have cQs : ∀ X : Matrix g g ℂ, Qs * (Qsᴴ * X) = X :=
      fun X => by rw [← Matrix.mul_assoc, hQs, Matrix.one_mul]
    have cQs' : ∀ X : Matrix g g ℂ, Qsᴴ * (Qs * X) = X :=
      fun X => by rw [← Matrix.mul_assoc, hQs', Matrix.one_mul]
    have cQt : ∀ X : Matrix g g ℂ, Qt * (Qtᴴ * X) = X :=
      fun X => by rw [← Matrix.mul_assoc, hQt, Matrix.one_mul]
    have cQt' : ∀ X : Matrix g g ℂ, Qtᴴ * (Qt * X) = X :=
      fun X => by rw [← Matrix.mul_assoc, hQt', Matrix.one_mul]
    have cU : ∀ X : Matrix g g ℂ, U * (Uᴴ * X) = X :=
      fun X => by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    have cU' : ∀ X : Matrix g g ℂ, Uᴴ * (U * X) = X :=
      fun X => by rw [← Matrix.mul_assoc, hU', Matrix.one_mul]
    refine Iff.trans
      (polar_edge_of_posDef U P (Qs * R * Qsᴴ)
        (Qt * R * Qtᴴ) hU hU' hP) ?_
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · -- `[R, K_e] = 0` from `[R_λ, P²] = 0`
        have h := congrArg (fun X => Qsᴴ * X * Qs) h1
        simpa only [Matrix.mul_assoc, cQs, cQs', hQs, hQs',
          Matrix.mul_one, Matrix.one_mul] using h
      · -- `[R, W_e] = 0` from `R_μ = U R_λ Uᴴ`
        have h := congrArg (fun X => Qtᴴ * X * (U * Qs)) h2
        simpa only [Matrix.mul_assoc, cQt, cQt', cU, cU',
          hQs, hQs', hU, hU', Matrix.mul_one,
          Matrix.one_mul] using h
    · rintro ⟨hK, hW⟩
      constructor
      · -- `[R_λ, P²] = 0` from `[R, K_e] = 0`
        have h := congrArg (fun X => Qs * X * Qsᴴ) hK
        simpa only [Matrix.mul_assoc, cQs, cQs', hQs, hQs',
          Matrix.mul_one, Matrix.one_mul] using h
      · -- `R_μ = U R_λ Uᴴ` from `[R, W_e] = 0`
        have h := congrArg (fun X => Qt * X * (Qsᴴ * Uᴴ)) hW
        simpa only [Matrix.mul_assoc, cQs, cQs', cQt, cQt',
          cU, cU', hQt, hQt', hU, hU', hQs, hQs',
          Matrix.mul_one, Matrix.one_mul] using h
  · intro O hstar T hT
    exact double_commutant O hstar T hT

end NCG
