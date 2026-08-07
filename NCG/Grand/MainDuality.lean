/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.Bicommutant

/-!
# SM–spacetime loaded Howe duality
  (`thm:SMST-main-duality`, Gran-Tensor manuscript)

* `smst_main_duality`: for the joint typed action algebra
  `𝒜_act` (a unital `*`-closed subalgebra of the finite
  history-carrier matrices):
  (i) the mutual commutant duality
      `𝒜_act' = M_type` (definitional, the residual typed
      multiplicity algebra) and `M_type' = 𝒜_act` — i.e.
      `(𝒜_act')' = 𝒜_act` as sets, by the finite bicommutant
      theorem;
  (ii) the residual algebra `M_type = 𝒜_act'` is itself a
      unital algebra closed under products, sums and adjoints,
      so the duality pairs two genuine `*`-algebras.

Rendering disclosed: the identification of `𝒜_act'` with the
typed parallel multiplicity transformations is the proved
`smst_edge_commutant` record; the root-fibre realization
`M_type^{(o)} = 𝒪_{F,X}'`, `𝒪_{F,X} = (M_type^{(o)})'` is the
proved `smst_polar_holonomy`; that all algebras are
reconstructed from loaded words at saturated depth is the
proved loaded-emergence record — the manuscript's proof cites
exactly these theorems plus the bicommutant step proved here.
-/

open Matrix

namespace NCG

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `thm:SMST-main-duality`. -/
theorem smst_main_duality (A : Subalgebra ℂ (Matrix n n ℂ))
    (hstar : ∀ a ∈ A, aᴴ ∈ A) :
    -- (i) mutual commutant duality `(𝒜_act')' = 𝒜_act`
    matCommutant (matCommutant (A : Set (Matrix n n ℂ)))
      = (A : Set (Matrix n n ℂ))
    -- (ii) the residual `M_type = 𝒜_act'` is a unital *-algebra
    ∧ (1 : Matrix n n ℂ)
        ∈ matCommutant (A : Set (Matrix n n ℂ))
    ∧ (∀ b c : Matrix n n ℂ,
        b ∈ matCommutant (A : Set (Matrix n n ℂ)) →
        c ∈ matCommutant (A : Set (Matrix n n ℂ)) →
        b * c ∈ matCommutant (A : Set (Matrix n n ℂ))
        ∧ b + c ∈ matCommutant (A : Set (Matrix n n ℂ)))
    ∧ (∀ b ∈ matCommutant (A : Set (Matrix n n ℂ)),
        bᴴ ∈ matCommutant (A : Set (Matrix n n ℂ))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Set.eq_of_subset_of_subset
    · intro T hT
      exact double_commutant A hstar T hT
    · intro a ha b hb
      exact (hb a ha).symm
  · intro a _
    rw [Matrix.one_mul, Matrix.mul_one]
  · intro b c hb hc
    constructor
    · intro a ha
      calc b * c * a = b * (a * c) := by
            rw [Matrix.mul_assoc, hc a ha]
        _ = a * (b * c) := by
            rw [← Matrix.mul_assoc, hb a ha,
              Matrix.mul_assoc]
    · intro a ha
      rw [Matrix.add_mul, Matrix.mul_add, hb a ha, hc a ha]
  · intro b hb a ha
    have h := congrArg conjTranspose (hb aᴴ (hstar a ha))
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] at h
    exact h.symm

end NCG
