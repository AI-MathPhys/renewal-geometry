/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual

/-!
# Moore--Penrose export of the private multiplicity propagator

This is the exact finite linear-algebra content of
`cor:SMST-private-SM-export`.  The aggregate and matching-axis frames are two
coefficient panels of the same reconstructed source.  Vanishing source Schur
residual gives factorization through the aggregate frame.  When that frame is
the stated orthogonal basis (equivalently, its Gram is invertible), the factor
is unique and equals `G_A† C_AT`.  A homogeneous tail then contributes exactly
the reciprocal survival scalar.
-/

open Matrix

namespace NCG

/-- The private propagator reconstructed from the aggregate Gram and the
aggregate--tail cross Gram. -/
noncomputable def privateMultiplicityPropagator {h a t : ℕ}
    (A : Matrix (Fin h) (Fin a) ℂ)
    (T : Matrix (Fin h) (Fin t) ℂ) : Matrix (Fin a) (Fin t) ℂ :=
  sourceGramPseudoinverse A * (Aᴴ * T)

/-- An invertible aggregate Gram makes its CFC Moore--Penrose inverse a true
left inverse. -/
theorem sourceGramPseudoinverse_mul_gram_eq_one_of_invertible
    {h a : ℕ} (A : Matrix (Fin h) (Fin a) ℂ)
    [Invertible (Aᴴ * A)] :
    sourceGramPseudoinverse A * (Aᴴ * A) = 1 := by
  let X : Matrix (Fin a) (Fin a) ℂ := Aᴴ * A
  let J : Matrix (Fin a) (Fin a) ℂ := sourceGramPseudoinverse A
  have hXJX : X * J * X = X :=
    (sourceGramPseudoinverse_projection A).2.1
  calc
    J * X = 1 * (J * X) := by rw [Matrix.one_mul]
    _ = (X⁻¹ * X) * (J * X) := by
      rw [Matrix.inv_mul_of_invertible]
    _ = X⁻¹ * (X * J * X) := by
      simp only [Matrix.mul_assoc]
    _ = X⁻¹ * X := by rw [hXJX]
    _ = 1 := Matrix.inv_mul_of_invertible X

/-- On the orthogonal/full-column-rank aggregate frame, any exact tail factor
is the Moore--Penrose cross-Gram factor. -/
theorem privateMultiplicityPropagator_eq_factor
    {h a t : ℕ}
    (A : Matrix (Fin h) (Fin a) ℂ)
    (T : Matrix (Fin h) (Fin t) ℂ)
    (P : Matrix (Fin a) (Fin t) ℂ)
    [Invertible (Aᴴ * A)] (hT : T = A * P) :
    privateMultiplicityPropagator A T = P := by
  rw [privateMultiplicityPropagator, hT]
  calc
    sourceGramPseudoinverse A * (Aᴴ * (A * P)) =
        (sourceGramPseudoinverse A * (Aᴴ * A)) * P := by
      simp only [Matrix.mul_assoc]
    _ = P := by
      rw [sourceGramPseudoinverse_mul_gram_eq_one_of_invertible,
        Matrix.one_mul]

/-- The factor through a full-column-rank aggregate frame is unique. -/
theorem privateMultiplicityFactor_unique
    {h a t : ℕ}
    (A : Matrix (Fin h) (Fin a) ℂ)
    (T : Matrix (Fin h) (Fin t) ℂ)
    [Invertible (Aᴴ * A)]
    (P Q : Matrix (Fin a) (Fin t) ℂ)
    (hP : T = A * P) (hQ : T = A * Q) : P = Q := by
  calc
    P = privateMultiplicityPropagator A T :=
      (privateMultiplicityPropagator_eq_factor A T P hP).symm
    _ = Q := privateMultiplicityPropagator_eq_factor A T Q hQ

/-- The exact Schur-zero branch reconstructs the unique private propagator by
the boxed formula `G_A† C_AT`. -/
theorem zeroSchur_privateMultiplicityPropagator_reconstruction
    {h a t : ℕ}
    (A : Matrix (Fin h) (Fin a) ℂ)
    (T : Matrix (Fin h) (Fin t) ℂ)
    [Invertible (Aᴴ * A)]
    (hzero : sourceSchurResidual A T = 0) :
    T = A * privateMultiplicityPropagator A T ∧
      (∀ P : Matrix (Fin a) (Fin t) ℂ,
        T = A * P → P = privateMultiplicityPropagator A T) := by
  obtain ⟨P, hP⟩ :=
    (sourceSchurResidual_eq_zero_iff_rangeIncluded A T).mp hzero
  have hcanonical : privateMultiplicityPropagator A T = P :=
    privateMultiplicityPropagator_eq_factor A T P hP
  constructor
  · rw [hcanonical]
    exact hP
  · intro Q hQ
    exact (privateMultiplicityFactor_unique A T Q P hQ hP).trans
      hcanonical.symm

/-- Homogeneous private-tail survival exports the same propagator with the
single reciprocal scale `M_SM = P_priv/s`. -/
theorem homogeneousPrivateTail_export
    {a t : ℕ} (Ppriv MSM : Matrix (Fin a) (Fin t) ℂ)
    (s : ℝ) (hs : s ≠ 0) (hTail : Ppriv = (s : ℂ) • MSM) :
    MSM = ((s : ℂ)⁻¹) • Ppriv := by
  rw [hTail, smul_smul]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [inv_mul_cancel₀ hsC, one_smul]

/-- Exact packet for `cor:SMST-private-SM-export`: the selected entry and
matching-axis panels identify one unique propagator, and a homogeneous tail
has precisely the stated rescaling. -/
theorem private_multiplicity_moore_penrose_export
    {h a t : ℕ}
    (A : Matrix (Fin h) (Fin a) ℂ)
    (T : Matrix (Fin h) (Fin t) ℂ)
    [Invertible (Aᴴ * A)]
    (hzero : sourceSchurResidual A T = 0)
    (MSM : Matrix (Fin a) (Fin t) ℂ)
    (s : ℝ) (hs : s ≠ 0)
    (hTail : privateMultiplicityPropagator A T = (s : ℂ) • MSM) :
    T = A * privateMultiplicityPropagator A T ∧
      (∀ P : Matrix (Fin a) (Fin t) ℂ,
        T = A * P → P = privateMultiplicityPropagator A T) ∧
      MSM = ((s : ℂ)⁻¹) • privateMultiplicityPropagator A T := by
  exact ⟨(zeroSchur_privateMultiplicityPropagator_reconstruction A T hzero).1,
    (zeroSchur_privateMultiplicityPropagator_reconstruction A T hzero).2,
    homogeneousPrivateTail_export _ _ s hs hTail⟩

end NCG
