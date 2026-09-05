/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteRewardLumpabilityAndTiltedSelfEnergy

/-!
# Perron closure for finite reward-lumpable tilts

This file removes the Perron-eigenvector interface from the closure branch of
`thm:accepted-tilted-retract`.  For an irreducible finite tilt, positivity of
the encoder and decoder transports the Perron vector through the commuting
quotient projection.  Thus the fine and compressed matrices have the same
unique eigenvalue admitting a strictly positive eigenvector.
-/

open Matrix

namespace NCG
namespace FiniteRewardPerronClosure

open FiniteRewardLumpabilityAndTiltedSelfEnergy

variable {u x : Type*} [Fintype u] [Fintype x] [Nonempty u] [Nonempty x]
  [DecidableEq u] [DecidableEq x]

/-- A finite nonnegative matrix has no zero row.  Together with a strictly
positive input vector this is exactly what is needed for strict positivity of
its image. -/
def HasPositiveRow {a b : Type*} [Fintype b] (T : Matrix a b ℝ) : Prop :=
  (∀ i j, 0 ≤ T i j) ∧ ∀ i, ∃ j, 0 < T i j

theorem mulVec_pos_of_hasPositiveRow {a b : Type*} [Fintype b]
    (T : Matrix a b ℝ) (hT : HasPositiveRow T)
    (v : b → ℝ) (hv : ∀ j, 0 < v j) :
    ∀ i, 0 < T.mulVec v i := by
  intro i
  obtain ⟨j₀, hj₀⟩ := hT.2 i
  rw [Matrix.mulVec, dotProduct]
  exact Finset.sum_pos'
    (fun j _ => mul_nonneg (hT.1 i j) (hv j).le)
    ⟨j₀, Finset.mem_univ j₀, mul_pos hj₀ (hv j₀)⟩

/-- **Perron part of `thm:accepted-tilted-retract`, without supplied
eigenvectors.**  If `E = C R` commutes with the irreducible fine tilt and
`R C = I`, positive encoder/decoder rows construct a common strictly positive
fine/coarse eigenpair.  Moreover every strictly positive coarse eigenpair has
that same exponent. -/
theorem exists_common_perron_pair
    (B : Matrix x x ℝ) (C : Matrix x u ℝ) (R : Matrix u x ℝ)
    (hRC : R * C = 1) (hcomm : (C * R) * B = B * (C * R))
    (hBirr : B.IsIrreducible) (hC : HasPositiveRow C)
    (hR : HasPositiveRow R) :
    ∃ (psi : ℝ) (fine : x → ℝ) (coarse : u → ℝ),
      0 < psi ∧ (∀ i, 0 < fine i) ∧ (∀ a, 0 < coarse a) ∧
      B.mulVec fine = psi • fine ∧
      (R * B * C).mulVec coarse = psi • coarse ∧
      (∀ (lambda : ℝ) (v : u → ℝ),
        (∀ a, 0 < v a) →
        (R * B * C).mulVec v = lambda • v → lambda = psi) := by
  obtain ⟨psi, fine, hpsi, hfine, hfineEig⟩ :=
    hBirr.exists_pos_eigenvector
  let coarse : u → ℝ := R.mulVec fine
  have hcoarse : ∀ a, 0 < coarse a := by
    intro a
    exact mulVec_pos_of_hasPositiveRow R hR fine hfine a
  have hinter := coarse_to_fine_intertwining B C R hRC hcomm
  have hcoarseEig : (R * B * C).mulVec coarse = psi • coarse := by
    calc
      (R * B * C).mulVec coarse = ((R * B * C) * R).mulVec fine := by
        rw [Matrix.mulVec_mulVec]
      _ = (R * B).mulVec fine := by rw [← hinter]
      _ = R.mulVec (B.mulVec fine) := by rw [Matrix.mulVec_mulVec]
      _ = R.mulVec (psi • fine) := by rw [hfineEig]
      _ = psi • coarse := by rw [Matrix.mulVec_smul]
  refine ⟨psi, fine, coarse, hpsi, hfine, hcoarse, hfineEig,
    hcoarseEig, ?_⟩
  intro lambda v hv hvEig
  have hCv : ∀ i, 0 < C.mulVec v i :=
    mulVec_pos_of_hasPositiveRow C hC v hv
  have hlift : B.mulVec (C.mulVec v) = lambda • C.mulVec v :=
    lift_compressed_eigenvector B C R hRC hcomm v lambda hvEig
  exact (hBirr.eigenvalue_eq_of_pos_eigenvectors hCv hfine hlift hfineEig)

/-- Family form used by the tilted large-deviation statement.  The Perron
functions and positive fine/coarse eigenvectors are outputs, and their common
Legendre--Fenchel rate function is therefore identical on both descriptions. -/
theorem exists_common_perron_pressures_and_rate_functions
    (B : ℝ → Matrix x x ℝ) (C : Matrix x u ℝ) (R : Matrix u x ℝ)
    (hRC : R * C = 1)
    (hcomm : ∀ k, (C * R) * B k = B k * (C * R))
    (hirr : ∀ k, (B k).IsIrreducible)
    (hC : HasPositiveRow C) (hR : HasPositiveRow R) :
    ∃ (fineExponent coarseExponent : ℝ → ℝ)
      (fineVector : ℝ → x → ℝ) (coarseVector : ℝ → u → ℝ),
      (∀ k i, 0 < fineVector k i) ∧
      (∀ k a, 0 < coarseVector k a) ∧
      (∀ k, (B k).mulVec (fineVector k) =
        fineExponent k • fineVector k) ∧
      (∀ k, (R * B k * C).mulVec (coarseVector k) =
        coarseExponent k • coarseVector k) ∧
      fineExponent = coarseExponent ∧
      ∀ a, rateFunction fineExponent a = rateFunction coarseExponent a := by
  have hex (k : ℝ) :=
    exists_common_perron_pair (B k) C R hRC (hcomm k) (hirr k) hC hR
  choose psi fine coarse hpsi hfine hcoarse hfineEig hcoarseEig hunique using hex
  refine ⟨psi, psi, fine, coarse, hfine, hcoarse, hfineEig,
    hcoarseEig, rfl, ?_⟩
  intro a
  rfl

/-! ## Actual tilted-resolvent Schur formula -/

/-- The visible block of the inverse of the actual tilted resolvent is the
inverse self-energy Schur complement.  Unlike the earlier corner lemma, the
block resolvent equations and their inverses are not hypotheses: they are
derived by the matrix Schur inverse theorem from invertibility of the hidden
corner and the displayed effective visible operator.  The arguments `B` and
`C` are the signed off-diagonal blocks of `zI-B_k` (and hence are the negatives
of the corresponding transition blocks). -/
theorem tilted_resolvent_visible_block
    {v h : Type*} [Fintype v] [Fintype h] [DecidableEq v] [DecidableEq h]
    (A : Matrix v v ℝ) (B : Matrix v h ℝ)
    (C : Matrix h v ℝ) (D : Matrix h h ℝ)
    [Invertible D] [Invertible (A - B * D⁻¹ * C)] :
    (((Matrix.fromBlocks A B C D)⁻¹).toBlocks₁₁) =
      (A - B * D⁻¹ * C)⁻¹ := by
  haveI hSchurInvOf : Invertible (A - B * ⅟D * C) :=
    (inferInstance : Invertible (A - B * D⁻¹ * C)).copy _ (by
      rw [Matrix.invOf_eq_nonsing_inv])
  haveI hFull : Invertible (Matrix.fromBlocks A B C D) :=
    Matrix.fromBlocks₂₂Invertible A B C D
  have hinv := Matrix.invOf_fromBlocks₂₂_eq A B C D
  rw [← Matrix.invOf_eq_nonsing_inv (Matrix.fromBlocks A B C D),
    hinv, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv (A - B * ⅟D * C),
    Matrix.invOf_eq_nonsing_inv D]

end FiniteRewardPerronClosure
end NCG
