/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SimultaneousNuisanceUniversalShort
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Provenance-aware connected short

Exact finite-dimensional source calculus for
`thm:provenance-aware-connected-short`.  Provenance is first orthogonalized
against the common nuisance range.  The connected source is then shortened
against that residual provenance in the same experiment.  The resulting Gram
is the manuscript's Moore--Penrose Schur correction.  The final section gives
the resolvent perturbation bound and the corresponding cutoff-sign test.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace ProvenanceAwareConnectedShort

/-- Provenance after removal of the common nuisance range. -/
noncomputable def residualProvenance {h u p : ℕ}
    (U : Matrix (Fin h) (Fin u) ℂ) (P : Matrix (Fin h) (Fin p) ℂ) :
    Matrix (Fin h) (Fin p) ℂ :=
  nuisanceShortedSource U P

/-- Candidate connected source after simultaneous nuisance and provenance
removal. -/
noncomputable def connectedSource {h u p f : ℕ}
    (U : Matrix (Fin h) (Fin u) ℂ) (P : Matrix (Fin h) (Fin p) ℂ)
    (F : Matrix (Fin h) (Fin f) ℂ) : Matrix (Fin h) (Fin f) ℂ :=
  nuisanceShortedSource (residualProvenance U P)
    (nuisanceShortedSource U F)

/-- The residual provenance range is orthogonal to the nuisance range. -/
theorem nuisance_orthogonal_residualProvenance {h u p : ℕ}
    (U : Matrix (Fin h) (Fin u) ℂ) (P : Matrix (Fin h) (Fin p) ℂ) :
    Uᴴ * residualProvenance U P = 0 := by
  let Q : Matrix (Fin h) (Fin h) ℂ := 1 - sourceRangeProjection U
  obtain ⟨hPH, hP2, hPU⟩ :=
    (sourceGramPseudoinverse_projection U).2.2.2
  have hUP : Uᴴ * sourceRangeProjection U = Uᴴ := by
    have ht := congrArg Matrix.conjTranspose hPU
    simpa only [Matrix.conjTranspose_mul, hPH,
      Matrix.conjTranspose_conjTranspose] using ht
  change Uᴴ * ((1 - sourceRangeProjection U) * P) = 0
  rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hUP,
    sub_self, Matrix.zero_mul]

/-- Orthogonalization does not discard any joint nuisance--provenance vector:
every vector synthesized by `U` and `P` is a sum of a nuisance vector and a
residual-provenance vector. -/
theorem joint_vector_decomposition {h u p : ℕ}
    (U : Matrix (Fin h) (Fin u) ℂ) (P : Matrix (Fin h) (Fin p) ℂ)
    (a : Fin u → ℂ) (b : Fin p → ℂ) :
    U *ᵥ a + P *ᵥ b =
      U *ᵥ (a + sourceGramPseudoinverse U *ᵥ (Uᴴ *ᵥ (P *ᵥ b))) +
        residualProvenance U P *ᵥ b := by
  simp only [residualProvenance, nuisanceShortedSource,
    Matrix.sub_mul, Matrix.one_mul, sourceRangeProjection, Matrix.mul_assoc,
    Matrix.mulVec_add, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  abel

/-- The common-experiment connected Gram is exactly the displayed
provenance Schur correction, with the Moore--Penrose inverse of the residual
provenance Gram. -/
theorem connectedGram_eq_schurCorrection {h u p f : ℕ}
    (U : Matrix (Fin h) (Fin u) ℂ) (P : Matrix (Fin h) (Fin p) ℂ)
    (F : Matrix (Fin h) (Fin f) ℂ) :
    (connectedSource U P F)ᴴ * connectedSource U P F =
      let Q := 1 - sourceRangeProjection U
      Fᴴ * Q * F - (Pᴴ * Q * F)ᴴ *
        sourceGramPseudoinverse (residualProvenance U P) *
          (Pᴴ * Q * F) := by
  let Q : Matrix (Fin h) (Fin h) ℂ := 1 - sourceRangeProjection U
  obtain ⟨hPH, hP2, _⟩ :=
    (sourceGramPseudoinverse_projection U).2.2.2
  have hQH : Qᴴ = Q := by
    simp only [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  have hFF :
      (nuisanceShortedSource U F)ᴴ * nuisanceShortedSource U F =
        Fᴴ * Q * F := by
    simp only [nuisanceShortedSource, Matrix.conjTranspose_mul]
    change (Fᴴ * Qᴴ) * (Q * F) = Fᴴ * Q * F
    rw [hQH]
    calc
      (Fᴴ * Q) * (Q * F) = Fᴴ * ((Q * Q) * F) := by
        simp only [Matrix.mul_assoc]
      _ = Fᴴ * Q * F := by rw [hQ2]; simp only [Matrix.mul_assoc]
  have hPF :
      (residualProvenance U P)ᴴ * nuisanceShortedSource U F =
        Pᴴ * Q * F := by
    simp only [residualProvenance, nuisanceShortedSource,
      Matrix.conjTranspose_mul]
    change (Pᴴ * Qᴴ) * (Q * F) = Pᴴ * Q * F
    rw [hQH]
    calc
      (Pᴴ * Q) * (Q * F) = Pᴴ * ((Q * Q) * F) := by
        simp only [Matrix.mul_assoc]
      _ = Pᴴ * Q * F := by rw [hQ2]; simp only [Matrix.mul_assoc]
  change
    (nuisanceShortedSource (residualProvenance U P)
      (nuisanceShortedSource U F))ᴴ *
      nuisanceShortedSource (residualProvenance U P)
        (nuisanceShortedSource U F) = _
  rw [nuisanceShortedSource_pair]
  simp only [hFF, hPF, Q]

/-! ## Explicit perturbation budget -/

/-- Resolvent identity in the form used for the nuisance-Gram inverse. -/
theorem inverse_difference_identity {A : Type*} [Ring A]
    (G G' J J' : A) (hJG : J * G = 1) (hGJ' : G' * J' = 1) :
    J - J' = J * (G' - G) * J' := by
  calc
    J - J' = J * (G' * J') - (J * G) * J' := by rw [hGJ', hJG, mul_one, one_mul]
    _ = J * (G' - G) * J' := by noncomm_ring

/-- Operator-Lipschitz inverse estimate with both inverse factors visible. -/
theorem norm_inverse_difference_le {A : Type*} [NormedRing A]
    (G G' J J' : A) (hJG : J * G = 1) (hGJ' : G' * J' = 1) :
    ‖J - J'‖ ≤ ‖J‖ * ‖G' - G‖ * ‖J'‖ := by
  rw [inverse_difference_identity G G' J J' hJG hGJ']
  exact norm_mul₃_le

/-- Abstract Schur block `D - L J R`. -/
def schurBlock {A : Type*} [Ring A] (D L J R : A) : A := D - L * J * R

/-- Exact four-block perturbation bound for a Schur correction. -/
theorem norm_schurBlock_difference_le {A : Type*} [NormedRing A]
    (D D' L L' J J' R R' : A) :
    ‖schurBlock D L J R - schurBlock D' L' J' R'‖ ≤
      ‖D - D'‖ + ‖L - L'‖ * ‖J‖ * ‖R‖ +
        ‖L'‖ * ‖J - J'‖ * ‖R‖ + ‖L'‖ * ‖J'‖ * ‖R - R'‖ := by
  have hid : schurBlock D L J R - schurBlock D' L' J' R' =
      (D - D') - (L - L') * J * R - L' * (J - J') * R -
        L' * J' * (R - R') := by
    simp only [schurBlock]
    noncomm_ring
  rw [hid]
  calc
    ‖(D - D') - (L - L') * J * R - L' * (J - J') * R -
          L' * J' * (R - R')‖
        ≤ ‖D - D'‖ + ‖(L - L') * J * R‖ +
            ‖L' * (J - J') * R‖ + ‖L' * J' * (R - R')‖ := by
          simpa only [sub_eq_add_neg, norm_neg] using
            (norm_add₄_le :
              ‖(D - D') + (-((L - L') * J * R)) +
                (-(L' * (J - J') * R)) + (-(L' * J' * (R - R')))‖ ≤
              ‖D - D'‖ + ‖-((L - L') * J * R)‖ +
                ‖-(L' * (J - J') * R)‖ + ‖-(L' * J' * (R - R'))‖)
    _ ≤ ‖D - D'‖ + ‖L - L'‖ * ‖J‖ * ‖R‖ +
          ‖L'‖ * ‖J - J'‖ * ‖R‖ + ‖L'‖ * ‖J'‖ * ‖R - R'‖ := by
        gcongr <;> exact norm_mul₃_le

/-- A separated scalar eigenvalue cannot cross zero inside the certified
operator perturbation budget.  Weyl's estimate supplies `hshift` when the
scalars are corresponding Hermitian eigenvalues. -/
theorem cutoff_sign_stable {lambda lambda' budget : ℝ}
    (hshift : |lambda' - lambda| ≤ budget) :
    (budget < lambda → 0 < lambda') ∧
      (budget < -lambda → lambda' < 0) := by
  rw [abs_le] at hshift
  constructor <;> intro h <;> linarith

end ProvenanceAwareConnectedShort
end NCG
