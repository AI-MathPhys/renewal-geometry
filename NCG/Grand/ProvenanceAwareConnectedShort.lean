/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SimultaneousNuisanceUniversalShort
import NCG.Grand.RobustReflectedPositivityExact
import NCG.Grand.SMOSWardShortTransportExact
import NCG.Grand.SampledVersusKilledExact
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
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

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

/-! ## Spectral-floor closure of the perturbation argument -/

/-- A Loewner floor for a finite Hermitian matrix is the corresponding
pointwise eigenvalue floor. -/
theorem eigenvalue_floor_of_matrix_floor {d : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (hG : G.IsHermitian)
    (gamma : ℝ)
    (hfloor : (G - (gamma : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef) :
    ∀ i, gamma ≤ hG.eigenvalues i := by
  intro i
  let U := hG.eigenvectorUnitary
  have hdiag : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * G *
      (U : Matrix (Fin d) (Fin d) ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hG.eigenvalues) := by
    have h := hG.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa only [star_eq_conjTranspose] using h
  have hUstarU : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * U = 1 := by
    change star (U : Matrix (Fin d) (Fin d) ℂ) * U = 1
    exact Unitary.coe_star_mul_self U
  have hconj := hfloor.conjTranspose_mul_mul_same (U : Matrix (Fin d) (Fin d) ℂ)
  have hform :
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ *
          (G - (gamma : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) * U =
        Matrix.diagonal (fun j => ((hG.eigenvalues j - gamma : ℝ) : ℂ)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hdiag]
    have hs :
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ *
            ((gamma : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) * U =
          (gamma : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      simp only [Matrix.mul_smul, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_one, hUstarU]
    rw [hs]
    ext a b
    by_cases hab : a = b
    · subst b
      simp [Function.comp_apply]
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  rw [hform] at hconj
  have hii := hconj.diag_nonneg (i := i)
  simpa [Complex.nonneg_iff, Function.comp_apply] using
    (Complex.le_def.mp hii).1

/-- A positive nuisance-Gram floor and an error smaller than half that floor
give positive definiteness of both Grams, sharp floor-based inverse bounds,
and the resolvent Lipschitz estimate. -/
theorem floor_perturbation_inverse_bounds {d : ℕ}
    (G G' : Matrix (Fin d) (Fin d) ℂ)
    (hG : G.IsHermitian) (hG' : G'.IsHermitian)
    (mu epsilon : ℝ) (hmu : 0 < mu) (hepsilon : 0 ≤ epsilon)
    (hhalf : epsilon < mu / 2)
    (hfloor : (G - (mu : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef)
    (hclose : ‖G' - G‖ ≤ epsilon) :
    G.PosDef ∧ G'.PosDef ∧
      ‖G⁻¹‖ ≤ mu⁻¹ ∧ ‖G'⁻¹‖ ≤ (mu - epsilon)⁻¹ ∧
      ‖G⁻¹ - G'⁻¹‖ ≤ mu⁻¹ * epsilon * (mu - epsilon)⁻¹ := by
  have hmue : 0 < mu - epsilon := by linarith
  have hGpd : G.PosDef := GRHRestoringShort.posDef_of_floor hfloor hmu
  let D := G' - G
  have hD : D.IsHermitian := hG'.sub hG
  have hDorder := (RobustReflectedPositivity.hermitian_norm_bound_gives_order_interval
    D hD epsilon hepsilon (by simpa [D] using hclose)).1
  have hG'floor :
      (G' - ((mu - epsilon : ℝ) : ℂ) •
        (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
    have heq :
        G' - ((mu - epsilon : ℝ) : ℂ) •
            (1 : Matrix (Fin d) (Fin d) ℂ) =
          (G - (mu : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) +
            (D + (epsilon : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D]
        ring
      · simp [D, Matrix.one_apply_ne hij]
    rw [heq]
    exact hfloor.add hDorder
  have hG'pd : G'.PosDef := GRHRestoringShort.posDef_of_floor hG'floor hmue
  have hGeig := eigenvalue_floor_of_matrix_floor G hG mu hfloor
  have hG'eig := eigenvalue_floor_of_matrix_floor G' hG' (mu - epsilon) hG'floor
  have hGinv : ‖G⁻¹‖ ≤ mu⁻¹ := by
    rw [← SampledVersusKilled.pinv_eq_inv hGpd]
    exact SMOSWardShortTransportExact.pinv_norm_le_inv hGpd.posSemidef mu hmu hGeig
  have hG'inv : ‖G'⁻¹‖ ≤ (mu - epsilon)⁻¹ := by
    rw [← SampledVersusKilled.pinv_eq_inv hG'pd]
    exact SMOSWardShortTransportExact.pinv_norm_le_inv
      hG'pd.posSemidef (mu - epsilon) hmue hG'eig
  have hleft : G⁻¹ * G = 1 := by
    rw [← SampledVersusKilled.pinv_eq_inv hGpd]
    exact GRHRestoringShort.pinv_mul_self hGpd
  have hright : G' * G'⁻¹ = 1 := by
    rw [← SampledVersusKilled.pinv_eq_inv hG'pd]
    exact GRHRestoringShort.self_mul_pinv hG'pd
  have hdiff := norm_inverse_difference_le G G' G⁻¹ G'⁻¹ hleft hright
  refine ⟨hGpd, hG'pd, hGinv, hG'inv, hdiff.trans ?_⟩
  exact mul_le_mul
    (mul_le_mul hGinv hclose (norm_nonneg _) (inv_nonneg.mpr hmu.le))
    hG'inv
    (norm_nonneg _)
    (mul_nonneg (inv_nonneg.mpr hmu.le) hepsilon)

/-- Explicit operator-Lipschitz budget for a perturbed connected Schur block.
Here `D = F*F`, `R = N*F`, `L = R*`, and `G = N*N` in the manuscript. -/
theorem connectedSchurBlock_operatorLipschitz {d : ℕ}
    (D D' L L' R R' G G' : Matrix (Fin d) (Fin d) ℂ)
    (hG : G.IsHermitian) (hG' : G'.IsHermitian)
    (mu epsilon M : ℝ) (hmu : 0 < mu) (hepsilon : 0 ≤ epsilon)
    (hhalf : epsilon < mu / 2) (hM : 0 ≤ M)
    (hfloor : (G - (mu : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef)
    (hGclose : ‖G' - G‖ ≤ epsilon)
    (hDclose : ‖D - D'‖ ≤ epsilon)
    (hLclose : ‖L - L'‖ ≤ epsilon)
    (hRclose : ‖R - R'‖ ≤ epsilon)
    (hR : ‖R‖ ≤ M) (hL' : ‖L'‖ ≤ M) :
    ‖schurBlock D L G⁻¹ R - schurBlock D' L' G'⁻¹ R'‖ ≤
      epsilon + epsilon * mu⁻¹ * M +
        M * (mu⁻¹ * epsilon * (mu - epsilon)⁻¹) * M +
        M * (mu - epsilon)⁻¹ * epsilon := by
  obtain ⟨_, _, hGinv, hG'inv, hInvDiff⟩ :=
    floor_perturbation_inverse_bounds G G' hG hG' mu epsilon
      hmu hepsilon hhalf hfloor hGclose
  refine (norm_schurBlock_difference_le D D' L L' G⁻¹ G'⁻¹ R R').trans ?_
  have hmue : 0 < mu - epsilon := by linarith
  gcongr <;> positivity

/-- A connected Hermitian block with a positive spectral margin cannot
acquire a nonpositive eigenvalue under a smaller operator perturbation. -/
theorem connected_positive_cutoff_stable {d : ℕ}
    (C C' : Matrix (Fin d) (Fin d) ℂ)
    (hC : C.IsHermitian) (hC' : C'.IsHermitian)
    (margin budget : ℝ) (hbudget : 0 ≤ budget)
    (hfloor : (C - (margin : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef)
    (hclose : ‖C' - C‖ ≤ budget) (hgap : budget < margin) :
    C'.PosDef := by
  apply RobustReflectedPositivity.posDef_of_approximate_min_gt_error
    C' C hC' hC budget margin hbudget
  · simpa [norm_sub_rev] using hclose
  · exact eigenvalue_floor_of_matrix_floor C hC margin hfloor
  · exact hgap

/-- The corresponding negative cutoff is stable by applying the positive
statement to the negatives. -/
theorem connected_negative_cutoff_stable {d : ℕ}
    (C C' : Matrix (Fin d) (Fin d) ℂ)
    (hC : C.IsHermitian) (hC' : C'.IsHermitian)
    (margin budget : ℝ) (hbudget : 0 ≤ budget)
    (hfloor : (-C - (margin : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef)
    (hclose : ‖C' - C‖ ≤ budget) (hgap : budget < margin) :
    (-C').PosDef := by
  apply connected_positive_cutoff_stable (-C) (-C') hC.neg hC'.neg
    margin budget hbudget hfloor
  · calc
      ‖-C' - -C‖ = ‖C' - C‖ := by
        rw [show -C' - -C = -(C' - C) by abel, norm_neg]
      _ ≤ budget := hclose
  · exact hgap

end ProvenanceAwareConnectedShort
end NCG
