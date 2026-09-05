/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ConnectedScoreDeformation
import NCG.Grand.PsdBlockSchurExact
import NCG.Grand.AssemblyRectangularStoppingFrontExact

/-!
# Efficient connected scores with the Moore--Penrose nuisance projection

This gives the literal pseudoinverse formulation of
`thm:efficient-connected-score`, without a full-column-rank assumption.  It
also derives the one-cell stationarity equations from the manuscript's
nuisance-span inclusion instead of taking those equations as hypotheses.
-/

open Matrix Finset
open scoped ComplexOrder

namespace NCG
namespace EfficientConnectedScorePseudoinverse

open SourceCoercivityInfluence PsdBlockSchur

variable {H k l : Type*} [Fintype H] [Fintype k] [Fintype l]
variable [DecidableEq H] [DecidableEq l]

/-- The nuisance Gram is positive semidefinite. -/
theorem nuisanceGram_posSemidef (Z : Matrix H l ℂ) :
    (Zᴴ * Z).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Z

/-- Spectral Moore--Penrose inverse of the nuisance Gram. -/
noncomputable def nuisanceGramPinv (Z : Matrix H l ℂ) : Matrix l l ℂ :=
  pinv (nuisanceGram_posSemidef Z).1

/-- Orthogonal projection onto the nuisance column span. -/
noncomputable def nuisanceProjection (Z : Matrix H l ℂ) : Matrix H H ℂ :=
  Z * nuisanceGramPinv Z * Zᴴ

/-- Connected residual after nuisance shorting. -/
noncomputable def connectedResidual (F : Matrix H k ℂ) (Z : Matrix H l ℂ) :
    Matrix H k ℂ := (1 - nuisanceProjection Z) * F

/-- Efficient connected-score Gram. -/
noncomputable def connectedGram (F : Matrix H k ℂ) (Z : Matrix H l ℂ) :
    Matrix k k ℂ := (connectedResidual F Z)ᴴ * connectedResidual F Z

theorem nuisanceGramPinv_isHermitian (Z : Matrix H l ℂ) :
    (nuisanceGramPinv Z).IsHermitian :=
  pinv_isHermitian (nuisanceGram_posSemidef Z).1

/-- The nuisance synthesis kills the null complement of its Gram support. -/
theorem mul_supportProj_nuisanceGram (Z : Matrix H l ℂ) :
    Z * supportProj (nuisanceGram_posSemidef Z).1 = Z := by
  let Q := supportProj (nuisanceGram_posSemidef Z).1
  have hQ := supportProj_posSemidef (nuisanceGram_posSemidef Z).1
  have hzero : (Z * (1 - Q))ᴴ * (Z * (1 - Q)) = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hQ.1.eq]
    calc
      ((1 - Q) * Zᴴ) * (Z * (1 - Q)) =
          (1 - Q) * ((Zᴴ * Z) * (1 - Q)) := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [mul_one_sub_supportProj (nuisanceGram_posSemidef Z),
          Matrix.mul_zero]
  have hz := Matrix.conjTranspose_mul_self_eq_zero.mp hzero
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hz
  exact hz.symm

/-- The spectral nuisance operator is an orthogonal projection. -/
theorem nuisanceProjection_isOrthProj (Z : Matrix H l ℂ) :
    AssemblyRectangularStoppingFront.IsOrthProj (nuisanceProjection Z) := by
  have hJ := nuisanceGramPinv_isHermitian Z
  constructor
  · unfold nuisanceProjection
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ.eq,
      Matrix.conjTranspose_conjTranspose]
    exact (Matrix.mul_assoc _ _ _).symm
  · unfold nuisanceProjection nuisanceGramPinv
    calc
      (Z * pinv (nuisanceGram_posSemidef Z).1 * Zᴴ) *
          (Z * pinv (nuisanceGram_posSemidef Z).1 * Zᴴ) =
        Z * (pinv (nuisanceGram_posSemidef Z).1 * (Zᴴ * Z) *
          pinv (nuisanceGram_posSemidef Z).1) * Zᴴ := by
            simp only [Matrix.mul_assoc]
      _ = Z * pinv (nuisanceGram_posSemidef Z).1 * Zᴴ := by
        rw [pinv_mul_self_mul_pinv]

theorem nuisanceProjection_mul_self (Z : Matrix H l ℂ) :
    nuisanceProjection Z * Z = Z := by
  unfold nuisanceProjection nuisanceGramPinv
  calc
    Z * pinv (nuisanceGram_posSemidef Z).1 * Zᴴ * Z =
        Z * (pinv (nuisanceGram_posSemidef Z).1 * (Zᴴ * Z)) := by
          simp only [Matrix.mul_assoc]
    _ = Z * supportProj (nuisanceGram_posSemidef Z).1 := by
      rw [supportProj_eq_pinv_mul]
    _ = Z := mul_supportProj_nuisanceGram Z

/-- Literal pseudoinverse form of the efficient connected-score short:
boxed short formula, positivity, exact vanishing criterion, nuisance-span
criterion, and frame congruence. -/
theorem efficient_connected_score_pseudoinverse
    (F : Matrix H k ℂ) (Z : Matrix H l ℂ) :
    connectedGram F Z =
        Fᴴ * F - Fᴴ * Z * nuisanceGramPinv Z * Zᴴ * F ∧
      (connectedGram F Z).PosSemidef ∧
      (connectedGram F Z = 0 ↔ connectedResidual F Z = 0) ∧
      (connectedResidual F Z = 0 ↔ ∃ A : Matrix l k ℂ, F = Z * A) ∧
      (∀ U : Matrix k k ℂ,
        connectedGram (F * U) Z = Uᴴ * connectedGram F Z * U) := by
  let P := nuisanceProjection Z
  have hP := nuisanceProjection_isOrthProj Z
  have hIH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.1]
  have hI2 : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]
    rw [hP.2]
    abel
  have hshort : connectedGram F Z =
      Fᴴ * F - Fᴴ * Z * nuisanceGramPinv Z * Zᴴ * F := by
    unfold connectedGram connectedResidual
    change (((1 - P) * F)ᴴ * ((1 - P) * F)) = _
    rw [Matrix.conjTranspose_mul, hIH]
    calc
      Fᴴ * (1 - P) * ((1 - P) * F) = Fᴴ * ((1 - P) * (1 - P)) * F := by
        simp only [Matrix.mul_assoc]
      _ = Fᴴ * (1 - P) * F := by rw [hI2]
      _ = Fᴴ * F - Fᴴ * Z * nuisanceGramPinv Z * Zᴴ * F := by
        unfold P nuisanceProjection
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
          Matrix.mul_assoc]
  refine ⟨hshort, Matrix.posSemidef_conjTranspose_mul_self _,
    Matrix.conjTranspose_mul_self_eq_zero, ?_, ?_⟩
  · constructor
    · intro hR
      refine ⟨nuisanceGramPinv Z * Zᴴ * F, ?_⟩
      unfold connectedResidual at hR
      have : F = nuisanceProjection Z * F := by
        have hR' : F - nuisanceProjection Z * F = 0 := by
          simpa only [Matrix.sub_mul, Matrix.one_mul] using hR
        exact sub_eq_zero.mp hR'
      simpa [nuisanceProjection, Matrix.mul_assoc] using this
    · rintro ⟨A, rfl⟩
      unfold connectedResidual
      calc
        (1 - nuisanceProjection Z) * (Z * A) =
            ((1 - nuisanceProjection Z) * Z) * A := by
              rw [Matrix.mul_assoc]
        _ = 0 := by
          rw [Matrix.sub_mul, Matrix.one_mul, nuisanceProjection_mul_self,
            sub_self, Matrix.zero_mul]
  · intro U
    unfold connectedGram connectedResidual
    simp only [Matrix.mul_assoc, Matrix.conjTranspose_mul]

/-! ## Deriving marginal stationarity from nuisance-span inclusion -/

variable {A B K L : Type*} [Fintype A] [Fintype B] [Fintype K] [Fintype L]
variable [DecidableEq A] [DecidableEq B]

/-- Weighted row test vector whose pairing with a score is the derivative of
the first marginal at `a`. -/
def rowTest (p : A × B → ℝ) (a : A) : A × B → ℝ :=
  fun ω => if ω.1 = a then p ω else 0

/-- Weighted column test vector whose pairing with a score is the derivative
of the second marginal at `b`. -/
def columnTest (p : A × B → ℝ) (b : B) : A × B → ℝ :=
  fun ω => if ω.2 = b then p ω else 0

/-- Orthogonality to a nuisance synthesis turns inclusion of every weighted
row and column test vector in its range into the two marginal-stationarity
identities. -/
theorem marginal_stationarity_of_nuisance_span
    (R : Matrix (A × B) K ℝ) (Z : Matrix (A × B) L ℝ)
    (p : A × B → ℝ)
    (horth : Zᵀ * R = 0)
    (hrowSpan : ∀ a, ∃ u : L → ℝ, Z *ᵥ u = rowTest p a)
    (hcolSpan : ∀ b, ∃ u : L → ℝ, Z *ᵥ u = columnTest p b) :
    ∀ v : K → ℝ,
      (∀ a, ∑ b, p (a, b) * (R *ᵥ v) (a, b) = 0) ∧
      (∀ b, ∑ a, p (a, b) * (R *ᵥ v) (a, b) = 0) := by
  intro v
  have hperp : ∀ u : L → ℝ, (Z *ᵥ u) ⬝ᵥ (R *ᵥ v) = 0 := by
    intro u
    calc
      (Z *ᵥ u) ⬝ᵥ (R *ᵥ v) =
          u ⬝ᵥ Zᵀ *ᵥ (R *ᵥ v) := by
            rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
      _ = u ⬝ᵥ ((Zᵀ * R) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec]
      _ = 0 := by
        rw [horth, Matrix.zero_mulVec, dotProduct_zero]
  constructor
  · intro a
    obtain ⟨u, hu⟩ := hrowSpan a
    have h := hperp u
    rw [hu] at h
    have heq : rowTest p a ⬝ᵥ (R *ᵥ v) =
        ∑ b, p (a, b) * (R *ᵥ v) (a, b) := by
      rw [dotProduct, Fintype.sum_prod_type]
      calc
        (∑ x, ∑ y, rowTest p a (x, y) * (R *ᵥ v) (x, y)) =
            ∑ y, rowTest p a (a, y) * (R *ᵥ v) (a, y) := by
          apply Finset.sum_eq_single a
          · intro a' _ hne
            simp [rowTest, hne]
          · simp [rowTest]
        _ = ∑ b, p (a, b) * (R *ᵥ v) (a, b) := by simp [rowTest]
    rw [heq] at h
    exact h
  · intro b
    obtain ⟨u, hu⟩ := hcolSpan b
    have h := hperp u
    rw [hu] at h
    have heq : columnTest p b ⬝ᵥ (R *ᵥ v) =
        ∑ a, p (a, b) * (R *ᵥ v) (a, b) := by
      rw [dotProduct, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      calc
        (∑ y, columnTest p b (a, y) * (R *ᵥ v) (a, y)) =
            columnTest p b (a, b) * (R *ᵥ v) (a, b) := by
          apply Finset.sum_eq_single b
          · intro b' _ hne
            simp [columnTest, hne]
          · simp [columnTest]
        _ = p (a, b) * (R *ᵥ v) (a, b) := by simp [columnTest]
    rw [heq] at h
    exact h

/-- The manuscript's nuisance-span assumption supplies the stationarity
hypotheses of the existing exponential-deformation theorem. -/
theorem connected_score_exponential_witness_of_nuisance_span
    (R : Matrix (A × B) K ℝ) (Z : Matrix (A × B) L ℝ)
    (v : K → ℝ) (p : A × B → ℝ)
    (hprob : ∑ ω, p ω = 1)
    (hcenter : ∑ ω, p ω * (R *ᵥ v) ω = 0)
    (horth : Zᵀ * R = 0)
    (hrowSpan : ∀ a, ∃ u : L → ℝ, Z *ᵥ u = rowTest p a)
    (hcolSpan : ∀ b, ∃ u : L → ℝ, Z *ᵥ u = columnTest p b)
    (hnonzero : R *ᵥ v ≠ 0) :
    (R *ᵥ v ≠ 0) ∧
      (∀ ω, HasDerivAt
        (fun t => scoreDeformation p (R *ᵥ v) t ω)
        (p ω * (R *ᵥ v) ω) 0) ∧
      (∀ a, HasDerivAt
        (fun t => firstMarginal (scoreDeformation p (R *ᵥ v) t) a) 0 0) ∧
      (∀ b, HasDerivAt
        (fun t => secondMarginal (scoreDeformation p (R *ᵥ v) t) b) 0 0) := by
  obtain ⟨hrow, hcol⟩ := marginal_stationarity_of_nuisance_span
    R Z p horth hrowSpan hcolSpan v
  exact connectedScoreExponentialWitness R v p hprob hcenter hrow hcol hnonzero

end EfficientConnectedScorePseudoinverse
end NCG
