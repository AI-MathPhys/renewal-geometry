/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Gauge covariance of the complete fermion coefficient

This file proves `prop:SMST-complete-fermion-gauge-covariance`.  The complete
same-history coefficient is the positive Hodge factor multiplying the sum of
the transported spacetime difference and the Clifford--finite-Dirac term.
Component intertwining and Hodge equivariance imply the advertised unitary
left--right covariance.  Rank, the full squared singular spectrum, determinant
divisor, every mass-regulated graph spectral polynomial, and zero-mode
multiplicity are then invariant.
-/

open Matrix

namespace NCG.CompleteFermionGaugeCovariance

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The three assembled constituents of the complete same-history Euclidean
fermion coefficient.  `cliffordFinite` is the already assembled
`Γ_Cl ⊗ D_F^Y(H)` term. -/
structure CoefficientData (n : Type*) [Fintype n] where
  hodge : Matrix n n ℂ
  spatial : Matrix n n ℂ
  cliffordFinite : Matrix n n ℂ

/-- `K_X(λ) = star₀(q) (D_sp^{U,q} + Γ_Cl(q) ⊗ D_F^Y(H))`. -/
def completeCoefficient (d : CoefficientData n) : Matrix n n ℂ :=
  d.hodge * (d.spatial + d.cliffordFinite)

/-- The characteristic polynomial of `KᴴK`; its roots, with multiplicity,
are the squared singular values. -/
noncomputable def squaredSingularPolynomial (K : Matrix n n ℂ) : Polynomial ℂ :=
  (Kᴴ * K).charpoly

/-- The determinant divisor carried by the complete coefficient. -/
def OnDivisor (K : Matrix n n ℂ) : Prop := K.det = 0

/-- The full graph-regulator spectral polynomial.  Varying `massSq` records
the spectral gap of the positive graph block `KᴴK + massSq I`. -/
noncomputable def graphRegulatorPolynomial (massSq : ℂ) (K : Matrix n n ℂ) :
    Polynomial ℂ :=
  (Kᴴ * K + massSq • (1 : Matrix n n ℂ)).charpoly

/-- Source zero-mode multiplicity, written using rank-nullity. -/
noncomputable def zeroModeMultiplicity (K : Matrix n n ℂ) : ℕ :=
  Fintype.card n - K.rank

section Covariance

variable (before after : CoefficientData n)
variable (UF UE : Matrix.unitaryGroup n ℂ)

private theorem unitary_left (U : Matrix.unitaryGroup n ℂ) :
    U.1ᴴ * U.1 = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U

private theorem unitary_right (U : Matrix.unitaryGroup n ℂ) :
    U.1 * U.1ᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp (SetLike.coe_mem U)
  simpa [Matrix.star_eq_conjTranspose] using h

/-- Gauge-link and finite Yukawa covariance, together with Hodge
intertwining, imply covariance of the assembled complete coefficient. -/
theorem completeCoefficient_covariant
    (hspatial : after.spatial = UF.1 * before.spatial * (UE⁻¹).1)
    (hfinite : after.cliffordFinite =
      UF.1 * before.cliffordFinite * (UE⁻¹).1)
    (hhodge : after.hodge * UF.1 = UF.1 * before.hodge) :
    completeCoefficient after =
      UF.1 * completeCoefficient before * (UE⁻¹).1 := by
  simp only [completeCoefficient, hspatial, hfinite]
  calc
    after.hodge *
        (UF.1 * before.spatial * (UE⁻¹).1 +
          UF.1 * before.cliffordFinite * (UE⁻¹).1) =
        (after.hodge * UF.1) *
          (before.spatial + before.cliffordFinite) * (UE⁻¹).1 := by
            noncomm_ring
    _ = (UF.1 * before.hodge) *
          (before.spatial + before.cliffordFinite) * (UE⁻¹).1 := by rw [hhodge]
    _ = UF.1 * (before.hodge *
          (before.spatial + before.cliffordFinite)) * (UE⁻¹).1 := by
            noncomm_ring

/-- Unitary left--right multiplication preserves matrix rank. -/
  theorem rank_gauge_invariant
    (K Kg : Matrix n n ℂ)
    (hcov : Kg = UF.1 * K * (UE⁻¹).1) :
    Kg.rank = K.rank := by
  rw [hcov]
  calc
    (UF.1 * K * (UE⁻¹).1).rank = (K * (UE⁻¹).1).rank := by
      rw [Matrix.mul_assoc]
      exact Matrix.rank_mul_eq_right_of_isUnit_det UF.1 _
        (Matrix.UnitaryGroup.det_isUnit UF)
    _ = K.rank := Matrix.rank_mul_eq_left_of_isUnit_det (UE⁻¹).1 K
      (Matrix.UnitaryGroup.det_isUnit (UE⁻¹))

/-- The Gram matrix is unitarily similar on the source coefficient space. -/
theorem gram_gauge_covariant
    (K Kg : Matrix n n ℂ)
    (hcov : Kg = UF.1 * K * (UE⁻¹).1) :
    Kgᴴ * Kg = UE.1 * (Kᴴ * K) * UE.1ᴴ := by
  have hcov' : Kg = UF.1 * K * UE.1ᴴ := by
    simpa [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose] using hcov
  rw [hcov']
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc UF.1ᴴ UF.1, unitary_left UF, Matrix.one_mul]

/-- The complete squared singular-value polynomial, hence all singular values
with multiplicity, is gauge invariant. -/
theorem squaredSingularPolynomial_gauge_invariant
    (K Kg : Matrix n n ℂ)
    (hcov : Kg = UF.1 * K * (UE⁻¹).1) :
    squaredSingularPolynomial Kg = squaredSingularPolynomial K := by
  rw [squaredSingularPolynomial, squaredSingularPolynomial,
    gram_gauge_covariant UF UE K Kg hcov]
  calc
    (UE.1 * (Kᴴ * K) * UE.1ᴴ).charpoly =
        (UE.1 * ((Kᴴ * K) * UE.1ᴴ)).charpoly := by rw [Matrix.mul_assoc]
    _ = ((Kᴴ * K) * UE.1ᴴ * UE.1).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = ((Kᴴ * K) * (UE.1ᴴ * UE.1)).charpoly := by rw [Matrix.mul_assoc]
    _ = (Kᴴ * K).charpoly := by rw [unitary_left UE, Matrix.mul_one]

/-- The determinant zero divisor is unchanged. -/
theorem divisor_gauge_invariant
    (K Kg : Matrix n n ℂ)
    (hcov : Kg = UF.1 * K * (UE⁻¹).1) :
    OnDivisor Kg ↔ OnDivisor K := by
  have hUF : UF.1.det ≠ 0 := (Matrix.UnitaryGroup.det_isUnit UF).ne_zero
  have hUE : ((UE⁻¹).1 : Matrix n n ℂ).det ≠ 0 :=
    (Matrix.UnitaryGroup.det_isUnit (UE⁻¹)).ne_zero
  simp only [OnDivisor, hcov, Matrix.det_mul]
  constructor
  · intro h
    have hleft : UF.1.det * K.det = 0 :=
      (mul_eq_zero.mp h).resolve_right hUE
    exact (mul_eq_zero.mp hleft).resolve_left hUF
  · intro h
    simp [h]

/-- Every mass-regulated graph spectral polynomial is invariant; in
particular the regulator gap extracted from its least root is invariant. -/
theorem graphRegulatorPolynomial_gauge_invariant
    (K Kg : Matrix n n ℂ)
    (hcov : Kg = UF.1 * K * (UE⁻¹).1)
    (massSq : ℂ) :
    graphRegulatorPolynomial massSq Kg =
      graphRegulatorPolynomial massSq K := by
  have hgram := gram_gauge_covariant UF UE K Kg hcov
  have hmass : UE.1 * (massSq • (1 : Matrix n n ℂ)) * UE.1ᴴ =
      massSq • (1 : Matrix n n ℂ) := by
    simp [Matrix.mul_assoc, unitary_right UE]
  have hconj : Kgᴴ * Kg + massSq • (1 : Matrix n n ℂ) =
      UE.1 * (Kᴴ * K + massSq • (1 : Matrix n n ℂ)) * UE.1ᴴ := by
    rw [hgram]
    calc
      UE.1 * (Kᴴ * K) * UE.1ᴴ + massSq • (1 : Matrix n n ℂ) =
          UE.1 * (Kᴴ * K) * UE.1ᴴ +
            UE.1 * (massSq • (1 : Matrix n n ℂ)) * UE.1ᴴ := by rw [hmass]
      _ = UE.1 * (Kᴴ * K + massSq • (1 : Matrix n n ℂ)) * UE.1ᴴ := by
        noncomm_ring
  rw [graphRegulatorPolynomial, graphRegulatorPolynomial, hconj]
  calc
    (UE.1 * (Kᴴ * K + massSq • (1 : Matrix n n ℂ)) * UE.1ᴴ).charpoly =
        (UE.1 * ((Kᴴ * K + massSq • (1 : Matrix n n ℂ)) * UE.1ᴴ)).charpoly := by
          rw [Matrix.mul_assoc]
    _ = ((Kᴴ * K + massSq • (1 : Matrix n n ℂ)) * UE.1ᴴ * UE.1).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = ((Kᴴ * K + massSq • (1 : Matrix n n ℂ)) *
        (UE.1ᴴ * UE.1)).charpoly := by rw [Matrix.mul_assoc]
    _ = (Kᴴ * K + massSq • (1 : Matrix n n ℂ)).charpoly := by
      rw [unitary_left UE, Matrix.mul_one]

/-- Source zero-mode multiplicity is invariant. -/
theorem zeroModeMultiplicity_gauge_invariant
    (K Kg : Matrix n n ℂ)
    (hcov : Kg = UF.1 * K * (UE⁻¹).1) :
    zeroModeMultiplicity Kg = zeroModeMultiplicity K := by
  simp only [zeroModeMultiplicity, rank_gauge_invariant UF UE K Kg hcov]

/-- `prop:SMST-complete-fermion-gauge-covariance`: the covariance equation is
derived from the assembled constituents, and all five listed finite
invariants are transported in one packet. -/
theorem complete_fermion_gauge_covariance
    (hspatial : after.spatial = UF.1 * before.spatial * (UE⁻¹).1)
    (hfinite : after.cliffordFinite =
      UF.1 * before.cliffordFinite * (UE⁻¹).1)
    (hhodge : after.hodge * UF.1 = UF.1 * before.hodge) :
    let K := completeCoefficient before
    let Kg := completeCoefficient after
    Kg = UF.1 * K * (UE⁻¹).1 ∧
      Kg.rank = K.rank ∧
      squaredSingularPolynomial Kg = squaredSingularPolynomial K ∧
      (OnDivisor Kg ↔ OnDivisor K) ∧
      (∀ massSq, graphRegulatorPolynomial massSq Kg =
        graphRegulatorPolynomial massSq K) ∧
      zeroModeMultiplicity Kg = zeroModeMultiplicity K := by
  dsimp only
  have hcov := completeCoefficient_covariant before after UF UE
    hspatial hfinite hhodge
  exact ⟨hcov,
    rank_gauge_invariant UF UE _ _ hcov,
    squaredSingularPolynomial_gauge_invariant UF UE _ _ hcov,
    divisor_gauge_invariant UF UE _ _ hcov,
    fun massSq => graphRegulatorPolynomial_gauge_invariant UF UE _ _ hcov massSq,
    zeroModeMultiplicity_gauge_invariant UF UE _ _ hcov⟩

end Covariance

end NCG.CompleteFermionGaugeCovariance
