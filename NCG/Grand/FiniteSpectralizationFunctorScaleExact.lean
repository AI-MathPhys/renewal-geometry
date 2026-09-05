/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteRealEvenSpectralizationExact

/-!
# Functoriality and scale of finite spectralization

Unitary coordinate transports intertwine every component of the finite
spectralization.  Positive rescaling of the differential multiplies the
Dirac and Lipschitz seminorms by the same factor.  The inverse scaling of the
finite Connes metric is proved at the level of its attained variational
maximum.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NCG.FiniteSpectralizationFunctorScaleExact

noncomputable section

open NCG.FiniteRealEvenSpectralizationExact

variable {A I J : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
  [StarModule ℂ A] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

/-- Coordinate data of a trace/Gram preserving packet isomorphism. -/
structure IsometricTransport
    (P Q : FiniteRealEvenSpectralizationExact.Packet
      (A := A) (I := I) (J := J)) where
  U0 : Matrix I I ℂ
  U1 : Matrix J J ℂ
  U0_star_mul : U0ᴴ * U0 = 1
  U0_mul_star : U0 * U0ᴴ = 1
  U1_star_mul : U1ᴴ * U1 = 1
  U1_mul_star : U1 * U1ᴴ = 1
  left0 : ∀ a, U0 * P.left0 a = Q.left0 a * U0
  left1 : ∀ a, U1 * P.left1 a = Q.left1 a * U1
  differential :
    U1 * P.differential = Q.differential * U0
  real0 : U0 * P.j0 = Q.j0 * U0.map star
  real1 : U1 * P.j1 = Q.j1 * U1.map star

namespace IsometricTransport

variable {P Q : FiniteRealEvenSpectralizationExact.Packet
  (A := A) (I := I) (J := J)}
  (F : IsometricTransport P Q)

def unitary : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks F.U0 0 0 F.U1

theorem differentialAdjoint :
    F.U0 * P.differentialᴴ = Q.differentialᴴ * F.U1 := by
  have h := congrArg Matrix.conjTranspose F.differential
  simp only [Matrix.conjTranspose_mul] at h
  calc
    F.U0 * P.differentialᴴ =
        (F.U0 * P.differentialᴴ) * (F.U1ᴴ * F.U1) := by
      rw [F.U1_star_mul, Matrix.mul_one]
    _ = F.U0 * (P.differentialᴴ * F.U1ᴴ) * F.U1 := by
      simp only [Matrix.mul_assoc]
    _ = F.U0 * (F.U0ᴴ * Q.differentialᴴ) * F.U1 := by rw [h]
    _ = (F.U0 * F.U0ᴴ) * Q.differentialᴴ * F.U1 := by
      simp only [Matrix.mul_assoc]
    _ = Q.differentialᴴ * F.U1 := by
      rw [F.U0_mul_star, Matrix.one_mul]

theorem unitary_star_mul :
    F.unitaryᴴ * F.unitary = 1 := by
  unfold unitary
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  exact ⟨by simpa using F.U0_star_mul, by simp, by simp,
    by simpa using F.U1_star_mul⟩

theorem unitary_mul_star :
    F.unitary * F.unitaryᴴ = 1 := by
  unfold unitary
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  exact ⟨by simpa using F.U0_mul_star, by simp, by simp,
    by simpa using F.U1_mul_star⟩

theorem intertwines_representation (a : A) :
    F.unitary * P.representation a =
      Q.representation a * F.unitary := by
  unfold unitary FiniteRealEvenSpectralizationExact.Packet.representation
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  exact ⟨by simpa using F.left0 a, by simp, by simp,
    by simpa using F.left1 a⟩

theorem intertwines_dirac :
    F.unitary * P.dirac = Q.dirac * F.unitary := by
  unfold unitary FiniteRealEvenSpectralizationExact.Packet.dirac
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  exact ⟨by simp, by simpa using F.differentialAdjoint,
    by simpa using F.differential, by simp⟩

theorem intertwines_grading :
    F.unitary * P.grading = Q.grading * F.unitary := by
  unfold unitary FiniteRealEvenSpectralizationExact.Packet.grading
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem intertwines_real :
    F.unitary * P.realMatrix =
      Q.realMatrix * F.unitary.map star := by
  unfold unitary FiniteRealEvenSpectralizationExact.Packet.realMatrix
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  exact ⟨by simpa using F.real0, by simp, by simp,
    by simpa using F.real1⟩

/-- Functoriality package for all four spectral-triple operators. -/
theorem finite_spectralization_functorial :
    F.unitaryᴴ * F.unitary = 1 ∧
    F.unitary * F.unitaryᴴ = 1 ∧
    (∀ a, F.unitary * P.representation a =
      Q.representation a * F.unitary) ∧
    F.unitary * P.dirac = Q.dirac * F.unitary ∧
    F.unitary * P.grading = Q.grading * F.unitary ∧
    F.unitary * P.realMatrix =
      Q.realMatrix * F.unitary.map star := by
  exact ⟨F.unitary_star_mul, F.unitary_mul_star,
    F.intertwines_representation, F.intertwines_dirac,
    F.intertwines_grading, F.intertwines_real⟩

end IsometricTransport

namespace Scale

variable (P : FiniteRealEvenSpectralizationExact.Packet
  (A := A) (I := I) (J := J))

def dirac (s : ℝ) : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks 0 (((s : ℂ) • P.differential)ᴴ)
    ((s : ℂ) • P.differential) 0

def lipschitz (s : ℝ) (a : A) : ℝ :=
  ‖(s : ℂ) • P.B a‖

theorem dirac_eq_smul (s : ℝ) :
    dirac P s = (s : ℂ) • P.dirac := by
  ext x y
  cases x <;> cases y <;>
    simp [dirac, FiniteRealEvenSpectralizationExact.Packet.dirac,
      Matrix.fromBlocks_smul]

theorem lipschitz_eq_mul {s : ℝ} (hs : 0 ≤ s) (a : A) :
    lipschitz P s a = s * ‖P.B a‖ := by
  simp [lipschitz, norm_smul, Complex.norm_real, abs_of_nonneg hs]

def distanceValues (φ ψ : A →ₗ[ℂ] ℂ) : Set ℝ :=
  {r | ∃ a : A, star a = a ∧ ‖P.B a‖ ≤ 1 ∧
    r = ‖φ a - ψ a‖}

def scaledDistanceValues (s : ℝ) (φ ψ : A →ₗ[ℂ] ℂ) : Set ℝ :=
  {r | ∃ a : A, star a = a ∧ s * ‖P.B a‖ ≤ 1 ∧
    r = ‖φ a - ψ a‖}

/-- On the finite branch, where the Connes variational supremum is attained,
positive differential scaling divides its maximum by s. -/
theorem connesDistance_scale_isGreatest
    {s d : ℝ} (hs : 0 < s) (φ ψ : A →ₗ[ℂ] ℂ)
    (hd : IsGreatest (distanceValues P φ ψ) d) :
    IsGreatest (scaledDistanceValues P s φ ψ) (s⁻¹ * d) := by
  rcases hd.1 with ⟨a, haStar, haLip, hdval⟩
  constructor
  · refine ⟨(s⁻¹ : ℂ) • a, ?_, ?_, ?_⟩
    · simp [haStar, Complex.ofReal_inv]
    · have hinv : (s : ℂ)⁻¹ = ((s⁻¹ : ℝ) : ℂ) := by norm_num
      rw [hinv, P.B_real_smul]
      simp only [norm_smul, Complex.norm_real,
        Real.norm_eq_abs]
      calc
        s * (|s⁻¹| * ‖P.B a‖) = ‖P.B a‖ := by
          rw [abs_of_pos (inv_pos.mpr hs)]
          rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
        _ ≤ 1 := haLip
    · rw [hdval]
      simp only [map_smul, ← smul_sub, norm_smul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hs)]
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  · rintro r ⟨a, haStar, haLip, rfl⟩
    have hmem : ‖φ ((s : ℂ) • a) - ψ ((s : ℂ) • a)‖ ≤ d := by
      apply hd.2
      refine ⟨(s : ℂ) • a, ?_, ?_, rfl⟩
      · simp [haStar]
      · rw [P.B_real_smul]
        simpa [norm_smul, Complex.norm_real, abs_of_pos hs] using haLip
    have heq :
        ‖φ ((s : ℂ) • a) - ψ ((s : ℂ) • a)‖ =
          s * ‖φ a - ψ a‖ := by
      simp only [map_smul, ← smul_sub, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hmul : s * ‖φ a - ψ a‖ ≤ d := by
      rw [← heq]
      exact hmem
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hs).2 (by simpa [mul_comm] using hmul)

/-- SP.14, with the distance statement expressed by its attained finite
variational maximum. -/
theorem finite_spectralization_scale
    {s : ℝ} (hs : 0 < s) :
    dirac P s = (s : ℂ) • P.dirac ∧
    (∀ a, lipschitz P s a = s * ‖P.B a‖) ∧
    (∀ (φ ψ : A →ₗ[ℂ] ℂ) d,
      IsGreatest (distanceValues P φ ψ) d →
      IsGreatest (scaledDistanceValues P s φ ψ) (s⁻¹ * d)) := by
  exact ⟨dirac_eq_smul P s, fun a => lipschitz_eq_mul P hs.le a,
    fun φ ψ d => connesDistance_scale_isGreatest P hs φ ψ⟩

end Scale

end

end NCG.FiniteSpectralizationFunctorScaleExact
