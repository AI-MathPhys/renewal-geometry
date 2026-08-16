/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTGraphRegulator
import NCG.Grand.CorrectedDualMeasureCriterion

/-!
# Finite geometry of the canonical graph regulator

This file supplies the projector, covariance, weighted Berry/moment, and
determinant-character layer of `thm:SMST-graph-regulator`, complementing the
block-square and gap theorem in `SMSTGraphRegulator`.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Negative spectral projector written in terms of a normalized Hermitian
sign operator. -/
noncomputable def graphNegativeProjector {n : Type*} [Fintype n] [DecidableEq n]
    (signH : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (1 - signH)

/-- The functional-calculus sign involution gives an orthogonal projector. -/
theorem graphNegativeProjector_orthogonal {n : Type*}
    [Fintype n] [DecidableEq n] (signH : Matrix n n ℂ)
    (hself : signHᴴ = signH) (hsq : signH * signH = 1) :
    (graphNegativeProjector signH)ᴴ = graphNegativeProjector signH
      ∧ graphNegativeProjector signH * graphNegativeProjector signH
        = graphNegativeProjector signH := by
  constructor
  · simp [graphNegativeProjector, Matrix.conjTranspose_sub, hself]
  · simp only [graphNegativeProjector, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hsq]
    module

/-- Gauge covariance of the negative projector follows from covariance of the
normalized sign and unitarity of the finite gauge transformation. -/
theorem graphNegativeProjector_covariant {n : Type*}
    [Fintype n] [DecidableEq n] (U signH : Matrix n n ℂ)
    (_hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) :
    graphNegativeProjector (U * signH * Uᴴ)
      = U * graphNegativeProjector signH * Uᴴ := by
  simp only [graphNegativeProjector, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hUU]

/-- The weighted Berry connection in canonical graph frames. -/
def canonicalGraphBerryConnection {E F : Type*}
    [Fintype E] [Fintype F]
    (WE : Matrix E E ℂ) (D dD : Matrix F E ℂ) : ℝ :=
  -(Matrix.trace (WE * Dᴴ * dD)).im

/-- The vertical moment in the trace-real convention. -/
def canonicalGraphVerticalMoment {E F : Type*}
    [Fintype E] [Fintype F]
    (AE : Matrix E E ℂ) (AF : Matrix F F ℂ)
    (XE : Matrix E E ℂ) (XF : Matrix F F ℂ) : ℝ :=
  -(Matrix.trace (AF * XF)).im + (Matrix.trace (AE * XE)).im

/-- Substitution of the gauge tangent `dD = XF D - D XE` into the Berry
connection gives the spectrally weighted vertical moment.  The two push-through
identities are exactly `D f(D*D) D* = I-m R_F^{-1}` and
`f(D*D)D*D = I-m R_E^{-1}` from finite functional calculus. -/
theorem canonicalGraphBerry_vertical
    {E F : Type*} [Fintype E] [Fintype F]
    (WE AE : Matrix E E ℂ) (AF : Matrix F F ℂ)
    (D : Matrix F E ℂ) (XE : Matrix E E ℂ) (XF : Matrix F F ℂ)
    (hF : D * WE * Dᴴ = AF) (hE : WE * Dᴴ * D = AE) :
    canonicalGraphBerryConnection WE D (XF * D - D * XE)
      = canonicalGraphVerticalMoment AE AF XE XF := by
  unfold canonicalGraphBerryConnection canonicalGraphVerticalMoment
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_im]
  have hleft : Matrix.trace (WE * Dᴴ * (XF * D)) =
      Matrix.trace (AF * XF) := by
    calc
      Matrix.trace (WE * Dᴴ * (XF * D))
          = Matrix.trace ((WE * Dᴴ * XF) * D) := by
              simp only [Matrix.mul_assoc]
      _ = Matrix.trace (D * (WE * Dᴴ * XF)) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace (D * WE * Dᴴ * XF) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (AF * XF) := by rw [hF]
  have hright : Matrix.trace (WE * Dᴴ * (D * XE)) =
      Matrix.trace (AE * XE) := by
    simp only [← Matrix.mul_assoc]
    rw [hE]
  rw [hleft, hright]
  ring

/-- Gauge cocycle of the graph determinant line. -/
noncomputable def graphDeterminantCharacter
    {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (UE : Matrix E E ℂ) (UF : Matrix F F ℂ) : ℂ :=
  UF.det * UE.det⁻¹

/-- The graph cocycle is a multiplicative fixed-fibre character. -/
theorem graphDeterminantCharacter_mul
    {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (UE₁ UE₂ : Matrix E E ℂ) (UF₁ UF₂ : Matrix F F ℂ) :
    graphDeterminantCharacter (UE₁ * UE₂) (UF₁ * UF₂)
      = graphDeterminantCharacter UE₁ UF₁
          * graphDeterminantCharacter UE₂ UF₂ := by
  simp only [graphDeterminantCharacter, Matrix.det_mul, _root_.mul_inv_rev]
  ring

/-- Anomaly cancellation trivializes the determinant character. -/
theorem graphDeterminantCharacter_eq_one
    {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (UE : Matrix E E ℂ) (UF : Matrix F F ℂ)
    (hdet : UF.det = UE.det) (hne : UE.det ≠ 0) :
    graphDeterminantCharacter UE UF = 1 := by
  simp [graphDeterminantCharacter, hdet, hne]

/-- `thm:SMST-graph-regulator`, finite projector/connection/cocycle assembly. -/
theorem canonical_graph_regulator_geometry :
    (∀ {n : Type*} [Fintype n] [DecidableEq n]
      (S : Matrix n n ℂ), Sᴴ = S → S * S = 1 →
      (graphNegativeProjector S)ᴴ = graphNegativeProjector S
        ∧ graphNegativeProjector S * graphNegativeProjector S
          = graphNegativeProjector S)
    ∧ (∀ {E F : Type*} [Fintype E] [Fintype F]
      [DecidableEq E] [DecidableEq F]
      (UE : Matrix E E ℂ) (UF : Matrix F F ℂ),
      UF.det = UE.det → UE.det ≠ 0 →
      graphDeterminantCharacter UE UF = 1) :=
  ⟨graphNegativeProjector_orthogonal, graphDeterminantCharacter_eq_one⟩

end NCG
