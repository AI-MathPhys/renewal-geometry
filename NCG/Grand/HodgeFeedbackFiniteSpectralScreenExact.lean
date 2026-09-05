/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianHeatSemigroup
import NCG.Grand.HodgeFeedbackSpectralReduction

/-!
# Finite functional-calculus screen for Hodge feedback

This file supplies the concrete spectral-calculus inequalities used by
`thm:Hodge-feedback-tail`.  In the eigenbasis of a nonnegative finite
Hermitian generator, the high projection is the indicator of `R < lambda`.
The heat multiplier and both resolvents are diagonal there, giving the exact
`exp (-R t)`, `R^-1`, and `|z| R^-2` bounds.  Unitary spectral transport then
turns these into statements about the original Hermitian matrix.
-/

open Matrix
open scoped Norms.L2Operator ComplexOrder

noncomputable section

namespace NCG
namespace HodgeFeedbackFiniteSpectralScreen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Exact finite heat semigroup law -/

theorem finiteSpectralHeat_add (ν : ι → ℝ) (t s : ℝ) :
    ImplicitEuler.finiteSpectralHeat ν (t + s) =
      ImplicitEuler.finiteSpectralHeat ν t *
        ImplicitEuler.finiteSpectralHeat ν s := by
  unfold ImplicitEuler.finiteSpectralHeat
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [show -((t + s) * ν i) = -(t * ν i) + -(s * ν i) by ring,
    Real.exp_add]
  norm_cast

theorem finiteUnitarySpectralHeat_add
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (t s : ℝ) :
    ImplicitEuler.finiteUnitarySpectralHeat U ν (t + s) =
      ImplicitEuler.finiteUnitarySpectralHeat U ν t *
        ImplicitEuler.finiteUnitarySpectralHeat U ν s := by
  unfold ImplicitEuler.finiteUnitarySpectralHeat
  rw [finiteSpectralHeat_add, map_mul]

theorem finiteHermitianHeat_add
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t s : ℝ) :
    ImplicitEuler.finiteHermitianHeat hH (t + s) =
      ImplicitEuler.finiteHermitianHeat hH t *
        ImplicitEuler.finiteHermitianHeat hH s := by
  exact finiteUnitarySpectralHeat_add
    hH.eigenvectorUnitary hH.eigenvalues t s

/-- Diagonal projector onto spectral coordinates strictly above `R`.
This is the complement of the manuscript's low projector on `[0,R]`. -/
def highProjection (ν : ι → ℝ) (R : ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if R < ν i then 1 else 0

theorem highProjection_mul_self (ν : ι → ℝ) (R : ℝ) :
    highProjection ν R * highProjection ν R = highProjection ν R := by
  unfold highProjection
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem finiteSpectralHeat_comm_highProjection
    (ν : ι → ℝ) (R t : ℝ) :
    ImplicitEuler.finiteSpectralHeat ν t * highProjection ν R =
      highProjection ν R * ImplicitEuler.finiteSpectralHeat ν t := by
  unfold ImplicitEuler.finiteSpectralHeat highProjection
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- High part of the heat multiplier in the spectral frame. -/
def highHeatWeight (ν : ι → ℝ) (R t : ℝ) (i : ι) : ℂ :=
  if R < ν i then Real.exp (-(t * ν i)) else 0

theorem finiteSpectralHeat_mul_highProjection
    (ν : ι → ℝ) (R t : ℝ) :
    ImplicitEuler.finiteSpectralHeat ν t * highProjection ν R =
      Matrix.diagonal (highHeatWeight ν R t) := by
  unfold ImplicitEuler.finiteSpectralHeat highProjection highHeatWeight
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- Functional calculus on the high carrier gives the exact exponential
screen, with no abstract screen hypothesis. -/
theorem norm_finiteSpectralHeat_mul_highProjection_le
    (ν : ι → ℝ) (R t : ℝ) (ht : 0 ≤ t) :
    ‖ImplicitEuler.finiteSpectralHeat ν t * highProjection ν R‖ ≤
      Real.exp (-(R * t)) := by
  rw [finiteSpectralHeat_mul_highProjection,
    Matrix.l2_opNorm_diagonal]
  have htarget : 0 ≤ Real.exp (-(R * t)) := (Real.exp_pos _).le
  apply (pi_norm_le_iff_of_nonneg htarget).2
  intro i
  by_cases hi : R < ν i
  · rw [highHeatWeight, if_pos hi, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith
  · simp [highHeatWeight, hi, htarget]

/-- Unitary transport of the high spectral projection. -/
def transportedHighProjection (U : Matrix.unitaryGroup ι ℂ)
    (ν : ι → ℝ) (R : ℝ) : Matrix ι ι ℂ :=
  (U : Matrix ι ι ℂ) * highProjection ν R * (U : Matrix ι ι ℂ)ᴴ

theorem transportedHighProjection_mul_self
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (R : ℝ) :
    transportedHighProjection U ν R * transportedHighProjection U ν R =
      transportedHighProjection U ν R := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  change e (highProjection ν R) * e (highProjection ν R) =
    e (highProjection ν R)
  rw [← map_mul, highProjection_mul_self]

theorem finiteUnitarySpectralHeat_comm_highProjection
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (R t : ℝ) :
    ImplicitEuler.finiteUnitarySpectralHeat U ν t *
        transportedHighProjection U ν R =
      transportedHighProjection U ν R *
        ImplicitEuler.finiteUnitarySpectralHeat U ν t := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  change e (ImplicitEuler.finiteSpectralHeat ν t) *
      e (highProjection ν R) =
    e (highProjection ν R) * e (ImplicitEuler.finiteSpectralHeat ν t)
  rw [← map_mul, ← map_mul, finiteSpectralHeat_comm_highProjection]

theorem norm_finiteUnitarySpectralHeat_mul_highProjection_le
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (R t : ℝ)
    (ht : 0 ≤ t) :
    ‖ImplicitEuler.finiteUnitarySpectralHeat U ν t *
        transportedHighProjection U ν R‖ ≤ Real.exp (-(R * t)) := by
  unfold ImplicitEuler.finiteUnitarySpectralHeat transportedHighProjection
  change ‖((U : Matrix ι ι ℂ) *
      ImplicitEuler.finiteSpectralHeat ν t * (star U : Matrix ι ι ℂ)) *
      ((U : Matrix ι ι ℂ) * highProjection ν R *
        (star U : Matrix ι ι ℂ))‖ ≤ _
  have hUU : (star U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  rw [show ((U : Matrix ι ι ℂ) *
      ImplicitEuler.finiteSpectralHeat ν t * (star U : Matrix ι ι ℂ)) *
      ((U : Matrix ι ι ℂ) * highProjection ν R *
        (star U : Matrix ι ι ℂ)) =
      (U : Matrix ι ι ℂ) *
        (ImplicitEuler.finiteSpectralHeat ν t * highProjection ν R) *
          (star U : Matrix ι ι ℂ) by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U : Matrix ι ι ℂ)
        (U : Matrix ι ι ℂ), hUU, Matrix.one_mul]]
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul]
  exact norm_finiteSpectralHeat_mul_highProjection_le ν R t ht

/-- The high projection of a Hermitian matrix, defined in its canonical
unitary eigenbasis. -/
def hermitianHighProjection {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (R : ℝ) : Matrix ι ι ℂ :=
  transportedHighProjection hH.eigenvectorUnitary hH.eigenvalues R

theorem norm_finiteHermitianHeat_mul_highProjection_le
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (R t : ℝ) (ht : 0 ≤ t) :
    ‖ImplicitEuler.finiteHermitianHeat hH t *
        hermitianHighProjection hH R‖ ≤ Real.exp (-(R * t)) := by
  exact norm_finiteUnitarySpectralHeat_mul_highProjection_le
    hH.eigenvectorUnitary hH.eigenvalues R t ht

/-! ### High resolvent in the same spectral frame -/

def highResolventWeight (ν : ι → ℝ) (R : ℝ) (z : ℂ) (i : ι) : ℂ :=
  if R < ν i then (z + ν i)⁻¹ else 0

def highResolvent (ν : ι → ℝ) (R : ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (highResolventWeight ν R z)

theorem norm_highResolvent_le (ν : ι → ℝ) (R : ℝ) (z : ℂ)
    (hR : 0 < R) (hz : 0 ≤ z.re) :
    ‖highResolvent ν R z‖ ≤ 1 / R := by
  rw [highResolvent, Matrix.l2_opNorm_diagonal]
  have htarget : 0 ≤ 1 / R := by positivity
  apply (pi_norm_le_iff_of_nonneg htarget).2
  intro i
  by_cases hi : R < ν i
  · rw [highResolventWeight, if_pos hi, norm_inv]
    have hreal : R ≤ (z + (ν i : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    have hnorm : R ≤ ‖z + (ν i : ℂ)‖ :=
      hreal.trans (Complex.re_le_norm _)
    have hnormpos : 0 < ‖z + (ν i : ℂ)‖ := lt_of_lt_of_le hR hnorm
    rw [one_div]
    exact inv_anti₀ hR hnorm
  · rw [highResolventWeight, if_neg hi]
    simpa using htarget

/-- Resolvent identity on the high carrier. -/
theorem highResolvent_sub_zero
    (ν : ι → ℝ) (R : ℝ) (z : ℂ) (hR : 0 < R)
    (hz : 0 ≤ z.re) :
    highResolvent ν R z - highResolvent ν R 0 =
      -(z • (highResolvent ν R z * highResolvent ν R 0)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : R < ν i
    · have hν : (ν i : ℂ) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt (hR.trans hi))
      have hsum : z + (ν i : ℂ) ≠ 0 := by
        intro hz0
        have hre := congrArg Complex.re hz0
        simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
        linarith
      simp [highResolvent, highResolventWeight, hi, hν, hsum]
      field_simp
      ring
    · simp [highResolvent, highResolventWeight, hi]
  · simp [highResolvent, Matrix.diagonal_apply, hij]

/-- The manuscript's two inverse estimates are now concrete spectral facts. -/
theorem high_resolvent_pair_bounds (ν : ι → ℝ) (R : ℝ) (z : ℂ)
    (hR : 0 < R) (hz : 0 ≤ z.re) :
    ‖highResolvent ν R 0‖ ≤ 1 / R ∧
      ‖highResolvent ν R z‖ ≤ 1 / R := by
  exact ⟨norm_highResolvent_le ν R 0 hR (by simp),
    norm_highResolvent_le ν R z hR hz⟩

/-! ### Low/high decomposition and unitary transport -/

/-- Full spectral resolvent multiplier.  Under the positive transient-floor
hypothesis used below, every displayed inverse is nonsingular on
`Re z >= 0`. -/
def spectralResolvent (ν : ι → ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => (z + ν i)⁻¹

/-- Low part of the resolvent, including the cutoff eigenvalue itself. -/
def lowResolvent (ν : ι → ℝ) (R : ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if ν i ≤ R then (z + ν i)⁻¹ else 0

theorem spectralResolvent_eq_low_add_high
    (ν : ι → ℝ) (R : ℝ) (z : ℂ) :
    spectralResolvent ν z =
      lowResolvent ν R z + highResolvent ν R z := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : R < ν i
    · simp [spectralResolvent, lowResolvent, highResolvent,
        highResolventWeight, hi, not_le.mpr hi]
    · have hle : ν i ≤ R := le_of_not_gt hi
      simp [spectralResolvent, lowResolvent, highResolvent,
        highResolventWeight, hi, hle]
  · simp [spectralResolvent, lowResolvent, highResolvent, hij]

def transportedSpectralResolvent (U : Matrix.unitaryGroup ι ℂ)
    (ν : ι → ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (spectralResolvent ν z)

def transportedLowResolvent (U : Matrix.unitaryGroup ι ℂ)
    (ν : ι → ℝ) (R : ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (lowResolvent ν R z)

def transportedHighResolvent (U : Matrix.unitaryGroup ι ℂ)
    (ν : ι → ℝ) (R : ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (highResolvent ν R z)

theorem transportedSpectralResolvent_eq_low_add_high
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (R : ℝ) (z : ℂ) :
    transportedSpectralResolvent U ν z =
      transportedLowResolvent U ν R z +
        transportedHighResolvent U ν R z := by
  unfold transportedSpectralResolvent transportedLowResolvent
    transportedHighResolvent
  rw [spectralResolvent_eq_low_add_high, map_add]

theorem norm_transportedHighResolvent_le
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (R : ℝ) (z : ℂ)
    (hR : 0 < R) (hz : 0 ≤ z.re) :
    ‖transportedHighResolvent U ν R z‖ ≤ 1 / R := by
  unfold transportedHighResolvent
  change ‖(U : Matrix ι ι ℂ) * highResolvent ν R z *
      (star U : Matrix ι ι ℂ)‖ ≤ _
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul]
  exact norm_highResolvent_le ν R z hR hz

theorem transportedHighResolvent_sub_zero
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (R : ℝ) (z : ℂ)
    (hR : 0 < R) (hz : 0 ≤ z.re) :
    transportedHighResolvent U ν R z -
        transportedHighResolvent U ν R 0 =
      -(z • (transportedHighResolvent U ν R z *
        transportedHighResolvent U ν R 0)) := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  change e (highResolvent ν R z) - e (highResolvent ν R 0) =
    -(z • (e (highResolvent ν R z) * e (highResolvent ν R 0)))
  rw [← map_sub, highResolvent_sub_zero ν R z hR hz]
  simp only [map_neg, map_smul, map_mul]

set_option maxHeartbeats 800000 in
/-- Concrete high-mode heat estimate after inserting the physical
couplings. -/
theorem norm_coupled_high_heat_le
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ)
    (B C : Matrix ι ι ℂ) (b c R t : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hB : ‖B‖ ≤ b) (hC : ‖C‖ ≤ c) :
    ‖B * ImplicitEuler.finiteUnitarySpectralHeat U ν t *
        transportedHighProjection U ν R * C‖ ≤
      b * c * Real.exp (-(R * t)) := by
  have hscreen :=
    norm_finiteUnitarySpectralHeat_mul_highProjection_le U ν R t ht
  have hgeneric := hodge_feedback_tail.1
    (A := Matrix ι ι ℂ)
    (B := B)
    (S := ImplicitEuler.finiteUnitarySpectralHeat U ν t *
      transportedHighProjection U ν R)
    (C := C) b c R t hb hc hB hC hscreen
  simpa only [Matrix.mul_assoc] using hgeneric

set_option maxHeartbeats 800000 in
/-- Exact finite-dimensional Feshbach package: full response equals the
low response plus the zero-frequency high correction and a remainder linear
in `z`; both high terms have the manuscript's stated norm bounds. -/
theorem coupled_resolvent_feshbach
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ)
    (B C : Matrix ι ι ℂ) (b c R : ℝ) (z : ℂ)
    (hR : 0 < R) (hz : 0 ≤ z.re)
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hB : ‖B‖ ≤ b) (hC : ‖C‖ ≤ c) :
    let full := B * transportedSpectralResolvent U ν z * C
    let low := B * transportedLowResolvent U ν R z * C
    let correction := B * transportedHighResolvent U ν R 0 * C
    let error := -(B * (z •
      (transportedHighResolvent U ν R z *
        transportedHighResolvent U ν R 0)) * C)
    full = low + correction + error
      ∧ ‖correction‖ ≤ b * c / R
      ∧ ‖error‖ ≤ ‖z‖ * b * c / R ^ 2 := by
  dsimp only
  let Rz := transportedHighResolvent U ν R z
  let R0 := transportedHighResolvent U ν R 0
  have hsplit :
      transportedSpectralResolvent U ν z =
        transportedLowResolvent U ν R z + Rz :=
    transportedSpectralResolvent_eq_low_add_high U ν R z
  have hres : Rz - R0 = -(z • (Rz * R0)) := by
    exact transportedHighResolvent_sub_zero U ν R z hR hz
  have hRz_eq : Rz = R0 + -(z • (Rz * R0)) := by
    calc
      Rz = (Rz - R0) + R0 := by abel
      _ = -(z • (Rz * R0)) + R0 := by rw [hres]
      _ = R0 + -(z • (Rz * R0)) := by abel
  have hR0 : ‖R0‖ ≤ 1 / R := by
    exact norm_transportedHighResolvent_le U ν R 0 hR (by simp)
  have hRz : ‖Rz‖ ≤ 1 / R :=
    norm_transportedHighResolvent_le U ν R z hR hz
  have hRinv : 0 ≤ 1 / R := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit, hRz_eq]
    noncomm_ring
  · calc
      ‖B * R0 * C‖ ≤ ‖B‖ * ‖R0‖ * ‖C‖ := by
        calc
          _ ≤ ‖B * R0‖ * ‖C‖ := norm_mul_le _ _
          _ ≤ (‖B‖ * ‖R0‖) * ‖C‖ := by
            gcongr
            exact norm_mul_le _ _
      _ ≤ b * (1 / R) * c := by gcongr
      _ = b * c / R := by ring
  · change ‖-(B * (z • (Rz * R0)) * C)‖ ≤ _
    calc
      ‖-(B * (z • (Rz * R0)) * C)‖
          = ‖B * (z • (Rz * R0)) * C‖ := norm_neg _
      _ ≤ ‖B * (z • (Rz * R0))‖ * ‖C‖ := norm_mul_le _ _
      _ ≤ (‖B‖ * ‖z • (Rz * R0)‖) * ‖C‖ := by
            gcongr
            exact norm_mul_le _ _
      _ = (‖B‖ * (‖z‖ * ‖Rz * R0‖)) * ‖C‖ := by
            rw [norm_smul]
      _ ≤ ‖B‖ * (‖z‖ * (‖Rz‖ * ‖R0‖)) * ‖C‖ := by
            gcongr
            exact norm_mul_le _ _
      _ ≤ b * (‖z‖ * ((1 / R) * (1 / R))) * c := by gcongr
      _ = ‖z‖ * b * c / R ^ 2 := by field_simp

end HodgeFeedbackFiniteSpectralScreen
end NCG
