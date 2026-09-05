/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExteriorReflectionPositivityCriterionExact
import NCG.Grand.NaimarkPhaseSharpness

/-!
# One-particle Pythagoras and strict exterior cutoff transport

This file proves `thm:SMQG-cutoff-exterior` for finite one-particle spaces.
The cutoff residual splits orthogonally into leakage and compression mismatch,
giving the exact Hilbert--Schmidt Pythagoras identity.  Cauchy--Binet then
transports exact one-particle intertwining through every exterior grade, and
the converse is recovered from the literal grade-one block.
-/

open Matrix

namespace NCG
namespace OneParticlePythagorasExteriorTransport

open FiniteCompoundMatrixExteriorPower

variable {m n p : ℕ}

/-- Compression mismatch `jᴴ P_Y j - P_X`. -/
def compressionDefect (j : Matrix (Fin m) (Fin n) ℂ) (PX : Matrix (Fin n) (Fin n) ℂ)
    (PY : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  jᴴ * PY * j - PX

/-- Leakage out of the old one-particle range. -/
def leakageDefect (j : Matrix (Fin m) (Fin n) ℂ) (PY : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin n) ℂ :=
  (1 - j * jᴴ) * PY * j

/-- Full one-particle cutoff intertwining residual. -/
def transportDefect (j : Matrix (Fin m) (Fin n) ℂ) (PX : Matrix (Fin n) (Fin n) ℂ)
    (PY : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  PY * j - j * PX

/-- The full residual is the sum of its orthogonal leakage and in-range
compression components. -/
theorem transportDefect_decomposition (j : Matrix (Fin m) (Fin n) ℂ)
    (PX : Matrix (Fin n) (Fin n) ℂ) (PY : Matrix (Fin m) (Fin m) ℂ)
    (hj : jᴴ * j = 1) :
    transportDefect j PX PY =
      leakageDefect j PY + j * compressionDefect j PX PY := by
  simp only [transportDefect, leakageDefect, compressionDefect]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel_nf

/-- Compression is the range projection of the full residual. -/
theorem compressionDefect_eq_conjTranspose_mul_transportDefect
    (j : Matrix (Fin m) (Fin n) ℂ) (PX : Matrix (Fin n) (Fin n) ℂ)
    (PY : Matrix (Fin m) (Fin m) ℂ)
    (hj : jᴴ * j = 1) :
    compressionDefect j PX PY = jᴴ * transportDefect j PX PY := by
  simp only [compressionDefect, transportDefect]
  rw [Matrix.mul_sub, ← Matrix.mul_assoc jᴴ j PX, hj, Matrix.one_mul,
    Matrix.mul_assoc]

/-- Leakage is the orthogonal projection of the full residual. -/
theorem leakageDefect_eq_projection_mul_transportDefect
    (j : Matrix (Fin m) (Fin n) ℂ) (PX : Matrix (Fin n) (Fin n) ℂ)
    (PY : Matrix (Fin m) (Fin m) ℂ)
    (hj : jᴴ * j = 1) :
    leakageDefect j PY = (1 - j * jᴴ) * transportDefect j PX PY := by
  have hQj : (1 - j * jᴴ) * j = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
      hj, Matrix.mul_one, sub_self]
  simp only [leakageDefect, transportDefect, Matrix.mul_sub]
  rw [← Matrix.mul_assoc (1 - j * jᴴ) j PX, hQj, Matrix.zero_mul, sub_zero,
    Matrix.mul_assoc]

/-- **QG.69.** Exact Hilbert--Schmidt Pythagoras for the cutoff packet. -/
theorem transportDefect_hsPythagoras (j : Matrix (Fin m) (Fin n) ℂ)
    (PX : Matrix (Fin n) (Fin n) ℂ) (PY : Matrix (Fin m) (Fin m) ℂ)
    (hj : jᴴ * j = 1) :
    hsFrobSq (transportDefect j PX PY) =
      hsFrobSq (leakageDefect j PY) +
        hsFrobSq (compressionDefect j PX PY) := by
  let R := transportDefect j PX PY
  let Q : Matrix (Fin m) (Fin m) ℂ := 1 - j * jᴴ
  have hQH : Qᴴ = Q := by
    simp [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have hQ2 : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc jᴴ j jᴴ, hj, Matrix.one_mul]
    noncomm_ring
  have hC : compressionDefect j PX PY = jᴴ * R := by
    exact compressionDefect_eq_conjTranspose_mul_transportDefect j PX PY hj
  have hL : leakageDefect j PY = Q * R := by
    exact leakageDefect_eq_projection_mul_transportDefect j PX PY hj
  rw [hC, hL]
  change hsFrobSq R = hsFrobSq (Q * R) + hsFrobSq (jᴴ * R)
  rw [hsFrobSq_eq_re_trace, hsFrobSq_eq_re_trace,
    hsFrobSq_eq_re_trace]
  rw [← Complex.add_re, ← Matrix.trace_add]
  congr 2
  rw [Matrix.conjTranspose_mul, hQH, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Q Q R, hQ2]
  calc
    Rᴴ * R = Rᴴ * ((Q + j * jᴴ) * R) := by
      have hsum : Q + j * jᴴ = 1 := by simp [Q]
      rw [hsum, Matrix.one_mul]
    _ = Rᴴ * (Q * R) + Rᴴ * (j * (jᴴ * R)) := by
      rw [Matrix.add_mul, Matrix.mul_add]
      simp only [Matrix.mul_assoc]

/-- Vanishing of the full residual is equivalent to simultaneous vanishing of
leakage and compression mismatch. -/
theorem transportDefect_eq_zero_iff (j : Matrix (Fin m) (Fin n) ℂ)
    (PX : Matrix (Fin n) (Fin n) ℂ) (PY : Matrix (Fin m) (Fin m) ℂ)
    (hj : jᴴ * j = 1) :
    transportDefect j PX PY = 0 ↔
      leakageDefect j PY = 0 ∧ compressionDefect j PX PY = 0 := by
  constructor
  · intro hR
    constructor
    · rw [leakageDefect_eq_projection_mul_transportDefect j PX PY hj, hR,
        Matrix.mul_zero]
    · rw [compressionDefect_eq_conjTranspose_mul_transportDefect j PX PY hj,
        hR, Matrix.mul_zero]
  · rintro ⟨hL, hC⟩
    rw [transportDefect_decomposition j PX PY hj, hL, hC,
      Matrix.mul_zero, add_zero]

/-- Exact one-particle transport is functorially transported through every
exterior grade. -/
theorem exterior_transport (r : ℕ) (j : Matrix (Fin m) (Fin n) ℂ)
    (PX : Matrix (Fin n) (Fin n) ℂ) (PY : Matrix (Fin m) (Fin m) ℂ)
    (htransport : PY * j = j * PX) :
    cmpd r PY * cmpd r j = cmpd r j * cmpd r PX := by
  rw [← cmpd_mul, ← cmpd_mul, htransport]

/-- Compounds of cutoff maps compose strictly. -/
theorem exterior_cutoff_compose (r : ℕ) (j : Matrix (Fin m) (Fin n) ℂ)
    (k : Matrix (Fin p) (Fin m) ℂ) : cmpd r (k * j) = cmpd r k * cmpd r j :=
  cmpd_mul k j

/-- Grade one is literally the original rectangular matrix. -/
theorem cmpd_one_submatrix_rectangular (A : Matrix (Fin m) (Fin n) ℂ) :
    (cmpd 1 A).submatrix
      ExteriorReflectionPositivityCriterion.singletonGrade
      ExteriorReflectionPositivityCriterion.singletonGrade = A := by
  ext i j
  rw [Matrix.submatrix_apply, cmpd_apply, Matrix.det_fin_one]
  simp [ExteriorReflectionPositivityCriterion.singletonGrade, sel]

/-- If the full exterior packet includes grade one, exterior intertwining
implies exact one-particle intertwining. -/
theorem oneParticle_transport_of_gradeOne
    (j : Matrix (Fin m) (Fin n) ℂ) (PX : Matrix (Fin n) (Fin n) ℂ)
    (PY : Matrix (Fin m) (Fin m) ℂ)
    (hgrade : cmpd 1 PY * cmpd 1 j = cmpd 1 j * cmpd 1 PX) :
    PY * j = j * PX := by
  rw [← cmpd_mul, ← cmpd_mul] at hgrade
  have hsub := congrArg (fun M => M.submatrix
    ExteriorReflectionPositivityCriterion.singletonGrade
    ExteriorReflectionPositivityCriterion.singletonGrade) hgrade
  simpa only [cmpd_one_submatrix_rectangular] using hsub

/-- Consolidated exact cutoff exterior certificate. -/
theorem smqg_cutoff_exterior (j : Matrix (Fin m) (Fin n) ℂ)
    (PX : Matrix (Fin n) (Fin n) ℂ) (PY : Matrix (Fin m) (Fin m) ℂ)
    (hj : jᴴ * j = 1) :
    hsFrobSq (transportDefect j PX PY) =
        hsFrobSq (leakageDefect j PY) + hsFrobSq (compressionDefect j PX PY) ∧
      (transportDefect j PX PY = 0 ↔
        leakageDefect j PY = 0 ∧ compressionDefect j PX PY = 0) ∧
      (transportDefect j PX PY = 0 → ∀ r,
        cmpd r PY * cmpd r j = cmpd r j * cmpd r PX) := by
  refine ⟨transportDefect_hsPythagoras j PX PY hj,
    transportDefect_eq_zero_iff j PX PY hj, ?_⟩
  intro hR r
  exact exterior_transport r j PX PY (sub_eq_zero.mp hR)

end OneParticlePythagorasExteriorTransport
end NCG
