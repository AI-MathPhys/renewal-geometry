/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.FrameTransport
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected

/-!
# global frame transport assembly

The local whitening, leakage, polar, coframe, and affine identities are
`smst_frame_transport`.  Here they are completed by the three global readings
used in the manuscript: uniqueness of the positive polar link, gauge covariance
of arbitrary ordered path products, the principal curvature logarithm, and the
iterated affine translation formula.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option maxHeartbeats 800000

/-- The two matrix identities defining a unitary change of frame. -/
def IsUnitaryMatrix {k : Type*} [Fintype k] [DecidableEq k]
    (G : Matrix k k ℂ) : Prop :=
  G * Gᴴ = 1 ∧ Gᴴ * G = 1

/-- The unitary and positive factors in an invertible polar decomposition are
unique. -/
theorem polar_link_unique {k : Type*} [Fintype k] [DecidableEq k]
    (A U V P Q : Matrix k k ℂ)
    (hU : IsUnitaryMatrix U) (hV : IsUnitaryMatrix V)
    (hP : P.PosDef) (hQ : Q.PosDef)
    (hA : A = U * P) (hA' : A = V * Q) :
    U = V ∧ P = Q := by
  have hP2 : P * P = Aᴴ * A := by
    rw [hA, Matrix.conjTranspose_mul, hP.isHermitian]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U P, hU.2, Matrix.one_mul]
  have hQ2 : Q * Q = Aᴴ * A := by
    rw [hA', Matrix.conjTranspose_mul, hQ.isHermitian]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V Q, hV.2, Matrix.one_mul]
  have hsP : CFC.sqrt (Aᴴ * A) = P :=
    sqrt_unique' hP.posSemidef hP2
  have hsQ : CFC.sqrt (Aᴴ * A) = Q :=
    sqrt_unique' hQ.posSemidef hQ2
  have hPQ : P = Q := hsP.symm.trans hsQ
  haveI := hP.isUnit.invertible
  have hUV : U = V := by
    calc
      U = (U * P) * P⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
          Matrix.mul_one]
      _ = A * P⁻¹ := by rw [← hA]
      _ = (V * P) * P⁻¹ := by rw [hA', hPQ]
      _ = V := by
        rw [Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
          Matrix.mul_one]
  exact ⟨hUV, hPQ⟩

/-- An ordered path is stored as `(link, targetGauge)` pairs.  Products are
composed in traversal order, so the last edge acts on the left. -/
def frameLinkProduct {k : Type*} [Fintype k] [DecidableEq k] :
    List (Matrix k k ℂ × Matrix k k ℂ) → Matrix k k ℂ
  | [] => 1
  | (U, _) :: rest => frameLinkProduct rest * U

/-- Gauge at the terminal vertex of an encoded path. -/
def frameEndGauge {k : Type*} [Fintype k] [DecidableEq k]
    (G₀ : Matrix k k ℂ) :
    List (Matrix k k ℂ × Matrix k k ℂ) → Matrix k k ℂ
  | [] => G₀
  | (_, G₁) :: rest => frameEndGauge G₁ rest

/-- Ordered product after the edgewise gauge transformation
`U_(x→y) ↦ G_y U_(x→y) G_x*`. -/
def frameGaugeProduct {k : Type*} [Fintype k] [DecidableEq k]
    (G₀ : Matrix k k ℂ) :
    List (Matrix k k ℂ × Matrix k k ℂ) → Matrix k k ℂ
  | [] => 1
  | (U, G₁) :: rest =>
      frameGaugeProduct G₁ rest * (G₁ * U * G₀ᴴ)

/-- Arbitrary finite path products are endpoint-gauge covariant.  On a loop,
the two endpoint gauges agree and this is conjugation covariance of holonomy. -/
theorem frame_path_gauge_covariance {k : Type*} [Fintype k]
    [DecidableEq k] (G₀ : Matrix k k ℂ)
    (path : List (Matrix k k ℂ × Matrix k k ℂ))
    (hG₀ : IsUnitaryMatrix G₀)
    (hpath : ∀ q ∈ path, IsUnitaryMatrix q.2) :
    frameGaugeProduct G₀ path
      = frameEndGauge G₀ path * frameLinkProduct path * G₀ᴴ := by
  induction path generalizing G₀ with
  | nil =>
      simp [frameGaugeProduct, frameEndGauge, frameLinkProduct, hG₀.1]
  | cons q rest ih =>
      obtain ⟨U, G₁⟩ := q
      have hG₁ : IsUnitaryMatrix G₁ :=
        hpath (U, G₁) List.mem_cons_self
      have hrest : ∀ q ∈ rest, IsUnitaryMatrix q.2 := by
        intro q hq
        exact hpath q (List.mem_cons_of_mem _ hq)
      rw [frameGaugeProduct, frameEndGauge, frameLinkProduct,
        ih G₁ hG₁ hrest]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc G₁ᴴ G₁ (U * G₀ᴴ), hG₁.2,
        Matrix.one_mul]

/-- If `-1` is absent from the spectrum of a unitary loop holonomy, its
principal argument is a finite self-adjoint curvature whose exponential is the
holonomy. -/
theorem principal_frame_curvature {k : Type*} [Fintype k]
    [DecidableEq k] (u : unitary (CStarMatrix k k ℂ))
    (hminus : (-1 : ℂ) ∉ spectrum ℂ (u : CStarMatrix k k ℂ)) :
    ∃ K : selfAdjoint (CStarMatrix k k ℂ),
      selfAdjoint.expUnitary K = u := by
  refine ⟨Unitary.argSelfAdjoint u, ?_⟩
  apply expUnitary_argSelfAdjoint
  exact (Unitary.norm_sub_one_lt_two_iff u.2).2 hminus

/-- Real part of a complex three-frame link. -/
def realFramePart (U : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j => (U i j).re

/-- Vanishing real-structure residual, unitary transport, and vanishing
orientation residual put the finite connection in `SO(3)`. -/
theorem real_oriented_frame_link_mem_SO3
    (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hunit : Uᴴ * U = 1)
    (hreal : ∀ i j, (U i j).im = 0)
    (horient : (realFramePart U).det = 1) :
    realFramePart U ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).2 ?_, horient⟩
  ext i j
  have hij := congrArg Complex.re (congrFun (congrFun hunit i) j)
  by_cases hieq : i = j
  · simpa [realFramePart, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.transpose_apply, Complex.mul_re, hreal, Matrix.one_apply,
      hieq] using hij
  · simpa [realFramePart, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.transpose_apply, Complex.mul_re, hreal, Matrix.one_apply,
      hieq] using hij

/-- The affine matrix attached to a rotational link and a coframe translation. -/
def frameAffineMatrix {k : Type*} [Fintype k] [DecidableEq k]
    (L : Matrix k k ℂ × Matrix k Unit ℂ) :
    Matrix (k ⊕ Unit) (k ⊕ Unit) ℂ :=
  Matrix.fromBlocks L.1 L.2 0 1

/-- Rotation and accumulated translation of an ordered affine path. -/
def frameAffineProduct {k : Type*} [Fintype k] [DecidableEq k] :
    List (Matrix k k ℂ × Matrix k Unit ℂ) →
      Matrix k k ℂ × Matrix k Unit ℂ
  | [] => (1, 0)
  | (U, ξ) :: rest =>
      let total := frameAffineProduct rest
      (total.1 * U, total.1 * ξ + total.2)

/-- Ordered product of the homogeneous affine-link matrices. -/
def frameAffineMatrixProduct {k : Type*} [Fintype k] [DecidableEq k] :
    List (Matrix k k ℂ × Matrix k Unit ℂ) →
      Matrix (k ⊕ Unit) (k ⊕ Unit) ℂ
  | [] => 1
  | L :: rest => frameAffineMatrixProduct rest * frameAffineMatrix L

/-- The top-right block of every finite affine path product is exactly the
recursively accumulated Cartan translation.  For a protected face this is the
finite torsion/affine-closure residual in the manuscript. -/
theorem frame_affine_path_product {k : Type*} [Fintype k]
    [DecidableEq k]
    (path : List (Matrix k k ℂ × Matrix k Unit ℂ)) :
    frameAffineMatrixProduct path = frameAffineMatrix (frameAffineProduct path) := by
  induction path with
  | nil =>
      change (1 : Matrix (k ⊕ Unit) (k ⊕ Unit) ℂ) =
        Matrix.fromBlocks 1 0 0 1
      exact Matrix.fromBlocks_one.symm
  | cons L rest ih =>
      obtain ⟨U, ξ⟩ := L
      rw [frameAffineMatrixProduct, ih]
      simp [frameAffineProduct, frameAffineMatrix,
        Matrix.fromBlocks_multiply]

end NCG
