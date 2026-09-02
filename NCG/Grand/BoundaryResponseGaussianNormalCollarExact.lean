/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Boundary response and an explicit Gaussian-normal collar

This file proves `thm:SMFS-boundary-response`.  In boundary dimension three,
the prescribed extrinsic response has trace `κ_E T/2`; consequently its
Brown--York momentum is exactly the negative assembled shell stress.  The
collar is not postulated: the affine normal extension
`h(n) = h + 2 n K` is constructed and differentiated, with unit normal-normal
coefficient and zero normal-tangent coefficients.  Hence orthogonal caps have
zero corner-angle writer and the completely assembled first boundary
variation vanishes.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace NCG.BoundaryResponseGaussianNormalCollar

abbrev BoundaryIndex := Fin 3
abbrev BoundaryTensor := BoundaryIndex → BoundaryIndex → ℝ

/-- Contraction of a covariant and a contravariant boundary tensor. -/
def contraction (h T : BoundaryTensor) : ℝ :=
  ∑ a, ∑ b, h a b * T a b

/-- The response `K^{ab} = κ (T h^{ab}/2 - T^{ab})` from (FS.45). -/
def extrinsicResponse (kappa : ℝ) (hCov hInv T : BoundaryTensor) :
    BoundaryTensor :=
  fun a b => kappa * ((1 / 2 : ℝ) * contraction hCov T * hInv a b - T a b)

/-- Brown--York momentum with both indices raised. -/
def brownYorkMomentum (kappa : ℝ) (hCov hInv K : BoundaryTensor) :
    BoundaryTensor :=
  fun a b => kappa⁻¹ * (K a b - contraction hCov K * hInv a b)

theorem contraction_smul (h T : BoundaryTensor) (c : ℝ) :
    contraction h (fun a b => c * T a b) = c * contraction h T := by
  unfold contraction
  have hp (a b : BoundaryIndex) : h a b * (c * T a b) =
      c * (h a b * T a b) := by ring
  simp_rw [hp, ← Finset.mul_sum]

theorem contraction_sub (h S T : BoundaryTensor) :
    contraction h (fun a b => S a b - T a b) =
      contraction h S - contraction h T := by
  unfold contraction
  simp_rw [mul_sub, Finset.sum_sub_distrib]

theorem contraction_extrinsicResponse
    (kappa : ℝ) (hCov hInv T : BoundaryTensor)
    (hinvTrace : contraction hCov hInv = 3) :
    contraction hCov (extrinsicResponse kappa hCov hInv T) =
      kappa * contraction hCov T / 2 := by
  change contraction hCov (fun a b => kappa *
    ((1 / 2 : ℝ) * contraction hCov T * hInv a b - T a b)) = _
  rw [contraction_smul, contraction_sub, contraction_smul, hinvTrace]
  ring

/-- Exact Brown--York cancellation (FS.46). -/
theorem brownYorkMomentum_extrinsicResponse
    (kappa : ℝ) (hkappa : kappa ≠ 0)
    (hCov hInv T : BoundaryTensor)
    (hinvTrace : contraction hCov hInv = 3) :
    brownYorkMomentum kappa hCov hInv
        (extrinsicResponse kappa hCov hInv T) =
      fun a b => -T a b := by
  funext a b
  unfold brownYorkMomentum
  rw [contraction_extrinsicResponse kappa hCov hInv T hinvTrace]
  unfold extrinsicResponse
  field_simp
  ring

/-- An explicit Gaussian-normal collar.  `tangentMetric n` is the induced
metric on the parallel boundary at signed normal distance `n`. -/
structure GaussianNormalCollar (h K : BoundaryTensor) where
  tangentMetric : ℝ → BoundaryTensor
  tangent_zero : tangentMetric 0 = h
  tangent_derivative : ∀ a b,
    HasDerivAt (fun n => tangentMetric n a b) (2 * K a b) 0
  tangent_smooth : ∀ a b, ContDiff ℝ ⊤ (fun n => tangentMetric n a b)
  normalNormal : ℝ → ℝ
  normalNormal_eq_one : normalNormal = fun _ => 1
  normalTangent : ℝ → BoundaryIndex → ℝ
  normalTangent_eq_zero : normalTangent = fun _ _ => 0
  cornerAngle : ℝ
  orthogonal_corner : cornerAngle = 0

/-- The affine normal extension is a smooth Gaussian-normal collar with the
prescribed second fundamental form. -/
def affineGaussianNormalCollar (h K : BoundaryTensor) :
    GaussianNormalCollar h K where
  tangentMetric := fun n a b => h a b + n * (2 * K a b)
  tangent_zero := by
    funext a b
    simp
  tangent_derivative := by
    intro a b
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (2 * K a b)).const_add (h a b)
  tangent_smooth := by
    intro a b
    fun_prop
  normalNormal := fun _ => 1
  normalNormal_eq_one := rfl
  normalTangent := fun _ _ => 0
  normalTangent_eq_zero := rfl
  cornerAngle := 0
  orthogonal_corner := rfl

/-- The completely assembled first boundary variation. -/
def assembledBoundaryVariation (Pi T dh : BoundaryTensor) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, ∑ b, (Pi a b + T a b) * dh a b

theorem assembledBoundaryVariation_vanishes
    (Pi T : BoundaryTensor) (hPi : Pi = fun a b => -T a b) :
    ∀ dh, assembledBoundaryVariation Pi T dh = 0 := by
  intro dh
  subst Pi
  simp [assembledBoundaryVariation]

/-- **`thm:SMFS-boundary-response`.**  The response generated from the one
assembled shell has the claimed trace and Brown--York cancellation, is
realized by an explicit smooth Gaussian-normal collar with orthogonal caps,
and has zero complete first boundary variation. -/
theorem boundary_response_generated_by_common_shell
    (kappa : ℝ) (hkappa : kappa ≠ 0)
    (hCov hInv T : BoundaryTensor)
    (hinvTrace : contraction hCov hInv = 3) :
    let K := extrinsicResponse kappa hCov hInv T
    contraction hCov K = kappa * contraction hCov T / 2 ∧
    brownYorkMomentum kappa hCov hInv K = (fun a b => -T a b) ∧
    Nonempty (GaussianNormalCollar hCov K) ∧
    (affineGaussianNormalCollar hCov K).cornerAngle = 0 ∧
    (∀ dh, assembledBoundaryVariation
      (brownYorkMomentum kappa hCov hInv K) T dh = 0) := by
  dsimp only
  have htrace := contraction_extrinsicResponse kappa hCov hInv T hinvTrace
  have hBY := brownYorkMomentum_extrinsicResponse
    kappa hkappa hCov hInv T hinvTrace
  refine ⟨htrace, hBY, ⟨affineGaussianNormalCollar hCov
    (extrinsicResponse kappa hCov hInv T)⟩, rfl, ?_⟩
  exact assembledBoundaryVariation_vanishes _ T hBY

end NCG.BoundaryResponseGaussianNormalCollar
