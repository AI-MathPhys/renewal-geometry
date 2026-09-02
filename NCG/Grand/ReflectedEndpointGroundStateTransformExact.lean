/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ReflectedEndpointActionExact

/-!
# Ground-state transform for the reflected endpoint action

This file supplies the representation-theoretic layer of
`thm:GT-reflected-endpoint-action`.  On a finite configuration space it
constructs the Doob/ground-state transform of a ℝ positivity-preserving
self-adjoint transfer, proves the Markov and detailed-balance identities,
transports the lower and upper quadratic-form bounds through the weighted
unitary, and identifies the mean conditional writer with the physical
transfer Dirichlet action.
-/

open Finset Matrix

namespace NCG
namespace ReflectedEndpointGroundState

noncomputable section

variable {X iota : Type*} [Fintype X]

/-- Multiplication by the strictly positive ground state. -/
def groundLift (Omega : X → ℝ) (f : X → ℂ) (x : X) : ℂ :=
  Omega x * f x

/-- The probability weight transported from counting measure. -/
def groundWeight (Omega : X → ℝ) (x : X) : ℝ := Omega x ^ 2

/-- A ℝ matrix acting on ℂ-valued functions. -/
def applyRealMatrix (T : Matrix X X ℝ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ y, (T x y : ℂ) * f y

/-- The finite ground-state/Doob transform `P = U_Omega⁻¹ T U_Omega`. -/
def groundStateTransform (T : Matrix X X ℝ) (Omega : X → ℝ) :
    X → X → ℝ :=
  fun x y => T x y * Omega y / Omega x

/-- The weighted `L²(mu)` inner product, linear in its second argument. -/
def weightedInner (Omega : X → ℝ) (f g : X → ℂ) : ℂ :=
  ∑ x, (groundWeight Omega x : ℂ) * star (f x) * g x

/-- The physical counting-space inner product. -/
def physicalInner (f g : X → ℂ) : ℂ :=
  ∑ x, star (f x) * g x

/-- Entrywise transfer Dirichlet action of the physical writer bank. -/
def transferDirichletAction (T : Matrix X X ℝ) (Omega : X → ℝ)
    (F : iota → X → ℂ) (a b : iota) : ℂ :=
  physicalInner (groundLift Omega (F a))
    (fun x => groundLift Omega (F b) x -
      applyRealMatrix T (groundLift Omega (F b)) x)

theorem groundStateTransform_nonnegative
    (T : Matrix X X ℝ) (Omega : X → ℝ)
    (hT : ∀ x y, 0 ≤ T x y) (hOmega : ∀ x, 0 < Omega x) :
    ∀ x y, 0 ≤ groundStateTransform T Omega x y := by
  intro x y
  exact div_nonneg (mul_nonneg (hT x y) (hOmega y).le) (hOmega x).le

theorem groundStateTransform_row_sum
    (T : Matrix X X ℝ) (Omega : X → ℝ)
    (hOmega : ∀ x, 0 < Omega x)
    (hGround : ∀ x, ∑ y, T x y * Omega y = Omega x) :
    ∀ x, ∑ y, groundStateTransform T Omega x y = 1 := by
  intro x
  unfold groundStateTransform
  rw [← Finset.sum_div, hGround x]
  exact div_self (ne_of_gt (hOmega x))

theorem groundStateTransform_reversible
    (T : Matrix X X ℝ) (Omega : X → ℝ)
    (hOmega : ∀ x, 0 < Omega x)
    (hSymm : ∀ x y, T x y = T y x) :
    ∀ x y,
      groundWeight Omega x * groundStateTransform T Omega x y =
      groundWeight Omega y * groundStateTransform T Omega y x := by
  intro x y
  unfold groundWeight groundStateTransform
  rw [hSymm x y]
  field_simp [ne_of_gt (hOmega x), ne_of_gt (hOmega y)]

theorem groundLift_transform
    (T : Matrix X X ℝ) (Omega : X → ℝ) (hOmega : ∀ x, 0 < Omega x)
    (f : X → ℂ) (x : X) :
    groundLift Omega
        (applyRealMatrix (groundStateTransform T Omega) f) x =
      applyRealMatrix T (groundLift Omega f) x := by
  unfold groundLift applyRealMatrix groundStateTransform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  push_cast
  field_simp [ne_of_gt (hOmega x)]

theorem weightedInner_groundLift
    (Omega : X → ℝ) (f g : X → ℂ) :
    weightedInner Omega f g =
      physicalInner (groundLift Omega f) (groundLift Omega g) := by
  unfold weightedInner physicalInner groundWeight groundLift
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [star_mul', Complex.star_def,
    Complex.conj_ofReal]
  push_cast
  ring

theorem weightedInner_transform
    (T : Matrix X X ℝ) (Omega : X → ℝ) (hOmega : ∀ x, 0 < Omega x)
    (f g : X → ℂ) :
    weightedInner Omega f
        (applyRealMatrix (groundStateTransform T Omega) g) =
      physicalInner (groundLift Omega f)
        (applyRealMatrix T (groundLift Omega g)) := by
  rw [weightedInner_groundLift]
  congr 1
  funext x
  exact groundLift_transform T Omega hOmega g x

theorem physicalInner_apply_selfAdjoint
    (T : Matrix X X ℝ) (hSymm : ∀ x y, T x y = T y x)
    (f g : X → ℂ) :
    physicalInner f (applyRealMatrix T g) =
      physicalInner (applyRealMatrix T f) g := by
  unfold physicalInner applyRealMatrix
  calc
    (∑ x, star (f x) * ∑ y, (T x y : ℂ) * g y) =
        ∑ x, ∑ y, star (f x) * ((T x y : ℂ) * g y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ y, ∑ x, star (f x) * ((T x y : ℂ) * g y) :=
      Finset.sum_comm
    _ = ∑ y, ∑ x, star ((T y x : ℂ) * f x) * g y := by
      refine Finset.sum_congr rfl fun y _ => ?_
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← hSymm x y]
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
      ring
    _ = ∑ y, star (∑ x, (T y x : ℂ) * f x) * g y := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [star_sum, Finset.sum_mul]

theorem weightedInner_transform_selfAdjoint
    (T : Matrix X X ℝ) (Omega : X → ℝ)
    (hOmega : ∀ x, 0 < Omega x)
    (hSymm : ∀ x y, T x y = T y x) (f g : X → ℂ) :
    weightedInner Omega f
        (applyRealMatrix (groundStateTransform T Omega) g) =
      weightedInner Omega
        (applyRealMatrix (groundStateTransform T Omega) f) g := by
  rw [weightedInner_transform T Omega hOmega,
    physicalInner_apply_selfAdjoint T hSymm]
  symm
  rw [weightedInner_groundLift]
  congr 1
  funext x
  exact groundLift_transform T Omega hOmega f x

theorem weighted_quadratic_bounds
    (T : Matrix X X ℝ) (Omega : X → ℝ)
    (hOmega : ∀ x, 0 < Omega x)
    (hLower : ∀ z : X → ℂ,
      0 ≤ (physicalInner z (applyRealMatrix T z)).re)
    (hUpper : ∀ z : X → ℂ,
      (physicalInner z (applyRealMatrix T z)).re ≤
        (physicalInner z z).re)
    (f : X → ℂ) :
    0 ≤ (weightedInner Omega f
        (applyRealMatrix (groundStateTransform T Omega) f)).re ∧
      (weightedInner Omega f
        (applyRealMatrix (groundStateTransform T Omega) f)).re ≤
        (weightedInner Omega f f).re := by
  rw [weightedInner_transform T Omega hOmega,
    weightedInner_groundLift]
  exact ⟨hLower _, hUpper _⟩

/-- Ground-state conjugation identifies the weighted Dirichlet form with the
physical transfer action `Y_F* (I-T) Y_F`, entrywise. -/
theorem dirichletForm_eq_transferDirichletAction
    (T : Matrix X X ℝ) (Omega : X → ℝ)
    (hOmega : ∀ x, 0 < Omega x)
    (F : iota → X → ℂ) (a b : iota) :
    ReflectedEndpointAction.dirichletForm
        (groundWeight Omega) (groundStateTransform T Omega) (F a) (F b) =
      transferDirichletAction T Omega F a b := by
  change weightedInner Omega (F a)
      (fun x => F b x -
        applyRealMatrix (groundStateTransform T Omega) (F b) x) =
    physicalInner (groundLift Omega (F a))
      (fun x => groundLift Omega (F b) x -
        applyRealMatrix T (groundLift Omega (F b)) x)
  rw [weightedInner_groundLift]
  congr 1
  funext x
  unfold groundLift
  rw [mul_sub]
  change (Omega x : ℂ) * F b x -
      groundLift Omega
        (applyRealMatrix (groundStateTransform T Omega) (F b)) x =
    (Omega x : ℂ) * F b x -
      applyRealMatrix T (groundLift Omega (F b)) x
  rw [groundLift_transform T Omega hOmega]

/-- Exact finite certificate for (AR.1)--(AR.7), including the previously
missing weighted-space conjugation. -/
structure Certificate (T : Matrix X X ℝ) (Omega : X → ℝ)
    (F : iota → X → ℂ) where
  kernelNonnegative :
    ∀ x y, 0 ≤ groundStateTransform T Omega x y
  markov :
    ∀ x, ∑ y, groundStateTransform T Omega x y = 1
  reversible :
    ∀ x y,
      groundWeight Omega x * groundStateTransform T Omega x y =
      groundWeight Omega y * groundStateTransform T Omega y x
  selfAdjoint :
    ∀ f g : X → ℂ,
      weightedInner Omega f
          (applyRealMatrix (groundStateTransform T Omega) g) =
        weightedInner Omega
          (applyRealMatrix (groundStateTransform T Omega) f) g
  positiveContraction :
    ∀ f : X → ℂ,
      0 ≤ (weightedInner Omega f
          (applyRealMatrix (groundStateTransform T Omega) f)).re ∧
        (weightedInner Omega f
          (applyRealMatrix (groundStateTransform T Omega) f)).re ≤
          (weightedInner Omega f f).re
  entranceConditional :
    ∀ x, groundWeight Omega x ≠ 0 →
      ReflectedEndpointAction.condExpFirst
          (groundWeight Omega) (groundStateTransform T Omega)
          (ReflectedEndpointAction.pairAction F) x =
        ReflectedEndpointAction.entranceWriter
          (groundStateTransform T Omega) F x
  exitConditional :
    ∀ x, groundWeight Omega x ≠ 0 →
      ReflectedEndpointAction.condExpSecond
          (groundWeight Omega) (groundStateTransform T Omega)
          (ReflectedEndpointAction.pairAction F) x =
        ReflectedEndpointAction.entranceWriter
          (groundStateTransform T Omega) F x
  meanAction :
    ∀ a b,
      (∑ x, (groundWeight Omega x : ℂ) •
        ReflectedEndpointAction.entranceWriter
          (groundStateTransform T Omega) F x) a b =
        transferDirichletAction T Omega F a b

theorem reflected_endpoint_action_identity
    (T : Matrix X X ℝ) (Omega : X → ℝ) (F : iota → X → ℂ)
    (hT : ∀ x y, 0 ≤ T x y)
    (hOmega : ∀ x, 0 < Omega x)
    (hSymm : ∀ x y, T x y = T y x)
    (hGround : ∀ x, ∑ y, T x y * Omega y = Omega x)
    (hLower : ∀ z : X → ℂ,
      0 ≤ (physicalInner z (applyRealMatrix T z)).re)
    (hUpper : ∀ z : X → ℂ,
      (physicalInner z (applyRealMatrix T z)).re ≤
        (physicalInner z z).re) :
    Nonempty (Certificate T Omega F) := by
  let P := groundStateTransform T Omega
  let mu := groundWeight Omega
  have hP0 : ∀ x y, 0 ≤ P x y :=
    groundStateTransform_nonnegative T Omega hT hOmega
  have hP1 : ∀ x, ∑ y, P x y = 1 :=
    groundStateTransform_row_sum T Omega hOmega hGround
  have hRev : ∀ x y, mu x * P x y = mu y * P y x :=
    groundStateTransform_reversible T Omega hOmega hSymm
  refine ⟨{
    kernelNonnegative := hP0
    markov := hP1
    reversible := hRev
    selfAdjoint := weightedInner_transform_selfAdjoint T Omega hOmega hSymm
    positiveContraction :=
      weighted_quadratic_bounds T Omega hOmega hLower hUpper
    entranceConditional := fun x hx =>
      ReflectedEndpointAction.condExp_entrance mu P hP1 F x hx
    exitConditional := fun x hx =>
      ReflectedEndpointAction.condExp_exit mu P hP1 hRev F x hx
    meanAction := fun a b =>
      (ReflectedEndpointAction.mean_entranceWriter mu P hP1 hRev F a b).trans
        (dirichletForm_eq_transferDirichletAction T Omega hOmega F a b)
  }⟩

end
end ReflectedEndpointGroundState
end NCG
