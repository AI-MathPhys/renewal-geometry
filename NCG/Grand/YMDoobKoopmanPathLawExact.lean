/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.YMDoobKoopman
import NCG.Grand.ReflectedEndpointGroundStateTransformExact

/-!
# Finite stationary path law for the vacuum Doob transform

This file adds the probabilistic layer missing from `YMDoobKoopman`: a
two-sided stationary cylinder law on every finite interval, with exact left
and right Kolmogorov consistency, and all `n`-step stationary correlations.
-/

open Finset Matrix

noncomputable section

namespace NCG.YMDoobKoopman

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Matrix-typed form of the ground-state transform, used to select matrix
powers rather than pointwise powers of the underlying function. -/
def doobMatrix (T : Matrix X X ℝ) (Omega : X → ℝ) : Matrix X X ℝ :=
  NCG.ReflectedEndpointGroundState.groundStateTransform T Omega

/-- Transition weight of a tail, conditional on its preceding state. -/
def transitionWeight (P : X → X → ℝ) : X → List X → ℝ
  | _, [] => 1
  | x, y :: ys => P x y * transitionWeight P y ys

/-- Stationary cylinder weight of a finite consecutive path. -/
def pathWeight (mu : X → ℝ) (P : X → X → ℝ) : List X → ℝ
  | [] => 1
  | x :: xs => mu x * transitionWeight P x xs

theorem transitionWeight_nonnegative (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) :
    ∀ x xs, 0 ≤ transitionWeight P x xs := by
  intro x xs
  induction xs generalizing x with
  | nil => simp [transitionWeight]
  | cons y ys ih =>
      exact mul_nonneg (hP x y) (ih y)

theorem transitionWeight_append_sum (P : X → X → ℝ)
    (hrow : ∀ x, ∑ y, P x y = 1) :
    ∀ x xs, ∑ y, transitionWeight P x (xs ++ [y]) =
      transitionWeight P x xs := by
  intro x xs
  induction xs generalizing x with
  | nil => simpa [transitionWeight] using hrow x
  | cons z zs ih =>
      simp only [List.cons_append, transitionWeight, ← Finset.mul_sum]
      rw [ih z]

theorem pathWeight_append_sum (mu : X → ℝ) (P : X → X → ℝ)
    (hrow : ∀ x, ∑ y, P x y = 1) :
    ∀ xs, xs ≠ [] →
      ∑ y, pathWeight mu P (xs ++ [y]) = pathWeight mu P xs := by
  intro xs hxs
  obtain ⟨x, tail, rfl⟩ := List.exists_cons_of_ne_nil hxs
  simp only [List.cons_append, pathWeight, ← Finset.mul_sum]
  rw [transitionWeight_append_sum P hrow]

/-- Detailed balance and the Markov row sum imply stationarity of `mu`. -/
theorem stationary_of_reversible (mu : X → ℝ) (P : X → X → ℝ)
    (hrev : ∀ x y, mu x * P x y = mu y * P y x)
    (hrow : ∀ x, ∑ y, P x y = 1) :
    ∀ y, ∑ x, mu x * P x y = mu y := by
  intro y
  calc
    ∑ x, mu x * P x y = ∑ x, mu y * P y x :=
      Finset.sum_congr rfl fun x _ => hrev x y
    _ = mu y * ∑ x, P y x := by rw [Finset.mul_sum]
    _ = mu y := by rw [hrow y, mul_one]

theorem pathWeight_prepend_sum (mu : X → ℝ) (P : X → X → ℝ)
    (hnorm : ∑ x, mu x = 1)
    (hstationary : ∀ y, ∑ x, mu x * P x y = mu y) :
    ∀ xs, ∑ x, pathWeight mu P (x :: xs) = pathWeight mu P xs := by
  intro xs
  cases xs with
  | nil => simpa [pathWeight, transitionWeight] using hnorm
  | cons y ys =>
      simp only [pathWeight, transitionWeight]
      rw [show (∑ x, mu x * (P x y * transitionWeight P y ys)) =
          (∑ x, mu x * P x y) * transitionWeight P y ys by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring]
      rw [hstationary y]

/-- A genuine two-sided stationary cylinder law: its finite-interval weights
are nonnegative, normalized on one site, and consistent under deleting either
endpoint. -/
structure TwoSidedCylinderLaw (mu : X → ℝ) (P : X → X → ℝ) where
  weight : List X → ℝ
  weight_eq : weight = pathWeight mu P
  nonnegative : ∀ xs, 0 ≤ weight xs
  empty : weight [] = 1
  singleton_normalized : ∑ x, weight [x] = 1
  extend_right : ∀ xs, xs ≠ [] →
    ∑ y, weight (xs ++ [y]) = weight xs
  extend_left : ∀ xs, ∑ x, weight (x :: xs) = weight xs

theorem twoSidedCylinderLaw_exists (mu : X → ℝ) (P : X → X → ℝ)
    (hmu : ∀ x, 0 ≤ mu x) (hnorm : ∑ x, mu x = 1)
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, mu x * P x y = mu y * P y x) :
    Nonempty (TwoSidedCylinderLaw mu P) := by
  have hstat := stationary_of_reversible mu P hrev hrow
  refine ⟨{
    weight := pathWeight mu P
    weight_eq := rfl
    nonnegative := ?_
    empty := rfl
    singleton_normalized := ?_
    extend_right := pathWeight_append_sum mu P hrow
    extend_left := pathWeight_prepend_sum mu P hnorm hstat }⟩
  · intro xs
    cases xs with
    | nil => simp [pathWeight]
    | cons x tail =>
        exact mul_nonneg (hmu x) (transitionWeight_nonnegative P hP x tail)
  · simpa [pathWeight, transitionWeight] using hnorm

/-- The `n`-step stationary path correlation. -/
def stationaryCorrelation (mu : X → ℝ) (P : Matrix X X ℝ)
    (n : ℕ) (f g : X → ℂ) : ℂ :=
  ∑ x, (mu x : ℂ) * star (f x) *
    (∑ y, ((P ^ n) x y : ℂ) * g y)

/-- Full `n`-step Koopman-compression identity in matrix/cylinder form. -/
theorem weightedInner_power_eq_stationaryCorrelation
    (Omega : X → ℝ) (P : Matrix X X ℝ) (n : ℕ) (f g : X → ℂ) :
    NCG.ReflectedEndpointGroundState.weightedInner Omega f
        (NCG.ReflectedEndpointGroundState.applyRealMatrix (P ^ n) g) =
      stationaryCorrelation
        (NCG.ReflectedEndpointGroundState.groundWeight Omega) P n f g := by
  rfl

/-- **Vacuum Doob transfer as a Koopman compression, complete finite form.**
The ground-state transform is a reversible Markov contraction, its stationary
two-sided cylinder law exists, and all time-separated correlations are exactly
the powers of the Doob transfer. -/
theorem ym_doob_koopman_path_law
    {iota : Type*}
    (T : Matrix X X ℝ) (Omega : X → ℝ) (F : iota → X → ℂ)
    (hT : ∀ x y, 0 ≤ T x y)
    (hOmega : ∀ x, 0 < Omega x)
    (hNorm : ∑ x, NCG.ReflectedEndpointGroundState.groundWeight Omega x = 1)
    (hSymm : ∀ x y, T x y = T y x)
    (hGround : ∀ x, ∑ y, T x y * Omega y = Omega x)
    (hLower : ∀ z : X → ℂ,
      0 ≤ (NCG.ReflectedEndpointGroundState.physicalInner z
        (NCG.ReflectedEndpointGroundState.applyRealMatrix T z)).re)
    (hUpper : ∀ z : X → ℂ,
      (NCG.ReflectedEndpointGroundState.physicalInner z
        (NCG.ReflectedEndpointGroundState.applyRealMatrix T z)).re ≤
      (NCG.ReflectedEndpointGroundState.physicalInner z z).re) :
    Nonempty (NCG.ReflectedEndpointGroundState.Certificate T Omega F) ∧
    Nonempty (TwoSidedCylinderLaw
      (NCG.ReflectedEndpointGroundState.groundWeight Omega)
      (doobMatrix T Omega)) ∧
    (∀ n f g,
      NCG.ReflectedEndpointGroundState.weightedInner Omega f
        (NCG.ReflectedEndpointGroundState.applyRealMatrix
          ((doobMatrix T Omega) ^ n) g) =
      stationaryCorrelation
        (NCG.ReflectedEndpointGroundState.groundWeight Omega)
        (doobMatrix T Omega) n f g) := by
  let P : Matrix X X ℝ := doobMatrix T Omega
  let mu := NCG.ReflectedEndpointGroundState.groundWeight Omega
  have hcert := NCG.ReflectedEndpointGroundState.reflected_endpoint_action_identity
    T Omega F hT hOmega hSymm hGround hLower hUpper
  have hP0 := NCG.ReflectedEndpointGroundState.groundStateTransform_nonnegative
    T Omega hT hOmega
  have hP1 := NCG.ReflectedEndpointGroundState.groundStateTransform_row_sum
    T Omega hOmega hGround
  have hrev := NCG.ReflectedEndpointGroundState.groundStateTransform_reversible
    T Omega hOmega hSymm
  exact ⟨hcert, twoSidedCylinderLaw_exists mu P
    (fun x => sq_nonneg (Omega x)) hNorm hP0 hP1 hrev,
    fun n f g => weightedInner_power_eq_stationaryCorrelation Omega P n f g⟩

end NCG.YMDoobKoopman
