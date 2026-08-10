/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Incidence-before-interference firewall

A self-contained finite network-closure theorem for two complementary typed
supports.  Adjoint closure of the primitive coefficient family upgrades the
displayed one-sided primitive incidence condition to a two-sided block
diagonal invariant.  The invariant then survives every finite network
operation and norm limit.
-/

open Matrix Finset
open scoped ComplexOrder

namespace NCG
namespace IncidenceBeforeInterferenceFirewall

/-- Both grading-changing blocks vanish. -/
def RespectsTypedSupports
    {d : Type*} [Fintype d]
    (Pleft Pright X : Matrix d d ℂ) : Prop :=
  Pleft * X * Pright = 0 ∧ Pright * X * Pleft = 0

/-- The network coefficients generated from a primitive family.  Finite
ancillary matrix coefficients cover environment measurement and
postselection; sums and products cover coherent order control. -/
inductive NetworkCoefficient
    {d : Type*} [Fintype d] [DecidableEq d]
    (primitive : Set (Matrix d d ℂ)) : Matrix d d ℂ → Prop
  | primitive {X} : X ∈ primitive → NetworkCoefficient primitive X
  | zero : NetworkCoefficient primitive 0
  | identity : NetworkCoefficient primitive 1
  | add {X Y} : NetworkCoefficient primitive X →
      NetworkCoefficient primitive Y → NetworkCoefficient primitive (X + Y)
  | mul {X Y} : NetworkCoefficient primitive X →
      NetworkCoefficient primitive Y → NetworkCoefficient primitive (X * Y)
  | adjoint {X} : NetworkCoefficient primitive X →
      NetworkCoefficient primitive Xᴴ
  | scale (a : ℂ) {X} : NetworkCoefficient primitive X →
      NetworkCoefficient primitive (a • X)
  | ancillaryCoefficient {ι : Type*} [Fintype ι]
      (a : ι → ℂ) (X : ι → Matrix d d ℂ) :
      (∀ i, NetworkCoefficient primitive (X i)) →
      NetworkCoefficient primitive (∑ i, a i • X i)
  | normLimit (X : ℕ → Matrix d d ℂ) (Y : Matrix d d ℂ) :
      (∀ n, NetworkCoefficient primitive (X n)) →
      Filter.Tendsto X Filter.atTop (nhds Y) →
      NetworkCoefficient primitive Y

/-- A one-sided primitive incidence condition is automatically two-sided
when the primitive family is closed under adjoints. -/
theorem primitive_respects_both_supports
    {d : Type*} [Fintype d] [DecidableEq d]
    (Pleft Pright : Matrix d d ℂ)
    (hleft : Pleftᴴ = Pleft) (hright : Prightᴴ = Pright)
    (primitive : Set (Matrix d d ℂ))
    (hstar : ∀ ⦃X⦄, X ∈ primitive → Xᴴ ∈ primitive)
    (hprimitive : ∀ ⦃X⦄, X ∈ primitive → Pleft * X * Pright = 0)
    {X : Matrix d d ℂ} (hX : X ∈ primitive) :
    RespectsTypedSupports Pleft Pright X := by
  constructor
  · exact hprimitive hX
  · have hadj : Pleft * Xᴴ * Pright = 0 := hprimitive (hstar hX)
    have h := congrArg star hadj
    simpa [star_eq_conjTranspose, Matrix.conjTranspose_mul, hleft, hright,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using h

/-- Main firewall theorem: every generated finite coefficient and every norm
limit remains block diagonal for the typed support decomposition. -/
theorem networkCoefficient_respects_typed_supports
    {d : Type*} [Fintype d] [DecidableEq d]
    (Pleft Pright : Matrix d d ℂ)
    (hleft : Pleftᴴ = Pleft) (hright : Prightᴴ = Pright)
    (hcomplement : Pleft + Pright = 1)
    (horthLR : Pleft * Pright = 0)
    (horthRL : Pright * Pleft = 0)
    (primitive : Set (Matrix d d ℂ))
    (hstar : ∀ ⦃X⦄, X ∈ primitive → Xᴴ ∈ primitive)
    (hprimitive : ∀ ⦃X⦄, X ∈ primitive → Pleft * X * Pright = 0)
    {X : Matrix d d ℂ} (hX : NetworkCoefficient primitive X) :
    RespectsTypedSupports Pleft Pright X := by
  induction hX with
  | primitive hmem =>
      exact primitive_respects_both_supports Pleft Pright hleft hright
        primitive hstar hprimitive hmem
  | zero => simp [RespectsTypedSupports]
  | identity => simp [RespectsTypedSupports, horthLR, horthRL]
  | add hA hB ihA ihB =>
      constructor
      · simp [Matrix.mul_add, Matrix.add_mul, ihA.1, ihB.1]
      · simp [Matrix.mul_add, Matrix.add_mul, ihA.2, ihB.2]
  | mul hA hB ihA ihB =>
      rename_i A B
      constructor
      · calc
          Pleft * (A * B) * Pright =
              Pleft * A * (Pleft + Pright) * B * Pright := by
                rw [hcomplement, Matrix.mul_one]
                simp [Matrix.mul_assoc]
          _ = Pleft * A * (Pleft * B * Pright) +
              (Pleft * A * Pright) * (B * Pright) := by noncomm_ring
          _ = 0 := by rw [ihB.1, ihA.1]; simp
      · calc
          Pright * (A * B) * Pleft =
              Pright * A * (Pleft + Pright) * B * Pleft := by
                rw [hcomplement, Matrix.mul_one]
                simp [Matrix.mul_assoc]
          _ = (Pright * A * Pleft) * (B * Pleft) +
              Pright * A * (Pright * B * Pleft) := by noncomm_ring
          _ = 0 := by rw [ihA.2, ihB.2]; simp
  | adjoint hA ihA =>
      constructor
      · have h := congrArg star ihA.2
        simpa [star_eq_conjTranspose, Matrix.conjTranspose_mul, hleft, hright,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using h
      · have h := congrArg star ihA.1
        simpa [star_eq_conjTranspose, Matrix.conjTranspose_mul, hleft, hright,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using h
  | scale a hA ihA =>
      constructor
      · rw [Matrix.mul_smul, Matrix.smul_mul, ihA.1, smul_zero]
      · rw [Matrix.mul_smul, Matrix.smul_mul, ihA.2, smul_zero]
  | ancillaryCoefficient a A hA ihA =>
      constructor
      · rw [Matrix.mul_sum, Matrix.sum_mul]
        apply Finset.sum_eq_zero
        intro i _
        rw [Matrix.mul_smul, Matrix.smul_mul, (ihA i).1, smul_zero]
      · rw [Matrix.mul_sum, Matrix.sum_mul]
        apply Finset.sum_eq_zero
        intro i _
        rw [Matrix.mul_smul, Matrix.smul_mul, (ihA i).2, smul_zero]
  | normLimit A Y hA hlim ihA =>
      constructor
      · have hlimBlock : Filter.Tendsto (fun n => Pleft * A n * Pright)
            Filter.atTop (nhds (Pleft * Y * Pright)) :=
          (hlim.const_mul Pleft).mul_const Pright
        have hlimZero : Filter.Tendsto (fun n => Pleft * A n * Pright)
            Filter.atTop (nhds 0) := by
          apply tendsto_const_nhds.congr'
          exact Filter.Eventually.of_forall fun n => (ihA n).1.symm
        exact tendsto_nhds_unique hlimBlock hlimZero
      · have hlimBlock : Filter.Tendsto (fun n => Pright * A n * Pleft)
            Filter.atTop (nhds (Pright * Y * Pleft)) :=
          (hlim.const_mul Pright).mul_const Pleft
        have hlimZero : Filter.Tendsto (fun n => Pright * A n * Pleft)
            Filter.atTop (nhds 0) := by
          apply tendsto_const_nhds.congr'
          exact Filter.Eventually.of_forall fun n => (ihA n).2.symm
        exact tendsto_nhds_unique hlimBlock hlimZero

/-- Character, Walsh, Maslov, and relative-history compressions are finite
linear combinations, hence are covered explicitly by the firewall. -/
theorem finite_compression_cannot_create_cross_block
    {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]
    (Pleft Pright : Matrix d d ℂ)
    (a : ι → ℂ) (K : ι → Matrix d d ℂ)
    (hK : ∀ i, RespectsTypedSupports Pleft Pright (K i)) :
    RespectsTypedSupports Pleft Pright (∑ i, a i • K i) := by
  constructor
  · rw [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_eq_zero
    intro i _
    rw [Matrix.mul_smul, Matrix.smul_mul, (hK i).1, smul_zero]
  · rw [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_eq_zero
    intro i _
    rw [Matrix.mul_smul, Matrix.smul_mul, (hK i).2, smul_zero]

end IncidenceBeforeInterferenceFirewall
end NCG
