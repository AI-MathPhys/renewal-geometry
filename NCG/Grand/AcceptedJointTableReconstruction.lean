/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ReversibleIdempotentPartitionKernel

/-!
# Reconstruction from a stationary accepted joint table

This file encodes the residuals and reconstruction theorem of
`thm:accepted-joint-table`.  The residuals are literal finite Euclidean and
Hilbert--Schmidt squares.
-/

open Matrix

namespace NCG
namespace AcceptedJointTableReconstruction

variable {X : Type*} [Fintype X] [DecidableEq X]

def rowMarginal (J : Matrix X X ℝ) (x : X) : ℝ := ∑ y, J x y

def columnMarginal (J : Matrix X X ℝ) (y : X) : ℝ := ∑ x, J x y

noncomputable def acceptedKernel (J : Matrix X X ℝ) (μ : X → ℝ) : Matrix X X ℝ :=
  fun x y => J x y / μ x

noncomputable def weightedJointComposite
    (J : Matrix X X ℝ) (μ : X → ℝ) : Matrix X X ℝ :=
  fun x y => ∑ z, J x z * (J z y / μ z)

def vectorNormSq (f : X → ℝ) : ℝ := ∑ x, f x ^ 2

def matrixHilbertSchmidtSq (A : Matrix X X ℝ) : ℝ :=
  ∑ p : X × X, A p.1 p.2 ^ 2

def marginalResidual (J : Matrix X X ℝ) (μ : X → ℝ) : ℝ :=
  vectorNormSq (fun x => rowMarginal J x - μ x) +
    vectorNormSq (fun x => columnMarginal J x - μ x)

def reversibilityResidual (J : Matrix X X ℝ) : ℝ :=
  matrixHilbertSchmidtSq (fun x y => J x y - J y x)

noncomputable def idempotencyResidual (J : Matrix X X ℝ) (μ : X → ℝ) : ℝ :=
  matrixHilbertSchmidtSq (fun x y => weightedJointComposite J μ x y - J x y)

theorem vectorNormSq_nonneg (f : X → ℝ) : 0 ≤ vectorNormSq f := by
  exact Finset.sum_nonneg fun x _ => sq_nonneg (f x)

theorem vectorNormSq_eq_zero_iff (f : X → ℝ) :
    vectorNormSq f = 0 ↔ ∀ x, f x = 0 := by
  constructor
  · intro h x
    have hle : f x ^ 2 ≤ vectorNormSq f := by
      unfold vectorNormSq
      exact Finset.single_le_sum
        (fun z _ => sq_nonneg (f z)) (Finset.mem_univ x)
    nlinarith [sq_nonneg (f x)]
  · intro h
    unfold vectorNormSq
    simp [h]

theorem matrixHilbertSchmidtSq_nonneg (A : Matrix X X ℝ) :
    0 ≤ matrixHilbertSchmidtSq A := by
  exact Finset.sum_nonneg fun p _ => sq_nonneg (A p.1 p.2)

theorem matrixHilbertSchmidtSq_eq_zero_iff (A : Matrix X X ℝ) :
    matrixHilbertSchmidtSq A = 0 ↔ ∀ x y, A x y = 0 := by
  constructor
  · intro h x y
    have hle : A x y ^ 2 ≤ matrixHilbertSchmidtSq A := by
      unfold matrixHilbertSchmidtSq
      exact Finset.single_le_sum
        (fun p _ => sq_nonneg (A p.1 p.2))
        (Finset.mem_univ (x, y))
    nlinarith [sq_nonneg (A x y)]
  · intro h
    unfold matrixHilbertSchmidtSq
    simp [h]

theorem marginalResidual_eq_zero_iff
    (J : Matrix X X ℝ) (μ : X → ℝ) :
    marginalResidual J μ = 0 ↔
      (∀ x, rowMarginal J x = μ x) ∧
      (∀ y, columnMarginal J y = μ y) := by
  have hr := vectorNormSq_nonneg (fun x => rowMarginal J x - μ x)
  have hc := vectorNormSq_nonneg (fun x => columnMarginal J x - μ x)
  constructor
  · intro h
    have hr0 : vectorNormSq (fun x => rowMarginal J x - μ x) = 0 := by
      unfold marginalResidual at h
      linarith
    have hc0 : vectorNormSq (fun x => columnMarginal J x - μ x) = 0 := by
      unfold marginalResidual at h
      linarith
    constructor
    · intro x
      have := (vectorNormSq_eq_zero_iff _).1 hr0 x
      linarith
    · intro x
      have := (vectorNormSq_eq_zero_iff _).1 hc0 x
      linarith
  · rintro ⟨hr0, hc0⟩
    unfold marginalResidual
    rw [(vectorNormSq_eq_zero_iff _).2,
      (vectorNormSq_eq_zero_iff _).2]
    · simp
    · intro x
      simp [hc0 x]
    · intro x
      simp [hr0 x]

theorem reversibilityResidual_eq_zero_iff (J : Matrix X X ℝ) :
    reversibilityResidual J = 0 ↔ ∀ x y, J x y = J y x := by
  unfold reversibilityResidual
  constructor
  · intro h x y
    have h0 := (matrixHilbertSchmidtSq_eq_zero_iff
      (fun x y : X => J x y - J y x)).1 h x y
    linarith
  · intro h
    apply (matrixHilbertSchmidtSq_eq_zero_iff
      (fun x y : X => J x y - J y x)).2
    intro x y
    simp [h x y]

theorem idempotencyResidual_eq_zero_iff
    (J : Matrix X X ℝ) (μ : X → ℝ) :
    idempotencyResidual J μ = 0 ↔
      ∀ x y, weightedJointComposite J μ x y = J x y := by
  unfold idempotencyResidual
  constructor
  · intro h x y
    have h0 := (matrixHilbertSchmidtSq_eq_zero_iff
      (fun x y : X => weightedJointComposite J μ x y - J x y)).1 h x y
    linarith
  · intro h
    apply (matrixHilbertSchmidtSq_eq_zero_iff
      (fun x y : X => weightedJointComposite J μ x y - J x y)).2
    intro x y
    simp [h x y]

structure ReversibleIdempotentMarkov
    (R : Matrix X X ℝ) (μ : X → ℝ) : Prop where
  nonnegative : ∀ x y, 0 ≤ R x y
  stochastic : ∀ x, ∑ y, R x y = 1
  reversible : ∀ x y, μ x * R x y = μ y * R y x
  idempotent : R * R = R

theorem joint_eq_mass_mul_kernel
    (J : Matrix X X ℝ) (μ : X → ℝ)
    (hμ : ∀ x, 0 < μ x) (x y : X) :
    J x y = μ x * acceptedKernel J μ x y := by
  unfold acceptedKernel
  field_simp [ne_of_gt (hμ x)]

theorem weightedJointComposite_eq_mass_mul_kernelSq
    (J : Matrix X X ℝ) (μ : X → ℝ)
    (hμ : ∀ x, 0 < μ x) (x y : X) :
    weightedJointComposite J μ x y =
      μ x * (acceptedKernel J μ * acceptedKernel J μ) x y := by
  unfold weightedJointComposite
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  unfold acceptedKernel
  field_simp [ne_of_gt (hμ x), ne_of_gt (hμ z)]

/-- The joint-table support and the normalized-kernel support are identical
when the marginal is faithful. -/
theorem jointSupport_iff_kernelSupport
    (J : Matrix X X ℝ) (μ : X → ℝ)
    (hμ : ∀ x, 0 < μ x) (x y : X) :
    0 < J x y ↔
      ReversibleIdempotentPartitionKernel.supportRel
        (acceptedKernel J μ) x y := by
  unfold ReversibleIdempotentPartitionKernel.supportRel acceptedKernel
  constructor
  · intro h
    exact div_pos h (hμ x)
  · intro h
    rcases (div_pos_iff.mp h) with hpos | hneg
    · exact hpos.1
    · linarith [hμ x]

/-- The three literal table residuals vanish exactly on the branch where
`D_μ⁻¹ J` is a nonnegative stochastic, `μ`-reversible idempotent kernel. -/
theorem residuals_vanish_iff_reversibleIdempotentMarkov
    (J : Matrix X X ℝ) (μ : X → ℝ)
    (hJ : ∀ x y, 0 ≤ J x y) (hμ : ∀ x, 0 < μ x) :
    (marginalResidual J μ = 0 ∧
      reversibilityResidual J = 0 ∧
      idempotencyResidual J μ = 0) ↔
      ReversibleIdempotentMarkov (acceptedKernel J μ) μ := by
  constructor
  · rintro ⟨hmarg, hrev, hidem⟩
    have hm := (marginalResidual_eq_zero_iff J μ).1 hmarg
    have hs := (reversibilityResidual_eq_zero_iff J).1 hrev
    have hi := (idempotencyResidual_eq_zero_iff J μ).1 hidem
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y
      exact div_nonneg (hJ x y) (hμ x).le
    · intro x
      unfold acceptedKernel
      rw [← Finset.sum_div]
      change rowMarginal J x / μ x = 1
      rw [hm.1 x]
      exact div_self (ne_of_gt (hμ x))
    · intro x y
      rw [← joint_eq_mass_mul_kernel J μ hμ x y,
        ← joint_eq_mass_mul_kernel J μ hμ y x]
      exact hs x y
    · ext x y
      have hcomp := weightedJointComposite_eq_mass_mul_kernelSq J μ hμ x y
      have hjoint := joint_eq_mass_mul_kernel J μ hμ x y
      have hzeroμ := hμ x
      nlinarith [hi x y]
  · intro H
    have hrowJ : ∀ x, rowMarginal J x = μ x := by
      intro x
      unfold rowMarginal
      simp_rw [joint_eq_mass_mul_kernel J μ hμ]
      rw [← Finset.mul_sum, H.stochastic x, mul_one]
    have hcolJ : ∀ y, columnMarginal J y = μ y := by
      intro y
      unfold columnMarginal
      simp_rw [joint_eq_mass_mul_kernel J μ hμ]
      calc
        ∑ x, μ x * acceptedKernel J μ x y =
            ∑ x, μ y * acceptedKernel J μ y x := by
              apply Finset.sum_congr rfl
              intro x _
              exact H.reversible x y
        _ = μ y * ∑ x, acceptedKernel J μ y x := by
          rw [Finset.mul_sum]
        _ = μ y := by rw [H.stochastic y, mul_one]
    refine ⟨(marginalResidual_eq_zero_iff J μ).2 ⟨hrowJ, hcolJ⟩, ?_, ?_⟩
    · apply (reversibilityResidual_eq_zero_iff J).2
      intro x y
      rw [joint_eq_mass_mul_kernel J μ hμ,
        joint_eq_mass_mul_kernel J μ hμ]
      exact H.reversible x y
    · apply (idempotencyResidual_eq_zero_iff J μ).2
      intro x y
      rw [weightedJointComposite_eq_mass_mul_kernelSq J μ hμ,
        congrFun (congrFun H.idempotent x) y]
      exact (joint_eq_mass_mul_kernel J μ hμ x y).symm

/-- Complete reconstruction package on the zero-residual branch: the support
setoid is the canonical partition, its rows are conditional faithful masses,
and the stationary free action obeys the supported-edge log identity. -/
theorem acceptedJointTable_reconstruction
    (J : Matrix X X ℝ) (μ : X → ℝ)
    (hJ : ∀ x y, 0 ≤ J x y) (hμ : ∀ x, 0 < μ x)
    (hzero : marginalResidual J μ = 0 ∧
      reversibilityResidual J = 0 ∧
      idempotencyResidual J μ = 0) :
    let R := acceptedKernel J μ
    let H := (residuals_vanish_iff_reversibleIdempotentMarkov J μ hJ hμ).1 hzero
    (∀ x y, R x y = if ReversibleIdempotentPartitionKernel.supportRel R x y
        then μ y / ReversibleIdempotentPartitionKernel.classMass R μ x else 0) ∧
    (∀ x y, J x y = if ReversibleIdempotentPartitionKernel.supportRel R x y
        then μ x * μ y /
          ReversibleIdempotentPartitionKernel.classMass R μ x else 0) ∧
    (∀ x y, ReversibleIdempotentPartitionKernel.supportRel R x y →
      Real.log (R x y / R y x) +
        ReversibleIdempotentPartitionKernel.stationaryFreeAction μ y -
        ReversibleIdempotentPartitionKernel.stationaryFreeAction μ x = 0) := by
  dsimp only
  let H := (residuals_vanish_iff_reversibleIdempotentMarkov J μ hJ hμ).1 hzero
  have hpartition :=
    ReversibleIdempotentPartitionKernel.kernel_eq_partitionAverager
      (acceptedKernel J μ) μ H.nonnegative H.stochastic hμ H.reversible H.idempotent
  refine ⟨hpartition, ?_, ?_⟩
  · intro x y
    rw [joint_eq_mass_mul_kernel J μ hμ x y, hpartition x y]
    split_ifs <;> ring
  · intro x y hxy
    exact ReversibleIdempotentPartitionKernel.supportedTransition_logRatio_add_freeAction_eq_zero
        (acceptedKernel J μ) μ hμ H.reversible hxy

/-- On the zero-residual branch, membership in the canonical partition is
exactly positivity of the joint table.  Thus every block is a complete
support subgraph and different blocks have no support edge, which identifies
the blocks with the support-graph connected components. -/
theorem canonicalPartition_iff_positiveJointSupport
    (J : Matrix X X ℝ) (μ : X → ℝ)
    (hJ : ∀ x y, 0 ≤ J x y) (hμ : ∀ x, 0 < μ x)
    (hzero : marginalResidual J μ = 0 ∧
      reversibilityResidual J = 0 ∧
      idempotencyResidual J μ = 0) :
    let R := acceptedKernel J μ
    let H := (residuals_vanish_iff_reversibleIdempotentMarkov J μ hJ hμ).1 hzero
    let S := ReversibleIdempotentPartitionKernel.supportSetoid
      R μ H.nonnegative H.stochastic hμ H.reversible H.idempotent
    ∀ x y, S.r x y ↔ 0 < J x y := by
  dsimp only
  intro x y
  exact (jointSupport_iff_kernelSupport J μ hμ x y).symm

end AcceptedJointTableReconstruction
end NCG
