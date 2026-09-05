/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite differential occurrence compiler

This file supplies the universal first-order differential calculus used by the
finite NCG landing.  In particular it turns the three finite sums of squares
in `thm:GT-NCG-differential-occurrence` into global unit, Leibniz, and
reversal identities and records the actual universal factor map through
`ker (A ⊗ A → A)`.
-/

open scoped ComplexConjugate TensorProduct InnerProductSpace

namespace NCG
namespace FiniteDifferentialOccurrenceCompiler

noncomputable section

variable {n : ℕ} {A K : Type*}
  [NormedRing A] [NormedAlgebra ℂ A]
  [StarRing A] [StarModule ℂ A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The universal one-forms `Ω¹_u(A) = ker (A ⊗ A → A)`. -/
abbrev UniversalOneForm (A : Type*) [Ring A] [Algebra ℂ A] :=
  LinearMap.ker (LinearMap.mul' ℂ A)

/-- The universal differential `d_u a = 1 ⊗ a - a ⊗ 1`. -/
def universalDifferentialTensor : A →ₗ[ℂ] A ⊗[ℂ] A :=
  TensorProduct.mk ℂ A A 1 - (TensorProduct.mk ℂ A A).flip 1

def universalDifferential : A →ₗ[ℂ] UniversalOneForm A where
  toFun a := ⟨universalDifferentialTensor a, by
    simp [universalDifferentialTensor]⟩
  map_add' a b := by
    apply Subtype.ext
    exact (universalDifferentialTensor.map_add a b)
  map_smul' z a := by
    apply Subtype.ext
    exact (universalDifferentialTensor.map_smul z a)

@[simp]
theorem universalDifferential_coe (a : A) :
    (universalDifferential a : A ⊗[ℂ] A) = 1 ⊗ₜ[ℂ] a - a ⊗ₜ[ℂ] 1 := by
  rfl

/-- Data of a finite represented tangent packet.  `right` is deliberately a
linear right action here: its anti-multiplicativity and commutation with
`left` are retained as explicit laws, so no opposite-algebra coercions are
hidden in the statement. -/
structure Packet (n : ℕ) (A K : Type*)
    [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [StarModule ℂ A]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] where
  basis : Module.Basis (Fin n) ℂ A
  unitIndex : Fin n
  basis_unit : basis unitIndex = 1
  delta : A →ₗ[ℂ] K
  left : A →ₐ[ℂ] Module.End ℂ K
  right : A →ₗ[ℂ] Module.End ℂ K
  right_one : right 1 = 1
  right_mul : ∀ a b, right (a * b) = right b * right a
  commute_actions : ∀ a b, Commute (left a) (right b)
  reverse : K ≃ₗ⋆[ℂ] K
  reverse_left : ∀ a x, reverse (left a x) = right (star a) (reverse x)
  reverse_right : ∀ a x, reverse (right a x) = left (star a) (reverse x)
  reverse_involutive : Function.Involutive reverse
  left_star_adjoint : ∀ a x y,
    ⟪left a x, y⟫_ℂ = ⟪x, left (star a) y⟫_ℂ
  right_star_adjoint : ∀ a x y,
    ⟪right a x, y⟫_ℂ = ⟪x, right (star a) y⟫_ℂ
  reverse_inner : ∀ x y, ⟪reverse x, reverse y⟫_ℂ = ⟪y, x⟫_ℂ

namespace Packet

variable (P : Packet n A K)

/-- The unit defect in (SP.5). -/
def unitResidual : ℝ := ‖P.delta 1‖ ^ 2

/-- One basis-pair Leibniz defect. -/
def leibnizDefect (a b : A) : K :=
  P.delta (a * b) - P.left a (P.delta b) - P.right b (P.delta a)

/-- The Leibniz defect is genuinely bilinear; this is what allows a finite
basis table to certify the identity on the whole algebra. -/
def leibnizDefectLinear : A →ₗ[ℂ] A →ₗ[ℂ] K :=
  LinearMap.mk₂ ℂ P.leibnizDefect
    (by
      intro a a' b
      simp only [leibnizDefect, add_mul, map_add, LinearMap.add_apply]
      abel)
    (by
      intro z a b
      simp only [leibnizDefect, smul_mul_assoc, map_smul, LinearMap.smul_apply]
      module)
    (by
      intro a b b'
      simp only [leibnizDefect, mul_add, map_add, LinearMap.add_apply]
      abel)
    (by
      intro z a b
      simp only [leibnizDefect, mul_smul_comm, map_smul, LinearMap.smul_apply]
      module)

/-- The finite Leibniz sum of squares in (SP.5). -/
def leibnizResidual : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ‖P.leibnizDefect (P.basis i) (P.basis j)‖ ^ 2

/-- One star/reversal defect. -/
def starDefect (a : A) : K := P.delta (star a) - P.reverse (P.delta a)

/-- The star/reversal defect is conjugate-linear. -/
def starDefectSemilinear : A →ₛₗ[starRingEnd ℂ] K where
  toFun := P.starDefect
  map_add' a b := by
    simp only [starDefect, star_add, map_add]
    abel
  map_smul' z a := by
    change P.starDefect (z • a) = star z • P.starDefect a
    simp [starDefect, star_smul, smul_sub, LinearEquiv.map_smulₛₗ]

/-- The finite star sum of squares in (SP.5). -/
def starResidual : ℝ := ∑ i : Fin n, ‖P.starDefect (P.basis i)‖ ^ 2

/-- The global content of (D2). -/
def IsStarBimoduleDerivation : Prop :=
  P.delta 1 = 0 ∧
  (∀ a b, P.delta (a * b) =
    P.left a (P.delta b) + P.right b (P.delta a)) ∧
  (∀ a, P.delta (star a) = P.reverse (P.delta a))

theorem unitResidual_eq_zero_iff : P.unitResidual = 0 ↔ P.delta 1 = 0 := by
  simp [unitResidual]

theorem leibnizResidual_eq_zero_iff_basis :
    P.leibnizResidual = 0 ↔
      ∀ i j, P.leibnizDefect (P.basis i) (P.basis j) = 0 := by
  constructor
  · intro h i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦
      Finset.sum_nonneg (fun j _ ↦ sq_nonneg
        ‖P.leibnizDefect (P.basis i) (P.basis j)‖))).mp h i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg
      ‖P.leibnizDefect (P.basis i) (P.basis j)‖)).mp hi j (Finset.mem_univ j)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hij)
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    simp [h i j]

theorem starResidual_eq_zero_iff_basis :
    P.starResidual = 0 ↔ ∀ i, P.starDefect (P.basis i) = 0 := by
  constructor
  · intro h i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg
      ‖P.starDefect (P.basis i)‖)).mp h i (Finset.mem_univ i)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    simp [h i]

theorem leibniz_basis_iff_global :
    (∀ i j, P.leibnizDefect (P.basis i) (P.basis j) = 0) ↔
      ∀ a b, P.leibnizDefect a b = 0 := by
  constructor
  · intro h
    have houter : P.leibnizDefectLinear = 0 := by
      apply P.basis.ext
      intro i
      apply P.basis.ext
      intro j
      exact h i j
    intro a b
    have hab := congrArg (fun f : A →ₗ[ℂ] K ↦ f b)
      (congrArg (fun f : A →ₗ[ℂ] A →ₗ[ℂ] K ↦ f a) houter)
    simpa [leibnizDefectLinear] using hab
  · exact fun h i j ↦ h (P.basis i) (P.basis j)

theorem star_basis_iff_global :
    (∀ i, P.starDefect (P.basis i) = 0) ↔ ∀ a, P.starDefect a = 0 := by
  constructor
  · intro h
    have hmap : P.starDefectSemilinear = 0 := by
      apply P.basis.ext
      exact h
    intro a
    have ha := congrArg (fun f : A →ₛₗ[starRingEnd ℂ] K ↦ f a) hmap
    simpa [starDefectSemilinear] using ha
  · exact fun h i ↦ h (P.basis i)

/-- The three finite residuals vanish exactly when the tangent is a global
star-compatible bimodule derivation.  No identities away from the chosen
basis are assumed. -/
theorem residuals_zero_iff_star_bimodule_derivation :
    (P.unitResidual = 0 ∧ P.leibnizResidual = 0 ∧
      P.starResidual = 0) ↔ P.IsStarBimoduleDerivation := by
  rw [unitResidual_eq_zero_iff, leibnizResidual_eq_zero_iff_basis,
    starResidual_eq_zero_iff_basis, leibniz_basis_iff_global,
    star_basis_iff_global]
  simp only [IsStarBimoduleDerivation, leibnizDefect, starDefect,
    sub_eq_iff_eq_add, zero_add, add_comm]

/-- The tensor-level formula `a ⊗ b ↦ λ(a) δ(b)` from the manuscript proof. -/
def factorTensor : A ⊗[ℂ] A →ₗ[ℂ] K :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ
    (fun a b ↦ P.left a (P.delta b))
    (by intro a a' b; simp)
    (by intro z a b; simp)
    (by intro a b b'; simp)
    (by intro z a b; simp)

@[simp]
theorem factorTensor_tmul (a b : A) :
    P.factorTensor (a ⊗ₜ[ℂ] b) = P.left a (P.delta b) := rfl

/-- The canonical factor on universal one-forms. -/
def universalFactor : UniversalOneForm A →ₗ[ℂ] K :=
  P.factorTensor.comp (LinearMap.ker (LinearMap.mul' ℂ A)).subtype

@[simp]
theorem universalFactor_apply (ω : UniversalOneForm A) :
    P.universalFactor ω = P.factorTensor (ω : A ⊗[ℂ] A) := rfl

/-- On the derivation branch the canonical factor sends `d_u a` to `δa`. -/
theorem universalFactor_comp_differential
    (h : P.IsStarBimoduleDerivation) :
    P.universalFactor.comp universalDifferential = P.delta := by
  ext a
  simp [universalFactor, universalDifferential, universalDifferentialTensor,
    factorTensor, h.1]

/-- Left multiplication on the ambient tensor square. -/
def tensorLeft (a : A) : A ⊗[ℂ] A →ₗ[ℂ] A ⊗[ℂ] A :=
  TensorProduct.map (LinearMap.mul ℂ A a) LinearMap.id

/-- Right multiplication on the ambient tensor square. -/
def tensorRight (a : A) : A ⊗[ℂ] A →ₗ[ℂ] A ⊗[ℂ] A :=
  TensorProduct.map LinearMap.id (LinearMap.mulRight ℂ a)

@[simp] theorem tensorLeft_tmul (a x y : A) :
    tensorLeft a (x ⊗ₜ[ℂ] y) = (a * x) ⊗ₜ[ℂ] y := rfl

@[simp] theorem tensorRight_tmul (a x y : A) :
    tensorRight a (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] (y * a) := rfl

theorem mul_comp_tensorLeft (a : A) :
    LinearMap.mul' ℂ A ∘ₗ tensorLeft a =
      LinearMap.mul ℂ A a ∘ₗ LinearMap.mul' ℂ A := by
  apply TensorProduct.ext'
  intro x y
  simp [tensorLeft, LinearMap.comp_apply, mul_assoc]

theorem mul_comp_tensorRight (a : A) :
    LinearMap.mul' ℂ A ∘ₗ tensorRight a =
      LinearMap.mulRight ℂ a ∘ₗ LinearMap.mul' ℂ A := by
  apply TensorProduct.ext'
  intro x y
  simp [tensorRight, LinearMap.comp_apply, mul_assoc]

/-- The induced left action on universal one-forms. -/
def oneFormLeft (a : A) : UniversalOneForm A →ₗ[ℂ] UniversalOneForm A where
  toFun ω := ⟨tensorLeft a ω.1, by
    have hω := ω.property
    rw [LinearMap.mem_ker] at hω ⊢
    have h := LinearMap.congr_fun (mul_comp_tensorLeft (A := A) a) ω.1
    change LinearMap.mul' ℂ A (tensorLeft a ω.1) = 0
    rw [show LinearMap.mul' ℂ A (tensorLeft a ω.1) =
      LinearMap.mul ℂ A a (LinearMap.mul' ℂ A ω.1) by
        simpa [LinearMap.comp_apply] using h]
    simp [hω]⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' z x := by
    apply Subtype.ext
    simp

/-- The induced right action on universal one-forms. -/
def oneFormRight (a : A) : UniversalOneForm A →ₗ[ℂ] UniversalOneForm A where
  toFun ω := ⟨tensorRight a ω.1, by
    have hω := ω.property
    rw [LinearMap.mem_ker] at hω ⊢
    have h := LinearMap.congr_fun (mul_comp_tensorRight (A := A) a) ω.1
    change LinearMap.mul' ℂ A (tensorRight a ω.1) = 0
    rw [show LinearMap.mul' ℂ A (tensorRight a ω.1) =
      LinearMap.mulRight ℂ a (LinearMap.mul' ℂ A ω.1) by
        simpa [LinearMap.comp_apply] using h]
    simp [hω]⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' z x := by
    apply Subtype.ext
    simp

@[simp] theorem oneFormLeft_coe (a : A) (ω : UniversalOneForm A) :
    ((oneFormLeft a ω : UniversalOneForm A) : A ⊗[ℂ] A) = tensorLeft a ω.1 := rfl

@[simp] theorem oneFormRight_coe (a : A) (ω : UniversalOneForm A) :
    ((oneFormRight a ω : UniversalOneForm A) : A ⊗[ℂ] A) = tensorRight a ω.1 := rfl

theorem factorTensor_tensorLeft (a : A) (x : A ⊗[ℂ] A) :
    P.factorTensor (tensorLeft a x) = P.left a (P.factorTensor x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      simp only [tensorLeft_tmul, factorTensor_tmul]
      have hm := congrArg (fun f : Module.End ℂ K ↦ f (P.delta y))
        (map_mul P.left a x)
      simpa [Module.End.mul_apply] using hm

theorem factorTensor_tensorRight (h : P.IsStarBimoduleDerivation)
    (a : A) (x : A ⊗[ℂ] A) :
    P.factorTensor (tensorRight a x) =
      P.left (LinearMap.mul' ℂ A x) (P.delta a) +
        P.right a (P.factorTensor x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_assoc, add_left_comm, add_comm]
  | tmul x y =>
      simp only [tensorRight_tmul, factorTensor_tmul,
        LinearMap.mul'_apply, h.2.1]
      have hmul := congrArg (fun f : Module.End ℂ K ↦ f (P.delta a))
        (map_mul P.left x y)
      have hcomm := congrArg (fun f : Module.End ℂ K ↦ f (P.delta y))
        (P.commute_actions x a).eq
      rw [map_add]
      simp only [Module.End.mul_apply] at hmul hcomm
      rw [hmul, hcomm]

theorem universalFactor_left (a : A) (ω : UniversalOneForm A) :
    P.universalFactor (oneFormLeft a ω) =
      P.left a (P.universalFactor ω) := by
  exact factorTensor_tensorLeft P a ω.1

theorem universalFactor_right (h : P.IsStarBimoduleDerivation)
    (a : A) (ω : UniversalOneForm A) :
    P.universalFactor (oneFormRight a ω) =
      P.right a (P.universalFactor ω) := by
  rw [universalFactor_apply, oneFormRight_coe,
    factorTensor_tensorRight P h]
  have hω := ω.property
  rw [LinearMap.mem_ker] at hω
  simp [hω]

/-- The normalized pure tensor `a d_u b = a ⊗ b - ab ⊗ 1`, regarded as
an element of the multiplication kernel. -/
def normalizedPure (a b : A) : UniversalOneForm A :=
  ⟨a ⊗ₜ[ℂ] b - (a * b) ⊗ₜ[ℂ] 1, by simp⟩

@[simp] theorem normalizedPure_coe (a b : A) :
    ((normalizedPure a b : UniversalOneForm A) : A ⊗[ℂ] A) =
      a ⊗ₜ[ℂ] b - (a * b) ⊗ₜ[ℂ] 1 := rfl

theorem normalizedPure_eq_left_differential (a b : A) :
    normalizedPure a b = oneFormLeft a (universalDifferential b) := by
  apply Subtype.ext
  simp [oneFormLeft, tensorLeft, universalDifferential,
    universalDifferentialTensor, normalizedPure]

/-- Linear normalization of a tensor into the universal multiplication
kernel.  It is the identity on that kernel. -/
def normalizeTensor : A ⊗[ℂ] A →ₗ[ℂ] UniversalOneForm A :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ normalizedPure
    (by
      intro a a' b
      apply Subtype.ext
      change (a + a') ⊗ₜ[ℂ] b - ((a + a') * b) ⊗ₜ[ℂ] 1 =
        (a ⊗ₜ[ℂ] b - (a * b) ⊗ₜ[ℂ] 1) +
          (a' ⊗ₜ[ℂ] b - (a' * b) ⊗ₜ[ℂ] 1)
      simp only [TensorProduct.add_tmul, add_mul]
      abel)
    (by
      intro z a b
      apply Subtype.ext
      change (z • a) ⊗ₜ[ℂ] b - ((z • a) * b) ⊗ₜ[ℂ] 1 =
        z • (a ⊗ₜ[ℂ] b - (a * b) ⊗ₜ[ℂ] 1)
      simp [TensorProduct.smul_tmul, smul_mul_assoc, smul_sub])
    (by
      intro a b b'
      apply Subtype.ext
      change a ⊗ₜ[ℂ] (b + b') - (a * (b + b')) ⊗ₜ[ℂ] 1 =
        (a ⊗ₜ[ℂ] b - (a * b) ⊗ₜ[ℂ] 1) +
          (a ⊗ₜ[ℂ] b' - (a * b') ⊗ₜ[ℂ] 1)
      simp only [TensorProduct.tmul_add, mul_add]
      rw [TensorProduct.add_tmul]
      abel)
    (by
      intro z a b
      apply Subtype.ext
      change a ⊗ₜ[ℂ] (z • b) - (a * (z • b)) ⊗ₜ[ℂ] 1 =
        z • (a ⊗ₜ[ℂ] b - (a * b) ⊗ₜ[ℂ] 1)
      simp only [TensorProduct.tmul_smul, mul_smul_comm, smul_sub]
      rw [← TensorProduct.smul_tmul'])

@[simp] theorem normalizeTensor_tmul (a b : A) :
    normalizeTensor (a ⊗ₜ[ℂ] b) = normalizedPure a b := rfl

theorem normalizeTensor_coe_formula (x : A ⊗[ℂ] A) :
    ((normalizeTensor x : UniversalOneForm A) : A ⊗[ℂ] A) =
      x - (LinearMap.mul' ℂ A x) ⊗ₜ[ℂ] 1 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [normalizeTensor.map_add]
      simp only [Submodule.coe_add]
      rw [(LinearMap.mul' ℂ A).map_add]
      rw [hx, hy, TensorProduct.add_tmul]
      abel
  | tmul a b => simp [normalizedPure]

theorem normalizeTensor_on_oneForm (ω : UniversalOneForm A) :
    normalizeTensor (ω : A ⊗[ℂ] A) = ω := by
  apply Subtype.ext
  rw [normalizeTensor_coe_formula]
  have hω := ω.property
  rw [LinearMap.mem_ker] at hω
  simp [hω]

/-- Universal uniqueness: a left-module map agreeing with `δ` on every
universal differential must be the canonical factor.  The right-module and
reversal requirements in (D3) therefore do not introduce extra choices. -/
theorem universalFactor_unique
    (T : UniversalOneForm A →ₗ[ℂ] K)
    (hdu : T.comp universalDifferential = P.delta)
    (hleft : ∀ a ω, T (oneFormLeft a ω) = P.left a (T ω)) :
    T = P.universalFactor := by
  have hcomp : T.comp normalizeTensor = P.factorTensor := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, normalizeTensor_tmul,
      factorTensor_tmul]
    rw [normalizedPure_eq_left_differential, hleft]
    have hb := LinearMap.congr_fun hdu b
    simpa [LinearMap.comp_apply] using congrArg (fun x ↦ P.left a x) hb
  ext ω
  have hω := LinearMap.congr_fun hcomp (ω : A ⊗[ℂ] A)
  calc
    T ω = T (normalizeTensor (ω : A ⊗[ℂ] A)) := by
      rw [normalizeTensor_on_oneForm]
    _ = P.factorTensor (ω : A ⊗[ℂ] A) := hω
    _ = P.universalFactor ω := rfl

/-- Universal reversal on the ambient tensor square:
`(a ⊗ b)ⁿ = -b* ⊗ a*`. -/
def tensorReversal : A ⊗[ℂ] A →ₛₗ[starRingEnd ℂ] A ⊗[ℂ] A where
  toFun x := -(TensorProduct.comm ℂ A A) (star x)
  map_add' x y := by simp [add_comm]
  map_smul' z x := by
    change -(TensorProduct.comm ℂ A A) (star (z • x)) =
      star z • (-(TensorProduct.comm ℂ A A) (star x))
    simp [star_smul]

@[simp] theorem tensorReversal_tmul (a b : A) :
    tensorReversal (a ⊗ₜ[ℂ] b) = -(star b ⊗ₜ[ℂ] star a) := rfl

theorem mul_tensorReversal (x : A ⊗[ℂ] A) :
    LinearMap.mul' ℂ A (tensorReversal x) =
      -star (LinearMap.mul' ℂ A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_comm]
  | tmul a b => simp [tensorReversal, star_mul]

/-- The universal reversal preserves the multiplication kernel. -/
def oneFormReversal : UniversalOneForm A →ₛₗ[starRingEnd ℂ]
    UniversalOneForm A where
  toFun ω := ⟨tensorReversal ω.1, by
    have hω := ω.property
    rw [LinearMap.mem_ker] at hω ⊢
    rw [mul_tensorReversal, hω, star_zero, neg_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' z x := by
    apply Subtype.ext
    exact tensorReversal.map_smul' z x.1

@[simp] theorem oneFormReversal_coe (ω : UniversalOneForm A) :
    ((oneFormReversal ω : UniversalOneForm A) : A ⊗[ℂ] A) =
      tensorReversal ω.1 := rfl

theorem oneFormReversal_involutive :
    Function.Involutive (oneFormReversal (A := A)) := by
  intro ω
  apply Subtype.ext
  change tensorReversal (tensorReversal ω.1) = ω.1
  induction ω.1 using TensorProduct.induction_on with
  | zero => simp [tensorReversal]
  | add x y hx hy => simp [hx, hy]
  | tmul a b => simp [tensorReversal]

theorem factorTensor_reversal_formula
    (h : P.IsStarBimoduleDerivation) (x : A ⊗[ℂ] A) :
    P.factorTensor (tensorReversal x) =
      P.reverse (P.factorTensor x) -
        P.reverse (P.delta (LinearMap.mul' ℂ A x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, hx, hy]
      abel
  | tmul a b =>
      simp only [tensorReversal_tmul, map_neg, factorTensor_tmul,
        LinearMap.mul'_apply]
      rw [h.2.2 a, h.2.1 a b, map_add,
        P.reverse_left, P.reverse_right]
      abel

/-- On the derivation branch the universal factor intertwines the universal
one-form reversal with the occurring antiunitary reversal. -/
theorem universalFactor_reversal
    (h : P.IsStarBimoduleDerivation) (ω : UniversalOneForm A) :
    P.universalFactor (oneFormReversal ω) =
      P.reverse (P.universalFactor ω) := by
  rw [universalFactor_apply, oneFormReversal_coe,
    factorTensor_reversal_formula P h]
  have hω := ω.property
  rw [LinearMap.mem_ker] at hω
  simp [hω]

theorem universalDifferential_mul (a b : A) :
    universalDifferential (a * b) =
      oneFormLeft a (universalDifferential b) +
        oneFormRight b (universalDifferential a) := by
  apply Subtype.ext
  simp [universalDifferential, universalDifferentialTensor,
    oneFormLeft, oneFormRight, tensorLeft, tensorRight]

theorem universalDifferential_star (a : A) :
    universalDifferential (star a) =
      oneFormReversal (universalDifferential a) := by
  apply Subtype.ext
  simp [universalDifferential, universalDifferentialTensor,
    oneFormReversal, tensorReversal]

/-- The exact content of (D3), including both module actions and reversal. -/
def IsUniversalRealization (T : UniversalOneForm A →ₗ[ℂ] K) : Prop :=
  T.comp universalDifferential = P.delta ∧
  (∀ a ω, T (oneFormLeft a ω) = P.left a (T ω)) ∧
  (∀ a ω, T (oneFormRight a ω) = P.right a (T ω)) ∧
  (∀ ω, T (oneFormReversal ω) = P.reverse (T ω))

theorem star_bimodule_derivation_iff_unique_universal_realization :
    P.IsStarBimoduleDerivation ↔
      ∃! T : UniversalOneForm A →ₗ[ℂ] K, P.IsUniversalRealization T := by
  constructor
  · intro h
    refine ⟨P.universalFactor, ?_, ?_⟩
    · exact ⟨universalFactor_comp_differential P h,
        universalFactor_left P, universalFactor_right P h,
        universalFactor_reversal P h⟩
    · intro T hT
      exact universalFactor_unique P T hT.1 hT.2.1
  · rintro ⟨T, hT, -⟩
    refine ⟨?_, ?_, ?_⟩
    · have h1 := LinearMap.congr_fun hT.1 (1 : A)
      have h1' : T (universalDifferential (1 : A)) = P.delta 1 := by
        simpa [LinearMap.comp_apply] using h1
      have hdu1 : universalDifferential (1 : A) = 0 := by
        apply Subtype.ext
        simp [universalDifferential, universalDifferentialTensor]
      rw [hdu1, map_zero] at h1'
      exact h1'.symm
    · intro a b
      have hab := LinearMap.congr_fun hT.1 (a * b)
      have ha := LinearMap.congr_fun hT.1 a
      have hb := LinearMap.congr_fun hT.1 b
      have ha' : T (universalDifferential a) = P.delta a := by
        simpa [LinearMap.comp_apply] using ha
      have hb' : T (universalDifferential b) = P.delta b := by
        simpa [LinearMap.comp_apply] using hb
      rw [LinearMap.comp_apply, universalDifferential_mul, map_add,
        hT.2.1, hT.2.2.1] at hab
      rw [ha', hb'] at hab
      exact hab.symm
    · intro a
      have hstar := LinearMap.congr_fun hT.1 (star a)
      have ha := LinearMap.congr_fun hT.1 a
      have ha' : T (universalDifferential a) = P.delta a := by
        simpa [LinearMap.comp_apply] using ha
      rw [LinearMap.comp_apply, universalDifferential_star,
        hT.2.2.2] at hstar
      rw [ha'] at hstar
      exact hstar.symm

/-- Combined (D1)–(D3) equivalence of the finite occurrence compiler. -/
theorem residuals_derivation_universal_equivalence :
    ((P.unitResidual = 0 ∧ P.leibnizResidual = 0 ∧
        P.starResidual = 0) ↔ P.IsStarBimoduleDerivation) ∧
    (P.IsStarBimoduleDerivation ↔
      ∃! T : UniversalOneForm A →ₗ[ℂ] K, P.IsUniversalRealization T) :=
  ⟨residuals_zero_iff_star_bimodule_derivation P,
    star_bimodule_derivation_iff_unique_universal_realization P⟩

/-- The Gram (SP.6) pulled back by the canonical universal factor. -/
def inducedGram (ω η : UniversalOneForm A) : ℂ :=
  ⟪P.universalFactor ω, P.universalFactor η⟫_ℂ

/-- The three admissibility identities (SP.3), positivity, and the exact null
space statement for the induced Gram. -/
structure AdmissibleInducedGram : Prop where
  positive : ∀ ω, 0 ≤ (P.inducedGram ω ω).re
  left_adjoint : ∀ a ω η,
    P.inducedGram (oneFormLeft a ω) η =
      P.inducedGram ω (oneFormLeft (star a) η)
  right_adjoint : ∀ a ω η,
    P.inducedGram (oneFormRight a ω) η =
      P.inducedGram ω (oneFormRight (star a) η)
  reversal : ∀ ω η,
    P.inducedGram (oneFormReversal ω) (oneFormReversal η) =
      P.inducedGram η ω
  null_iff : ∀ ω, P.inducedGram ω ω = 0 ↔ P.universalFactor ω = 0

theorem inducedGram_admissible (h : P.IsStarBimoduleDerivation) :
    P.AdmissibleInducedGram := by
  constructor
  · intro ω
    simpa [inducedGram] using
      (inner_self_nonneg (𝕜 := ℂ) (x := P.universalFactor ω))
  · intro a ω η
    simp only [inducedGram, universalFactor_left]
    exact P.left_star_adjoint a _ _
  · intro a ω η
    simp only [inducedGram, universalFactor_right P h]
    exact P.right_star_adjoint a _ _
  · intro ω η
    simp only [inducedGram, universalFactor_reversal P h]
    exact P.reverse_inner _ _
  · intro ω
    exact inner_self_eq_zero

/-- Algebraic source-minimal carrier: quotienting by the Gram null space is
canonically the range of the factor map (the finite-dimensional closure of
that range in the manuscript). -/
noncomputable def sourceMinimalEquivRange :
    (UniversalOneForm A ⧸ LinearMap.ker P.universalFactor) ≃ₗ[ℂ]
      LinearMap.range P.universalFactor :=
  LinearMap.quotKerEquivRange P.universalFactor

@[simp] theorem sourceMinimalEquivRange_apply (ω : UniversalOneForm A) :
    ((P.sourceMinimalEquivRange (Submodule.Quotient.mk ω) :
      LinearMap.range P.universalFactor) : K) = P.universalFactor ω := by
  exact LinearMap.quotKerEquivRange_apply_mk _ _

/-- A positive one of the three displayed finite residuals is a concrete
obstruction to the global derivation identities. -/
theorem positive_residual_obstructs_derivation
    (hpos : 0 < P.unitResidual ∨ 0 < P.leibnizResidual ∨
      0 < P.starResidual) : ¬ P.IsStarBimoduleDerivation := by
  intro hD
  have hz := residuals_zero_iff_star_bimodule_derivation P |>.2 hD
  rcases hpos with h | h | h
  · exact h.ne' hz.1
  · exact h.ne' hz.2.1
  · exact h.ne' hz.2.2

/-- **`thm:GT-NCG-differential-occurrence`**.  The finite residual criterion,
global star-bimodule derivation, and unique universal realization are
equivalent.  On that branch the pulled-back Gram is admissible, its null
space is exactly the factor kernel, and the first isomorphism theorem gives
the source-minimal range carrier.  A positive residual obstructs the branch. -/
theorem finite_differential_occurrence_compiler :
    ((P.unitResidual = 0 ∧ P.leibnizResidual = 0 ∧
        P.starResidual = 0) ↔ P.IsStarBimoduleDerivation) ∧
    (P.IsStarBimoduleDerivation ↔
      ∃! T : UniversalOneForm A →ₗ[ℂ] K, P.IsUniversalRealization T) ∧
    (P.IsStarBimoduleDerivation → P.AdmissibleInducedGram) ∧
    (∀ ω, ((P.sourceMinimalEquivRange (Submodule.Quotient.mk ω) :
      LinearMap.range P.universalFactor) : K) = P.universalFactor ω) ∧
    ((0 < P.unitResidual ∨ 0 < P.leibnizResidual ∨
      0 < P.starResidual) → ¬ P.IsStarBimoduleDerivation) := by
  exact ⟨residuals_zero_iff_star_bimodule_derivation P,
    star_bimodule_derivation_iff_unique_universal_realization P,
    inducedGram_admissible P, sourceMinimalEquivRange_apply P,
    positive_residual_obstructs_derivation P⟩

end Packet

end

end FiniteDifferentialOccurrenceCompiler
end NCG
