/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite projective kernel and skeleton transport

The static and dynamic part of `thm:RPESM-projective-transport` is a finite
calculation.  This module records it without measure-theoretic interfaces:
Boltzmann normalization gives an exact conditional kernel, adjoining that
kernel preserves the old marginal, and the lift-after-old-update skeleton is
reversible and intertwines every old observable.  The final section records
the determinant transport under the manuscript's determinant-one triangular
shell maps.
-/

open Finset Matrix
open scoped BigOperators

namespace NCG
namespace FiniteProjectiveKernelTransport

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Pointwise shell partition function. -/
noncomputable def shellPartition (κ : X → Y → ℝ) (V : X → Y → ℝ)
    (x : X) : ℝ :=
  ∑ y, Real.exp (-V x y) * κ x y

/-- The normalized Boltzmann detail kernel. -/
noncomputable def shellKernel (κ : X → Y → ℝ) (V : X → Y → ℝ)
    (x : X) (y : Y) : ℝ :=
  (shellPartition κ V x)⁻¹ * (Real.exp (-V x y) * κ x y)

theorem shellPartition_pos (κ : X → Y → ℝ) (V : X → Y → ℝ)
    (hκ : ∀ x y, 0 ≤ κ x y)
    (hκpos : ∀ x, ∃ y, 0 < κ x y) (x : X) :
    0 < shellPartition κ V x := by
  obtain ⟨y, hy⟩ := hκpos x
  unfold shellPartition
  apply Finset.sum_pos'
  · intro z _
    exact mul_nonneg (Real.exp_pos _).le (hκ x z)
  · refine ⟨y, Finset.mem_univ _, ?_⟩
    exact mul_pos (Real.exp_pos _) hy

theorem shellKernel_nonneg (κ : X → Y → ℝ) (V : X → Y → ℝ)
    (hκ : ∀ x y, 0 ≤ κ x y) (x : X) (y : Y) :
    0 ≤ shellKernel κ V x y := by
  exact mul_nonneg (inv_nonneg.mpr (Finset.sum_nonneg fun z _ =>
    mul_nonneg (Real.exp_pos _).le (hκ x z)))
    (mul_nonneg (Real.exp_pos _).le (hκ x y))

theorem sum_shellKernel (κ : X → Y → ℝ) (V : X → Y → ℝ)
    (hZ : ∀ x, shellPartition κ V x ≠ 0) (x : X) :
    ∑ y, shellKernel κ V x y = 1 := by
  simp_rw [shellKernel, ← Finset.mul_sum]
  rw [show (∑ y, Real.exp (-V x y) * κ x y) = shellPartition κ V x from rfl,
    inv_mul_cancel₀ (hZ x)]

/-- Adjoin the normalized detail conditional to an old law. -/
noncomputable def fineLaw (μ : X → ℝ) (K : X → Y → ℝ) : X × Y → ℝ :=
  fun p => μ p.1 * K p.1 p.2

/-- The old marginal is preserved exactly. -/
theorem fineLaw_fst_marginal (μ : X → ℝ) (K : X → Y → ℝ)
    (hK : ∀ x, ∑ y, K x y = 1) (x : X) :
    ∑ y, fineLaw μ K (x, y) = μ x := by
  simp_rw [fineLaw, ← Finset.mul_sum, hK x, mul_one]

/-- Parameterwise marginal preservation is equality of the complete scalar
functions, not only equality at one parameter. -/
theorem fineLaw_fst_marginal_family (μ : ℝ → X → ℝ)
    (K : ℝ → X → Y → ℝ) (hK : ∀ t x, ∑ y, K t x y = 1)
    (x : X) :
    (fun t => ∑ y, fineLaw (μ t) (K t) (x, y)) = fun t => μ t x := by
  funext t
  exact fineLaw_fst_marginal (μ t) (K t) (hK t) x

/-- Every old-supported first writer is transported because the complete
marginal functions agree. -/
theorem fineLaw_fst_marginal_hasDerivAt_iff (μ : ℝ → X → ℝ)
    (K : ℝ → X → Y → ℝ) (hK : ∀ t x, ∑ y, K t x y = 1)
    (x : X) (d t₀ : ℝ) :
    HasDerivAt (fun t => ∑ y, fineLaw (μ t) (K t) (x, y)) d t₀ ↔
      HasDerivAt (fun t => μ t x) d t₀ := by
  rw [fineLaw_fst_marginal_family μ K hK x]

/-- The same exact functional identity transports second writers as well. -/
theorem fineLaw_fst_marginal_secondDeriv_iff (μ : ℝ → X → ℝ)
    (K : ℝ → X → Y → ℝ) (hK : ∀ t x, ∑ y, K t x y = 1)
    (x : X) (d₂ t₀ : ℝ) :
    HasDerivAt (deriv (fun t => ∑ y, fineLaw (μ t) (K t) (x, y))) d₂ t₀ ↔
      HasDerivAt (deriv (fun t => μ t x)) d₂ t₀ := by
  rw [fineLaw_fst_marginal_family μ K hK x]

/-- Expectations of every old-supported writer are transported exactly. -/
theorem fineLaw_oldExpectation (μ : X → ℝ) (K : X → Y → ℝ)
    (hK : ∀ x, ∑ y, K x y = 1) (f : X → ℝ) :
    ∑ p : X × Y, fineLaw μ K p * f p.1 = ∑ x, μ x * f x := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  calc
    ∑ y, fineLaw μ K (x, y) * f x
        = (∑ y, fineLaw μ K (x, y)) * f x := by rw [Finset.sum_mul]
    _ = μ x * f x := by rw [fineLaw_fst_marginal μ K hK x]

/-- A detail conditional is genuinely coupled precisely when it varies with
the old field. -/
def GenuinelyCoupled (K : X → Y → ℝ) : Prop :=
  ∃ x x' y, K x y ≠ K x' y

theorem genuinelyCoupled_iff (K : X → Y → ℝ) :
    GenuinelyCoupled K ↔ ∃ x x' y, K x y ≠ K x' y := Iff.rfl

/-- Finite Markov normalization. -/
def IsMarkovKernel {A : Type*} [Fintype A] (P : A → A → ℝ) : Prop :=
  (∀ a b, 0 ≤ P a b) ∧ ∀ a, ∑ b, P a b = 1

/-- Detailed balance for a finite law and kernel. -/
def IsReversible {A : Type*} (μ : A → ℝ) (P : A → A → ℝ) : Prop :=
  ∀ a b, μ a * P a b = μ b * P b a

/-- First update the old state and then sample the new detail conditional. -/
def fineSkeleton (P : X → X → ℝ) (K : X → Y → ℝ) :
    X × Y → X × Y → ℝ :=
  fun p q => P p.1 q.1 * K q.1 q.2

theorem fineSkeleton_markov (P : X → X → ℝ) (K : X → Y → ℝ)
    (hP : IsMarkovKernel P) (hKnonneg : ∀ x y, 0 ≤ K x y)
    (hK : ∀ x, ∑ y, K x y = 1) :
    IsMarkovKernel (fineSkeleton P K) := by
  constructor
  · intro p q
    exact mul_nonneg (hP.1 _ _) (hKnonneg _ _)
  · intro p
    rw [Fintype.sum_prod_type]
    simp_rw [fineSkeleton, ← Finset.mul_sum, hK, mul_one]
    exact hP.2 p.1

/-- Reversibility of the old skeleton lifts exactly to the fine law. -/
theorem fineSkeleton_reversible (μ : X → ℝ) (P : X → X → ℝ)
    (K : X → Y → ℝ) (hrev : IsReversible μ P) :
    IsReversible (fineLaw μ K) (fineSkeleton P K) := by
  intro p q
  simp only [fineLaw, fineSkeleton]
  calc
    μ p.1 * K p.1 p.2 * (P p.1 q.1 * K q.1 q.2) =
        (μ p.1 * P p.1 q.1) * (K p.1 p.2 * K q.1 q.2) := by ring
    _ = (μ q.1 * P q.1 p.1) * (K p.1 p.2 * K q.1 q.2) := by
      rw [hrev p.1 q.1]
    _ = μ q.1 * K q.1 q.2 * (P q.1 p.1 * K p.1 p.2) := by ring

/-- Action of a finite transition kernel on observables. -/
def kernelAction {A : Type*} [Fintype A]
    (P : A → A → ℝ) (f : A → ℝ) (a : A) : ℝ :=
  ∑ b, P a b * f b

/-- The lifted skeleton intertwines every pullback old observable exactly. -/
theorem fineSkeleton_pullback (P : X → X → ℝ) (K : X → Y → ℝ)
    (hK : ∀ x, ∑ y, K x y = 1) (f : X → ℝ) (p : X × Y) :
    kernelAction (fineSkeleton P K) (fun q => f q.1) p =
      kernelAction P f p.1 := by
  unfold kernelAction
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  calc
    ∑ y, fineSkeleton P K p (x, y) * f x =
        ∑ y, (P p.1 x * f x) * K x y := by
          apply Finset.sum_congr rfl
          intro y _
          simp only [fineSkeleton]
          ring
    _ = (P p.1 x * f x) * ∑ y, K x y := by rw [Finset.mul_sum]
    _ = P p.1 x * f x := by rw [hK x, mul_one]

section LineTransport

variable {R : Type*} [CommRing R]
variable {m n : Type*} [Fintype m] [Fintype n]
variable [DecidableEq m] [DecidableEq n]

/-- Determinants multiply under direct-sum shell extension. -/
theorem det_blockShell (D : Matrix m m R) (E : Matrix n n R) :
    (Matrix.fromBlocks D 0 0 E).det = D.det * E.det := by
  rw [Matrix.det_fromBlocks_zero₂₁]

/-- Determinant-one left/right shell transports preserve the product line. -/
theorem det_shellTransport (D : Matrix m m R) (E : Matrix n n R)
    (L Rm : Matrix (m ⊕ n) (m ⊕ n) R)
    (hL : L.det = 1) (hR : Rm.det = 1) :
    (L * Matrix.fromBlocks D 0 0 E * Rm).det = D.det * E.det := by
  rw [Matrix.det_mul, Matrix.det_mul, hL, hR, one_mul, mul_one,
    det_blockShell]

/-- The explicit unitriangular shell maps used in RP.15 have determinant one. -/
theorem det_unitriangular_shell_maps
    (A : Matrix m n R) (B : Matrix n m R) :
    (Matrix.fromBlocks (1 : Matrix m m R) A 0 (1 : Matrix n n R)).det = 1 ∧
      (Matrix.fromBlocks (1 : Matrix m m R) 0 B (1 : Matrix n n R)).det = 1 := by
  constructor
  · rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]
  · rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, one_mul]

/-- A real Pfaffian-line section is a chosen square root of the determinant,
with its sign retained rather than discarded. -/
structure RealPfaffianSection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) where
  value : ℝ
  square_eq_det : value ^ 2 = A.det

/-- Tensor product of oriented Pfaffian sections under a direct-sum shell. -/
def RealPfaffianSection.directSum
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix n n ℝ}
    (p : RealPfaffianSection A) (q : RealPfaffianSection B) :
    RealPfaffianSection (Matrix.fromBlocks A 0 0 B) where
  value := p.value * q.value
  square_eq_det := by
    rw [det_blockShell, mul_pow, p.square_eq_det, q.square_eq_det]

@[simp] theorem RealPfaffianSection.directSum_value
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix n n ℝ}
    (p : RealPfaffianSection A) (q : RealPfaffianSection B) :
    (p.directSum q).value = p.value * q.value := rfl

/-- Divisor membership of the product Pfaffian is exactly the union of the
two divisor memberships. -/
theorem RealPfaffianSection.directSum_value_eq_zero_iff
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix n n ℝ}
    (p : RealPfaffianSection A) (q : RealPfaffianSection B) :
    (p.directSum q).value = 0 ↔ p.value = 0 ∨ q.value = 0 := by
  simp

/-- A block shell acts independently on its old and detail coordinates. -/
theorem blockShell_mulVec
    (D : Matrix m m R) (E : Matrix n n R)
    (x : m → R) (y : n → R) :
    Matrix.fromBlocks D 0 0 E *ᵥ Sum.elim x y =
      Sum.elim (D *ᵥ x) (E *ᵥ y) := by
  ext i
  cases i with
  | inl i => simp [Matrix.fromBlocks_mulVec]
  | inr i => simp [Matrix.fromBlocks_mulVec]

/-- Kernel transport under direct sum: a shell vector is null exactly when
both its old and detail components are null. -/
theorem blockShell_mulVec_eq_zero_iff
    (D : Matrix m m R) (E : Matrix n n R)
    (x : m → R) (y : n → R) :
    Matrix.fromBlocks D 0 0 E *ᵥ Sum.elim x y = 0 ↔
      D *ᵥ x = 0 ∧ E *ᵥ y = 0 := by
  rw [blockShell_mulVec]
  constructor
  · intro h
    constructor
    · funext i
      exact congrFun h (Sum.inl i)
    · funext i
      exact congrFun h (Sum.inr i)
  · rintro ⟨hx, hy⟩
    rw [hx, hy]
    funext i
    cases i <;> rfl

/-- Multiplication by an invertible left shell map does not alter the null
equation. -/
theorem left_mulVec_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L M : Matrix ι ι R) [Invertible L] (v : ι → R) :
    (L * M) *ᵥ v = 0 ↔ M *ᵥ v = 0 := by
  rw [← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have h' := congrArg (fun w => L⁻¹ *ᵥ w) h
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] at h'
    simpa using h'
  · intro h
    rw [h]
    simp

/-- Full invertible left/right transport identifies the new kernel equation
with the old block equation after the right coordinate change. -/
theorem transportedShell_mulVec_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L M Rm : Matrix ι ι R) [Invertible L] [Invertible Rm]
    (v : ι → R) :
    (L * M * Rm) *ᵥ v = 0 ↔ M *ᵥ (Rm *ᵥ v) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  exact left_mulVec_eq_zero_iff L M (Rm *ᵥ v)

/-- The dual null equation, hence the algebraic cokernel, is transported by
the transposed invertible shell maps in the opposite order. -/
theorem transportedShell_transpose_mulVec_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L M Rm : Matrix ι ι R) [Invertible L] [Invertible Rm]
    (w : ι → R) :
    (L * M * Rm)ᵀ *ᵥ w = 0 ↔ Mᵀ *ᵥ (Lᵀ *ᵥ w) = 0 := by
  haveI : Invertible Rmᵀ := Matrix.invertibleTranspose Rm
  simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using
    (transportedShell_mulVec_eq_zero_iff Rmᵀ Mᵀ Lᵀ w)

/-- Divisor orders add under a nonzero polynomial product. -/
theorem divisorOrder_product (p q : Polynomial ℝ) (a : ℝ) (hpq : p * q ≠ 0) :
    Polynomial.rootMultiplicity a (p * q) =
      Polynomial.rootMultiplicity a p + Polynomial.rootMultiplicity a q :=
  Polynomial.rootMultiplicity_mul hpq

/-- Consequently the mod-two crossing parity of a product is the sum of the
two crossing parities. -/
theorem crossingParity_product (p q : Polynomial ℝ) (a : ℝ) (hpq : p * q ≠ 0) :
    Polynomial.rootMultiplicity a (p * q) % 2 =
      (Polynomial.rootMultiplicity a p % 2 +
        Polynomial.rootMultiplicity a q % 2) % 2 := by
  rw [divisorOrder_product p q a hpq]
  exact Nat.add_mod _ _ 2

end LineTransport

end FiniteProjectiveKernelTransport
end NCG
