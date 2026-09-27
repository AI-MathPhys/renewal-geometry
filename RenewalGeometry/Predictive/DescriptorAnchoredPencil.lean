/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.DescriptorLaurentUniqueness

/-!
# Right-multiplication equivalence and the anchored pencil of a descriptor realization

Paper `predictive_spectral_geometry`, `cor:supp-all-rational` (partial: the first step of the
Weierstrass primary decomposition, "the pencil of any regular finite descriptor realization has a
primary decomposition at infinity and at finite spectral points").

* `DescriptorRealization.rightMul`: the **right-multiplication equivalence**
  `(E, A, Γ, J) ↦ (E V, A V, Γ, J V)` by an invertible `J`-self-adjoint `V` (`J V = V* J`): it is
  again a regular Pontryagin descriptor realization with the same source and the same transfer
  function at every regular point (`rightMul_transfer`).
* `DescriptorRealization.resolventAt`: for a **real regular point** `t₀` of the pencil, the
  resolvent `K = (A - t₀ E)⁻¹` is `J`-self-adjoint (`J_mul_resolventAt`), so that `J K` is a
  Gram operator and `T = E K` is `J K`-self-adjoint: `DescriptorRealization.anchored` is the
  finite Pontryagin realization `(T, Γ, J K)` and the transfer function of `D` is the
  Möbius-transformed transfer function `Γ* (J K) (1 - (z - t₀) T)⁻¹ Γ` of it
  (`transfer_eq_anchored`, `pencil_mul_resolventAt`).
* `DescriptorRealization.anchoredDescriptor`: the right-multiplication `D.rightMul K` of `D` by
  the resolvent, a descriptor realization with **commuting pencil** `E' = T`, `A' = 1 + t₀ T`
  (`anchoredDescriptor_A`), the same source and the same transfer function
  (`anchoredDescriptor_transfer`).  The primary decomposition of `T` at `0`
  (`Algebra/RootSubspaceProjection.lean`, `Krein/JSelfAdjointRootSpaces.lean`) splits this
  anchored pencil into its infinity and finite blocks.
* `DescriptorRealization.exists_real_regular`: a regular pencil on a finite-dimensional state space
  has a real regular point (the determinant of `A - z E` is a nonzero polynomial in `z`).
-/

open scoped InnerProductSpace InnerProduct
open Module

noncomputable section

namespace RenewalGeometry

/-- The inverse of a product of units, in a not necessarily commutative monoid with zero. -/
theorem inverse_mul_of_isUnit {R : Type*} [MonoidWithZero R] {a b : R} (ha : IsUnit a)
    (hb : IsUnit b) : Ring.inverse (a * b) = Ring.inverse b * Ring.inverse a := by
  rw [Ring.inverse_of_isUnit ha, Ring.inverse_of_isUnit hb, ← Units.val_mul, ← mul_inv_rev]
  have : a * b = ((ha.unit * hb.unit : Rˣ) : R) := by
    rw [Units.val_mul, ha.unit_spec, hb.unit_spec]
  rw [this, Ring.inverse_unit]

/-- The inverse of the inverse of a unit. -/
theorem inverse_inverse_of_isUnit {R : Type*} [MonoidWithZero R] {a : R} (ha : IsUnit a) :
    Ring.inverse (Ring.inverse a) = a := by
  rw [Ring.inverse_of_isUnit ha, Ring.inverse_unit, inv_inv, ha.unit_spec]

namespace DescriptorRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (D : DescriptorRealization H N)

/-! ## Right-multiplication equivalence -/

/-- **The right-multiplication equivalence** `(E, A, Γ, J) ↦ (E V, A V, Γ, J V)` by an invertible
`J`-self-adjoint operator `V` (`J V = V* J`). -/
def rightMul (V : N →L[ℂ] N) (hV : IsUnit V) (hJV : D.J * V = star V * D.J) :
    DescriptorRealization H N where
  E := D.E * V
  A := D.A * V
  Γ := D.Γ
  J := D.J * V
  J_selfAdjoint := by
    rw [IsSelfAdjoint, star_mul, D.J_selfAdjoint.star_eq, hJV]
  J_isUnit := D.J_isUnit.mul hV
  J_mul_A := by
    calc D.J * V * (D.A * V) = star V * D.J * D.A * V := by rw [hJV]; simp only [mul_assoc]
      _ = star V * (star D.A * D.J) * V := by rw [mul_assoc (star V), D.J_mul_A]
      _ = star (D.A * V) * (D.J * V) := by rw [star_mul]; simp only [mul_assoc]
  J_mul_E := by
    calc D.J * V * (D.E * V) = star V * D.J * D.E * V := by rw [hJV]; simp only [mul_assoc]
      _ = star V * (star D.E * D.J) * V := by rw [mul_assoc (star V), D.J_mul_E]
      _ = star (D.E * V) * (D.J * V) := by rw [star_mul]; simp only [mul_assoc]
  regular := by
    obtain ⟨z, hz⟩ := D.regular
    exact ⟨z, by rw [← smul_mul_assoc, ← sub_mul]; exact hz.mul hV⟩

variable (V : N →L[ℂ] N) (hV : IsUnit V) (hJV : D.J * V = star V * D.J)

theorem rightMul_E : (D.rightMul V hV hJV).E = D.E * V := rfl
theorem rightMul_A : (D.rightMul V hV hJV).A = D.A * V := rfl
theorem rightMul_Γ : (D.rightMul V hV hJV).Γ = D.Γ := rfl
theorem rightMul_J : (D.rightMul V hV hJV).J = D.J * V := rfl

/-- The pencil of the right-multiplied realization is `(A - z E) V`. -/
theorem rightMul_pencil (z : ℂ) :
    (D.rightMul V hV hJV).A - z • (D.rightMul V hV hJV).E = (D.A - z • D.E) * V := by
  rw [rightMul_A, rightMul_E, ← smul_mul_assoc, ← sub_mul]

/-- **Right multiplication preserves the transfer function** at every regular point. -/
theorem rightMul_transfer {z : ℂ} (hz : IsUnit (D.A - z • D.E)) :
    (D.rightMul V hV hJV).transfer z = D.transfer z := by
  unfold transfer
  rw [rightMul_pencil, rightMul_Γ, rightMul_J, inverse_mul_of_isUnit hz hV]
  have key : D.J * V * (Ring.inverse V * Ring.inverse (D.A - z • D.E)) =
      D.J * Ring.inverse (D.A - z • D.E) := by
    rw [mul_assoc, ← mul_assoc V, Ring.mul_inverse_cancel V hV, one_mul]
  ext h
  have := congrArg (fun T : N →L[ℂ] N => T (D.Γ h)) key
  simp only [mul_apply_eq_comp] at this
  simp only [ContinuousLinearMap.comp_apply, mul_apply_eq_comp, this]

/-! ## The anchored pencil at a real regular point -/

variable (t₀ : ℝ) (ht₀ : IsUnit (D.A - (t₀ : ℂ) • D.E))

/-- The resolvent `K = (A - t₀ E)⁻¹` at a real regular point. -/
def resolventAt : N →L[ℂ] N := Ring.inverse (D.A - (t₀ : ℂ) • D.E)

/-- `J (A - t₀ E) = (A - t₀ E)* J` for real `t₀`. -/
theorem J_mul_pencil_real :
    D.J * (D.A - (t₀ : ℂ) • D.E) = star (D.A - (t₀ : ℂ) • D.E) * D.J := by
  rw [mul_sub, mul_smul_comm, star_sub, star_smul, Complex.star_def, Complex.conj_ofReal, sub_mul,
    smul_mul_assoc, D.J_mul_A, D.J_mul_E]

include ht₀

/-- **The resolvent at a real regular point is `J`-self-adjoint**: `J K = K* J`. -/
theorem J_mul_resolventAt :
    D.J * D.resolventAt t₀ = star (D.resolventAt t₀) * D.J := by
  set X := D.A - (t₀ : ℂ) • D.E with hX
  set K := D.resolventAt t₀ with hK
  have hXK : X * K = 1 := Ring.mul_inverse_cancel X ht₀
  have hJX : star X * D.J = D.J * X := (D.J_mul_pencil_real t₀).symm
  calc D.J * K = star (X * K) * D.J * K := by rw [hXK, star_one, one_mul]
    _ = star K * (star X * D.J) * K := by rw [star_mul]; simp only [mul_assoc]
    _ = star K * D.J * (X * K) := by rw [hJX]; simp only [mul_assoc]
    _ = star K * D.J := by rw [hXK, mul_one]

theorem isUnit_resolventAt : IsUnit (D.resolventAt t₀) := by
  rw [resolventAt, Ring.inverse_of_isUnit ht₀]
  exact Units.isUnit _

/-- `A K = 1 + t₀ E K`. -/
theorem A_mul_resolventAt : D.A * D.resolventAt t₀ = 1 + (t₀ : ℂ) • (D.E * D.resolventAt t₀) := by
  have h : (D.A - (t₀ : ℂ) • D.E) * D.resolventAt t₀ = 1 := Ring.mul_inverse_cancel _ ht₀
  rw [sub_mul, smul_mul_assoc] at h
  rw [← h, sub_add_cancel]

/-- **The anchored pencil**: `(A - z E) K = 1 - (z - t₀) E K`. -/
theorem pencil_mul_resolventAt (z : ℂ) :
    (D.A - z • D.E) * D.resolventAt t₀ = 1 - (z - t₀ : ℂ) • (D.E * D.resolventAt t₀) := by
  rw [sub_mul, D.A_mul_resolventAt t₀ ht₀, smul_mul_assoc, sub_smul]
  abel

/-- **The anchored Pontryagin realization** `(T, Γ, J K)` with `T = E K`, `K = (A - t₀ E)⁻¹`,
at a real regular point `t₀`: `J K` is a Gram operator and `T` is `J K`-self-adjoint. -/
def anchored : PontryaginRealization H N where
  A := D.E * D.resolventAt t₀
  Γ := D.Γ
  J := D.J * D.resolventAt t₀
  J_selfAdjoint := by
    rw [IsSelfAdjoint, star_mul, D.J_selfAdjoint.star_eq, D.J_mul_resolventAt t₀ ht₀]
  J_isUnit := D.J_isUnit.mul (D.isUnit_resolventAt t₀ ht₀)
  J_mul_A := by
    calc D.J * D.resolventAt t₀ * (D.E * D.resolventAt t₀)
        = star (D.resolventAt t₀) * D.J * D.E * D.resolventAt t₀ := by
          rw [D.J_mul_resolventAt t₀ ht₀]; simp only [mul_assoc]
      _ = star (D.resolventAt t₀) * (star D.E * D.J) * D.resolventAt t₀ := by
          rw [mul_assoc (star _), D.J_mul_E]
      _ = star (D.E * D.resolventAt t₀) * (D.J * D.resolventAt t₀) := by
          rw [star_mul]; simp only [mul_assoc]

theorem anchored_A : (D.anchored t₀ ht₀).A = D.E * D.resolventAt t₀ := rfl
theorem anchored_Γ : (D.anchored t₀ ht₀).Γ = D.Γ := rfl
theorem anchored_J : (D.anchored t₀ ht₀).J = D.J * D.resolventAt t₀ := rfl

/-- The anchored pencil `1 - (z - t₀) T` is invertible exactly at the regular points of `D`. -/
theorem isUnit_anchored_pencil {z : ℂ} (hz : IsUnit (D.A - z • D.E)) :
    IsUnit (1 - (z - t₀ : ℂ) • (D.anchored t₀ ht₀).A) := by
  rw [anchored_A, ← D.pencil_mul_resolventAt t₀ ht₀]
  exact hz.mul (D.isUnit_resolventAt t₀ ht₀)

/-- **The transfer function of `D` through the anchored realization**:
`Γ* J (A - z E)⁻¹ Γ = Γ* (J K) (1 - (z - t₀) T)⁻¹ Γ` at every regular point `z`. -/
theorem transfer_eq_anchored {z : ℂ} (hz : IsUnit (D.A - z • D.E)) :
    D.transfer z = (D.anchored t₀ ht₀).sandwich
      (Ring.inverse (1 - (z - t₀ : ℂ) • (D.anchored t₀ ht₀).A)) := by
  rw [PontryaginRealization.sandwich_apply, anchored_A, anchored_Γ, anchored_J,
    ← D.pencil_mul_resolventAt t₀ ht₀, inverse_mul_of_isUnit hz (D.isUnit_resolventAt t₀ ht₀),
    resolventAt, inverse_inverse_of_isUnit ht₀]
  unfold transfer
  have key : D.J * Ring.inverse (D.A - (t₀ : ℂ) • D.E) *
      ((D.A - (t₀ : ℂ) • D.E) * Ring.inverse (D.A - z • D.E)) =
      D.J * Ring.inverse (D.A - z • D.E) := by
    rw [mul_assoc, ← mul_assoc (Ring.inverse _), Ring.inverse_mul_cancel _ ht₀, one_mul]
  ext h
  have := congrArg (fun T : N →L[ℂ] N => T (D.Γ h)) key
  simp only [mul_apply_eq_comp] at this
  simp only [ContinuousLinearMap.comp_apply, mul_apply_eq_comp, this]

/-! ## The anchored descriptor realization: a commuting pencil -/

/-- **The anchored descriptor realization** `D.rightMul K`: the right multiplication of `D` by
the resolvent `K = (A - t₀ E)⁻¹` at a real regular point, `(E K, A K, Γ, J K)`. -/
def anchoredDescriptor : DescriptorRealization H N :=
  D.rightMul (D.resolventAt t₀) (D.isUnit_resolventAt t₀ ht₀) (D.J_mul_resolventAt t₀ ht₀)

theorem anchoredDescriptor_E : (D.anchoredDescriptor t₀ ht₀).E = (D.anchored t₀ ht₀).A := rfl
theorem anchoredDescriptor_Γ : (D.anchoredDescriptor t₀ ht₀).Γ = D.Γ := rfl
theorem anchoredDescriptor_J : (D.anchoredDescriptor t₀ ht₀).J = (D.anchored t₀ ht₀).J := rfl

/-- **The anchored pencil commutes**: `A' = 1 + t₀ E'`, so that `A' - z E' = 1 - (z - t₀) T`. -/
theorem anchoredDescriptor_A :
    (D.anchoredDescriptor t₀ ht₀).A = 1 + (t₀ : ℂ) • (D.anchoredDescriptor t₀ ht₀).E :=
  D.A_mul_resolventAt t₀ ht₀

theorem anchoredDescriptor_pencil (z : ℂ) :
    (D.anchoredDescriptor t₀ ht₀).A - z • (D.anchoredDescriptor t₀ ht₀).E =
      1 - (z - t₀ : ℂ) • (D.anchored t₀ ht₀).A := by
  rw [anchoredDescriptor_A, anchoredDescriptor_E, sub_smul]
  abel

/-- The anchored descriptor realization has the same transfer function as `D` at every regular
point. -/
theorem anchoredDescriptor_transfer {z : ℂ} (hz : IsUnit (D.A - z • D.E)) :
    (D.anchoredDescriptor t₀ ht₀).transfer z = D.transfer z :=
  D.rightMul_transfer _ _ _ hz

/-- The anchored descriptor realization is regular at `t₀` with unit pencil `A' - t₀ E' = 1`. -/
theorem anchoredDescriptor_pencil_self :
    (D.anchoredDescriptor t₀ ht₀).A - (t₀ : ℂ) • (D.anchoredDescriptor t₀ ht₀).E = 1 := by
  rw [anchoredDescriptor_pencil, sub_self, zero_smul, sub_zero]

end DescriptorRealization

/-! ## Existence of a real regular point -/

section RealRegular

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
  [FiniteDimensional ℂ N]

open Polynomial in
/-- The determinant polynomial `p(X) = det (A - X E)` of a pencil, computed in a basis. -/
def pencilPolynomial (E A : N →L[ℂ] N) : ℂ[X] :=
  (Matrix.of fun i j =>
    C (LinearMap.toMatrix (Module.finBasis ℂ N) (Module.finBasis ℂ N) (A : N →ₗ[ℂ] N) i j) -
      X * C (LinearMap.toMatrix (Module.finBasis ℂ N) (Module.finBasis ℂ N)
        (E : N →ₗ[ℂ] N) i j)).det

/-- `p(z) = det (A - z E)`. -/
theorem eval_pencilPolynomial (E A : N →L[ℂ] N) (z : ℂ) :
    (pencilPolynomial E A).eval z = LinearMap.det ((A - z • E : N →L[ℂ] N) : N →ₗ[ℂ] N) := by
  set b := Module.finBasis ℂ N
  rw [pencilPolynomial, ← Polynomial.coe_evalRingHom, RingHom.map_det, ← LinearMap.det_toMatrix b]
  congr 1
  ext i j
  simp only [b, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Polynomial.coe_evalRingHom,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_smul, map_sub, map_smul,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

/-- A pencil is invertible at `z` iff `z` is not a root of its determinant polynomial. -/
theorem isUnit_pencil_iff (E A : N →L[ℂ] N) (z : ℂ) :
    IsUnit (A - z • E) ↔ (pencilPolynomial E A).eval z ≠ 0 := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, eval_pencilPolynomial]

/-- **A regular pencil on a finite-dimensional space has a real regular point**: the determinant
polynomial is nonzero, hence has finitely many roots. -/
theorem exists_real_regular_of_isUnit {E A : N →L[ℂ] N} {z₀ : ℂ} (hz₀ : IsUnit (A - z₀ • E)) :
    ∃ t : ℝ, IsUnit (A - (t : ℂ) • E) := by
  have hp : pencilPolynomial E A ≠ 0 := by
    intro h
    have := (isUnit_pencil_iff E A z₀).mp hz₀
    rw [h, Polynomial.eval_zero] at this
    exact this rfl
  obtain ⟨z, ⟨t, rfl⟩, hz⟩ := (Set.infinite_range_of_injective Complex.ofReal_injective)
    |>.exists_notMem_finset (pencilPolynomial E A).roots.toFinset
  refine ⟨t, (isUnit_pencil_iff E A t).mpr fun h => hz ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
  exact h

/-- **Every regular Pontryagin descriptor realization has a real regular point.** -/
theorem DescriptorRealization.exists_real_regular {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (D : DescriptorRealization H N) :
    ∃ t : ℝ, IsUnit (D.A - (t : ℂ) • D.E) :=
  let ⟨_, hz₀⟩ := D.regular
  exists_real_regular_of_isUnit hz₀

end RealRegular

end RenewalGeometry

end
