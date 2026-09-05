/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Semisimplicity of finite complex matrix star subalgebras

Every star subalgebra of a finite complex matrix algebra is semisimple. The
proof uses the nondegenerate trace pairing. For a left ideal, the orthogonal
complement of its adjoint right ideal is again a left ideal; positivity of the
Hilbert--Schmidt square makes the intersection trivial, and finite-dimensional
rank-nullity makes the sum exhaustive.

The construction retains the complementary left ideal, not merely the
resulting semisimple-ring instance.
-/

noncomputable section

open Matrix
open scoped ComplexOrder

namespace NCG
namespace FiniteComplexStarSubalgebraSemisimplicity

variable {n : Type*} [Fintype n] [DecidableEq n]

def tracePairing (S : StarSubalgebra ℂ (Matrix n n ℂ)) :
    LinearMap.BilinForm ℂ S :=
  LinearMap.mk₂ ℂ
    (fun x y => Matrix.trace (x.1 * y.1))
    (by intro x y z; simp [Matrix.add_mul])
    (by intro c x y; simp)
    (by intro x y z; simp [Matrix.mul_add])
    (by intro c x y; simp)

@[simp] theorem tracePairing_apply
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (x y : S) :
    tracePairing S x y = Matrix.trace (x.1 * y.1) := rfl

theorem tracePairing_isSymm (S : StarSubalgebra ℂ (Matrix n n ℂ)) :
    (tracePairing S).IsSymm := by
  constructor
  intro x y
  exact Matrix.trace_mul_comm x.1 y.1

theorem tracePairing_nondegenerate (S : StarSubalgebra ℂ (Matrix n n ℂ)) :
    (tracePairing S).Nondegenerate := by
  apply (tracePairing_isSymm S).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  have h := hx (star x)
  simp only [tracePairing_apply] at h
  have hmatrix : x.1 = 0 := by
    rw [show (star x).1 = x.1ᴴ by rfl] at h
    exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp h
  exact Subtype.ext hmatrix

def adjointSubspace
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (I : Submodule S S) :
    Submodule ℂ S :=
  Submodule.map (starLinearEquiv ℂ).toLinearMap (I.restrictScalars ℂ)

theorem finrank_adjointSubspace
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (I : Submodule S S) :
    Module.finrank ℂ (adjointSubspace S I) =
      Module.finrank ℂ (I.restrictScalars ℂ) := by
  let e : (I.restrictScalars ℂ) ≃ₛₗ[starRingEnd ℂ]
      (adjointSubspace S I) :=
    (starLinearEquiv ℂ).submoduleMap (I.restrictScalars ℂ)
  have hbij : Function.Bijective (starRingEnd ℂ) := by
    constructor
    · intro x y h
      calc
        x = star (star x) := (star_star x).symm
        _ = star (star y) := congrArg star (by simpa only [starRingEnd_apply] using h)
        _ = y := star_star y
    · intro x
      exact ⟨star x, by simpa only [starRingEnd_apply] using star_star x⟩
  have hrank := lift_rank_eq_of_equiv_equiv (starRingEnd ℂ)
    e.toAddEquiv hbij (fun c x => e.map_smulₛₗ c x)
  have hnat := congrArg Cardinal.toNat hrank
  change Cardinal.toNat (Module.rank ℂ (adjointSubspace S I)) =
    Cardinal.toNat (Module.rank ℂ (I.restrictScalars ℂ))
  simpa only [Cardinal.toNat_lift] using hnat.symm

theorem star_mem_adjointSubspace
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (I : Submodule S S)
    {x : S} (hx : x ∈ I) :
    star x ∈ adjointSubspace S I := by
  refine ⟨x, ?_, rfl⟩
  exact hx

theorem adjointSubspace_mul_mem
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (I : Submodule S S)
    {z : S} (hz : z ∈ adjointSubspace S I) (a : S) :
    z * a ∈ adjointSubspace S I := by
  rcases hz with ⟨y, hy, rfl⟩
  refine ⟨star a * y, ?_, ?_⟩
  · exact I.smul_mem (star a) hy
  · simp [star_mul]

def leftIdealOrthogonalComplement
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (I : Submodule S S) :
    Submodule S S where
  carrier := {x | ∀ z, z ∈ adjointSubspace S I →
    tracePairing S z x = 0}
  zero_mem' := by
    intro z hz
    simp
  add_mem' := by
    intro x y hx hy z hz
    have hx0 := hx z hz
    have hy0 := hy z hz
    change Matrix.trace (z.1 * x.1) = 0 at hx0
    change Matrix.trace (z.1 * y.1) = 0 at hy0
    change Matrix.trace (z.1 * (x.1 + y.1)) = 0
    rw [Matrix.mul_add, Matrix.trace_add, hx0, hy0, add_zero]
  smul_mem' := by
    intro a x hx z hz
    have hza := adjointSubspace_mul_mem S I hz a
    have hzero := hx (z * a) hza
    change Matrix.trace ((z.1 * a.1) * x.1) = 0 at hzero
    change Matrix.trace (z.1 * (a.1 * x.1)) = 0
    simpa only [Matrix.mul_assoc] using hzero

theorem restrictScalars_leftIdealOrthogonalComplement
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (I : Submodule S S) :
    (leftIdealOrthogonalComplement S I).restrictScalars ℂ =
      (tracePairing S).orthogonal (adjointSubspace S I) := by
  ext x
  rfl

theorem leftIdealOrthogonalComplement_disjoint
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (I : Submodule S S) :
    Disjoint (I.restrictScalars ℂ)
      ((leftIdealOrthogonalComplement S I).restrictScalars ℂ) := by
  rw [restrictScalars_leftIdealOrthogonalComplement]
  rw [Submodule.disjoint_def]
  intro x hxI hxQ
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hxQ
  have hstar : star x ∈ adjointSubspace S I :=
    star_mem_adjointSubspace S I hxI
  have hzero := hxQ (star x) hstar
  simp only [tracePairing_apply] at hzero
  have hmatrix : x.1 = 0 := by
    rw [show (star x).1 = x.1ᴴ by rfl] at hzero
    exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hzero
  exact Subtype.ext hmatrix

theorem leftIdealOrthogonalComplement_isCompl_complex
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (I : Submodule S S) :
    IsCompl (I.restrictScalars ℂ)
      ((leftIdealOrthogonalComplement S I).restrictScalars ℂ) := by
  letI : FiniteDimensional ℂ S :=
    FiniteDimensional.of_injective
      (Subalgebra.val S.toSubalgebra).toLinearMap
      (fun _ _ h => Subtype.ext h)
  rw [restrictScalars_leftIdealOrthogonalComplement]
  let J := adjointSubspace S I
  let Q := (tracePairing S).orthogonal J
  change IsCompl (I.restrictScalars ℂ) Q
  have hdis : Disjoint (I.restrictScalars ℂ) Q := by
    simpa only [Q, J, restrictScalars_leftIdealOrthogonalComplement] using
      leftIdealOrthogonalComplement_disjoint S I
  refine ⟨hdis, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_finrank_eq
  have hJ : Module.finrank ℂ J =
      Module.finrank ℂ (I.restrictScalars ℂ) := by
    simpa only [J] using finrank_adjointSubspace S I
  calc
    Module.finrank ℂ ↥((I.restrictScalars ℂ) ⊔ Q) =
        Module.finrank ℂ ↥((I.restrictScalars ℂ) ⊔ Q) +
          Module.finrank ℂ ↥((I.restrictScalars ℂ) ⊓ Q) := by
            simp [hdis.eq_bot]
    _ = Module.finrank ℂ (I.restrictScalars ℂ) +
          Module.finrank ℂ Q :=
      Submodule.finrank_sup_add_finrank_inf_eq
        (I.restrictScalars ℂ) Q
    _ = Module.finrank ℂ (I.restrictScalars ℂ) +
          (Module.finrank ℂ S - Module.finrank ℂ J) := by
      rw [show Module.finrank ℂ Q =
        Module.finrank ℂ S - Module.finrank ℂ J by
          exact LinearMap.BilinForm.finrank_orthogonal
            (tracePairing_nondegenerate S) J]
    _ = Module.finrank ℂ S := by
      rw [hJ, Nat.add_sub_of_le
        (Submodule.finrank_le (I.restrictScalars ℂ))]

theorem leftIdealOrthogonalComplement_isCompl
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (I : Submodule S S) :
    IsCompl I (leftIdealOrthogonalComplement S I) := by
  exact (Submodule.isCompl_restrictScalars_iff ℂ).mp
    (leftIdealOrthogonalComplement_isCompl_complex S I)

theorem starSubalgebra_isSemisimpleRing
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) :
    IsSemisimpleRing S := by
  apply (isSemisimpleModule_iff S S).mpr
  exact ⟨fun I => ⟨leftIdealOrthogonalComplement S I,
      leftIdealOrthogonalComplement_isCompl S I⟩⟩

end FiniteComplexStarSubalgebraSemisimplicity
end NCG
