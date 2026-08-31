/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTMonoidalTransport

/-!
# Flat word-basis monoidal transport

This file instantiates the monoidal residual at an actual finite word basis.
Its columns are the unit, involution, and pairwise product defects.  Vanishing
of the residual Gram forces those identities on the basis, hence everywhere
by finite basis expansion, and produces the unique trace-preserving unital
star-algebra equivalence whose L2 extension is the proposed unitary.
-/

noncomputable section

open Matrix
open scoped ComplexOrder

namespace NCG
namespace WordBasisMonoidalTransport

variable {A B ι κ : Type*}
  [NormedRing A] [StarRing A] [InnerProductSpace ℂ A] [StarModule ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NormedRing B] [StarRing B] [InnerProductSpace ℂ B] [StarModule ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Unit, star, and product columns of the finite monoidal residual. -/
abbrev MonoidalColumn (ι : Type*) := Unit ⊕ ι ⊕ (ι × ι)

/-- The literal defect vector attached to one residual column. -/
def monoidalResidual (w : Module.Basis ι ℂ A) (U : A ≃ₗᵢ[ℂ] B) :
    MonoidalColumn ι → B
  | Sum.inl _ => U 1 - 1
  | Sum.inr (Sum.inl i) => U (star (w i)) - star (U (w i))
  | Sum.inr (Sum.inr (i, j)) => U (w i * w j) - U (w i) * U (w j)

/-- Coordinate synthesis of all monoidal defects in an orthonormal output
basis. -/
def residualSynthesis (w : Module.Basis ι ℂ A) (e : OrthonormalBasis κ ℂ B)
    (U : A ≃ₗᵢ[ℂ] B) : Matrix κ (MonoidalColumn ι) ℂ :=
  fun k c => (e.repr (monoidalResidual w U c)).ofLp k

/-- The monoidal innovation Gram. -/
def monoidalInnovation (w : Module.Basis ι ℂ A) (e : OrthonormalBasis κ ℂ B)
    (U : A ≃ₗᵢ[ℂ] B) : Matrix (MonoidalColumn ι) (MonoidalColumn ι) ℂ :=
  (residualSynthesis w e U)ᴴ * residualSynthesis w e U

theorem residualSynthesis_eq_zero_iff
    (w : Module.Basis ι ℂ A) (e : OrthonormalBasis κ ℂ B)
    (U : A ≃ₗᵢ[ℂ] B) :
    residualSynthesis w e U = 0 ↔ ∀ c, monoidalResidual w U c = 0 := by
  constructor
  · intro h c
    apply e.repr.injective
    apply WithLp.ofLp_injective 2
    funext k
    have hk := congrFun (congrFun h k) c
    simpa [residualSynthesis] using hk
  · intro h
    ext k c
    have hc := congrArg (fun z : B => (e.repr z).ofLp k) (h c)
    simpa [residualSynthesis] using hc

/-- The innovation is positive and vanishes exactly when every literal
word-basis defect vanishes. -/
theorem monoidalInnovation_posSemidef_and_zero_iff
    (w : Module.Basis ι ℂ A) (e : OrthonormalBasis κ ℂ B)
    (U : A ≃ₗᵢ[ℂ] B) :
    (monoidalInnovation w e U).PosSemidef ∧
      (monoidalInnovation w e U = 0 ↔
        ∀ c, monoidalResidual w U c = 0) := by
  constructor
  · exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [monoidalInnovation, Matrix.conjTranspose_mul_self_eq_zero,
      residualSynthesis_eq_zero_iff]

/-- Vanishing star defects on a complex basis extend to the entire algebra. -/
theorem map_star_of_basis
    (w : Module.Basis ι ℂ A) (U : A ≃ₗᵢ[ℂ] B)
    (hstar : ∀ i, U (star (w i)) = star (U (w i))) :
    ∀ a : A, U (star a) = star (U a) := by
  intro a
  rw [← w.sum_repr a]
  simp only [map_sum, star_sum, star_smul, map_smul]
  simp only [hstar]

/-- Vanishing product defects on all pairs of basis words extend bilinearly to
all algebra elements. -/
theorem map_mul_of_basis
    (w : Module.Basis ι ℂ A) (U : A ≃ₗᵢ[ℂ] B)
    (hmul : ∀ i j, U (w i * w j) = U (w i) * U (w j)) :
    ∀ a b : A, U (a * b) = U a * U b := by
  intro a b
  rw [← w.sum_repr a, ← w.sum_repr b]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, map_smul,
    smul_mul_assoc, mul_smul_comm]
  simp only [hmul]

/-- **GT.1 at a flat word basis.**  The literal residual Gram vanishes iff the
proposed L2 unitary is the extension of a trace-preserving unital star-algebra
isomorphism. -/
theorem monoidalInnovation_zero_iff_starAlgEquiv
    (w : Module.Basis ι ℂ A) (e : OrthonormalBasis κ ℂ B)
    (U : A ≃ₗᵢ[ℂ] B) (τA : A →ₗ[ℂ] ℂ) (τB : B →ₗ[ℂ] ℂ)
    (hτA : ∀ a, τA a = inner ℂ (1 : A) a)
    (hτB : ∀ b, τB b = inner ℂ (1 : B) b) :
    monoidalInnovation w e U = 0 ↔
      ∃ E : A ≃⋆+* B,
        (∀ a, E a = U a) ∧ ∀ a, τB (E a) = τA a := by
  constructor
  · intro hzero
    have hres := (monoidalInnovation_posSemidef_and_zero_iff w e U).2.mp hzero
    have hone : U (1 : A) = (1 : B) := by
      have h := hres (Sum.inl ())
      simpa [monoidalResidual] using sub_eq_zero.mp h
    have hstarBasis : ∀ i, U (star (w i)) = star (U (w i)) := by
      intro i
      have h := hres (Sum.inr (Sum.inl i))
      exact sub_eq_zero.mp (by simpa [monoidalResidual] using h)
    have hmulBasis : ∀ i j, U (w i * w j) = U (w i) * U (w j) := by
      intro i j
      have h := hres (Sum.inr (Sum.inr (i, j)))
      exact sub_eq_zero.mp (by simpa [monoidalResidual] using h)
    have hstar := map_star_of_basis w U hstarBasis
    have hmul := map_mul_of_basis w U hmulBasis
    let E : A ≃⋆+* B :=
      { U.toLinearEquiv.toEquiv with
        map_add' := U.map_add
        map_mul' := hmul
        map_star' := hstar }
    refine ⟨E, ?_, ?_⟩
    · intro a
      rfl
    · intro a
      change τB (U a) = τA a
      rw [hτB, hτA, ← hone]
      exact U.inner_map_map 1 a
  · rintro ⟨E, hEU, _htrace⟩
    rw [(monoidalInnovation_posSemidef_and_zero_iff w e U).2]
    intro c
    rcases c with _ | i | ij
    · simp [monoidalResidual, ← hEU, map_one]
    · simp [monoidalResidual, ← hEU, map_star]
    · rcases ij with ⟨i, j⟩
      simp [monoidalResidual, ← hEU, map_mul]

/-- Complete bundle: the instantiated positive Gram/zero-isomorphism theorem
and the product-defect cocycle (GT.2). -/
theorem word_level_monoidal_transport
    (w : Module.Basis ι ℂ A) (e : OrthonormalBasis κ ℂ B)
    (U : A ≃ₗᵢ[ℂ] B) (τA : A →ₗ[ℂ] ℂ) (τB : B →ₗ[ℂ] ℂ)
    (hτA : ∀ a, τA a = inner ℂ (1 : A) a)
    (hτB : ∀ b, τB b = inner ℂ (1 : B) b) :
    (monoidalInnovation w e U).PosSemidef ∧
    (monoidalInnovation w e U = 0 ↔
      ∃ E : A ≃⋆+* B,
        (∀ a, E a = U a) ∧ ∀ a, τB (E a) = τA a) :=
  ⟨(monoidalInnovation_posSemidef_and_zero_iff w e U).1,
    monoidalInnovation_zero_iff_starAlgEquiv w e U τA τB hτA hτB⟩

end WordBasisMonoidalTransport
end NCG
