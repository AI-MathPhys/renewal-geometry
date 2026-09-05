/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PreCStarDirectLimitUniversalProperty
import NCG.Grand.AFInductiveLimitState
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Finite C-star quotient inductive systems

This file packages the quotient bookkeeping needed for contextually separated cutoff
algebras. A raw star-algebra homomorphism descends through two surjective quotient maps exactly
under forward kernel containment. Kernel reflection makes the descended map injective. For
finite-dimensional C-star algebras, such an injective map is isometric, so a strict sequence of
finite quotient certificates produces an isometric directed system suitable for the completed
C-star direct-limit machinery.
-/

open scoped CStarAlgebra

noncomputable section

namespace NCG

universe u v w z

variable {A : Type u} {B : Type v} {Q : Type w} {R : Type z}
variable [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra Q] [CStarAlgebra R]

/-- Descend a star-algebra homomorphism through a surjective source quotient. -/
def StarAlgHom.descendSurjective (qA : A →⋆ₐ[ℂ] Q) (hqA : Function.Surjective qA)
    (qB : B →⋆ₐ[ℂ] R) (φ : A →⋆ₐ[ℂ] B)
    (hker : RingHom.ker qA.toRingHom ≤
      Ideal.comap φ.toRingHom (RingHom.ker qB.toRingHom)) : Q →⋆ₐ[ℂ] R := by
  let ψRing : Q →+* R :=
    qA.toRingHom.liftOfSurjective hqA
      ⟨qB.toRingHom.comp φ.toRingHom, hker⟩
  have hψRing : ∀ a, ψRing (qA a) = qB (φ a) := by
    intro a
    exact qA.toRingHom.liftOfSurjective_comp_apply hqA
      ⟨qB.toRingHom.comp φ.toRingHom, hker⟩ a
  let ψAlg : Q →ₐ[ℂ] R :=
    { ψRing with
      commutes' := fun c => by
        calc
          ψRing (algebraMap ℂ Q c) =
              ψRing (qA (algebraMap ℂ A c)) :=
            congrArg ψRing (qA.commutes c).symm
          _ = qB (φ (algebraMap ℂ A c)) := hψRing _
          _ = qB (algebraMap ℂ B c) := congrArg qB (φ.commutes c)
          _ = algebraMap ℂ R c := qB.commutes c }
  exact
    { ψAlg with
      map_star' := fun q => by
        obtain ⟨a, rfl⟩ := hqA q
        calc
          ψAlg (star (qA a)) = ψAlg (qA (star a)) :=
            congrArg ψAlg (map_star qA a).symm
          _ = qB (φ (star a)) := hψRing _
          _ = star (qB (φ a)) := by rw [map_star, map_star]
          _ = star (ψAlg (qA a)) := congrArg star (hψRing a).symm }

namespace StarAlgHom.descendSurjective

variable (qA : A →⋆ₐ[ℂ] Q) (hqA : Function.Surjective qA)
variable (qB : B →⋆ₐ[ℂ] R) (φ : A →⋆ₐ[ℂ] B)
variable (hker : RingHom.ker qA.toRingHom ≤
  Ideal.comap φ.toRingHom (RingHom.ker qB.toRingHom))

@[simp]
theorem apply_quotient (a : A) :
    NCG.StarAlgHom.descendSurjective qA hqA qB φ hker (qA a) = qB (φ a) := by
  simp only [StarAlgHom.descendSurjective]
  exact qA.toRingHom.liftOfSurjective_comp_apply hqA
    ⟨qB.toRingHom.comp φ.toRingHom, hker⟩ a

/-- The descended map is the only star-algebra homomorphism making the quotient square
commute. -/
theorem unique (ψ : Q →⋆ₐ[ℂ] R) (hψ : ∀ a, ψ (qA a) = qB (φ a)) :
    ψ = NCG.StarAlgHom.descendSurjective qA hqA qB φ hker := by
  ext q
  obtain ⟨a, rfl⟩ := hqA q
  rw [hψ, apply_quotient]

/-- Kernel reflection makes the descended quotient map injective. -/
theorem injective
    (hreflect : Ideal.comap φ.toRingHom (RingHom.ker qB.toRingHom) ≤
      RingHom.ker qA.toRingHom) :
    Function.Injective (NCG.StarAlgHom.descendSurjective qA hqA qB φ hker) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := hqA x
  obtain ⟨b, rfl⟩ := hqA y
  apply sub_eq_zero.mp
  rw [← map_sub]
  rw [← RingHom.mem_ker]
  apply hreflect
  rw [Ideal.mem_comap, RingHom.mem_ker, map_sub, map_sub, sub_eq_zero]
  change qB (φ a) = qB (φ b)
  rw [apply_quotient, apply_quotient] at hxy
  exact hxy

end StarAlgHom.descendSurjective

/-- An injective star-algebra homomorphism out of a finite-dimensional C-star algebra is
isometric.  This specialization exposes the norm fact used by finite AF stages. -/
theorem StarAlgHom.isometry_of_injective_finiteDimensional
    [FiniteDimensional ℂ A] (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) :
    Isometry φ := NonUnitalStarAlgHom.isometry φ hφ

end NCG
