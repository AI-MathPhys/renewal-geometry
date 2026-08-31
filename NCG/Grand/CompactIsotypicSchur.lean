/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.RepresentationTheory.FDRep
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Schur extraction for compact isotypic packet averages

This file turns Mathlib's categorical Schur lemma for `FDRep` into two
unbundled linear-map statements convenient for Haar-averaged packet
operators.  No compactness is needed at this layer: compactness enters only
when the averaged operator is constructed.
-/

open CategoryTheory
open Module

namespace NCG
namespace CompactIsotypicSchur

universe v

variable {G : Type v} [Group G]
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Bundle a matrix-valued group representation as a representation on
column vectors. -/
noncomputable def matrixRepresentation {I : Type} [Fintype I] [DecidableEq I]
    (ρ : G →* Matrix I I ℂ) : Representation ℂ G (I → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ

/-- A linear map commuting with an irreducible complex representation is a
scalar multiple of the identity.  This is the unbundled form of Schur's
lemma used for diagonal isotypic blocks. -/
theorem equivariant_endomorphism_eq_smul_id
    (ρ : Representation ℂ G V) [Simple (FDRep.of ρ)]
    (T : V →ₗ[ℂ] V)
    (hT : ∀ g, T.comp (ρ g) = (ρ g).comp T) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  let f : FDRep.of ρ ⟶ FDRep.of ρ :=
    { hom := InducedCategory.homMk (ModuleCat.ofHom T)
      comm := fun g => by
        ext x
        exact LinearMap.congr_fun (hT g) x }
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f
  refine ⟨c, ?_⟩
  have hc' := congrArg
    (fun q : FDRep.of ρ ⟶ FDRep.of ρ =>
      q.hom.hom.hom)
    hc
  have hunder :
      (c • (𝟙 (FDRep.of ρ))).hom.hom.hom = c • LinearMap.id := by
    ext x
    change c • x = c • x
    rfl
  have hTf : T = (c • (𝟙 (FDRep.of ρ))).hom.hom.hom := by
    simpa [f] using hc'.symm
  exact hTf.trans hunder

/-- An intertwiner between two nonisomorphic irreducible complex
representations is zero.  This is the off-diagonal block of Schur's lemma. -/
theorem equivariant_map_eq_zero_of_not_isomorphic
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Simple (FDRep.of ρ)] [Simple (FDRep.of σ)]
    (hnot : IsEmpty (FDRep.of ρ ≅ FDRep.of σ))
    (T : V →ₗ[ℂ] W)
    (hT : ∀ g, T.comp (ρ g) = (σ g).comp T) :
    T = 0 := by
  let f : FDRep.of ρ ⟶ FDRep.of σ :=
    { hom := InducedCategory.homMk (ModuleCat.ofHom T)
      comm := fun g => by
        ext x
        exact LinearMap.congr_fun (hT g) x }
  have hdim : finrank ℂ (FDRep.of ρ ⟶ FDRep.of σ) = 0 := by
    rw [FDRep.finrank_hom_simple_simple]
    simp [not_nonempty_iff.mpr hnot]
  letI : Subsingleton (FDRep.of ρ ⟶ FDRep.of σ) :=
    Module.finrank_zero_iff.mp hdim
  have hf : f = 0 := Subsingleton.elim _ _
  have hf' := congrArg
    (fun q : FDRep.of ρ ⟶ FDRep.of σ =>
      q.hom.hom.hom)
    hf
  simpa [f] using hf'

/-- Matrix form of the diagonal Schur block: a matrix commuting with an
irreducible matrix representation is scalar. -/
theorem matrix_eq_smul_one_of_commutes_irreducible
    {I : Type} [Fintype I] [DecidableEq I]
    (ρ : G →* Matrix I I ℂ)
    [Simple (FDRep.of (matrixRepresentation ρ))]
    (A : Matrix I I ℂ)
    (hA : ∀ g, A * ρ g = ρ g * A) :
    ∃ c : ℂ, A = c • (1 : Matrix I I ℂ) := by
  obtain ⟨c, hc⟩ := equivariant_endomorphism_eq_smul_id
    (matrixRepresentation ρ) A.mulVecLin (fun g => by
      change A.mulVecLin.comp (ρ g).mulVecLin =
        (ρ g).mulVecLin.comp A.mulVecLin
      rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, hA g])
  refine ⟨c, ?_⟩
  apply Matrix.toLin'.injective
  simpa [Matrix.toLin'_apply', Matrix.mulVecLin_one] using hc

/-- Matrix form of the off-diagonal Schur block: an intertwining matrix
between nonisomorphic irreducible matrix representations is zero. -/
theorem matrix_eq_zero_of_intertwines_nonisomorphic
    {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (ρ : G →* Matrix I I ℂ) (σ : G →* Matrix J J ℂ)
    [Simple (FDRep.of (matrixRepresentation ρ))]
    [Simple (FDRep.of (matrixRepresentation σ))]
    (hnot : IsEmpty
      (FDRep.of (matrixRepresentation ρ) ≅
        FDRep.of (matrixRepresentation σ)))
    (A : Matrix J I ℂ)
    (hA : ∀ g, A * ρ g = σ g * A) :
    A = 0 := by
  have hlin := equivariant_map_eq_zero_of_not_isomorphic
    (matrixRepresentation ρ) (matrixRepresentation σ) hnot A.mulVecLin
    (fun g => by
      change A.mulVecLin.comp (ρ g).mulVecLin =
        (σ g).mulVecLin.comp A.mulVecLin
      rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, hA g])
  apply Matrix.toLin'.injective
  simpa [Matrix.toLin'_apply'] using hlin

end CompactIsotypicSchur
end NCG
