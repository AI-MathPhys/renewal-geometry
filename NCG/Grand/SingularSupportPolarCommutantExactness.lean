/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SingularPolarData
import NCG.Grand.SMSTCommutant

/-!
# Exact support--polar commutant for singular incidence maps

This file completes `thm:SMST-support-polar-commutant`.  Unlike the earlier
polynomial-commutation lemma, it uses the CFC construction in
`SingularPolarData` to obtain the support projection and polar partial
isometry for every rectangular matrix, including rank-deficient and zero
matrices.  It then identifies the full incidence-intertwiner set with the
support--metric--polar intertwiner set and consequently identifies their
finite block commutants.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- A block-diagonal endomorphism of the source and target carriers of a
rectangular incidence map. -/
structure IncidenceBlockEndomorphism (e h : ℕ) where
  source : Matrix (Fin e) (Fin e) ℂ
  target : Matrix (Fin h) (Fin h) ℂ

/-- Componentwise commutation on the source and target blocks. -/
def IncidenceBlockEndomorphism.Commutes {e h : ℕ}
    (A B : IncidenceBlockEndomorphism e h) : Prop :=
  Commute A.source B.source ∧ Commute A.target B.target

/-- The finite block commutant of a set of block-diagonal endomorphisms. -/
def incidenceBlockCommutant {e h : ℕ}
    (S : Set (IncidenceBlockEndomorphism e h)) :
    Set (IncidenceBlockEndomorphism e h) :=
  {A | ∀ B ∈ S, A.Commutes B}

/-- Multiplicity symmetries defined from the original incidence arrow and its
adjoint. -/
def incidenceIntertwinerSet {e h : ℕ}
    (F : Matrix (Fin h) (Fin e) ℂ) :
    Set (IncidenceBlockEndomorphism e h) :=
  {R | R.target * F = F * R.source ∧
    R.source * Fᴴ = Fᴴ * R.target}

/-- Multiplicity symmetries defined from the positive support metric and polar
partial isometry. -/
def supportPolarIntertwinerSet {e h : ℕ}
    (U : Matrix (Fin h) (Fin e) ℂ)
    (P : Matrix (Fin e) (Fin e) ℂ) :
    Set (IncidenceBlockEndomorphism e h) :=
  {R | R.source * (P * P) = (P * P) * R.source ∧
    R.target * U = U * R.source ∧
    R.source * Uᴴ = Uᴴ * R.target}

/-- The CFC-constructed support boundary is respected by every source
endomorphism commuting with the positive incidence metric.  This is the
rank-deficient clause missing from polynomial-only encodings. -/
theorem singularPolar_supportBoundary_in_commutant {e h : ℕ}
    (F : Matrix (Fin h) (Fin e) ℂ) :
    ∃ (U : Matrix (Fin h) (Fin e) ℂ)
      (P Pd : Matrix (Fin e) (Fin e) ℂ),
      P.PosSemidef ∧ F = U * P ∧ P * P = Fᴴ * F ∧
      U * (Uᴴ * U) = U ∧
      P * Pd = Uᴴ * U ∧ Pd * P = Uᴴ * U ∧
      (∀ R : Matrix (Fin e) (Fin e) ℂ,
        Commute R (Fᴴ * F) → Commute R (Uᴴ * U)) := by
  rcases exists_singular_polar_data F with
    ⟨U, P, Pd, hP, hF, hP2, hU, hPPd, hPdP, hsupp⟩
  refine ⟨U, P, Pd, hP, hF, hP2, hU, hPPd, hPdP, ?_⟩
  intro R hR
  exact hsupp R (by simpa [hP2] using hR.eq)

/-- Exact one-edge support--polar commutant theorem.  It is simultaneous in
all source/target endomorphisms, so it identifies the complete symmetry set,
not just one chosen commutant element. -/
theorem singularSupportPolar_intertwinerSet_eq {e h : ℕ}
    (F : Matrix (Fin h) (Fin e) ℂ) :
    ∃ (U : Matrix (Fin h) (Fin e) ℂ)
      (P Pd : Matrix (Fin e) (Fin e) ℂ),
      P.PosSemidef ∧ F = U * P ∧ P * P = Fᴴ * F ∧
      U * (Uᴴ * U) = U ∧
      P * Pd = Uᴴ * U ∧ Pd * P = Uᴴ * U ∧
      incidenceIntertwinerSet F = supportPolarIntertwinerSet U P := by
  rcases exists_singular_polar_data F with
    ⟨U, P, Pd, hP, hF, hP2, hU, hPPd, hPdP, hsupp⟩
  refine ⟨U, P, Pd, hP, hF, hP2, hU, hPPd, hPdP, ?_⟩
  ext R
  change
    (R.target * F = F * R.source ∧
      R.source * Fᴴ = Fᴴ * R.target) ↔
    (R.source * (P * P) = (P * P) * R.source ∧
      R.target * U = U * R.source ∧
      R.source * Uᴴ = Uᴴ * R.target)
  exact (polar_edge_singular F U P Pd R.source R.target
    hP hF hP2 hU hPPd hPdP hsupp).1

/-- Equal multiplicity symmetry sets have equal finite block commutants.  This
is the reverse/bicommutant presentation of the same generated observable
algebra. -/
theorem incidenceBlockCommutant_congr {e h : ℕ}
    {S T : Set (IncidenceBlockEndomorphism e h)} (hST : S = T) :
    incidenceBlockCommutant S = incidenceBlockCommutant T := by
  rw [hST]

/-- Exact support--polar theorem including both commutant directions: the
original incidence presentation and the CFC support--polar presentation have
the same multiplicity algebra and the same finite block bicommutant. -/
theorem singular_support_polar_commutant_exactness {e h : ℕ}
    (F : Matrix (Fin h) (Fin e) ℂ) :
    ∃ (U : Matrix (Fin h) (Fin e) ℂ)
      (P Pd : Matrix (Fin e) (Fin e) ℂ),
      P.PosSemidef ∧ F = U * P ∧ P * P = Fᴴ * F ∧
      U * (Uᴴ * U) = U ∧
      P * Pd = Uᴴ * U ∧ Pd * P = Uᴴ * U ∧
      incidenceIntertwinerSet F = supportPolarIntertwinerSet U P ∧
      incidenceBlockCommutant (incidenceIntertwinerSet F) =
        incidenceBlockCommutant (supportPolarIntertwinerSet U P) := by
  rcases singularSupportPolar_intertwinerSet_eq F with
    ⟨U, P, Pd, hP, hF, hP2, hU, hPPd, hPdP, hsets⟩
  exact ⟨U, P, Pd, hP, hF, hP2, hU, hPPd, hPdP, hsets,
    incidenceBlockCommutant_congr hsets⟩

/-- Common multiplicity symmetries of a finite incidence family. -/
def incidenceFamilyIntertwinerSet {J : Type*} {e h : ℕ}
    (F : J → Matrix (Fin h) (Fin e) ℂ) :
    Set (IncidenceBlockEndomorphism e h) :=
  {R | ∀ j, R ∈ incidenceIntertwinerSet (F j)}

/-- Common multiplicity symmetries of its support--polar presentation. -/
def supportPolarFamilyIntertwinerSet {J : Type*} {e h : ℕ}
    (U : J → Matrix (Fin h) (Fin e) ℂ)
    (P : J → Matrix (Fin e) (Fin e) ℂ) :
    Set (IncidenceBlockEndomorphism e h) :=
  {R | ∀ j, R ∈ supportPolarIntertwinerSet (U j) (P j)}

/-- Finite-family form of the exact theorem.  Every edge may be rectangular,
singular, rank-deficient, or zero; no common rank hypothesis is used. -/
theorem finiteFamily_singular_support_polar_commutant_exactness
    {J : Type*} {e h : ℕ}
    (F : J → Matrix (Fin h) (Fin e) ℂ) :
    ∃ (U : J → Matrix (Fin h) (Fin e) ℂ)
      (P Pd : J → Matrix (Fin e) (Fin e) ℂ),
      (∀ j, (P j).PosSemidef ∧ F j = U j * P j ∧
        P j * P j = (F j)ᴴ * F j ∧
        U j * ((U j)ᴴ * U j) = U j ∧
        P j * Pd j = (U j)ᴴ * U j ∧
        Pd j * P j = (U j)ᴴ * U j) ∧
      incidenceFamilyIntertwinerSet F =
        supportPolarFamilyIntertwinerSet U P ∧
      incidenceBlockCommutant (incidenceFamilyIntertwinerSet F) =
        incidenceBlockCommutant (supportPolarFamilyIntertwinerSet U P) := by
  choose U P Pd hP hF hP2 hU hPPd hPdP hsets using
    fun j => singularSupportPolar_intertwinerSet_eq (F j)
  refine ⟨U, P, Pd, ?_, ?_, ?_⟩
  · intro j
    exact ⟨hP j, hF j, hP2 j, hU j, hPPd j, hPdP j⟩
  · ext R
    constructor <;> intro hR j
    · rw [← hsets j]
      exact hR j
    · rw [hsets j]
      exact hR j
  · apply incidenceBlockCommutant_congr
    ext R
    constructor <;> intro hR j
    · rw [← hsets j]
      exact hR j
    · rw [hsets j]
      exact hR j

end NCG
