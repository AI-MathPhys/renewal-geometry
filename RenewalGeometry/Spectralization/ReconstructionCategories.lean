/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.SpectralTriple.Basic
import RenewalGeometry.Spectralization.MarkedCommutantCoordinates
/-!
# Finite reconstruction and spectral-compression data

This file encodes `def:reconstruction-categories` of `predictive_spectral_geometry`
(revised 1 Oct 2026).

## Finite level

* `FiniteUnitaryEquivalence S S'`: a unitary `U : ℂ^K → ℂ^{K'}` intertwining the
  represented algebra, `D`, the declared operator marks, the grading and the real
  structure (with equal declared signs).
* `FiniteMarkedObject A ι` with the groupoid instance: the category `Spec_fin` of finite
  marked spectral triples with unitary equivalences as isomorphisms.
* (C1) `CalibratedFiniteTriple`: a finite marked triple together with a separating
  (injective) real linear commutant-coordinate map on `c_S`; its retained record
  `CalibratedFiniteTriple.record` consists of the represented algebra, the symmetry
  marks, the declared marks, the commutator derivation and the commutant coordinates
  of `D`; the reconstruction `𝔖_fin^cal` is the functor `finiteReconstruction` to
  `Spec_fin`.

## Compact-resolvent level

* `MarkedCompactTriple A H ι`: an `NCG.SpectralTriple` with dense unital smooth
  `*`-subalgebra `𝒜_D` (density of `π(𝒜_D)` in `π(𝒜)` in operator norm), optional
  grading and real structure, and declared bounded marks.
* `CompactUnitaryEquivalence`, `CompactMarkedObject A ι` (separable carriers) with the
  groupoid instance: `Spec_cpt^sep`.
* `SpectralProjectionSequence S`: finite-rank spectral projections `P_n = 1_{B_n}(D)`
  (orthogonal projections onto the span of the eigenvectors with eigenvalue in `B_n`),
  commuting with `D`, increasing, `P_n → I` strongly; `IsSymmetricSpectralProjection`
  is the symmetric case `B = [-R, R]`.
* (C2) `IsStrongCompression` (eq:strong-compression-topology, including the declared
  bounded marks) and (C3) `IsNormMultiplicativeCompression`
  (eq:norm-multiplicative-compression); the source categories
  `StrongCompressionObject`, `NormCompressionObject` with morphisms the unitary
  equivalences intertwining the compression maps, and the reconstruction functors
  `strongReconstruction`, `normReconstruction` to `Spec_cpt^sep`.
* `IsSpectrallyQuasidiagonal` (eq:sqd, equivariant for `J`, `γ` when marked) and the full
  subcategory `SpecCptSqd`.
-/

open CategoryTheory Filter Topology Matrix
open scoped InnerProductSpace

namespace RenewalGeometry.ReconstructionCategories

open RenewalGeometry.MarkedCommutantCoordinates

noncomputable section

/-! ### Auxiliary lemmas on `Option.Rel` -/

theorem optionRel_refl {α : Type*} {r : α → α → Prop} (h : ∀ a, r a a) :
    ∀ x : Option α, Option.Rel r x x
  | none => .none
  | some a => .some (h a)

theorem optionRel_trans {α β γ : Type*} {r₁ : α → β → Prop} {r₂ : β → γ → Prop}
    {r₃ : α → γ → Prop} (h : ∀ a b c, r₁ a b → r₂ b c → r₃ a c) :
    ∀ {x y z}, Option.Rel r₁ x y → Option.Rel r₂ y z → Option.Rel r₃ x z
  | _, _, _, .some hab, .some hbc => .some (h _ _ _ hab hbc)
  | _, _, _, .none, .none => .none

theorem optionRel_symm {α β : Type*} {r : α → β → Prop} {r' : β → α → Prop}
    (h : ∀ a b, r a b → r' b a) : ∀ {x y}, Option.Rel r x y → Option.Rel r' y x
  | _, _, .some hab => .some (h _ _ hab)
  | _, _, .none => .none

/-! ### The finite category `Spec_fin` -/

section Finite

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] {ι : Type*}

/-- Conjugation of an intertwining relation by the inverse of a (rectangular) unitary. -/
theorem conjTranspose_intertwine {K K' : Type*} [Fintype K] [Fintype K'] [DecidableEq K]
    [DecidableEq K'] {U : Matrix K' K ℂ} (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1)
    {X : Matrix K K ℂ} {Y : Matrix K' K' ℂ} (h : U * X = Y * U) : Uᴴ * Y = X * Uᴴ :=
  calc Uᴴ * Y = Uᴴ * Y * (U * Uᴴ) := by rw [h2, Matrix.mul_one]
    _ = Uᴴ * (Y * U) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = Uᴴ * (U * X) * Uᴴ := by rw [h]
    _ = (Uᴴ * U) * X * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = X * Uᴴ := by rw [h1, Matrix.one_mul]

/-- Intertwining relation for real structures under a unitary `U`. -/
def RealIntertwines {K K' : Type*} [Fintype K] [Fintype K'] (U : Matrix K' K ℂ)
    (R : CoordinateRealStructure K) (R' : CoordinateRealStructure K') : Prop :=
  R'.sqSign = R.sqSign ∧ R'.diracSign = R.diracSign ∧ R'.gradingSign = R.gradingSign ∧
    ∀ ξ, U *ᵥ R.J ξ = R'.J (U *ᵥ ξ)

/-- A unitary equivalence of marked finite spectral triples: a unitary
`U : ℂ^K → ℂ^{K'}` intertwining `π`, `D`, the declared operator marks, the grading and
the real structure (the latter with equal declared signs); absent marks must be absent
on both sides. -/
@[ext]
structure FiniteUnitaryEquivalence {K K' : Type*} [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (S : MarkedFiniteSpectralTriple A K ι)
    (S' : MarkedFiniteSpectralTriple A K' ι) where
  U : Matrix K' K ℂ
  unitary_left : Uᴴ * U = 1
  unitary_right : U * Uᴴ = 1
  rep : ∀ a, U * S.rep a = S'.rep a * U
  dirac : U * S.dirac = S'.dirac * U
  mark : ∀ i, U * S.mark i = S'.mark i * U
  grading : Option.Rel (fun g g' => U * g = g' * U) S.grading S'.grading
  real : Option.Rel (RealIntertwines U) S.real S'.real

namespace FiniteUnitaryEquivalence

variable {K K' K'' : Type*} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
  [Fintype K''] [DecidableEq K'']

/-- The identity equivalence. -/
def refl (S : MarkedFiniteSpectralTriple A K ι) : FiniteUnitaryEquivalence S S where
  U := 1
  unitary_left := by simp
  unitary_right := by simp
  rep _ := by simp
  dirac := by simp
  mark _ := by simp
  grading := optionRel_refl (fun _ => by simp) _
  real := optionRel_refl (fun _ => ⟨rfl, rfl, rfl, fun _ => by simp⟩) _

/-- Composition of equivalences. -/
def trans {S : MarkedFiniteSpectralTriple A K ι} {S' : MarkedFiniteSpectralTriple A K' ι}
    {S'' : MarkedFiniteSpectralTriple A K'' ι} (f : FiniteUnitaryEquivalence S S')
    (g : FiniteUnitaryEquivalence S' S'') : FiniteUnitaryEquivalence S S'' where
  U := g.U * f.U
  unitary_left := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc g.Uᴴ, g.unitary_left,
      Matrix.one_mul, f.unitary_left]
  unitary_right := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc f.U, f.unitary_right,
      Matrix.one_mul, g.unitary_right]
  rep a := by rw [Matrix.mul_assoc, f.rep, ← Matrix.mul_assoc, g.rep, Matrix.mul_assoc]
  dirac := by rw [Matrix.mul_assoc, f.dirac, ← Matrix.mul_assoc, g.dirac, Matrix.mul_assoc]
  mark i := by rw [Matrix.mul_assoc, f.mark, ← Matrix.mul_assoc, g.mark, Matrix.mul_assoc]
  grading := optionRel_trans (fun a b c hab hbc => by
    rw [Matrix.mul_assoc, hab, ← Matrix.mul_assoc, hbc, Matrix.mul_assoc]) f.grading g.grading
  real := optionRel_trans (fun R R' R'' h h' => ⟨h'.1.trans h.1, h'.2.1.trans h.2.1,
    h'.2.2.1.trans h.2.2.1, fun ξ => by
      rw [← Matrix.mulVec_mulVec, h.2.2.2, h'.2.2.2, Matrix.mulVec_mulVec]⟩) f.real g.real

/-- The inverse equivalence `Uᴴ`. -/
def symm {S : MarkedFiniteSpectralTriple A K ι} {S' : MarkedFiniteSpectralTriple A K' ι}
    (f : FiniteUnitaryEquivalence S S') : FiniteUnitaryEquivalence S' S where
  U := f.Uᴴ
  unitary_left := by rw [conjTranspose_conjTranspose, f.unitary_right]
  unitary_right := by rw [conjTranspose_conjTranspose, f.unitary_left]
  rep a := conjTranspose_intertwine f.unitary_left f.unitary_right (f.rep a)
  dirac := conjTranspose_intertwine f.unitary_left f.unitary_right f.dirac
  mark i := conjTranspose_intertwine f.unitary_left f.unitary_right (f.mark i)
  grading := optionRel_symm (fun _ _ h =>
    conjTranspose_intertwine f.unitary_left f.unitary_right h) f.grading
  real := optionRel_symm (fun R R' h => ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun η => by
      have hη : η = f.U *ᵥ (f.Uᴴ *ᵥ η) := by
        rw [Matrix.mulVec_mulVec, f.unitary_right, Matrix.one_mulVec]
      conv_lhs => rw [hη, ← h.2.2.2, Matrix.mulVec_mulVec, f.unitary_left,
        Matrix.one_mulVec]⟩) f.real

theorem _root_.RenewalGeometry.ReconstructionCategories.optionRel_some_right {α β : Type*}
    {r : α → β → Prop} {x : Option α} {b : β} (h : Option.Rel r x (some b)) :
    ∃ a, x = some a ∧ r a b := by
  cases h with
  | some h => exact ⟨_, rfl, h⟩

section Conj

variable {S : MarkedFiniteSpectralTriple A K ι} {S' : MarkedFiniteSpectralTriple A K' ι}

theorem conj_mul_conj (f : FiniteUnitaryEquivalence S S') (X Y : Matrix K K ℂ) :
    f.U * (X * Y) * f.Uᴴ = (f.U * X * f.Uᴴ) * (f.U * Y * f.Uᴴ) := by
  calc f.U * (X * Y) * f.Uᴴ = f.U * X * (f.Uᴴ * f.U) * Y * f.Uᴴ := by
        rw [f.unitary_left, Matrix.mul_one, Matrix.mul_assoc f.U X Y]
    _ = (f.U * X * f.Uᴴ) * (f.U * Y * f.Uᴴ) := by simp only [Matrix.mul_assoc]

theorem conj_eq_of_intertwine (f : FiniteUnitaryEquivalence S S') {X : Matrix K K ℂ}
    {Y : Matrix K' K' ℂ} (h : f.U * X = Y * f.U) : f.U * X * f.Uᴴ = Y := by
  rw [h, Matrix.mul_assoc, f.unitary_right, Matrix.mul_one]

/-- A unitary equivalence conjugates the compatible commutant `c_S` into `c_{S'}`. -/
theorem conj_mem_commutantSpace (f : FiniteUnitaryEquivalence S S') {C : Matrix K K ℂ}
    (hC : C ∈ S.commutantSpace) : f.U * C * f.Uᴴ ∈ S'.commutantSpace := by
  rw [MarkedFiniteSpectralTriple.mem_commutantSpace_iff] at hC ⊢
  obtain ⟨hH, hcomm, hgr, hreal⟩ := hC
  refine ⟨?_, fun a => ?_, fun g' hg' => ?_, fun R' hR' ξ => ?_⟩
  · unfold Matrix.IsHermitian at hH ⊢
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH,
      Matrix.mul_assoc]
  · rw [← conj_eq_of_intertwine f (f.rep a), ← conj_mul_conj, ← conj_mul_conj, hcomm]
  · obtain ⟨g, hg, hgg'⟩ := optionRel_some_right (hg' ▸ f.grading)
    rw [← conj_eq_of_intertwine f hgg', ← conj_mul_conj, ← conj_mul_conj, ← Matrix.add_mul,
      ← Matrix.mul_add, hgr g hg, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨R, hR, hRR'⟩ := optionRel_some_right (hR' ▸ f.real)
    have key : ∀ η, R'.J (f.U *ᵥ η) = f.U *ᵥ R.J η := fun η => (hRR'.2.2.2 η).symm
    have hJ' : R'.J ξ = f.U *ᵥ R.J (f.Uᴴ *ᵥ ξ) := by
      rw [← key, Matrix.mulVec_mulVec, f.unitary_right, Matrix.one_mulVec]
    have h1 : (f.U * C * f.Uᴴ) *ᵥ ξ = f.U *ᵥ (C *ᵥ (f.Uᴴ *ᵥ ξ)) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [h1, key, hreal R hR, hJ', hRR'.2.1, Matrix.mulVec_smul]
    congr 1
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, f.unitary_left, Matrix.mul_one]

end Conj

end FiniteUnitaryEquivalence

/-- An object of `Spec_fin`: a marked finite spectral triple on some finite carrier. -/
structure FiniteMarkedObject (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] (ι : Type*) where
  K : Type
  [fintype : Fintype K]
  [decEq : DecidableEq K]
  triple : MarkedFiniteSpectralTriple A K ι

attribute [instance] FiniteMarkedObject.fintype FiniteMarkedObject.decEq

/-- **`def:reconstruction-categories`, `Spec_fin`.**  Finite marked spectral triples with
unitary equivalences intertwining the represented algebra, `D` and all declared marks as
isomorphisms (a groupoid). -/
instance : Groupoid (FiniteMarkedObject A ι) where
  Hom S S' := FiniteUnitaryEquivalence S.triple S'.triple
  id S := FiniteUnitaryEquivalence.refl S.triple
  comp f g := f.trans g
  id_comp f := by
    ext1
    exact Matrix.mul_one _
  comp_id f := by
    ext1
    exact Matrix.one_mul _
  assoc f g h := by
    ext1
    exact (Matrix.mul_assoc _ _ _).symm
  inv f := f.symm
  inv_comp f := by
    ext1
    exact f.unitary_right
  comp_inv f := by
    ext1
    exact f.unitary_left

/-- (C1) A calibrated finite triple: a marked finite spectral triple together with
separating (injective) real linear commutant coordinates on `c_S`. -/
structure CalibratedFiniteTriple (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A]
    (ι : Type*) where
  obj : FiniteMarkedObject A ι
  m : ℕ
  coordinates : obj.triple.CommutantCoordinateMap m
  separating : Function.Injective coordinates

namespace CalibratedFiniteTriple

variable (T : CalibratedFiniteTriple A ι)

/-- The retained finite reconstruction record (C1): represented algebra, symmetry marks,
declared operator marks, the commutator derivation `a ↦ [D, π(a)]` and the commutant
coordinates `α(P_{c_S} D)` of the Dirac operator. -/
def record :
    (A →⋆ₐ[ℂ] Matrix T.obj.K T.obj.K ℂ) × Option (Matrix T.obj.K T.obj.K ℂ) ×
      Option (CoordinateRealStructure T.obj.K) × (ι → Matrix T.obj.K T.obj.K ℂ) ×
      (A → Matrix T.obj.K T.obj.K ℂ) × (Fin T.m → ℝ) :=
  (T.obj.triple.rep, T.obj.triple.grading, T.obj.triple.real, T.obj.triple.mark,
    fun a => T.obj.triple.dirac * T.obj.triple.rep a - T.obj.triple.rep a * T.obj.triple.dirac,
    T.coordinates (T.obj.triple.commutantProjectionMem T.obj.triple.dirac))

/-- Morphisms of calibrated finite triples: unitary equivalences of the underlying triples
transporting the commutant-coordinate functionals (`α'(U C Uᴴ) = α(C)`). -/
@[ext]
structure Hom (T T' : CalibratedFiniteTriple A ι) where
  equiv : FiniteUnitaryEquivalence T.obj.triple T'.obj.triple
  dim_eq : T.m = T'.m
  coordinates : ∀ C (hC : C ∈ T.obj.triple.commutantSpace),
    T'.coordinates ⟨equiv.U * C * equiv.Uᴴ, equiv.conj_mem_commutantSpace hC⟩ =
      fun j => T.coordinates ⟨C, hC⟩ (Fin.cast dim_eq.symm j)

end CalibratedFiniteTriple

/-- The source category of (C1): calibrated finite triples with unitary equivalences
preserving the commutant-coordinate functionals. -/
instance : Category (CalibratedFiniteTriple A ι) where
  Hom := CalibratedFiniteTriple.Hom
  id T := ⟨FiniteUnitaryEquivalence.refl _, rfl, fun C hC => by
    have e : (⟨(FiniteUnitaryEquivalence.refl T.obj.triple).U * C *
        (FiniteUnitaryEquivalence.refl T.obj.triple).Uᴴ,
        (FiniteUnitaryEquivalence.refl T.obj.triple).conj_mem_commutantSpace hC⟩ :
          T.obj.triple.commutantSpace) = ⟨C, hC⟩ :=
      Subtype.ext (by simp [FiniteUnitaryEquivalence.refl])
    rw [e]
    rfl⟩
  comp {T T' T''} f g := ⟨f.equiv.trans g.equiv, f.dim_eq.trans g.dim_eq, fun C hC => by
    have e : (⟨(f.equiv.trans g.equiv).U * C * (f.equiv.trans g.equiv).Uᴴ,
        (f.equiv.trans g.equiv).conj_mem_commutantSpace hC⟩ :
          T''.obj.triple.commutantSpace) =
        ⟨g.equiv.U * (f.equiv.U * C * f.equiv.Uᴴ) * g.equiv.Uᴴ,
          g.equiv.conj_mem_commutantSpace (f.equiv.conj_mem_commutantSpace hC)⟩ :=
      Subtype.ext (by simp [FiniteUnitaryEquivalence.trans, conjTranspose_mul, Matrix.mul_assoc])
    rw [e, g.coordinates _ (f.equiv.conj_mem_commutantSpace hC), f.coordinates C hC]
    rfl⟩
  id_comp f := CalibratedFiniteTriple.Hom.ext
    (FiniteUnitaryEquivalence.ext (Matrix.mul_one _))
  comp_id f := CalibratedFiniteTriple.Hom.ext
    (FiniteUnitaryEquivalence.ext (Matrix.one_mul _))
  assoc f g h := CalibratedFiniteTriple.Hom.ext
    (FiniteUnitaryEquivalence.ext (Matrix.mul_assoc _ _ _).symm)

/-- **(C1)** The finite calibrated reconstruction `𝔖_fin^cal`: the reconstruction functor
from calibrated finite data to `Spec_fin` (the Dirac operator is recovered from the
retained record by `MarkedFiniteSpectralTriple.finite_calibrated_recovery`). -/
def finiteReconstruction : CalibratedFiniteTriple A ι ⥤ FiniteMarkedObject A ι where
  obj T := T.obj
  map f := f.equiv

/-- Every marked finite spectral triple carries separating commutant coordinates with
exactly `q_S` components. -/
theorem exists_separating_coordinates (S : FiniteMarkedObject A ι) :
    ∃ α : S.triple.CommutantCoordinateMap S.triple.commutantDim, Function.Injective α :=
  ⟨(LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_fin_fun]
      rfl)).toLinearMap, LinearEquiv.injective _⟩

/-- **Finite line of `thm:essential-image`, image part.**  Every object of `Spec_fin`
lies in the essential image of the finite calibrated reconstruction. -/
theorem finiteReconstruction_essImage (S : FiniteMarkedObject A ι) :
    (finiteReconstruction (A := A) (ι := ι)).essImage S := by
  obtain ⟨α, hα⟩ := exists_separating_coordinates S
  exact ⟨⟨S, _, α, hα⟩, ⟨Iso.refl _⟩⟩


end Finite

/-! ### The compact-resolvent category `Spec_cpt^sep` -/

section Compact

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {ι : Type*}

/-- A real structure on a Hilbert space: a surjective antiunitary (conjugate-linear,
`⟪Jx, Jy⟫ = ⟪y, x⟫`) operator `J` with declared signs `J² = ε`, `JD = ε'DJ`,
`Jγ = ε''γJ`. -/
structure HilbertRealStructure (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  J : H →ₗ⋆[ℂ] H
  antiunitary : ∀ x y, ⟪J x, J y⟫_ℂ = ⟪y, x⟫_ℂ
  surjective : Function.Surjective J
  sqSign : ℤˣ
  sq_eq : ∀ x, J (J x) = ((sqSign : ℤ) : ℂ) • x
  diracSign : ℤˣ
  gradingSign : ℤˣ

/-- A marked compact-resolvent spectral triple: an `NCG.SpectralTriple` (compact
resolvent, distinguished unital smooth `*`-subalgebra `𝒜_D` with bounded commutators)
whose smooth subalgebra is dense (`π(𝒜_D)` is operator-norm dense in `π(𝒜)`), with an
optional grading, an optional real structure, and declared bounded marks. -/
structure MarkedCompactTriple (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ι : Type*) extends NCG.SpectralTriple A H where
  smooth_dense : ∀ a : A, rep a ∈ closure (rep '' (smoothAlgebra : Set A))
  grading : Option (H →L[ℂ] H)
  grading_spec : ∀ g, grading = some g → IsSelfAdjoint g ∧ g * g = 1 ∧
    (∀ a, g * rep a = rep a * g) ∧
    ∀ x (hx : x ∈ dirac.domain), ∃ hgx : g x ∈ dirac.domain,
      dirac ⟨g x, hgx⟩ = - g (dirac ⟨x, hx⟩)
  real : Option (HilbertRealStructure H)
  real_dirac : ∀ R, real = some R → ∀ x (hx : x ∈ dirac.domain),
    ∃ hJx : R.J x ∈ dirac.domain,
      dirac ⟨R.J x, hJx⟩ = ((R.diracSign : ℤ) : ℂ) • R.J (dirac ⟨x, hx⟩)
  real_grading : ∀ R g, real = some R → grading = some g → ∀ x,
    R.J (g x) = ((R.gradingSign : ℤ) : ℂ) • g (R.J x)
  mark : ι → H →L[ℂ] H

variable {H H' H'' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup H''] [InnerProductSpace ℂ H''] [CompleteSpace H'']

/-- Intertwining of real structures by a unitary, with equal declared signs. -/
def HilbertRealIntertwines (U : H ≃ₗᵢ[ℂ] H') (R : HilbertRealStructure H)
    (R' : HilbertRealStructure H') : Prop :=
  R'.sqSign = R.sqSign ∧ R'.diracSign = R.diracSign ∧ R'.gradingSign = R.gradingSign ∧
    ∀ x, U (R.J x) = R'.J (U x)

/-- A unitary equivalence of marked compact triples: a unitary `U : H → H'`
intertwining the represented algebra, mapping `dom D` onto `dom D'` with `D' U = U D`,
preserving `𝒜_D`, and intertwining the declared marks, grading and real structure. -/
@[ext]
structure CompactUnitaryEquivalence (S : MarkedCompactTriple A H ι)
    (S' : MarkedCompactTriple A H' ι) where
  U : H ≃ₗᵢ[ℂ] H'
  smooth : S'.smoothAlgebra = S.smoothAlgebra
  rep : ∀ a x, U (S.rep a x) = S'.rep a (U x)
  domain : ∀ x, x ∈ S.dirac.domain ↔ U x ∈ S'.dirac.domain
  dirac : ∀ x (hx : x ∈ S.dirac.domain),
    S'.dirac ⟨U x, (domain x).mp hx⟩ = U (S.dirac ⟨x, hx⟩)
  mark : ∀ i x, U (S.mark i x) = S'.mark i (U x)
  grading : Option.Rel (fun g g' => ∀ x, U (g x) = g' (U x)) S.grading S'.grading
  real : Option.Rel (HilbertRealIntertwines U) S.real S'.real

namespace CompactUnitaryEquivalence

/-- The identity equivalence. -/
def refl (S : MarkedCompactTriple A H ι) : CompactUnitaryEquivalence S S where
  U := LinearIsometryEquiv.refl ℂ H
  smooth := rfl
  rep _ _ := rfl
  domain _ := Iff.rfl
  dirac _ _ := rfl
  mark _ _ := rfl
  grading := optionRel_refl (fun _ _ => rfl) _
  real := optionRel_refl (fun _ => ⟨rfl, rfl, rfl, fun _ => rfl⟩) _

/-- Composition of equivalences. -/
def trans {S : MarkedCompactTriple A H ι} {S' : MarkedCompactTriple A H' ι}
    {S'' : MarkedCompactTriple A H'' ι} (f : CompactUnitaryEquivalence S S')
    (g : CompactUnitaryEquivalence S' S'') : CompactUnitaryEquivalence S S'' where
  U := f.U.trans g.U
  smooth := g.smooth.trans f.smooth
  rep a x := by
    simp only [LinearIsometryEquiv.trans_apply, f.rep, g.rep]
  domain x := (f.domain x).trans (g.domain (f.U x))
  dirac x hx := (g.dirac (f.U x) ((f.domain x).mp hx)).trans (congrArg g.U (f.dirac x hx))
  mark i x := by
    simp only [LinearIsometryEquiv.trans_apply, f.mark, g.mark]
  grading := optionRel_trans (fun _ _ _ h h' x => by
    simp only [LinearIsometryEquiv.trans_apply, h, h']) f.grading g.grading
  real := optionRel_trans (fun _ _ _ h h' => ⟨h'.1.trans h.1, h'.2.1.trans h.2.1,
    h'.2.2.1.trans h.2.2.1, fun x => by
      simp only [LinearIsometryEquiv.trans_apply, h.2.2.2, h'.2.2.2]⟩) f.real g.real

/-- The inverse equivalence. -/
def symm {S : MarkedCompactTriple A H ι} {S' : MarkedCompactTriple A H' ι}
    (f : CompactUnitaryEquivalence S S') : CompactUnitaryEquivalence S' S where
  U := f.U.symm
  smooth := f.smooth.symm
  rep a y := by
    apply f.U.injective
    rw [f.rep, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  domain y := by
    rw [f.domain, LinearIsometryEquiv.apply_symm_apply]
  dirac y hy := by
    apply f.U.injective
    have h1 := f.dirac (f.U.symm y) ((f.domain _).mpr (by
      rwa [LinearIsometryEquiv.apply_symm_apply]))
    rw [← h1]
    conv_rhs => rw [LinearIsometryEquiv.apply_symm_apply]
    congr 1
    exact Subtype.ext (LinearIsometryEquiv.apply_symm_apply _ _)
  mark i y := by
    apply f.U.injective
    rw [f.mark, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  grading := optionRel_symm (fun g g' h y => by
    apply f.U.injective
    rw [h, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply])
    f.grading
  real := optionRel_symm (fun R R' h => ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun y => by
    apply f.U.injective
    rw [h.2.2.2, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]⟩)
    f.real

end CompactUnitaryEquivalence

/-- An object of `Spec_cpt^sep`: a marked compact-resolvent spectral triple on a
separable Hilbert space. -/
structure CompactMarkedObject (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (ι : Type*) where
  H : Type
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace ℂ H]
  [completeSpace : CompleteSpace H]
  [separableSpace : TopologicalSpace.SeparableSpace H]
  triple : MarkedCompactTriple A H ι

attribute [instance] CompactMarkedObject.normedAddCommGroup
  CompactMarkedObject.innerProductSpace CompactMarkedObject.completeSpace
  CompactMarkedObject.separableSpace

/-- **`def:reconstruction-categories`, `Spec_cpt^sep`.**  Separable marked
compact-resolvent triples with unitary equivalences as isomorphisms (a groupoid). -/
instance : Groupoid (CompactMarkedObject A ι) where
  Hom S S' := CompactUnitaryEquivalence S.triple S'.triple
  id S := CompactUnitaryEquivalence.refl S.triple
  comp f g := f.trans g
  id_comp f := CompactUnitaryEquivalence.ext (LinearIsometryEquiv.refl_trans _)
  comp_id f := CompactUnitaryEquivalence.ext (LinearIsometryEquiv.trans_refl _)
  assoc f g h := CompactUnitaryEquivalence.ext (LinearIsometryEquiv.trans_assoc _ _ _)
  inv f := f.symm
  inv_comp f := CompactUnitaryEquivalence.ext (LinearIsometryEquiv.symm_trans_self _)
  comp_inv f := CompactUnitaryEquivalence.ext (LinearIsometryEquiv.self_trans_symm _)

namespace MarkedCompactTriple

variable (S : MarkedCompactTriple A H ι)

/-- The spectral subspace `span {x ∈ dom D : D x = λ x, λ ∈ B}`, the range of the spectral
projection `1_B(D)` of the compact-resolvent operator `D`. -/
def spectralSubspace (B : Set ℝ) : Submodule ℂ H :=
  Submodule.span ℂ {x | ∃ hx : x ∈ S.dirac.domain, ∃ l ∈ B, S.dirac ⟨x, hx⟩ = (l : ℂ) • x}

/-- The symmetric spectral window `1_{[-R, R]}(D) H`. -/
def spectralWindow (R : ℝ) : Submodule ℂ H := S.spectralSubspace (Set.Icc (-R) R)

/-- `P D ⊆ D P`: `P` preserves `dom D` and commutes with `D` there. -/
def CommutesWithDirac (P : H →L[ℂ] H) : Prop :=
  ∀ x (hx : x ∈ S.dirac.domain), ∃ hPx : P x ∈ S.dirac.domain,
    S.dirac ⟨P x, hPx⟩ = P (S.dirac ⟨x, hx⟩)

/-- `P = 1_B(D)` for some Borel set `B`: the orthogonal projection onto a spectral
subspace. -/
def IsSpectralProjection (P : H →L[ℂ] H) : Prop :=
  IsStarProjection P ∧ ∃ B : Set ℝ, LinearMap.range (P : H →ₗ[ℂ] H) = S.spectralSubspace B

/-- `P = 1_{[-R, R]}(D)` for some `R ≥ 0`: the orthogonal projection onto the symmetric
spectral window. -/
def IsSymmetricSpectralProjection (P : H →L[ℂ] H) : Prop :=
  IsStarProjection P ∧ ∃ R : ℝ, 0 ≤ R ∧ LinearMap.range (P : H →ₗ[ℂ] H) = S.spectralWindow R

/-- Increasing finite-rank spectral projections `P_n ↑ I` with `P_n D = D P_n`. -/
structure SpectralProjectionSequence where
  P : ℕ → H →L[ℂ] H
  spectral : ∀ n, S.IsSpectralProjection (P n)
  finiteRank : ∀ n, FiniteDimensional ℂ (LinearMap.range (P n : H →ₗ[ℂ] H))
  commutes : ∀ n, S.CommutesWithDirac (P n)
  mono : Monotone fun n => LinearMap.range (P n : H →ₗ[ℂ] H)
  tendsto_id : ∀ ξ, Tendsto (fun n => P n ξ) atTop (𝓝 ξ)

/-- Two-sided compression `P T P`, i.e. `P T|_{P H}` extended by zero on `(P H)^⊥`. -/
def compress (P T : H →L[ℂ] H) : H →L[ℂ] H := P ∘L T ∘L P

/-- `Rz` is the resolvent `(D - z)⁻¹`. -/
def IsResolventAt (z : ℂ) (Rz : H →L[ℂ] H) : Prop :=
  (∀ y, ∃ h : Rz y ∈ S.dirac.domain, S.dirac ⟨Rz y, h⟩ - z • Rz y = y) ∧
    ∀ x : S.dirac.domain, Rz (S.dirac x - z • (x : H)) = x

/-- `T` is the bounded extension of the commutator `[D, π(a)]`. -/
def IsCommutatorExtension (a : A) (T : H →L[ℂ] H) : Prop :=
  ∀ x (hx : x ∈ S.dirac.domain), ∃ hax : S.rep a x ∈ S.dirac.domain,
    T x = S.dirac ⟨S.rep a x, hax⟩ - S.rep a (S.dirac ⟨x, hx⟩)

/-- **(C2), eq:strong-compression-topology.**  Strong convergence of the compressed
algebra, commutators, resolvents, product defects and declared bounded marks. -/
def IsStrongCompression (P : S.SpectralProjectionSequence) : Prop :=
  (∀ a ∈ S.smoothAlgebra, ∀ ξ,
    Tendsto (fun n => compress (P.P n) (S.rep a) ξ) atTop (𝓝 (S.rep a ξ))) ∧
  (∀ a ∈ S.smoothAlgebra, ∀ T, S.IsCommutatorExtension a T → ∀ ξ,
    Tendsto (fun n => compress (P.P n) T ξ) atTop (𝓝 (T ξ))) ∧
  (∀ z : ℂ, z.im ≠ 0 → ∀ Rz, S.IsResolventAt z Rz → ∀ ξ,
    Tendsto (fun n => compress (P.P n) Rz ξ) atTop (𝓝 (Rz ξ))) ∧
  (∀ a ∈ S.smoothAlgebra, ∀ b ∈ S.smoothAlgebra, ∀ ξ,
    Tendsto (fun n => (P.P n ∘L S.rep (a * b) ∘L P.P n -
      P.P n ∘L S.rep a ∘L P.P n ∘L S.rep b ∘L P.P n) ξ) atTop (𝓝 0)) ∧
  (∀ i ξ, Tendsto (fun n => compress (P.P n) (S.mark i) ξ) atTop (𝓝 (S.mark i ξ)))

/-- **(C3), eq:norm-multiplicative-compression.** -/
def IsNormMultiplicativeCompression (P : S.SpectralProjectionSequence) : Prop :=
  S.IsStrongCompression P ∧
    ∀ a ∈ S.smoothAlgebra, ∀ b ∈ S.smoothAlgebra,
      Tendsto (fun n => ‖P.P n ∘L S.rep (a * b) ∘L P.P n -
        P.P n ∘L S.rep a ∘L P.P n ∘L S.rep b ∘L P.P n‖) atTop (𝓝 0)

/-- **eq:sqd.**  Spectral quasidiagonality: finite-rank symmetric spectral projections
`P_n ↑ I`, `P_n D = D P_n`, with `‖[P_n, π(a)]‖ → 0` for every `a ∈ 𝒜_D`, commuting with
`γ` and `J` when these are marked. -/
def IsSpectrallyQuasidiagonal : Prop :=
  ∃ P : S.SpectralProjectionSequence, (∀ n, S.IsSymmetricSpectralProjection (P.P n)) ∧
    (∀ a ∈ S.smoothAlgebra,
      Tendsto (fun n => ‖P.P n * S.rep a - S.rep a * P.P n‖) atTop (𝓝 0)) ∧
    (∀ g, S.grading = some g → ∀ n, P.P n * g = g * P.P n) ∧
    (∀ R, S.real = some R → ∀ n x, P.P n (R.J x) = R.J (P.P n x))

end MarkedCompactTriple

/-- `Spec_cpt^sqd` as an object property of `Spec_cpt^sep`. -/
def sqdProperty : ObjectProperty (CompactMarkedObject A ι) :=
  fun X => X.triple.IsSpectrallyQuasidiagonal

/-- **`Spec_cpt^sqd`**: the full subcategory of spectrally quasidiagonal triples. -/
abbrev SpecCptSqd (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (ι : Type*) := (sqdProperty (A := A) (ι := ι)).FullSubcategory

/-- Conjugation `U T U⁻¹` of a bounded operator by a unitary. -/
def conjOp (U : H ≃ₗᵢ[ℂ] H') (T : H →L[ℂ] H) : H' →L[ℂ] H' :=
  (U : H →L[ℂ] H') ∘L T ∘L (U.symm : H' →L[ℂ] H)

/-- An object of the strong spectral-compression source category (C2): a separable
marked compact triple with a strong compression sequence and recorded finite
commutant-coordinate functionals `coordinates n` (of dimension `cdim n`) on the
compressed operators. -/
structure StrongCompressionObject (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (ι : Type*) where
  obj : CompactMarkedObject A ι
  P : obj.triple.SpectralProjectionSequence
  strong : obj.triple.IsStrongCompression P
  cdim : ℕ → ℕ
  coordinates : ∀ n, (obj.H →L[ℂ] obj.H) →ₗ[ℝ] (Fin (cdim n) → ℝ)

/-- Morphisms of (C2) sources: unitary equivalences intertwining the compression maps and
transporting the recorded commutant-coordinate functionals. -/
@[ext]
structure StrongCompressionObject.Hom (X Y : StrongCompressionObject A ι) where
  equiv : CompactUnitaryEquivalence X.obj.triple Y.obj.triple
  compress : ∀ n x, equiv.U (X.P.P n x) = Y.P.P n (equiv.U x)
  cdim_eq : X.cdim = Y.cdim
  coordinates : ∀ n T, Y.coordinates n (conjOp equiv.U T) =
    fun j => X.coordinates n T (Fin.cast (congrFun cdim_eq n).symm j)

instance : Category (StrongCompressionObject A ι) where
  Hom := StrongCompressionObject.Hom
  id X := ⟨CompactUnitaryEquivalence.refl _, fun _ _ => rfl, rfl, fun n T => by
    have : conjOp (CompactUnitaryEquivalence.refl X.obj.triple).U T = T :=
      ContinuousLinearMap.ext fun _ => rfl
    rw [this]
    rfl⟩
  comp {X Y Z} f g := ⟨f.equiv.trans g.equiv, fun n x => by
      change g.equiv.U (f.equiv.U (X.P.P n x)) = Z.P.P n (g.equiv.U (f.equiv.U x))
      rw [f.compress, g.compress],
    f.cdim_eq.trans g.cdim_eq, fun n T => by
      have : conjOp (f.equiv.trans g.equiv).U T = conjOp g.equiv.U (conjOp f.equiv.U T) :=
        ContinuousLinearMap.ext fun _ => rfl
      rw [this, g.coordinates, f.coordinates]
      rfl⟩
  id_comp f := StrongCompressionObject.Hom.ext
    (CompactUnitaryEquivalence.ext (LinearIsometryEquiv.refl_trans _))
  comp_id f := StrongCompressionObject.Hom.ext
    (CompactUnitaryEquivalence.ext (LinearIsometryEquiv.trans_refl _))
  assoc f g h := StrongCompressionObject.Hom.ext
    (CompactUnitaryEquivalence.ext (LinearIsometryEquiv.trans_assoc _ _ _))

/-- **(C2)** The strong reconstruction `𝔖_cpt^{strong,cal}`, forgetting the compression
data. -/
def strongReconstruction : StrongCompressionObject A ι ⥤ CompactMarkedObject A ι where
  obj X := X.obj
  map f := f.equiv

/-- The norm-multiplicative sources as an object property of the strong sources. -/
def normCompressionProperty : ObjectProperty (StrongCompressionObject A ι) :=
  fun X => X.obj.triple.IsNormMultiplicativeCompression X.P

/-- **(C3)** The norm-multiplicative source category. -/
abbrev NormCompressionObject (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (ι : Type*) :=
  (normCompressionProperty (A := A) (ι := ι)).FullSubcategory

/-- **(C3)** The norm-multiplicative reconstruction `𝔖_cpt^{norm,cal}`. -/
def normReconstruction : NormCompressionObject A ι ⥤ CompactMarkedObject A ι :=
  normCompressionProperty.ι ⋙ strongReconstruction

end Compact


end

end RenewalGeometry.ReconstructionCategories
