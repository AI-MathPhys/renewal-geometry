/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.DerivationOnlyAustereImage
/-!
# Marked finite spectral triples, compatible commutant and commutant coordinates

This file covers `def:marked-spectral-triple`, `thm:commutant-fibre` and the finite
recovery statement `prop:finite-calibrated-recovery` of `predictive_spectral_geometry`
(revised 1 Oct 2026).

## Abstract layer

Over a finite-dimensional real inner-product space `V` with the commutator derivation
and the declared sign equations given as real-linear constraint maps (the model of
`DerivationOnlyAustereImage`), we add:

* `anchor_starProjection_eq_sum`, `eq_centered_add_sum`: for any orthonormal basis
  `b` of the compatible anchor space `c`, `P_c D = ∑ ⟪b j, D⟫ b j` and hence
  `D = D_der + ∑ ⟪b j, D⟫ b j` (eq:commutant-reconstruction);
* `eq_centered_iff_anchor_projection_eq_zero`: within a fibre, `X = D_der ↔ P_c X = 0`;
* `eq_of_anchor_coordinates_eq`: equal derivation data and equal values of an
  injective linear coordinate map on `P_c X`, `P_c D` force `X = D`;
* `exists_ne_of_lt_anchorRank`: with fewer than `q = dim c` coordinates two distinct
  points of the fibre always have equal coordinates.

## Concrete layer

* `HSMatrix K`: complex `K × K` matrices with the real Hilbert–Schmidt inner product
  `⟪X, Y⟫ = Re tr (Xᴴ Y)` (`hsInner`).
* `CoordinateRealStructure K`: an antiunitary `J` on `ℂ^K` with the signs
  `J² = ε`, `J D = ε' D J`, `J γ = ε'' γ J`.
* `MarkedFiniteSpectralTriple A K ι`: `(𝒜, ℂ^K, π, D, J, γ; 𝔪)` with optional
  grading and real structure (absent marks impose no condition) and declared operator
  marks `𝔪 : ι → Matrix K K ℂ`.
* `commutantSpace S`: the compatible real commutant
  `c_S = {C ∈ π(𝒜)'_sa : Cγ + γC = 0, JC = ε'CJ}` (eq:commutant-space), its real
  Hilbert–Schmidt projection `commutantProjection`, `centeredDirac S = D - P_c D` and
  `commutantDim S = dim_ℝ c_S` (eq:centered-D); `CommutantCoordinateMap S m` is a real
  linear map `c_S → ℝ^m`.
* `commutant_fibre`: the bundled statement of `thm:commutant-fibre`.
-/

open Matrix
open scoped InnerProductSpace

namespace RenewalGeometry.MarkedCommutantCoordinates

noncomputable section

open RenewalGeometry.DerivationOnlyAustereImage

/-! ### Abstract layer -/

section Abstract

variable {V DerivData SignData : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [AddCommGroup DerivData] [Module ℝ DerivData]
variable [AddCommGroup SignData] [Module ℝ SignData]
variable (derivation : V →ₗ[ℝ] DerivData) (signs : V →ₗ[ℝ] SignData)

/-- Expansion of the compatible-anchor projection in an orthonormal basis. -/
theorem anchor_starProjection_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (compatibleAnchor derivation signs)) (D : V) :
    (compatibleAnchor derivation signs).starProjection D =
      ∑ i, ⟪(b i : V), D⟫_ℝ • (b i : V) := by
  rw [b.starProjection_eq_sum_rankOne]
  simp [InnerProductSpace.rankOne_apply]

/-- `eq:commutant-reconstruction` in the abstract model:
`D = D_der + ∑ ⟪b j, D⟫ b j`. -/
theorem eq_centered_add_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (compatibleAnchor derivation signs)) (D : V) :
    D = centeredRepresentative derivation signs D + ∑ i, ⟪(b i : V), D⟫_ℝ • (b i : V) := by
  rw [← anchor_starProjection_eq_sum, centeredRepresentative, sub_add_cancel]

/-- The centered representative of `X` is its orthogonal-complement projection. -/
theorem centeredRepresentative_eq_orthogonal_projection (X : V) :
    centeredRepresentative derivation signs X =
      (compatibleAnchor derivation signs)ᗮ.starProjection X :=
  (orthogonal_projection_eq_centered derivation signs (X := X) (D := X) ⟨rfl, rfl⟩).symm

/-- The centered representative is constant on a marked derivation fibre. -/
theorem centeredRepresentative_eq_of_same {D X : V}
    (hX : SameMarkedDerivation derivation signs D X) :
    centeredRepresentative derivation signs X = centeredRepresentative derivation signs D := by
  rw [centeredRepresentative_eq_orthogonal_projection,
    orthogonal_projection_eq_centered derivation signs hX]

/-- Every fibre point is the centered representative plus its anchor projection. -/
theorem eq_centered_add_anchor_projection {D X : V}
    (hX : SameMarkedDerivation derivation signs D X) :
    X = centeredRepresentative derivation signs D +
      (compatibleAnchor derivation signs).starProjection X := by
  rw [← centeredRepresentative_eq_of_same derivation signs hX, centeredRepresentative,
    sub_add_cancel]

/-- `D_der = D` exactly when `P_c D = 0`. -/
theorem centeredRepresentative_eq_self_iff (D : V) :
    centeredRepresentative derivation signs D = D ↔
      (compatibleAnchor derivation signs).starProjection D = 0 := by
  rw [centeredRepresentative, sub_eq_self]

/-- Within a fibre, the canonical derivation-only representative is exactly the point
with vanishing anchor projection. -/
theorem eq_centered_iff_anchor_projection_eq_zero {D X : V}
    (hX : SameMarkedDerivation derivation signs D X) :
    X = centeredRepresentative derivation signs D ↔
      (compatibleAnchor derivation signs).starProjection X = 0 := by
  conv_lhs => rw [eq_centered_add_anchor_projection derivation signs hX]
  constructor
  · intro h
    have := congrArg (fun Y => Y - centeredRepresentative derivation signs D) h
    simpa using this
  · intro h
    rw [h, add_zero]

/-- Recovery: equal marked derivation data and equal values of an injective linear
coordinate map on the anchor projections force equality. -/
theorem eq_of_anchor_coordinates_eq {m : ℕ}
    (α : compatibleAnchor derivation signs →ₗ[ℝ] (Fin m → ℝ)) (hα : Function.Injective α)
    {D X : V} (hX : SameMarkedDerivation derivation signs D X)
    (hcoord : α ((compatibleAnchor derivation signs).orthogonalProjectionOnto X) =
      α ((compatibleAnchor derivation signs).orthogonalProjectionOnto D)) :
    X = D := by
  have hP := congrArg (Subtype.val) (hα hcoord)
  simp only [Submodule.coe_orthogonalProjectionOnto_apply] at hP
  rw [eq_centered_add_anchor_projection derivation signs hX, hP,
    centeredRepresentative, sub_add_cancel]

/-- Recovery from orthonormal coordinates `⟪b j, ·⟫`. -/
theorem eq_of_inner_eq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (compatibleAnchor derivation signs))
    {D X : V} (hX : SameMarkedDerivation derivation signs D X)
    (hcoord : ∀ i, ⟪(b i : V), X⟫_ℝ = ⟪(b i : V), D⟫_ℝ) : X = D := by
  rw [eq_centered_add_sum derivation signs b X, eq_centered_add_sum derivation signs b D,
    centeredRepresentative_eq_of_same derivation signs hX]
  simp only [hcoord]

/-- Sharpness: fewer than `q = dim c` linear coordinates leave two distinct points of
every fibre with the same coordinates. -/
theorem exists_ne_of_lt_anchorRank {m : ℕ}
    (hm : m < anchorRank (derivation := derivation) (signs := signs))
    (α : compatibleAnchor derivation signs →ₗ[ℝ] (Fin m → ℝ)) (D : V) :
    ∃ X, SameMarkedDerivation derivation signs D X ∧ X ≠ D ∧
      α ((compatibleAnchor derivation signs).orthogonalProjectionOnto X) =
        α ((compatibleAnchor derivation signs).orthogonalProjectionOnto D) := by
  have hni := fewer_anchors_not_injective derivation signs hm α
  rw [← LinearMap.ker_eq_bot] at hni
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp hni
  refine ⟨D + c, (complete_solution_fibre derivation signs D (D + c)).mpr ⟨c, rfl⟩, ?_, ?_⟩
  · intro h
    apply hc0
    apply Subtype.ext
    simpa using h
  · rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, map_add,
      LinearMap.mem_ker.mp hc, add_zero]

end Abstract

/-! ### The real Hilbert–Schmidt space of matrices -/

section HilbertSchmidt

variable {K : Type*} [Fintype K]

/-- The real Hilbert–Schmidt inner product `⟪X, Y⟫_{HS,ℝ} = Re tr (Xᴴ Y)`. -/
noncomputable def hsInner (X Y : Matrix K K ℂ) : ℝ := (Xᴴ * Y).trace.re

theorem hsInner_comm (X Y : Matrix K K ℂ) : hsInner X Y = hsInner Y X := by
  unfold hsInner
  rw [show Yᴴ * X = (Xᴴ * Y)ᴴ by rw [conjTranspose_mul, conjTranspose_conjTranspose],
    trace_conjTranspose]
  simp

theorem hsInner_add_left (X Y Z : Matrix K K ℂ) :
    hsInner (X + Y) Z = hsInner X Z + hsInner Y Z := by
  simp [hsInner, conjTranspose_add, add_mul, trace_add]

theorem hsInner_smul_left (r : ℝ) (X Y : Matrix K K ℂ) :
    hsInner (r • X) Y = r * hsInner X Y := by
  simp [hsInner, conjTranspose_smul, Matrix.smul_mul, trace_smul]

theorem hsInner_self_eq (X : Matrix K K ℂ) :
    hsInner X X = ∑ i, ∑ k, Complex.normSq (X k i) := by
  simp only [hsInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re]

theorem hsInner_self_nonneg (X : Matrix K K ℂ) : 0 ≤ hsInner X X := by
  rw [hsInner_self_eq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _

theorem hsInner_self_eq_zero {X : Matrix K K ℂ} (h : hsInner X X = 0) : X = 0 := by
  rw [hsInner_self_eq] at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => Complex.normSq_nonneg (X k i)).mp h
  ext k i
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
    Complex.normSq_nonneg (X k i)).mp (h1 i (Finset.mem_univ i)) k (Finset.mem_univ k)
  simpa using h2

/-- Type synonym: complex `K × K` matrices regarded as a real inner-product space for
the Hilbert–Schmidt inner product `Re tr (Xᴴ Y)`. -/
def HSMatrix (K : Type*) [Fintype K] : Type _ := Matrix K K ℂ

namespace HSMatrix

noncomputable instance : AddCommGroup (HSMatrix K) :=
  inferInstanceAs (AddCommGroup (Matrix K K ℂ))

noncomputable instance : Module ℝ (HSMatrix K) :=
  inferInstanceAs (Module ℝ (Matrix K K ℂ))

/-- The identity identification of matrices with the Hilbert–Schmidt space. -/
def ofMatrix : Matrix K K ℂ ≃ₗ[ℝ] HSMatrix K := LinearEquiv.refl ℝ (Matrix K K ℂ)

@[simp] theorem ofMatrix_symm_ofMatrix (X : Matrix K K ℂ) :
    ofMatrix.symm (ofMatrix X : HSMatrix K) = X := rfl

/-- The Hilbert–Schmidt inner-product core. -/
noncomputable def hsCore : InnerProductSpace.Core ℝ (HSMatrix K) where
  inner X Y := hsInner (ofMatrix.symm X) (ofMatrix.symm Y)
  conj_inner_symm X Y := by
    simp only [conj_trivial]
    exact hsInner_comm _ _
  re_inner_nonneg X := hsInner_self_nonneg _
  add_left X Y Z := hsInner_add_left (ofMatrix.symm X) (ofMatrix.symm Y) (ofMatrix.symm Z)
  smul_left X Y r := by
    simp only [conj_trivial]
    exact hsInner_smul_left r (ofMatrix.symm X) (ofMatrix.symm Y)
  definite X h := hsInner_self_eq_zero h

noncomputable instance : NormedAddCommGroup (HSMatrix K) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := hsCore)

noncomputable instance : InnerProductSpace ℝ (HSMatrix K) :=
  InnerProductSpace.ofCore hsCore.toCore

instance : FiniteDimensional ℝ (HSMatrix K) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix K K ℂ))

theorem inner_ofMatrix (X Y : Matrix K K ℂ) :
    ⟪(ofMatrix X : HSMatrix K), ofMatrix Y⟫_ℝ = hsInner X Y := rfl

theorem inner_def (X Y : HSMatrix K) :
    ⟪X, Y⟫_ℝ = hsInner (ofMatrix.symm X) (ofMatrix.symm Y) := rfl

end HSMatrix

/-- The Hilbert–Schmidt norm `‖X‖_HS = √(Re tr (Xᴴ X))`. -/
noncomputable def hsNorm (X : Matrix K K ℂ) : ℝ := ‖(HSMatrix.ofMatrix X : HSMatrix K)‖

theorem hsNorm_eq_sqrt (X : Matrix K K ℂ) : hsNorm X = Real.sqrt (hsInner X X) := by
  rw [hsNorm, @norm_eq_sqrt_re_inner ℝ, HSMatrix.inner_ofMatrix]
  rfl

end HilbertSchmidt

/-! ### Marked finite spectral triples -/

section Triples

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- A real structure on `ℂ^K` in coordinates: an antiunitary (conjugate-linear,
inner-product reversing) operator `J` with the declared signs `J² = ε`,
`J D = ε' D J` (`diracSign`) and `J γ = ε'' γ J` (`gradingSign`); the signs are
units of `ℤ`, i.e. `±1`. -/
structure CoordinateRealStructure (K : Type*) [Fintype K] where
  /-- The antilinear operator `J`. -/
  J : (K → ℂ) →ₗ⋆[ℂ] (K → ℂ)
  /-- Antiunitarity: `⟨Jξ, Jη⟩ = ⟨η, ξ⟩`. -/
  antiunitary : ∀ ξ η : K → ℂ, star (J ξ) ⬝ᵥ J η = star η ⬝ᵥ ξ
  /-- The sign `ε` in `J² = ε`. -/
  sqSign : ℤˣ
  sq_eq : ∀ ξ, J (J ξ) = ((sqSign : ℤ) : ℂ) • ξ
  /-- The Dirac sign `ε'` in `J D = ε' D J`. -/
  diracSign : ℤˣ
  /-- The grading sign `ε''` in `J γ = ε'' γ J`. -/
  gradingSign : ℤˣ

namespace CoordinateRealStructure

variable (R : CoordinateRealStructure K)

/-- `J` is real-linear. -/
theorem J_real_smul (r : ℝ) (v : K → ℂ) : R.J (r • v) = r • R.J v := by
  have h1 : (r • v : K → ℂ) = (r : ℂ) • v := by
    funext k; simp [Complex.real_smul]
  have h2 : (r • R.J v : K → ℂ) = (r : ℂ) • R.J v := by
    funext k; simp [Complex.real_smul]
  rw [h1, h2, LinearMap.map_smulₛₗ, Complex.conj_ofReal]

/-- The `J`-sign defect `ξ ↦ J(Xξ) - ε' X(Jξ)` of a matrix `X`. -/
def signDefect (X : Matrix K K ℂ) : (K → ℂ) → (K → ℂ) :=
  fun ξ => R.J (X *ᵥ ξ) - ((R.diracSign : ℤ) : ℂ) • (X *ᵥ R.J ξ)

theorem signDefect_add (X Y : Matrix K K ℂ) :
    R.signDefect (X + Y) = R.signDefect X + R.signDefect Y := by
  funext ξ
  simp only [signDefect, add_mulVec, map_add, smul_add, Pi.add_apply]
  abel

theorem signDefect_smul (r : ℝ) (X : Matrix K K ℂ) :
    R.signDefect (r • X) = r • R.signDefect X := by
  funext ξ
  simp only [signDefect, Matrix.smul_mulVec, J_real_smul, Pi.smul_apply, smul_sub]
  rw [smul_comm]

end CoordinateRealStructure

/-- **`def:marked-spectral-triple`.**  A marked finite spectral triple
`𝖲 = (𝒜, ℋ = ℂ^K, π, D, J, γ; 𝔪)` in an orthonormal coordinate basis: a unital
`*`-representation `π` of the complex `*`-algebra `𝒜`, a self-adjoint Dirac matrix
`D`, an optional grading `γ` (self-adjoint involution commuting with `π(𝒜)` and
anticommuting with `D`), an optional real structure `J` with Dirac sign
`J D = ε' D J` (and `J γ = ε'' γ J` when both are present), and declared operator
marks `𝔪 : ι → Matrix K K ℂ`.  Absent marks impose no condition. -/
structure MarkedFiniteSpectralTriple (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A]
    (K : Type*) [Fintype K] [DecidableEq K] (ι : Type*) where
  rep : A →⋆ₐ[ℂ] Matrix K K ℂ
  dirac : Matrix K K ℂ
  dirac_isHermitian : dirac.IsHermitian
  grading : Option (Matrix K K ℂ)
  grading_spec : ∀ g, grading = some g →
    g.IsHermitian ∧ g * g = 1 ∧ (∀ a, g * rep a = rep a * g) ∧ dirac * g + g * dirac = 0
  real : Option (CoordinateRealStructure K)
  real_dirac : ∀ R, real = some R → ∀ ξ,
    R.J (dirac *ᵥ ξ) = ((R.diracSign : ℤ) : ℂ) • (dirac *ᵥ R.J ξ)
  real_grading : ∀ R g, real = some R → grading = some g → ∀ ξ,
    R.J (g *ᵥ ξ) = ((R.gradingSign : ℤ) : ℂ) • (g *ᵥ R.J ξ)
  mark : ι → Matrix K K ℂ

namespace MarkedFiniteSpectralTriple

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] {ι : Type*}
variable (S : MarkedFiniteSpectralTriple A K ι)

open HSMatrix

/-- The commutator derivation `X ↦ (a ↦ [X, π(a)])` on matrices. -/
def matDerivation : Matrix K K ℂ →ₗ[ℝ] (A → Matrix K K ℂ) where
  toFun X a := X * S.rep a - S.rep a * X
  map_add' X Y := by
    funext a
    simp only [add_mul, mul_add, Pi.add_apply]
    abel
  map_smul' r X := by
    funext a
    simp only [Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply, Pi.smul_apply, smul_sub]

/-- The grading defect `Xγ + γX` (zero when no grading is declared). -/
def gradingDefect (X : Matrix K K ℂ) : Matrix K K ℂ :=
  S.grading.elim 0 fun g => X * g + g * X

/-- The real-structure defect `J X - ε' X J` (zero when no real structure is declared). -/
def realDefect (X : Matrix K K ℂ) : (K → ℂ) → (K → ℂ) :=
  S.real.elim 0 fun R => R.signDefect X

/-- The declared linear sign equations: self-adjointness `Xᴴ - X`, the grading defect and
the real-structure defect. -/
def matSigns : Matrix K K ℂ →ₗ[ℝ]
    (Matrix K K ℂ × Matrix K K ℂ × ((K → ℂ) → (K → ℂ))) where
  toFun X := (Xᴴ - X, S.gradingDefect X, S.realDefect X)
  map_add' X Y := by
    simp only [gradingDefect, realDefect, conjTranspose_add, Prod.mk_add_mk]
    refine Prod.ext (by abel) (Prod.ext ?_ ?_)
    · cases S.grading <;> simp [add_mul, mul_add] <;> abel
    · cases S.real <;> simp [CoordinateRealStructure.signDefect_add]
  map_smul' r X := by
    simp only [gradingDefect, realDefect, conjTranspose_smul, star_trivial, RingHom.id_apply,
      Prod.smul_mk, smul_sub]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · cases S.grading <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_add]
    · cases S.real <;> simp [CoordinateRealStructure.signDefect_smul]

/-- The derivation on the Hilbert–Schmidt space. -/
def derivationMap : HSMatrix K →ₗ[ℝ] (A → Matrix K K ℂ) :=
  S.matDerivation.comp (ofMatrix (K := K)).symm.toLinearMap

/-- The declared sign equations on the Hilbert–Schmidt space. -/
def signMap : HSMatrix K →ₗ[ℝ]
    (Matrix K K ℂ × Matrix K K ℂ × ((K → ℂ) → (K → ℂ))) :=
  S.matSigns.comp (ofMatrix (K := K)).symm.toLinearMap

/-- The compatible commutant inside the Hilbert–Schmidt space. -/
abbrev commutant : Submodule ℝ (HSMatrix K) :=
  compatibleAnchor S.derivationMap S.signMap

/-- **`eq:commutant-space`.**  The compatible real commutant
`c_S = {C ∈ π(𝒜)'_sa : Cγ + γC = 0, JC = ε'CJ}` as a real subspace of matrices. -/
def commutantSpace : Submodule ℝ (Matrix K K ℂ) :=
  S.commutant.comap (ofMatrix (K := K)).toLinearMap

/-- An `m`-component real linear commutant-coordinate map `α : c_S → ℝ^m`. -/
abbrev CommutantCoordinateMap (m : ℕ) := S.commutantSpace →ₗ[ℝ] (Fin m → ℝ)

/-- `q_S = dim_ℝ c_S`. -/
noncomputable def commutantDim : ℕ := Module.finrank ℝ S.commutantSpace

/-- The real Hilbert–Schmidt orthogonal projection `P_{c_S}` on matrices. -/
noncomputable def commutantProjection (X : Matrix K K ℂ) : Matrix K K ℂ :=
  ofMatrix.symm (S.commutant.starProjection (ofMatrix X))

/-- The centered implementer `D_der = D - P_{c_S} D` (eq:centered-D). -/
noncomputable def centeredDirac : Matrix K K ℂ :=
  S.dirac - S.commutantProjection S.dirac

/-- Self-adjoint matrices with the declared grading and reality signs implementing the
same commutator derivation as `D`. -/
def IsCompatibleImplementer (X : Matrix K K ℂ) : Prop :=
  X.IsHermitian ∧ (∀ g, S.grading = some g → X * g + g * X = 0) ∧
    (∀ R, S.real = some R → ∀ ξ,
      R.J (X *ᵥ ξ) = ((R.diracSign : ℤ) : ℂ) • (X *ᵥ R.J ξ)) ∧
    ∀ a, X * S.rep a - S.rep a * X = S.dirac * S.rep a - S.rep a * S.dirac

theorem matSigns_eq_zero_iff (X : Matrix K K ℂ) :
    S.matSigns X = 0 ↔ X.IsHermitian ∧ (∀ g, S.grading = some g → X * g + g * X = 0) ∧
      (∀ R, S.real = some R → ∀ ξ,
        R.J (X *ᵥ ξ) = ((R.diracSign : ℤ) : ℂ) • (X *ᵥ R.J ξ)) := by
  change ((Xᴴ - X, S.gradingDefect X, S.realDefect X) :
      Matrix K K ℂ × Matrix K K ℂ × ((K → ℂ) → (K → ℂ))) = 0 ↔ _
  rw [Prod.mk_eq_zero, Prod.mk_eq_zero, sub_eq_zero]
  apply and_congr Iff.rfl
  apply and_congr
  · unfold gradingDefect
    cases S.grading with
    | none => simp
    | some g => simp
  · unfold realDefect
    cases S.real with
    | none => simp
    | some R =>
      simp only [Option.elim_some, Option.some.injEq, forall_eq']
      constructor
      · intro h ξ
        exact sub_eq_zero.mp (congrFun h ξ)
      · intro h
        funext ξ
        exact sub_eq_zero.mpr (h ξ)

theorem matSigns_dirac : S.matSigns S.dirac = 0 :=
  (S.matSigns_eq_zero_iff S.dirac).mpr
    ⟨S.dirac_isHermitian, fun g hg => (S.grading_spec g hg).2.2.2, S.real_dirac⟩

theorem mem_commutant_iff (X : HSMatrix K) :
    X ∈ S.commutant ↔ S.matDerivation (ofMatrix.symm X) = 0 ∧
      S.matSigns (ofMatrix.symm X) = 0 := by
  simp [commutant, compatibleAnchor, derivationMap, signMap]

/-- **`eq:commutant-space`** unfolded: membership in `c_S`. -/
theorem mem_commutantSpace_iff (C : Matrix K K ℂ) :
    C ∈ S.commutantSpace ↔ C.IsHermitian ∧ (∀ a, C * S.rep a = S.rep a * C) ∧
      (∀ g, S.grading = some g → C * g + g * C = 0) ∧
      (∀ R, S.real = some R → ∀ ξ,
        R.J (C *ᵥ ξ) = ((R.diracSign : ℤ) : ℂ) • (C *ᵥ R.J ξ)) := by
  change ofMatrix C ∈ S.commutant ↔ _
  rw [mem_commutant_iff, ofMatrix_symm_ofMatrix, matSigns_eq_zero_iff]
  have hder : S.matDerivation C = 0 ↔ ∀ a, C * S.rep a = S.rep a * C := by
    constructor
    · intro h a
      exact sub_eq_zero.mp (congrFun h a)
    · intro h
      funext a
      exact sub_eq_zero.mpr (h a)
  rw [hder]
  tauto

theorem mem_commutantSpace_iff_ofMatrix (C : Matrix K K ℂ) :
    C ∈ S.commutantSpace ↔ ofMatrix C ∈ S.commutant := Iff.rfl

/-- Compatible implementers are exactly the points of the abstract marked derivation
fibre of `D`. -/
theorem isCompatibleImplementer_iff (X : Matrix K K ℂ) :
    S.IsCompatibleImplementer X ↔
      SameMarkedDerivation S.derivationMap S.signMap (ofMatrix S.dirac) (ofMatrix X) := by
  unfold SameMarkedDerivation
  simp only [derivationMap, signMap, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, ofMatrix_symm_ofMatrix, matSigns_dirac]
  rw [matSigns_eq_zero_iff]
  have hder : S.matDerivation X = S.matDerivation S.dirac ↔
      ∀ a, X * S.rep a - S.rep a * X = S.dirac * S.rep a - S.rep a * S.dirac := by
    constructor
    · intro h a
      exact congrFun h a
    · intro h
      funext a
      exact h a
  rw [hder, IsCompatibleImplementer]
  tauto

theorem commutantProjection_mem (X : Matrix K K ℂ) :
    S.commutantProjection X ∈ S.commutantSpace :=
  S.commutant.starProjection_apply_mem (ofMatrix X)

/-- The projection `P_{c_S} X` as an element of `c_S`. -/
noncomputable def commutantProjectionMem (X : Matrix K K ℂ) : S.commutantSpace :=
  ⟨S.commutantProjection X, S.commutantProjection_mem X⟩

theorem centeredDirac_eq :
    ofMatrix S.centeredDirac =
      centeredRepresentative S.derivationMap S.signMap (ofMatrix S.dirac) := rfl

/-- `q_S` equals the abstract anchor rank of the Hilbert–Schmidt model. -/
theorem commutantDim_eq_anchorRank :
    S.commutantDim = anchorRank (derivation := S.derivationMap) (signs := S.signMap) := by
  unfold commutantDim anchorRank
  have hmap : S.commutantSpace.map (ofMatrix (K := K)).toLinearMap = S.commutant :=
    Submodule.map_comap_eq_of_surjective (ofMatrix (K := K)).surjective _
  exact (((ofMatrix (K := K)).submoduleMap S.commutantSpace).trans
    (LinearEquiv.ofEq _ _ hmap)).finrank_eq

/-- The commutant coordinate map transported to the Hilbert–Schmidt model. -/
def toAnchorCoordinates {m : ℕ} (α : S.CommutantCoordinateMap m) :
    compatibleAnchor S.derivationMap S.signMap →ₗ[ℝ] (Fin m → ℝ) where
  toFun c := α ⟨ofMatrix.symm (c : HSMatrix K), c.2⟩
  map_add' c c' := by
    rw [← map_add]
    rfl
  map_smul' r c := by
    rw [RingHom.id_apply, ← map_smul]
    rfl

theorem toAnchorCoordinates_apply {m : ℕ} (α : S.CommutantCoordinateMap m) (X : Matrix K K ℂ) :
    S.toAnchorCoordinates α (S.commutant.orthogonalProjectionOnto (ofMatrix X)) =
      α (S.commutantProjectionMem X) := rfl

theorem toAnchorCoordinates_injective {m : ℕ} (α : S.CommutantCoordinateMap m)
    (hα : Function.Injective α) : Function.Injective (S.toAnchorCoordinates α) := by
  intro c c' h
  have := hα h
  apply Subtype.ext
  exact congrArg Subtype.val this


/-! #### `thm:commutant-fibre` -/

theorem dirac_isCompatibleImplementer : S.IsCompatibleImplementer S.dirac :=
  ⟨S.dirac_isHermitian, fun g hg => (S.grading_spec g hg).2.2.2, S.real_dirac, fun _ => rfl⟩

/-- **`eq:Dirac-affine`.**  The compatible implementers of the commutator derivation of
`D` are exactly `D + c_S`. -/
theorem isCompatibleImplementer_iff_exists (X : Matrix K K ℂ) :
    S.IsCompatibleImplementer X ↔ ∃ C ∈ S.commutantSpace, X = S.dirac + C := by
  rw [isCompatibleImplementer_iff, complete_solution_fibre]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨ofMatrix.symm (c : HSMatrix K), c.2, hc⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨⟨ofMatrix C, hC⟩, rfl⟩

theorem centeredDirac_isCompatibleImplementer : S.IsCompatibleImplementer S.centeredDirac := by
  rw [isCompatibleImplementer_iff, centeredDirac_eq]
  exact centered_sameMarkedDerivation _ _ _

/-- `D_der` has minimal Hilbert–Schmidt norm in the fibre. -/
theorem hsNorm_centeredDirac_le {X : Matrix K K ℂ} (hX : S.IsCompatibleImplementer X) :
    hsNorm S.centeredDirac ≤ hsNorm X := by
  rw [isCompatibleImplementer_iff] at hX
  exact centered_norm_minimal _ _ hX

/-- `D_der` is the unique minimum-norm point of the fibre. -/
theorem hsNorm_eq_centeredDirac_iff {X : Matrix K K ℂ} (hX : S.IsCompatibleImplementer X) :
    hsNorm X = hsNorm S.centeredDirac ↔ X = S.centeredDirac := by
  rw [isCompatibleImplementer_iff] at hX
  exact centered_norm_eq_iff _ _ hX

/-- A real Hilbert–Schmidt orthonormal family of `q_S` elements of `c_S` is an orthonormal
basis of the commutant. -/
def orthonormalBasisOfFamily {q : ℕ} (hq : q = S.commutantDim)
    (C : Fin q → Matrix K K ℂ) (hC : ∀ j, C j ∈ S.commutantSpace)
    (hon : ∀ i j, hsInner (C i) (C j) = if i = j then 1 else 0) :
    OrthonormalBasis (Fin q) ℝ S.commutant :=
  have hon' : Orthonormal ℝ (fun j => (⟨ofMatrix (C j), hC j⟩ : S.commutant)) := by
    rw [orthonormal_iff_ite]
    intro i j
    exact hon i j
  OrthonormalBasis.mk hon'
    (hon'.linearIndependent.span_eq_top_of_card_eq_finrank' (by
      rw [Fintype.card_fin, hq, commutantDim_eq_anchorRank]
      rfl)).ge

theorem orthonormalBasisOfFamily_apply {q : ℕ} (hq : q = S.commutantDim)
    (C : Fin q → Matrix K K ℂ) (hC : ∀ j, C j ∈ S.commutantSpace)
    (hon : ∀ i j, hsInner (C i) (C j) = if i = j then 1 else 0) (j : Fin q) :
    (S.orthonormalBasisOfFamily hq C hC hon j : HSMatrix K) = ofMatrix (C j) := by
  unfold orthonormalBasisOfFamily
  rw [OrthonormalBasis.coe_mk]

/-- **`eq:commutant-reconstruction`** for every compatible implementer:
`X = D_der + ∑_j ⟪C_j, X⟫_{HS,ℝ} C_j` for a real Hilbert–Schmidt orthonormal basis
`C_1, …, C_{q_S}` of `c_S`. -/
theorem eq_centeredDirac_add_sum {q : ℕ} (hq : q = S.commutantDim)
    (C : Fin q → Matrix K K ℂ) (hC : ∀ j, C j ∈ S.commutantSpace)
    (hon : ∀ i j, hsInner (C i) (C j) = if i = j then 1 else 0)
    {X : Matrix K K ℂ} (hX : S.IsCompatibleImplementer X) :
    X = S.centeredDirac + ∑ j, hsInner (C j) X • C j := by
  rw [isCompatibleImplementer_iff] at hX
  have h := eq_centered_add_sum S.derivationMap S.signMap
    (S.orthonormalBasisOfFamily hq C hC hon) (ofMatrix X)
  rw [centeredRepresentative_eq_of_same _ _ hX] at h
  have hsum : ∑ i, ⟪((S.orthonormalBasisOfFamily hq C hC hon i : S.commutant) : HSMatrix K),
      ofMatrix X⟫_ℝ • ((S.orthonormalBasisOfFamily hq C hC hon i : S.commutant) : HSMatrix K) =
      ofMatrix (∑ j, hsInner (C j) X • C j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [orthonormalBasisOfFamily_apply, map_smul, HSMatrix.inner_ofMatrix]
  rw [hsum] at h
  exact h

/-- **`eq:commutant-reconstruction`**: `D = D_der + ∑_j α_j(D) C_j` with
`α_j(D) = ⟪C_j, D⟫_{HS,ℝ}` (eq:commutant-coordinates). -/
theorem dirac_eq_centeredDirac_add_sum {q : ℕ} (hq : q = S.commutantDim)
    (C : Fin q → Matrix K K ℂ) (hC : ∀ j, C j ∈ S.commutantSpace)
    (hon : ∀ i j, hsInner (C i) (C j) = if i = j then 1 else 0) :
    S.dirac = S.centeredDirac + ∑ j, hsInner (C j) S.dirac • C j :=
  S.eq_centeredDirac_add_sum hq C hC hon S.dirac_isCompatibleImplementer

/-- Recovery from the `q_S` orthonormal commutant coordinates: a compatible implementer
with the same coordinates as `D` is `D`. -/
theorem eq_dirac_of_hsInner_eq {q : ℕ} (hq : q = S.commutantDim)
    (C : Fin q → Matrix K K ℂ) (hC : ∀ j, C j ∈ S.commutantSpace)
    (hon : ∀ i j, hsInner (C i) (C j) = if i = j then 1 else 0)
    {X : Matrix K K ℂ} (hX : S.IsCompatibleImplementer X)
    (hcoord : ∀ j, hsInner (C j) X = hsInner (C j) S.dirac) : X = S.dirac :=
  calc X = S.centeredDirac + ∑ j, hsInner (C j) X • C j :=
        S.eq_centeredDirac_add_sum hq C hC hon hX
    _ = S.centeredDirac + ∑ j, hsInner (C j) S.dirac • C j := by simp only [hcoord]
    _ = S.dirac := (S.dirac_eq_centeredDirac_add_sum hq C hC hon).symm

/-- Real Hilbert–Schmidt orthonormal bases of `c_S` exist (the hypotheses of the
reconstruction formula are satisfiable for every marked triple). -/
theorem exists_orthonormal_commutant_family :
    ∃ C : Fin S.commutantDim → Matrix K K ℂ, (∀ j, C j ∈ S.commutantSpace) ∧
      ∀ i j, hsInner (C i) (C j) = if i = j then 1 else 0 := by
  have hdim : Module.finrank ℝ S.commutant = S.commutantDim := by
    rw [commutantDim_eq_anchorRank]
    rfl
  let b := (stdOrthonormalBasis ℝ S.commutant).reindex (finCongr hdim)
  refine ⟨fun j => ofMatrix.symm (b j : HSMatrix K), fun j => (b j).2, fun i j => ?_⟩
  have := orthonormal_iff_ite.mp b.orthonormal i j
  exact this

/-- Recovery from any injective real linear commutant-coordinate map. -/
theorem eq_dirac_of_commutantCoordinates_eq {m : ℕ} (α : S.CommutantCoordinateMap m)
    (hα : Function.Injective α) {X : Matrix K K ℂ} (hX : S.IsCompatibleImplementer X)
    (hcoord : α (S.commutantProjectionMem X) = α (S.commutantProjectionMem S.dirac)) :
    X = S.dirac := by
  rw [isCompatibleImplementer_iff] at hX
  exact eq_of_anchor_coordinates_eq _ _ (S.toAnchorCoordinates α)
    (S.toAnchorCoordinates_injective α hα) hX hcoord

/-- Fewer than `q_S` real linear commutant coordinates are never injective. -/
theorem not_injective_of_lt_commutantDim {m : ℕ} (hm : m < S.commutantDim)
    (α : S.CommutantCoordinateMap m) : ¬ Function.Injective α := by
  intro hα
  have := LinearMap.finrank_le_finrank_of_injective hα
  rw [Module.finrank_fin_fun] at this
  exact absurd hm (not_lt.mpr this)

/-- Sharpness: with fewer than `q_S` coordinates, some compatible implementer different
from `D` has the same coordinates as `D`. -/
theorem exists_ne_of_lt_commutantDim {m : ℕ} (hm : m < S.commutantDim)
    (α : S.CommutantCoordinateMap m) :
    ∃ X, S.IsCompatibleImplementer X ∧ X ≠ S.dirac ∧
      α (S.commutantProjectionMem X) = α (S.commutantProjectionMem S.dirac) := by
  rw [commutantDim_eq_anchorRank] at hm
  obtain ⟨Y, hY, hne, hcoord⟩ :=
    exists_ne_of_lt_anchorRank _ _ hm (S.toAnchorCoordinates α) (ofMatrix S.dirac)
  exact ⟨ofMatrix.symm Y, (S.isCompatibleImplementer_iff _).mpr hY, hne, hcoord⟩

/-- Within the fibre, the canonical derivation-only reconstruction `D_der` is exactly
the centered class `P_{c_S} X = 0`. -/
theorem eq_centeredDirac_iff {X : Matrix K K ℂ} (hX : S.IsCompatibleImplementer X) :
    X = S.centeredDirac ↔ S.commutantProjection X = 0 := by
  rw [isCompatibleImplementer_iff] at hX
  have h := eq_centered_iff_anchor_projection_eq_zero S.derivationMap S.signMap hX
  exact h

theorem centeredDirac_eq_dirac_iff :
    S.centeredDirac = S.dirac ↔ S.commutantProjection S.dirac = 0 :=
  centeredRepresentative_eq_self_iff S.derivationMap S.signMap (ofMatrix S.dirac)

/-- **`thm:commutant-fibre`.**  For a marked finite spectral triple `S`:
1. (eq:Dirac-affine) the self-adjoint operators with the declared grading and reality
   signs implementing the commutator derivation of `D` are exactly `D + c_S`;
2. `D_der = D - P_{c_S} D` lies in this fibre and is its unique minimum
   Hilbert–Schmidt-norm representative;
3. for every real Hilbert–Schmidt orthonormal basis `C_1, …, C_{q_S}` of `c_S`,
   `D = D_der + ∑_j ⟪C_j, D⟫ C_j` (eq:commutant-coordinates,
   eq:commutant-reconstruction), and every compatible implementer with the same
   `q_S` coordinates equals `D`; such bases exist;
4. any injective real linear commutant-coordinate map recovers `D`, while for
   `m < q_S` every `m`-component map leaves two distinct compatible implementers with
   equal coordinates;
5. the canonical derivation-only reconstruction is exactly the centered class:
   a compatible `X` equals `D_der` iff `P_{c_S} X = 0`, and `D = D_der` iff
   `P_{c_S} D = 0`. -/
theorem commutant_fibre :
    (∀ X, S.IsCompatibleImplementer X ↔ ∃ C ∈ S.commutantSpace, X = S.dirac + C) ∧
    S.IsCompatibleImplementer S.centeredDirac ∧
    (∀ X, S.IsCompatibleImplementer X → hsNorm S.centeredDirac ≤ hsNorm X) ∧
    (∀ X, S.IsCompatibleImplementer X →
      (hsNorm X = hsNorm S.centeredDirac ↔ X = S.centeredDirac)) ∧
    (∀ C : Fin S.commutantDim → Matrix K K ℂ, (∀ j, C j ∈ S.commutantSpace) →
      (∀ i j, hsInner (C i) (C j) = if i = j then 1 else 0) →
      S.dirac = S.centeredDirac + ∑ j, hsInner (C j) S.dirac • C j ∧
      ∀ X, S.IsCompatibleImplementer X →
        (∀ j, hsInner (C j) X = hsInner (C j) S.dirac) → X = S.dirac) ∧
    (∃ C : Fin S.commutantDim → Matrix K K ℂ, (∀ j, C j ∈ S.commutantSpace) ∧
      ∀ i j, hsInner (C i) (C j) = if i = j then 1 else 0) ∧
    (∀ (m : ℕ) (α : S.CommutantCoordinateMap m), Function.Injective α →
      ∀ X, S.IsCompatibleImplementer X →
        α (S.commutantProjectionMem X) = α (S.commutantProjectionMem S.dirac) →
        X = S.dirac) ∧
    (∀ (m : ℕ) (α : S.CommutantCoordinateMap m), m < S.commutantDim →
      ∃ X, S.IsCompatibleImplementer X ∧ X ≠ S.dirac ∧
        α (S.commutantProjectionMem X) = α (S.commutantProjectionMem S.dirac)) ∧
    (∀ X, S.IsCompatibleImplementer X → (X = S.centeredDirac ↔ S.commutantProjection X = 0)) ∧
    (S.centeredDirac = S.dirac ↔ S.commutantProjection S.dirac = 0) :=
  ⟨S.isCompatibleImplementer_iff_exists, S.centeredDirac_isCompatibleImplementer,
    fun _ hX => S.hsNorm_centeredDirac_le hX, fun _ hX => S.hsNorm_eq_centeredDirac_iff hX,
    fun C hC hon => ⟨S.dirac_eq_centeredDirac_add_sum rfl C hC hon,
      fun _ hX hcoord => S.eq_dirac_of_hsInner_eq rfl C hC hon hX hcoord⟩,
    S.exists_orthonormal_commutant_family,
    fun _ α hα _ hX hcoord => S.eq_dirac_of_commutantCoordinates_eq α hα hX hcoord,
    fun _ α hm => S.exists_ne_of_lt_commutantDim hm α,
    fun _ hX => S.eq_centeredDirac_iff hX, S.centeredDirac_eq_dirac_iff⟩

/-! #### The real Hilbert–Schmidt projection and finite calibrated recovery -/

/-- `P_{c_S}` is the real Hilbert–Schmidt orthogonal projection: `X - P_{c_S} X` is
Hilbert–Schmidt orthogonal to every `C ∈ c_S`. -/
theorem hsInner_sub_commutantProjection (X C : Matrix K K ℂ) (hC : C ∈ S.commutantSpace) :
    hsInner (X - S.commutantProjection X) C = 0 := by
  have h := S.commutant.starProjection_inner_eq_zero (ofMatrix X) (ofMatrix C) hC
  exact h

/-- `P_{c_S}` fixes `c_S`. -/
theorem commutantProjection_eq_self {C : Matrix K K ℂ} (hC : C ∈ S.commutantSpace) :
    S.commutantProjection C = C := by
  have h := (Submodule.starProjection_eq_self_iff (K := S.commutant)
    (v := ofMatrix C)).mpr hC
  exact h

/-- Replace the Dirac operator of `S` by a compatible implementer, keeping the
represented algebra, grading, real structure and marks. -/
def withDirac (X : Matrix K K ℂ) (hX : S.IsCompatibleImplementer X) :
    MarkedFiniteSpectralTriple A K ι where
  rep := S.rep
  dirac := X
  dirac_isHermitian := hX.1
  grading := S.grading
  grading_spec g hg := ⟨(S.grading_spec g hg).1, (S.grading_spec g hg).2.1,
    (S.grading_spec g hg).2.2.1, hX.2.1 g hg⟩
  real := S.real
  real_dirac := hX.2.2.1
  real_grading := S.real_grading
  mark := S.mark

theorem withDirac_dirac : S.withDirac S.dirac S.dirac_isCompatibleImplementer = S := by
  cases S
  rfl

/-- Two marked finite spectral triples have the same retained finite reconstruction data
(C1): the same represented algebra, symmetry marks, declared operator marks and commutator
derivation. -/
def SameCommutatorData (S' : MarkedFiniteSpectralTriple A K ι) : Prop :=
  S'.rep = S.rep ∧ S'.grading = S.grading ∧ S'.real = S.real ∧ S'.mark = S.mark ∧
    ∀ a, S'.dirac * S.rep a - S.rep a * S'.dirac = S.dirac * S.rep a - S.rep a * S.dirac

theorem isCompatibleImplementer_of_sameCommutatorData {S' : MarkedFiniteSpectralTriple A K ι}
    (h : S.SameCommutatorData S') : S.IsCompatibleImplementer S'.dirac := by
  obtain ⟨-, hgr, hreal, -, hder⟩ := h
  refine ⟨S'.dirac_isHermitian, fun g hg => ?_, fun R hR => ?_, hder⟩
  · exact (S'.grading_spec g (hgr.trans hg)).2.2.2
  · exact S'.real_dirac R (hreal.trans hR)

theorem eq_withDirac_of_sameCommutatorData {S' : MarkedFiniteSpectralTriple A K ι}
    (h : S.SameCommutatorData S') :
    S' = S.withDirac S'.dirac (S.isCompatibleImplementer_of_sameCommutatorData h) := by
  obtain ⟨hrep, hgr, hreal, hmark, -⟩ := h
  cases S'
  cases S
  simp only at hrep hgr hreal hmark
  subst hrep hgr hreal hmark
  rfl

theorem withDirac_sameCommutatorData (X : Matrix K K ℂ) (hX : S.IsCompatibleImplementer X) :
    S.SameCommutatorData (S.withDirac X hX) :=
  ⟨rfl, rfl, rfl, rfl, hX.2.2.2⟩

/-- **`prop:finite-calibrated-recovery`** (and the finite line of `thm:essential-image`).
For marked finite spectral triples `S, S'` with the same represented algebra, symmetry
marks, declared marks and commutator derivation:
1. the centered implementers agree, `S'_der = S_der` (the commutator data determine
   `D_der`);
2. if in addition the `q_S` orthonormal commutant coordinates `⟪C_j, D⟫_{HS,ℝ}` agree,
   then `S' = S`;
3. more generally, equal values of any injective real linear commutant-coordinate map
   force `S' = S`. -/
theorem finite_calibrated_recovery {S' : MarkedFiniteSpectralTriple A K ι}
    (h : S.SameCommutatorData S') :
    S'.centeredDirac = S.centeredDirac ∧
    (∀ C : Fin S.commutantDim → Matrix K K ℂ, (∀ j, C j ∈ S.commutantSpace) →
      (∀ i j, hsInner (C i) (C j) = if i = j then 1 else 0) →
      (∀ j, hsInner (C j) S'.dirac = hsInner (C j) S.dirac) → S' = S) ∧
    (∀ (m : ℕ) (α : S.CommutantCoordinateMap m), Function.Injective α →
      α (S.commutantProjectionMem S'.dirac) = α (S.commutantProjectionMem S.dirac) →
      S' = S) := by
  have hX := S.isCompatibleImplementer_of_sameCommutatorData h
  have hS' := S.eq_withDirac_of_sameCommutatorData h
  have hfinal : S'.dirac = S.dirac → S' = S := by
    intro hD
    rw [hS']
    conv_rhs => rw [← S.withDirac_dirac]
    congr 1
  refine ⟨?_, fun C hC hon hcoord => hfinal (S.eq_dirac_of_hsInner_eq rfl C hC hon hX hcoord),
    fun m α hα hcoord => hfinal (S.eq_dirac_of_commutantCoordinates_eq α hα hX hcoord)⟩
  rw [hS']
  have hsame := (S.isCompatibleImplementer_iff _).mp hX
  have hc := centeredRepresentative_eq_of_same S.derivationMap S.signMap hsame
  exact hc

/-- **Sharpness in `prop:finite-calibrated-recovery`.**  With fewer than `q_S` real linear
commutant coordinates, some marked triple `S' ≠ S` has the same retained finite
reconstruction data and the same coordinates. -/
theorem finite_calibrated_recovery_sharp {m : ℕ} (hm : m < S.commutantDim)
    (α : S.CommutantCoordinateMap m) :
    ∃ S' : MarkedFiniteSpectralTriple A K ι, S.SameCommutatorData S' ∧ S' ≠ S ∧
      α (S.commutantProjectionMem S'.dirac) = α (S.commutantProjectionMem S.dirac) := by
  obtain ⟨X, hX, hne, hcoord⟩ := S.exists_ne_of_lt_commutantDim hm α
  refine ⟨S.withDirac X hX, S.withDirac_sameCommutatorData X hX, fun heq => hne ?_, hcoord⟩
  exact congrArg MarkedFiniteSpectralTriple.dirac heq

end MarkedFiniteSpectralTriple

/-- Non-vacuity witness for `MarkedFiniteSpectralTriple`: the one-dimensional triple
of the scalar matrix algebra with zero Dirac operator and no grading or real
structure. -/
def trivialMarkedFiniteSpectralTriple :
    MarkedFiniteSpectralTriple (Matrix (Fin 1) (Fin 1) ℂ) (Fin 1) Empty where
  rep := StarAlgHom.id ℂ _
  dirac := 0
  dirac_isHermitian := Matrix.isHermitian_zero
  grading := none
  grading_spec := fun _ h => by cases h
  real := none
  real_dirac := fun _ h => by cases h
  real_grading := fun _ _ h _ => by cases h
  mark := Empty.elim

end Triples

end

end RenewalGeometry.MarkedCommutantCoordinates
