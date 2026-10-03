/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.AustereUnitZeroModeExact
import RenewalGeometry.Spectralization.FiniteSpectralizationFunctorScaleExact
/-!
# The finite Hodge--Dirac triple of a finite real differential datum

This file constructs the coordinate packet of
`FiniteRealEvenSpectralizationExact` from the paper's input data and derives
every one of its fields (`predictive_spectral_geometry`,
`thm:finite-Hodge-Dirac`, `prop:hodge-zero-mode`, `prop:no-scale`).

* `FaithfulTracialState A` is a faithful tracial state `τ` on a star algebra,
  and `TracialL2 τ` is the Hilbert space `L²(A, τ)` with `⟪a, b⟫ = τ(a^* b)`.
* For a `FiniteRealDifferentialDatum` (`def:finite-real-differential`) the
  one-form space is the source-minimal carrier `Ran T_δ ⊆ K`, isometric to
  `Ω¹_u(A) / Ker T_δ` with the Gram `Q_δ`.  On `H₀ = L²(A, τ)` and on this
  carrier we define the genuine operators `L_a, R_a, J₀ a = a^*`, `λ(a), ρ(a)`,
  `J₁ = C|_{H₁}`, the derivation `∂ a = δ a` and `B_a b = (∂ a) b`.
* `Packet.ofDatum D τ b₀ b₁` takes the matrices of these operators in arbitrary
  orthonormal bases `b₀, b₁`.  Each packet field (star-adjointness, commuting
  actions, Leibniz block, right-linearity of `B_a`, `J² = I`, `JD = DJ`,
  opposite representation, ...) is a theorem derived from `δ(1) = 0`, the
  Leibniz rule, `Cδ = δ∘*`, the reversal law and traciality of `τ`.

No field of the coordinate packet is assumed.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
  TensorProduct

namespace RenewalGeometry
namespace FiniteHodgeDiracDatum

set_option linter.unusedSectionVars false

noncomputable section

/-! ## Matrices of maps in orthonormal bases -/

section Coordinates

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-- The matrix `⟪c i, f (b j)⟫` of an arbitrary map in orthonormal bases.  For a
linear map this is the usual matrix; for an antilinear map `f` it is the matrix
`j` with `coords (f x) = j * conj (coords x)`. -/
def coordMat (c : OrthonormalBasis κ ℂ F) (b : OrthonormalBasis ι ℂ E) (f : E → F) :
    Matrix κ ι ℂ :=
  Matrix.of fun i j => ⟪c i, f (b j)⟫_ℂ

/-- Orthonormal coordinates `⟪b i, x⟫` of a vector. -/
def coordVec (b : OrthonormalBasis ι ℂ E) (x : E) : ι → ℂ := fun i => ⟪b i, x⟫_ℂ

@[simp] theorem coordMat_apply (c : OrthonormalBasis κ ℂ F) (b : OrthonormalBasis ι ℂ E)
    (f : E → F) (i : κ) (j : ι) : coordMat c b f i j = ⟪c i, f (b j)⟫_ℂ := rfl

theorem coordVec_injective (b : OrthonormalBasis ι ℂ E) :
    Function.Injective (coordVec b) := by
  intro x y h
  rw [← b.sum_repr' x, ← b.sum_repr' y]
  exact Finset.sum_congr rfl fun i _ => by rw [show ⟪b i, x⟫_ℂ = ⟪b i, y⟫_ℂ from congrFun h i]

theorem coordVec_eq_zero_iff (b : OrthonormalBasis ι ℂ E) (x : E) :
    coordVec b x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply coordVec_injective b
    rw [h]; funext i; simp [coordVec]
  · rintro rfl; funext i; simp [coordVec]

/-- Composition with a linear map on the left is matrix multiplication. -/
theorem coordMat_comp_linear (d : OrthonormalBasis μ ℂ G) (c : OrthonormalBasis κ ℂ F)
    (b : OrthonormalBasis ι ℂ E) (g : F →ₗ[ℂ] G) (f : E → F) :
    coordMat d b (fun x => g (f x)) = coordMat d c g * coordMat c b f := by
  ext i j
  simp only [coordMat_apply, Matrix.mul_apply]
  conv_lhs => rw [← c.sum_repr' (f (b j))]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Composition with a unitary on the left is matrix multiplication. -/
theorem coordMat_comp_isometry (d : OrthonormalBasis μ ℂ G) (c : OrthonormalBasis κ ℂ F)
    (b : OrthonormalBasis ι ℂ E) (g : F ≃ₗᵢ[ℂ] G) (f : E → F) :
    coordMat d b (fun x => g (f x)) = coordMat d c g * coordMat c b f :=
  coordMat_comp_linear d c b g.toLinearEquiv.toLinearMap f

/-- Composition with an antilinear map on the left: the right factor is
conjugated entrywise. -/
theorem coordMat_comp_antilinear (d : OrthonormalBasis μ ℂ G) (c : OrthonormalBasis κ ℂ F)
    (b : OrthonormalBasis ι ℂ E) (g : F →ₗ⋆[ℂ] G) (f : E → F) :
    coordMat d b (fun x => g (f x)) = coordMat d c g * (coordMat c b f).map star := by
  ext i j
  simp only [coordMat_apply, Matrix.mul_apply, Matrix.map_apply]
  conv_lhs => rw [← c.sum_repr' (f (b j))]
  simp only [map_sum, LinearMap.map_smulₛₗ, inner_sum, inner_smul_right]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]; rfl

/-- Matrix of a vector image under a linear map. -/
theorem coordMat_mulVec (c : OrthonormalBasis κ ℂ F) (b : OrthonormalBasis ι ℂ E)
    (f : E →ₗ[ℂ] F) (x : E) :
    coordMat c b f *ᵥ coordVec b x = coordVec c (f x) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, coordMat_apply, coordVec]
  conv_rhs => rw [← b.sum_repr' x]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem coordMat_id [DecidableEq ι] (b : OrthonormalBasis ι ℂ E) :
    coordMat b b (fun x => x) = 1 := by
  ext i j
  rw [coordMat_apply, b.inner_eq_ite, Matrix.one_apply]

theorem coordMat_sub (c : OrthonormalBasis κ ℂ F) (b : OrthonormalBasis ι ℂ E)
    (f g : E → F) :
    coordMat c b (fun x => f x - g x) = coordMat c b f - coordMat c b g := by
  ext i j
  simp [inner_sub_right]

theorem coordMat_smul (c : OrthonormalBasis κ ℂ F) (b : OrthonormalBasis ι ℂ E)
    (z : ℂ) (f : E → F) :
    coordMat c b (fun x => z • f x) = z • coordMat c b f := by
  ext i j
  simp [inner_smul_right]

theorem coordMat_zero (c : OrthonormalBasis κ ℂ F) (b : OrthonormalBasis ι ℂ E) :
    coordMat c b (fun _ : E => (0 : F)) = 0 := by
  ext i j
  simp

/-- Formally adjoint maps have conjugate-transposed matrices. -/
theorem coordMat_of_adjoint (c : OrthonormalBasis κ ℂ F) (b : OrthonormalBasis ι ℂ E)
    (f : E → F) (g : F → E) (h : ∀ x y, ⟪f x, y⟫_ℂ = ⟪x, g y⟫_ℂ) :
    coordMat b c g = (coordMat c b f)ᴴ := by
  ext i j
  simp only [coordMat_apply, Matrix.conjTranspose_apply]
  rw [← h, ← inner_conj_symm]
  rfl

/-- The Gram matrix of the images of the basis vectors. -/
theorem coordMat_conjTranspose_mul_self (c : OrthonormalBasis κ ℂ F)
    (b : OrthonormalBasis ι ℂ E) (f : E → F) :
    (coordMat c b f)ᴴ * coordMat c b f = Matrix.of fun k l => ⟪f (b k), f (b l)⟫_ℂ := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, coordMat_apply, Matrix.of_apply]
  rw [← c.sum_inner_mul_inner]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← inner_conj_symm (c i) (f (b k))]; simp [Complex.star_def]

/-- An antiunitary map has a unitary coordinate matrix. -/
theorem coordMat_antiunitary [DecidableEq ι] (b : OrthonormalBasis ι ℂ E) (f : E → E)
    (h : ∀ x y, ⟪f x, f y⟫_ℂ = ⟪y, x⟫_ℂ) :
    (coordMat b b f)ᴴ * coordMat b b f = 1 := by
  rw [coordMat_conjTranspose_mul_self]
  ext k l
  rw [Matrix.of_apply, h, b.inner_eq_ite, Matrix.one_apply]
  by_cases hkl : k = l
  · subst hkl; simp
  · simp [hkl, Ne.symm hkl]

/-- A unitary map has a unitary coordinate matrix. -/
theorem coordMat_unitary [DecidableEq ι] (c : OrthonormalBasis ι ℂ F)
    (b : OrthonormalBasis ι ℂ E) (f : E → F) (h : ∀ x y, ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ) :
    (coordMat c b f)ᴴ * coordMat c b f = 1 := by
  rw [coordMat_conjTranspose_mul_self]
  ext k l
  rw [Matrix.of_apply, h, b.inner_eq_ite, Matrix.one_apply]

/-- Linear maps with equal matrices are equal. -/
theorem coordMat_injective (c : OrthonormalBasis κ ℂ F) (b : OrthonormalBasis ι ℂ E)
    {f g : E →ₗ[ℂ] F} (h : coordMat c b f = coordMat c b g) : f = g := by
  apply b.toBasis.ext
  intro j
  rw [OrthonormalBasis.coe_toBasis]
  apply coordVec_injective c
  funext i
  exact congrFun (congrFun h i) j

end Coordinates

/-! ## Faithful tracial states and `L²(A, τ)` -/

/-- A faithful tracial state on a complex star algebra: a positive normalized
linear functional with `τ(ab) = τ(ba)` and `τ(a^* a) = 0 ⇒ a = 0`. -/
structure FaithfulTracialState (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] where
  /-- The underlying linear functional. -/
  toLinearMap : A →ₗ[ℂ] ℂ
  map_star : ∀ a, toLinearMap (star a) = star (toLinearMap a)
  nonneg : ∀ a, 0 ≤ toLinearMap (star a * a)
  faithful : ∀ a, toLinearMap (star a * a) = 0 → a = 0
  trace_comm : ∀ a b, toLinearMap (a * b) = toLinearMap (b * a)
  map_one : toLinearMap 1 = 1

section L2

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

namespace FaithfulTracialState

theorem one_ne_zero (τ : FaithfulTracialState A) : (1 : A) ≠ 0 := by
  intro h
  have := τ.map_one
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem nontrivial (τ : FaithfulTracialState A) : Nontrivial A := ⟨⟨1, 0, τ.one_ne_zero⟩⟩

end FaithfulTracialState

/-- The GNS Hilbert space `L²(A, τ)`: the algebra itself with
`⟪a, b⟫ = τ(a^* b)`. -/
def TracialL2 (_τ : FaithfulTracialState A) : Type _ := A

namespace TracialL2

variable (τ : FaithfulTracialState A)

instance : AddCommGroup (TracialL2 τ) := inferInstanceAs (AddCommGroup A)
instance : Module ℂ (TracialL2 τ) := inferInstanceAs (Module ℂ A)

/-- The identification of `L²(A, τ)` with `A`. -/
def equiv : TracialL2 τ ≃ₗ[ℂ] A := LinearEquiv.refl ℂ A

instance core : InnerProductSpace.Core ℂ (TracialL2 τ) where
  inner x y := τ.toLinearMap (star (equiv τ x) * equiv τ y)
  conj_inner_symm x y := by
    change star (τ.toLinearMap (star (equiv τ y) * equiv τ x)) =
      τ.toLinearMap (star (equiv τ x) * equiv τ y)
    rw [← τ.map_star, star_mul, star_star]
  re_inner_nonneg x := by
    have h := τ.nonneg (equiv τ x)
    exact (Complex.nonneg_iff.mp h).1
  add_left x y z := by
    change τ.toLinearMap (star (equiv τ x + equiv τ y) * equiv τ z) = _
    rw [star_add, add_mul, map_add]
  smul_left x y r := by
    change τ.toLinearMap (star (r • equiv τ x) * equiv τ y) = _
    rw [star_smul, smul_mul_assoc, map_smul, smul_eq_mul]
    rfl
  definite x h := τ.faithful (equiv τ x) h

instance : NormedAddCommGroup (TracialL2 τ) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (TracialL2 τ) := InnerProductSpace.ofCore _

instance [FiniteDimensional ℂ A] : FiniteDimensional ℂ (TracialL2 τ) :=
  inferInstanceAs (FiniteDimensional ℂ A)

theorem inner_def (x y : TracialL2 τ) :
    ⟪x, y⟫_ℂ = τ.toLinearMap (star (equiv τ x) * equiv τ y) := rfl

/-- The vector of `L²(A, τ)` represented by `a ∈ A`. -/
def ofA (a : A) : TracialL2 τ := (equiv τ).symm a

@[simp] theorem equiv_ofA (a : A) : equiv τ (ofA τ a) = a := rfl

/-- Left multiplication `L_a` on `L²(A, τ)`. -/
def mulLeft (a : A) : TracialL2 τ →ₗ[ℂ] TracialL2 τ :=
  (equiv τ).symm.toLinearMap ∘ₗ LinearMap.mulLeft ℂ a ∘ₗ (equiv τ).toLinearMap

/-- Right multiplication `R_a` on `L²(A, τ)`. -/
def mulRight (a : A) : TracialL2 τ →ₗ[ℂ] TracialL2 τ :=
  (equiv τ).symm.toLinearMap ∘ₗ LinearMap.mulRight ℂ a ∘ₗ (equiv τ).toLinearMap

/-- The antilinear involution `J₀ a = a^*` on `L²(A, τ)`. -/
def involution : TracialL2 τ →ₗ⋆[ℂ] TracialL2 τ where
  toFun x := ofA τ (star (equiv τ x))
  map_add' x y := by
    change ofA τ (star (equiv τ x + equiv τ y)) = _
    rw [star_add]; rfl
  map_smul' z x := by
    change ofA τ (star (z • equiv τ x)) = _
    rw [star_smul]; rfl

@[simp] theorem equiv_mulLeft (a : A) (x : TracialL2 τ) :
    equiv τ (mulLeft τ a x) = a * equiv τ x := rfl

@[simp] theorem equiv_mulRight (a : A) (x : TracialL2 τ) :
    equiv τ (mulRight τ a x) = equiv τ x * a := rfl

@[simp] theorem equiv_involution (x : TracialL2 τ) :
    equiv τ (involution τ x) = star (equiv τ x) := rfl

theorem ext_equiv {x y : TracialL2 τ} (h : equiv τ x = equiv τ y) : x = y :=
  (equiv τ).injective h

theorem inner_mulLeft (a : A) (x y : TracialL2 τ) :
    ⟪mulLeft τ a x, y⟫_ℂ = ⟪x, mulLeft τ (star a) y⟫_ℂ := by
  simp only [inner_def, equiv_mulLeft, star_mul, mul_assoc]

theorem inner_mulRight (a : A) (x y : TracialL2 τ) :
    ⟪mulRight τ a x, y⟫_ℂ = ⟪x, mulRight τ (star a) y⟫_ℂ := by
  simp only [inner_def, equiv_mulRight, star_mul]
  rw [mul_assoc, τ.trace_comm, mul_assoc]

theorem inner_involution (x y : TracialL2 τ) :
    ⟪involution τ x, involution τ y⟫_ℂ = ⟪y, x⟫_ℂ := by
  simp only [inner_def, equiv_involution, star_star]
  exact τ.trace_comm _ _

theorem involution_involution (x : TracialL2 τ) : involution τ (involution τ x) = x := by
  apply ext_equiv; simp

theorem mulLeft_mulRight_comm (a b : A) (x : TracialL2 τ) :
    mulLeft τ a (mulRight τ b x) = mulRight τ b (mulLeft τ a x) := by
  apply ext_equiv; simp [mul_assoc]

theorem involution_mulLeft (a : A) (x : TracialL2 τ) :
    involution τ (mulLeft τ a x) = mulRight τ (star a) (involution τ x) := by
  apply ext_equiv; simp [star_mul]

end TracialL2

end L2

end

end FiniteHodgeDiracDatum

/-! ## The Hodge operators of a finite real differential datum -/

namespace AustereUnitZeroMode.FiniteRealDifferentialDatum

open FiniteDifferentialOccurrenceCompiler FiniteDifferentialOccurrenceCompiler.Packet
  FiniteHodgeDiracDatum

noncomputable section

variable {n : ℕ} {A K : Type*}
  [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (D : FiniteRealDifferentialDatum n A K)

/-- The algebra of a datum is finite dimensional (it carries a finite basis). -/
theorem finiteDimensional_algebra (D₀ : FiniteRealDifferentialDatum n A K) :
    FiniteDimensional ℂ A :=
  Module.Finite.of_basis (FiniteDifferentialOccurrenceCompiler.Packet.basis D₀.packet)

theorem delta_mem (a : A) : D.packet.delta a ∈ D.sourceMinimalCarrier :=
  ⟨universalDifferential a, D.universalFactor_differential a⟩

theorem left_mem (a : A) {ξ : K} (h : ξ ∈ D.sourceMinimalCarrier) :
    D.packet.left a ξ ∈ D.sourceMinimalCarrier := by
  obtain ⟨ω, rfl⟩ := h
  exact ⟨oneFormLeft a ω, D.packet.universalFactor_left a ω⟩

theorem right_mem (a : A) {ξ : K} (h : ξ ∈ D.sourceMinimalCarrier) :
    D.packet.right a ξ ∈ D.sourceMinimalCarrier := by
  obtain ⟨ω, rfl⟩ := h
  exact ⟨oneFormRight a ω, D.packet.universalFactor_right D.2 a ω⟩

theorem reverse_mem {ξ : K} (h : ξ ∈ D.sourceMinimalCarrier) :
    D.packet.reverse ξ ∈ D.sourceMinimalCarrier := by
  obtain ⟨ω, rfl⟩ := h
  exact ⟨oneFormReversal ω, D.packet.universalFactor_reversal D.2 ω⟩

/-- The left action `λ(a)` restricted to the one-form space `H₁(δ) = Ran T_δ`. -/
def carrierLeft (a : A) : D.sourceMinimalCarrier →ₗ[ℂ] D.sourceMinimalCarrier :=
  (D.packet.left a).restrict (fun _ h => D.left_mem a h)

/-- The right action `ρ(a)` restricted to `H₁(δ)`. -/
def carrierRight (a : A) : D.sourceMinimalCarrier →ₗ[ℂ] D.sourceMinimalCarrier :=
  (D.packet.right a).restrict (fun _ h => D.right_mem a h)

/-- The real structure `J₁ = C|_{H₁(δ)}`; under `Ran T_δ ≅ Ω¹_u / Ker T_δ` it is
`[ω] ↦ [ω^♮]` (`universalFactor_reversal`). -/
def carrierReverse : D.sourceMinimalCarrier →ₗ⋆[ℂ] D.sourceMinimalCarrier where
  toFun ξ := ⟨D.packet.reverse ξ, D.reverse_mem ξ.2⟩
  map_add' x y := by ext; simp
  map_smul' z x := by ext; simp [LinearEquiv.map_smulₛₗ]

/-- The derivation vector `∂ a = [d_u a] ∈ H₁(δ)`, i.e. `δ a ∈ Ran T_δ`. -/
def partialVec (a : A) : D.sourceMinimalCarrier := ⟨D.packet.delta a, D.delta_mem a⟩

@[simp] theorem coe_carrierLeft (a : A) (ξ : D.sourceMinimalCarrier) :
    ((D.carrierLeft a ξ : D.sourceMinimalCarrier) : K) = D.packet.left a ξ := rfl

@[simp] theorem coe_carrierRight (a : A) (ξ : D.sourceMinimalCarrier) :
    ((D.carrierRight a ξ : D.sourceMinimalCarrier) : K) = D.packet.right a ξ := rfl

@[simp] theorem coe_carrierReverse (ξ : D.sourceMinimalCarrier) :
    ((D.carrierReverse ξ : D.sourceMinimalCarrier) : K) = D.packet.reverse ξ := rfl

@[simp] theorem coe_partialVec (a : A) :
    ((D.partialVec a : D.sourceMinimalCarrier) : K) = D.packet.delta a := rfl

theorem partialVec_eq_zero_iff (a : A) : D.partialVec a = 0 ↔ D.packet.delta a = 0 := by
  constructor
  · intro h; simpa using congrArg Subtype.val h
  · intro h; ext; simp [h]

theorem partialVec_one : D.partialVec 1 = 0 :=
  (D.partialVec_eq_zero_iff 1).2 D.delta_one

theorem carrierLeft_adjoint (a : A) (ξ η : D.sourceMinimalCarrier) :
    ⟪D.carrierLeft a ξ, η⟫_ℂ = ⟪ξ, D.carrierLeft (star a) η⟫_ℂ :=
  D.packet.left_star_adjoint a ξ η

theorem carrierRight_adjoint (a : A) (ξ η : D.sourceMinimalCarrier) :
    ⟪D.carrierRight a ξ, η⟫_ℂ = ⟪ξ, D.carrierRight (star a) η⟫_ℂ :=
  D.packet.right_star_adjoint a ξ η

theorem carrierReverse_inner (ξ η : D.sourceMinimalCarrier) :
    ⟪D.carrierReverse ξ, D.carrierReverse η⟫_ℂ = ⟪η, ξ⟫_ℂ :=
  D.packet.reverse_inner ξ η

theorem carrierReverse_carrierReverse (ξ : D.sourceMinimalCarrier) :
    D.carrierReverse (D.carrierReverse ξ) = ξ := by
  ext; exact D.packet.reverse_involutive ξ

theorem carrierLeft_carrierRight_comm (a b : A) (ξ : D.sourceMinimalCarrier) :
    D.carrierLeft a (D.carrierRight b ξ) = D.carrierRight b (D.carrierLeft a ξ) := by
  ext
  have h := congrArg (fun f : Module.End ℂ K => f ξ) (D.packet.commute_actions a b).eq
  simpa [Module.End.mul_apply] using h

theorem carrierReverse_carrierLeft (a : A) (ξ : D.sourceMinimalCarrier) :
    D.carrierReverse (D.carrierLeft a ξ) = D.carrierRight (star a) (D.carrierReverse ξ) := by
  ext; exact D.packet.reverse_left a ξ

variable (τ : FaithfulTracialState A)

/-- The derivation `∂ : H₀ = L²(A, τ) → H₁(δ)`, `a ↦ [d_u a] = δ a`. -/
def hodgeDifferential : TracialL2 τ →ₗ[ℂ] D.sourceMinimalCarrier :=
  LinearMap.codRestrict _ (D.packet.delta ∘ₗ (TracialL2.equiv τ).toLinearMap)
    (fun _ => D.delta_mem _)

/-- The Lipschitz block `B_a : H₀ → H₁(δ)`, `B_a b = (∂ a) b = ρ(b) δ(a)`. -/
def lipschitzBlock (a : A) : TracialL2 τ →ₗ[ℂ] D.sourceMinimalCarrier where
  toFun x := ⟨D.packet.right (TracialL2.equiv τ x) (D.packet.delta a),
    D.right_mem _ (D.delta_mem a)⟩
  map_add' x y := by ext; simp
  map_smul' z x := by ext; simp

@[simp] theorem coe_hodgeDifferential (x : TracialL2 τ) :
    ((D.hodgeDifferential τ x : D.sourceMinimalCarrier) : K) =
      D.packet.delta (TracialL2.equiv τ x) := rfl

@[simp] theorem coe_lipschitzBlock (a : A) (x : TracialL2 τ) :
    ((D.lipschitzBlock τ a x : D.sourceMinimalCarrier) : K) =
      D.packet.right (TracialL2.equiv τ x) (D.packet.delta a) := rfl

/-- The Leibniz identity `∂ L_a - λ(a) ∂ = B_a`. -/
theorem hodgeDifferential_leibniz (a : A) (x : TracialL2 τ) :
    D.hodgeDifferential τ (TracialL2.mulLeft τ a x) -
        D.carrierLeft a (D.hodgeDifferential τ x) = D.lipschitzBlock τ a x := by
  ext
  simp [D.leibniz]

/-- Right `A`-linearity of `B_a`: `B_a R_b = ρ(b) B_a`. -/
theorem lipschitzBlock_mulRight (a b : A) (x : TracialL2 τ) :
    D.lipschitzBlock τ a (TracialL2.mulRight τ b x) =
      D.carrierRight b (D.lipschitzBlock τ a x) := by
  ext
  simp [D.packet.right_mul, Module.End.mul_apply]

theorem lipschitzBlock_one (a : A) :
    D.lipschitzBlock τ a (TracialL2.ofA τ 1) = D.partialVec a := by
  ext
  simp [D.packet.right_one]

theorem lipschitzBlock_smul (z : ℂ) (a : A) (x : TracialL2 τ) :
    D.lipschitzBlock τ (z • a) x = z • D.lipschitzBlock τ a x := by
  ext
  simp

theorem lipschitzBlock_eq_zero_of (a : A) (h : D.packet.delta a = 0) (x : TracialL2 τ) :
    D.lipschitzBlock τ a x = 0 := by
  ext
  simp [h]

/-- Star compatibility on the Hodge carriers: `J₁ ∂ = ∂ J₀`. -/
theorem carrierReverse_hodgeDifferential (x : TracialL2 τ) :
    D.carrierReverse (D.hodgeDifferential τ x) =
      D.hodgeDifferential τ (TracialL2.involution τ x) := by
  ext
  simp [D.delta_star]

theorem hodgeDifferential_ofA (a : A) :
    D.hodgeDifferential τ (TracialL2.ofA τ a) = D.partialVec a := rfl

section Adjoint

variable [FiniteDimensional ℂ A]

/-- The codifferential `∂^* : H₁(δ) → H₀`. -/
def hodgeCodifferential : D.sourceMinimalCarrier →ₗ[ℂ] TracialL2 τ :=
  LinearMap.adjoint (D.hodgeDifferential τ)

/-- `J₀ ∂^* = ∂^* J₁`, derived from `J₁ ∂ = ∂ J₀` and antiunitarity. -/
theorem involution_hodgeCodifferential (ξ : D.sourceMinimalCarrier) :
    TracialL2.involution τ (D.hodgeCodifferential τ ξ) =
      D.hodgeCodifferential τ (D.carrierReverse ξ) := by
  apply ext_inner_left ℂ
  intro v
  rw [hodgeCodifferential, LinearMap.adjoint_inner_right]
  conv_lhs => rw [← TracialL2.involution_involution τ v]
  rw [TracialL2.inner_involution, LinearMap.adjoint_inner_left,
    ← D.carrierReverse_hodgeDifferential τ v]
  conv_lhs => rw [← D.carrierReverse_carrierReverse ξ]
  rw [D.carrierReverse_inner]

end Adjoint

end

end AustereUnitZeroMode.FiniteRealDifferentialDatum


/-! ## The coordinate packet of a datum, with every field derived -/

namespace FiniteRealEvenSpectralizationExact.Packet

open FiniteHodgeDiracDatum AustereUnitZeroMode

noncomputable section

section Grading

variable {A I J : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
  [StarModule ℂ A] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]
  (P : FiniteRealEvenSpectralizationExact.Packet (A := A) (I := I) (J := J))

/-- `γ^* = γ` (eq:even-grading-axioms). -/
theorem grading_isHermitian : P.grading.IsHermitian := by
  unfold grading
  rw [Matrix.isHermitian_fromBlocks_iff]
  refine ⟨Matrix.isHermitian_one, by simp, by simp, ?_⟩
  exact (Matrix.isHermitian_one).neg

/-- `γ² = I` (eq:even-grading-axioms). -/
theorem grading_mul_self : P.grading * P.grading = 1 := by
  unfold grading
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  simp

/-- `[γ, π(a)] = 0` (eq:even-grading-axioms). -/
theorem grading_commutes_representation (a : A) :
    P.grading * P.representation a = P.representation a * P.grading := by
  unfold grading representation
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

end Grading

variable {n : ℕ} {A K : Type*}
  [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ A]
  {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- **`thm:finite-Hodge-Dirac`, construction.**  The coordinate packet of the
Hodge construction of a finite real differential datum `D` on `(A, τ)`:
`H₀ = L²(A, τ)` with orthonormal basis `b₀`, `H₁(δ) = Ran T_δ ≅ Ω¹_u / Ker T_δ`
with orthonormal basis `b₁`; `left0, right0, j0` are the matrices of `L_a, R_a`
and `a ↦ a^*`, `left1, right1, j1` those of `λ(a), ρ(a)` and `J₁`, and
`differential, B a` those of `∂` and `B_a`.  Every packet law is *derived*
from the datum and from traciality/faithfulness of `τ`. -/
def ofDatum (D : FiniteRealDifferentialDatum n A K) (τ : FaithfulTracialState A)
    (b₀ : OrthonormalBasis I ℂ (TracialL2 τ))
    (b₁ : OrthonormalBasis J ℂ D.sourceMinimalCarrier) :
    FiniteRealEvenSpectralizationExact.Packet (A := A) (I := I) (J := J) where
  left0 a := coordMat b₀ b₀ (TracialL2.mulLeft τ a)
  left1 a := coordMat b₁ b₁ (D.carrierLeft a)
  right0 a := coordMat b₀ b₀ (TracialL2.mulRight τ a)
  right1 a := coordMat b₁ b₁ (D.carrierRight a)
  differential := coordMat b₁ b₀ (D.hodgeDifferential τ)
  B a := coordMat b₁ b₀ (D.lipschitzBlock τ a)
  B_real_smul r a := by
    rw [← coordMat_smul]
    congr 1
    funext x
    exact D.lipschitzBlock_smul τ _ a x
  partialVector a := coordVec b₁ (D.partialVec a)
  unitVector := coordVec b₀ (TracialL2.ofA τ 1)
  left0_star a := (coordMat_of_adjoint b₀ b₀ _ _ (TracialL2.inner_mulLeft τ a)).symm
  left1_star a := (coordMat_of_adjoint b₁ b₁ _ _ (D.carrierLeft_adjoint a)).symm
  right0_star a := (coordMat_of_adjoint b₀ b₀ _ _ (TracialL2.inner_mulRight τ a)).symm
  right1_star a := (coordMat_of_adjoint b₁ b₁ _ _ (D.carrierRight_adjoint a)).symm
  commute0 a b := by
    rw [← coordMat_comp_linear, ← coordMat_comp_linear]
    congr 1
    funext x
    exact TracialL2.mulLeft_mulRight_comm τ a b x
  commute1 a b := by
    rw [← coordMat_comp_linear, ← coordMat_comp_linear]
    congr 1
    funext x
    exact D.carrierLeft_carrierRight_comm a b x
  leibniz a := by
    rw [← coordMat_comp_linear, ← coordMat_comp_linear, ← coordMat_sub]
    congr 1
    funext x
    exact D.hodgeDifferential_leibniz τ a x
  B_right a b := by
    rw [← coordMat_comp_linear, ← coordMat_comp_linear]
    congr 1
    funext x
    exact D.lipschitzBlock_mulRight τ a b x
  B_unit a := by
    rw [coordMat_mulVec, D.lipschitzBlock_one]
  B_zero_of_partial_zero a h := by
    have h' : D.packet.delta a = 0 :=
      (D.partialVec_eq_zero_iff a).1 ((coordVec_eq_zero_iff _ _).1 h)
    rw [← coordMat_zero b₁ b₀]
    congr 1
    funext x
    exact D.lipschitzBlock_eq_zero_of τ a h' x
  j0 := coordMat b₀ b₀ (TracialL2.involution τ)
  j1 := coordMat b₁ b₁ D.carrierReverse
  j0_sq := by
    rw [← coordMat_comp_antilinear,
      show (fun x => TracialL2.involution τ (TracialL2.involution τ x)) = fun x => x from
        funext (TracialL2.involution_involution τ), coordMat_id]
  j1_sq := by
    rw [← coordMat_comp_antilinear,
      show (fun x => D.carrierReverse (D.carrierReverse x)) = fun x => x from
        funext D.carrierReverse_carrierReverse, coordMat_id]
  j0_left a := by
    rw [← coordMat_comp_antilinear, ← coordMat_comp_linear]
    congr 1
    funext x
    exact TracialL2.involution_mulLeft τ a x
  j1_left a := by
    rw [← coordMat_comp_antilinear, ← coordMat_comp_linear]
    congr 1
    funext x
    exact D.carrierReverse_carrierLeft a x
  j_differential := by
    rw [← coordMat_comp_antilinear, ← coordMat_comp_linear]
    congr 1
    funext x
    exact D.carrierReverse_hodgeDifferential τ x
  j_differentialAdjoint := by
    rw [← coordMat_of_adjoint b₁ b₀ _ (D.hodgeCodifferential τ)
      (fun x y => (LinearMap.adjoint_inner_right _ x y).symm)]
    rw [← coordMat_comp_antilinear, ← coordMat_comp_linear]
    congr 1
    funext x
    exact D.involution_hodgeCodifferential τ x


section OfDatum

variable (D : FiniteRealDifferentialDatum n A K) (τ : FaithfulTracialState A)
  (b₀ : OrthonormalBasis I ℂ (TracialL2 τ))
  (b₁ : OrthonormalBasis J ℂ D.sourceMinimalCarrier)

/-- The adjoint block of the packet is the matrix of the codifferential `∂^*`. -/
theorem ofDatum_differential_conjTranspose :
    (ofDatum D τ b₀ b₁).differentialᴴ = coordMat b₀ b₁ (D.hodgeCodifferential τ) :=
  (coordMat_of_adjoint b₁ b₀ _ _ (fun x y => (LinearMap.adjoint_inner_right _ x y).symm)).symm

/-- The Dirac matrix of the datum is the matrix of
`D = [[0, ∂^*], [∂, 0]]` on `H₀ ⊕ H₁(δ)` (eq:finite-D). -/
theorem ofDatum_dirac :
    (ofDatum D τ b₀ b₁).dirac =
      Matrix.fromBlocks 0 (coordMat b₀ b₁ (D.hodgeCodifferential τ))
        (coordMat b₁ b₀ (D.hodgeDifferential τ)) 0 := by
  rw [dirac, ofDatum_differential_conjTranspose]
  rfl

/-- The representation is `π(a) = L_a ⊕ λ(a)` (eq:finite-D). -/
theorem ofDatum_representation (a : A) :
    (ofDatum D τ b₀ b₁).representation a =
      Matrix.fromBlocks (coordMat b₀ b₀ (TracialL2.mulLeft τ a)) 0 0
        (coordMat b₁ b₁ (D.carrierLeft a)) := rfl

/-- The opposite representation is `π°(b) = R_b ⊕ ρ(b)`. -/
theorem ofDatum_oppositeRepresentation (b : A) :
    (ofDatum D τ b₀ b₁).oppositeRepresentation b =
      Matrix.fromBlocks (coordMat b₀ b₀ (TracialL2.mulRight τ b)) 0 0
        (coordMat b₁ b₁ (D.carrierRight b)) := rfl

/-- `B_a` is the matrix of `b ↦ (∂ a) b`. -/
theorem ofDatum_B (a : A) :
    (ofDatum D τ b₀ b₁).B a = coordMat b₁ b₀ (D.lipschitzBlock τ a) := rfl

/-- The real structure is `J = J₀ ⊕ J₁` with `J₀ a = a^*` and `J₁ = C|_{H₁}`. -/
theorem ofDatum_realMatrix :
    (ofDatum D τ b₀ b₁).realMatrix =
      Matrix.fromBlocks (coordMat b₀ b₀ (TracialL2.involution τ)) 0 0
        (coordMat b₁ b₁ D.carrierReverse) := rfl

/-- `π` is faithful (left regular summand). -/
theorem ofDatum_representation_injective :
    Function.Injective (ofDatum D τ b₀ b₁).representation := by
  intro a a' h
  have h0 : coordMat b₀ b₀ (TracialL2.mulLeft τ a) =
      coordMat b₀ b₀ (TracialL2.mulLeft τ a') := by
    have := congrArg Matrix.toBlocks₁₁ h
    simpa [ofDatum_representation] using this
  have hL := coordMat_injective b₀ b₀ h0
  have := congrArg
    (fun f : TracialL2 τ →ₗ[ℂ] TracialL2 τ => TracialL2.equiv τ (f (TracialL2.ofA τ 1))) hL
  simpa using this

/-- `J` is antiunitary: its coordinate matrix is unitary. -/
theorem ofDatum_realMatrix_unitary :
    (ofDatum D τ b₀ b₁).realMatrixᴴ * (ofDatum D τ b₀ b₁).realMatrix = 1 := by
  rw [ofDatum_realMatrix, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨by simpa using coordMat_antiunitary b₀ _ (TracialL2.inner_involution τ),
    by simp, by simp, by simpa using coordMat_antiunitary b₁ _ D.carrierReverse_inner⟩

/-- The kernel clause of eq:finite-Lip: for `a = a^*`, `‖[D, π(a)]‖ = 0` iff
`∂ a = 0`, i.e. `δ a = 0`. -/
theorem ofDatum_commutator_norm_eq_zero_iff {a : A} (ha : star a = a) :
    ‖(ofDatum D τ b₀ b₁).commutator (ofDatum D τ b₀ b₁).dirac
        ((ofDatum D τ b₀ b₁).representation a)‖ = 0 ↔ D.packet.delta a = 0 := by
  rw [commutator_norm_eq_B _ ha, norm_eq_zero, B_eq_zero_iff_partialVector_eq_zero]
  exact (coordVec_eq_zero_iff _ _).trans (D.partialVec_eq_zero_iff a)

/-- **`thm:finite-Hodge-Dirac`.**  For every finite real differential datum on
a finite-dimensional star algebra with faithful tracial state `τ`, and every
choice of orthonormal bases of `H₀ = L²(A, τ)` and `H₁(δ) = Ran T_δ`, the Hodge
packet `ofDatum` is a real even finite spectral triple of KO-dimension `0`:
`π` faithful; `D = D^*` (finite dimensional, hence compact resolvent and bounded
commutators); `γ^* = γ`, `γ² = I`, `[γ, π(a)] = 0`, `Dγ = -γD`; `J`
antiunitary with `J² = I`, `JD = DJ`, `Jγ = γJ`; `J π(b^*) J⁻¹ = π°(b)`
(`= R_b ⊕ ρ(b)`, `ofDatum_oppositeRepresentation`); order zero and first order;
the commutator formula eq:finite-commutator; and eq:finite-Lip
(`‖[D, π(a)]‖ = ‖B_a‖` and the kernel clause) for `a = a^*`. -/
theorem finite_hodge_dirac :
    Function.Injective (ofDatum D τ b₀ b₁).representation ∧
    (ofDatum D τ b₀ b₁).dirac.IsHermitian ∧
    ((ofDatum D τ b₀ b₁).grading.IsHermitian ∧
      (ofDatum D τ b₀ b₁).grading * (ofDatum D τ b₀ b₁).grading = 1 ∧
      (∀ a, (ofDatum D τ b₀ b₁).grading * (ofDatum D τ b₀ b₁).representation a =
        (ofDatum D τ b₀ b₁).representation a * (ofDatum D τ b₀ b₁).grading) ∧
      (ofDatum D τ b₀ b₁).dirac * (ofDatum D τ b₀ b₁).grading +
        (ofDatum D τ b₀ b₁).grading * (ofDatum D τ b₀ b₁).dirac = 0) ∧
    (ofDatum D τ b₀ b₁).realMatrixᴴ * (ofDatum D τ b₀ b₁).realMatrix = 1 ∧
    (ofDatum D τ b₀ b₁).realMatrix * (ofDatum D τ b₀ b₁).realMatrix.map star = 1 ∧
    (ofDatum D τ b₀ b₁).realMatrix * (ofDatum D τ b₀ b₁).dirac.map star =
      (ofDatum D τ b₀ b₁).dirac * (ofDatum D τ b₀ b₁).realMatrix ∧
    (ofDatum D τ b₀ b₁).realMatrix * (ofDatum D τ b₀ b₁).grading.map star =
      (ofDatum D τ b₀ b₁).grading * (ofDatum D τ b₀ b₁).realMatrix ∧
    (∀ b, (ofDatum D τ b₀ b₁).realMatrix *
        ((ofDatum D τ b₀ b₁).representation (star b)).map star *
          (ofDatum D τ b₀ b₁).realMatrix.map star =
        (ofDatum D τ b₀ b₁).oppositeRepresentation b) ∧
    (∀ a b, (ofDatum D τ b₀ b₁).commutator ((ofDatum D τ b₀ b₁).representation a)
      ((ofDatum D τ b₀ b₁).oppositeRepresentation b) = 0) ∧
    (∀ a b, (ofDatum D τ b₀ b₁).commutator
      ((ofDatum D τ b₀ b₁).commutator (ofDatum D τ b₀ b₁).dirac
        ((ofDatum D τ b₀ b₁).representation a))
      ((ofDatum D τ b₀ b₁).oppositeRepresentation b) = 0) ∧
    (∀ a, (ofDatum D τ b₀ b₁).commutator (ofDatum D τ b₀ b₁).dirac
        ((ofDatum D τ b₀ b₁).representation a) =
      Matrix.fromBlocks 0 (-((ofDatum D τ b₀ b₁).B (star a))ᴴ)
        ((ofDatum D τ b₀ b₁).B a) 0) ∧
    (∀ a, star a = a →
      ‖(ofDatum D τ b₀ b₁).commutator (ofDatum D τ b₀ b₁).dirac
        ((ofDatum D τ b₀ b₁).representation a)‖ = ‖(ofDatum D τ b₀ b₁).B a‖) ∧
    (∀ a, star a = a →
      (‖(ofDatum D τ b₀ b₁).commutator (ofDatum D τ b₀ b₁).dirac
        ((ofDatum D τ b₀ b₁).representation a)‖ = 0 ↔ D.packet.delta a = 0)) :=
  ⟨ofDatum_representation_injective D τ b₀ b₁, dirac_isHermitian _,
    ⟨grading_isHermitian _, grading_mul_self _, grading_commutes_representation _,
      dirac_odd _⟩,
    ofDatum_realMatrix_unitary D τ b₀ b₁, realMatrix_sq _,
    realMatrix_intertwines_dirac _, realMatrix_commutes_grading _,
    realMatrix_implements_opposite _, order_zero _, first_order _,
    dirac_commutator_formula _, fun _ ha => commutator_norm_eq_B _ ha,
    fun _ ha => ofDatum_commutator_norm_eq_zero_iff D τ b₀ b₁ ha⟩

/-! ### `prop:hodge-zero-mode` -/

/-- Operator form of eq:hodge-zero-mode: `∂ 1 = 0`, so `D(1, 0) = (∂^* 0, ∂ 1) = 0`. -/
theorem hodgeDifferential_one :
    D.hodgeDifferential τ (TracialL2.ofA τ 1) = 0 := by
  rw [D.hodgeDifferential_ofA, D.partialVec_one]

theorem ofDatum_differential_mulVec_unitVector :
    (ofDatum D τ b₀ b₁).differential *ᵥ (ofDatum D τ b₀ b₁).unitVector = 0 := by
  change coordMat b₁ b₀ (D.hodgeDifferential τ) *ᵥ coordVec b₀ (TracialL2.ofA τ 1) = 0
  rw [coordMat_mulVec, hodgeDifferential_one]
  exact (coordVec_eq_zero_iff _ _).2 rfl

theorem ofDatum_unitVector_ne_zero : (ofDatum D τ b₀ b₁).unitVector ≠ 0 := by
  intro h
  exact τ.one_ne_zero ((coordVec_eq_zero_iff b₀ _).1 h)

/-- **`prop:hodge-zero-mode`.**  For every finite real differential datum
(and every faithful tracial state and orthonormal bases), the Hodge--Dirac
matrix kills the coordinate vector of `(1, 0) ∈ H₀ ⊕ H₁(δ)`, which is nonzero;
hence `det D = 0` and the Hodge construction never produces an invertible
finite Dirac operator.  (The commutant-ambiguity sentence is
`thm:commutant-fibre`, `MarkedCommutantCoordinates.MarkedFiniteSpectralTriple.commutant_fibre`.) -/
theorem hodge_zero_mode :
    (ofDatum D τ b₀ b₁).dirac *ᵥ AustereUnitZeroMode.unitZeroForm (ofDatum D τ b₀ b₁) = 0 ∧
    AustereUnitZeroMode.unitZeroForm (ofDatum D τ b₀ b₁) ≠ 0 ∧
    (ofDatum D τ b₀ b₁).dirac.det = 0 ∧ ¬ IsUnit (ofDatum D τ b₀ b₁).dirac :=
  AustereUnitZeroMode.austere_unit_zero_mode _
    (ofDatum_differential_mulVec_unitVector D τ b₀ b₁) (ofDatum_unitVector_ne_zero D τ b₀ b₁)

/-- The vector killed in `hodge_zero_mode` is the coordinate vector of `(1, 0)`. -/
theorem unitZeroForm_ofDatum :
    AustereUnitZeroMode.unitZeroForm (ofDatum D τ b₀ b₁) =
      Sum.elim (coordVec b₀ (TracialL2.ofA τ 1)) 0 := rfl

end OfDatum

end

end FiniteRealEvenSpectralizationExact.Packet


/-! ## Scaling the differential (`prop:no-scale`) -/

namespace AustereUnitZeroMode.FiniteRealDifferentialDatum

open FiniteDifferentialOccurrenceCompiler FiniteDifferentialOccurrenceCompiler.Packet
  FiniteHodgeDiracDatum

noncomputable section

variable {n : ℕ} {A K : Type*}
  [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (D : FiniteRealDifferentialDatum n A K)

/-- The datum `s δ` (`s` real): same algebra, bimodule, actions and `C`; the
derivation axioms are re-derived for `s δ`. -/
def scale (s : ℝ) : FiniteRealDifferentialDatum n A K :=
  ⟨{ D.packet with delta := (s : ℂ) • D.packet.delta }, by
    refine ⟨?_, ?_, ?_⟩
    · change (s : ℂ) • D.packet.delta 1 = 0
      rw [D.delta_one, smul_zero]
    · intro a b
      change (s : ℂ) • D.packet.delta (a * b) =
        D.packet.left a ((s : ℂ) • D.packet.delta b) +
          D.packet.right b ((s : ℂ) • D.packet.delta a)
      rw [D.leibniz, map_smul, map_smul, smul_add]
    · intro a
      change (s : ℂ) • D.packet.delta (star a) = D.packet.reverse ((s : ℂ) • D.packet.delta a)
      rw [D.delta_star, LinearEquiv.map_smulₛₗ, Complex.conj_ofReal]⟩

@[simp] theorem scale_delta (s : ℝ) (a : A) :
    (D.scale s).packet.delta a = (s : ℂ) • D.packet.delta a := rfl

@[simp] theorem scale_left (s : ℝ) : (D.scale s).packet.left = D.packet.left := rfl
@[simp] theorem scale_right (s : ℝ) : (D.scale s).packet.right = D.packet.right := rfl
@[simp] theorem scale_reverse (s : ℝ) : (D.scale s).packet.reverse = D.packet.reverse := rfl

/-- `T_{sδ} = s T_δ`. -/
theorem scale_universalFactor (s : ℝ) :
    (D.scale s).packet.universalFactor = (s : ℂ) • D.packet.universalFactor := by
  have h : (D.scale s).packet.factorTensor = (s : ℂ) • D.packet.factorTensor := by
    apply TensorProduct.ext'
    intro x y
    simp [factorTensor_tmul, map_smul]
  ext ω
  simp [universalFactor_apply, h]

/-- `Ker T_{sδ} = Ker T_δ` for `s ≠ 0`. -/
theorem scale_ker_universalFactor {s : ℝ} (hs : s ≠ 0) :
    LinearMap.ker (D.scale s).packet.universalFactor = LinearMap.ker D.packet.universalFactor := by
  ext ω
  simp [scale_universalFactor, LinearMap.mem_ker, smul_eq_zero, Complex.ofReal_eq_zero, hs]

/-- `Ran T_{sδ} = Ran T_δ` for `s ≠ 0`. -/
theorem scale_sourceMinimalCarrier {s : ℝ} (hs : s ≠ 0) :
    (D.scale s).sourceMinimalCarrier = D.sourceMinimalCarrier := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  apply le_antisymm
  · rintro _ ⟨ω, rfl⟩
    refine ⟨(s : ℂ) • ω, ?_⟩
    rw [scale_universalFactor, LinearMap.smul_apply, map_smul]
  · rintro _ ⟨ω, rfl⟩
    refine ⟨(s : ℂ)⁻¹ • ω, ?_⟩
    rw [scale_universalFactor, LinearMap.smul_apply, map_smul, smul_smul,
      mul_inv_cancel₀ hs', one_smul]

/-- The Gram of `s δ` is `s² Q_δ`. -/
theorem scale_inducedGram (s : ℝ) (ω η : UniversalOneForm A) :
    (D.scale s).packet.inducedGram ω η = ((s : ℂ) ^ 2) * D.packet.inducedGram ω η := by
  simp only [inducedGram, scale_universalFactor, LinearMap.smul_apply, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal]
  ring

/-- The identity of `Ω¹_u / Ker T_{sδ} = Ω¹_u / Ker T_δ`, transported to the
range carriers: `ξ ↦ ι_δ [ι_{sδ}⁻¹ ξ]`. -/
def scaleClassIdentification {s : ℝ} (hs : s ≠ 0) :
    (D.scale s).sourceMinimalCarrier →ₗ[ℂ] D.sourceMinimalCarrier :=
  D.sourceMinimalEquiv.toLinearMap ∘ₗ
    (Submodule.quotEquivOfEq _ _ (D.scale_ker_universalFactor hs)).toLinearMap ∘ₗ
      (D.scale s).sourceMinimalEquiv.symm.toLinearMap

/-- The class identification is `s⁻¹ · id` on the range carriers. -/
theorem scaleClassIdentification_apply {s : ℝ} (hs : s ≠ 0)
    (ξ : (D.scale s).sourceMinimalCarrier) :
    ((D.scaleClassIdentification hs ξ : D.sourceMinimalCarrier) : K) = (s : ℂ)⁻¹ • (ξ : K) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  obtain ⟨x, rfl⟩ := (D.scale s).sourceMinimalEquiv.surjective ξ
  induction x using Submodule.Quotient.induction_on with
  | H ω =>
    simp only [scaleClassIdentification, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_apply_apply, Submodule.quotEquivOfEq_mk]
    simp only [sourceMinimalEquiv, sourceMinimalEquivRange_apply, scale_universalFactor,
      LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hs', one_smul]

/-- The canonical unitary `H₁(sδ) → H₁(δ)` of the proof of `prop:no-scale`:
`s` times the class identification, i.e. `[ω] ↦ s [ω]`. -/
def scaleCanonicalUnitary {s : ℝ} (hs : s ≠ 0) :
    (D.scale s).sourceMinimalCarrier →ₗ[ℂ] D.sourceMinimalCarrier :=
  (s : ℂ) • D.scaleClassIdentification hs

theorem scaleCanonicalUnitary_apply {s : ℝ} (hs : s ≠ 0)
    (ξ : (D.scale s).sourceMinimalCarrier) :
    ((D.scaleCanonicalUnitary hs ξ : D.sourceMinimalCarrier) : K) = (ξ : K) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [scaleCanonicalUnitary, LinearMap.smul_apply, Submodule.coe_smul,
    scaleClassIdentification_apply, smul_smul, mul_inv_cancel₀ hs', one_smul]

/-- The canonical unitary is isometric for the Grams `s² Q_δ` and `Q_δ`. -/
theorem scaleCanonicalUnitary_inner {s : ℝ} (hs : s ≠ 0)
    (ξ η : (D.scale s).sourceMinimalCarrier) :
    ⟪D.scaleCanonicalUnitary hs ξ, D.scaleCanonicalUnitary hs η⟫_ℂ = ⟪ξ, η⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, scaleCanonicalUnitary_apply,
    scaleCanonicalUnitary_apply]

/-- It sends the derivation vector `∂_{sδ} a` to `s ∂_δ a`. -/
theorem scaleCanonicalUnitary_partialVec {s : ℝ} (hs : s ≠ 0) (a : A) :
    D.scaleCanonicalUnitary hs ((D.scale s).partialVec a) = (s : ℂ) • D.partialVec a := by
  ext
  rw [scaleCanonicalUnitary_apply]
  simp

/-- The canonical unitary as a linear isometry equivalence (it is the identity
of the common range `Ran T_{sδ} = Ran T_δ`). -/
def scaleCarrierEquiv {s : ℝ} (hs : s ≠ 0) :
    (D.scale s).sourceMinimalCarrier ≃ₗᵢ[ℂ] D.sourceMinimalCarrier :=
  LinearIsometryEquiv.ofEq _ _ (D.scale_sourceMinimalCarrier hs)

theorem scaleCarrierEquiv_eq_canonicalUnitary {s : ℝ} (hs : s ≠ 0)
    (ξ : (D.scale s).sourceMinimalCarrier) :
    D.scaleCarrierEquiv hs ξ = D.scaleCanonicalUnitary hs ξ := by
  ext
  rw [scaleCanonicalUnitary_apply]
  rfl

/-- A nonzero derivation is nonzero on some self-adjoint element. -/
theorem exists_selfAdjoint_delta_ne_zero (hδ : D.packet.delta ≠ 0) :
    ∃ a : A, star a = a ∧ D.packet.delta a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hδ
  ext x
  set h : A := (1 / 2 : ℂ) • (x + star x) with hh
  set k : A := (-Complex.I / 2) • (x - star x) with hk
  have hhs : star h = h := by
    rw [hh, star_smul, star_add, star_star, add_comm]
    congr 1
    simp [map_div₀]
  have hks : star k = k := by
    rw [hk, star_smul, star_sub, star_star]
    rw [show star (-Complex.I / 2) = Complex.I / 2 by simp [map_div₀]]
    rw [show x - star x = -(star x - x) by abel, smul_neg, ← neg_smul]
    congr 1
    ring
  have hI : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; norm_num
  have hx : x = h + Complex.I • k := by
    rw [hh, hk, smul_smul, hI]; module
  clear_value h k
  rw [hx, map_add, map_smul, hcon h hhs, hcon k hks, smul_zero, add_zero,
    LinearMap.zero_apply]

end

end AustereUnitZeroMode.FiniteRealDifferentialDatum

namespace FiniteRealEvenSpectralizationExact.Packet

open FiniteHodgeDiracDatum AustereUnitZeroMode FiniteSpectralizationFunctorScaleExact

noncomputable section

variable {n : ℕ} {A K : Type*}
  [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ A]
  {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (D : FiniteRealDifferentialDatum n A K) (τ : FaithfulTracialState A)
  (b₀ : OrthonormalBasis I ℂ (TracialL2 τ))
  (b₁ : OrthonormalBasis J ℂ D.sourceMinimalCarrier)

/-- The basis of `H₁(sδ)` corresponding to `b₁` under the canonical unitary. -/
def scaleBasis {s : ℝ} (hs : s ≠ 0) : OrthonormalBasis J ℂ (D.scale s).sourceMinimalCarrier :=
  b₁.map (D.scaleCarrierEquiv hs).symm

theorem coe_scaleBasis {s : ℝ} (hs : s ≠ 0) (j : J) :
    ((scaleBasis D b₁ hs j : (D.scale s).sourceMinimalCarrier) : K) = (b₁ j : K) := rfl

/-- Under the canonical identification, every block of the Hodge packet of `s δ`
agrees with that of `δ` except `∂ ↦ s ∂` and `B_a ↦ s B_a`. -/
theorem ofDatum_scale_blocks {s : ℝ} (hs : s ≠ 0) :
    (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs)).left0 = (ofDatum D τ b₀ b₁).left0 ∧
    (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs)).left1 = (ofDatum D τ b₀ b₁).left1 ∧
    (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs)).right0 = (ofDatum D τ b₀ b₁).right0 ∧
    (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs)).right1 = (ofDatum D τ b₀ b₁).right1 ∧
    (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs)).j0 = (ofDatum D τ b₀ b₁).j0 ∧
    (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs)).j1 = (ofDatum D τ b₀ b₁).j1 ∧
    (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs)).differential =
      (s : ℂ) • (ofDatum D τ b₀ b₁).differential ∧
    (∀ a, (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs)).B a =
      (s : ℂ) • (ofDatum D τ b₀ b₁).B a) := by
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · funext a; ext i j; rfl
  · funext a; ext i j; rfl
  · ext i j; rfl
  · ext i j
    change ⟪(scaleBasis D b₁ hs i : K), (s : ℂ) • D.packet.delta _⟫_ℂ =
      (s : ℂ) * ⟪(b₁ i : K), D.packet.delta _⟫_ℂ
    rw [inner_smul_right]
    rfl
  · intro a
    ext i j
    change ⟪(scaleBasis D b₁ hs i : K), D.packet.right _ ((s : ℂ) • D.packet.delta a)⟫_ℂ =
      (s : ℂ) * ⟪(b₁ i : K), D.packet.right _ (D.packet.delta a)⟫_ℂ
    rw [map_smul, inner_smul_right]
    rfl

/-- `D ↦ s D` (eq:scale-D). -/
theorem ofDatum_scale_dirac {s : ℝ} (hs : s ≠ 0) :
    (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs)).dirac = (s : ℂ) • (ofDatum D τ b₀ b₁).dirac := by
  rw [← Scale.dirac_eq_smul]
  unfold dirac Scale.dirac
  rw [(ofDatum_scale_blocks D τ b₀ b₁ hs).2.2.2.2.2.2.1]

theorem ofDatum_scale_representation {s : ℝ} (hs : s ≠ 0) (a : A) :
    (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs)).representation a =
      (ofDatum D τ b₀ b₁).representation a := by
  obtain ⟨h0, h1, -⟩ := ofDatum_scale_blocks D τ b₀ b₁ hs
  unfold representation
  rw [h0, h1]

/-- `L_D(a) = ‖[D, π(a)]‖ ↦ s L_D(a)` (eq:scale-D), for every `a`. -/
theorem ofDatum_scale_lipschitz {s : ℝ} (hs : 0 < s) (a : A) :
    ‖(ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).commutator
        (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).dirac
        ((ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).representation a)‖ =
      s * ‖(ofDatum D τ b₀ b₁).commutator (ofDatum D τ b₀ b₁).dirac
        ((ofDatum D τ b₀ b₁).representation a)‖ := by
  rw [ofDatum_scale_dirac, ofDatum_scale_representation]
  unfold commutator
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs]

/-- Connes distance `d_D ↦ s⁻¹ d_D` whenever it is finite (attained). -/
theorem ofDatum_scale_connesDistance {s : ℝ} (hs : 0 < s) (φ ψ : A →ₗ[ℂ] ℂ) {d : ℝ}
    (hd : IsGreatest (Scale.distanceValues (ofDatum D τ b₀ b₁) φ ψ) d) :
    IsGreatest (Scale.distanceValues (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')) φ ψ)
      (s⁻¹ * d) := by
  have hset : Scale.distanceValues (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')) φ ψ =
      Scale.scaledDistanceValues (ofDatum D τ b₀ b₁) s φ ψ := by
    ext r
    simp only [Scale.distanceValues, Scale.scaledDistanceValues, Set.mem_ofPred_eq,
      (ofDatum_scale_blocks D τ b₀ b₁ hs.ne').2.2.2.2.2.2.2, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
  rw [hset]
  exact Scale.connesDistance_scale_isGreatest _ hs φ ψ hd

/-- **`prop:no-scale`.**  Let `δ ≠ 0` and `s > 0`.  Replacing `δ` by `s δ`
keeps `(A, τ)` (and the bimodule, actions and `C`); `Ker T_{sδ} = Ker T_δ`,
the Gram becomes `s² Q_δ`, and the canonical unitary `H₁(sδ) → H₁(δ)`
(`s` times the class identification, which is `s⁻¹ · id` on ranges) is isometric
and sends `∂_{sδ} a` to `s ∂_δ a`.  In the corresponding bases the Hodge triple
of `s δ` has `D ↦ s D`, `L_D ↦ s L_D`, and the attained Connes distance
scales by `s⁻¹`.  Since `δ ≠ 0`, some self-adjoint `a` has `L_D(a) > 0`, so for
`s ≠ 1` the Lipschitz seminorms and Dirac operators differ although `(A, τ)`
is the same: the algebra and trace do not determine the metric scale. -/
theorem no_scale (hδ : D.packet.delta ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∀ a, (D.scale s).packet.delta a = (s : ℂ) • D.packet.delta a) ∧
    (D.scale s).packet.left = D.packet.left ∧ (D.scale s).packet.right = D.packet.right ∧
    (D.scale s).packet.reverse = D.packet.reverse ∧
    LinearMap.ker (D.scale s).packet.universalFactor =
      LinearMap.ker D.packet.universalFactor ∧
    (∀ ω η, (D.scale s).packet.inducedGram ω η = ((s : ℂ) ^ 2) * D.packet.inducedGram ω η) ∧
    (∀ ξ, ((D.scaleClassIdentification hs.ne' ξ : D.sourceMinimalCarrier) : K) =
      (s : ℂ)⁻¹ • (ξ : K)) ∧
    (∀ ξ η, ⟪D.scaleCanonicalUnitary hs.ne' ξ, D.scaleCanonicalUnitary hs.ne' η⟫_ℂ =
      ⟪ξ, η⟫_ℂ) ∧
    (∀ a, D.scaleCanonicalUnitary hs.ne' ((D.scale s).partialVec a) =
      (s : ℂ) • D.partialVec a) ∧
    (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).dirac =
      (s : ℂ) • (ofDatum D τ b₀ b₁).dirac ∧
    (∀ a, ‖(ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).commutator
        (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).dirac
        ((ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).representation a)‖ =
      s * ‖(ofDatum D τ b₀ b₁).commutator (ofDatum D τ b₀ b₁).dirac
        ((ofDatum D τ b₀ b₁).representation a)‖) ∧
    (∀ (φ ψ : A →ₗ[ℂ] ℂ) d, IsGreatest (Scale.distanceValues (ofDatum D τ b₀ b₁) φ ψ) d →
      IsGreatest (Scale.distanceValues (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne'))
        φ ψ) (s⁻¹ * d)) ∧
    (∃ a : A, star a = a ∧
      0 < ‖(ofDatum D τ b₀ b₁).commutator (ofDatum D τ b₀ b₁).dirac
        ((ofDatum D τ b₀ b₁).representation a)‖ ∧
      (s ≠ 1 →
        ‖(ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).commutator
          (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).dirac
          ((ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).representation a)‖ ≠
        ‖(ofDatum D τ b₀ b₁).commutator (ofDatum D τ b₀ b₁).dirac
          ((ofDatum D τ b₀ b₁).representation a)‖)) := by
  obtain ⟨a, ha, hda⟩ := D.exists_selfAdjoint_delta_ne_zero hδ
  have hpos : 0 < ‖(ofDatum D τ b₀ b₁).commutator (ofDatum D τ b₀ b₁).dirac
      ((ofDatum D τ b₀ b₁).representation a)‖ :=
    lt_of_le_of_ne (norm_nonneg _)
      (fun h => hda ((ofDatum_commutator_norm_eq_zero_iff D τ b₀ b₁ ha).1 h.symm))
  refine ⟨D.scale_delta s, rfl, rfl, rfl, D.scale_ker_universalFactor hs.ne',
    D.scale_inducedGram s, D.scaleClassIdentification_apply hs.ne',
    D.scaleCanonicalUnitary_inner hs.ne', D.scaleCanonicalUnitary_partialVec hs.ne',
    ofDatum_scale_dirac D τ b₀ b₁ hs.ne', ofDatum_scale_lipschitz D τ b₀ b₁ hs,
    fun φ ψ d hd => ofDatum_scale_connesDistance D τ b₀ b₁ hs φ ψ hd, a, ha, hpos, ?_⟩
  intro hs1 heq
  rw [ofDatum_scale_lipschitz D τ b₀ b₁ hs] at heq
  apply hs1
  have := mul_right_cancel₀ hpos.ne' (heq.trans (one_mul _).symm)
  exact this

/-- For `δ ≠ 0` and `s > 0`, `s ≠ 1`, the Dirac operators of `δ` and `s δ`
(on the canonically identified carriers) differ. -/
theorem ofDatum_scale_dirac_ne (hδ : D.packet.delta ≠ 0) {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) :
    (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).dirac ≠ (ofDatum D τ b₀ b₁).dirac := by
  intro h
  obtain ⟨a, -, -, hne⟩ := (no_scale D τ b₀ b₁ hδ hs).2.2.2.2.2.2.2.2.2.2.2.2
  apply hne hs1
  rw [h, ofDatum_scale_representation]
  rfl

end

end FiniteRealEvenSpectralizationExact.Packet


/-! ## Non-vacuity: an inner-derivation datum on `M₂(ℂ)` -/

namespace FiniteHodgeDiracDatum

open FiniteDifferentialOccurrenceCompiler AustereUnitZeroMode

noncomputable section

section InnerDerivation

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A]
  (τ : FaithfulTracialState A)

/-- A finite-dimensional algebra with `1 ≠ 0` has a finite basis containing `1`. -/
theorem exists_basis_with_one [FiniteDimensional ℂ A] (h1 : (1 : A) ≠ 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ A) (i : Fin n), b i = 1 := by
  have hs : LinearIndepOn ℂ id ({1} : Set A) := (linearIndepOn_singleton_iff ℂ).2 h1
  let b := Module.Basis.extend hs
  have : Finite (hs.extend (Set.subset_univ _)) := Module.Finite.finite_basis b
  let _ : Fintype (hs.extend (Set.subset_univ _)) := Fintype.ofFinite _
  let e := Fintype.equivFin (hs.extend (Set.subset_univ _))
  refine ⟨_, b.reindex e, e ⟨1, Module.Basis.subset_extend hs rfl⟩, ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.extend_apply_self]

/-- The left regular representation on `L²(A, τ)` as an algebra map. -/
def l2LeftAlgHom : A →ₐ[ℂ] Module.End ℂ (TracialL2 τ) where
  toFun a := TracialL2.mulLeft τ a
  map_one' := by ext x; apply TracialL2.ext_equiv; simp
  map_mul' a b := by ext x; apply TracialL2.ext_equiv; simp [mul_assoc]
  map_zero' := by ext x; apply TracialL2.ext_equiv; simp
  map_add' a b := by ext x; apply TracialL2.ext_equiv; simp [add_mul]
  commutes' c := by
    ext x; apply TracialL2.ext_equiv
    simp [Algebra.algebraMap_eq_smul_one, Module.algebraMap_end_apply]

/-- The right regular action on `L²(A, τ)`. -/
def l2Right : A →ₗ[ℂ] Module.End ℂ (TracialL2 τ) where
  toFun a := TracialL2.mulRight τ a
  map_add' a b := by ext x; apply TracialL2.ext_equiv; simp [mul_add]
  map_smul' c a := by ext x; apply TracialL2.ext_equiv; simp

/-- `J₀` as an antilinear equivalence. -/
def l2Reverse : TracialL2 τ ≃ₗ⋆[ℂ] TracialL2 τ :=
  { TracialL2.involution τ with
    invFun := TracialL2.involution τ
    left_inv := TracialL2.involution_involution τ
    right_inv := TracialL2.involution_involution τ }

@[simp] theorem l2LeftAlgHom_apply (a : A) (y : TracialL2 τ) :
    l2LeftAlgHom τ a y = TracialL2.mulLeft τ a y := rfl
@[simp] theorem l2Right_apply (a : A) (y : TracialL2 τ) :
    l2Right τ a y = TracialL2.mulRight τ a y := rfl
@[simp] theorem l2Reverse_apply (y : TracialL2 τ) :
    l2Reverse τ y = TracialL2.involution τ y := rfl

/-- The inner derivation `δ_x a = x a - a x`, valued in `L²(A, τ)`. -/
def innerDerivation (x : A) : A →ₗ[ℂ] TracialL2 τ :=
  (TracialL2.equiv τ).symm.toLinearMap ∘ₗ (LinearMap.mulLeft ℂ x - LinearMap.mulRight ℂ x)

@[simp] theorem equiv_innerDerivation (x a : A) :
    TracialL2.equiv τ (innerDerivation τ x a) = x * a - a * x := rfl

/-- The compiler packet of the inner derivation `[x, ·]` with `K = L²(A, τ)`. -/
def innerDerivationPacket {n : ℕ} (x : A) (b : Module.Basis (Fin n) ℂ A) (i : Fin n)
    (hi : b i = 1) : FiniteDifferentialOccurrenceCompiler.Packet n A (TracialL2 τ) where
  basis := b
  unitIndex := i
  basis_unit := hi
  delta := innerDerivation τ x
  left := l2LeftAlgHom τ
  right := l2Right τ
  right_one := by ext y; apply TracialL2.ext_equiv; simp
  right_mul a c := by ext y; apply TracialL2.ext_equiv; simp [mul_assoc]
  commute_actions a c := by
    show l2LeftAlgHom τ a * l2Right τ c = l2Right τ c * l2LeftAlgHom τ a
    ext y; apply TracialL2.ext_equiv; simp [mul_assoc]
  reverse := l2Reverse τ
  reverse_left a y := by apply TracialL2.ext_equiv; simp [star_mul]
  reverse_right a y := by apply TracialL2.ext_equiv; simp [star_mul]
  reverse_involutive := TracialL2.involution_involution τ
  left_star_adjoint := TracialL2.inner_mulLeft τ
  right_star_adjoint := TracialL2.inner_mulRight τ
  reverse_inner := TracialL2.inner_involution τ

/-- For skew-adjoint `x`, `[x, ·]` is a finite real differential datum on
`(A, τ)` with `K = L²(A, τ)` and `C = J₀`. -/
def innerDerivationDatum {n : ℕ} (x : A) (hx : star x = -x) (b : Module.Basis (Fin n) ℂ A)
    (i : Fin n) (hi : b i = 1) : FiniteRealDifferentialDatum n A (TracialL2 τ) :=
  ⟨innerDerivationPacket τ x b i hi, by
    refine ⟨?_, ?_, ?_⟩
    · apply TracialL2.ext_equiv
      change x * 1 - 1 * x = (0 : A)
      simp
    · intro a c
      apply TracialL2.ext_equiv
      change x * (a * c) - a * c * x = a * (x * c - c * x) + (x * a - a * x) * c
      noncomm_ring
    · intro a
      apply TracialL2.ext_equiv
      change x * star a - star a * x = star (x * a - a * x)
      rw [star_sub, star_mul, star_mul, hx]
      noncomm_ring⟩

@[simp] theorem innerDerivationDatum_delta {n : ℕ} (x : A) (hx : star x = -x)
    (b : Module.Basis (Fin n) ℂ A) (i : Fin n) (hi : b i = 1) (a : A) :
    TracialL2.equiv τ ((innerDerivationDatum τ x hx b i hi).packet.delta a) =
      x * a - a * x := rfl

end InnerDerivation

/-! ### `M₂(ℂ)` with its normalized trace -/

/-- The normalized trace `τ(a) = Tr(a)/2` on `M₂(ℂ)`: a faithful tracial state. -/
def matrixNormalizedTrace : FaithfulTracialState (Matrix (Fin 2) (Fin 2) ℂ) where
  toLinearMap := (1 / 2 : ℂ) • Matrix.traceLinearMap (Fin 2) ℂ ℂ
  map_star a := by
    simp [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
  nonneg a := by
    simp only [LinearMap.smul_apply, Matrix.traceLinearMap_apply, smul_eq_mul,
      Matrix.star_eq_conjTranspose]
    refine mul_nonneg ?_ (Matrix.posSemidef_conjTranspose_mul_self a).trace_nonneg
    rw [Complex.nonneg_iff]
    norm_num
  faithful a h := by
    simp only [LinearMap.smul_apply, Matrix.traceLinearMap_apply, smul_eq_mul,
      Matrix.star_eq_conjTranspose, mul_eq_zero] at h
    rcases h with h | h
    · norm_num at h
    · exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h
  trace_comm a b := by
    simp only [LinearMap.smul_apply, Matrix.traceLinearMap_apply]
    rw [Matrix.trace_mul_comm]
  map_one := by
    simp only [LinearMap.smul_apply, Matrix.traceLinearMap_apply, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul]
    norm_num

/-- The skew-adjoint element `x = diag(i, -i)`. -/
def pauliSkew : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

theorem star_pauliSkew : star pauliSkew = -pauliSkew := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliSkew, Matrix.star_apply]

/-- **Non-vacuity.**  There is a finite real differential datum with `δ ≠ 0` on
the non-commutative algebra `M₂(ℂ)` with its normalized trace (the inner
derivation `[diag(i, -i), ·]`). -/
theorem exists_matrix_datum :
    ∃ (n : ℕ) (D : FiniteRealDifferentialDatum n (Matrix (Fin 2) (Fin 2) ℂ)
      (TracialL2 matrixNormalizedTrace)), D.packet.delta ≠ 0 := by
  obtain ⟨n, b, i, hi⟩ := exists_basis_with_one (A := Matrix (Fin 2) (Fin 2) ℂ)
    (FaithfulTracialState.one_ne_zero matrixNormalizedTrace)
  refine ⟨n, innerDerivationDatum matrixNormalizedTrace pauliSkew star_pauliSkew b i hi, ?_⟩
  intro h
  have h' := congrArg (fun f => TracialL2.equiv matrixNormalizedTrace
    (f !![(0 : ℂ), 1; 0, 0]) 0 1) h
  simp [pauliSkew, Matrix.mul_apply, Fin.sum_univ_two] at h'

end

end FiniteHodgeDiracDatum

/-- Non-vacuity of `finite_hodge_dirac`, `hodge_zero_mode` and `no_scale`: they apply to
a datum with `δ ≠ 0` on `M₂(ℂ)`, giving in particular a non-invertible Hodge--Dirac
matrix and, for `s = 2`, a Lipschitz seminorm that genuinely changes. -/
example : ∃ (n : ℕ) (D : AustereUnitZeroMode.FiniteRealDifferentialDatum n
      (Matrix (Fin 2) (Fin 2) ℂ) (FiniteHodgeDiracDatum.TracialL2
        FiniteHodgeDiracDatum.matrixNormalizedTrace)),
    D.packet.delta ≠ 0 ∧
    ¬ IsUnit (FiniteRealEvenSpectralizationExact.Packet.ofDatum D
      FiniteHodgeDiracDatum.matrixNormalizedTrace (stdOrthonormalBasis ℂ _)
      (stdOrthonormalBasis ℂ _)).dirac ∧
    (FiniteRealEvenSpectralizationExact.Packet.ofDatum (D.scale 2)
      FiniteHodgeDiracDatum.matrixNormalizedTrace (stdOrthonormalBasis ℂ _)
      (FiniteRealEvenSpectralizationExact.Packet.scaleBasis D (stdOrthonormalBasis ℂ _)
        two_ne_zero)).dirac ≠
    (FiniteRealEvenSpectralizationExact.Packet.ofDatum D
      FiniteHodgeDiracDatum.matrixNormalizedTrace (stdOrthonormalBasis ℂ _)
      (stdOrthonormalBasis ℂ _)).dirac := by
  obtain ⟨n, D, hD⟩ := FiniteHodgeDiracDatum.exists_matrix_datum
  exact ⟨n, D, hD,
    (FiniteRealEvenSpectralizationExact.Packet.hodge_zero_mode D _ _ _).2.2.2,
    FiniteRealEvenSpectralizationExact.Packet.ofDatum_scale_dirac_ne D _ _ _ hD two_pos
      (by norm_num)⟩


/-! ## Functoriality under trace- and differential-preserving `*`-isomorphisms -/

namespace FiniteRealEvenSpectralizationExact.Packet

variable {A A' I J : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring A'] [Algebra ℂ A'] [StarRing A'] [StarModule ℂ A']
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Pull back a coordinate packet along a `*`-algebra isomorphism. -/
def comap (Q : FiniteRealEvenSpectralizationExact.Packet (A := A') (I := I) (J := J))
    (φ : A ≃⋆ₐ[ℂ] A') : FiniteRealEvenSpectralizationExact.Packet (A := A) (I := I) (J := J) where
  left0 a := Q.left0 (φ a)
  left1 a := Q.left1 (φ a)
  right0 a := Q.right0 (φ a)
  right1 a := Q.right1 (φ a)
  differential := Q.differential
  B a := Q.B (φ a)
  B_real_smul r a := by rw [map_smul]; exact Q.B_real_smul r (φ a)
  partialVector a := Q.partialVector (φ a)
  unitVector := Q.unitVector
  left0_star a := by rw [Q.left0_star, map_star]
  left1_star a := by rw [Q.left1_star, map_star]
  right0_star a := by rw [Q.right0_star, map_star]
  right1_star a := by rw [Q.right1_star, map_star]
  commute0 a b := Q.commute0 _ _
  commute1 a b := Q.commute1 _ _
  leibniz a := Q.leibniz _
  B_right a b := Q.B_right _ _
  B_unit a := Q.B_unit _
  B_zero_of_partial_zero a := Q.B_zero_of_partial_zero _
  j0 := Q.j0
  j1 := Q.j1
  j0_sq := Q.j0_sq
  j1_sq := Q.j1_sq
  j0_left a := by rw [Q.j0_left, map_star]
  j1_left a := by rw [Q.j1_left, map_star]
  j_differential := Q.j_differential
  j_differentialAdjoint := Q.j_differentialAdjoint

end FiniteRealEvenSpectralizationExact.Packet

namespace FiniteHodgeDiracDatum

open FiniteDifferentialOccurrenceCompiler FiniteDifferentialOccurrenceCompiler.Packet
  AustereUnitZeroMode

noncomputable section

section OneForms

variable {A A' : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A]
  [NormedRing A'] [NormedAlgebra ℂ A'] [StarRing A'] [StarModule ℂ A']

/-- `φ ⊗ φ` on the ambient tensor square. -/
def tensorMap (φ : A ≃⋆ₐ[ℂ] A') : A ⊗[ℂ] A →ₗ[ℂ] A' ⊗[ℂ] A' :=
  TensorProduct.map φ.toAlgEquiv.toLinearMap φ.toAlgEquiv.toLinearMap

@[simp] theorem tensorMap_tmul (φ : A ≃⋆ₐ[ℂ] A') (x y : A) :
    tensorMap φ (x ⊗ₜ[ℂ] y) = φ x ⊗ₜ[ℂ] φ y := rfl

theorem mul_tensorMap (φ : A ≃⋆ₐ[ℂ] A') (t : A ⊗[ℂ] A) :
    LinearMap.mul' ℂ A' (tensorMap φ t) = φ (LinearMap.mul' ℂ A t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

/-- The induced map `Ω¹_u(A) → Ω¹_u(A')`. -/
def oneFormMap (φ : A ≃⋆ₐ[ℂ] A') : UniversalOneForm A →ₗ[ℂ] UniversalOneForm A' :=
  (tensorMap φ).restrict (fun t ht => by
    rw [LinearMap.mem_ker] at ht ⊢
    rw [mul_tensorMap, ht, map_zero])

@[simp] theorem coe_oneFormMap (φ : A ≃⋆ₐ[ℂ] A') (ω : UniversalOneForm A) :
    ((oneFormMap φ ω : UniversalOneForm A') : A' ⊗[ℂ] A') = tensorMap φ ω := rfl

theorem oneFormMap_left (φ : A ≃⋆ₐ[ℂ] A') (a : A) (ω : UniversalOneForm A) :
    oneFormMap φ (oneFormLeft a ω) = oneFormLeft (φ a) (oneFormMap φ ω) := by
  apply Subtype.ext
  simp only [coe_oneFormMap, oneFormLeft_coe]
  induction (ω : A ⊗[ℂ] A) using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

theorem oneFormMap_right (φ : A ≃⋆ₐ[ℂ] A') (a : A) (ω : UniversalOneForm A) :
    oneFormMap φ (oneFormRight a ω) = oneFormRight (φ a) (oneFormMap φ ω) := by
  apply Subtype.ext
  simp only [coe_oneFormMap, oneFormRight_coe]
  induction (ω : A ⊗[ℂ] A) using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

theorem oneFormMap_reversal (φ : A ≃⋆ₐ[ℂ] A') (ω : UniversalOneForm A) :
    oneFormMap φ (oneFormReversal ω) = oneFormReversal (oneFormMap φ ω) := by
  apply Subtype.ext
  simp only [coe_oneFormMap, oneFormReversal_coe]
  induction (ω : A ⊗[ℂ] A) using TensorProduct.induction_on with
  | zero => simp [tensorReversal]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [map_star]

theorem oneFormMap_symm (φ : A ≃⋆ₐ[ℂ] A') (ω : UniversalOneForm A') :
    oneFormMap φ (oneFormMap φ.symm ω) = ω := by
  apply Subtype.ext
  simp only [coe_oneFormMap]
  induction (ω : A' ⊗[ℂ] A') using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

end OneForms

variable {n n' : ℕ} {A A' K K' : Type*}
  [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A]
  [NormedRing A'] [NormedAlgebra ℂ A'] [StarRing A'] [StarModule ℂ A']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K']

/-- A trace- and differential-preserving `*`-isomorphism between finite real
differential data `(A, τ, δ)` and `(A', τ', δ')`: a `*`-isomorphism `φ` with
`τ' ∘ φ = τ`, and an isometry `u : K → K'` carrying the generators
`a δ(b)` of the retained bimodule to `φ(a) δ'(φ b)`. -/
structure DatumIso (D : FiniteRealDifferentialDatum n A K) (τ : FaithfulTracialState A)
    (D' : FiniteRealDifferentialDatum n' A' K') (τ' : FaithfulTracialState A') where
  alg : A ≃⋆ₐ[ℂ] A'
  trace_comp : ∀ a, τ'.toLinearMap (alg a) = τ.toLinearMap a
  bimod : K →ₗᵢ[ℂ] K'
  generator : ∀ a b, bimod (D.packet.left a (D.packet.delta b)) =
    D'.packet.left (alg a) (D'.packet.delta (alg b))

namespace DatumIso

variable {D : FiniteRealDifferentialDatum n A K} {τ : FaithfulTracialState A}
  {D' : FiniteRealDifferentialDatum n' A' K'} {τ' : FaithfulTracialState A'}
  (F : DatumIso D τ D' τ')

theorem bimod_delta (b : A) : F.bimod (D.packet.delta b) = D'.packet.delta (F.alg b) := by
  have h := F.generator 1 b
  rwa [map_one, map_one, map_one, Module.End.one_apply, Module.End.one_apply] at h

theorem bimod_factorTensor (t : A ⊗[ℂ] A) :
    F.bimod (D.packet.factorTensor t) = D'.packet.factorTensor (tensorMap F.alg t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simpa using F.generator x y

theorem bimod_universalFactor (ω : UniversalOneForm A) :
    F.bimod (D.packet.universalFactor ω) = D'.packet.universalFactor (oneFormMap F.alg ω) :=
  F.bimod_factorTensor ω

theorem bimod_mem {ξ : K} (h : ξ ∈ D.sourceMinimalCarrier) :
    F.bimod ξ ∈ D'.sourceMinimalCarrier := by
  obtain ⟨ω, rfl⟩ := h
  exact ⟨oneFormMap F.alg ω, (F.bimod_universalFactor ω).symm⟩

/-- The induced isometry of one-form spaces `H₁(δ) → H₁(δ')`. -/
def carrierMap : D.sourceMinimalCarrier →ₗᵢ[ℂ] D'.sourceMinimalCarrier :=
  (F.bimod.toLinearMap.restrict (fun _ h => F.bimod_mem h)).isometryOfInner
    (fun x y => F.bimod.inner_map_map x y)

@[simp] theorem coe_carrierMap (ξ : D.sourceMinimalCarrier) :
    ((F.carrierMap ξ : D'.sourceMinimalCarrier) : K') = F.bimod ξ := rfl

theorem carrierMap_surjective : Function.Surjective F.carrierMap := by
  rintro ⟨_, ω', rfl⟩
  refine ⟨⟨D.packet.universalFactor (oneFormMap F.alg.symm ω'), ⟨_, rfl⟩⟩, ?_⟩
  ext
  simp only [coe_carrierMap]
  rw [F.bimod_universalFactor, oneFormMap_symm]

/-- The induced unitary `H₁(δ) ≃ H₁(δ')`. -/
def carrierEquiv : D.sourceMinimalCarrier ≃ₗᵢ[ℂ] D'.sourceMinimalCarrier :=
  LinearIsometryEquiv.ofSurjective F.carrierMap F.carrierMap_surjective

@[simp] theorem coe_carrierEquiv (ξ : D.sourceMinimalCarrier) :
    ((F.carrierEquiv ξ : D'.sourceMinimalCarrier) : K') = F.bimod ξ := rfl

/-- The induced unitary `L²(A, τ) ≃ L²(A', τ')`, `a ↦ φ(a)`. -/
def l2Equiv : TracialL2 τ ≃ₗᵢ[ℂ] TracialL2 τ' :=
  LinearEquiv.isometryOfInner
    ((TracialL2.equiv τ).trans (F.alg.toAlgEquiv.toLinearEquiv.trans (TracialL2.equiv τ').symm))
    (fun x y => by
      simp only [TracialL2.inner_def]
      change τ'.toLinearMap (star (F.alg (TracialL2.equiv τ x)) * F.alg (TracialL2.equiv τ y)) = _
      rw [← map_star, ← map_mul, F.trace_comp])

@[simp] theorem equiv_l2Equiv (x : TracialL2 τ) :
    TracialL2.equiv τ' (F.l2Equiv x) = F.alg (TracialL2.equiv τ x) := rfl

theorem l2Equiv_mulLeft (a : A) (x : TracialL2 τ) :
    F.l2Equiv (TracialL2.mulLeft τ a x) = TracialL2.mulLeft τ' (F.alg a) (F.l2Equiv x) := by
  apply TracialL2.ext_equiv; simp

theorem l2Equiv_mulRight (a : A) (x : TracialL2 τ) :
    F.l2Equiv (TracialL2.mulRight τ a x) = TracialL2.mulRight τ' (F.alg a) (F.l2Equiv x) := by
  apply TracialL2.ext_equiv; simp

theorem l2Equiv_involution (x : TracialL2 τ) :
    F.l2Equiv (TracialL2.involution τ x) = TracialL2.involution τ' (F.l2Equiv x) := by
  apply TracialL2.ext_equiv; simp [map_star]

theorem carrierEquiv_left (a : A) (ξ : D.sourceMinimalCarrier) :
    F.carrierEquiv (D.carrierLeft a ξ) = D'.carrierLeft (F.alg a) (F.carrierEquiv ξ) := by
  obtain ⟨_, ω, rfl⟩ := ξ
  ext
  simp only [coe_carrierEquiv, FiniteRealDifferentialDatum.coe_carrierLeft]
  rw [← universalFactor_left, F.bimod_universalFactor, F.bimod_universalFactor,
    oneFormMap_left, universalFactor_left]

theorem carrierEquiv_right (a : A) (ξ : D.sourceMinimalCarrier) :
    F.carrierEquiv (D.carrierRight a ξ) = D'.carrierRight (F.alg a) (F.carrierEquiv ξ) := by
  obtain ⟨_, ω, rfl⟩ := ξ
  ext
  simp only [coe_carrierEquiv, FiniteRealDifferentialDatum.coe_carrierRight]
  rw [← universalFactor_right _ D.2, F.bimod_universalFactor, F.bimod_universalFactor,
    oneFormMap_right, universalFactor_right _ D'.2]

theorem carrierEquiv_reverse (ξ : D.sourceMinimalCarrier) :
    F.carrierEquiv (D.carrierReverse ξ) = D'.carrierReverse (F.carrierEquiv ξ) := by
  obtain ⟨_, ω, rfl⟩ := ξ
  ext
  simp only [coe_carrierEquiv, FiniteRealDifferentialDatum.coe_carrierReverse]
  rw [← universalFactor_reversal _ D.2, F.bimod_universalFactor, F.bimod_universalFactor,
    oneFormMap_reversal, universalFactor_reversal _ D'.2]

theorem carrierEquiv_hodgeDifferential (x : TracialL2 τ) :
    F.carrierEquiv (D.hodgeDifferential τ x) = D'.hodgeDifferential τ' (F.l2Equiv x) := by
  ext
  simp [F.bimod_delta]

theorem carrierEquiv_lipschitzBlock (a : A) (x : TracialL2 τ) :
    F.carrierEquiv (D.lipschitzBlock τ a x) =
      D'.lipschitzBlock τ' (F.alg a) (F.l2Equiv x) := by
  have h := F.carrierEquiv_right (TracialL2.equiv τ x) (D.partialVec a)
  ext
  have h' := congrArg Subtype.val h
  simp only [coe_carrierEquiv, FiniteRealDifferentialDatum.coe_carrierRight,
    FiniteRealDifferentialDatum.coe_partialVec] at h'
  simp only [coe_carrierEquiv, FiniteRealDifferentialDatum.coe_lipschitzBlock, equiv_l2Equiv]
  rw [h', F.bimod_delta]

/-- Identity morphism. -/
def refl (D : FiniteRealDifferentialDatum n A K) (τ : FaithfulTracialState A) :
    DatumIso D τ D τ where
  alg := StarAlgEquiv.refl ℂ A
  trace_comp _ := rfl
  bimod := LinearIsometry.id
  generator _ _ := rfl

/-- Composition of morphisms. -/
def comp {n'' : ℕ} {A'' K'' : Type*} [NormedRing A''] [NormedAlgebra ℂ A''] [StarRing A'']
    [StarModule ℂ A''] [NormedAddCommGroup K''] [InnerProductSpace ℂ K'']
    {D'' : FiniteRealDifferentialDatum n'' A'' K''} {τ'' : FaithfulTracialState A''}
    (G : DatumIso D' τ' D'' τ'') (F : DatumIso D τ D' τ') : DatumIso D τ D'' τ'' where
  alg := F.alg.trans G.alg
  trace_comp a := by
    change τ''.toLinearMap (G.alg (F.alg a)) = _
    rw [G.trace_comp, F.trace_comp]
  bimod := G.bimod.comp F.bimod
  generator a b := by
    change G.bimod (F.bimod _) = _
    rw [F.generator, G.generator]
    rfl

/-- Functoriality on `H₀`: `U₀(id) = id` and `U₀(G ∘ F) = U₀(G) U₀(F)`. -/
theorem l2Equiv_refl (x : TracialL2 τ) : (refl D τ).l2Equiv x = x := rfl

theorem l2Equiv_comp {n'' : ℕ} {A'' K'' : Type*} [NormedRing A''] [NormedAlgebra ℂ A'']
    [StarRing A''] [StarModule ℂ A''] [NormedAddCommGroup K''] [InnerProductSpace ℂ K'']
    {D'' : FiniteRealDifferentialDatum n'' A'' K''} {τ'' : FaithfulTracialState A''}
    (G : DatumIso D' τ' D'' τ'') (x : TracialL2 τ) :
    (G.comp F).l2Equiv x = G.l2Equiv (F.l2Equiv x) := rfl

/-- Functoriality on `H₁`. -/
theorem carrierEquiv_refl (ξ : D.sourceMinimalCarrier) : (refl D τ).carrierEquiv ξ = ξ := by
  ext; rfl

theorem carrierEquiv_comp {n'' : ℕ} {A'' K'' : Type*} [NormedRing A''] [NormedAlgebra ℂ A'']
    [StarRing A''] [StarModule ℂ A''] [NormedAddCommGroup K''] [InnerProductSpace ℂ K'']
    {D'' : FiniteRealDifferentialDatum n'' A'' K''} {τ'' : FaithfulTracialState A''}
    (G : DatumIso D' τ' D'' τ'') (ξ : D.sourceMinimalCarrier) :
    (G.comp F).carrierEquiv ξ = G.carrierEquiv (F.carrierEquiv ξ) := by
  ext; rfl

end DatumIso

end

end FiniteHodgeDiracDatum

namespace FiniteRealEvenSpectralizationExact.Packet

open FiniteHodgeDiracDatum AustereUnitZeroMode FiniteSpectralizationFunctorScaleExact

noncomputable section

variable {n n' : ℕ} {A A' K K' : Type*}
  [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A] [FiniteDimensional ℂ A]
  [NormedRing A'] [NormedAlgebra ℂ A'] [StarRing A'] [StarModule ℂ A'] [FiniteDimensional ℂ A']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
  {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {D : FiniteRealDifferentialDatum n A K} {τ : FaithfulTracialState A}
  {D' : FiniteRealDifferentialDatum n' A' K'} {τ' : FaithfulTracialState A'}
  (F : DatumIso D τ D' τ')
  (b₀ : OrthonormalBasis I ℂ (TracialL2 τ)) (b₁ : OrthonormalBasis J ℂ D.sourceMinimalCarrier)
  (b₀' : OrthonormalBasis I ℂ (TracialL2 τ')) (b₁' : OrthonormalBasis J ℂ D'.sourceMinimalCarrier)

/-- **Functoriality (`thm:summary-finite` (i)).**  A trace- and
differential-preserving `*`-isomorphism induces, in any orthonormal bases, an
`IsometricTransport` from the Hodge packet of `(A, τ, δ)` to the pull-back of
the Hodge packet of `(A', τ', δ')`; all intertwinings are derived. -/
def ofDatumTransport :
    IsometricTransport (ofDatum D τ b₀ b₁) ((ofDatum D' τ' b₀' b₁').comap F.alg) where
  U0 := coordMat b₀' b₀ F.l2Equiv
  U1 := coordMat b₁' b₁ F.carrierEquiv
  U0_star_mul := coordMat_unitary b₀' b₀ _ (fun x y => F.l2Equiv.inner_map_map x y)
  U0_mul_star := mul_eq_one_comm.1
    (coordMat_unitary b₀' b₀ _ (fun x y => F.l2Equiv.inner_map_map x y))
  U1_star_mul := coordMat_unitary b₁' b₁ _ (fun x y => F.carrierEquiv.inner_map_map x y)
  U1_mul_star := mul_eq_one_comm.1
    (coordMat_unitary b₁' b₁ _ (fun x y => F.carrierEquiv.inner_map_map x y))
  left0 a := by
    change coordMat b₀' b₀ F.l2Equiv * coordMat b₀ b₀ (TracialL2.mulLeft τ a) =
      coordMat b₀' b₀' (TracialL2.mulLeft τ' (F.alg a)) * coordMat b₀' b₀ F.l2Equiv
    rw [← coordMat_comp_isometry (g := F.l2Equiv),
      ← coordMat_comp_linear]
    congr 1
    funext x
    exact F.l2Equiv_mulLeft a x
  left1 a := by
    change coordMat b₁' b₁ F.carrierEquiv * coordMat b₁ b₁ (D.carrierLeft a) =
      coordMat b₁' b₁' (D'.carrierLeft (F.alg a)) * coordMat b₁' b₁ F.carrierEquiv
    rw [← coordMat_comp_isometry (g := F.carrierEquiv),
      ← coordMat_comp_linear]
    congr 1
    funext x
    exact F.carrierEquiv_left a x
  differential := by
    change coordMat b₁' b₁ F.carrierEquiv * coordMat b₁ b₀ (D.hodgeDifferential τ) =
      coordMat b₁' b₀' (D'.hodgeDifferential τ') * coordMat b₀' b₀ F.l2Equiv
    rw [← coordMat_comp_isometry (g := F.carrierEquiv),
      ← coordMat_comp_linear]
    congr 1
    funext x
    exact F.carrierEquiv_hodgeDifferential x
  real0 := by
    change coordMat b₀' b₀ F.l2Equiv * coordMat b₀ b₀ (TracialL2.involution τ) =
      coordMat b₀' b₀' (TracialL2.involution τ') * (coordMat b₀' b₀ F.l2Equiv).map star
    rw [← coordMat_comp_isometry (g := F.l2Equiv),
      ← coordMat_comp_antilinear]
    congr 1
    funext x
    exact F.l2Equiv_involution x
  real1 := by
    change coordMat b₁' b₁ F.carrierEquiv * coordMat b₁ b₁ D.carrierReverse =
      coordMat b₁' b₁' D'.carrierReverse * (coordMat b₁' b₁ F.carrierEquiv).map star
    rw [← coordMat_comp_isometry (g := F.carrierEquiv),
      ← coordMat_comp_antilinear]
    congr 1
    funext x
    exact F.carrierEquiv_reverse x

/-- The transport also intertwines the opposite representation and `B_a`. -/
theorem ofDatumTransport_right_B (a : A) :
    (ofDatumTransport F b₀ b₁ b₀' b₁').unitary * (ofDatum D τ b₀ b₁).oppositeRepresentation a =
      ((ofDatum D' τ' b₀' b₁').comap F.alg).oppositeRepresentation a *
        (ofDatumTransport F b₀ b₁ b₀' b₁').unitary ∧
    (ofDatumTransport F b₀ b₁ b₀' b₁').U1 * (ofDatum D τ b₀ b₁).B a =
      ((ofDatum D' τ' b₀' b₁').comap F.alg).B a * (ofDatumTransport F b₀ b₁ b₀' b₁').U0 := by
  have h0 : coordMat b₀' b₀ F.l2Equiv * coordMat b₀ b₀ (TracialL2.mulRight τ a) =
      coordMat b₀' b₀' (TracialL2.mulRight τ' (F.alg a)) * coordMat b₀' b₀ F.l2Equiv := by
    rw [← coordMat_comp_isometry (g := F.l2Equiv),
      ← coordMat_comp_linear]
    congr 1
    funext x
    exact F.l2Equiv_mulRight a x
  have h1 : coordMat b₁' b₁ F.carrierEquiv * coordMat b₁ b₁ (D.carrierRight a) =
      coordMat b₁' b₁' (D'.carrierRight (F.alg a)) * coordMat b₁' b₁ F.carrierEquiv := by
    rw [← coordMat_comp_isometry (g := F.carrierEquiv),
      ← coordMat_comp_linear]
    congr 1
    funext x
    exact F.carrierEquiv_right a x
  refine ⟨?_, ?_⟩
  · change Matrix.fromBlocks (coordMat b₀' b₀ F.l2Equiv) 0 0 (coordMat b₁' b₁ F.carrierEquiv) *
        Matrix.fromBlocks (coordMat b₀ b₀ (TracialL2.mulRight τ a)) 0 0
          (coordMat b₁ b₁ (D.carrierRight a)) =
      Matrix.fromBlocks (coordMat b₀' b₀' (TracialL2.mulRight τ' (F.alg a))) 0 0
          (coordMat b₁' b₁' (D'.carrierRight (F.alg a))) *
        Matrix.fromBlocks (coordMat b₀' b₀ F.l2Equiv) 0 0 (coordMat b₁' b₁ F.carrierEquiv)
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, h0, h1]
    simp
  · change coordMat b₁' b₁ F.carrierEquiv * coordMat b₁ b₀ (D.lipschitzBlock τ a) =
      coordMat b₁' b₀' (D'.lipschitzBlock τ' (F.alg a)) * coordMat b₀' b₀ F.l2Equiv
    rw [← coordMat_comp_isometry (g := F.carrierEquiv),
      ← coordMat_comp_linear]
    congr 1
    funext x
    exact F.carrierEquiv_lipschitzBlock a x

/-- Functoriality of the induced coordinate unitaries: for a composite
morphism, the transport matrices multiply (`U(G ∘ F) = U(G) U(F)`), and the
identity morphism in equal bases gives the identity matrices. -/
theorem ofDatumTransport_comp {n'' : ℕ} {A'' K'' : Type*} [NormedRing A'']
    [NormedAlgebra ℂ A''] [StarRing A''] [StarModule ℂ A''] [FiniteDimensional ℂ A'']
    [NormedAddCommGroup K''] [InnerProductSpace ℂ K'']
    {D'' : FiniteRealDifferentialDatum n'' A'' K''} {τ'' : FaithfulTracialState A''}
    (G : DatumIso D' τ' D'' τ'')
    (b₀'' : OrthonormalBasis I ℂ (TracialL2 τ''))
    (b₁'' : OrthonormalBasis J ℂ D''.sourceMinimalCarrier) :
    (ofDatumTransport (G.comp F) b₀ b₁ b₀'' b₁'').U0 =
      (ofDatumTransport G b₀' b₁' b₀'' b₁'').U0 * (ofDatumTransport F b₀ b₁ b₀' b₁').U0 ∧
    (ofDatumTransport (G.comp F) b₀ b₁ b₀'' b₁'').U1 =
      (ofDatumTransport G b₀' b₁' b₀'' b₁'').U1 * (ofDatumTransport F b₀ b₁ b₀' b₁').U1 := by
  constructor
  · change coordMat b₀'' b₀ (G.comp F).l2Equiv =
      coordMat b₀'' b₀' G.l2Equiv * coordMat b₀' b₀ F.l2Equiv
    rw [← coordMat_comp_isometry (g := G.l2Equiv)]
    rfl
  · change coordMat b₁'' b₁ (G.comp F).carrierEquiv =
      coordMat b₁'' b₁' G.carrierEquiv * coordMat b₁' b₁ F.carrierEquiv
    rw [← coordMat_comp_isometry (g := G.carrierEquiv)]
    exact congrArg _ (funext fun ξ => DatumIso.carrierEquiv_comp F G ξ)

theorem ofDatumTransport_refl :
    (ofDatumTransport (DatumIso.refl D τ) b₀ b₁ b₀ b₁).U0 = 1 ∧
    (ofDatumTransport (DatumIso.refl D τ) b₀ b₁ b₀ b₁).U1 = 1 := by
  constructor
  · exact coordMat_id b₀
  · change coordMat b₁ b₁ (DatumIso.refl D τ).carrierEquiv = 1
    rw [← coordMat_id b₁]
    exact congrArg _ (funext fun ξ => DatumIso.carrierEquiv_refl ξ)

/-- **`thm:summary-finite` (i), functoriality.**  The Hodge construction is
functorial: every trace- and differential-preserving `*`-isomorphism yields a
unitary `U = U₀ ⊕ U₁` with `U π(a) = π'(φ a) U`, `U D = D' U`, `U γ = γ' U`,
`U J = J' U`, intertwining also `π°` and `B_a`, and these unitaries respect
identities and composition. -/
theorem finite_hodge_dirac_functorial :
    (ofDatumTransport F b₀ b₁ b₀' b₁').unitaryᴴ * (ofDatumTransport F b₀ b₁ b₀' b₁').unitary = 1 ∧
    (∀ a, (ofDatumTransport F b₀ b₁ b₀' b₁').unitary * (ofDatum D τ b₀ b₁).representation a =
      (ofDatum D' τ' b₀' b₁').representation (F.alg a) *
        (ofDatumTransport F b₀ b₁ b₀' b₁').unitary) ∧
    (ofDatumTransport F b₀ b₁ b₀' b₁').unitary * (ofDatum D τ b₀ b₁).dirac =
      (ofDatum D' τ' b₀' b₁').dirac * (ofDatumTransport F b₀ b₁ b₀' b₁').unitary ∧
    (ofDatumTransport F b₀ b₁ b₀' b₁').unitary * (ofDatum D τ b₀ b₁).grading =
      (ofDatum D' τ' b₀' b₁').grading * (ofDatumTransport F b₀ b₁ b₀' b₁').unitary ∧
    (ofDatumTransport F b₀ b₁ b₀' b₁').unitary * (ofDatum D τ b₀ b₁).realMatrix =
      (ofDatum D' τ' b₀' b₁').realMatrix * (ofDatumTransport F b₀ b₁ b₀' b₁').unitary.map star ∧
    (∀ a, (ofDatumTransport F b₀ b₁ b₀' b₁').unitary *
        (ofDatum D τ b₀ b₁).oppositeRepresentation a =
      (ofDatum D' τ' b₀' b₁').oppositeRepresentation (F.alg a) *
        (ofDatumTransport F b₀ b₁ b₀' b₁').unitary) :=
  ⟨(ofDatumTransport F b₀ b₁ b₀' b₁').unitary_star_mul,
    (ofDatumTransport F b₀ b₁ b₀' b₁').intertwines_representation,
    (ofDatumTransport F b₀ b₁ b₀' b₁').intertwines_dirac,
    (ofDatumTransport F b₀ b₁ b₀' b₁').intertwines_grading,
    (ofDatumTransport F b₀ b₁ b₀' b₁').intertwines_real,
    fun a => (ofDatumTransport_right_B F b₀ b₁ b₀' b₁' a).1⟩

end

end FiniteRealEvenSpectralizationExact.Packet


/-! ## The quotient picture `H₁(δ) = Ω¹_u / Ker T_δ` -/

namespace AustereUnitZeroMode.FiniteRealDifferentialDatum

open FiniteDifferentialOccurrenceCompiler FiniteDifferentialOccurrenceCompiler.Packet

variable {n : ℕ} {A K : Type*}
  [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (D : FiniteRealDifferentialDatum n A K)

theorem coe_sourceMinimalEquiv_mk (ω : UniversalOneForm A) :
    ((D.sourceMinimalEquiv (Submodule.Quotient.mk ω) : D.sourceMinimalCarrier) : K) =
      D.packet.universalFactor ω :=
  D.packet.sourceMinimalEquivRange_apply ω

/-- The isometric identification carries the Gram `Q_δ` (eq:differential-Gram). -/
theorem inner_sourceMinimalEquiv_mk (ω η : UniversalOneForm A) :
    ⟪D.sourceMinimalEquiv (Submodule.Quotient.mk ω),
      D.sourceMinimalEquiv (Submodule.Quotient.mk η)⟫_ℂ = D.packet.inducedGram ω η := by
  rw [Submodule.coe_inner, coe_sourceMinimalEquiv_mk, coe_sourceMinimalEquiv_mk]
  rfl

/-- `∂ a = [d_u a]`. -/
theorem partialVec_eq_class (a : A) :
    D.partialVec a = D.sourceMinimalEquiv (Submodule.Quotient.mk (universalDifferential a)) := by
  ext
  rw [coe_sourceMinimalEquiv_mk, D.universalFactor_differential]
  rfl

/-- `J₁ [ω] = [ω^♮]`. -/
theorem carrierReverse_class (ω : UniversalOneForm A) :
    D.carrierReverse (D.sourceMinimalEquiv (Submodule.Quotient.mk ω)) =
      D.sourceMinimalEquiv (Submodule.Quotient.mk (oneFormReversal ω)) := by
  ext
  rw [coe_carrierReverse, coe_sourceMinimalEquiv_mk, coe_sourceMinimalEquiv_mk,
    D.packet.universalFactor_reversal D.2]

/-- `λ(a) [ω] = [a ω]`. -/
theorem carrierLeft_class (a : A) (ω : UniversalOneForm A) :
    D.carrierLeft a (D.sourceMinimalEquiv (Submodule.Quotient.mk ω)) =
      D.sourceMinimalEquiv (Submodule.Quotient.mk (oneFormLeft a ω)) := by
  ext
  rw [coe_carrierLeft, coe_sourceMinimalEquiv_mk, coe_sourceMinimalEquiv_mk,
    D.packet.universalFactor_left]

/-- `ρ(a) [ω] = [ω a]`. -/
theorem carrierRight_class (a : A) (ω : UniversalOneForm A) :
    D.carrierRight a (D.sourceMinimalEquiv (Submodule.Quotient.mk ω)) =
      D.sourceMinimalEquiv (Submodule.Quotient.mk (oneFormRight a ω)) := by
  ext
  rw [coe_carrierRight, coe_sourceMinimalEquiv_mk, coe_sourceMinimalEquiv_mk,
    D.packet.universalFactor_right D.2]

end AustereUnitZeroMode.FiniteRealDifferentialDatum

end RenewalGeometry
