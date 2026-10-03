/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.WordModuleDefect

/-!
# Module and symmetry defects on the regular word carrier `L²(A, τ_reg)`

Covers `prop:word-module-defect` of the spacetime–gauge duality paper, repairing the
typeclass packet of `RenewalGeometry/Predictive/WordModuleDefect.lean`.

In `WordModuleDefect.lean` the carrier was a `NormedRing A` whose norm is also the
`τ_reg` Hilbert norm; since a `NormedRing` norm is submultiplicative this packet is
satisfiable only by `A = ℂ`.  Here the Hilbert space `𝒲 = L²(A, τ_reg)` is a *type synonym*
`RegularWord A` of the algebra `A`, carrying the ring structure of `A` and the
non-submultiplicative norm of the inner product `⟪x, y⟫ = τ_reg(x^* y)`, built from an
`InnerProductSpace.Core`.

* `RegularTraceFaithful A`: `τ_reg` is Hermitian, positive and faithful.  It is *derived*
  (not assumed) for every unital star-subalgebra `A ⊆ M_n(ℂ) = B(ℂⁿ)` — the paper's setting
  `A ⊆ B(H)` — by `regularTraceFaithful_starSubalgebra`, and for the full matrix algebras
  (`regularTraceFaithful_matrix`).  The general criterion is
  `regularTraceFaithful_of_core`: any inner product for which `L_{z^*} = L_z^*`.
* `RegularWord A` with `inner_def : ⟪x, y⟫ = τ_reg(x^* y)`.
* The symmetries are star-algebra automorphisms `α_g` of `A` (e.g. `Ad u_g`); they are
  `τ_reg`-unitaries (`regularTraceForm_starAlgEquiv`, `wordSymmetry`).
* `word_module_defect_regular` (`eq:word-module-defect`, for every `τ_reg`-orthonormal
  basis), `word_module_invariant_defect_regular` (`eq:word-module-invariant-defect`) and
  `defects_vanish_iff_regular` (vanishing exactly on `L(A^G)`).
* Non-vacuity: the packet is instantiated on `A = M₂(ℂ)` (dimension `4`) at the end.
-/

open scoped InnerProductSpace ComplexConjugate
open Module Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace RenewalGeometry

namespace WordL2

/-! ### Faithfulness of the regular trace -/

section Faithful

variable (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- The regular trace `τ_reg` is a Hermitian, positive and faithful functional:
`τ(z^*) = conj τ(z)`, `Re τ(x^* x) ≥ 0`, and `τ(x^* x) = 0 → x = 0`.  These are the
properties making `⟪x, y⟫ = τ_reg(x^* y)` an inner product on `A`. -/
structure RegularTraceFaithful : Prop where
  star_eq : ∀ z : A, regularTraceForm A (star z) = conj (regularTraceForm A z)
  nonneg : ∀ x : A, 0 ≤ (regularTraceForm A (star x * x)).re
  definite : ∀ x : A, regularTraceForm A (star x * x) = 0 → x = 0

variable {A}

theorem mulLeft_add' (a b : A) :
    LinearMap.mulLeft ℂ (a + b) = LinearMap.mulLeft ℂ a + LinearMap.mulLeft ℂ b := by
  ext x; simp [add_mul]

theorem mulLeft_smul' (c : ℂ) (a : A) :
    LinearMap.mulLeft ℂ (c • a) = c • LinearMap.mulLeft ℂ a := by
  ext x; simp

theorem regularTraceForm_add (a b : A) :
    regularTraceForm A (a + b) = regularTraceForm A a + regularTraceForm A b := by
  simp only [regularTraceForm, mulLeft_add', map_add, mul_add]

theorem regularTraceForm_smul (c : ℂ) (a : A) :
    regularTraceForm A (c • a) = c * regularTraceForm A a := by
  simp only [regularTraceForm, mulLeft_smul', map_smul, smul_eq_mul]
  ring

/-- `τ_reg` is invariant under algebra automorphisms (they conjugate left multiplication). -/
theorem regularTraceForm_algEquiv [Module.Free ℂ A] [Module.Finite ℂ A]
    (φ : A ≃ₐ[ℂ] A) (z : A) :
    regularTraceForm A (φ z) = regularTraceForm A z := by
  simp only [regularTraceForm]
  congr 1
  rw [← LinearMap.trace_conj' (LinearMap.mulLeft ℂ z) φ.toLinearEquiv]
  congr 1
  ext b
  simp [LinearEquiv.conj_apply]

theorem regularTraceForm_starAlgEquiv [Module.Free ℂ A] [Module.Finite ℂ A]
    (φ : A ≃⋆ₐ[ℂ] A) (z : A) :
    regularTraceForm A (φ z) = regularTraceForm A z :=
  regularTraceForm_algEquiv (φ.toAlgEquiv) z

/-- **Criterion for faithfulness.**  If `A` carries some inner product for which the adjoint
of left multiplication by `z` is left multiplication by `z^*`, then `τ_reg` is Hermitian,
positive and faithful. -/
theorem regularTraceFaithful_of_core [FiniteDimensional ℂ A] (c : InnerProductSpace.Core ℂ A)
    (hadj : ∀ z a b : A, c.inner a (z * b) = c.inner (star z * a) b) :
    RegularTraceFaithful A := by
  let _ : NormedAddCommGroup A := @InnerProductSpace.Core.toNormedAddCommGroup ℂ A _ _ _ c
  let _ : InnerProductSpace ℂ A := InnerProductSpace.ofCore c.toCore
  have hinner : ∀ x y : A, ⟪x, y⟫_ℂ = c.inner x y := fun _ _ => rfl
  let e := stdOrthonormalBasis ℂ A
  have hstar : ∀ z : A, LinearMap.trace ℂ A (LinearMap.mulLeft ℂ (star z)) =
      conj (LinearMap.trace ℂ A (LinearMap.mulLeft ℂ z)) := by
    intro z
    rw [LinearMap.trace_eq_sum_inner _ e, LinearMap.trace_eq_sum_inner _ e, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearMap.mulLeft_apply, hinner]
    rw [hadj, star_star, ← c.conj_inner_symm]
  have hsq : ∀ x : A, LinearMap.trace ℂ A (LinearMap.mulLeft ℂ (star x * x)) =
      ((∑ i, ‖x * e i‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [LinearMap.trace_eq_sum_inner _ e]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.mulLeft_apply, mul_assoc, hinner, hadj, star_star, ← hinner,
      inner_self_eq_norm_sq_to_K]
    simp
  refine ⟨fun z => ?_, fun x => ?_, fun x hx => ?_⟩
  · simp only [regularTraceForm, map_mul, hstar, map_inv₀, map_natCast]
  · simp only [regularTraceForm, hsq]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    positivity
  · rcases subsingleton_or_nontrivial A with hA | hA
    · exact Subsingleton.elim _ _
    have hD : (finrank ℂ A : ℂ)⁻¹ ≠ 0 := by
      have : (finrank ℂ A : ℂ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℂ) (M := A)).ne'
      exact inv_ne_zero this
    simp only [regularTraceForm, hsq, mul_eq_zero, hD, false_or] at hx
    have hx' : ∑ i, ‖x * e i‖ ^ 2 = 0 := by exact_mod_cast hx
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)] at hx'
    have hL : LinearMap.mulLeft ℂ x = 0 :=
      e.toBasis.ext fun i => by
        have := hx' i (Finset.mem_univ _)
        simpa using this
    simpa using LinearMap.congr_fun hL 1

/-- Pull back an inner-product core along an injective linear map. -/
@[instance_reducible]
noncomputable def coreComap {B : Type*} [AddCommGroup B] [Module ℂ B]
    (c : InnerProductSpace.Core ℂ B) (f : A →ₗ[ℂ] B) (hf : Function.Injective f) :
    InnerProductSpace.Core ℂ A where
  inner x y := c.inner (f x) (f y)
  conj_inner_symm x y := c.conj_inner_symm (f x) (f y)
  re_inner_nonneg x := c.re_inner_nonneg (f x)
  add_left x y z := by simp only [map_add]; exact c.add_left _ _ _
  smul_left x y r := by simp only [map_smul]; exact c.smul_left _ _ _
  definite x hx := hf (by rw [map_zero]; exact c.definite _ hx)

end Faithful

/-! ### The Frobenius (Hilbert–Schmidt) inner product on matrices -/

section Frobenius

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The Hilbert–Schmidt inner product `⟪x, y⟫ = Tr(x^H y)` on `M_n(ℂ)`. -/
@[instance_reducible]
noncomputable def frobeniusCore : InnerProductSpace.Core ℂ (Matrix n n ℂ) where
  inner x y := (xᴴ * y).trace
  conj_inner_symm x y := by
    simp only [starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  re_inner_nonneg x :=
    (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self x).trace_nonneg).1
  add_left x y z := by simp [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add]
  smul_left x y r := by
    simp [Matrix.conjTranspose_smul, Matrix.trace_smul]
  definite x hx := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hx

theorem frobeniusCore_inner (a b : Matrix n n ℂ) :
    (frobeniusCore n).inner a b = (aᴴ * b).trace := rfl

theorem frobeniusCore_adj (z a b : Matrix n n ℂ) :
    (frobeniusCore n).inner a (z * b) = (frobeniusCore n).inner (star z * a) b := by
  rw [frobeniusCore_inner, frobeniusCore_inner, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- `τ_reg` is faithful on the full matrix algebra `M_n(ℂ)`. -/
theorem regularTraceFaithful_matrix : RegularTraceFaithful (Matrix n n ℂ) :=
  regularTraceFaithful_of_core (frobeniusCore n) (frobeniusCore_adj n)

/-- **`τ_reg` is faithful on every finite `C^*`-algebra of operators.**  For every
star-subalgebra `A ⊆ M_n(ℂ) = B(ℂⁿ)` (the paper's `A ⊆ B(H)`), the regular trace of `A` is
Hermitian, positive and faithful. -/
theorem regularTraceFaithful_starSubalgebra (S : StarSubalgebra ℂ (Matrix n n ℂ)) :
    RegularTraceFaithful S := by
  have : FiniteDimensional ℂ S :=
    FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule S.toSubalgebra)
  refine regularTraceFaithful_of_core
    (coreComap (frobeniusCore n) (S.toSubalgebra.val.toLinearMap) Subtype.val_injective) ?_
  intro z a b
  change (frobeniusCore n).inner (a : Matrix n n ℂ) ((z : Matrix n n ℂ) * b) =
    (frobeniusCore n).inner (star (z : Matrix n n ℂ) * a) b
  exact frobeniusCore_adj n _ _ _

end Frobenius



/-! ### The regular word carrier `𝒲 = L²(A, τ_reg)` -/

section Carrier

variable (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [FiniteDimensional ℂ A]

/-- The regular word carrier `𝒲 = L²(A, τ_reg)`: a type synonym of `A` keeping the algebra
structure of `A` and carrying the regular-trace inner product (not a normed ring). -/
def RegularWord : Type _ := A

instance : Ring (RegularWord A) := inferInstanceAs (Ring A)
instance : StarRing (RegularWord A) := inferInstanceAs (StarRing A)
instance : Algebra ℂ (RegularWord A) := inferInstanceAs (Algebra ℂ A)
instance : StarModule ℂ (RegularWord A) := inferInstanceAs (StarModule ℂ A)
instance : FiniteDimensional ℂ (RegularWord A) := inferInstanceAs (FiniteDimensional ℂ A)

variable {A}

/-- The identification `A → 𝒲`, `a ↦ a`. -/
def toWord : A → RegularWord A := id

/-- The identification `𝒲 → A`, `x ↦ x`. -/
def ofWord : RegularWord A → A := id

variable [hA : Fact (RegularTraceFaithful A)]

/-- The regular-trace inner product core `⟪x, y⟫ = τ_reg(x^* y)` on `𝒲`. -/
@[instance_reducible]
noncomputable def regularInnerCore : InnerProductSpace.Core ℂ (RegularWord A) where
  inner x y := regularTraceForm A (star (ofWord x) * (ofWord y))
  conj_inner_symm x y := by
    change conj (regularTraceForm A (star (ofWord y) * (ofWord x))) =
      regularTraceForm A (star (ofWord x) * (ofWord y))
    rw [← hA.out.star_eq, star_mul, star_star]
  re_inner_nonneg x := hA.out.nonneg (ofWord x)
  add_left x y z := by
    change regularTraceForm A (star (ofWord x + ofWord y) * ofWord z) =
      regularTraceForm A (star (ofWord x) * ofWord z) +
        regularTraceForm A (star (ofWord y) * ofWord z)
    rw [star_add, add_mul, regularTraceForm_add]
  smul_left x y r := by
    change regularTraceForm A (star (r • (ofWord x)) * (ofWord y)) =
      conj r * regularTraceForm A (star (ofWord x) * (ofWord y))
    rw [star_smul, smul_mul_assoc, regularTraceForm_smul]
    rfl
  definite x hx := hA.out.definite (ofWord x) hx

noncomputable instance : NormedAddCommGroup (RegularWord A) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (regularInnerCore (A := A))

noncomputable instance : InnerProductSpace ℂ (RegularWord A) :=
  InnerProductSpace.ofCore (regularInnerCore (A := A)).toCore

/-- The inner product of the word carrier is the regular-trace form `⟪x, y⟫ = τ_reg(x^* y)`. -/
theorem inner_def (x y : RegularWord A) :
    ⟪x, y⟫_ℂ = regularTraceForm A (star (ofWord x) * (ofWord y)) := rfl

theorem inner_toWord (a b : A) :
    ⟪toWord a, toWord b⟫_ℂ = regularTraceForm A (star a * b) := rfl

/-- `Tr_𝒲(L_z) = D τ_reg(z)` with `D = dim_ℂ A`. -/
theorem trace_mulLeft_eq [Nontrivial A] (z : RegularWord A) :
    LinearMap.trace ℂ (RegularWord A) (LinearMap.mulLeft ℂ z) =
      (finrank ℂ A : ℂ) * regularTraceForm A (ofWord z) := by
  have hD : (finrank ℂ A : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := A)).ne'
  rw [regularTraceForm_apply, ← mul_assoc, mul_inv_cancel₀ hD, one_mul]
  rfl

end Carrier

/-! ### Hilbert–Schmidt norm on `End(𝒲)` -/

section HS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The vector `(S e_ν)_ν ∈ ℓ²(E)` of images of the standard orthonormal basis. -/
noncomputable def l2HsVector (S : Module.End ℂ E) :
    PiLp 2 (fun _ : Fin (finrank ℂ E) => E) :=
  WithLp.toLp 2 fun i => S (stdOrthonormalBasis ℂ E i)

/-- The Hilbert–Schmidt norm `‖S‖_{HS} = (∑_ν ‖S e_ν‖²)^{1/2}` on `End(E)`. -/
noncomputable def l2HsNorm (S : Module.End ℂ E) : ℝ :=
  ‖l2HsVector S‖

theorem l2HsNorm_nonneg (S : Module.End ℂ E) : 0 ≤ l2HsNorm S := norm_nonneg _

theorem l2HsNorm_add_le (S S' : Module.End ℂ E) :
    l2HsNorm (S + S') ≤ l2HsNorm S + l2HsNorm S' := by
  unfold l2HsNorm
  have : l2HsVector (S + S') = l2HsVector S + l2HsVector S' := by
    simp only [l2HsVector, LinearMap.add_apply]; rfl
  rw [this]
  exact norm_add_le _ _

theorem l2_sum_norm_sq_eq_re_trace {ι : Type*} [Fintype ι] (S : Module.End ℂ E)
    (e : OrthonormalBasis ι ℂ E) :
    ∑ i, ‖S (e i)‖ ^ 2 =
      RCLike.re (LinearMap.trace ℂ E (LinearMap.adjoint S ∘ₗ S)) := by
  rw [LinearMap.trace_eq_sum_inner _ e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]

/-- Basis independence: `‖S‖²_{HS} = ∑_ν ‖S e_ν‖²` for every orthonormal basis. -/
theorem l2HsNorm_sq_eq_sum {ι : Type*} [Fintype ι] (S : Module.End ℂ E)
    (e : OrthonormalBasis ι ℂ E) :
    l2HsNorm S ^ 2 = ∑ i, ‖S (e i)‖ ^ 2 := by
  unfold l2HsNorm l2HsVector
  rw [PiLp.norm_sq_eq_of_L2, l2_sum_norm_sq_eq_re_trace S e,
    ← l2_sum_norm_sq_eq_re_trace S (stdOrthonormalBasis ℂ E)]

theorem l2HsNorm_eq_sqrt_sum {ι : Type*} [Fintype ι] (S : Module.End ℂ E)
    (e : OrthonormalBasis ι ℂ E) :
    l2HsNorm S = √(∑ i, ‖S (e i)‖ ^ 2) := by
  rw [← l2HsNorm_sq_eq_sum S e, Real.sqrt_sq (l2HsNorm_nonneg S)]

theorem l2HsNorm_eq_zero_iff (S : Module.End ℂ E) : l2HsNorm S = 0 ↔ S = 0 := by
  constructor
  · intro h
    have h2 : ∑ i, ‖S (stdOrthonormalBasis ℂ E i)‖ ^ 2 = 0 := by
      rw [← l2HsNorm_sq_eq_sum, h]; ring
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)] at h2
    exact (stdOrthonormalBasis ℂ E).toBasis.ext fun i => by
      simpa using h2 i (Finset.mem_univ _)
  · rintro rfl
    unfold l2HsNorm l2HsVector
    simp only [LinearMap.zero_apply]
    exact norm_eq_zero.mpr rfl

end HS

/-! ### Orthogonal group averaging on an inner product space -/

section Average

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {G : Type*} [Group G] [Fintype G] (α : G →* (E ≃ₗᵢ[ℂ] E))

/-- The group average `E_G(a) = |G|⁻¹ ∑_g α_g(a)`. -/
noncomputable def l2GroupAverage (a : E) : E :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, α g a

theorem l2_symmetry_groupAverage (a : E) (k : G) :
    α k (l2GroupAverage α a) = l2GroupAverage α a := by
  unfold l2GroupAverage
  rw [map_smul, map_sum]
  congr 1
  have h : ∀ g, α k (α g a) = α (k * g) a := fun g => by
    rw [map_mul]
    rfl
  simp_rw [h]
  exact Equiv.sum_comp (Equiv.mulLeft k) (fun g => α g a)

theorem l2_inner_groupAverage_self (a : E) :
    ⟪l2GroupAverage α a, a⟫_ℂ = ⟪l2GroupAverage α a, l2GroupAverage α a⟫_ℂ := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hexp : ⟪l2GroupAverage α a, l2GroupAverage α a⟫_ℂ =
      ⟪l2GroupAverage α a, (Fintype.card G : ℂ)⁻¹ • ∑ g, α g a⟫_ℂ := rfl
  rw [hexp, inner_smul_right, inner_sum]
  have h : ∀ h : G, ⟪l2GroupAverage α a, α h a⟫_ℂ = ⟪l2GroupAverage α a, a⟫_ℂ := by
    intro h
    conv_lhs => rw [← l2_symmetry_groupAverage α a h]
    exact (α h).inner_map_map _ _
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard,
    one_mul]

theorem l2_norm_sub_groupAverage_sq (a : E) :
    ‖a - l2GroupAverage α a‖ ^ 2 = ‖a‖ ^ 2 - ‖l2GroupAverage α a‖ ^ 2 := by
  rw [@norm_sub_sq ℂ, inner_re_symm, l2_inner_groupAverage_self, inner_self_eq_norm_sq]
  ring

/-- **Orthogonal group averaging.** `|G|⁻¹ ∑_g ‖α_g(a) − a‖² = 2 ‖a − E_G(a)‖²`. -/
theorem l2_groupAverage_identity (a : E) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖α g a - a‖ ^ 2 = 2 * ‖a - l2GroupAverage α a‖ ^ 2 := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hterm : ∀ g, ‖α g a - a‖ ^ 2 = 2 * ‖a‖ ^ 2 - 2 * RCLike.re ⟪α g a, a⟫_ℂ := by
    intro g
    rw [@norm_sub_sq ℂ, LinearIsometryEquiv.norm_map]
    ring
  have hE : RCLike.re ⟪l2GroupAverage α a, a⟫_ℂ =
      (Fintype.card G : ℝ)⁻¹ * ∑ g, RCLike.re ⟪α g a, a⟫_ℂ := by
    rw [l2GroupAverage, inner_smul_left, sum_inner]
    have hc : (starRingEnd ℂ) (Fintype.card G : ℂ)⁻¹ = (((Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ) := by
      simp
    rw [hc]
    simp only [RCLike.re_to_complex]
    rw [Complex.re_ofReal_mul, Complex.re_sum]
  rw [l2_norm_sub_groupAverage_sq, ← inner_self_eq_norm_sq (𝕜 := ℂ) (l2GroupAverage α a),
    ← l2_inner_groupAverage_self, hE]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    mul_sub, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hcard]
  ring

end Average

/-! ### Defects on the regular word carrier -/

section Defects

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [FiniteDimensional ℂ A]
  [hA : Fact (RegularTraceFaithful A)]

/-- `L_{z^*} = L_z^*` on `𝒲` (the regular-trace inner product). -/
theorem adjoint_mulLeft_word (b : RegularWord A) :
    LinearMap.adjoint (LinearMap.mulLeft ℂ b) = LinearMap.mulLeft ℂ (star b) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_def, inner_def, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply]
  change regularTraceForm A (star ((star (ofWord b)) * (ofWord x)) * (ofWord y)) =
    regularTraceForm A (star (ofWord x) * (ofWord b * (ofWord y)))
  rw [star_mul, star_star, mul_assoc]

/-- `‖L_b‖²_{HS(𝒲)} = D ‖b‖²_τ`. -/
theorem l2HsNorm_mulLeft_sq (b : RegularWord A) :
    l2HsNorm (LinearMap.mulLeft ℂ b) ^ 2 = (finrank ℂ A : ℝ) * ‖b‖ ^ 2 := by
  rcases subsingleton_or_nontrivial A with hs | hn
  · have hD : (finrank ℂ A) = 0 := Module.finrank_zero_of_subsingleton
    have hb : b = 0 := Subsingleton.elim (α := A) _ _
    subst hb
    rw [hD]
    have h0 : LinearMap.mulLeft ℂ (0 : RegularWord A) = 0 := by ext; simp
    rw [h0, (l2HsNorm_eq_zero_iff (E := RegularWord A) 0).mpr rfl]
    simp
  rw [l2HsNorm_sq_eq_sum _ (stdOrthonormalBasis ℂ (RegularWord A)),
    l2_sum_norm_sq_eq_re_trace, adjoint_mulLeft_word, ← LinearMap.mulLeft_mul,
    trace_mulLeft_eq]
  have hb : regularTraceForm A (ofWord (star b * b)) = ⟪b, b⟫_ℂ := rfl
  rw [hb, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- The module defect `δ_R(T) = (∑_ν ‖[T, R_{e_ν}] 1‖²_τ)^{1/2}` for a `τ_reg`-orthonormal
basis `(e_ν)` of `A`. -/
noncomputable def l2ModuleDefect {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ (RegularWord A)) (T : Module.End ℂ (RegularWord A)) : ℝ :=
  √(∑ i, ‖(T * LinearMap.mulRight ℂ (e i) - LinearMap.mulRight ℂ (e i) * T) 1‖ ^ 2)

theorem l2_commutator_mulRight_one (T : Module.End ℂ (RegularWord A)) (b : RegularWord A) :
    (T * LinearMap.mulRight ℂ b - LinearMap.mulRight ℂ b * T) 1 =
      (T - LinearMap.mulLeft ℂ (T 1)) b := by
  simp [Module.End.mul_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply]

/-- **`eq:word-module-defect`.**  For every `τ_reg`-orthonormal basis `(e_ν)` of `A`,
`‖T − L_a‖_{HS(𝒲)} = δ_R(T)` with `a = T 1`. -/
theorem word_module_defect_regular {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ (RegularWord A)) (T : Module.End ℂ (RegularWord A)) :
    l2HsNorm (T - LinearMap.mulLeft ℂ (T 1)) = l2ModuleDefect e T := by
  rw [l2HsNorm_eq_sqrt_sum _ e, l2ModuleDefect]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [l2_commutator_mulRight_one]

/-- A star-algebra automorphism `φ` of `A` is a unitary `U_φ x = φ(x)` of `𝒲`. -/
noncomputable def wordSymmetry (φ : A ≃⋆ₐ[ℂ] A) : RegularWord A ≃ₗᵢ[ℂ] RegularWord A :=
  LinearEquiv.isometryOfInner (φ.toAlgEquiv.toLinearEquiv : A ≃ₗ[ℂ] A) fun x y => by
    change regularTraceForm A (star (φ (ofWord x)) * φ (ofWord y)) =
      regularTraceForm A (star (ofWord x) * (ofWord y))
    rw [← map_star, ← map_mul, regularTraceForm_starAlgEquiv]

theorem wordSymmetry_apply (φ : A ≃⋆ₐ[ℂ] A) (x : RegularWord A) :
    wordSymmetry φ x = toWord (φ (ofWord x)) := rfl

/-- The unitary representation `g ↦ U_g` of `G` on `𝒲` induced by `α : G →* Aut_⋆(A)`. -/
noncomputable def wordSymmetryHom {G : Type*} [Group G] (α : G →* (A ≃⋆ₐ[ℂ] A)) :
    G →* (RegularWord A ≃ₗᵢ[ℂ] RegularWord A) where
  toFun g := wordSymmetry (α g)
  map_one' := by
    ext x
    rw [wordSymmetry_apply, map_one]
    rfl
  map_mul' g h := by
    ext x
    rw [wordSymmetry_apply, map_mul]
    rfl

variable {G : Type*} [Group G] [Fintype G]

/-- The symmetry defect `δ_G(T) = (|G|⁻¹ ∑_g ‖[U_g, T] 1‖²_τ)^{1/2}`. -/
noncomputable def l2SymmetryDefect (α : G →* (A ≃⋆ₐ[ℂ] A))
    (T : Module.End ℂ (RegularWord A)) : ℝ :=
  √((Fintype.card G : ℝ)⁻¹ * ∑ g,
    ‖((wordSymmetryHom α g).toLinearEquiv.toLinearMap * T -
      T * (wordSymmetryHom α g).toLinearEquiv.toLinearMap) 1‖ ^ 2)

/-- `E_G(a) = |G|⁻¹ ∑_g α_g(a)` on `𝒲`. -/
noncomputable def l2WordAverage (α : G →* (A ≃⋆ₐ[ℂ] A)) (a : RegularWord A) : RegularWord A :=
  l2GroupAverage (wordSymmetryHom α) a

theorem l2WordAverage_eq (α : G →* (A ≃⋆ₐ[ℂ] A)) (a : RegularWord A) :
    l2WordAverage α a = (Fintype.card G : ℂ)⁻¹ • ∑ g, toWord (α g (ofWord a)) := rfl

theorem l2SymmetryDefect_sq_eq (α : G →* (A ≃⋆ₐ[ℂ] A)) (T : Module.End ℂ (RegularWord A)) :
    l2SymmetryDefect α T ^ 2 = 2 * ‖T 1 - l2WordAverage α (T 1)‖ ^ 2 := by
  unfold l2SymmetryDefect
  rw [Real.sq_sqrt (by positivity), l2WordAverage, ← l2_groupAverage_identity]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : (wordSymmetryHom α g) (1 : RegularWord A) = 1 := by
    change toWord ((α g) (1 : A)) = 1
    rw [map_one]; rfl
  change ‖(wordSymmetryHom α g) (T 1) - T ((wordSymmetryHom α g) 1)‖ ^ 2 = _
  rw [h1]

/-- **`eq:word-module-invariant-defect`.**
`‖T − L_{E_G(a)}‖_{HS(𝒲)} ≤ δ_R(T) + √(D/2) δ_G(T)` with `a = T 1`, `D = dim_ℂ A`. -/
theorem word_module_invariant_defect_regular {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ (RegularWord A)) (α : G →* (A ≃⋆ₐ[ℂ] A))
    (T : Module.End ℂ (RegularWord A)) :
    l2HsNorm (T - LinearMap.mulLeft ℂ (l2WordAverage α (T 1))) ≤
      l2ModuleDefect e T + √((finrank ℂ A : ℝ) / 2) * l2SymmetryDefect α T := by
  set a := T 1
  have hsplit : T - LinearMap.mulLeft ℂ (l2WordAverage α a) =
      (T - LinearMap.mulLeft ℂ a) + LinearMap.mulLeft ℂ (a - l2WordAverage α a) := by
    ext x
    simp [LinearMap.mulLeft_apply, sub_mul]
  have hL : l2HsNorm (LinearMap.mulLeft ℂ (a - l2WordAverage α a)) =
      √((finrank ℂ A : ℝ) / 2) * l2SymmetryDefect α T := by
    have h1 : l2HsNorm (LinearMap.mulLeft ℂ (a - l2WordAverage α a)) ^ 2 =
        (√((finrank ℂ A : ℝ) / 2) * l2SymmetryDefect α T) ^ 2 := by
      rw [l2HsNorm_mulLeft_sq, mul_pow, Real.sq_sqrt (by positivity), l2SymmetryDefect_sq_eq]
      ring
    exact (pow_left_inj₀ (l2HsNorm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) two_ne_zero).mp h1
  calc l2HsNorm (T - LinearMap.mulLeft ℂ (l2WordAverage α a))
      ≤ l2HsNorm (T - LinearMap.mulLeft ℂ a) +
          l2HsNorm (LinearMap.mulLeft ℂ (a - l2WordAverage α a)) := by
        rw [hsplit]
        exact l2HsNorm_add_le _ _
    _ = l2ModuleDefect e T + √((finrank ℂ A : ℝ) / 2) * l2SymmetryDefect α T := by
        rw [word_module_defect_regular e, hL]

/-- **Vanishing clause of `prop:word-module-defect`.**  `δ_R(T) = δ_G(T) = 0` iff
`T = L_a` for a `G`-invariant `a ∈ A^G` (the algebra `L(A^G)` of
`eq:word-module-recognition`). -/
theorem defects_vanish_iff_regular {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ (RegularWord A)) (α : G →* (A ≃⋆ₐ[ℂ] A))
    (T : Module.End ℂ (RegularWord A)) :
    (l2ModuleDefect e T = 0 ∧ l2SymmetryDefect α T = 0) ↔
      ∃ a : A, (∀ g, α g a = a) ∧ T = LinearMap.mulLeft ℂ (toWord a) := by
  have hR : l2ModuleDefect e T = 0 ↔ T = LinearMap.mulLeft ℂ (T 1) := by
    rw [← word_module_defect_regular e, l2HsNorm_eq_zero_iff, sub_eq_zero]
  have hG : l2SymmetryDefect α T = 0 ↔ ∀ g, α g (ofWord (T 1)) = ofWord (T 1) := by
    have hsq : l2SymmetryDefect α T = 0 ↔ l2SymmetryDefect α T ^ 2 = 0 := by
      constructor
      · intro h; rw [h]; ring
      · intro h; exact pow_eq_zero_iff two_ne_zero |>.mp h
    rw [hsq, l2SymmetryDefect_sq_eq, mul_eq_zero, or_iff_right two_ne_zero,
      pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero]
    constructor
    · intro h g
      have := l2_symmetry_groupAverage (wordSymmetryHom α) (T 1) g
      rw [← l2WordAverage, ← h] at this
      exact this
    · intro h
      rw [l2WordAverage_eq]
      have : ∀ g, toWord (α g (ofWord (T 1))) = T 1 := fun g => h g
      simp_rw [this]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
  rw [hR, hG]
  constructor
  · rintro ⟨hT, hinv⟩
    exact ⟨T 1, hinv, hT⟩
  · rintro ⟨a, hinv, rfl⟩
    have h1 : LinearMap.mulLeft ℂ (toWord a) 1 = toWord a := by simp
    rw [h1]
    exact ⟨rfl, hinv⟩

end Defects

/-! ### Non-vacuity: the packet on `M₂(ℂ)` -/

instance factRegularTraceFaithful_matrix (n : Type*) [Fintype n] [DecidableEq n] :
    Fact (RegularTraceFaithful (Matrix n n ℂ)) :=
  ⟨regularTraceFaithful_matrix n⟩

/-- The word carrier of `M₂(ℂ)` has dimension `D = 4` (so the packet is not the trivial
`A = ℂ`). -/
theorem finrank_regularWord_matrix_two :
    finrank ℂ (RegularWord (Matrix (Fin 2) (Fin 2) ℂ)) = 4 := by
  change finrank ℂ (Matrix (Fin 2) (Fin 2) ℂ) = 4
  simp [Module.finrank_matrix]

/-- Non-vacuity: `eq:word-module-invariant-defect` instantiated on `A = M₂(ℂ)` with
`⟪x, y⟫ = τ_reg(x^* y)` and the two-element group acting trivially. -/
example (T : Module.End ℂ (RegularWord (Matrix (Fin 2) (Fin 2) ℂ))) :
    l2HsNorm (T - LinearMap.mulLeft ℂ
        (l2WordAverage (1 : Multiplicative (ZMod 2) →* _) (T 1))) ≤
      l2ModuleDefect (stdOrthonormalBasis ℂ _) T +
        √((4 : ℝ) / 2) * l2SymmetryDefect (1 : Multiplicative (ZMod 2) →* _) T := by
  have := word_module_invariant_defect_regular (stdOrthonormalBasis ℂ _)
    (1 : Multiplicative (ZMod 2) →* (Matrix (Fin 2) (Fin 2) ℂ ≃⋆ₐ[ℂ] _)) T
  have h4 : (finrank ℂ (Matrix (Fin 2) (Fin 2) ℂ) : ℝ) = 4 := by
    have := finrank_regularWord_matrix_two
    exact_mod_cast this
  rwa [h4] at this

/-- Non-vacuity: the regular-trace norm on `𝒲(M₂(ℂ))` is non-degenerate on a non-scalar
matrix unit. -/
example : ‖toWord (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≠ 0 := by
  rw [norm_ne_zero_iff]
  intro h
  have := congrFun (congrFun (show (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 from h)
    0) 1
  simp at this


end WordL2

end RenewalGeometry
