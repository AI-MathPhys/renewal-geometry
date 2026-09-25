/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact module and symmetry defects on the regular word carrier

Covers `prop:word-module-defect` of the spacetime–gauge duality paper.

The regular word carrier `𝒲 = L²(A, τ_reg)` is encoded as a finite-dimensional
normed star ring `A` carrying an inner product which is the regular-trace form
`⟨x, y⟩ = τ_reg(x^* y)`, where `τ_reg(z) = D⁻¹ Tr_A(L_z)` is the normalised trace of
left multiplication (`D = dim_ℂ A`; this is the same formula as
`RenewalGeometry.normalizedRegularTrace`, and equals `D⁻¹ ∑_β n_β Tr(z_β)` in the
Wedderburn form `A ≅ ⊕_β M_{n_β}(ℂ)`).  The symmetries `U_g x = α_g(x)` are given by a
group homomorphism `α : G →* (A ≃ₗᵢ[ℂ] A)` with `α_g(1) = 1`; the inner automorphisms
`α_g = Ad(u_g)` by unitaries of the paper are a special case
(`isometry` because `τ_reg` is tracial, see `regularTraceForm_mul_comm`).

* `hsNorm S = ‖(S e_ν)_ν‖_{ℓ²}` is the Hilbert–Schmidt norm on `End(𝒲)`;
  `hsNorm_sq_eq_sum` shows it is independent of the orthonormal basis.
* `moduleDefect T = δ_R(T)`, `symmetryDefect α T = δ_G(T)` and
  `groupAverage α a = E_G(a)` are the paper's quantities.
* `word_module_defect` is `eq:word-module-defect`,
  `word_module_invariant_defect` is `eq:word-module-invariant-defect`, and
  `defects_vanish_iff` is the "both defects vanish exactly on `L(A^G)`" clause.
-/

open scoped InnerProductSpace
open Module

set_option linter.unusedSectionVars false

namespace RenewalGeometry

section RegularTraceForm

variable (A : Type*) [Ring A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]

/-- The normalised regular trace `τ_reg(z) = D⁻¹ Tr_A(L_z)`, the trace of left
multiplication divided by `D = dim_ℂ A` (the formula of `normalizedRegularTrace`). -/
noncomputable def regularTraceForm (z : A) : ℂ :=
  (finrank ℂ A : ℂ)⁻¹ * LinearMap.trace ℂ A (LinearMap.mulLeft ℂ z)

variable {A}

theorem regularTraceForm_apply (z : A) :
    regularTraceForm A z = (finrank ℂ A : ℂ)⁻¹ * LinearMap.trace ℂ A (LinearMap.mulLeft ℂ z) :=
  rfl

/-- Traciality of the regular trace: `τ_reg(ab) = τ_reg(ba)`. -/
theorem regularTraceForm_mul_comm [Module.Finite ℂ A] [Module.Free ℂ A] (a b : A) :
    regularTraceForm A (a * b) = regularTraceForm A (b * a) := by
  simp only [regularTraceForm, LinearMap.mulLeft_mul]
  congr 1
  exact LinearMap.trace_comp_comm' _ _

end RegularTraceForm

section WordCarrier

variable {A : Type*} [NormedRing A] [InnerProductSpace ℂ A] [SMulCommClass ℂ A A]
  [IsScalarTower ℂ A A] [StarRing A] [FiniteDimensional ℂ A]

/-- The inner product of the word carrier is the regular-trace form
`⟨x, y⟩ = τ_reg(x^* y)`: this is the defining property of `𝒲 = L²(A, τ_reg)`. -/
def IsRegularTraceInner (A : Type*) [NormedRing A] [InnerProductSpace ℂ A]
    [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarRing A] : Prop :=
  ∀ x y : A, ⟪x, y⟫_ℂ = regularTraceForm A (star x * y)

/-- The vector `(S e_ν)_ν ∈ ℓ²(𝒲)` of images of the standard orthonormal basis. -/
noncomputable def hsVector (S : Module.End ℂ A) :
    PiLp 2 (fun _ : Fin (finrank ℂ A) => A) :=
  WithLp.toLp 2 fun i => S (stdOrthonormalBasis ℂ A i)

/-- The Hilbert–Schmidt norm `‖S‖_{HS(𝒲)} = (∑_ν ‖S e_ν‖²)^{1/2}` on `End(𝒲)`. -/
noncomputable def hsNorm (S : Module.End ℂ A) : ℝ :=
  ‖hsVector S‖

theorem hsVector_add (S S' : Module.End ℂ A) :
    hsVector (S + S') = hsVector S + hsVector S' := by
  simp only [hsVector, LinearMap.add_apply]
  rfl

theorem hsNorm_nonneg (S : Module.End ℂ A) : 0 ≤ hsNorm S := norm_nonneg _

/-- Triangle inequality for the Hilbert–Schmidt norm. -/
theorem hsNorm_add_le (S S' : Module.End ℂ A) : hsNorm (S + S') ≤ hsNorm S + hsNorm S' := by
  unfold hsNorm
  rw [hsVector_add]
  exact norm_add_le _ _

/-- `∑_ν ‖S e_ν‖² = Re Tr(S^* S)` for every orthonormal basis `(e_ν)`. -/
theorem sum_norm_sq_eq_re_trace {ι : Type*} [Fintype ι] (S : Module.End ℂ A)
    (e : OrthonormalBasis ι ℂ A) :
    ∑ i, ‖S (e i)‖ ^ 2 =
      RCLike.re (LinearMap.trace ℂ A (LinearMap.adjoint S ∘ₗ S)) := by
  rw [LinearMap.trace_eq_sum_inner _ e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]

/-- The Hilbert–Schmidt norm is independent of the orthonormal basis:
`‖S‖²_{HS} = ∑_ν ‖S e_ν‖²` for every orthonormal basis. -/
theorem hsNorm_sq_eq_sum {ι : Type*} [Fintype ι] (S : Module.End ℂ A)
    (e : OrthonormalBasis ι ℂ A) :
    hsNorm S ^ 2 = ∑ i, ‖S (e i)‖ ^ 2 := by
  unfold hsNorm hsVector
  rw [PiLp.norm_sq_eq_of_L2, sum_norm_sq_eq_re_trace S e,
    ← sum_norm_sq_eq_re_trace S (stdOrthonormalBasis ℂ A)]

theorem hsNorm_eq_sqrt_sum {ι : Type*} [Fintype ι] (S : Module.End ℂ A)
    (e : OrthonormalBasis ι ℂ A) :
    hsNorm S = √(∑ i, ‖S (e i)‖ ^ 2) := by
  rw [← hsNorm_sq_eq_sum S e, Real.sqrt_sq (hsNorm_nonneg S)]

/-- The adjoint of left multiplication is left multiplication by the star,
for the regular-trace inner product. -/
theorem adjoint_mulLeft (hτ : IsRegularTraceInner A) (b : A) :
    LinearMap.adjoint (LinearMap.mulLeft ℂ b) = LinearMap.mulLeft ℂ (star b) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [hτ, hτ, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, star_mul, star_star,
    mul_assoc]

/-- `‖L_b‖²_{HS(𝒲)} = D ‖b‖²_τ`: the Hilbert–Schmidt norm of a left multiplication. -/
theorem hsNorm_mulLeft_sq [Nontrivial A] (hτ : IsRegularTraceInner A) (b : A) :
    hsNorm (LinearMap.mulLeft ℂ b) ^ 2 = (finrank ℂ A : ℝ) * ‖b‖ ^ 2 := by
  rw [hsNorm_sq_eq_sum _ (stdOrthonormalBasis ℂ A), sum_norm_sq_eq_re_trace,
    adjoint_mulLeft hτ, ← LinearMap.mulLeft_mul]
  have hD : (finrank ℂ A : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := A)).ne'
  have hb : LinearMap.trace ℂ A (LinearMap.mulLeft ℂ (star b * b)) =
      (finrank ℂ A : ℂ) * ⟪b, b⟫_ℂ := by
    rw [hτ, regularTraceForm_apply, ← mul_assoc, mul_inv_cancel₀ hD, one_mul]
  rw [hb, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-! ### The defects -/

/-- The module defect `δ_R(T) = (∑_ν ‖[T, R_{e_ν}] 1‖²_τ)^{1/2}`. -/
noncomputable def moduleDefect (T : Module.End ℂ A) : ℝ :=
  √(∑ i, ‖(T * LinearMap.mulRight ℂ (stdOrthonormalBasis ℂ A i) -
      LinearMap.mulRight ℂ (stdOrthonormalBasis ℂ A i) * T) 1‖ ^ 2)

/-- The symmetry operator `U_g x = α_g(x)` as an endomorphism of the word carrier. -/
def symmetryOp {G : Type*} (α : G → (A ≃ₗᵢ[ℂ] A)) (g : G) : Module.End ℂ A :=
  (α g).toLinearEquiv.toLinearMap

/-- The symmetry defect `δ_G(T) = (|G|⁻¹ ∑_g ‖[U_g, T] 1‖²_τ)^{1/2}`. -/
noncomputable def symmetryDefect {G : Type*} [Fintype G] (α : G → (A ≃ₗᵢ[ℂ] A))
    (T : Module.End ℂ A) : ℝ :=
  √((Fintype.card G : ℝ)⁻¹ * ∑ g, ‖(symmetryOp α g * T - T * symmetryOp α g) 1‖ ^ 2)

/-- The group average `E_G(a) = |G|⁻¹ ∑_g α_g(a)`. -/
noncomputable def groupAverage {G : Type*} [Fintype G] (α : G → (A ≃ₗᵢ[ℂ] A)) (a : A) : A :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, α g a

theorem moduleDefect_nonneg (T : Module.End ℂ A) : 0 ≤ moduleDefect T := Real.sqrt_nonneg _

theorem symmetryDefect_nonneg {G : Type*} [Fintype G] (α : G → (A ≃ₗᵢ[ℂ] A))
    (T : Module.End ℂ A) : 0 ≤ symmetryDefect α T := Real.sqrt_nonneg _

/-- `[T, R_b] 1 = (T - L_{T 1}) b`. -/
theorem commutator_mulRight_one (T : Module.End ℂ A) (b : A) :
    (T * LinearMap.mulRight ℂ b - LinearMap.mulRight ℂ b * T) 1 =
      (T - LinearMap.mulLeft ℂ (T 1)) b := by
  simp [Module.End.mul_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply]

/-- **`eq:word-module-defect`.**  `‖T − L_a‖_{HS(𝒲)} = δ_R(T)` with `a = T 1`. -/
theorem word_module_defect (T : Module.End ℂ A) :
    hsNorm (T - LinearMap.mulLeft ℂ (T 1)) = moduleDefect T := by
  rw [hsNorm_eq_sqrt_sum _ (stdOrthonormalBasis ℂ A), moduleDefect]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [commutator_mulRight_one]

/-- `eq:word-module-defect` in squared form: `‖T − L_a‖²_{HS} = δ_R(T)²`. -/
theorem word_module_defect_sq (T : Module.End ℂ A) :
    hsNorm (T - LinearMap.mulLeft ℂ (T 1)) ^ 2 = moduleDefect T ^ 2 := by
  rw [word_module_defect]

/-- `[U_g, T] 1 = α_g(a) − a` with `a = T 1`, when `U_g 1 = 1`. -/
theorem commutator_symmetry_one {G : Type*} (α : G → (A ≃ₗᵢ[ℂ] A))
    (hα : ∀ g, α g 1 = 1) (T : Module.End ℂ A) (g : G) :
    (symmetryOp α g * T - T * symmetryOp α g) 1 = α g (T 1) - T 1 := by
  change α g (T 1) - T (α g 1) = _
  rw [hα g]

/-- `δ_G(T)² = |G|⁻¹ ∑_g ‖α_g(a) − a‖²_τ` with `a = T 1`. -/
theorem symmetryDefect_sq {G : Type*} [Fintype G] (α : G → (A ≃ₗᵢ[ℂ] A))
    (hα : ∀ g, α g 1 = 1) (T : Module.End ℂ A) :
    symmetryDefect α T ^ 2 = (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖α g (T 1) - T 1‖ ^ 2 := by
  unfold symmetryDefect
  rw [Real.sq_sqrt (by positivity)]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [commutator_symmetry_one α hα]

/-! ### Orthogonal group averaging -/

section GroupAverage

variable {G : Type*} [Group G] [Fintype G] (α : G →* (A ≃ₗᵢ[ℂ] A))

/-- The group average is `G`-invariant: `α_k(E_G a) = E_G a`. -/
theorem symmetry_groupAverage (a : A) (k : G) :
    α k (groupAverage α a) = groupAverage α a := by
  unfold groupAverage
  rw [map_smul, map_sum]
  congr 1
  have h : ∀ g, α k (α g a) = α (k * g) a := fun g => by
    rw [map_mul]
    rfl
  simp_rw [h]
  exact Equiv.sum_comp (Equiv.mulLeft k) (fun g => α g a)

/-- `⟨E_G a, a⟩ = ⟨E_G a, E_G a⟩`: the group average is an orthogonal projection. -/
theorem inner_groupAverage_self (a : A) :
    ⟪groupAverage α a, a⟫_ℂ = ⟪groupAverage α a, groupAverage α a⟫_ℂ := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hexp : ⟪groupAverage α a, groupAverage α a⟫_ℂ =
      ⟪groupAverage α a, (Fintype.card G : ℂ)⁻¹ • ∑ g, α g a⟫_ℂ := rfl
  rw [hexp, inner_smul_right, inner_sum]
  have h : ∀ h : G, ⟪groupAverage α a, α h a⟫_ℂ = ⟪groupAverage α a, a⟫_ℂ := by
    intro h
    conv_lhs => rw [← symmetry_groupAverage α a h]
    exact (α h).inner_map_map _ _
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard,
    one_mul]

/-- `‖a − E_G a‖² = ‖a‖² − ‖E_G a‖²`. -/
theorem norm_sub_groupAverage_sq (a : A) :
    ‖a - groupAverage α a‖ ^ 2 = ‖a‖ ^ 2 - ‖groupAverage α a‖ ^ 2 := by
  rw [@norm_sub_sq ℂ, inner_re_symm, inner_groupAverage_self, inner_self_eq_norm_sq]
  ring

/-- **Orthogonal group averaging.**
`|G|⁻¹ ∑_g ‖α_g(a) − a‖²_τ = 2 ‖a − E_G(a)‖²_τ`. -/
theorem groupAverage_identity (a : A) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖α g a - a‖ ^ 2 = 2 * ‖a - groupAverage α a‖ ^ 2 := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hterm : ∀ g, ‖α g a - a‖ ^ 2 = 2 * ‖a‖ ^ 2 - 2 * RCLike.re ⟪α g a, a⟫_ℂ := by
    intro g
    rw [@norm_sub_sq ℂ, LinearIsometryEquiv.norm_map]
    ring
  have hE : RCLike.re ⟪groupAverage α a, a⟫_ℂ =
      (Fintype.card G : ℝ)⁻¹ * ∑ g, RCLike.re ⟪α g a, a⟫_ℂ := by
    rw [groupAverage, inner_smul_left, sum_inner]
    have hc : (starRingEnd ℂ) (Fintype.card G : ℂ)⁻¹ = (((Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ) := by
      simp
    rw [hc]
    simp only [RCLike.re_to_complex]
    rw [Complex.re_ofReal_mul, Complex.re_sum]
  rw [norm_sub_groupAverage_sq, ← inner_self_eq_norm_sq (𝕜 := ℂ) (groupAverage α a),
    ← inner_groupAverage_self, hE]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    mul_sub, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hcard]
  ring

/-- `δ_G(T)² = 2 ‖a − E_G a‖²` with `a = T 1`. -/
theorem symmetryDefect_sq_eq (hα : ∀ g, α g 1 = 1) (T : Module.End ℂ A) :
    symmetryDefect α T ^ 2 = 2 * ‖T 1 - groupAverage α (T 1)‖ ^ 2 := by
  rw [symmetryDefect_sq α hα, groupAverage_identity]

/-- **`eq:word-module-invariant-defect`.**
`‖T − L_{E_G(a)}‖_{HS(𝒲)} ≤ δ_R(T) + √(D/2) δ_G(T)` with `a = T 1`, `D = dim_ℂ A`. -/
theorem word_module_invariant_defect [Nontrivial A] (hτ : IsRegularTraceInner A)
    (hα : ∀ g, α g 1 = 1) (T : Module.End ℂ A) :
    hsNorm (T - LinearMap.mulLeft ℂ (groupAverage α (T 1))) ≤
      moduleDefect T + √((finrank ℂ A : ℝ) / 2) * symmetryDefect α T := by
  set a := T 1
  have hsplit : T - LinearMap.mulLeft ℂ (groupAverage α a) =
      (T - LinearMap.mulLeft ℂ a) +
        LinearMap.mulLeft ℂ (a - groupAverage α a) := by
    ext x
    simp [LinearMap.mulLeft_apply, sub_mul]
  have hL : hsNorm (LinearMap.mulLeft ℂ (a - groupAverage α a)) =
      √((finrank ℂ A : ℝ) / 2) * symmetryDefect α T := by
    have h1 : hsNorm (LinearMap.mulLeft ℂ (a - groupAverage α a)) ^ 2 =
        (√((finrank ℂ A : ℝ) / 2) * symmetryDefect α T) ^ 2 := by
      rw [hsNorm_mulLeft_sq hτ, mul_pow, Real.sq_sqrt (by positivity),
        symmetryDefect_sq_eq α hα]
      ring
    exact (pow_left_inj₀ (hsNorm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (symmetryDefect_nonneg α T)) two_ne_zero).mp h1
  calc hsNorm (T - LinearMap.mulLeft ℂ (groupAverage α a))
      ≤ hsNorm (T - LinearMap.mulLeft ℂ a) +
          hsNorm (LinearMap.mulLeft ℂ (a - groupAverage α a)) := by
        rw [hsplit]
        exact hsNorm_add_le _ _
    _ = moduleDefect T + √((finrank ℂ A : ℝ) / 2) * symmetryDefect α T := by
        rw [word_module_defect, hL]

/-- `δ_R(T) = 0` iff `T` is the left multiplication `L_{T 1}`. -/
theorem moduleDefect_eq_zero_iff (T : Module.End ℂ A) :
    moduleDefect T = 0 ↔ T = LinearMap.mulLeft ℂ (T 1) := by
  rw [← word_module_defect]
  unfold hsNorm
  rw [norm_eq_zero]
  constructor
  · intro h
    have hb : ∀ i, (T - LinearMap.mulLeft ℂ (T 1)) (stdOrthonormalBasis ℂ A i) = 0 := by
      intro i
      have := congrArg (fun v : PiLp 2 (fun _ : Fin (finrank ℂ A) => A) => v i) h
      simpa [hsVector] using this
    have hzero : T - LinearMap.mulLeft ℂ (T 1) = 0 :=
      (stdOrthonormalBasis ℂ A).toBasis.ext fun i => by simpa using hb i
    exact sub_eq_zero.mp hzero
  · intro h
    have hzero : T - LinearMap.mulLeft ℂ (T 1) = 0 := sub_eq_zero.mpr h
    unfold hsVector
    rw [hzero]
    rfl

/-- `δ_G(T) = 0` iff `T 1` is `G`-invariant (when `U_g 1 = 1`). -/
theorem symmetryDefect_eq_zero_iff {G : Type*} [Fintype G] [Nonempty G]
    (α : G → (A ≃ₗᵢ[ℂ] A)) (hα : ∀ g, α g 1 = 1) (T : Module.End ℂ A) :
    symmetryDefect α T = 0 ↔ ∀ g, α g (T 1) = T 1 := by
  have hcard : (Fintype.card G : ℝ)⁻¹ ≠ 0 := by
    have : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact inv_ne_zero this
  have hsq : symmetryDefect α T = 0 ↔ symmetryDefect α T ^ 2 = 0 := by
    constructor
    · intro h; rw [h]; ring
    · intro h; exact pow_eq_zero_iff two_ne_zero |>.mp h
  rw [hsq, symmetryDefect_sq α hα, mul_eq_zero, or_iff_right hcard,
    Finset.sum_eq_zero_iff_of_nonneg (fun g _ => by positivity)]
  simp only [Finset.mem_univ, true_implies, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, norm_eq_zero, sub_eq_zero]

/-- **Vanishing clause of `prop:word-module-defect`.**  Both defects vanish exactly on the
algebra `L(A^G)` of `thm:word-module-recognition`: `δ_R(T) = δ_G(T) = 0` iff `T` is left
multiplication by an invariant element. -/
theorem defects_vanish_iff {G : Type*} [Fintype G] [Nonempty G]
    (α : G → (A ≃ₗᵢ[ℂ] A)) (hα : ∀ g, α g 1 = 1) (T : Module.End ℂ A) :
    (moduleDefect T = 0 ∧ symmetryDefect α T = 0) ↔
      ∃ a : A, (∀ g, α g a = a) ∧ T = LinearMap.mulLeft ℂ a := by
  rw [moduleDefect_eq_zero_iff, symmetryDefect_eq_zero_iff α hα]
  constructor
  · rintro ⟨hT, hinv⟩
    exact ⟨T 1, hinv, hT⟩
  · rintro ⟨a, hinv, rfl⟩
    have h1 : LinearMap.mulLeft ℂ a 1 = a := by simp
    rw [h1]
    exact ⟨rfl, hinv⟩

end GroupAverage

end WordCarrier

end RenewalGeometry
