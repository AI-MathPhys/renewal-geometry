/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.UnboundedSelfAdjointResolvent

/-!
# Symmetric pseudo-resolvents and their self-adjoint generators

A *symmetric pseudo-resolvent* on a complex Hilbert space `H` is a family of bounded operators
`R(z)`, indexed by the non-real points `z`, satisfying the resolvent identity
`R(z) - R(w) = (z - w) R(z) R(w)` and the adjoint symmetry `R(z)† = R(z̄)`.  Mathlib has no theory
of unbounded self-adjoint operators beyond `LinearPMap.adjoint`; the library represents an
unbounded self-adjoint operator by `SelfAdjointResolventData` (a symmetric partial linear map with
two-sided bounded inverses of `op - z`, bridged to Mathlib by
`SelfAdjointResolventData.isSelfAdjoint_op`).  This file proves the pseudo-resolvent theorem in
that representation:

* `IsSymmetricPseudoResolvent.commute`: the operators `R(z)` commute;
* `IsSymmetricPseudoResolvent.norm_le`: the automatic bound `‖R(z)‖ ≤ |Im z|⁻¹`;
* `IsSymmetricPseudoResolvent.injective_of_injective`: the kernel does not depend on `z`;
* `IsSymmetricPseudoResolvent.toSelfAdjointResolventData`: **an injective symmetric
  pseudo-resolvent is the resolvent of a self-adjoint operator** (domain `range R(i)`, operator
  `R(i)⁻¹ + i`); `existsUnique_selfAdjointResolventData` adds uniqueness;
* `SelfAdjointResolventData.op_eq_of_resolvent_eq`, `SelfAdjointResolventData.ext_of_resolvent`:
  the resolvent at one point determines the operator;
* `SelfAdjointResolventData.isSymmetricPseudoResolvent`, `injective_resolvent`,
  `denseRange_resolvent`: conversely the resolvent of a self-adjoint operator is an injective
  symmetric pseudo-resolvent with dense range (so injectivity is necessary, and dense range is
  automatic);
* `strongLimit`, `isSymmetricPseudoResolvent_strongLimit`: a strongly convergent sequence of
  symmetric pseudo-resolvents has a symmetric pseudo-resolvent as its strong limit (the limit
  operators are bounded by Banach–Steinhaus);
* `existsUnique_strongResolventLimit` (**pseudo-resolvent lemma**): if, moreover, the strong
  limit is injective at `z = i`, it is the resolvent of a unique self-adjoint operator, which is
  self-adjoint in Mathlib's sense, and the limit resolvents have dense range.

The stage resolvents may be degenerate (e.g. compressions `P_n (D_n - z)⁻¹ P_n` to finite screens
are not injective); only the limit is required to be injective.
-/

open Filter Topology ComplexConjugate
open scoped InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace RenewalGeometry

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A resolvent family: a bounded operator `R(z)` for every non-real `z`. -/
abbrev ResolventFamily (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  ∀ z : ℂ, z.im ≠ 0 → H →L[ℂ] H

/-- A **symmetric pseudo-resolvent**: the resolvent identity
`R(z) - R(w) = (z - w) R(z) R(w)` and the adjoint symmetry `R(z)† = R(z̄)`. -/
structure IsSymmetricPseudoResolvent (R : ResolventFamily H) : Prop where
  identity : ∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
    R z hz - R w hw = (z - w) • (R z hz * R w hw)
  adjoint : ∀ (z : ℂ) (hz : z.im ≠ 0) (hz' : (conj z).im ≠ 0),
    ContinuousLinearMap.adjoint (R z hz) = R (conj z) hz'

theorem im_I_ne_zero : (Complex.I).im ≠ 0 := by simp

theorem im_neg_I_ne_zero : (-Complex.I).im ≠ 0 := by simp

theorem im_conj_ne_zero {z : ℂ} (hz : z.im ≠ 0) : (conj z).im ≠ 0 := by simpa using hz

namespace IsSymmetricPseudoResolvent

variable {R : ResolventFamily H} (hR : IsSymmetricPseudoResolvent R)
include hR

/-- The resolvent identity applied to a vector. -/
theorem apply_sub_apply (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) (x : H) :
    R z hz x - R w hw x = (z - w) • R z hz (R w hw x) := by
  have h := congrArg (fun A : H →L[ℂ] H => A x) (hR.identity z w hz hw)
  simpa using h

/-- The adjoint symmetry, at any point equal to `z̄`. -/
theorem adjoint_eq (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) (h : w = conj z) :
    ContinuousLinearMap.adjoint (R z hz) = R w hw := by
  subst h
  exact hR.adjoint z hz hw

/-- `⟪R(z̄) x, y⟫ = ⟪x, R(z) y⟫`. -/
theorem inner_conj_apply (z : ℂ) (hz : z.im ≠ 0) (hz' : (conj z).im ≠ 0) (x y : H) :
    ⟪R (conj z) hz' x, y⟫_ℂ = ⟪x, R z hz y⟫_ℂ := by
  rw [← hR.adjoint z hz hz', ContinuousLinearMap.adjoint_inner_left]

/-- The operators of a pseudo-resolvent commute. -/
theorem commute (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    R z hz * R w hw = R w hw * R z hz := by
  by_cases h : z = w
  · subst h
    rfl
  · have h1 := hR.identity z w hz hw
    have h2 := hR.identity w z hw hz
    have hzw : z - w ≠ 0 := sub_ne_zero.mpr h
    have key : (z - w) • (R z hz * R w hw) = (z - w) • (R w hw * R z hz) := by
      rw [← h1, show z - w = -(w - z) by ring, neg_smul, ← h2]
      abel
    have := congrArg (fun A : H →L[ℂ] H => (z - w)⁻¹ • A) key
    simpa [smul_smul, inv_mul_cancel₀ hzw] using this

/-- `R(z) x = R(w) (x + (z - w) R(z) x)`: every `R(z)` factors through `R(w)`. -/
theorem apply_eq_apply_add (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) (x : H) :
    R z hz x = R w hw (x + (z - w) • R z hz x) := by
  have h := hR.apply_sub_apply w z hw hz x
  rw [map_add, map_smul]
  have : (z - w) • R w hw (R z hz x) = -((w - z) • R w hw (R z hz x)) := by
    rw [← neg_smul, neg_sub]
  rw [this, ← h]
  abel

/-- The ranges coincide: `R(z) x ∈ range R(w)`. -/
theorem apply_mem_range (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) (x : H) :
    R z hz x ∈ LinearMap.range (R w hw : H →ₗ[ℂ] H) :=
  ⟨x + (z - w) • R z hz x, (hR.apply_eq_apply_add z w hz hw x).symm⟩

/-- The kernels coincide. -/
theorem apply_eq_zero_of_apply_eq_zero (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) {x : H}
    (h : R w hw x = 0) : R z hz x = 0 := by
  have := hR.apply_sub_apply z w hz hw x
  rwa [h, map_zero, smul_zero, sub_zero] at this

/-- Injectivity at one point gives injectivity everywhere. -/
theorem injective_of_injective {w : ℂ} {hw : w.im ≠ 0} (hinj : Function.Injective (R w hw))
    (z : ℂ) (hz : z.im ≠ 0) : Function.Injective (R z hz) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  exact (injective_iff_map_eq_zero (R w hw)).1 hinj x
    (hR.apply_eq_zero_of_apply_eq_zero w z hw hz hx)

/-- `‖R(z̄) x‖ = ‖R(z) x‖` (the operators are normal). -/
theorem norm_conj_apply (z : ℂ) (hz : z.im ≠ 0) (hz' : (conj z).im ≠ 0) (x : H) :
    ‖R (conj z) hz' x‖ = ‖R z hz x‖ := by
  have hadj := hR.adjoint z hz hz'
  have hc := hR.commute z (conj z) hz hz'
  have h1 : ⟪R (conj z) hz' x, R (conj z) hz' x⟫_ℂ = ⟪x, R z hz (R (conj z) hz' x)⟫_ℂ := by
    rw [← hadj, ContinuousLinearMap.adjoint_inner_left]
  have h2 : ⟪R z hz x, R z hz x⟫_ℂ = ⟪x, R (conj z) hz' (R z hz x)⟫_ℂ := by
    rw [← hadj, ContinuousLinearMap.adjoint_inner_right]
  have h3 : R z hz (R (conj z) hz' x) = R (conj z) hz' (R z hz x) := by
    have := congrArg (fun A : H →L[ℂ] H => A x) hc
    simpa using this
  have h4 : ⟪R (conj z) hz' x, R (conj z) hz' x⟫_ℂ = ⟪R z hz x, R z hz x⟫_ℂ := by
    rw [h1, h2, h3]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h4
  have h5 : ‖R (conj z) hz' x‖ ^ 2 = ‖R z hz x‖ ^ 2 := by exact_mod_cast h4
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h5

/-- **Automatic resolvent bound** `‖R(z) x‖ ≤ |Im z|⁻¹ ‖x‖` for a symmetric pseudo-resolvent. -/
theorem norm_apply_le (z : ℂ) (hz : z.im ≠ 0) (x : H) : ‖R z hz x‖ ≤ |z.im|⁻¹ * ‖x‖ := by
  have hz' := im_conj_ne_zero hz
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  -- `⟪x, R(z) x⟫ - conj ⟪x, R(z) x⟫ = (z - z̄) ‖R(z̄) x‖²`
  have hkey : ⟪x, R z hz x⟫_ℂ - conj ⟪x, R z hz x⟫_ℂ =
      (z - conj z) * ((‖R (conj z) hz' x‖ : ℂ) ^ 2) := by
    have e1 : conj ⟪x, R z hz x⟫_ℂ = ⟪x, R (conj z) hz' x⟫_ℂ := by
      rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, hR.adjoint z hz hz']
    have e2 : ⟪x, R z hz (R (conj z) hz' x)⟫_ℂ = (‖R (conj z) hz' x‖ : ℂ) ^ 2 := by
      rw [← hR.inner_conj_apply z hz hz']
      exact inner_self_eq_norm_sq_to_K _
    rw [e1, ← inner_sub_right, hR.apply_sub_apply z (conj z) hz hz' x, inner_smul_right, e2]
  have him := congrArg Complex.im hkey
  have hBx : ((‖R (conj z) hz' x‖ : ℂ) ^ 2).im = 0 := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
  have hBre : ((‖R (conj z) hz' x‖ : ℂ) ^ 2).re = ‖R (conj z) hz' x‖ ^ 2 := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
  simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.sub_re, Complex.conj_re,
    hBx, hBre, mul_zero, zero_add] at him
  -- `Im ⟪x, R(z) x⟫ = Im z ‖R(z) x‖²`
  have hnorm : ‖R (conj z) hz' x‖ = ‖R z hz x‖ := hR.norm_conj_apply z hz hz' x
  have him' : (⟪x, R z hz x⟫_ℂ).im = z.im * ‖R z hz x‖ ^ 2 := by
    rw [← hnorm]; linarith
  have hle : |z.im| * ‖R z hz x‖ ^ 2 ≤ ‖x‖ * ‖R z hz x‖ := by
    calc |z.im| * ‖R z hz x‖ ^ 2 = |(⟪x, R z hz x⟫_ℂ).im| := by
          rw [him', abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖R z hz x‖ ^ 2)]
      _ ≤ ‖⟪x, R z hz x⟫_ℂ‖ := Complex.abs_im_le_norm _
      _ ≤ ‖x‖ * ‖R z hz x‖ := norm_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (R z hz x)) with h0 | hAx
  · rw [← h0]; positivity
  · rw [inv_mul_eq_div, le_div_iff₀ hpos]
    have : |z.im| * ‖R z hz x‖ * ‖R z hz x‖ ≤ ‖x‖ * ‖R z hz x‖ := by
      calc |z.im| * ‖R z hz x‖ * ‖R z hz x‖ = |z.im| * ‖R z hz x‖ ^ 2 := by ring
        _ ≤ _ := hle
    nlinarith

/-- **Automatic resolvent bound** `‖R(z)‖ ≤ |Im z|⁻¹`. -/
theorem norm_le (z : ℂ) (hz : z.im ≠ 0) : ‖R z hz‖ ≤ |z.im|⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (abs_nonneg _)) (hR.norm_apply_le z hz)

/-! ### The generator of an injective symmetric pseudo-resolvent -/

section Generator

variable (hinj : Function.Injective (R Complex.I im_I_ne_zero))

/-- The linear equivalence `H ≃ range R(i)`. -/
def rangeEquiv : H ≃ₗ[ℂ] LinearMap.range (R Complex.I im_I_ne_zero : H →ₗ[ℂ] H) :=
  LinearEquiv.ofInjective (R Complex.I im_I_ne_zero : H →ₗ[ℂ] H) hinj

omit hR in
theorem apply_rangeEquiv_symm (u : LinearMap.range (R Complex.I im_I_ne_zero : H →ₗ[ℂ] H)) :
    R Complex.I im_I_ne_zero ((rangeEquiv (R := R) hinj).symm u) = u :=
  LinearEquiv.ofInjective_symm_apply (f := (R Complex.I im_I_ne_zero : H →ₗ[ℂ] H)) u

omit hR in
theorem rangeEquiv_symm_eq {u : LinearMap.range (R Complex.I im_I_ne_zero : H →ₗ[ℂ] H)} {g : H}
    (h : (u : H) = R Complex.I im_I_ne_zero g) : (rangeEquiv (R := R) hinj).symm u = g := by
  apply hinj
  rw [apply_rangeEquiv_symm, h]

/-- The generator: domain `range R(i)`, `A u = R(i)⁻¹ u + i u`. -/
def generator : H →ₗ.[ℂ] H where
  domain := LinearMap.range (R Complex.I im_I_ne_zero : H →ₗ[ℂ] H)
  toFun := (rangeEquiv (R := R) hinj).symm.toLinearMap +
    Complex.I • (LinearMap.range (R Complex.I im_I_ne_zero : H →ₗ[ℂ] H)).subtype

omit hR in
theorem generator_apply (u : (generator (R := R) hinj).domain) :
    generator (R := R) hinj u = (rangeEquiv (R := R) hinj).symm u + Complex.I • (u : H) := rfl

omit hR in
theorem generator_apply_of_eq (u : (generator (R := R) hinj).domain) {g : H}
    (h : (u : H) = R Complex.I im_I_ne_zero g) :
    generator (R := R) hinj u = g + Complex.I • (u : H) := by
  rw [generator_apply, rangeEquiv_symm_eq hinj h]

/-- The generator is symmetric. -/
theorem generator_symm : (generator (R := R) hinj).IsFormalAdjoint (generator (R := R) hinj) := by
  intro x y
  set g := (rangeEquiv (R := R) hinj).symm x
  set h := (rangeEquiv (R := R) hinj).symm y
  have hx : (x : H) = R Complex.I im_I_ne_zero g := (apply_rangeEquiv_symm hinj x).symm
  have hy : (y : H) = R Complex.I im_I_ne_zero h := (apply_rangeEquiv_symm hinj y).symm
  rw [generator_apply_of_eq hinj x hx, generator_apply_of_eq hinj y hy, hx, hy]
  set a := R Complex.I im_I_ne_zero g
  set b := R Complex.I im_I_ne_zero h
  have hc : conj Complex.I = -Complex.I := Complex.conj_I
  -- `⟪g, R(i) h⟫ = ⟪R(-i) g, h⟫`
  have e1 : ⟪g, b⟫_ℂ = ⟪R (-Complex.I) im_neg_I_ne_zero g, h⟫_ℂ := by
    rw [← hR.adjoint_eq Complex.I (-Complex.I) im_I_ne_zero im_neg_I_ne_zero hc.symm,
      ContinuousLinearMap.adjoint_inner_left]
  have e2 : R (-Complex.I) im_neg_I_ne_zero g =
      a + (-Complex.I - Complex.I) • R (-Complex.I) im_neg_I_ne_zero a := by
    rw [← hR.apply_sub_apply (-Complex.I) Complex.I im_neg_I_ne_zero im_I_ne_zero g]
    abel
  have e3 : ⟪R (-Complex.I) im_neg_I_ne_zero a, h⟫_ℂ = ⟪a, b⟫_ℂ := by
    rw [← hR.adjoint_eq Complex.I (-Complex.I) im_I_ne_zero im_neg_I_ne_zero hc.symm,
      ContinuousLinearMap.adjoint_inner_left]
  rw [inner_add_left, inner_add_right, e1, e2, inner_add_left, inner_smul_left, e3,
    inner_smul_left, inner_smul_right, hc]
  simp only [map_sub, map_neg, Complex.conj_I]
  ring

theorem generator_resolvent_mem (z : ℂ) (hz : z.im ≠ 0) (f : H) :
    R z hz f ∈ (generator (R := R) hinj).domain :=
  hR.apply_mem_range z Complex.I hz im_I_ne_zero f

/-- **The pseudo-resolvent theorem.**  An injective symmetric pseudo-resolvent is the resolvent
family of a self-adjoint operator: `R(z) = (A - z)⁻¹` for the generator `A`. -/
def toSelfAdjointResolventData : SelfAdjointResolventData H where
  op := generator (R := R) hinj
  symm := hR.generator_symm hinj
  resolvent := R
  resolvent_mem := hR.generator_resolvent_mem hinj
  op_resolvent z hz f := by
    rw [generator_apply_of_eq hinj _ (hR.apply_eq_apply_add z Complex.I hz im_I_ne_zero f)]
    simp only
    rw [sub_smul]
    abel
  resolvent_op z hz u := by
    set g := (rangeEquiv (R := R) hinj).symm u
    have hu : (u : H) = R Complex.I im_I_ne_zero g := (apply_rangeEquiv_symm hinj u).symm
    rw [generator_apply_of_eq hinj u hu]
    have h := hR.apply_sub_apply z Complex.I hz im_I_ne_zero g
    rw [hu, add_sub_assoc, ← sub_smul, map_add, map_smul]
    have : (Complex.I - z) • R z hz (R Complex.I im_I_ne_zero g) =
        -((z - Complex.I) • R z hz (R Complex.I im_I_ne_zero g)) := by
      rw [← neg_smul, neg_sub]
    rw [this, ← h]
    abel

@[simp] theorem toSelfAdjointResolventData_resolvent (z : ℂ) (hz : z.im ≠ 0) :
    (hR.toSelfAdjointResolventData hinj).resolvent z hz = R z hz := rfl

end Generator

end IsSymmetricPseudoResolvent

/-! ### Uniqueness and the converse -/

namespace SelfAdjointResolventData

variable (T : SelfAdjointResolventData H)

/-- The domain is the range of any resolvent. -/
theorem mem_domain_iff {z : ℂ} (hz : z.im ≠ 0) (x : H) :
    x ∈ T.op.domain ↔ ∃ f, T.resolvent z hz f = x := by
  constructor
  · intro hx
    exact ⟨T.op ⟨x, hx⟩ - z • x, T.resolvent_op z hz ⟨x, hx⟩⟩
  · rintro ⟨f, rfl⟩
    exact T.resolvent_mem z hz f

/-- **Uniqueness**: the resolvent at one non-real point determines the operator. -/
theorem op_eq_of_resolvent_eq (T' : SelfAdjointResolventData H) {z : ℂ} (hz : z.im ≠ 0)
    (h : T.resolvent z hz = T'.resolvent z hz) : T.op = T'.op := by
  have hdom : T.op.domain = T'.op.domain := by
    ext x
    rw [T.mem_domain_iff hz, T'.mem_domain_iff hz, h]
  refine LinearPMap.ext hdom fun x hx hx' => ?_
  set f := T.op ⟨x, hx⟩ - z • x with hf
  have hxT : x = T.resolvent z hz f := T.eq_resolvent_of_op_sub hz ⟨x, hx⟩ f hf.symm
  have hxT' : x = T'.resolvent z hz f := by rw [hxT, h]
  have key : T'.op ⟨x, hx'⟩ = f + z • x := by
    have hop := T'.op_resolvent z hz f
    have hsub : (⟨x, hx'⟩ : T'.op.domain) =
        ⟨T'.resolvent z hz f, T'.resolvent_mem z hz f⟩ := Subtype.ext hxT'
    rw [hsub, eq_add_of_sub_eq hop, ← hxT']
  rw [key, hf]
  abel

/-- Two resolvent presentations with the same resolvent family are equal. -/
theorem ext_of_resolvent (T' : SelfAdjointResolventData H)
    (h : ∀ z hz, T.resolvent z hz = T'.resolvent z hz) : T = T' := by
  have hop := T.op_eq_of_resolvent_eq T' im_I_ne_zero (h _ _)
  have hres : T.resolvent = T'.resolvent := by funext z hz; exact h z hz
  cases T
  cases T'
  cases hop
  cases hres
  rfl

/-- The resolvent identity `(A - z)⁻¹ - (A - w)⁻¹ = (z - w)(A - z)⁻¹(A - w)⁻¹`. -/
theorem resolvent_identity (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    T.resolvent z hz - T.resolvent w hw = (z - w) • (T.resolvent z hz * T.resolvent w hw) := by
  ext f
  set v : T.op.domain := ⟨T.resolvent w hw f, T.resolvent_mem w hw f⟩
  have hv : T.op v - w • (v : H) = f := T.op_resolvent w hw f
  have h := T.resolvent_op z hz v
  have e : T.op v - z • (v : H) = f + (w - z) • (v : H) := by
    rw [← hv, sub_smul]; abel
  rw [e, map_add, map_smul] at h
  have hres : T.resolvent w hw f = (v : H) := rfl
  have h' := eq_sub_of_add_eq h
  show T.resolvent z hz f - T.resolvent w hw f = (z - w) • T.resolvent z hz (T.resolvent w hw f)
  rw [hres, h', show z - w = -(w - z) by ring, neg_smul]
  abel

/-- The resolvent of a self-adjoint operator is a symmetric pseudo-resolvent. -/
theorem isSymmetricPseudoResolvent : IsSymmetricPseudoResolvent T.resolvent where
  identity := T.resolvent_identity
  adjoint z hz hz' := T.adjoint_resolvent hz hz'

/-- The resolvents are injective. -/
theorem injective_resolvent {z : ℂ} (hz : z.im ≠ 0) : Function.Injective (T.resolvent z hz) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  rw [← T.op_resolvent z hz f]
  have : (⟨T.resolvent z hz f, T.resolvent_mem z hz f⟩ : T.op.domain) = 0 := Subtype.ext hf
  rw [this, LinearPMap.map_zero, hf, smul_zero, sub_zero]

/-- The resolvents have dense range (the range is the dense domain). -/
theorem denseRange_resolvent {z : ℂ} (hz : z.im ≠ 0) : DenseRange (T.resolvent z hz) := by
  have h : Set.range (T.resolvent z hz) = (T.op.domain : Set H) := by
    ext x
    rw [Set.mem_range, SetLike.mem_coe, T.mem_domain_iff hz]
  rw [DenseRange, h]
  exact T.dense_domain

end SelfAdjointResolventData

namespace IsSymmetricPseudoResolvent

variable {R : ResolventFamily H} (hR : IsSymmetricPseudoResolvent R)
include hR

/-- **Pseudo-resolvent theorem with uniqueness**: an injective symmetric pseudo-resolvent is the
resolvent family of exactly one self-adjoint operator. -/
theorem existsUnique_selfAdjointResolventData
    (hinj : Function.Injective (R Complex.I im_I_ne_zero)) :
    ∃! T : SelfAdjointResolventData H, ∀ z hz, T.resolvent z hz = R z hz :=
  ⟨hR.toSelfAdjointResolventData hinj, fun _ _ => rfl, fun T hT =>
    T.ext_of_resolvent _ fun z hz => hT z hz⟩

end IsSymmetricPseudoResolvent

/-! ### Strong limits of symmetric pseudo-resolvents -/

section StrongLimit

variable (R : ℕ → ResolventFamily H)
  (hconv : ∀ z (hz : z.im ≠ 0) x, ∃ y, Tendsto (fun n => R n z hz x) atTop (𝓝 y))

/-- The strong limit of a pointwise convergent sequence of resolvent families (bounded by the
Banach–Steinhaus theorem). -/
def strongLimit : ResolventFamily H := fun z hz =>
  continuousLinearMapOfTendsto (fun n => R n z hz)
    (f := fun x => limUnder atTop (fun n => R n z hz x))
    (tendsto_pi_nhds.2 fun x => tendsto_nhds_limUnder (hconv z hz x))

theorem tendsto_strongLimit (z : ℂ) (hz : z.im ≠ 0) (x : H) :
    Tendsto (fun n => R n z hz x) atTop (𝓝 (strongLimit R hconv z hz x)) :=
  tendsto_nhds_limUnder (hconv z hz x)

/-- A strong limit of symmetric pseudo-resolvents is a symmetric pseudo-resolvent. -/
theorem isSymmetricPseudoResolvent_strongLimit (hR : ∀ n, IsSymmetricPseudoResolvent (R n)) :
    IsSymmetricPseudoResolvent (strongLimit R hconv) where
  identity z w hz hw := by
    ext x
    have h1 : Tendsto (fun n => R n z hz x - R n w hw x) atTop (𝓝 ((strongLimit R hconv) z hz x - (strongLimit R hconv) w hw x)) :=
      (tendsto_strongLimit R hconv z hz x).sub (tendsto_strongLimit R hconv w hw x)
    -- `R_n(z) R_n(w) x → (strongLimit R hconv)(z) (strongLimit R hconv)(w) x`, using the uniform bound `‖R_n(z)‖ ≤ |Im z|⁻¹`
    have hdiff : Tendsto (fun n => R n z hz (R n w hw x) - R n z hz ((strongLimit R hconv) w hw x)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hw0 : Tendsto (fun n => ‖R n w hw x - (strongLimit R hconv) w hw x‖) atTop (𝓝 0) :=
        (tendsto_zero_iff_norm_tendsto_zero).1
          (by simpa using (tendsto_strongLimit R hconv w hw x).sub_const ((strongLimit R hconv) w hw x))
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        (by simpa using hw0.const_mul |z.im|⁻¹)
      rw [← map_sub]
      exact (hR n).norm_apply_le z hz _
    have h2 : Tendsto (fun n => R n z hz (R n w hw x)) atTop (𝓝 ((strongLimit R hconv) z hz ((strongLimit R hconv) w hw x))) := by
      have := hdiff.add (tendsto_strongLimit R hconv z hz ((strongLimit R hconv) w hw x))
      simpa using this
    have h3 : Tendsto (fun n => R n z hz x - R n w hw x) atTop
        (𝓝 ((z - w) • (strongLimit R hconv) z hz ((strongLimit R hconv) w hw x))) := by
      refine (h2.const_smul (z - w)).congr fun n => ?_
      exact ((hR n).apply_sub_apply z w hz hw x).symm
    have := tendsto_nhds_unique h1 h3
    simpa using this
  adjoint z hz hz' := by
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    have h1 : Tendsto (fun n => ⟪R n (conj z) hz' x, y⟫_ℂ) atTop (𝓝 ⟪(strongLimit R hconv) (conj z) hz' x, y⟫_ℂ) :=
      (tendsto_strongLimit R hconv _ hz' x).inner tendsto_const_nhds
    have h2 : Tendsto (fun n => ⟪x, R n z hz y⟫_ℂ) atTop (𝓝 ⟪x, (strongLimit R hconv) z hz y⟫_ℂ) :=
      tendsto_const_nhds.inner (tendsto_strongLimit R hconv z hz y)
    refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
    exact ((hR n).inner_conj_apply z hz hz' x y).symm

include hconv in
/-- **Pseudo-resolvent lemma for strong limits.**  Let `R_n` be symmetric pseudo-resolvents
(resolvent identity and adjoint symmetry; e.g. resolvents of stage operators compressed to finite
screens) converging strongly at every non-real `z`, and assume the limit is injective at `z = i`
(no vector is sent to `0` in the limit).  Then there is a unique self-adjoint operator (in the
resolvent presentation) whose resolvents are the strong limits of the `R_n(z)`; it is
self-adjoint in Mathlib's sense, and the limit resolvents are injective with dense range. -/
theorem existsUnique_strongResolventLimit (hR : ∀ n, IsSymmetricPseudoResolvent (R n))
    (hinj : ∀ x, Tendsto (fun n => R n Complex.I im_I_ne_zero x) atTop (𝓝 0) → x = 0) :
    ∃! T : SelfAdjointResolventData H,
      ∀ z hz x, Tendsto (fun n => R n z hz x) atTop (𝓝 (T.resolvent z hz x)) := by
  have hL := isSymmetricPseudoResolvent_strongLimit R hconv hR
  have hLinj : Function.Injective (strongLimit R hconv Complex.I im_I_ne_zero) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply hinj x
    simpa [hx] using tendsto_strongLimit R hconv Complex.I im_I_ne_zero x
  refine ⟨hL.toSelfAdjointResolventData hLinj, fun z hz x => tendsto_strongLimit R hconv z hz x,
    fun T hT => T.ext_of_resolvent _ fun z hz => ?_⟩
  ext x
  exact tendsto_nhds_unique (hT z hz x) (tendsto_strongLimit R hconv z hz x)

end StrongLimit

end RenewalGeometry
