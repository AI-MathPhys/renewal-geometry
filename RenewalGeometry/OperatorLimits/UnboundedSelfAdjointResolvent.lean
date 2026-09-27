/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Unbounded self-adjoint operators presented by their resolvents

Mathlib has `LinearPMap.adjoint` and `IsSelfAdjoint` for unbounded operators but no resolvent
theory for them.  This file records the surrogate used throughout the compact-spin limit theorems
of the paper `predictive_spectral_geometry` (`def:stable-spin-atlas`,
`thm:supp-compact-spin-resolvent`): a symmetric partial linear map `op` on a complex Hilbert
space together with, for every non-real `z`, a bounded two-sided inverse of `op - z`
(`SelfAdjointResolventData`).  By the standard criterion (symmetric with `op - z` surjective for
every non-real `z`) this is exactly a self-adjoint operator; the bridge to Mathlib's
`IsSelfAdjoint` for `LinearPMap` is `SelfAdjointResolventData.isSelfAdjoint_op`.

Consequences proved here:

* `abs_im_mul_norm_le`: `|Im z| ‖u‖ ≤ ‖(op - z) u‖` on the domain;
* `norm_resolvent_le`: `‖(op - z)⁻¹‖ ≤ |Im z|⁻¹` (`eq:uniform-resolvent-bounds`);
* `adjoint_resolvent`: `((op - z)⁻¹)† = (op - z̄)⁻¹`;
* `ofBounded`: every bounded self-adjoint operator on a complete space yields such data, with
  resolvent `Ring.inverse (A - z)`.
-/

open Filter Topology ComplexConjugate
open scoped InnerProductSpace

noncomputable section

namespace RenewalGeometry

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Elementary bounds for symmetric shifts -/

/-- If `⟪w, u⟫` is real then `Im ⟪w - z u, u⟫ = Im z ‖u‖²`. -/
theorem im_inner_sub_smul_self (w u : H) (z : ℂ) (hw : (⟪w, u⟫_ℂ).im = 0) :
    (⟪w - z • u, u⟫_ℂ).im = z.im * ‖u‖ ^ 2 := by
  rw [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [hw, ← Complex.ofReal_pow]

/-- The lower bound `|Im z| ‖u‖ ≤ ‖w - z u‖` whenever `⟪w, u⟫` is real. -/
theorem abs_im_mul_norm_le (w u : H) (z : ℂ) (hw : (⟪w, u⟫_ℂ).im = 0) :
    |z.im| * ‖u‖ ≤ ‖w - z • u‖ := by
  have h1 : |z.im| * ‖u‖ ^ 2 ≤ ‖w - z • u‖ * ‖u‖ := by
    calc
      |z.im| * ‖u‖ ^ 2 = |(⟪w - z • u, u⟫_ℂ).im| := by
        rw [im_inner_sub_smul_self w u z hw, abs_mul,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖u‖ ^ 2)]
      _ ≤ ‖⟪w - z • u, u⟫_ℂ‖ := Complex.abs_im_le_norm _
      _ ≤ ‖w - z • u‖ * ‖u‖ := norm_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · have : |z.im| * ‖u‖ * ‖u‖ ≤ ‖w - z • u‖ * ‖u‖ := by
      calc |z.im| * ‖u‖ * ‖u‖ = |z.im| * ‖u‖ ^ 2 := by ring
        _ ≤ ‖w - z • u‖ * ‖u‖ := h1
    exact le_of_mul_le_mul_right this hpos

/-! ### The resolvent presentation -/

/-- An unbounded self-adjoint operator on the complex Hilbert space `H`, presented by its
resolvents: a symmetric partial linear map `op` together with, for every non-real `z`, a bounded
two-sided inverse `resolvent z` of `op - z`.  Symmetry with `op - z` surjective for every non-real
`z` is the classical characterisation of self-adjointness (`isSelfAdjoint_op` below).  This is
the surrogate for the doubled Dirac operator `D̂ = D_{M,𝔰} ⊗ σ₁` on `L²(M; S ⊗ ℂ²)` of
`def:stable-spin-atlas`. -/
structure SelfAdjointResolventData (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The operator with its domain. -/
  op : H →ₗ.[ℂ] H
  /-- Symmetry: `⟪op u, v⟫ = ⟪u, op v⟫` on the domain. -/
  symm : op.IsFormalAdjoint op
  /-- The resolvent `(op - z)⁻¹` at a non-real point. -/
  resolvent : ∀ z : ℂ, z.im ≠ 0 → H →L[ℂ] H
  /-- The resolvent maps into the domain. -/
  resolvent_mem : ∀ (z : ℂ) (hz : z.im ≠ 0) (f : H), resolvent z hz f ∈ op.domain
  /-- `(op - z) (op - z)⁻¹ = 1`. -/
  op_resolvent : ∀ (z : ℂ) (hz : z.im ≠ 0) (f : H),
    op ⟨resolvent z hz f, resolvent_mem z hz f⟩ - z • resolvent z hz f = f
  /-- `(op - z)⁻¹ (op - z) = 1` on the domain. -/
  resolvent_op : ∀ (z : ℂ) (hz : z.im ≠ 0) (u : op.domain),
    resolvent z hz (op u - z • (u : H)) = u

namespace SelfAdjointResolventData

variable (T : SelfAdjointResolventData H)

/-- `⟪op u, u⟫` is real. -/
theorem im_inner_op_self (u : T.op.domain) : (⟪T.op u, (u : H)⟫_ℂ).im = 0 := by
  have h : ⟪T.op u, (u : H)⟫_ℂ = conj ⟪T.op u, (u : H)⟫_ℂ := by
    rw [inner_conj_symm]
    exact T.symm u u
  exact Complex.conj_eq_iff_im.mp h.symm

/-- `|Im z| ‖u‖ ≤ ‖(op - z) u‖` on the domain. -/
theorem abs_im_mul_norm_le_op_sub (u : T.op.domain) (z : ℂ) :
    |z.im| * ‖(u : H)‖ ≤ ‖T.op u - z • (u : H)‖ :=
  RenewalGeometry.abs_im_mul_norm_le _ _ z (T.im_inner_op_self u)

/-- `(op - z) u = f` on the domain forces `u = (op - z)⁻¹ f`. -/
theorem eq_resolvent_of_op_sub {z : ℂ} (hz : z.im ≠ 0) (u : T.op.domain) (f : H)
    (hu : T.op u - z • (u : H) = f) : (u : H) = T.resolvent z hz f := by
  rw [← hu, T.resolvent_op z hz u]

/-- Pointwise resolvent bound `‖(op - z)⁻¹ f‖ ≤ |Im z|⁻¹ ‖f‖`. -/
theorem norm_resolvent_apply_le {z : ℂ} (hz : z.im ≠ 0) (f : H) :
    ‖T.resolvent z hz f‖ ≤ |z.im|⁻¹ * ‖f‖ := by
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  have h := T.abs_im_mul_norm_le_op_sub ⟨T.resolvent z hz f, T.resolvent_mem z hz f⟩ z
  rw [T.op_resolvent z hz f] at h
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  simpa [mul_comm] using h

/-- **`eq:uniform-resolvent-bounds`.** `‖(op - z)⁻¹‖ ≤ |Im z|⁻¹`. -/
theorem norm_resolvent_le {z : ℂ} (hz : z.im ≠ 0) : ‖T.resolvent z hz‖ ≤ |z.im|⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (abs_nonneg _))
    fun f => T.norm_resolvent_apply_le hz f

/-- The imaginary part of the conjugate is nonzero. -/
theorem conj_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : (conj z).im ≠ 0 := by
  simpa using hz

/-- The adjoint of the resolvent at `z` is the resolvent at `z̄`. -/
theorem adjoint_resolvent [CompleteSpace H] {z : ℂ} (hz : z.im ≠ 0) (hz' : (conj z).im ≠ 0) :
    ContinuousLinearMap.adjoint (T.resolvent z hz) = T.resolvent (conj z) hz' := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  set u : T.op.domain := ⟨T.resolvent (conj z) hz' x, T.resolvent_mem _ hz' x⟩
  set v : T.op.domain := ⟨T.resolvent z hz y, T.resolvent_mem _ hz y⟩
  have hx : T.op u - (conj z) • (u : H) = x := T.op_resolvent _ hz' x
  have hy : T.op v - z • (v : H) = y := T.op_resolvent _ hz y
  change ⟪(u : H), y⟫_ℂ = ⟪x, (v : H)⟫_ℂ
  rw [← hx, ← hy, inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left,
    Complex.conj_conj, T.symm u v]

/-- The domain is dense: a vector orthogonal to the domain vanishes, because `op + i` is
surjective and `op - i` pairs it away. -/
theorem dense_domain [CompleteSpace H] : Dense (T.op.domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have hi : (Complex.I).im ≠ 0 := by simp
  have hI' : (-Complex.I).im ≠ 0 := by simp
  set v : T.op.domain := ⟨T.resolvent (-Complex.I) hI' g, T.resolvent_mem _ hI' g⟩
  have hv : T.op v - (-Complex.I) • (v : H) = g := T.op_resolvent _ hI' g
  have hpair : ∀ f : H, ⟪f, (v : H)⟫_ℂ = 0 := by
    intro f
    set u : T.op.domain := ⟨T.resolvent Complex.I hi f, T.resolvent_mem _ hi f⟩
    have hu : T.op u - Complex.I • (u : H) = f := T.op_resolvent _ hi f
    calc ⟪f, (v : H)⟫_ℂ = ⟪T.op u - Complex.I • (u : H), (v : H)⟫_ℂ := by rw [hu]
      _ = ⟪(u : H), T.op v⟫_ℂ - conj Complex.I * ⟪(u : H), (v : H)⟫_ℂ := by
        rw [inner_sub_left, inner_smul_left, T.symm u v]
      _ = ⟪(u : H), T.op v - (-Complex.I) • (v : H)⟫_ℂ := by
        rw [inner_sub_right, inner_smul_right]
        simp
      _ = 0 := by rw [hv]; exact hg _ u.2
  have hv0 : (v : H) = 0 := inner_self_eq_zero.mp (hpair v)
  have : g = T.op v - (-Complex.I) • (v : H) := hv.symm
  rw [this]
  have hvz : v = 0 := Subtype.ext hv0
  rw [hvz]
  simp

/-- **Bridge to Mathlib.** The partial operator `op` is self-adjoint in the sense of
`LinearPMap.adjoint`: it is symmetric, and surjectivity of `op + i` identifies the adjoint
domain with the domain. -/
theorem isSelfAdjoint_op [CompleteSpace H] : IsSelfAdjoint T.op := by
  have hdense := T.dense_domain
  have hle : T.op ≤ LinearPMap.adjoint T.op :=
    LinearPMap.IsFormalAdjoint.le_adjoint hdense T.symm
  have hadj := LinearPMap.adjoint_isFormalAdjoint (T := T.op) hdense
  rw [LinearPMap.isSelfAdjoint_def]
  symm
  apply LinearPMap.eq_of_le_of_domain_eq hle
  apply le_antisymm hle.1
  intro y hy
  have hi : (Complex.I).im ≠ 0 := by simp
  have hI' : (-Complex.I).im ≠ 0 := by simp
  set w : H := LinearPMap.adjoint T.op ⟨y, hy⟩
  have hw : ∀ x : T.op.domain, ⟪w, (x : H)⟫_ℂ = ⟪y, T.op x⟫_ℂ := fun x => hadj ⟨y, hy⟩ x
  set v : T.op.domain := ⟨T.resolvent Complex.I hi (w - Complex.I • y),
    T.resolvent_mem _ hi _⟩
  have hv : T.op v - Complex.I • (v : H) = w - Complex.I • y := T.op_resolvent _ hi _
  have hpair : ∀ f : H, ⟪y - (v : H), f⟫_ℂ = 0 := by
    intro f
    set x : T.op.domain := ⟨T.resolvent (-Complex.I) hI' f, T.resolvent_mem _ hI' f⟩
    have hx : T.op x - (-Complex.I) • (x : H) = f := T.op_resolvent _ hI' f
    have hwv : w - T.op v = Complex.I • (y - (v : H)) := by
      have h1 : T.op v = w - Complex.I • y + Complex.I • (v : H) := by
        rw [← hv]; abel
      rw [h1, smul_sub]; abel
    calc ⟪y - (v : H), f⟫_ℂ = ⟪y - (v : H), T.op x - (-Complex.I) • (x : H)⟫_ℂ := by rw [hx]
      _ = ⟪y, T.op x⟫_ℂ - ⟪(v : H), T.op x⟫_ℂ + Complex.I * ⟪y - (v : H), (x : H)⟫_ℂ := by
        rw [inner_sub_right, inner_sub_left, inner_smul_right]
        simp only [neg_mul]
        ring
      _ = ⟪w - T.op v, (x : H)⟫_ℂ + Complex.I * ⟪y - (v : H), (x : H)⟫_ℂ := by
        rw [← hw x, ← T.symm v x, inner_sub_left (w) (T.op v) (x : H)]
      _ = conj Complex.I * ⟪y - (v : H), (x : H)⟫_ℂ
            + Complex.I * ⟪y - (v : H), (x : H)⟫_ℂ := by
        rw [hwv, inner_smul_left]
      _ = 0 := by simp
  have h0 : y - (v : H) = 0 := inner_self_eq_zero.mp (hpair _)
  have : y = (v : H) := sub_eq_zero.mp h0
  rw [this]
  exact v.2

/-! ### Bounded self-adjoint operators -/

section ofBounded

/-- The shifted operator `A - z`. -/
def shifted (A : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H := A - z • (1 : H →L[ℂ] H)

@[simp] theorem shifted_apply (A : H →L[ℂ] H) (z : ℂ) (x : H) :
    shifted A z x = A x - z • x := by
  simp [shifted]

variable [CompleteSpace H]

/-- `⟪A x, x⟫` is real for a self-adjoint bounded operator. -/
theorem im_inner_apply_self_of_isSelfAdjoint {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (x : H) :
    (⟪A x, x⟫_ℂ).im = 0 := by
  have h : ⟪A x, x⟫_ℂ = conj ⟪A x, x⟫_ℂ := by
    rw [inner_conj_symm]
    exact hA.isSymmetric x x
  exact Complex.conj_eq_iff_im.mp h.symm

/-- `A - z` is invertible for non-real `z` and bounded self-adjoint `A`. -/
theorem isUnit_shifted {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (shifted A z) := by
  have hpos : (0 : ℝ) < |z.im| := abs_pos.mpr hz
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map (shifted A z)
    (c := ⟨|z.im|, abs_nonneg _⟩) (by exact_mod_cast hpos)
  intro x
  change ‖x‖ ^ 2 * |z.im| ≤ ‖⟪shifted A z x, x⟫_ℂ‖
  calc ‖x‖ ^ 2 * |z.im| = |(⟪shifted A z x, x⟫_ℂ).im| := by
        rw [shifted_apply, im_inner_sub_smul_self _ _ _ (im_inner_apply_self_of_isSelfAdjoint hA x),
          abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2)]
        ring
    _ ≤ ‖⟪shifted A z x, x⟫_ℂ‖ := Complex.abs_im_le_norm _

/-- A bounded self-adjoint operator on a Hilbert space, as resolvent data with domain `⊤`
and resolvent `Ring.inverse (A - z)`.  This packages the finite stage operators `D_h` of
`def:stable-spin-atlas`. -/
def ofBounded (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) : SelfAdjointResolventData H where
  op := (A : H →ₗ[ℂ] H).toPMap ⊤
  symm := fun x y => hA.isSymmetric x y
  resolvent z _ := Ring.inverse (shifted A z)
  resolvent_mem _ _ _ := Submodule.mem_top
  op_resolvent z hz f := by
    change A (Ring.inverse (shifted A z) f) - z • Ring.inverse (shifted A z) f = f
    rw [← shifted_apply, ← mul_apply_eq_comp,
      Ring.mul_inverse_cancel _ (isUnit_shifted hA hz), one_apply_eq_self]
  resolvent_op z hz u := by
    change Ring.inverse (shifted A z) (A u - z • (u : H)) = u
    rw [← shifted_apply, ← mul_apply_eq_comp,
      Ring.inverse_mul_cancel _ (isUnit_shifted hA hz), one_apply_eq_self]

@[simp] theorem ofBounded_op_apply (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (u : (ofBounded A hA).op.domain) : (ofBounded A hA).op u = A u := rfl

theorem ofBounded_domain (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    (ofBounded A hA).op.domain = ⊤ := rfl

/-- `(A - z) (A - z)⁻¹ f = f`. -/
theorem ofBounded_apply_resolvent (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (f : H) :
    A ((ofBounded A hA).resolvent z hz f) - z • (ofBounded A hA).resolvent z hz f = f :=
  (ofBounded A hA).op_resolvent z hz f

/-- `(A - z)⁻¹ (A x - z x) = x`. -/
theorem ofBounded_resolvent_apply_sub (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (x : H) :
    (ofBounded A hA).resolvent z hz (A x - z • x) = x :=
  (ofBounded A hA).resolvent_op z hz ⟨x, Submodule.mem_top⟩

end ofBounded

end SelfAdjointResolventData

end RenewalGeometry
