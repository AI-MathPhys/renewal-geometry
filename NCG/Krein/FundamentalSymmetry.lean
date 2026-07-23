/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Krein fundamental symmetries and the positivity obstruction

A **fundamental symmetry** on a complex Hilbert space `H` is a self-adjoint
involution `J = J⋆`, `J² = 1`.  It defines the **Krein form**
`[x, y]_J = ⟪x, J y⟫`, turning `H` into a Krein space whose signature is
the pair of eigenspaces of `J` (manuscript, Definition `def:J-eps`,
Proposition `prop:krein-datum`).

The central structural fact of the manuscript's positive sector is the
**positivity obstruction** (Lemma `lem:fundamental-symmetry`, Corollary
`cor:positivity-obstruction`): a fundamental symmetry whose Krein form is
positive semidefinite is the identity — positive data cannot carry a
nontrivial (indefinite, Lorentzian) signature.  Signature must therefore
come from the *signed* sector (`NCG.Graph.SignedCover`,
`NCG.Krein.CoverModel`).

## Main definitions

* `NCG.IsFundamentalSymmetry` — self-adjoint involutions;
* `NCG.kreinForm` — the indefinite form `[x, y]_J = ⟪x, J y⟫`;
* `NCG.IsKreinSelfAdjoint` — Krein self-adjointness `J T⋆ J = T`.

## Main results

* `NCG.IsFundamentalSymmetry.eq_one_of_krein_nonneg` — the positivity
  obstruction (Lemma `lem:fundamental-symmetry`): a positive fundamental
  symmetry is `1`;
* `NCG.isKreinSelfAdjoint_iff` — `T` is Krein self-adjoint iff `J * T` is
  self-adjoint, the standard bridge between Krein and Hilbert theory. -/

namespace NCG

open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A **fundamental symmetry**: a self-adjoint involution `J = J⋆`,
`J² = 1` (Definition `def:J-eps`). -/
structure IsFundamentalSymmetry (J : H →L[ℂ] H) : Prop where
  isSelfAdjoint : IsSelfAdjoint J
  mul_self : J * J = 1

namespace IsFundamentalSymmetry

variable {J : H →L[ℂ] H}

theorem apply_apply (hJ : IsFundamentalSymmetry J) (x : H) : J (J x) = x := by
  have h := congrArg (fun T : H →L[ℂ] H => T x) hJ.mul_self
  simpa [ContinuousLinearMap.mul_apply] using h

/-- A fundamental symmetry is a unitary involution; in particular it is
injective. -/
theorem injective (hJ : IsFundamentalSymmetry J) : Function.Injective J := by
  intro x y h
  have h' := congrArg J h
  rwa [hJ.apply_apply, hJ.apply_apply] at h'

end IsFundamentalSymmetry

/-- The **Krein form** `[x, y]_J = ⟪x, J y⟫` associated with `J`
(Proposition `prop:krein-datum`). -/
noncomputable def kreinForm (J : H →L[ℂ] H) (x y : H) : ℂ := ⟪x, J y⟫

theorem kreinForm_def (J : H →L[ℂ] H) (x y : H) :
    kreinForm J x y = ⟪x, J y⟫ := rfl

/-- **The positivity obstruction** (Lemma `lem:fundamental-symmetry`,
Corollary `cor:positivity-obstruction`): a fundamental symmetry whose Krein
form is positive semidefinite is the identity.  Hence a genuinely indefinite
(Krein/Lorentzian) form requires both eigenspaces of `J` to be nonzero, and
positive completely positive data — which produce positive forms — cannot
canonically supply a nontrivial fundamental symmetry. -/
theorem IsFundamentalSymmetry.eq_one_of_krein_nonneg {J : H →L[ℂ] H}
    (hJ : IsFundamentalSymmetry J)
    (hpos : ∀ x : H, 0 ≤ (kreinForm J x x).re) : J = 1 := by
  ext x
  -- Consider `z = x - J x`; it satisfies `J z = -z`.
  set z := x - J x with hzdef
  have hJz : J z = -z := by
    simp only [hzdef, map_sub, hJ.apply_apply]
    abel
  -- The Krein form is `-‖z‖²` on `z`, so positivity forces `z = 0`.
  have hform : (kreinForm J z z).re = -(‖z‖ ^ 2) := by
    rw [kreinForm_def, hJz, inner_neg_right, inner_self_eq_norm_sq_to_K,
      RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.neg_re,
      Complex.ofReal_re]
  have hge := hpos z
  rw [hform] at hge
  have hz : z = 0 := by
    have hn : ‖z‖ ^ 2 ≤ 0 := by linarith
    have hnorm : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
    exact norm_eq_zero.mp hnorm
  have hx : J x = x := by
    have h' := sub_eq_zero.mp (hzdef ▸ hz)
    exact h'.symm
  simpa using hx

/-- `T` is **Krein self-adjoint** with respect to `J` when `J T⋆ J = T`
(the condition on the bounded perturbation `B` in the signed modular Dirac
`D_χ = J_χ e^{βN} + B`, Definition `def:signed-modular-twist`). -/
def IsKreinSelfAdjoint (J T : H →L[ℂ] H) : Prop :=
  J * star T * J = T

/-- Krein self-adjointness with respect to a fundamental symmetry `J` is
equivalent to ordinary self-adjointness of `J * T`.  This is the standard
mechanism by which Krein-self-adjoint operators are analyzed through
Hilbert-space theory (used for `D_χ = J e^{βN} + B` in Theorem
`thm:signed-dirac`). -/
theorem isKreinSelfAdjoint_iff {J T : H →L[ℂ] H}
    (hJ : IsFundamentalSymmetry J) :
    IsKreinSelfAdjoint J T ↔ IsSelfAdjoint (J * T) := by
  have hstar : star J = J := hJ.isSelfAdjoint
  constructor
  · intro h
    show star (J * T) = J * T
    rw [star_mul, hstar]
    -- from `J T⋆ J = T`: multiply by `J` on the left
    have h' : J * (J * star T * J) = J * T := by rw [h]
    calc star T * J = 1 * (star T * J) := by rw [one_mul]
      _ = (J * J) * (star T * J) := by rw [hJ.mul_self]
      _ = J * (J * star T * J) := by simp only [mul_assoc]
      _ = J * T := h'
  · intro h
    have h' : star T * J = J * T := by
      have hs := h.star_eq
      rwa [star_mul, hstar] at hs
    show J * star T * J = T
    calc J * star T * J = J * (star T * J) := by rw [mul_assoc]
      _ = J * (J * T) := by rw [h']
      _ = (J * J) * T := by rw [mul_assoc]
      _ = T := by rw [hJ.mul_self, one_mul]

end NCG
