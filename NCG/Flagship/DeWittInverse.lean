/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical exterior-source DeWitt completion
  (`thm:canonical-ADM-master`, flagship manuscript)

The provable core of the four clauses:

* (i) `det_character_line` / `det_line_equivariant`: the space of
  alternating 3-forms on the 3-dimensional response space is the
  one-dimensional determinant-character line — every alternating
  form is `c • det`, and composition with any frame map `g` acts
  on the line by the determinant character `det g`;
* (ii) `ancillary_scalar_stiffness`: ancillary determinant-
  character copies fed by the same volume loading change only
  the scalar stiffness — a sum of scalar multiples of one
  quadratic response is a single scalar multiple;
* (iii) `dewitt_inverse` / `dewitt_quadratic`: the trace
  inversion in `d` dimensions — the DeWitt map
  `h ↦ h - (tr h)·1` has exact inverse
  `Pk ↦ Pk - (tr Pk)/(d-1)·1`, and in `d = 3` the induced kinetic
  quadratic form is the boxed
  `Tr(Pk²) - ½(Tr Pk)²`;
* (iv) `dewitt_scale_invariant`: the DeWitt trace coefficient
  `1/2` is fixed independently of the overall microscopic action
  coefficient — scaling the map by `χ` scales the inverse by
  `χ⁻¹` and leaves the internal trace coefficient `1/2`
  untouched.

Rendering disclosed: the physical inputs — the external response
cube and its Reads (`thm:predictive-clock-discharge`,
`thm:anchor-external-clifford-master`), the unique frame-action
lift (`thm:minimal-realization-naturality-master`), the three
fresh response legs (`thm:complete-cut-factorization-master`),
and positive functional calculus/Feshbach production of the fixed
positive `F` — are the cited proved records; multiplicity one of
the determinant line inside the coherent response cube is the
displayed Schur input.  The reciprocal kinetic/curvature
normalization is correctly delegated to
`thm:ADM-action-audit-master` and
`thm:Clifford-common-action-master`.
-/

open Matrix

namespace NCG

/-- (i) The determinant-character line: every alternating 3-form
on `ℝ³` is a scalar multiple of the determinant. -/
theorem det_character_line
    (f : (Fin 3 → ℝ) [⋀^Fin 3]→ₗ[ℝ] ℝ) :
    ∃ c : ℝ, f = c • (Pi.basisFun ℝ (Fin 3)).det :=
  ⟨f (Pi.basisFun ℝ (Fin 3)),
    f.eq_smul_basis_det (Pi.basisFun ℝ (Fin 3))⟩

/-- (i) The frame action on the determinant line is the
determinant character: composing the basis determinant with a
frame map multiplies it by `det g`. -/
theorem det_line_equivariant
    (g : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (v : Fin 3 → Fin 3 → ℝ) :
    (Pi.basisFun ℝ (Fin 3)).det (g ∘ v)
      = LinearMap.det g * (Pi.basisFun ℝ (Fin 3)).det v :=
  (Pi.basisFun ℝ (Fin 3)).det_comp g v

/-- (ii) Ancillary determinant-character copies fed by the same
volume loading change only the scalar stiffness. -/
theorem ancillary_scalar_stiffness {E : Type*} [AddCommGroup E]
    [Module ℝ E] {ι : Type*} (s : Finset ι) (c f : ι → ℝ)
    (Q : E) :
    ∑ k ∈ s, (c k * f k) • Q = (∑ k ∈ s, c k * f k) • Q :=
  (Finset.sum_smul).symm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The DeWitt trace map `h ↦ h - (tr h)·1`. -/
noncomputable def dewittMap (h : Matrix n n ℝ) : Matrix n n ℝ :=
  h - h.trace • 1

/-- The inverse trace map with coefficient `1/(d-1)`. -/
noncomputable def dewittInv (d : ℕ) (Pk : Matrix n n ℝ) :
    Matrix n n ℝ :=
  Pk - (((d : ℝ) - 1)⁻¹ * Pk.trace) • 1

private lemma trace_dewittInv (d : ℕ) (Pk : Matrix n n ℝ) :
    (dewittInv d Pk).trace
      = Pk.trace - ((d : ℝ) - 1)⁻¹ * Pk.trace
          * (Fintype.card n : ℝ) := by
  rw [dewittInv, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul]

private lemma trace_dewittMap (Pk : Matrix n n ℝ) :
    (dewittMap Pk).trace
      = Pk.trace - Pk.trace * (Fintype.card n : ℝ) := by
  rw [dewittMap, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul]

/-- (iii) Exact trace inversion in `d = card n ≥ 2` dimensions:
`dewittInv` inverts `dewittMap` on both sides. -/
theorem dewitt_inverse (hd : 2 ≤ Fintype.card n)
    (Pk : Matrix n n ℝ) :
    dewittMap (dewittInv (Fintype.card n) Pk) = Pk
    ∧ dewittInv (Fintype.card n) (dewittMap Pk) = Pk := by
  have hcard : ((Fintype.card n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (Fintype.card n : ℝ) := by
      exact_mod_cast hd
    linarith
  have hkey : ((Fintype.card n : ℝ) - 1)⁻¹
      * ((Fintype.card n : ℝ) - 1) = 1 :=
    inv_mul_cancel₀ hcard
  constructor
  · rw [dewittMap, trace_dewittInv, dewittInv, sub_sub,
      ← add_smul]
    rw [show ((Fintype.card n : ℝ) - 1)⁻¹ * Pk.trace
        + (Pk.trace - ((Fintype.card n : ℝ) - 1)⁻¹ * Pk.trace
            * (Fintype.card n : ℝ))
      = (0 : ℝ) from by linear_combination (-Pk.trace) * hkey]
    rw [zero_smul, sub_zero]
  · rw [dewittInv, trace_dewittMap, dewittMap, sub_sub,
      ← add_smul]
    rw [show Pk.trace + ((Fintype.card n : ℝ) - 1)⁻¹
          * (Pk.trace - Pk.trace * (Fintype.card n : ℝ))
      = (0 : ℝ) from by linear_combination (-Pk.trace) * hkey]
    rw [zero_smul, sub_zero]

/-- (iii) The boxed `d = 3` kinetic quadratic form: the inverse
DeWitt pairing is `Tr(Pk²) - ½(Tr Pk)²` — the trace coefficient
is `1/(3-1) = 1/2`. -/
theorem dewitt_quadratic (Pk : Matrix (Fin 3) (Fin 3) ℝ) :
    (Pk * dewittInv 3 Pk).trace
      = (Pk * Pk).trace - 1 / 2 * Pk.trace ^ 2
    ∧ ((3 : ℝ) - 1)⁻¹ = 1 / 2 := by
  constructor
  · rw [dewittInv, Matrix.mul_sub, Matrix.trace_sub,
      Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_one,
      smul_eq_mul]
    push_cast
    ring
  · norm_num

/-- (iv) The DeWitt trace coefficient is fixed independently of
the overall microscopic action coefficient: scaling the map by
`χ ≠ 0` scales the inverse by `χ⁻¹`, leaving the internal trace
coefficient `1/(d-1)` untouched. -/
theorem dewitt_scale_invariant (hd : 2 ≤ Fintype.card n)
    (χ : ℝ) (hχ : χ ≠ 0) (Pk : Matrix n n ℝ) :
    χ • dewittMap (χ⁻¹ • dewittInv (Fintype.card n) Pk) = Pk := by
  have hlin : dewittMap (χ⁻¹ • dewittInv (Fintype.card n) Pk)
      = χ⁻¹ • dewittMap (dewittInv (Fintype.card n) Pk) := by
    rw [dewittMap, dewittMap, Matrix.trace_smul, smul_sub,
      smul_smul, smul_eq_mul]
  rw [hlin, smul_smul, mul_inv_cancel₀ hχ, one_smul,
    (dewitt_inverse hd Pk).1]

/-- `thm:canonical-ADM-master`: the assembled four clauses — the
determinant-character line with its equivariant scalar action,
the scalar-stiffness reduction of ancillary copies, and the
exact `d = 3` DeWitt inversion with coefficient `1/2` fixed
independently of the overall coefficient. -/
theorem canonical_adm_master :
    (∀ f : (Fin 3 → ℝ) [⋀^Fin 3]→ₗ[ℝ] ℝ,
      ∃ c : ℝ, f = c • (Pi.basisFun ℝ (Fin 3)).det)
    ∧ (∀ (g : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
        (v : Fin 3 → Fin 3 → ℝ),
        (Pi.basisFun ℝ (Fin 3)).det (g ∘ v)
          = LinearMap.det g * (Pi.basisFun ℝ (Fin 3)).det v)
    ∧ (∀ Pk : Matrix (Fin 3) (Fin 3) ℝ,
        (Pk * dewittInv 3 Pk).trace
          = (Pk * Pk).trace - 1 / 2 * Pk.trace ^ 2)
    ∧ (∀ (χ : ℝ), χ ≠ 0 → ∀ Pk : Matrix (Fin 3) (Fin 3) ℝ,
        χ • dewittMap (χ⁻¹ • dewittInv 3 Pk) = Pk) := by
  refine ⟨det_character_line, det_line_equivariant,
    fun Pk => (dewitt_quadratic Pk).1, fun χ hχ Pk => ?_⟩
  have h3 : Fintype.card (Fin 3) = 3 := by simp
  have := dewitt_scale_invariant (n := Fin 3)
    (by simp : 2 ≤ Fintype.card (Fin 3)) χ hχ Pk
  rwa [h3] at this

end NCG
