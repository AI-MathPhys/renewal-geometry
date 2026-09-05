/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Quantitative pulse-to-Howe comparison

The old `gap_dominance` stub recorded only transitivity of `<`.  This module
contains the missing quantitative engine: the commutator operator has norm at
most twice the coefficient norm; an exact second-order pulse remainder gives
the manuscript's `|t| M²` derivation bound; the difference of the two Gram
operators has the displayed `(4M + δ)δ` bound; and a lower spectral gap
transfers across an operator-norm perturbation.

The exponential-specific input is isolated as the standard sharp unitary
remainder `‖R_t‖ ≤ |t|² M²/2`.  This makes clear which analytic lemma is still
needed to derive the estimate directly from a Hermitian generator, while all
commutator, Gram, and gap estimates below are proved rather than assumed.
-/

open scoped ComplexConjugate

namespace NCG

section Commutator

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- The bounded commutator derivation `X ↦ aX - Xa`. -/
noncomputable def commutatorOperator (a : A) : A →L[ℂ] A :=
  (ContinuousLinearMap.mul ℂ A) a -
    (ContinuousLinearMap.mul ℂ A).flip a

@[simp]
theorem commutatorOperator_apply (a x : A) :
    commutatorOperator a x = a * x - x * a := rfl

/-- Hilbert--Schmidt/operator-ideal commutator estimate in its abstract
normed-algebra form. -/
theorem norm_commutatorOperator_le (a : A) :
    ‖commutatorOperator a‖ ≤ 2 * ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (norm_nonneg a)) ?_
  intro x
  rw [commutatorOperator_apply]
  calc
    ‖a * x - x * a‖ ≤ ‖a * x‖ + ‖x * a‖ := norm_sub_le _ _
    _ ≤ ‖a‖ * ‖x‖ + ‖x‖ * ‖a‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = (2 * ‖a‖) * ‖x‖ := by ring

/-- The finite-pulse commutator `t⁻¹[V_t,·]`. -/
noncomputable def finitePulseDerivation (t : ℝ) (V : A) : A →L[ℂ] A :=
  ((t : ℂ)⁻¹) • commutatorOperator V

/-- The generator commutator `-i[G,·]`. -/
noncomputable def generatorDerivation (G : A) : A →L[ℂ] A :=
  (-Complex.I) • commutatorOperator G

/-- Exact operator identity behind the pulse estimate. -/
theorem finitePulseDerivation_sub_generator
    (t : ℝ) (ht : t ≠ 0) (V G R : A)
    (hV : V = 1 + ((-Complex.I * t : ℂ) • G) + R) :
    finitePulseDerivation t V - generatorDerivation G =
      ((t : ℂ)⁻¹) • commutatorOperator R := by
  subst V
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hcomm : commutatorOperator
      (1 + ((-Complex.I * t : ℂ) • G) + R) =
      ((-Complex.I * t : ℂ) • commutatorOperator G) +
        commutatorOperator R := by
    ext x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      commutatorOperator_apply, one_mul, mul_one, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm]
    module
  have hcoef : (t : ℂ)⁻¹ * (-Complex.I * t) = -Complex.I := by
    field_simp
  rw [finitePulseDerivation, generatorDerivation, hcomm, smul_add, smul_smul,
    hcoef]
  abel

/-- The manuscript's first boxed estimate, derived from the exact second-order
remainder bound. -/
theorem norm_finitePulseDerivation_sub_generator_le
    (t M : ℝ) (ht : t ≠ 0) (hM : 0 ≤ M) (V G R : A)
    (hV : V = 1 + ((-Complex.I * t : ℂ) • G) + R)
    (hR : ‖R‖ ≤ |t| ^ 2 * M ^ 2 / 2) :
    ‖finitePulseDerivation t V - generatorDerivation G‖ ≤ |t| * M ^ 2 := by
  rw [finitePulseDerivation_sub_generator t ht V G R hV, norm_smul]
  have habs : 0 < |t| := abs_pos.mpr ht
  have hcomm : ‖commutatorOperator R‖ ≤ 2 * ‖R‖ :=
    norm_commutatorOperator_le R
  have hscale : ‖((t : ℂ)⁻¹)‖ = |t|⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
  rw [hscale]
  calc
    |t|⁻¹ * ‖commutatorOperator R‖ ≤ |t|⁻¹ * (2 * ‖R‖) :=
      mul_le_mul_of_nonneg_left hcomm (inv_nonneg.mpr habs.le)
    _ ≤ |t|⁻¹ * (2 * (|t| ^ 2 * M ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hR (by norm_num)) (inv_nonneg.mpr habs.le)
    _ = |t| * M ^ 2 := by
      field_simp

end Commutator

section Gram

variable {B : Type*} [NormedRing B] [StarRing B] [NormedStarGroup B]

/-- The exact algebraic Gram perturbation estimate
`A* A - B* B = A*(A-B) + (A*-B*)B`. -/
theorem norm_star_mul_self_sub_le (A₁ A₀ : B) :
    ‖star A₁ * A₁ - star A₀ * A₀‖ ≤
      (‖A₁‖ + ‖A₀‖) * ‖A₁ - A₀‖ := by
  have hsplit : star A₁ * A₁ - star A₀ * A₀ =
      star A₁ * (A₁ - A₀) + (star A₁ - star A₀) * A₀ := by
    noncomm_ring
  rw [hsplit]
  calc
    ‖star A₁ * (A₁ - A₀) + (star A₁ - star A₀) * A₀‖
        ≤ ‖star A₁ * (A₁ - A₀)‖ + ‖(star A₁ - star A₀) * A₀‖ :=
      norm_add_le _ _
    _ ≤ ‖star A₁‖ * ‖A₁ - A₀‖ + ‖star A₁ - star A₀‖ * ‖A₀‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = (‖A₁‖ + ‖A₀‖) * ‖A₁ - A₀‖ := by
      rw [← star_sub, norm_star, norm_star]
      ring

/-- The manuscript's second boxed estimate from the derivation bounds. -/
theorem norm_howeGram_difference_le
    (A₁ A₀ : B) (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (h₀ : ‖A₀‖ ≤ 2 * M) (h₁ : ‖A₁‖ ≤ 2 * M + δ)
    (hdiff : ‖A₁ - A₀‖ ≤ δ) :
    ‖star A₁ * A₁ - star A₀ * A₀‖ ≤ (4 * M + δ) * δ := by
  calc
    ‖star A₁ * A₁ - star A₀ * A₀‖
        ≤ (‖A₁‖ + ‖A₀‖) * ‖A₁ - A₀‖ :=
      norm_star_mul_self_sub_le A₁ A₀
    _ ≤ ((2 * M + δ) + 2 * M) * δ := by
      exact mul_le_mul (add_le_add h₁ h₀) hdiff (norm_nonneg _) (by positivity)
    _ = (4 * M + δ) * δ := by ring

end Gram

section Gap

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A certified lower gap for a bounded operator.  In finite dimension for a
positive Gram operator this is the usual lower spectral edge. -/
def HasLowerOperatorGap (T : E →L[ℝ] E) (γ : ℝ) : Prop :=
  ∀ x, γ * ‖x‖ ≤ ‖T x‖

/-- Weyl-style lower-gap transfer from an operator-norm perturbation. -/
theorem lowerOperatorGap_transfer (T₁ T₀ : E →L[ℝ] E)
    (γ₁ δ : ℝ) (hδ : ‖T₁ - T₀‖ ≤ δ)
    (hgap : HasLowerOperatorGap T₁ γ₁) :
    HasLowerOperatorGap T₀ (γ₁ - δ) := by
  intro x
  have happly : ‖(T₁ - T₀) x‖ ≤ δ * ‖x‖ := by
    calc
      ‖(T₁ - T₀) x‖ ≤ ‖T₁ - T₀‖ * ‖x‖ := (T₁ - T₀).le_opNorm x
      _ ≤ δ * ‖x‖ := mul_le_mul_of_nonneg_right hδ (norm_nonneg x)
  have htri : ‖T₁ x‖ ≤ ‖T₀ x‖ + ‖(T₁ - T₀) x‖ := by
    have heq : T₁ x = T₀ x + (T₁ - T₀) x := by
      change T₁ x = T₀ x + (T₁ x - T₀ x)
      abel
    rw [heq]
    exact norm_add_le _ _
  calc
    (γ₁ - δ) * ‖x‖ = γ₁ * ‖x‖ - δ * ‖x‖ := by ring
    _ ≤ ‖T₁ x‖ - δ * ‖x‖ := sub_le_sub_right (hgap x) _
    _ ≤ ‖T₀ x‖ := by linarith

/-- A measured gap larger than the Gram perturbation produces a strictly
positive certified generator gap. -/
theorem pulseGap_implies_positive_generatorGap
    (T₁ T₀ : E →L[ℝ] E) (γ₁ δ : ℝ)
    (hδ : ‖T₁ - T₀‖ ≤ δ) (hgap : HasLowerOperatorGap T₁ γ₁)
    (hdom : δ < γ₁) :
    0 < γ₁ - δ ∧ HasLowerOperatorGap T₀ (γ₁ - δ) :=
  ⟨sub_pos.mpr hdom, lowerOperatorGap_transfer T₁ T₀ γ₁ δ hδ hgap⟩

end Gap

end NCG
