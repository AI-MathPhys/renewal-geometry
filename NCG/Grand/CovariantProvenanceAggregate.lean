/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompletionAggregateInversion
import NCG.Grand.WardCurrentScalars

/-!
# Covariant scalar provenance aggregate

This module specializes completion aggregation to the standard centered
four-entry provenance triplet.  A scalar channel is manifestly permutation
covariant; its geometric dwell aggregate is the manuscript's Möbius transform,
with the exact inverse and the quadratic-Gram sign ambiguity.
-/

namespace NCG

open Matrix

/-- Permutation action on four-entry provenance coefficients. -/
def permuteProvenance (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun i => v (σ.symm i)

/-- The centered standard-triplet carrier is preserved by every `S₄`
permutation. -/
theorem permuteProvenance_centered (σ : Equiv.Perm (Fin 4))
    (v : Fin 4 → ℂ) (hv : ∑ i, v i = 0) :
    ∑ i, permuteProvenance σ v i = 0 := by
  rw [show (∑ i, permuteProvenance σ v i) = ∑ i, v i by
    exact Equiv.sum_comp σ.symm v]
  exact hv

/-- Scalar provenance propagation commutes with the full `S₄` action. -/
theorem scalarProvenanceChannel_covariant (ρ : ℂ)
    (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℂ) :
    permuteProvenance σ (ρ • v) = ρ • permuteProvenance σ v := by
  rfl

/-- Scalar centered provenance propagator on the three-dimensional standard
triplet. -/
noncomputable def scalarProvenancePropagator (ρ : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (ρ : ℂ) • 1

/-- Explicit resolvent of a scalar provenance propagator. -/
noncomputable def scalarProvenanceResolvent (s ρ : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (((1 - s * ρ)⁻¹ : ℝ) : ℂ) • 1

/-- The displayed scalar resolvent is a two-sided inverse. -/
theorem scalarProvenanceResolvent_inverse (s ρ : ℝ)
    (hne : 1 - s * ρ ≠ 0) :
    (1 - (s : ℂ) • scalarProvenancePropagator ρ)
        * scalarProvenanceResolvent s ρ = 1
      ∧ scalarProvenanceResolvent s ρ
        * (1 - (s : ℂ) • scalarProvenancePropagator ρ) = 1 := by
  have hneC : (1 : ℂ) - (s : ℂ) * (ρ : ℂ) ≠ 0 := by
    exact_mod_cast hne
  constructor <;> ext i j <;> by_cases hij : i = j
  · subst j
    simp [scalarProvenancePropagator, scalarProvenanceResolvent,
      Matrix.mul_apply, Matrix.one_apply, hneC]
  · simp [scalarProvenancePropagator, scalarProvenanceResolvent,
      Matrix.mul_apply, Matrix.one_apply, hij]
  · subst j
    simp [scalarProvenancePropagator, scalarProvenanceResolvent,
      Matrix.mul_apply, Matrix.one_apply, hneC]
  · simp [scalarProvenancePropagator, scalarProvenanceResolvent,
      Matrix.mul_apply, Matrix.one_apply, hij]

/-- Geometric completion aggregate of the scalar provenance channel. -/
noncomputable def scalarProvenanceAggregate (s ρ : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ((1 - s : ℝ) : ℂ) •
    (scalarProvenancePropagator ρ * scalarProvenanceResolvent s ρ)

/-- The aggregate is scalar with Möbius coefficient
`α_s(ρ)=(1-s)ρ/(1-sρ)`. -/
theorem scalarProvenanceAggregate_eq (s ρ : ℝ) :
    scalarProvenanceAggregate s ρ
      = (((1 - s) * ρ / (1 - s * ρ) : ℝ) : ℂ) • 1 := by
  ext i j
  simp [scalarProvenanceAggregate, scalarProvenancePropagator,
    scalarProvenanceResolvent, Matrix.mul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp
    push_cast
    ring
  · simp [hij]

/-- Exact inverse Möbius transform, including the `s=1/3` specialization. -/
theorem scalarProvenanceMobius_inversion (s ρ α : ℝ)
    (hs : s ≠ 1) (hres : 1 - s * ρ ≠ 0)
    (hα : α = (1 - s) * ρ / (1 - s * ρ)) :
    ρ = α / (1 - s + s * α)
      ∧ (s = 1 / 3 → ρ = 3 * α / (2 + α)) := by
  have hden : 1 - s + s * α ≠ 0 := by
    rw [hα]
    have heq : 1 - s + s * ((1 - s) * ρ / (1 - s * ρ))
        = (1 - s) / (1 - s * ρ) := by
      field_simp
      ring
    rw [heq]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hs)) hres
  constructor
  · rw [eq_div_iff hden]
    exact (covariant_provenance_inversion s ρ hs
      (by intro h; apply hres; rw [h]; norm_num : s * ρ ≠ 1) α hα).1
  · intro hs3
    subst s
    have htwo : 2 + α ≠ 0 := by
      intro h
      apply hden
      norm_num at h ⊢
      linarith
    rw [eq_div_iff htwo]
    exact (covariant_provenance_inversion (1 / 3) ρ
      (by norm_num)
      (by intro h; apply hres; rw [h]; norm_num) α hα).2 rfl

/-- A terminal quadratic Gram cannot distinguish the aggregate coefficient
`α` from `-α`. -/
theorem scalarProvenanceGram_loses_sign (α : ℝ) :
    ((((α : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ))ᴴ)
        * ((α : ℂ) • 1))
      = ((((-α : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ))ᴴ)
        * (((-α : ℝ) : ℂ) • 1) := by
  simp [Matrix.conjTranspose_smul]

/-- `cor:covariant-provenance-inversion`: covariance of the standard triplet,
the scalar completion aggregate, exact inverse, and sign loss of a terminal
Gram. -/
theorem covariant_provenance_inversion_exact (s ρ α : ℝ)
    (hs : s ≠ 1) (hres : 1 - s * ρ ≠ 0)
    (hα : α = (1 - s) * ρ / (1 - s * ρ)) :
    scalarProvenanceAggregate s ρ = (α : ℂ) • 1
      ∧ ρ = α / (1 - s + s * α)
      ∧ (s = 1 / 3 → ρ = 3 * α / (2 + α))
      ∧ ((((α : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ))ᴴ)
          * ((α : ℂ) • 1))
        = ((((-α : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ))ᴴ)
          * (((-α : ℝ) : ℂ) • 1) := by
  refine ⟨?_, (scalarProvenanceMobius_inversion s ρ α hs hres hα).1,
    (scalarProvenanceMobius_inversion s ρ α hs hres hα).2,
    scalarProvenanceGram_loses_sign α⟩
  rw [scalarProvenanceAggregate_eq, hα]

end NCG
