/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Exact source-core Pythagoras on graph Hilbert spaces

This is the unbounded-operator form of thm:source-core-Pythagoras.
The domain of the closed operator is represented by its graph Hilbert
space DA; the inclusion and generator action are bounded from that
space, while the ambient operators remain genuinely unbounded.
-/

open Set ContinuousLinearMap
open scoped InnerProduct

noncomputable section

namespace NCG
namespace SourceCorePythagoras

universe u v w x

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {DA : Type w} [NormedAddCommGroup DA] [InnerProductSpace ℂ DA]
  [CompleteSpace DA]
variable {DN : Type x} [NormedAddCommGroup DN] [NormedSpace ℂ DN]

/-- The ambient intertwining defect, pulled back to the graph Hilbert space. -/
def defect (V : E →L[ℂ] H) (A : DA →L[ℂ] E)
    (N : DN →L[ℂ] H) (Vdom : DA →L[ℂ] DN) : DA →L[ℂ] H :=
  N.comp Vdom - V.comp A

/-- The part of NV leaking orthogonally out of the isometric source range. -/
def leakage (V : E →L[ℂ] H) (N : DN →L[ℂ] H)
    (Vdom : DA →L[ℂ] DN) : DA →L[ℂ] H :=
  ((1 : H →L[ℂ] H) - V.comp (V†)).comp (N.comp Vdom)

/-- The mismatch between the compressed ambient generator and the source
generator. -/
def compressionMismatch (V : E →L[ℂ] H) (A : DA →L[ℂ] E)
    (N : DN →L[ℂ] H) (Vdom : DA →L[ℂ] DN) : DA →L[ℂ] E :=
  (V†).comp (N.comp Vdom) - A

/-- Exact graph-domain splitting R = L + VC. -/
theorem defect_eq_leakage_add_compression
    (V : E →L[ℂ] H) (A : DA →L[ℂ] E)
    (N : DN →L[ℂ] H) (Vdom : DA →L[ℂ] DN) :
    defect V A N Vdom =
      leakage V N Vdom + V.comp (compressionMismatch V A N Vdom) := by
  ext z
  simp only [defect, leakage, compressionMismatch, sub_apply, add_apply,
    comp_apply, one_apply_eq_self, map_sub]
  abel

/-- The leakage range is orthogonal to the transported compression range. -/
theorem inner_leakage_compression_eq_zero
    (V : E →L[ℂ] H) (A : DA →L[ℂ] E)
    (N : DN →L[ℂ] H) (Vdom : DA →L[ℂ] DN)
    (hV : (V†).comp V = 1) (x y : DA) :
    inner ℂ (leakage V N Vdom x)
      (V (compressionMismatch V A N Vdom y)) = 0 := by
  rw [← V.adjoint_inner_left]
  simp only [leakage, comp_apply, sub_apply, one_apply_eq_self, map_sub]
  change inner ℂ
    ((V†) (N (Vdom x)) - ((V†).comp V) ((V†) (N (Vdom x))))
    (compressionMismatch V A N Vdom y) = 0
  rw [hV]
  simp

/-- The exact sesquilinear Pythagoras identity on the graph domain. -/
theorem inner_defect_eq
    (V : E →L[ℂ] H) (A : DA →L[ℂ] E)
    (N : DN →L[ℂ] H) (Vdom : DA →L[ℂ] DN)
    (hV : (V†).comp V = 1) (x y : DA) :
    inner ℂ (defect V A N Vdom x) (defect V A N Vdom y) =
      inner ℂ (leakage V N Vdom x) (leakage V N Vdom y) +
        inner ℂ (compressionMismatch V A N Vdom x)
          (compressionMismatch V A N Vdom y) := by
  rw [defect_eq_leakage_add_compression]
  simp only [add_apply, comp_apply, inner_add_left, inner_add_right]
  have hcross :
      inner ℂ (V (compressionMismatch V A N Vdom x))
        (leakage V N Vdom y) = 0 := by
    rw [← inner_conj_symm,
      inner_leakage_compression_eq_zero V A N Vdom hV]
    simp
  rw [inner_leakage_compression_eq_zero V A N Vdom hV,
    hcross, zero_add, add_zero]
  rw [(V.inner_map_map_iff_adjoint_comp_self.mpr hV)
    (compressionMismatch V A N Vdom x)
    (compressionMismatch V A N Vdom y)]

/-- The bounded quadratic-form identity on the graph Hilbert space. -/
theorem defect_gram_eq
    (V : E →L[ℂ] H) (A : DA →L[ℂ] E)
    (N : DN →L[ℂ] H) (Vdom : DA →L[ℂ] DN)
    (hV : (V†).comp V = 1) :
    ((defect V A N Vdom)†).comp (defect V A N Vdom) =
      ((leakage V N Vdom)†).comp (leakage V N Vdom) +
        ((compressionMismatch V A N Vdom)†).comp
          (compressionMismatch V A N Vdom) := by
  ext x
  refine ext_inner_right ℂ fun y => ?_
  simp only [comp_apply, adjoint_inner_left, add_apply, inner_add_left]
  exact inner_defect_eq V A N Vdom hV x y

/-- Pointwise squared-norm Pythagoras for the two graph-domain defects. -/
theorem norm_defect_sq
    (V : E →L[ℂ] H) (A : DA →L[ℂ] E)
    (N : DN →L[ℂ] H) (Vdom : DA →L[ℂ] DN)
    (hV : (V†).comp V = 1) (x : DA) :
    ‖defect V A N Vdom x‖ ^ 2 =
      ‖leakage V N Vdom x‖ ^ 2 +
        ‖compressionMismatch V A N Vdom x‖ ^ 2 := by
  have h := congrArg Complex.re (inner_defect_eq V A N Vdom hV x x)
  rw [Complex.add_re] at h
  calc
    ‖defect V A N Vdom x‖ ^ 2 =
        (inner ℂ (defect V A N Vdom x) (defect V A N Vdom x)).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    _ = (inner ℂ (leakage V N Vdom x) (leakage V N Vdom x)).re +
          (inner ℂ (compressionMismatch V A N Vdom x)
            (compressionMismatch V A N Vdom x)).re := h
    _ = ‖leakage V N Vdom x‖ ^ 2 +
          ‖compressionMismatch V A N Vdom x‖ ^ 2 := by
      exact congrArg₂ (· + ·)
        (inner_self_eq_norm_sq (𝕜 := ℂ) (leakage V N Vdom x))
        (inner_self_eq_norm_sq (𝕜 := ℂ)
          (compressionMismatch V A N Vdom x))

/-- Exact intertwining is equivalent to simultaneous vanishing of leakage
and compression mismatch. -/
theorem defect_eq_zero_iff
    (V : E →L[ℂ] H) (A : DA →L[ℂ] E)
    (N : DN →L[ℂ] H) (Vdom : DA →L[ℂ] DN)
    (hV : (V†).comp V = 1) :
    defect V A N Vdom = 0 ↔
      leakage V N Vdom = 0 ∧ compressionMismatch V A N Vdom = 0 := by
  constructor
  · intro hR
    constructor
    · ext x
      have hs := norm_defect_sq V A N Vdom hV x
      rw [hR] at hs
      simp only [zero_apply, norm_zero] at hs
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (leakage V N Vdom x),
        norm_nonneg (compressionMismatch V A N Vdom x)]
    · ext x
      have hs := norm_defect_sq V A N Vdom hV x
      rw [hR] at hs
      simp only [zero_apply, norm_zero] at hs
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (leakage V N Vdom x),
        norm_nonneg (compressionMismatch V A N Vdom x)]
  · rintro ⟨hL, hC⟩
    rw [defect_eq_leakage_add_compression, hL, hC]
    simp

/-- Vanishing on an A-core (a dense subset of the graph Hilbert space)
extends to the whole graph domain by continuity. -/
theorem defect_eq_zero_of_core
    (V : E →L[ℂ] H) (A : DA →L[ℂ] E)
    (N : DN →L[ℂ] H) (Vdom : DA →L[ℂ] DN)
    (hV : (V†).comp V = 1) {core : Type*} (j : core → DA)
    (hj : DenseRange j)
    (hL : ∀ z, leakage V N Vdom (j z) = 0)
    (hC : ∀ z, compressionMismatch V A N Vdom (j z) = 0) :
    defect V A N Vdom = 0 := by
  apply (defect_eq_zero_iff V A N Vdom hV).2
  constructor
  · ext x
    exact congrFun
      (hj.equalizer (leakage V N Vdom).continuous continuous_const
        (funext hL)) x
  · ext x
    exact congrFun
      (hj.equalizer (compressionMismatch V A N Vdom).continuous continuous_const
        (funext hC)) x

end SourceCorePythagoras
end NCG
