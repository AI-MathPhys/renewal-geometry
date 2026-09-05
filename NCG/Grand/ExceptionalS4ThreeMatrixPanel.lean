/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact S₄ exceptional three-matrix panel

The twist-adapted multiplicity normal form consists of two rectangular
contractions, pairing `[4]` with `[1⁴]` and `[31]` with `[211]`, and one
Hermitian contraction on the self-twist `[22]` multiplicity.  This module
proves the exact exceptional defect formula and its simultaneous zero branch.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace ExceptionalS4ThreeMatrixPanel

noncomputable section

variable {a b : Type*} [Fintype a] [Fintype b]
  [DecidableEq a] [DecidableEq b]

/-- Real Hilbert--Schmidt square of a rectangular complex matrix. -/
def hilbertSchmidtSquare (A : Matrix b a ℂ) : ℝ :=
  (Matrix.trace (Aᴴ * A)).re

/-- The two-sided contraction defect of a paired sign-twist block. -/
def pairedDefect (A : Matrix b a ℂ) : ℝ :=
  (Matrix.trace (1 - Aᴴ * A)).re +
    (Matrix.trace (1 - A * Aᴴ)).re

/-- The contraction defect of the self-twist `[22]` block. -/
def selfTwistDefect (A : Matrix a a ℂ) : ℝ :=
  (Matrix.trace (1 - A * A)).re

theorem pairedDefect_expanded (A : Matrix b a ℂ) :
    pairedDefect A = Fintype.card a + Fintype.card b -
      2 * hilbertSchmidtSquare A := by
  unfold pairedDefect hilbertSchmidtSquare
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_one,
    Matrix.trace_one, Matrix.trace_mul_comm A Aᴴ]
  simp
  ring

theorem selfTwistDefect_expanded (A : Matrix a a ℂ) :
    selfTwistDefect A = Fintype.card a - (Matrix.trace (A * A)).re := by
  unfold selfTwistDefect
  rw [Matrix.trace_sub, Matrix.trace_one]
  simp

lemma posSemidef_traceReal_nonnegative {n : Type*} [Fintype n]
    {X : Matrix n n ℂ} (hX : X.PosSemidef) : 0 ≤ X.trace.re := by
  have h := hX.trace_nonneg
  rw [Complex.nonneg_iff] at h
  exact h.1

lemma posSemidef_traceReal_eq_zero_iff {n : Type*} [Fintype n]
    [DecidableEq n] {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    X.trace.re = 0 ↔ X = 0 := by
  constructor
  · intro hre
    have hnon := hX.trace_nonneg
    rw [Complex.nonneg_iff] at hnon
    have htrace : X.trace = 0 := Complex.ext hre hnon.2.symm
    exact hX.trace_eq_zero_iff.mp htrace
  · rintro rfl
    simp

/-- A paired contraction has zero defect exactly when its rectangular matrix
is unitary on both sides. -/
theorem pairedDefect_eq_zero_iff
    (A : Matrix b a ℂ)
    (hdom : (1 - Aᴴ * A).PosSemidef)
    (hcod : (1 - A * Aᴴ).PosSemidef) :
    pairedDefect A = 0 ↔ Aᴴ * A = 1 ∧ A * Aᴴ = 1 := by
  have hd := posSemidef_traceReal_nonnegative hdom
  have hc := posSemidef_traceReal_nonnegative hcod
  constructor
  · intro hzero
    unfold pairedDefect at hzero
    have hd0 : (1 - Aᴴ * A).trace.re = 0 := by linarith
    have hc0 : (1 - A * Aᴴ).trace.re = 0 := by linarith
    have hdmat := (posSemidef_traceReal_eq_zero_iff hdom).mp hd0
    have hcmat := (posSemidef_traceReal_eq_zero_iff hcod).mp hc0
    exact ⟨(sub_eq_zero.mp hdmat).symm, (sub_eq_zero.mp hcmat).symm⟩
  · rintro ⟨hA, hAH⟩
    unfold pairedDefect
    rw [hA, hAH]
    simp

theorem pairedDefect_nonnegative
    (A : Matrix b a ℂ)
    (hdom : (1 - Aᴴ * A).PosSemidef)
    (hcod : (1 - A * Aᴴ).PosSemidef) :
    0 ≤ pairedDefect A := by
  unfold pairedDefect
  exact add_nonneg (posSemidef_traceReal_nonnegative hdom)
    (posSemidef_traceReal_nonnegative hcod)

/-- A two-sided rectangular unitary forces equality of the multiplicities. -/
theorem pairedUnitary_cardinality
    (A : Matrix b a ℂ) (hdom : Aᴴ * A = 1) (hcod : A * Aᴴ = 1) :
    Fintype.card a = Fintype.card b := by
  have htrace : Matrix.trace (Aᴴ * A) = Matrix.trace (A * Aᴴ) :=
    Matrix.trace_mul_comm Aᴴ A
  rw [hdom, hcod, Matrix.trace_one, Matrix.trace_one] at htrace
  exact_mod_cast htrace

theorem selfTwistDefect_eq_zero_iff
    (A : Matrix a a ℂ) (hcontract : (1 - A * A).PosSemidef) :
    selfTwistDefect A = 0 ↔ A * A = 1 := by
  unfold selfTwistDefect
  rw [posSemidef_traceReal_eq_zero_iff hcontract, sub_eq_zero]
  exact eq_comm

theorem selfTwistDefect_nonnegative
    (A : Matrix a a ℂ) (hcontract : (1 - A * A).PosSemidef) :
    0 ≤ selfTwistDefect A :=
  posSemidef_traceReal_nonnegative hcontract

section Panel

variable {m1 msgn m31 m211 m22 : Type*}
  [Fintype m1] [Fintype msgn] [Fintype m31] [Fintype m211]
  [Fintype m22] [DecidableEq m1] [DecidableEq msgn]
  [DecidableEq m31] [DecidableEq m211] [DecidableEq m22]

/-- The three multiplicity matrices in twist-adapted `S₄` frames, together
with their contraction certificates. -/
structure ExceptionalPanel where
  A1 : Matrix msgn m1 ℂ
  A3 : Matrix m211 m31 ℂ
  A2 : Matrix m22 m22 ℂ
  A2_hermitian : A2ᴴ = A2
  A1_domain_contraction : (1 - A1ᴴ * A1).PosSemidef
  A1_codomain_contraction : (1 - A1 * A1ᴴ).PosSemidef
  A3_domain_contraction : (1 - A3ᴴ * A3).PosSemidef
  A3_codomain_contraction : (1 - A3 * A3ᴴ).PosSemidef
  A2_contraction : (1 - A2 * A2).PosSemidef

/-- Exceptional contribution `d_N Tr(I-T²)` after the five isotypes have
been reduced to the three allowed sign-twist blocks. -/
def exceptionalContribution (dN : ℝ)
    (P : ExceptionalPanel (m1 := m1) (msgn := msgn) (m31 := m31)
      (m211 := m211) (m22 := m22)) : ℝ :=
  dN * (pairedDefect P.A1 + 3 * pairedDefect P.A3 +
    2 * selfTwistDefect P.A2)

theorem exceptionalContribution_expanded (dN : ℝ)
    (P : ExceptionalPanel (m1 := m1) (msgn := msgn) (m31 := m31)
      (m211 := m211) (m22 := m22)) :
    exceptionalContribution dN P = dN *
      ((Fintype.card m1 + Fintype.card msgn -
          2 * hilbertSchmidtSquare P.A1) +
       3 * (Fintype.card m31 + Fintype.card m211 -
          2 * hilbertSchmidtSquare P.A3) +
       2 * (Fintype.card m22 - (Matrix.trace (P.A2 * P.A2)).re)) := by
  unfold exceptionalContribution
  rw [pairedDefect_expanded, pairedDefect_expanded,
    selfTwistDefect_expanded]

theorem exceptionalContribution_nonnegative (dN : ℝ) (hdN : 0 ≤ dN)
    (P : ExceptionalPanel (m1 := m1) (msgn := msgn) (m31 := m31)
      (m211 := m211) (m22 := m22)) :
    0 ≤ exceptionalContribution dN P := by
  unfold exceptionalContribution
  have h1 := pairedDefect_nonnegative P.A1
    P.A1_domain_contraction P.A1_codomain_contraction
  have h3 := pairedDefect_nonnegative P.A3
    P.A3_domain_contraction P.A3_codomain_contraction
  have h2 := selfTwistDefect_nonnegative P.A2 P.A2_contraction
  positivity

/-- Exact zero branch: both paired matrices are two-sided unitaries, the
self-twist matrix is an involution, and the paired multiplicities balance. -/
theorem exceptionalContribution_eq_zero_iff (dN : ℝ) (hdN : 0 < dN)
    (P : ExceptionalPanel (m1 := m1) (msgn := msgn) (m31 := m31)
      (m211 := m211) (m22 := m22)) :
    exceptionalContribution dN P = 0 ↔
      Fintype.card m1 = Fintype.card msgn ∧
      Fintype.card m31 = Fintype.card m211 ∧
      P.A1ᴴ * P.A1 = 1 ∧ P.A1 * P.A1ᴴ = 1 ∧
      P.A3ᴴ * P.A3 = 1 ∧ P.A3 * P.A3ᴴ = 1 ∧
      P.A2 * P.A2 = 1 := by
  have h1 := pairedDefect_nonnegative P.A1
    P.A1_domain_contraction P.A1_codomain_contraction
  have h3 := pairedDefect_nonnegative P.A3
    P.A3_domain_contraction P.A3_codomain_contraction
  have h2 := selfTwistDefect_nonnegative P.A2 P.A2_contraction
  constructor
  · intro hzero
    unfold exceptionalContribution at hzero
    have hsum : pairedDefect P.A1 + 3 * pairedDefect P.A3 +
        2 * selfTwistDefect P.A2 = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hdN)
    have hz1 : pairedDefect P.A1 = 0 := by nlinarith
    have hz3 : pairedDefect P.A3 = 0 := by nlinarith
    have hz2 : selfTwistDefect P.A2 = 0 := by nlinarith
    obtain ⟨h1d, h1c⟩ := (pairedDefect_eq_zero_iff P.A1
      P.A1_domain_contraction P.A1_codomain_contraction).mp hz1
    obtain ⟨h3d, h3c⟩ := (pairedDefect_eq_zero_iff P.A3
      P.A3_domain_contraction P.A3_codomain_contraction).mp hz3
    have h2u := (selfTwistDefect_eq_zero_iff P.A2 P.A2_contraction).mp hz2
    exact ⟨pairedUnitary_cardinality P.A1 h1d h1c,
      pairedUnitary_cardinality P.A3 h3d h3c,
      h1d, h1c, h3d, h3c, h2u⟩
  · rintro ⟨-, -, h1d, h1c, h3d, h3c, h2u⟩
    unfold exceptionalContribution
    rw [(pairedDefect_eq_zero_iff P.A1 P.A1_domain_contraction
      P.A1_codomain_contraction).mpr ⟨h1d, h1c⟩,
      (pairedDefect_eq_zero_iff P.A3 P.A3_domain_contraction
      P.A3_codomain_contraction).mpr ⟨h3d, h3c⟩,
      (selfTwistDefect_eq_zero_iff P.A2 P.A2_contraction).mpr h2u]
    ring

end Panel
end
end ExceptionalS4ThreeMatrixPanel
end NCG
