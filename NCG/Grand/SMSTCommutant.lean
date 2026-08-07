/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# SMST commutants: support-polar loading, the multiplicity
  quiver, and the massless alternatives
  (`thm:SMST-support-polar-commutant`,
  `thm:SMST-quiver-commutant`, `cor:SMST-graph-massless`,
  Gran-Tensor manuscript)

* `commutant_polynomial_calculus`: the no-extra-loading core of
  the boxed commutant equalities — anything commuting with an
  incidence datum commutes with every polynomial functional
  calculus output of it, so support projections, support
  metrics, and polar data add no finite loading;
* `commutant_support_gram`: in particular the support Gram
  `F*F` stays in the bicommutant of `{F, F*}`;
* `quiver_certificate`: the boxed quiver-form kernel — the
  Hilbert–Schmidt weight `tr(K*K)` of a commutator block
  vanishes iff the block intertwines exactly (`K = 0`), so the
  first positive quiver eigenvalue certifies the absence of
  additional flavour/generation endomorphisms;
* `quiver_form_kernel`: the summed form — the full nonnegative
  commutator ledger vanishes iff every block intertwines;
* `massless_limit`: the constant-rank branch limit
  `α_m → -Im Tr(D†dD)` as `m ↓ 0` (each singular-value factor
  `a/(s + m²) → a/s` continuously);
* `zero_mode_dichotomy`: the boxed full-rank alternative — a
  square incidence map either has `det D ≠ 0` (flat massless
  connection after the determinant phase) or carries an explicit
  zero mode, the exact remaining local obstruction.

Rendering disclosed: the von Neumann bicommutant identifications
`𝓜 = (𝓞^sup)'` and `C*(𝓢,T)' ≅ End 𝔔` as algebra isomorphisms,
the Hilbert–Schmidt basis expansion of the ambient commutator
form, and the determinant-line curvature statement
`(det ker D)* ⊗ det coker D` are the manuscript's
operator-algebra and line-bundle layers; the functional-calculus
closure, the exact kernel certificates, the scalar limit, and
the rank dichotomy are proved here.
-/

open Matrix Polynomial

namespace NCG

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]

/-- Functional-calculus closure of the commutant: `X` commuting
with `M` commutes with every polynomial in `M` — support data
add no finite loading. -/
theorem commutant_polynomial_calculus (X M : Matrix n n ℂ)
    (h : Commute X M) (p : Polynomial ℂ) :
    Commute X (Polynomial.aeval M p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_right hq
  | monomial k a =>
    rw [Polynomial.aeval_monomial]
    have hsc : Commute X (algebraMap ℂ (Matrix n n ℂ) a) :=
      (Algebra.commutes a X).symm
    exact hsc.mul_right (h.pow_right k)

omit [DecidableEq n] in
/-- The support Gram stays in the commutant closure: commuting
with `F` and `F*` gives commuting with `F*F`. -/
theorem commutant_support_gram (X F : Matrix n n ℂ)
    (hF : Commute X F) (hFH : Commute X Fᴴ) :
    Commute X (Fᴴ * F) :=
  hFH.mul_right hF

omit [DecidableEq n] in
open scoped ComplexOrder in
/-- Boxed quiver certificate: the Hilbert–Schmidt weight of a
commutator block vanishes iff the block intertwines exactly. -/
theorem quiver_certificate (K : Matrix n m ℂ) :
    (Kᴴ * K).trace = 0 ↔ K = 0 :=
  Matrix.trace_conjTranspose_mul_self_eq_zero_iff

omit [DecidableEq n] in
/-- Summed quiver-form kernel: the full nonnegative commutator
ledger vanishes iff every block intertwines. -/
theorem quiver_form_kernel {J : Type*} [Fintype J]
    (K : J → Matrix n m ℂ) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hrep : ∀ j, ((K j)ᴴ * K j).trace = (f j : ℂ)) :
    (∑ j, f j = 0) ↔ ∀ j, K j = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => hf j)]
  constructor
  · intro hz j
    have : ((K j)ᴴ * K j).trace = 0 := by
      rw [hrep j, hz j (Finset.mem_univ j)]
      norm_num
    exact (quiver_certificate (K j)).mp this
  · intro hz j _
    have : ((f j : ℝ) : ℂ) = 0 := by
      rw [← hrep j, hz j]
      simp
    exact_mod_cast this

/-- Constant-rank massless limit: each singular-value factor of
`α_m` converges continuously as `m ↓ 0`. -/
theorem massless_limit (a s : ℝ) (hs : 0 < s) :
    Filter.Tendsto (fun μ : ℝ => a / (s + μ ^ 2))
      (nhds 0) (nhds (a / s)) := by
  have hc : Continuous fun μ : ℝ => a / (s + μ ^ 2) := by
    refine continuous_const.div (by fun_prop) fun μ => ?_
    positivity
  simpa using hc.tendsto 0

/-- Boxed full-rank alternative: a square incidence map either
has `det D ≠ 0` or carries an explicit zero mode. -/
theorem zero_mode_dichotomy (D : Matrix n n ℂ) :
    D.det ≠ 0 ∨ ∃ v ≠ 0, D.mulVec v = 0 := by
  by_cases h : D.det = 0
  · exact Or.inr (Matrix.exists_mulVec_eq_zero_iff.mpr h)
  · exact Or.inl h

end NCG
