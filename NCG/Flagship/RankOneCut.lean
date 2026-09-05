/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Rank-one complete cut is exactly a replacement
  (`thm:rank-one-cut-replacement-master`, flagship manuscript)

Let `ℛ` be the completed reset on the complete physical cut span
(a trace-preserving linear map on finite matrix spaces).  Then:

* the complete cut response has a one-dimensional output span iff
  there is one normalized state `ω` with the boxed replacement
  form `ℛ(A) = Tr(A)·ω` (`rank_one_cut_replacement`): trace
  preservation pins the coefficient functional to the trace;
* if the output span is not one-dimensional, the reachable range
  contains two distinct outputs, so any admitted future family
  separating the range distinguishes two reset outputs — an
  explicit consequential memory source
  (`memory_source_of_not_rank_one`).

"Response-matrix rank one" is rendered as the one-dimensionality
of the output span (the manuscript's future-tomography
identification); "admitted futures separate the reachable output
range" enters as the separation hypothesis on effect functionals
(disclosed interface).
-/

open Matrix

namespace NCG

variable {n m : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype m] [DecidableEq m]

omit [DecidableEq n] [Nonempty n] [DecidableEq m] in
/-- `thm:rank-one-cut-replacement-master`, boxed equivalence: the
output span is one-dimensional (spanned by a normalized state) iff
the reset is the replacement channel `ℛ(A) = Tr(A)·ω`. -/
theorem rank_one_cut_replacement
    (R : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (htr : ∀ A, (R A).trace = A.trace) :
    (∃ ω : Matrix m m ℂ, ω.trace = 1 ∧ ∀ A, ∃ c : ℂ, R A = c • ω)
      ↔ ∃ ω : Matrix m m ℂ, ω.trace = 1 ∧ ∀ A, R A = A.trace • ω := by
  constructor
  · rintro ⟨ω, hω1, hspan⟩
    refine ⟨ω, hω1, fun A => ?_⟩
    obtain ⟨c, hc⟩ := hspan A
    have htrA := htr A
    rw [hc, Matrix.trace_smul, hω1, smul_eq_mul, mul_one] at htrA
    rw [hc, htrA]
  · rintro ⟨ω, hω1, hrep⟩
    exact ⟨ω, hω1, fun A => ⟨A.trace, hrep A⟩⟩

omit [DecidableEq n] [DecidableEq m] in
/-- If the output span is not one-dimensional, two reachable
outputs differ, and any separating family of admitted future
effects distinguishes them: an explicit consequential memory
source. -/
theorem memory_source_of_not_rank_one {ι : Type*}
    (R : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (htr : ∀ A, (R A).trace = A.trace)
    (f : ι → Matrix m m ℂ →ₗ[ℂ] ℂ)
    (hsep : ∀ A A' : Matrix n n ℂ, R A ≠ R A' →
      ∃ i, f i (R A) ≠ f i (R A'))
    (hnot : ¬ ∃ ω : Matrix m m ℂ, ω.trace = 1
      ∧ ∀ A, ∃ c : ℂ, R A = c • ω) :
    ∃ A A' : Matrix n n ℂ, ∃ i, f i (R A) ≠ f i (R A') := by
  classical
  -- a normalized reachable output exists
  obtain ⟨i0⟩ := (inferInstance : Nonempty n)
  set A₀ : Matrix n n ℂ := Matrix.single i0 i0 1 with hA₀
  have htr₀ : (R A₀).trace = 1 := by
    rw [htr, hA₀]
    simp [Matrix.trace, Matrix.diag, Matrix.single_apply]
  -- some output escapes its line
  have hesc : ∃ A, ∀ c : ℂ, R A ≠ c • R A₀ := by
    by_contra hcon
    rw [not_exists] at hcon
    refine hnot ⟨R A₀, htr₀, fun A => ?_⟩
    by_contra hA
    rw [not_exists] at hA
    exact hcon A (fun c => hA c)
  obtain ⟨A, hA⟩ := hesc
  refine ⟨A, A₀, ?_⟩
  refine hsep A A₀ ?_
  intro heq
  exact hA 1 (by rw [heq, one_smul])

end NCG
