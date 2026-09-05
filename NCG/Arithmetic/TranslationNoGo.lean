/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite self-translation no-go
  (`prop:v002-translation-nogo`, arithmetic monograph)

Given a finite zero multiset `Z`, finitely many sample points (the
shifted values `z_i − η_j`, collected in a `Finset` so they are
pairwise distinct) avoiding `Z`, and arbitrary nonzero target values
`A`, there is an entire function `F` whose zero multiset contains `Z`
(witnessed by the exact factorization `F = P·G` with `P` the
polynomial with zero multiset `Z` and `G` entire and nonvanishing)
and which takes the prescribed values at all sample points.

The construction is the manuscript's: Lagrange interpolation of
logarithm branches, `F = P·e^h`.  The concluding sentence — that a
finite lower frame of horizontally translated values therefore does
not constrain the horizontal zero positions — is interpretive prose.
-/

open Polynomial

namespace NCG

/-- `prop:v002-translation-nogo` (finite self-translation no-go):
for any finite zero multiset `Z`, pairwise-distinct sample points `S`
avoiding `Z`, and nonzero targets `A`, there is an entire `F = P·G`
with `P` the polynomial with zero multiset `Z`, `G` entire and
everywhere nonzero, and `F = A` on `S`. -/
theorem translation_nogo (Z : Multiset ℂ) (S : Finset ℂ)
    (hZS : ∀ w ∈ S, w ∉ Z) (A : ℂ → ℂ) (hA : ∀ w ∈ S, A w ≠ 0) :
    ∃ F G : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ G ∧
      (∀ z : ℂ, G z ≠ 0) ∧
      (F = fun z => ((Z.map fun w => X - Polynomial.C w).prod.eval z)
        * G z) ∧
      (∀ w ∈ S, F w = A w) := by
  classical
  set P : Polynomial ℂ := (Z.map fun w => X - Polynomial.C w).prod
    with hP
  -- `P` does not vanish at the sample points
  have hPne : ∀ w ∈ S, P.eval w ≠ 0 := by
    intro w hw
    rw [hP, Polynomial.eval_multiset_prod]
    refine Multiset.prod_ne_zero ?_
    intro h0
    simp only [Multiset.map_map, Multiset.mem_map,
      Function.comp_apply] at h0
    obtain ⟨z, hz, hz0⟩ := h0
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hz0
    have hwz : w = z := sub_eq_zero.mp hz0
    exact hZS w hw (hwz ▸ hz)
  -- interpolate logarithm branches at the sample points
  set h : Polynomial ℂ :=
    Lagrange.interpolate S id (fun w => Complex.log (A w / P.eval w))
    with hh
  refine ⟨fun z => P.eval z * Complex.exp (h.eval z),
    fun z => Complex.exp (h.eval z),
    (P.differentiable).mul
      (Complex.differentiable_exp.comp h.differentiable),
    Complex.differentiable_exp.comp h.differentiable,
    fun z => Complex.exp_ne_zero _, rfl, ?_⟩
  intro w hw
  have hnode : h.eval w = Complex.log (A w / P.eval w) := by
    rw [hh]
    simpa using Lagrange.eval_interpolate_at_node
      (v := id) (r := fun w => Complex.log (A w / P.eval w))
      (Set.injOn_id _) hw
  change P.eval w * Complex.exp (h.eval w) = A w
  rw [hnode, Complex.exp_log (div_ne_zero (hA w hw) (hPne w hw)),
    mul_comm, div_mul_cancel₀ _ (hPne w hw)]

end NCG
