/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Regular-graph dimension selection, Clifford-marginal
  countermodel, and the two-not-three countertheorem
  (`cor:dimension-regular-graph`,
  `cth:SMST-Clifford-marginals`, `cth:GT-two-not-three`,
  Gran-Tensor manuscript)

* `dimension_regular_graph`: the boxed balance
  `(4-k)v = 4` for a connected simple `k`-regular relation
  graph (cut rank `v-1` = cycle rank `kv/2 - v + 1`) has
  `v = 4, k = 3` (i.e. `K₄`) as its unique solution with
  more than one endpoint.

* `smst_clifford_marginals`: on the Kronecker square, the
  intrinsic grading `Z⊗I` and the multiplicity grading
  `I⊗X` are both involutions with equal (traceless) fibre
  dimensions, yet the first anticommutes and the second
  commutes with the Clifford axis `X⊗I` — separate
  marginals do not determine the relative grading action.

* `gt_two_not_three`: an isometry into a strictly larger
  carrier always leaves nonzero leakage (`ΓΓ* ≠ 1` by the
  trace count), and no surjective linear map exists onto a
  strictly larger space — so exact one- and two-occurrence
  tensor data coexist with an arbitrary extra degree-three
  sector, and the first triple panel is logically
  independent.
-/

open Matrix FiniteDimensional
open scoped Kronecker

namespace NCG

/-- `cor:dimension-regular-graph`. -/
theorem dimension_regular_graph :
    ∀ v k : ℕ, 2 ≤ v → k + 1 ≤ v →
      (4 - k) * v = 4 → v = 4 ∧ k = 3 := by
  intro v k hv hk h
  have hdvd : v ∣ 4 := Dvd.intro_left _ h
  have hv4 : v ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases v <;> omega

/-- `cth:SMST-Clifford-marginals`. -/
theorem smst_clifford_marginals :
    let Z : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
    let X : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let Jchir := Z ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
    let Jsep := (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ X
    let K := X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
    -- both gradings are involutions
    (Jchir * Jchir = 1 ∧ Jsep * Jsep = 1)
    -- with equal (traceless) sign-fibre dimensions
    ∧ (Jchir.trace = 0 ∧ Jsep.trace = 0)
    -- yet opposite relative Clifford action
    ∧ (Jchir * K = -(K * Jchir))
    ∧ (Jsep * K = K * Jsep) := by
  intro Z X Jchir Jsep K
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · ext p q
    fin_cases p <;> fin_cases q <;>
      norm_num [Z, Jchir, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.kroneckerMap_apply, Matrix.one_apply,
        Prod.mk.injEq]
  · ext p q
    fin_cases p <;> fin_cases q <;>
      norm_num [X, Jsep, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.kroneckerMap_apply, Matrix.one_apply,
        Prod.mk.injEq]
  · simp only [Jchir]
    rw [Matrix.trace_kronecker]
    norm_num [Z, Matrix.trace_fin_two_of,
      Matrix.trace_one]
  · simp only [Jsep]
    rw [Matrix.trace_kronecker]
    norm_num [X, Matrix.trace_fin_two_of,
      Matrix.trace_one]
  · ext p q
    fin_cases p <;> fin_cases q <;>
      norm_num [Z, X, Jchir, K, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.kroneckerMap_apply, Matrix.one_apply,
        Matrix.neg_apply, Prod.mk.injEq]
  · ext p q
    fin_cases p <;> fin_cases q <;>
      norm_num [X, Jsep, K, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.kroneckerMap_apply, Matrix.one_apply,
        Prod.mk.injEq]

/-- `cth:GT-two-not-three`. -/
theorem gt_two_not_three :
    -- an isometry into a strictly larger carrier always
    -- leaves nonzero leakage
    (∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
      [DecidableEq b] (Γ : Matrix a b ℂ),
      Γᴴ * Γ = 1 → Fintype.card b < Fintype.card a →
      Γ * Γᴴ ≠ 1)
    -- and no surjective linear map onto a larger space
    ∧ (∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
        [AddCommGroup W] [Module ℂ W]
        [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
        (f : V →ₗ[ℂ] W), Function.Surjective f →
        Module.finrank ℂ W ≤ Module.finrank ℂ V) := by
  constructor
  · intro a b _ _ _ _ Γ hiso hcard heq
    have h1 : (Γ * Γᴴ).trace = (Γᴴ * Γ).trace :=
      Matrix.trace_mul_comm Γ Γᴴ
    rw [heq, hiso, Matrix.trace_one, Matrix.trace_one]
      at h1
    have : (Fintype.card a : ℂ) = (Fintype.card b : ℂ) :=
      h1
    have hnat : Fintype.card a = Fintype.card b := by
      exact_mod_cast this
    omega
  · intro V W _ _ _ _ _ _ f hsurj
    have h := LinearMap.finrank_range_le f
    rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top]
      at h

end NCG
