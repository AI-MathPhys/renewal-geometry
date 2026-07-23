/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Isotropy is not derived; power counting is grade-blind

**Proposition `prop:isotropy-not-derived`**: literal isotropy of the
reset second moment is an extra hypothesis — there are normalised
direction weights whose second moment is **not** a multiple of the
identity (`NCG.isotropy_not_derived`): weight the first axis twice as
much as the others.

**Theorem `thm:rg-no-dimension-selection`** (counting core): the
canonical engineering dimension of a first-order Dirac coupling is one
in every spatial dimension — the fermion bilinear has dimension `d`
inside a density of dimension `d + 1`, independently of the inserted
Clifford grade (`NCG.engineering_coupling_dimension`).  The `d = 3`
selection is the Hodge/Clifford-grade matching
(`NCG.closure_selects_three`), not RG relevance. -/

namespace NCG

/-- **Proposition `prop:isotropy-not-derived`**: for every rank `d ≥ 2`
there are strictly positive normalised axis weights whose diagonal
second moment is not isotropic — the weighted-axis reset law is a
counterexample to "ergodicity implies isotropy". -/
theorem isotropy_not_derived {d : ℕ} (hd : 2 ≤ d) :
    ∃ p : Fin d → ℝ, (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧
      Matrix.diagonal p
        ≠ ((1 : ℝ) / d) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hd0 : (0:ℝ) < (d:ℝ) + 1 := by positivity
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  refine ⟨fun i => (if i = i0 then 2 else 1) / ((d : ℝ) + 1),
    fun i => ?_, ?_, ?_⟩
  · show (0:ℝ) < (if i = i0 then (2:ℝ) else 1) / ((d : ℝ) + 1)
    rcases eq_or_ne i i0 with rfl | hi
    · rw [if_pos rfl]
      positivity
    · rw [if_neg hi]
      positivity
  · rw [← Finset.sum_div]
    rw [show (∑ i : Fin d, (if i = i0 then (2:ℝ) else 1))
        = ∑ i : Fin d, (1 + if i = i0 then (1:ℝ) else 0) by
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> norm_num]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Finset.sum_ite_eq' Finset.univ i0
        (fun _ => (1:ℝ))]
    have h0mem : i0 ∈ Finset.univ := Finset.mem_univ _
    simp only [if_pos h0mem, nsmul_eq_mul, mul_one]
    field_simp
  · intro hcontra
    have h00 : Matrix.diagonal
        (fun i : Fin d => (if i = i0 then (2:ℝ) else 1) / ((d : ℝ) + 1))
        i0 i0
        = (((1 : ℝ) / d) • (1 : Matrix (Fin d) (Fin d) ℝ)) i0 i0 := by
      rw [hcontra]
    rw [Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, if_pos rfl] at h00
    have hdpos : (0:ℝ) < (d:ℝ) := by
      have : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      linarith
    rw [div_eq_div_iff (ne_of_gt (by linarith : (0:ℝ) < (d:ℝ) + 1))
      (ne_of_gt hdpos)] at h00
    have h2d : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    nlinarith

/-- **Theorem `thm:rg-no-dimension-selection`** (grade-blind counting):
the engineering dimension of the first-order coupling coefficient is
`(d + 1) − d = 1` in every spatial dimension `d` — canonical power
counting cannot distinguish Clifford grades, so it selects no
dimension.  The `d = 3` selection is the Hodge-degree matching of
`NCG.closure_selects_three`. -/
theorem engineering_coupling_dimension (d : ℕ) :
    ((d : ℤ) + 1) - d = 1 := by
  ring

end NCG
