/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Continuum firewalls: completeness and norm-small comparisons
  (`cth:finite-complete-not-uniform`, `cth:norm-small-gapless`,
   Gran-Tensor manuscript)

* `finite_complete_not_uniform`: `S_ε = [[1,1],[0,ε]]` is
  invertible for every `ε ≠ 0` (source complete), while the
  Rayleigh quotient at the fixed unit direction `(1,-1)/√2` is
  `ε²/2 → 0` — pointwise completeness gives no uniform frame
  floor.
* `norm_small_gapless`: if `‖S_X - S_{0,X}‖ → 0` and
  `‖S_{0,X}‖ → 1`, then `‖S_X‖ → 1` — a norm-small perturbation
  of a gapless family cannot establish a noncollapsing gap.

Rendering disclosed: `λ_min(S_ε^*S_ε) → 0` is rendered by the
explicit Rayleigh witness (`‖S_ε u‖² = ε²` at `‖u‖² = 2`), which
dominates the least eigenvalue; the comparison family is indexed
by `ℕ` along the cutoff filter.
-/

open Matrix Filter

namespace NCG

/-- `cth:finite-complete-not-uniform`: invertibility at every
`ε ≠ 0` with collapsing Rayleigh quotient. -/
theorem finite_complete_not_uniform :
    (∀ ε : ℝ, ε ≠ 0 →
      IsUnit (!![1, 1; 0, ε] : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ (∀ ε : ℝ,
        ((!![1, 1; 0, ε] : Matrix (Fin 2) (Fin 2) ℝ)
            *ᵥ ![1, -1]) ⬝ᵥ
          ((!![1, 1; 0, ε] : Matrix (Fin 2) (Fin 2) ℝ)
            *ᵥ ![1, -1]) = ε ^ 2)
    ∧ (((![1, -1] : Fin 2 → ℝ) ⬝ᵥ ![1, -1]) = 2)
    ∧ Tendsto (fun ε : ℝ => ε ^ 2 / 2) (nhds 0) (nhds 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε hε
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
    simpa using isUnit_iff_ne_zero.mpr hε
  · intro ε
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [dotProduct, Fin.sum_univ_two]
    norm_num
  · have h := ((continuous_pow 2).div_const (2 : ℝ)).tendsto 0
    simpa using h

/-- `cth:norm-small-gapless`: a uniformly norm-small
perturbation of a gapless reference keeps the norm collapsing
to one. -/
theorem norm_small_gapless {E : Type*} [SeminormedAddCommGroup E]
    (S S0 : ℕ → E)
    (hdiff : Tendsto (fun n => ‖S n - S0 n‖) atTop (nhds 0))
    (hS0 : Tendsto (fun n => ‖S0 n‖) atTop (nhds 1)) :
    Tendsto (fun n => ‖S n‖) atTop (nhds 1) := by
  have hsq : Tendsto (fun n => ‖S n‖ - ‖S0 n‖) atTop (nhds 0) :=
    squeeze_zero_norm
      (fun n => abs_norm_sub_norm_le (S n) (S0 n)) hdiff
  have hadd := hsq.add hS0
  simpa using hadd

end NCG
