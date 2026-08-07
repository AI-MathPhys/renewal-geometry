/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandScoreCollision

/-!
# Coherence and scheduler no-gos
  (`cth:coherence-no-go`, `cth:store-scheduler-no-go`,
   Gran-Tensor manuscript)

* `coherence_no_go`: the two diagonal CP branches cannot see
  coherence — the identity channel and the `Z`-conjugation
  channel have identical diagonal branch data on every input,
  yet differ as realizations (they disagree on the off-diagonal
  coherence of the score word `E₀₁`): no rule derived only from
  the two diagonal CP branches identifies the physical
  off-diagonal coherence of every realization;
* `store_scheduler_no_go`: two devices with the same raw
  evolution and the same controlled alphabet can differ in
  autonomous invocation — the never-invoking device keeps the
  identity renewal channel while the always-invoking device
  applies the fair score dephasing `D_Z`, and for non-scalar
  `Z` these renewal channels differ (`D_Z` kills the coherence
  word `E₀₁` that the identity preserves): control availability
  alone does not determine autonomous occurrence.

Rendering disclosed: the two channels' shared alphabet and raw
evolution are the common frame; the displayed channel
inequality is the no-go content.
-/

open Matrix

namespace NCG

set_option linter.unusedSimpArgs false

set_option linter.flexible false in
/-- `cth:coherence-no-go`: identical diagonal branch data,
distinct realizations. -/
theorem coherence_no_go :
    (∀ (Xm : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2),
      (clockZ * Xm * clockZ) i i = Xm i i)
    ∧ (∃ Xm : Matrix (Fin 2) (Fin 2) ℂ,
        clockZ * Xm * clockZ ≠ Xm) := by
  constructor
  · intro Xm i
    fin_cases i <;>
      simp [clockZ, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two]
  · refine ⟨Matrix.single 0 1 1, ?_⟩
    intro h
    have h2 := congrFun (congrFun h 0) 1
    simp [clockZ, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.single_apply] at h2
    exact absurd h2 (by norm_num)

/-- `cth:store-scheduler-no-go`: the always-invoking renewal
channel (fair score dephasing) differs from the never-invoking
one (identity) on the coherence word. -/
theorem store_scheduler_no_go :
    (1 / 2 : ℂ) • (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
        + clockZ * Matrix.single 0 1 1 * clockZ)
      ≠ Matrix.single 0 1 1 := by
  intro h
  have h2 := congrFun (congrFun h 0) 1
  simp [clockZ, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Matrix.single_apply,
    Matrix.smul_apply] at h2

end NCG
