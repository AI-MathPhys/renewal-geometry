/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ClockQuarterRoot

/-!
# One routing relation suffices, and the bare tensor decides
  nothing (`prop:SM-one-routing`, `cth:SM-bare-universal-no-go`,
  Gran-Tensor manuscript)

* `grading_even_iff` / `sm_one_routing`: a coefficient crosses
  the grading exactly when it fails to commute with `Z` (the
  commutant of `Z` is the diagonal sector), and adjoining the
  routing relations gives everything:
  `C*(X, Y, Z) = M₂(ℂ)` — the canonical completion is minimal
  at the level of support-changing routing;
* `sm_bare_universal_no_go`: one and the same grading-even
  expectation tensor (all even-sector expectations of the two
  states agree) extends to both a zero-occurrence state and a
  nonzero-occurrence state, so the bare tensor cannot imply
  nonzero grading-changing matter occurrence.

Rendering disclosed: phase conjugation supplying `Y` from `X`
is one line of the generation clause; the process-level version
of the countermodel follows by preparing the two displayed
states.
-/

open Matrix

namespace NCG

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-- A coefficient crosses the grading exactly when it fails to
commute with `Z`: the commutant of `Z` is the diagonal
sector. -/
theorem grading_even_iff (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * clockZ = clockZ * M ↔ M 0 1 = 0 ∧ M 1 0 = 0 := by
  constructor
  · intro h
    have hz00 : clockZ 0 0 = 1 := by simp [clockZ]
    have hz01 : clockZ 0 1 = 0 := by simp [clockZ]
    have hz10 : clockZ 1 0 = 0 := by simp [clockZ]
    have hz11 : clockZ 1 1 = -1 := by simp [clockZ]
    constructor
    · have hL : (M * clockZ) 0 1 = -(M 0 1) := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, hz01, hz11]
        ring
      have hR : (clockZ * M) 0 1 = M 0 1 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, hz00, hz01]
        ring
      have h01 := congrFun (congrFun h 0) 1
      rw [hL, hR] at h01
      have h2 : (2 : ℂ) * M 0 1 = 0 := by
        linear_combination - h01
      rcases mul_eq_zero.mp h2 with hbad | hgood
      · exact absurd hbad (by norm_num)
      · exact hgood
    · have hL : (M * clockZ) 1 0 = M 1 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, hz00, hz10]
        ring
      have hR : (clockZ * M) 1 0 = -(M 1 0) := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, hz10, hz11]
        ring
      have h10 := congrFun (congrFun h 1) 0
      rw [hL, hR] at h10
      have h2 : (2 : ℂ) * M 1 0 = 0 := by
        linear_combination h10
      rcases mul_eq_zero.mp h2 with hbad | hgood
      · exact absurd hbad (by norm_num)
      · exact hgood
  · rintro ⟨h01, h10⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockZ, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two, h01, h10] <;>
      try ring

/-- `prop:SM-one-routing`: the routing relations generate the
full grading algebra, `C*(X, Y, Z) = M₂(ℂ)`. -/
theorem sm_one_routing :
    StarAlgebra.adjoin ℂ
      ({clockX, clockY, clockZ}
        : Set (Matrix (Fin 2) (Fin 2) ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  have hXm : clockX ∈ StarAlgebra.adjoin ℂ
      ({clockX, clockY, clockZ}
        : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    StarAlgebra.subset_adjoin ℂ _ (by simp)
  have hYm : clockY ∈ StarAlgebra.adjoin ℂ
      ({clockX, clockY, clockZ}
        : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    StarAlgebra.subset_adjoin ℂ _ (by simp)
  have hZm : clockZ ∈ StarAlgebra.adjoin ℂ
      ({clockX, clockY, clockZ}
        : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    StarAlgebra.subset_adjoin ℂ _ (by simp)
  have h00 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
      = (2⁻¹ : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ)
        + clockZ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockZ, Matrix.single_apply, Matrix.one_apply] <;>
      try norm_num
  have h11 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)
      = (2⁻¹ : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ)
        - clockZ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockZ, Matrix.single_apply, Matrix.one_apply] <;>
      try norm_num
  have h01 : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
      = (2⁻¹ : ℂ) • (clockX + Complex.I • clockY) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockX, clockY, Matrix.single_apply] <;>
      try ring_nf <;>
      try (simp [Complex.I_sq]) <;>
      try ring_nf
  have h10 : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)
      = (2⁻¹ : ℂ) • (clockX - Complex.I • clockY) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockX, clockY, Matrix.single_apply] <;>
      try ring_nf <;>
      try (simp [Complex.I_sq]) <;>
      try ring_nf
  have hexp : M = M 0 0
        • Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
      + M 0 1 • Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
      + M 1 0 • Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)
      + M 1 1
        • Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.single_apply]
  rw [hexp]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
  · refine SMulMemClass.smul_mem _ ?_
    rw [h00]
    exact SMulMemClass.smul_mem _ (add_mem (one_mem _) hZm)
  · refine SMulMemClass.smul_mem _ ?_
    rw [h01]
    exact SMulMemClass.smul_mem _
      (add_mem hXm (SMulMemClass.smul_mem _ hYm))
  · refine SMulMemClass.smul_mem _ ?_
    rw [h10]
    exact SMulMemClass.smul_mem _
      (sub_mem hXm (SMulMemClass.smul_mem _ hYm))
  · refine SMulMemClass.smul_mem _ ?_
    rw [h11]
    exact SMulMemClass.smul_mem _ (sub_mem (one_mem _) hZm)

/-- `cth:SM-bare-universal-no-go`: the same grading-even
expectation tensor extends to a zero-occurrence state and a
nonzero-occurrence state. -/
theorem sm_bare_universal_no_go :
    (∀ Mx : Matrix (Fin 2) (Fin 2) ℂ,
      Mx * clockZ = clockZ * Mx →
      (((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
          * Mx).trace
        = (((1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ)
            + clockX)) * Mx).trace)
    ∧ ((((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        * clockX).trace = 0)
    ∧ ((((1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ)
        + clockX)) * clockX).trace ≠ 0) := by
  have htrX : (clockX : Matrix (Fin 2) (Fin 2) ℂ).trace = 0 := by
    simp [clockX, Matrix.trace_fin_two]
  have htrXM : ∀ Mx : Matrix (Fin 2) (Fin 2) ℂ,
      (clockX * Mx).trace = Mx 0 1 + Mx 1 0 := by
    intro Mx
    rw [Matrix.trace_fin_two, Matrix.mul_apply,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [clockX]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro Mx h
    obtain ⟨h01, h10⟩ := (grading_even_iff Mx).mp h
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul,
      Matrix.trace_smul, Matrix.add_mul, Matrix.one_mul,
      Matrix.trace_add, htrXM, h01, h10, add_zero, add_zero]
  · rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.one_mul,
      htrX, smul_zero]
  · have h2 : (((1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ)
        + clockX)) * clockX).trace = 1 := by
      rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul,
        Matrix.one_mul, Matrix.trace_add, htrX, zero_add,
        show (clockX * clockX).trace = 2 from by
          rw [htrXM]
          norm_num [clockX],
        smul_eq_mul]
      norm_num
    rw [h2]
    norm_num

end NCG
