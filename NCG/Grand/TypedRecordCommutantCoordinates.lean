/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Real coordinates of the typed record commutant

The typed record commutant in `thm:SM-typed-occurrence-RN` consists of six
scalar effects and one Hermitian `2 × 2` effect.  This file supplies its
literal ten-real-coordinate model and proves that a nonzero conductance
constraint cuts out a nine-dimensional linear tangent space.  It is shared by
the RN theorem and `cth:SM-occurrence-marginal-nonselection`.
-/

open scoped BigOperators

namespace NCG

/-- Six scalar coordinates followed by the two diagonal and two off-diagonal
real coordinates of a Hermitian `2 × 2` effect. -/
abbrev TypedRecordEffectCoordinates := Fin 10 → ℝ

/-- The displayed typed commutant has real dimension `6 + 4 = 10`. -/
theorem typedRecordEffectCoordinates_finrank :
    Module.finrank ℝ TypedRecordEffectCoordinates = 10 := by simp

/-- A real affine conductance panel on the typed commutant. -/
def typedConductanceFunctional (g : Fin 10 → ℝ) :
    TypedRecordEffectCoordinates →ₗ[ℝ] ℝ where
  toFun x := ∑ i, g i * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    calc
      ∑ i, g i * (a * x i) = ∑ i, a * (g i * x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = a * ∑ i, g i * x i := by rw [Finset.mul_sum]

/-- A nonzero coefficient panel makes the conductance functional nonzero. -/
theorem typedConductanceFunctional_ne_zero
    (g : Fin 10 → ℝ) (hg : g ≠ 0) :
    typedConductanceFunctional g ≠ 0 := by
  classical
  intro hzero
  apply hg
  funext i
  have happly := LinearMap.congr_fun hzero (Pi.single i 1)
  have hi : typedConductanceFunctional g (Pi.single i 1) = g i := by
    simp [typedConductanceFunctional, Pi.single_apply]
  rw [hi] at happly
  simpa using happly

/-- Every nonzero real functional to `ℝ` is surjective. -/
theorem realLinearFunctional_surjective
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] ℝ) (hL : L ≠ 0) : Function.Surjective L := by
  have hex : ∃ v, L v ≠ 0 := by
    by_contra h
    push Not at h
    apply hL
    ext v
    simpa using h v
  obtain ⟨v, hv⟩ := hex
  intro y
  refine ⟨(y / L v) • v, ?_⟩
  simp [hv]

/-- One independently fixed, nonzero conductance removes exactly one of the
ten real typed-effect coordinates. -/
theorem typedConductanceKernel_finrank_nine
    (g : Fin 10 → ℝ) (hg : g ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (typedConductanceFunctional g)) = 9 := by
  let L := typedConductanceFunctional g
  have hsurj : Function.Surjective L :=
    realLinearFunctional_surjective L
      (typedConductanceFunctional_ne_zero g hg)
  have hrange : Module.finrank ℝ (LinearMap.range L) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hdomain : Module.finrank ℝ TypedRecordEffectCoordinates = 10 :=
    typedRecordEffectCoordinates_finrank
  have heq : 1 + Module.finrank ℝ (LinearMap.ker L) = 10 := by
    calc
      1 + Module.finrank ℝ (LinearMap.ker L) =
          Module.finrank ℝ (LinearMap.range L) +
            Module.finrank ℝ (LinearMap.ker L) := by rw [hrange]
      _ = Module.finrank ℝ TypedRecordEffectCoordinates :=
        LinearMap.finrank_range_add_finrank_ker L
      _ = 10 := hdomain
  have hker : Module.finrank ℝ (LinearMap.ker L) = 9 := by omega
  simpa [L] using hker

/-- The fixed-conductance affine fibre through `x₀` is translated by exactly
the nine-dimensional kernel. -/
theorem typedConductance_fibre_difference_iff
    (g : Fin 10 → ℝ) (x x₀ : TypedRecordEffectCoordinates) :
    typedConductanceFunctional g x = typedConductanceFunctional g x₀ ↔
      x - x₀ ∈ LinearMap.ker (typedConductanceFunctional g) := by
  simp [LinearMap.mem_ker, sub_eq_zero]

/-! ## Concrete effect inequalities -/

/-- Coordinate form of `0 ⪯ K ⪯ I` for six scalar blocks and the Hermitian
`2 × 2` block `[[a,z],[conj z,b]]`, where `z=x+iy`.  The last two inequalities
are exactly the determinant tests for that block and its complement. -/
def TypedRecordEffectFeasible (x : TypedRecordEffectCoordinates) : Prop :=
  (0 ≤ x 0 ∧ x 0 ≤ 1) ∧ (0 ≤ x 1 ∧ x 1 ≤ 1) ∧
  (0 ≤ x 2 ∧ x 2 ≤ 1) ∧ (0 ≤ x 3 ∧ x 3 ≤ 1) ∧
  (0 ≤ x 4 ∧ x 4 ≤ 1) ∧ (0 ≤ x 5 ∧ x 5 ≤ 1) ∧
  (0 ≤ x 6 ∧ x 6 ≤ 1) ∧ (0 ≤ x 7 ∧ x 7 ≤ 1) ∧
  x 8 ^ 2 + x 9 ^ 2 ≤ x 6 * x 7 ∧
  x 8 ^ 2 + x 9 ^ 2 ≤ (1 - x 6) * (1 - x 7)

/-- The scalar interior effect `κI` in the ten-coordinate model. -/
def scalarTypedRecordEffect (κ : ℝ) : TypedRecordEffectCoordinates :=
  fun i => if i.val < 8 then κ else 0

/-- Every scalar effect with `0 ≤ κ ≤ 1` is concretely feasible, including
the full `2 × 2` positivity and complement-positivity determinant tests. -/
theorem scalarTypedRecordEffect_feasible
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    TypedRecordEffectFeasible (scalarTypedRecordEffect κ) := by
  simp [TypedRecordEffectFeasible, scalarTypedRecordEffect, hκ0, hκ1]
  constructor <;> nlinarith [sq_nonneg κ, sq_nonneg (1 - κ)]

/-- Strictly interior conductance ratios give a feasible effect distinct from
both zero and identity. -/
theorem scalarTypedRecordEffect_interior
    (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    TypedRecordEffectFeasible (scalarTypedRecordEffect κ) ∧
      scalarTypedRecordEffect κ ≠ 0 ∧
      scalarTypedRecordEffect κ ≠ scalarTypedRecordEffect 1 := by
  refine ⟨scalarTypedRecordEffect_feasible κ hκ0.le hκ1.le, ?_, ?_⟩
  · intro hzero
    have h := congrFun hzero 0
    simp [scalarTypedRecordEffect] at h
    linarith
  · intro hone
    have h := congrFun hone 0
    simp [scalarTypedRecordEffect] at h
    linarith

/-- The concrete typed-effect spectrahedron is closed. -/
theorem typedRecordEffectFeasible_isClosed :
    IsClosed {x : TypedRecordEffectCoordinates | TypedRecordEffectFeasible x} := by
  unfold TypedRecordEffectFeasible
  simp only [Set.setOf_and]
  repeat' apply IsClosed.inter
  all_goals exact isClosed_le (by fun_prop) (by fun_prop)

/-- Every feasible coordinate has absolute value at most one.  For the
off-diagonal coordinates this follows from the `2 × 2` determinant test. -/
theorem typedRecordEffectFeasible_abs_le_one
    (x : TypedRecordEffectCoordinates) (hx : TypedRecordEffectFeasible x) :
    ∀ i, |x i| ≤ 1 := by
  rcases hx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hdet, hcomp⟩
  intro i
  fin_cases i
  · exact abs_le.2 ⟨(le_trans (by norm_num) h0.1), h0.2⟩
  · exact abs_le.2 ⟨(le_trans (by norm_num) h1.1), h1.2⟩
  · exact abs_le.2 ⟨(le_trans (by norm_num) h2.1), h2.2⟩
  · exact abs_le.2 ⟨(le_trans (by norm_num) h3.1), h3.2⟩
  · exact abs_le.2 ⟨(le_trans (by norm_num) h4.1), h4.2⟩
  · exact abs_le.2 ⟨(le_trans (by norm_num) h5.1), h5.2⟩
  · exact abs_le.2 ⟨(le_trans (by norm_num) h6.1), h6.2⟩
  · exact abs_le.2 ⟨(le_trans (by norm_num) h7.1), h7.2⟩
  · have hprod : x 6 * x 7 ≤ 1 := by
      nlinarith [h6.1, h6.2, h7.1, h7.2]
    have hsq : x 8 ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (x 9)]
    simpa using Real.abs_le_sqrt hsq
  · have hprod : x 6 * x 7 ≤ 1 := by
      nlinarith [h6.1, h6.2, h7.1, h7.2]
    have hsq : x 9 ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (x 8)]
    simpa using Real.abs_le_sqrt hsq

/-- The concrete typed-effect spectrahedron is bounded. -/
theorem typedRecordEffectFeasible_isBounded :
    Bornology.IsBounded
      {x : TypedRecordEffectCoordinates | TypedRecordEffectFeasible x} := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, ?_⟩
  intro x hx
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  simpa [Real.norm_eq_abs] using typedRecordEffectFeasible_abs_le_one x hx i

/-- Hence the typed-effect spectrahedron is compact. -/
theorem typedRecordEffectFeasible_isCompact :
    IsCompact {x : TypedRecordEffectCoordinates | TypedRecordEffectFeasible x} := by
  exact Metric.isCompact_iff_isClosed_bounded.2
    ⟨typedRecordEffectFeasible_isClosed, typedRecordEffectFeasible_isBounded⟩

end NCG
