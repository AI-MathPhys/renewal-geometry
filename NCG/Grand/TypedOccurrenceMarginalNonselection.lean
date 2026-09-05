/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TypedRecordCommutantCoordinates

/-!
# Typed occurrence marginals do not select the joint occurrence effect

This file proves `cth:SM-occurrence-marginal-nonselection` in the literal
ten-real-coordinate model of the typed-record commutant.  The feasible effect
set is compact, one nonzero conductance equation has a nine-dimensional
tangent kernel, and the scalar solution is an interior point of the effect
spectrahedron.  Thus the conductance slice has the asserted affine dimension
rather than merely an abstract rank-nullity count.
-/

namespace NCG

/-- The concrete fixed-conductance slice of typed-record-compatible effects. -/
def TypedOccurrenceConductanceSlice (g : Fin 10 → ℝ) (c : ℝ) :
    Set TypedRecordEffectCoordinates :=
  {x | TypedRecordEffectFeasible x ∧ typedConductanceFunctional g x = c}

/-- A fixed conductance cuts the compact effect spectrahedron by a closed
affine hyperplane, so the resulting spectrahedron is compact. -/
theorem typedOccurrenceConductanceSlice_isCompact (g : Fin 10 → ℝ) (c : ℝ) :
    IsCompact (TypedOccurrenceConductanceSlice g c) := by
  have hc : IsClosed
      {x : TypedRecordEffectCoordinates | typedConductanceFunctional g x = c} :=
    isClosed_eq
      (typedConductanceFunctional g).continuous_of_finiteDimensional continuous_const
  change IsCompact
    ({x : TypedRecordEffectCoordinates | TypedRecordEffectFeasible x} ∩
      {x : TypedRecordEffectCoordinates | typedConductanceFunctional g x = c})
  exact IsCompact.inter_right typedRecordEffectFeasible_isCompact hc

/-- Scalar effects are scalar multiples of the identity effect in coordinates. -/
theorem scalarTypedRecordEffect_eq_smul_identity (k : ℝ) :
    scalarTypedRecordEffect k = k • scalarTypedRecordEffect 1 := by
  funext i
  simp only [scalarTypedRecordEffect, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- If the identity has total conductance `t`, the scalar ratio `c/t` has
conductance `c`. -/
theorem scalarTypedRecordEffect_conductance
    (g : Fin 10 → ℝ) (t c : ℝ) (ht : t ≠ 0)
    (hidentity : typedConductanceFunctional g (scalarTypedRecordEffect 1) = t) :
    typedConductanceFunctional g (scalarTypedRecordEffect (c / t)) = c := by
  rw [scalarTypedRecordEffect_eq_smul_identity,
    LinearMap.map_smul, hidentity, smul_eq_mul, div_mul_cancel₀ c ht]

/-- A strict scalar effect has an explicit open coordinate box contained in
the concrete effect spectrahedron.  This verifies positivity of both the
Hermitian `2 × 2` block and its complement under small perturbations. -/
theorem scalarTypedRecordEffect_has_feasible_coordinate_box
    (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    ∃ ε > 0, ∀ x : TypedRecordEffectCoordinates,
      (∀ i, |x i - scalarTypedRecordEffect k i| < ε) →
      TypedRecordEffectFeasible x := by
  let ε := min k (1 - k) / 4
  have hε0 : 0 < ε := by
    dsimp [ε]
    positivity
  have hεk : ε ≤ k / 4 := by
    dsimp [ε]
    gcongr
    exact min_le_left _ _
  have hεc : ε ≤ (1 - k) / 4 := by
    dsimp [ε]
    gcongr
    exact min_le_right _ _
  refine ⟨ε, hε0, ?_⟩
  intro x hbox
  have h0 : k < ε + x 0 ∧ x 0 - k < ε := by
    simpa [scalarTypedRecordEffect, abs_lt] using hbox 0
  have h1 : k < ε + x 1 ∧ x 1 - k < ε := by
    simpa [scalarTypedRecordEffect, abs_lt] using hbox 1
  have h2 : k < ε + x 2 ∧ x 2 - k < ε := by
    simpa [scalarTypedRecordEffect, abs_lt] using hbox 2
  have h3 : k < ε + x 3 ∧ x 3 - k < ε := by
    simpa [scalarTypedRecordEffect, abs_lt] using hbox 3
  have h4 : k < ε + x 4 ∧ x 4 - k < ε := by
    simpa [scalarTypedRecordEffect, abs_lt] using hbox 4
  have h5 : k < ε + x 5 ∧ x 5 - k < ε := by
    simpa [scalarTypedRecordEffect, abs_lt] using hbox 5
  have h6 : k < ε + x 6 ∧ x 6 - k < ε := by
    simpa [scalarTypedRecordEffect, abs_lt] using hbox 6
  have h7 : k < ε + x 7 ∧ x 7 - k < ε := by
    simpa [scalarTypedRecordEffect, abs_lt] using hbox 7
  have h8 : -ε < x 8 ∧ x 8 < ε := by
    simpa [scalarTypedRecordEffect, abs_lt] using hbox 8
  have h9 : -ε < x 9 ∧ x 9 < ε := by
    simpa [scalarTypedRecordEffect, abs_lt] using hbox 9
  have hscalar (a : ℝ) (ha : k < ε + a ∧ a - k < ε) :
      0 ≤ a ∧ a ≤ 1 := by
    constructor <;> linarith only [ha.1, ha.2, hk0, hk1, hεk, hεc]
  have hs0 := hscalar (x 0) h0
  have hs1 := hscalar (x 1) h1
  have hs2 := hscalar (x 2) h2
  have hs3 := hscalar (x 3) h3
  have hs4 := hscalar (x 4) h4
  have hs5 := hscalar (x 5) h5
  have hs6 := hscalar (x 6) h6
  have hs7 := hscalar (x 7) h7
  refine ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, ?_, ?_⟩
  · have hz8 : x 8 ^ 2 < ε ^ 2 := by
      have hp : 0 < (ε - x 8) * (ε + x 8) :=
        mul_pos (by linarith [h8.2]) (by linarith [h8.1])
      nlinarith only [hp]
    have hz9 : x 9 ^ 2 < ε ^ 2 := by
      have hp : 0 < (ε - x 9) * (ε + x 9) :=
        mul_pos (by linarith [h9.2]) (by linarith [h9.1])
      nlinarith only [hp]
    have hbudget : 2 * ε ^ 2 ≤ (k - ε) ^ 2 := by
      have hp : 0 ≤ (k - 4 * ε) * (k + 2 * ε) :=
        mul_nonneg (by linarith [hεk]) (by linarith)
      nlinarith only [hp, sq_nonneg ε]
    have hlower6 : k - ε < x 6 := by linarith only [h6.1]
    have hlower7 : k - ε < x 7 := by linarith only [h7.1]
    have hbase : 0 < k - ε := by linarith only [hk0, hεk]
    have hproduct : (k - ε) ^ 2 < x 6 * x 7 := by
      calc
        (k - ε) ^ 2 = (k - ε) * (k - ε) := by ring
        _ < (k - ε) * x 7 := mul_lt_mul_of_pos_left hlower7 hbase
        _ < x 6 * x 7 :=
          mul_lt_mul_of_pos_right hlower6 (by linarith only [hlower7, hbase])
    linarith only [hz8, hz9, hbudget, hproduct]
  · have hz8 : x 8 ^ 2 < ε ^ 2 := by
      have hp : 0 < (ε - x 8) * (ε + x 8) :=
        mul_pos (by linarith [h8.2]) (by linarith [h8.1])
      nlinarith only [hp]
    have hz9 : x 9 ^ 2 < ε ^ 2 := by
      have hp : 0 < (ε - x 9) * (ε + x 9) :=
        mul_pos (by linarith [h9.2]) (by linarith [h9.1])
      nlinarith only [hp]
    have hbudget : 2 * ε ^ 2 ≤ (1 - k - ε) ^ 2 := by
      have hp : 0 ≤ (1 - k - 4 * ε) * (1 - k + 2 * ε) :=
        mul_nonneg (by linarith [hεc]) (by linarith)
      nlinarith only [hp, sq_nonneg ε]
    have hlower6 : 1 - k - ε < 1 - x 6 := by linarith only [h6.2]
    have hlower7 : 1 - k - ε < 1 - x 7 := by linarith only [h7.2]
    have hbase : 0 < 1 - k - ε := by linarith only [hk1, hεc]
    have hproduct : (1 - k - ε) ^ 2 < (1 - x 6) * (1 - x 7) := by
      calc
        (1 - k - ε) ^ 2 = (1 - k - ε) * (1 - k - ε) := by ring
        _ < (1 - k - ε) * (1 - x 7) :=
          mul_lt_mul_of_pos_left hlower7 hbase
        _ < (1 - x 6) * (1 - x 7) :=
          mul_lt_mul_of_pos_right hlower6 (by linarith only [hlower7, hbase])
    linarith only [hz8, hz9, hbudget, hproduct]

/-- `cth:SM-occurrence-marginal-nonselection`, in the concrete typed-record
commutant.  The four clauses say respectively that the feasible conductance
slice is compact, its affine tangent has dimension nine, the scalar solution
belongs to the slice and has a genuine ambient feasible neighbourhood, and
the whole conductance fibre through it is exactly the translate of that
nine-dimensional kernel.  Together these are the spectrahedron and affine-
dimension assertions used to conclude that typed and colour marginals do not
select the fine occurrence correlation. -/
theorem typedOccurrence_marginal_nonselection
    (g : Fin 10 → ℝ) (hg : g ≠ 0) (total c : ℝ)
    (htotal : 0 < total) (hc0 : 0 < c) (hctotal : c < total)
    (hidentity :
      typedConductanceFunctional g (scalarTypedRecordEffect 1) = total) :
    IsCompact (TypedOccurrenceConductanceSlice g c) ∧
      Module.finrank ℝ (LinearMap.ker (typedConductanceFunctional g)) = 9 ∧
      scalarTypedRecordEffect (c / total) ∈
        TypedOccurrenceConductanceSlice g c ∧
      (∃ ε > 0, ∀ x : TypedRecordEffectCoordinates,
        (∀ i, |x i - scalarTypedRecordEffect (c / total) i| < ε) →
          TypedRecordEffectFeasible x) ∧
      (∀ x : TypedRecordEffectCoordinates,
        typedConductanceFunctional g x = c ↔
          x - scalarTypedRecordEffect (c / total) ∈
            LinearMap.ker (typedConductanceFunctional g)) := by
  have htotal_ne : total ≠ 0 := ne_of_gt htotal
  have hk0 : 0 < c / total := div_pos hc0 htotal
  have hk1 : c / total < 1 := (div_lt_one htotal).2 hctotal
  have hconductance :
      typedConductanceFunctional g (scalarTypedRecordEffect (c / total)) = c :=
    scalarTypedRecordEffect_conductance g total c htotal_ne hidentity
  refine ⟨typedOccurrenceConductanceSlice_isCompact g c,
    typedConductanceKernel_finrank_nine g hg, ?_,
    scalarTypedRecordEffect_has_feasible_coordinate_box (c / total) hk0 hk1, ?_⟩
  · exact ⟨scalarTypedRecordEffect_feasible (c / total) hk0.le hk1.le,
      hconductance⟩
  · intro x
    constructor
    · intro hx
      apply (typedConductance_fibre_difference_iff g x
        (scalarTypedRecordEffect (c / total))).mp
      exact hx.trans hconductance.symm
    · intro hx
      have hsame := (typedConductance_fibre_difference_iff g x
        (scalarTypedRecordEffect (c / total))).mpr hx
      exact hsame.trans hconductance

end NCG
