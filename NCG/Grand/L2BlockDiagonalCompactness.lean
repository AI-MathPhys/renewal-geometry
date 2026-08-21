/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.L2BlockDiagonalScreens
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Compact finite screens for block-diagonal `ℓ²` operators

When the fibre is finite-dimensional, every finite coordinate screen on an
`ℓ²` direct sum is compact.  Consequently any operator that is approximated
in operator norm by its finite-screen compressions is compact.
-/

open Filter Topology
open scoped lp

noncomputable section

namespace NCG

variable {ι E : Type*}
variable [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Projection onto a single coordinate of an `ℓ²` direct sum. -/
def l2CoordinateProjection (i : ι) : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E) :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ι ↦ E) 2 i).comp
    (lp.evalCLM ℂ (fun _ : ι ↦ E) 2 i)

@[simp]
theorem l2CoordinateProjection_apply
    (i : ι) (f : ℓ²(ι, E)) (j : ι) :
    l2CoordinateProjection i f j = if j = i then f i else 0 := by
  change (Pi.single i (f i) : ι → E) j = _
  rw [Pi.single_apply]

/-- A finite coordinate screen is the sum of its one-coordinate
projections. -/
theorem l2FinsetScreen_eq_sum_coordinateProjections (s : Finset ι) :
    l2FinsetScreen (E := E) s =
      ∑ i ∈ s, l2CoordinateProjection (E := E) i := by
  ext f j
  rw [l2FinsetScreen_apply]
  rw [sum_apply]
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp_rw [l2CoordinateProjection_apply]
  by_cases hj : j ∈ s <;> simp [hj]

/-- A one-coordinate projection is compact when the fibre is
finite-dimensional. -/
theorem l2CoordinateProjection_isCompactOperator
    [FiniteDimensional ℂ E] (i : ι) :
    IsCompactOperator
      ((l2CoordinateProjection (E := E) i : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E)) :
        ℓ²(ι, E) → ℓ²(ι, E)) := by
  have hEval : IsCompactOperator
      ((lp.evalCLM ℂ (fun _ : ι ↦ E) 2 i : ℓ²(ι, E) →L[ℂ] E) :
        ℓ²(ι, E) → E) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact hEval.clm_comp
    (lp.singleContinuousLinearMap ℂ (fun _ : ι ↦ E) 2 i)

/-- Every finite coordinate screen is compact when the fibre is
finite-dimensional. -/
theorem l2FinsetScreen_isCompactOperator
    [FiniteDimensional ℂ E] (s : Finset ι) :
    IsCompactOperator
      ((l2FinsetScreen (E := E) s : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E)) :
        ℓ²(ι, E) → ℓ²(ι, E)) := by
  rw [l2FinsetScreen_eq_sum_coordinateProjections]
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact isCompactOperator_zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (l2CoordinateProjection_isCompactOperator (E := E) i).add ih

/-- Compressing any bounded operator by a finite coordinate screen gives a
compact operator. -/
theorem screenCompression_l2FinsetScreen_isCompactOperator
    [FiniteDimensional ℂ E]
    (s : Finset ι) (T : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E)) :
    IsCompactOperator
      ((screenCompression (l2FinsetScreen (E := E) s) T :
          ℓ²(ι, E) →L[ℂ] ℓ²(ι, E)) :
        ℓ²(ι, E) → ℓ²(ι, E)) := by
  have hs := l2FinsetScreen_isCompactOperator (E := E) s
  exact (hs.clm_comp T).clm_comp (l2FinsetScreen (E := E) s)

/-- An operator is compact if a sequence of finite coordinate
compressions approximates it at the canonical `1/(n+1)` rate. -/
theorem isCompactOperator_of_finsetScreen_compression_approx
    [FiniteDimensional ℂ E]
    (T : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E))
    (s : ℕ → Finset ι)
    (happrox : ∀ n,
      ‖T - screenCompression (l2FinsetScreen (E := E) (s n)) T‖ <
        1 / ((n + 1 : ℕ) : ℝ)) :
    IsCompactOperator (T : ℓ²(ι, E) → ℓ²(ι, E)) := by
  have hTendsto :
      Tendsto
        (fun n ↦ screenCompression (l2FinsetScreen (E := E) (s n)) T)
        atTop (𝓝 T) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hev :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (Iio_mem_nhds hε)
    rw [eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun n hn ↦ ?_⟩
    have happ := happrox n
    rw [Nat.cast_add, Nat.cast_one] at happ
    simpa only [dist_eq_norm, norm_sub_rev] using
      happ.trans (hN n hn)
  apply isCompactOperator_of_tendsto hTendsto
  exact Eventually.of_forall fun n ↦
    screenCompression_l2FinsetScreen_isCompactOperator (E := E) (s n) T

/-- The epsilon-form finite-screen approximation criterion for compactness. -/
theorem isCompactOperator_of_finsetScreen_compression_approx_arbitrarily
    [FiniteDimensional ℂ E]
    (T : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E))
    (happrox : ∀ ε, 0 < ε → ∃ s : Finset ι,
      ‖T - screenCompression (l2FinsetScreen (E := E) s) T‖ < ε) :
    IsCompactOperator (T : ℓ²(ι, E) → ℓ²(ι, E)) := by
  choose s hs using fun n : ℕ ↦
    happrox (1 / ((n + 1 : ℕ) : ℝ)) (by positivity)
  exact isCompactOperator_of_finsetScreen_compression_approx T s hs

end NCG
