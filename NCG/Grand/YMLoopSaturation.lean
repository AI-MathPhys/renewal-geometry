/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Primitive invariant-loop saturation
  (`thm:YM-primitive-loop-saturation`,
  Gran-Tensor manuscript)

* `ym_primitive_loop_saturation`: on the compact product
  of chord holonomies (after maximal-tree gauge
  reduction), a conjugation-closed loop algebra that
  separates points
  (i) is dense in the full continuous algebra —
      **Stone–Weierstrass** on the compact holonomy
      space, exactly the manuscript's density mechanism;
  (ii) is cyclic for the vacuum representation: its image
      under `ContinuousMap.toLp` is dense in
      `L²(μ)` for every finite regular vacuum measure —
      uniform density composed with `L²`-density of
      continuous functions, so the constant vacuum is a
      cyclic vector for the loop algebra.

The identification of the gauge-invariant lattice
algebra with `C(X, ℂ)` on the chord-holonomy product
(maximal-tree reduction, gauge averaging, and the
retained global cycle/centre-flux records — including
the necessity clause that contractible plaquettes miss
centre one-forms), and the unitary
`L²(|Ω|²dμ) ≅ 𝓗_phys` implemented by a strictly
positive vacuum, are the manuscript's gauge and
vacuum layers; the separation hypothesis is where the
defining-representation matrix coefficients enter.
-/

open MeasureTheory
open scoped ENNReal

namespace NCG

/-- `thm:YM-primitive-loop-saturation` (Stone–Weierstrass
density of the separating loop algebra, and its `L²`
cyclicity for every finite regular vacuum measure). -/
theorem ym_primitive_loop_saturation
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (A : StarSubalgebra ℂ C(X, ℂ))
    (hA : A.SeparatesPoints)
    (μ : Measure X) [μ.WeaklyRegular]
    [IsFiniteMeasure μ] :
    -- (i) the loop algebra is uniformly dense
    A.topologicalClosure = ⊤
    -- (ii) and `L²(μ)`-cyclic
    ∧ Dense ((ContinuousMap.toLp
        (E := ℂ) 2 μ ℂ) '' (A : Set C(X, ℂ)) :
        Set (Lp ℂ 2 μ)) := by
  have hdense :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      A hA
  refine ⟨hdense, ?_⟩
  have hAdense : Dense (A : Set C(X, ℂ)) := by
    rw [dense_iff_closure_eq]
    have hcl : closure (A : Set C(X, ℂ))
        = (A.topologicalClosure : Set C(X, ℂ)) := rfl
    rw [hcl, hdense]
    rfl
  have hrange : DenseRange (ContinuousMap.toLp
      (E := ℂ) 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ) :=
    ContinuousMap.toLp_denseRange ℂ μ ℂ
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  exact hrange.dense_image
    (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).continuous
    hAdense

end NCG
