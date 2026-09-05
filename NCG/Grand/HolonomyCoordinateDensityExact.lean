/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Instances.Matrix

/-!
# Density of concrete holonomy matrix coefficients

The writers here are the actual defining-representation entries of every
retained edge or chord holonomy. Separation is proved by matrix extensionality,
not supplied as a hypothesis. The result applies to any compact matrix-valued
configuration fibre, including unitary and special-unitary holonomies.

This is the unaveraged density step for `thm:YM-primitive-loop-saturation`.
Gauge reduction, gauge averaging, and the physical vacuum representation are
separate steps; no density of invariant writers is asserted in this file.
-/

open MeasureTheory
open scoped ENNReal

namespace NCG.HolonomyCoordinateDensity

noncomputable section

variable {E n : Type*} [Finite E]
variable (K : Set (Matrix n n ℂ)) [CompactSpace K]

/-- A retained holonomy's defining-representation matrix entry. -/
def coordinate (e : E) (i j : n) : C(E → K, ℂ) where
  toFun U := (U e).val i j
  continuous_toFun := by
    have hc : Continuous (fun U : E → K => (U e).val) :=
      continuous_subtype_val.comp (continuous_apply e)
    exact hc.matrix_elem i j

/-- Finite sums, products and adjoints of the retained matrix-entry writers. -/
def coordinateAlgebra : StarSubalgebra ℂ C(E → K, ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range fun a : E × n × n =>
    coordinate K a.1 a.2.1 a.2.2)

theorem coordinate_mem (e : E) (i j : n) :
    coordinate K e i j ∈ coordinateAlgebra (E := E) K :=
  StarAlgebra.subset_adjoin ℂ _ ⟨(e, i, j), rfl⟩

/-- Distinct configurations are distinguished by an actual retained entry. -/
theorem exists_coordinate_ne {U W : E → K} (hne : U ≠ W) :
    ∃ e i j, coordinate K e i j U ≠ coordinate K e i j W := by
  by_contra h
  push Not at h
  apply hne
  funext e
  apply Subtype.ext
  funext i j
  exact h e i j

/-- The concrete entry algebra separates configurations without an abstract
separation premise. -/
theorem coordinateAlgebra_separatesPoints :
    (coordinateAlgebra (E := E) K).SeparatesPoints := by
  intro U W hne
  obtain ⟨e, i, j, h⟩ := exists_coordinate_ne K hne
  exact ⟨coordinate K e i j,
    ⟨coordinate K e i j, coordinate_mem K e i j, rfl⟩, h⟩

/-- Uniform Stone–Weierstrass density for the concrete holonomy writers. -/
theorem coordinateAlgebra_topologicalClosure :
    (coordinateAlgebra (E := E) K).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    _ (coordinateAlgebra_separatesPoints K)

/-- The same explicit writers are dense for every finite regular Borel
vacuum measure on the compact holonomy configuration space. -/
theorem coordinateAlgebra_L2_dense
    [MeasurableSpace (E → K)] [BorelSpace (E → K)]
    (μ : Measure (E → K)) [μ.WeaklyRegular] [IsFiniteMeasure μ] :
    Dense ((ContinuousMap.toLp (E := ℂ) 2 μ ℂ) ''
      (coordinateAlgebra (E := E) K : Set C(E → K, ℂ)) :
      Set (Lp ℂ 2 μ)) := by
  have hdense : Dense (coordinateAlgebra (E := E) K : Set C(E → K, ℂ)) := by
    rw [dense_iff_closure_eq]
    change ((coordinateAlgebra (E := E) K).topologicalClosure :
      Set C(E → K, ℂ)) = Set.univ
    rw [coordinateAlgebra_topologicalClosure]
    rfl
  exact (ContinuousMap.toLp_denseRange ℂ μ ℂ
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).dense_image
    (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).continuous hdense

end

end NCG.HolonomyCoordinateDensity
