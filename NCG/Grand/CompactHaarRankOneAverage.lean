/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Normalized compact Haar averages of rank-one operators

Reusable infrastructure for the compact-group averages occurring in the
Gran--Tensor manuscript.  Mathlib supplies Haar measure for locally compact
groups, but its algebraic `Matrix.specialUnitaryGroup` does not carry a
compact-space instance.  We establish that instance in finite dimension,
normalize Haar measure on the whole compact group, and define the genuine
Bochner integral of a rank-one orbit.
-/

open Matrix MeasureTheory Set
open scoped InnerProductSpace

namespace NCG
namespace CompactHaarRankOneAverage

/-- The special unitary group in dimension four. -/
abbrev SU4 := Matrix.specialUnitaryGroup (Fin 4) ℂ

/-- The matrix-subtype topology on `SU(4)`.  The algebraic special-unitary
submonoid in Mathlib does not currently install this instance itself. -/
noncomputable instance su4TopologicalSpace : TopologicalSpace SU4 :=
  TopologicalSpace.induced Subtype.val inferInstance

/-- The induced topology makes the algebraic `SU(4)` subtype a topological group. -/
noncomputable instance su4IsTopologicalGroup : IsTopologicalGroup SU4 where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    exact (continuous_induced_dom.comp continuous_fst).mul
      (continuous_induced_dom.comp continuous_snd)
  continuous_inv := by
    apply continuous_induced_rng.mpr
    exact Continuous.star continuous_induced_dom

/-- The Borel measurable structure on `SU(4)`. -/
noncomputable instance su4MeasurableSpace : MeasurableSpace SU4 := borel SU4

noncomputable instance su4BorelSpace : BorelSpace SU4 := ⟨rfl⟩

private theorem isCompact_unitary_four :
    IsCompact (Matrix.unitaryGroup (Fin 4) ℂ : Set (Matrix (Fin 4) (Fin 4) ℂ)) := by
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset isClosed_unitary
  intro U hU
  rw [Set.mem_matrix]
  intro i j
  simpa [Metric.mem_closedBall, dist_zero_right] using
    entry_norm_bound_of_unitary hU i j

private theorem isClosed_specialUnitary_four :
    IsClosed (Matrix.specialUnitaryGroup (Fin 4) ℂ :
      Set (Matrix (Fin 4) (Fin 4) ℂ)) := by
  change IsClosed ((Matrix.unitaryGroup (Fin 4) ℂ :
    Set (Matrix (Fin 4) (Fin 4) ℂ)) ∩ {A | Matrix.det A = 1})
  exact isClosed_unitary.inter
    (isClosed_singleton.preimage continuous_id.matrix_det)

private theorem isCompact_specialUnitary_four :
    IsCompact (Matrix.specialUnitaryGroup (Fin 4) ℂ :
      Set (Matrix (Fin 4) (Fin 4) ℂ)) := by
  exact isCompact_unitary_four.of_isClosed_subset isClosed_specialUnitary_four
    Matrix.specialUnitaryGroup_le_unitaryGroup

/-- `SU(4)` is compact in its matrix topology. -/
noncomputable instance su4CompactSpace : CompactSpace SU4 :=
  isCompact_iff_compactSpace.mp isCompact_specialUnitary_four

/-- The whole compact group, regarded as the normalizing positive compact. -/
noncomputable def wholePositiveCompact (G : Type*) [TopologicalSpace G] [CompactSpace G] [One G] :
    TopologicalSpace.PositiveCompacts G :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Haar measure normalized to have total mass one. -/
noncomputable def normalizedHaar (G : Type*) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [CompactSpace G] : Measure G :=
  Measure.haarMeasure (wholePositiveCompact G)

/-- The normalized Haar measure has total mass one. -/
theorem normalizedHaar_univ (G : Type*) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [CompactSpace G] :
    normalizedHaar G Set.univ = 1 := by
  simpa [normalizedHaar, wholePositiveCompact] using
    (Measure.haarMeasure_self (K₀ := wholePositiveCompact G))

noncomputable instance normalizedHaarProbability (G : Type*) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [CompactSpace G] :
    IsProbabilityMeasure (normalizedHaar G) :=
  ⟨normalizedHaar_univ G⟩

noncomputable instance normalizedHaarLeftInvariant (G : Type*) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [CompactSpace G] :
    Measure.IsMulLeftInvariant (normalizedHaar G) := by
  unfold normalizedHaar
  infer_instance

variable {G E : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- A continuous unitary action on a finite-dimensional Hilbert space. -/
structure ContinuousUnitaryAction where
  act : G → E →L[ℂ] E
  continuous_act : Continuous fun p : G × E => act p.1 p.2
  one_act : act 1 = 1
  mul_act : ∀ g h, act (g * h) = (act g).comp (act h)
  inner_map : ∀ g x y, ⟪act g x, act g y⟫_ℂ = ⟪x, y⟫_ℂ

variable (ρ : ContinuousUnitaryAction (G := G) (E := E))

/-- The barycenter of a continuous unitary orbit with respect to normalized
Haar measure. -/
noncomputable def orbitMean
    (ρ : ContinuousUnitaryAction (G := G) (E := E)) (v : E) : E :=
  ∫ g : G, ρ.act g v ∂normalizedHaar G

private theorem orbit_integrable
    (ρ : ContinuousUnitaryAction (G := G) (E := E)) (v : E) :
    Integrable (fun g : G => ρ.act g v) (normalizedHaar G) := by
  have hc : Continuous (fun g : G => ρ.act g v) :=
    ρ.continuous_act.comp (continuous_id.prodMk continuous_const)
  exact integrableOn_univ.mp
    (hc.continuousOn.integrableOn_of_subset_isCompact isCompact_univ MeasurableSet.univ
      Subset.rfl (measure_ne_top (normalizedHaar G) Set.univ))

/-- The normalized Haar barycenter of an orbit is fixed by the action. -/
theorem orbitMean_invariant (h : G) (v : E) :
    ρ.act h (orbitMean ρ v) = orbitMean ρ v := by
  rw [orbitMean]
  calc
    ρ.act h (∫ g : G, ρ.act g v ∂normalizedHaar G) =
        ∫ g : G, ρ.act h (ρ.act g v) ∂normalizedHaar G :=
      (ContinuousLinearMap.integral_comp_comm _ (orbit_integrable ρ v)).symm
    _ = ∫ g : G, ρ.act (h * g) v ∂normalizedHaar G := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [ρ.mul_act, ContinuousLinearMap.comp_apply]
    _ = ∫ g : G, ρ.act g v ∂normalizedHaar G :=
      integral_mul_left_eq_self (μ := normalizedHaar G) (fun g : G => ρ.act g v) h

/-- Continuous linear functionals commute with the orbit barycenter. -/
theorem map_orbitMean (L : E →L[ℂ] ℂ) (v : E) :
    L (orbitMean ρ v) = ∫ g : G, L (ρ.act g v) ∂normalizedHaar G := by
  exact (ContinuousLinearMap.integral_comp_comm L (orbit_integrable ρ v)).symm

/-- The genuine normalized Haar average of the orbit rank-one operators
`|ρ(g)v⟩⟨ρ(g)v|`. -/
noncomputable def average (ρ : ContinuousUnitaryAction (G := G) (E := E)) (v : E) :
    E →L[ℂ] E :=
  ∫ g : G, InnerProductSpace.rankOne ℂ (ρ.act g v) (ρ.act g v) ∂normalizedHaar G

private theorem average_integrable (ρ : ContinuousUnitaryAction (G := G) (E := E)) (v : E) :
    Integrable (fun g : G => InnerProductSpace.rankOne ℂ (ρ.act g v) (ρ.act g v))
      (normalizedHaar G) := by
  have horbit : Continuous (fun g : G => ρ.act g v) :=
    ρ.continuous_act.comp (continuous_id.prodMk continuous_const)
  have hcontinuous : Continuous
      (fun g : G => InnerProductSpace.rankOne ℂ (ρ.act g v) (ρ.act g v)) := by
    rw [continuous_clm_apply]
    intro x
    simp only [InnerProductSpace.rankOne_apply]
    fun_prop
  exact integrableOn_univ.mp
    (hcontinuous.continuousOn.integrableOn_of_subset_isCompact isCompact_univ
      MeasurableSet.univ Subset.rfl (measure_ne_top (normalizedHaar G) Set.univ))

theorem average_apply (v x : E) :
    average ρ v x = ∫ g : G, ⟪ρ.act g v, x⟫_ℂ • ρ.act g v ∂normalizedHaar G := by
  rw [average, ContinuousLinearMap.integral_apply (average_integrable ρ v) x]
  apply integral_congr_ae
  filter_upwards [] with g
  simp [InnerProductSpace.rankOne_apply]

/-- If the tested vector has a constant inner product along the orbit, the
rank-one Haar average is that scalar times the orbit barycenter. -/
theorem average_apply_of_inner_eq (v x : E) (c : ℂ)
    (h : ∀ g : G, ⟪ρ.act g v, x⟫_ℂ = c) :
    average ρ v x = c • orbitMean ρ v := by
  rw [average_apply]
  simp_rw [h]
  rw [integral_smul]
  rfl

/-- A point-evaluation of the rank-one orbit is integrable. -/
private theorem averageVector_integrable
    (ρ : ContinuousUnitaryAction (G := G) (E := E)) (v x : E) :
    Integrable (fun g : G => ⟪ρ.act g v, x⟫_ℂ • ρ.act g v) (normalizedHaar G) := by
  have horbit : Continuous (fun g : G => ρ.act g v) :=
    ρ.continuous_act.comp (continuous_id.prodMk continuous_const)
  have hc : Continuous (fun g : G => ⟪ρ.act g v, x⟫_ℂ • ρ.act g v) := by
    fun_prop
  exact integrableOn_univ.mp
    (hc.continuousOn.integrableOn_of_subset_isCompact isCompact_univ MeasurableSet.univ
      Subset.rfl (measure_ne_top (normalizedHaar G) Set.univ))

/-- The Haar rank-one average intertwines the given unitary action. -/
theorem average_equivariant (h : G) (v x : E) :
    average ρ v (ρ.act h x) = ρ.act h (average ρ v x) := by
  rw [average_apply, average_apply]
  calc
    (∫ g : G, ⟪ρ.act g v, ρ.act h x⟫_ℂ • ρ.act g v ∂normalizedHaar G)
        = ∫ g : G, ⟪ρ.act (h * g) v, ρ.act h x⟫_ℂ • ρ.act (h * g) v
            ∂normalizedHaar G := by
          symm
          exact integral_mul_left_eq_self (μ := normalizedHaar G)
            (fun g : G => (⟪ρ.act g v, ρ.act h x⟫_ℂ • ρ.act g v : E)) h
    _ = ∫ g : G, ρ.act h (⟪ρ.act g v, x⟫_ℂ • ρ.act g v) ∂normalizedHaar G := by
          apply integral_congr_ae
          filter_upwards [] with g
          rw [ρ.mul_act, ContinuousLinearMap.comp_apply, ρ.inner_map,
            map_smul]
    _ = ρ.act h (∫ g : G, ⟪ρ.act g v, x⟫_ℂ • ρ.act g v ∂normalizedHaar G) :=
          ContinuousLinearMap.integral_comp_comm _ (averageVector_integrable ρ v x)

/-- A Haar average of positive rank-one operators is self-adjoint. -/
theorem average_inner_symmetric (v x y : E) :
    ⟪x, average ρ v y⟫_ℂ = ⟪average ρ v x, y⟫_ℂ := by
  rw [average_apply]
  rw [← integral_inner (averageVector_integrable ρ v y) x]
  rw [← inner_conj_symm]
  rw [average_apply]
  rw [← integral_inner (averageVector_integrable ρ v x) y]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with g
  rw [inner_smul_right]
  rw [inner_smul_right, map_mul,
    inner_conj_symm x (ρ.act g v), inner_conj_symm (ρ.act g v) y]
  exact mul_comm _ _

/-- The trace functional on continuous endomorphisms, bundled continuously in
finite dimension. -/
noncomputable def traceContinuous : (E →L[ℂ] E) →L[ℂ] ℂ :=
  ((LinearMap.trace ℂ E).comp (ContinuousLinearMap.coeLM ℂ)).toContinuousLinearMap

@[simp] theorem traceContinuous_apply (T : E →L[ℂ] E) :
    traceContinuous T = T.toLinearMap.trace ℂ E := by
  rfl

/-- The trace of a normalized Haar average of rank-one operators is the
squared norm of the seed. -/
theorem average_trace (v : E) :
    (average ρ v).toLinearMap.trace ℂ E = ⟪v, v⟫_ℂ := by
  rw [← traceContinuous_apply]
  rw [average]
  rw [← ContinuousLinearMap.integral_comp_comm traceContinuous (average_integrable ρ v)]
  simp_rw [traceContinuous_apply, InnerProductSpace.trace_rankOne, ρ.inner_map]
  simp

end CompactHaarRankOneAverage
end NCG
