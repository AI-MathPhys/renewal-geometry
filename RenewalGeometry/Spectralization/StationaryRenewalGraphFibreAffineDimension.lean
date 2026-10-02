/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.StationaryRenewalGraphCurrentFibreExact
import RenewalGeometry.Spectralization.NonlinearAffinityHodgeExact
/-!
# Affine dimension of the stationary current fibre

This file covers `cor:supp-fibre-dimension` of `predictive_spectral_geometry`
(revised 1 Oct 2026).  For a connected simple graph `G` presented by an
orientation, positive masses `m` and positive edge conductances `c`:

* the real cycle space `ker B ⊆ ℝ^E` has real dimension `|E| - |V| + 1 = b₁(G)`
  (`realCycleSpace_finrank`, via rank–nullity for `B` and `Bᵀ`);
* both the closed polytope `J̄(G,c)` and its relative interior `J(G,c)` have
  affine span equal to the real cycle space, hence affine dimension `b₁(G)`
  (`vectorSpan_currentPolytope`, `vectorSpan_closedCurrentPolytope`,
  `currentPolytope_affineDim`, `closedCurrentPolytope_affineDim`);
* the reversible realization is the only stationary realization exactly when
  `G` is a tree, `|E| + 1 = |V|` (`reversible_unique_iff_tree`);
* if `b₁(G) > 0` two distinct stationary realizations share the same
  Hodge–Dirac matrix (`spectralization_not_faithful`, re-exported).

The bundled statement is `fibre_affine_dimension_and_faithfulness`.
-/

open Matrix Finset

namespace RenewalGeometry
namespace StationaryRenewalGraphFibre
namespace SimpleOrientation

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : SimpleOrientation V E)

set_option linter.unusedSectionVars false

/-- The real cycle space `ker B ⊆ ℝ^E` of the oriented graph. -/
def realCycleSpace : Submodule ℝ (E → ℝ) :=
  LinearMap.ker G.incidenceReal.mulVecLin

theorem mem_realCycleSpace {j : E → ℝ} :
    j ∈ G.realCycleSpace ↔ G.incidenceReal *ᵥ j = 0 := by
  simp [realCycleSpace]

/-- For a connected graph the kernel of `Bᵀ` is the line of constants. -/
theorem ker_transpose_incidenceReal_finrank [Nonempty V] (hG : G.Connected) :
    Module.finrank ℝ (LinearMap.ker (G.incidenceRealᵀ).mulVecLin) = 1 := by
  have hB := NonlinearAffinityHodge.isConnectedIncidence_incidenceReal G hG
  have hker : LinearMap.ker (G.incidenceRealᵀ).mulVecLin =
      Submodule.span ℝ {fun _ : V => (1 : ℝ)} := by
    apply le_antisymm
    · intro φ hφ
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hφ
      obtain ⟨t, rfl⟩ := hB.eq_const_of_transpose_mulVec_eq_zero φ hφ
      rw [Submodule.mem_span_singleton]
      exact ⟨t, by funext x; simp⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      change _ ∈ LinearMap.ker _
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact hB.transpose_mulVec_one
  rw [hker, finrank_span_singleton]
  intro h
  have := congrFun h (Classical.arbitrary V)
  simp at this

/-- The real incidence matrix of a connected graph has rank `|V| - 1`. -/
theorem incidenceReal_rank [Nonempty V] (hG : G.Connected) :
    G.incidenceReal.rank = Fintype.card V - 1 := by
  have h1 := G.ker_transpose_incidenceReal_finrank hG
  have hrn := LinearMap.finrank_range_add_finrank_ker (G.incidenceRealᵀ).mulVecLin
  have hrank : (G.incidenceRealᵀ).rank = Fintype.card V - 1 := by
    rw [Matrix.rank]
    simp only [Module.finrank_fintype_fun_eq_card] at hrn
    omega
  rw [← Matrix.rank_transpose, hrank]

/-- **`eq:supp-fibre-dimension`, linear part.**  The real cycle space of a
connected graph has dimension `|E| - |V| + 1 = b₁(G)`. -/
theorem realCycleSpace_finrank [Nonempty V] (hG : G.Connected) :
    Module.finrank ℝ G.realCycleSpace = Fintype.card E + 1 - Fintype.card V := by
  have hrank := G.incidenceReal_rank hG
  have hrn := LinearMap.finrank_range_add_finrank_ker G.incidenceReal.mulVecLin
  simp only [Module.finrank_fintype_fun_eq_card] at hrn
  have hle : G.incidenceReal.rank ≤ Fintype.card E := Matrix.rank_le_card_width _
  have hV : 0 < Fintype.card V := Fintype.card_pos
  rw [Matrix.rank] at hrank hle
  change Module.finrank ℝ (LinearMap.ker G.incidenceReal.mulVecLin) = _
  omega

/-- A connected graph has at least `|V| - 1` edges. -/
theorem card_le_card_edges_add_one [Nonempty V] (hG : G.Connected) :
    Fintype.card V ≤ Fintype.card E + 1 := by
  have hrank := G.incidenceReal_rank hG
  have hle : G.incidenceReal.rank ≤ Fintype.card E := Matrix.rank_le_card_width _
  omega

/-- Every cycle current has a positive multiple in the open polytope. -/
theorem exists_pos_smul_mem_currentPolytope (c : E → ℝ) (hc : ∀ e, 0 < c e)
    {v : E → ℝ} (hv : G.incidenceReal *ᵥ v = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε • v ∈ G.currentPolytope c := by
  by_cases hE : Nonempty E
  · obtain ⟨e₀⟩ := hE
    obtain ⟨emin, -, hmin⟩ := Finset.exists_min_image univ c ⟨e₀, Finset.mem_univ e₀⟩
    set M : ℝ := ∑ e, |v e| with hM
    have hMnn : 0 ≤ M := Finset.sum_nonneg (fun e _ => abs_nonneg _)
    have hle : ∀ e, |v e| ≤ M := fun e =>
      Finset.single_le_sum (f := fun e => |v e|) (fun e _ => abs_nonneg _) (Finset.mem_univ e)
    have hM1 : M + 1 ≠ 0 := by linarith
    set ε : ℝ := c emin / (M + 1) with hε_def
    have hε : 0 < ε := div_pos (hc emin) (by linarith)
    refine ⟨ε, hε, ?_, ?_⟩
    · rw [Matrix.mulVec_smul, hv, smul_zero]
    · intro e
      rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hε]
      calc ε * |v e| ≤ ε * M := mul_le_mul_of_nonneg_left (hle e) hε.le
        _ < ε * (M + 1) := mul_lt_mul_of_pos_left (by linarith) hε
        _ = c emin := by rw [hε_def, div_mul_cancel₀ _ hM1]
        _ ≤ c e := hmin e (Finset.mem_univ e)
  · refine ⟨1, one_pos, ?_, fun e => (hE ⟨e⟩).elim⟩
    rw [one_smul, hv]

theorem currentPolytope_subset_realCycleSpace (c : E → ℝ) :
    G.currentPolytope c ⊆ G.realCycleSpace :=
  fun _ hj => (G.mem_realCycleSpace).mpr hj.1

theorem closedCurrentPolytope_subset_realCycleSpace (c : E → ℝ) :
    G.closedCurrentPolytope c ⊆ G.realCycleSpace :=
  fun _ hj => (G.mem_realCycleSpace).mpr hj.1

/-- The vector span of any set squeezed between the open polytope and the cycle
space is the cycle space. -/
theorem vectorSpan_eq_realCycleSpace_of_subset (c : E → ℝ) (hc : ∀ e, 0 < c e)
    {S : Set (E → ℝ)} (hS₁ : G.currentPolytope c ⊆ S) (hS₂ : S ⊆ G.realCycleSpace) :
    vectorSpan ℝ S = G.realCycleSpace := by
  apply le_antisymm
  · rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact G.realCycleSpace.sub_mem (hS₂ hx) (hS₂ hy)
  · intro v hv
    obtain ⟨ε, hε, hεv⟩ := G.exists_pos_smul_mem_currentPolytope c hc
      ((G.mem_realCycleSpace).mp hv)
    have h0 : (0 : E → ℝ) ∈ S := hS₁ (G.zero_mem_currentPolytope c hc)
    have hmem : ε • v -ᵥ (0 : E → ℝ) ∈ vectorSpan ℝ S :=
      vsub_mem_vectorSpan ℝ (hS₁ hεv) h0
    rw [vsub_eq_sub, sub_zero] at hmem
    have := (vectorSpan ℝ S).smul_mem ε⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hε.ne', one_smul] at this

/-- The affine span of the open polytope `J(G,c)` has direction the cycle space. -/
theorem vectorSpan_currentPolytope (c : E → ℝ) (hc : ∀ e, 0 < c e) :
    vectorSpan ℝ (G.currentPolytope c) = G.realCycleSpace :=
  G.vectorSpan_eq_realCycleSpace_of_subset c hc le_rfl
    (G.currentPolytope_subset_realCycleSpace c)

/-- The affine span of the closed polytope `J̄(G,c)` has direction the cycle space. -/
theorem vectorSpan_closedCurrentPolytope (c : E → ℝ) (hc : ∀ e, 0 < c e) :
    vectorSpan ℝ (G.closedCurrentPolytope c) = G.realCycleSpace :=
  G.vectorSpan_eq_realCycleSpace_of_subset c hc (G.currentPolytope_subset_closed c)
    (G.closedCurrentPolytope_subset_realCycleSpace c)

/-- **`cor:supp-fibre-dimension`, open fibre.**  The relative interior `J(G,c)`
has affine dimension `|E| - |V| + 1`. -/
theorem currentPolytope_affineDim [Nonempty V] (hG : G.Connected) (c : E → ℝ)
    (hc : ∀ e, 0 < c e) :
    Module.finrank ℝ (affineSpan ℝ (G.currentPolytope c)).direction =
      Fintype.card E + 1 - Fintype.card V := by
  rw [direction_affineSpan, G.vectorSpan_currentPolytope c hc, G.realCycleSpace_finrank hG]

/-- **`cor:supp-fibre-dimension`, closed fibre.**  The closed polytope
`J̄(G,c)` has affine dimension `|E| - |V| + 1`. -/
theorem closedCurrentPolytope_affineDim [Nonempty V] (hG : G.Connected) (c : E → ℝ)
    (hc : ∀ e, 0 < c e) :
    Module.finrank ℝ (affineSpan ℝ (G.closedCurrentPolytope c)).direction =
      Fintype.card E + 1 - Fintype.card V := by
  rw [direction_affineSpan, G.vectorSpan_closedCurrentPolytope c hc,
    G.realCycleSpace_finrank hG]

/-- **`cor:supp-fibre-dimension`, tree criterion.**  The reversible
realization `c/m` is the only stationary realization of `(m, G, c)` exactly
when the connected graph `G` is a tree, `|E| + 1 = |V|`. -/
theorem reversible_unique_iff_tree [Nonempty V] (hG : G.Connected) {m : V → ℝ}
    (hm : ∀ x, 0 < m x) (c : E → ℝ) (hc : ∀ e, 0 < c e) :
    (∀ k, G.IsRealization m c k → k = G.reversibleRates m c) ↔
      Fintype.card E + 1 = Fintype.card V := by
  have hdim := G.realCycleSpace_finrank hG
  have hle := G.card_le_card_edges_add_one hG
  constructor
  · intro huniq
    by_contra hne
    have hpos : 0 < Module.finrank ℝ G.realCycleSpace := by omega
    obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    obtain ⟨ε, hε, hεz⟩ := G.exists_pos_smul_mem_currentPolytope c hc
      ((G.mem_realCycleSpace).mp z.2)
    have hk := G.isRealization_rates hm c (G.currentPolytope_subset_closed c hεz)
    have heq := huniq _ hk
    have h0 : ε • (z : E → ℝ) = 0 := G.rates_injective hm c heq
    apply hz
    apply Subtype.ext
    simpa [hε.ne'] using h0
  · intro htree k hk
    have hzero : Module.finrank ℝ G.realCycleSpace = 0 := by omega
    have hbot : G.realCycleSpace = ⊥ := Submodule.finrank_eq_zero.mp hzero
    obtain ⟨j, ⟨hj, hkj⟩, -⟩ := hk.existsUnique_current hm
    have hj0 : j = 0 := by
      have : j ∈ G.realCycleSpace := G.closedCurrentPolytope_subset_realCycleSpace c hj
      rw [hbot] at this
      exact (Submodule.mem_bot ℝ).mp this
    rw [hkj, hj0]
    rfl

/-- **`cor:supp-fibre-dimension`** (revised statement).  For a connected simple
graph `G` with positive masses and positive edge conductances:
1. the closed polytope `J̄(G,c)` and its relative interior `J(G,c)` both have
   affine dimension `|E| - |V| + 1 = b₁(G)`;
2. the reversible realization is the only stationary realization exactly when
   `G` is a tree;
3. if `b₁(G) > 0`, two distinct stationary realizations have the same
   Hodge–Dirac matrix, so the metric passage to spectral data is not faithful. -/
theorem fibre_affine_dimension_and_faithfulness [Nonempty V] (hG : G.Connected)
    {m : V → ℝ} (hm : ∀ x, 0 < m x) (c : E → ℝ) (hc : ∀ e, 0 < c e) :
    Module.finrank ℝ (affineSpan ℝ (G.closedCurrentPolytope c)).direction =
        Fintype.card E + 1 - Fintype.card V ∧
      Module.finrank ℝ (affineSpan ℝ (G.currentPolytope c)).direction =
        Fintype.card E + 1 - Fintype.card V ∧
      ((∀ k, G.IsRealization m c k → k = G.reversibleRates m c) ↔
        Fintype.card E + 1 = Fintype.card V) ∧
      (Fintype.card V < Fintype.card E + 1 →
        ∃ j₁ ∈ G.currentPolytope c, ∃ j₂ ∈ G.currentPolytope c,
          G.rates m c j₁ ≠ G.rates m c j₂ ∧
          FiniteWeightedGraphHodgeDirac.dirac m
              (StationaryFluxAdjoint.symmetrizedConductance
                (fun x y => m x * G.rates m c j₁ x y)) =
            FiniteWeightedGraphHodgeDirac.dirac m
              (StationaryFluxAdjoint.symmetrizedConductance
                (fun x y => m x * G.rates m c j₂ x y))) :=
  ⟨G.closedCurrentPolytope_affineDim hG c hc, G.currentPolytope_affineDim hG c hc,
    G.reversible_unique_iff_tree hG hm c hc,
    fun hb => G.spectralization_not_faithful hG hm c hc hb⟩

/-- Non-vacuity witness: the one-vertex tree satisfies every hypothesis of
`fibre_affine_dimension_and_faithfulness`. -/
example : ∃ G : SimpleOrientation Unit Empty, G.Connected ∧
    (∀ x : Unit, 0 < (fun _ => (1 : ℝ)) x) ∧ ∀ e : Empty, 0 < (Empty.elim e : ℝ) :=
  ⟨⟨Empty.elim, Empty.elim, fun e => e.elim, fun e => e.elim⟩,
    fun x y => by cases x; cases y; exact Relation.ReflTransGen.refl,
    fun _ => one_pos, fun e => e.elim⟩

end SimpleOrientation
end StationaryRenewalGraphFibre
end RenewalGeometry
