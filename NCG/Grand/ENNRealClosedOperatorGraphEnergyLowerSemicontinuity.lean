/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealOperatorGraphEnergy
import NCG.Grand.ClosedLinearPMapMixedLimit
import NCG.Grand.VaryingHilbertWeakNormLowerSemicontinuity
import Mathlib.Analysis.Real.Sqrt

/-!
# Lower semicontinuity of closed-operator graph energies

For a closed operator into a separable Hilbert space, bounded graph energy gives a weakly
convergent subsequence of operator values.  Weak closedness of the graph identifies its limit,
and weak lower semicontinuity of the norm closes the energy epigraph.
-/

open Set Filter Topology
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
  [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]
  [CompleteSpace F] [TopologicalSpace.SeparableSpace F]

/-- The partial linear map associated with an algebraic operator on a submodule domain. -/
def operatorLinearPMap (D : Submodule K E) (A : D →ₗ[K] F) : E →ₗ.[K] F :=
  ⟨D, A⟩

omit [CompleteSpace E] [CompleteSpace F] [TopologicalSpace.SeparableSpace F] in
@[simp] theorem operatorLinearPMap_domain (D : Submodule K E) (A : D →ₗ[K] F) :
    (operatorLinearPMap D A).domain = D :=
  rfl

omit [CompleteSpace E] [CompleteSpace F] [TopologicalSpace.SeparableSpace F] in
@[simp] theorem operatorLinearPMap_apply
    (D : Submodule K E) (A : D →ₗ[K] F) (x : D) :
    operatorLinearPMap D A x = A x :=
  rfl

omit [CompleteSpace E] in
/-- The extended squared energy of a norm-closed partial operator is lower semicontinuous. -/
theorem lowerSemicontinuous_ennrealOperatorGraphEnergy_of_isClosed
    (D : Submodule K E) (A : D →ₗ[K] F)
    (hclosed : (operatorLinearPMap D A).IsClosed) :
    LowerSemicontinuous (ennrealOperatorGraphEnergy D A) := by
  apply lowerSemicontinuous_iff_isClosed_epigraph.mpr
  apply IsSeqClosed.isClosed
  intro u p hu hup
  by_cases hpTop : p.2 = ∞
  · simp [hpTop]
  have hxAll : Tendsto (fun n ↦ (u n).1) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hup
  have hrAll : Tendsto (fun n ↦ (u n).2) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hup
  have hrFiniteEventually : ∀ᶠ n in atTop, (u n).2 < ∞ :=
    hrAll.eventually (eventually_lt_nhds (lt_top_iff_ne_top.mpr hpTop))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hrFiniteEventually
  let xs : ℕ → E := fun n ↦ (u (N + n)).1
  let rs : ℕ → ENNReal := fun n ↦ (u (N + n)).2
  have hrsFinite (n : ℕ) : rs n ≠ ∞ :=
    ne_of_lt (hN (N + n) (Nat.le_add_right N n))
  have henergyLe (n : ℕ) : ennrealOperatorGraphEnergy D A (xs n) ≤ rs n :=
    hu (N + n)
  have hxsMem (n : ℕ) : xs n ∈ D := by
    rw [← ennrealOperatorGraphEnergy_ne_top_iff D A]
    exact ne_top_of_le_ne_top (hrsFinite n) (henergyLe n)
  have hrToReal : Tendsto (fun n ↦ ((u n).2).toReal) atTop (𝓝 p.2.toReal) :=
    (ENNReal.continuousAt_toReal hpTop).tendsto.comp hrAll
  obtain ⟨C, hC⟩ :=
    (Metric.isBounded_range_of_tendsto _ hrToReal).exists_norm_le
  have hCnonneg : 0 ≤ C := by
    exact (norm_nonneg (((u 0).2).toReal)).trans (hC _ ⟨0, rfl⟩)
  let ys : ℕ → F := fun n ↦ A ⟨xs n, hxsMem n⟩
  have hysSq (n : ℕ) : ‖ys n‖ ^ 2 ≤ (rs n).toReal := by
    have htoReal := ENNReal.toReal_mono (hrsFinite n) (henergyLe n)
    simpa [ys, ennrealOperatorGraphEnergy_toReal D A (xs n) (hxsMem n)] using htoReal
  have hysBound (n : ℕ) : ‖ys n‖ ≤ Real.sqrt C := by
    apply Real.le_sqrt_of_sq_le
    exact (hysSq n).trans <| by
      have habs := hC ((rs n).toReal) ⟨N + n, rfl⟩
      simpa [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using habs
  obtain ⟨ylim, ψ, hψ, hyWeak⟩ :=
    NCG.exists_tendsto_toWeakSpace_subsequence_of_bounded
      (K := K) (E := F) ys (Real.sqrt C) hysBound
  have hxShift : Tendsto xs atTop (𝓝 p.1) := by
    have htail : Tendsto (fun n : ℕ ↦ N + n) atTop atTop :=
      (tendsto_add_atTop_nat N).congr (fun n ↦ Nat.add_comm n N)
    exact hxAll.comp htail
  have hxSub : Tendsto (fun k ↦ xs (ψ k)) atTop (𝓝 p.1) :=
    hxShift.comp hψ.tendsto_atTop
  have hgraphSeq : ∀ k, (xs (ψ k), ys (ψ k)) ∈ (operatorLinearPMap D A).graph := by
    intro k
    exact (operatorLinearPMap D A).mem_graph ⟨xs (ψ k), hxsMem (ψ k)⟩
  have hlimitGraph : (p.1, ylim) ∈ (operatorLinearPMap D A).graph :=
    LinearPMap.IsClosed.mem_graph_of_strong_weak_limit hclosed
      (Eventually.of_forall hgraphSeq) hxSub hyWeak
  rw [LinearPMap.mem_graph_iff] at hlimitGraph
  rcases hlimitGraph with ⟨xD, hxD, hAxD⟩
  have hpMem : p.1 ∈ D := by
    rw [← hxD]
    exact xD.property
  have hxDEq : xD = ⟨p.1, hpMem⟩ := Subtype.ext hxD
  have hAylim : A ⟨p.1, hpMem⟩ = ylim := by
    simpa [operatorLinearPMap, hxDEq] using hAxD
  have hyInner :
      (VaryingHilbert.constantSystem K F).WeaklyConverges
        (fun k ↦ ys (ψ k)) ylim := by
    intro z
    change Tendsto (fun k ↦ inner K (ys (ψ k)) z) atTop
      (𝓝 (inner K ylim z))
    have heval := NCG.tendsto_apply_of_tendsto_toWeakSpace hyWeak
      (innerSL K z)
    change Tendsto (fun k ↦ inner K z (ys (ψ k))) atTop
      (𝓝 (inner K z ylim)) at heval
    have hconj := (RCLike.continuous_conj.tendsto (inner K z ylim)).comp heval
    change Tendsto (fun k ↦ (starRingEnd K) (inner K z (ys (ψ k)))) atTop
      (𝓝 ((starRingEnd K) (inner K z ylim))) at hconj
    simpa only [inner_conj_symm] using hconj
  have hyNormSq := hyInner.norm_sq_le_liminf
    (VaryingHilbert.constantSystem K F) (Real.sqrt C) (fun k ↦ hysBound (ψ k))
  have hrSub : Tendsto (fun k ↦ (rs (ψ k)).toReal) atTop (𝓝 p.2.toReal) := by
    have htail : Tendsto (fun n : ℕ ↦ N + n) atTop atTop :=
      (tendsto_add_atTop_nat N).congr (fun n ↦ Nat.add_comm n N)
    exact hrToReal.comp (htail.comp hψ.tendsto_atTop)
  have hliminfCompare :
      liminf (fun k ↦ ‖ys (ψ k)‖ ^ 2) atTop ≤
        liminf (fun k ↦ (rs (ψ k)).toReal) atTop := by
    exact liminf_le_liminf (Eventually.of_forall fun k ↦ hysSq (ψ k))
      (hu := isBoundedUnder_of ⟨0, fun k ↦ sq_nonneg ‖ys (ψ k)‖⟩)
      (hv := hrSub.isCoboundedUnder_ge)
  have hnormSq : ‖ylim‖ ^ 2 ≤ p.2.toReal := by
    calc
      ‖ylim‖ ^ 2 ≤ liminf (fun k ↦ ‖ys (ψ k)‖ ^ 2) atTop := hyNormSq
      _ ≤ liminf (fun k ↦ (rs (ψ k)).toReal) atTop := hliminfCompare
      _ = p.2.toReal := hrSub.liminf_eq
  change ennrealOperatorGraphEnergy D A p.1 ≤ p.2
  rw [ennrealOperatorGraphEnergy]
  split
  · rename_i hpMem'
    have hsub : (⟨p.1, hpMem'⟩ : D) = ⟨p.1, hpMem⟩ := Subtype.ext rfl
    rw [hsub, hAylim]
    exact ENNReal.ofReal_le_of_le_toReal hnormSq
  · rename_i hpNotMem
    exact (hpNotMem hpMem).elim

end NCG.VaryingHilbert
