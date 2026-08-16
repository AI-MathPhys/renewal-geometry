/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AFInductiveLimitState

/-!
# Projective compactness of finite-stage C-star states

This file proves the simultaneous diagonal compactness statement used in the Gran-Tensor
manuscript.  A sequence of arbitrary states on an increasing sequence of finite-dimensional
C-star algebras has one subsequence whose restrictions converge on every fixed stage.  The
limits are states, are compatible with all connecting maps, and therefore define a unique state
on the completed AF inductive limit.
-/

open scoped CStarAlgebra ComplexOrder

noncomputable section

namespace NCG.PreCStarDirectLimit

open Filter Topology

universe v

variable {A : ℕ → Type v} [∀ n, CStarAlgebra (A n)]
variable [∀ n, FiniteDimensional ℂ (A n)]
variable (f : ∀ m n, m ≤ n → A m →⋆ₐ[ℂ] A n)
variable [DirectedSystem A (fun m n hmn ↦ f m n hmn)] [IsometricSystem f]

/-- The compact closed unit ball in the continuous dual of one finite-dimensional stage. -/
abbrev StageDualBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :=
  Metric.closedBall (0 : E →L[ℂ] ℂ) 1

noncomputable instance stageDualBallCompactSpace (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] : CompactSpace (StageDualBall E) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E →L[ℂ] ℂ) 1)

/-- A connecting star-algebra homomorphism, bundled as a continuous linear contraction. -/
private def embeddingCLM {m n : ℕ} (hmn : m ≤ n) : A m →L[ℂ] A n :=
  (f m n hmn).toLinearMap.mkContinuous 1 fun a ↦ by
    change ‖f m n hmn a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le (f m n hmn) a

omit [∀ n, FiniteDimensional ℂ (A n)]
  [DirectedSystem A (fun m n hmn ↦ f m n hmn)] [IsometricSystem f] in
@[simp]
private theorem embeddingCLM_apply {m n : ℕ} (hmn : m ≤ n) (a : A m) :
    embeddingCLM f hmn a = f m n hmn a :=
  rfl

/-- Restrict the state at stage `n` to stage `m`; before `n` reaches `m`, use the state already
present at stage `m`.  The latter branch affects only finitely many terms. -/
def restrictedStateFunctional (ω : ∀ n, NCG.PreCStarState (A n)) (n m : ℕ) :
    A m →L[ℂ] ℂ :=
  if hmn : m ≤ n then
    (ω n).toContinuousLinearMap.comp (embeddingCLM f hmn)
  else
    (ω m).toContinuousLinearMap

omit [∀ n, FiniteDimensional ℂ (A n)]
  [DirectedSystem A (fun m n hmn ↦ f m n hmn)] [IsometricSystem f] in
@[simp]
theorem restrictedStateFunctional_of_le (ω : ∀ n, NCG.PreCStarState (A n))
    {n m : ℕ} (hmn : m ≤ n) (a : A m) :
    restrictedStateFunctional f ω n m a = ω n (f m n hmn a) := by
  simp only [restrictedStateFunctional, dif_pos hmn, ContinuousLinearMap.comp_apply,
    embeddingCLM_apply]

omit [∀ n, FiniteDimensional ℂ (A n)]
  [DirectedSystem A (fun m n hmn ↦ f m n hmn)] [IsometricSystem f] in
private theorem norm_restrictedStateFunctional_le (ω : ∀ n, NCG.PreCStarState (A n))
    (n m : ℕ) : ‖restrictedStateFunctional f ω n m‖ ≤ 1 := by
  by_cases hmn : m ≤ n
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    rw [restrictedStateFunctional_of_le f ω hmn]
    calc
      ‖ω n (f m n hmn a)‖ ≤ ‖(ω n).toContinuousLinearMap‖ * ‖f m n hmn a‖ :=
        (ω n).toContinuousLinearMap.le_opNorm _
      _ = ‖f m n hmn a‖ := by rw [(ω n).norm_eq_one, one_mul]
      _ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le (f m n hmn) a
      _ = 1 * ‖a‖ := (one_mul _).symm
  · simp only [restrictedStateFunctional, dif_neg hmn, (ω m).norm_eq_one, le_refl]

/-- All fixed-stage restrictions of the `n`th state, regarded as one point of a compact
countable product. -/
private def projectivePoint (ω : ∀ n, NCG.PreCStarState (A n)) (n : ℕ) :
    ∀ m, StageDualBall (A m) :=
  fun m ↦ ⟨restrictedStateFunctional f ω n m, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_restrictedStateFunctional_le f ω n m⟩


private def preCStarStateOfContractiveLimit {E : Type*} [CStarAlgebra E]
    (ψ : E →L[ℂ] ℂ) (hnorm : ‖ψ‖ ≤ 1) (hone : ψ 1 = 1)
    (hpos : ∀ a : E, 0 ≤ ψ (star a * a)) : NCG.PreCStarState E where
  toContinuousLinearMap := ψ
  map_one := hone
  map_star_mul_self_nonneg := hpos
  norm_eq_one := by
    apply le_antisymm hnorm
    letI : Nontrivial E := ⟨⟨0, 1, fun hzero ↦ by
      have : (0 : ℂ) = 1 := by
        calc
          0 = ψ 0 := by simp
          _ = ψ 1 := congrArg ψ hzero
          _ = 1 := hone
      exact zero_ne_one this⟩⟩
    calc
      1 = ‖ψ 1‖ := by rw [hone, norm_one]
      _ ≤ ‖ψ‖ * ‖(1 : E)‖ := ψ.le_opNorm 1
      _ = ‖ψ‖ := by rw [CStarRing.norm_one, mul_one]
/-- **Projective compactness.** There is one subsequence along which the restrictions to every
fixed finite-dimensional stage converge.  The limiting stage states are compatible, so they
assemble into a state on the completed AF direct limit. -/
theorem projective_state_compactness (ω : ∀ n, NCG.PreCStarState (A n)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ ωLimit : CompatibleState f,
      (∀ m (a : A m),
        Tendsto (fun j ↦ restrictedStateFunctional f ω (σ j) m a) atTop (𝓝 (ωLimit.state m a))) ∧
      ∃ Ω : Completion f →ₚ[ℂ] ℂ,
        ∀ m (a : A m), Ω (completionOf f m a) = ωLimit.state m a := by
  obtain ⟨Ψ, σ, hσ, hΨ⟩ := CompactSpace.tendsto_subseq (projectivePoint f ω)
  have hcoord (m : ℕ) :
      Tendsto (fun j ↦ restrictedStateFunctional f ω (σ j) m) atTop (𝓝 (Ψ m : A m →L[ℂ] ℂ)) := by
    have hc : Continuous (fun p : (∀ m, StageDualBall (A m)) ↦
        ((p m : StageDualBall (A m)) : A m →L[ℂ] ℂ)) :=
      continuous_subtype_val.comp (continuous_apply m)
    convert (hc.tendsto Ψ).comp hΨ using 1
    all_goals rfl
  have heval (m : ℕ) (a : A m) :
      Tendsto (fun j ↦ restrictedStateFunctional f ω (σ j) m a) atTop
        (𝓝 ((Ψ m : A m →L[ℂ] ℂ) a)) := by
    exact ((ContinuousLinearMap.apply ℂ ℂ a).continuous.tendsto _).comp (hcoord m)
  have hle_eventually (m : ℕ) : ∀ᶠ j in atTop, m ≤ σ j := by
    filter_upwards [eventually_ge_atTop m] with j hj
    exact hj.trans (hσ.le_apply)
  have hone (m : ℕ) : (Ψ m : A m →L[ℂ] ℂ) 1 = 1 := by
    have hones : ∀ᶠ j in atTop,
        restrictedStateFunctional f ω (σ j) m (1 : A m) = 1 := by
      filter_upwards [hle_eventually m] with j hj
      rw [restrictedStateFunctional_of_le f ω hj, map_one, (ω (σ j)).map_one]
    have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop
        (𝓝 ((Ψ m : A m →L[ℂ] ℂ) 1)) :=
      (heval m 1).congr' (hones.mono fun j hj ↦ hj)
    exact tendsto_nhds_unique hconst tendsto_const_nhds
  have hpos (m : ℕ) (a : A m) : 0 ≤ (Ψ m : A m →L[ℂ] ℂ) (star a * a) := by
    have hnonneg : ∀ᶠ j in atTop,
        0 ≤ restrictedStateFunctional f ω (σ j) m (star a * a) := by
      filter_upwards [hle_eventually m] with j hj
      rw [restrictedStateFunctional_of_le f ω hj, map_mul, map_star]
      exact (ω (σ j)).map_star_mul_self_nonneg (f m (σ j) hj a)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (heval m (star a * a)) hnonneg
  have hnorm (m : ℕ) : ‖(Ψ m : A m →L[ℂ] ℂ)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (Ψ m).property
  let ωlim : ∀ m, NCG.PreCStarState (A m) := fun m ↦
    preCStarStateOfContractiveLimit (Ψ m) (hnorm m) (hone m) (hpos m)
  have hcompatible (m l : ℕ) (hml : m ≤ l) (a : A m) :
      ωlim l (f m l hml a) = ωlim m a := by
    have heq : ∀ᶠ j in atTop,
        restrictedStateFunctional f ω (σ j) l (f m l hml a) =
          restrictedStateFunctional f ω (σ j) m a := by
      filter_upwards [hle_eventually l] with j hlj
      have hmj : m ≤ σ j := hml.trans hlj
      rw [restrictedStateFunctional_of_le f ω hlj, restrictedStateFunctional_of_le f ω hmj,
        DirectedSystem.map_map' f hml hlj a]
    have ht : Tendsto (fun j ↦ restrictedStateFunctional f ω (σ j) m a) atTop
        (𝓝 (ωlim l (f m l hml a))) :=
      (heval l (f m l hml a)).congr' heq
    exact tendsto_nhds_unique ht (heval m a)
  let ωLimit : CompatibleState f :=
    { state := ωlim
      compatible := hcompatible }
  refine ⟨σ, hσ, ωLimit, ?_, ?_⟩
  · intro m a
    exact heval m a
  · exact ⟨ωLimit.completionPositiveLinearMap, fun m a ↦
      ωLimit.completionPositiveLinearMap_of m a⟩

omit [∀ n, FiniteDimensional ℂ (A n)] in
/-- If the original stage states are exactly compatible, they already determine the unique
state on the completed AF limit; no subsequence or compactness argument is needed. -/
theorem exactly_compatible_state_unique (ω : CompatibleState f) :
    ∃! Ω : Completion f →ₚ[ℂ] ℂ,
      ∀ m (a : A m), Ω (completionOf f m a) = ω.state m a := by
  refine ⟨ω.completionPositiveLinearMap, ?_, ?_⟩
  · exact fun m a ↦ ω.completionPositiveLinearMap_of m a
  · intro Ω hΩ
    exact ω.completionPositiveLinearMap_unique Ω hΩ

end NCG.PreCStarDirectLimit
