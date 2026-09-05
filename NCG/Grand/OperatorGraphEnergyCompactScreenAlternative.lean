/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphNormCompactScreenCollectiveCompactness
import NCG.Grand.OperatorGraphNormCarrierEnergy

/-!
# Compact-screen alternative in extended graph-energy form

The negative branch is stated with effective-domain vectors satisfying the
literal manuscript inequality `‖u‖² + q_n(u) ≤ 1`.  Thus users do not need to
mention the graph-carrier subtype when instantiating the mass-escape
alternative.
-/

open Filter Set Topology
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z z'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, FiniteDimensional K (Hn n)]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace K F]
  [CompleteSpace F]
variable {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]

omit [CompleteSpace H] [∀ n, FiniteDimensional K (Hn n)] [CompleteSpace F] in
/-- Failure of the full graph-energy screen profile directly produces the
manuscript's cofinal effective-domain mass-escape sequence. -/
theorem energyMassEscape_of_not_graphNormScreenTight
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (screen : ℕ → WithLp 2 (H × F) →L[K] WithLp 2 (H × F))
    (hfail : ¬ NCG.VaryingHilbert.UniformGraphScreenTight
      (fun n u ↦ L.embedding n
        (operatorGraphNormInclusion (Dn n) (An n) u))
      (fun radius y ↦ y - screen radius y)
      (fun _ u ↦ ‖u‖ ≤ 1)) :
    ∃ ε > 0, ∃ radius cutoff : ℕ → ℕ,
      ∃ x : ∀ j, Dn (cutoff j),
        Tendsto radius atTop atTop ∧ Tendsto cutoff atTop atTop ∧
        ∀ j,
          ‖(x j : Hn (cutoff j))‖ ^ 2 +
              (ennrealOperatorGraphEnergy
                (Dn (cutoff j)) (An (cutoff j))
                (x j : Hn (cutoff j))).toReal ≤ 1 ∧
          ε ≤ ‖L.embedding (cutoff j)
              (operatorGraphNormInclusion
                (Dn (cutoff j)) (An (cutoff j))
                (operatorGraphNormVector
                  (Dn (cutoff j)) (An (cutoff j)) (x j))) -
            screen (radius j)
              (L.embedding (cutoff j)
                (operatorGraphNormInclusion
                  (Dn (cutoff j)) (An (cutoff j))
                  (operatorGraphNormVector
                    (Dn (cutoff j)) (An (cutoff j)) (x j))))‖ := by
  obtain ⟨ε, hε, radius, cutoff, u, hradius, hcutoff, hu⟩ :=
    NCG.VaryingHilbert.massEscape_of_not_uniformGraphScreenTight
      (fun n u ↦ L.embedding n
        (operatorGraphNormInclusion (Dn n) (An n) u))
      (fun radius y ↦ y - screen radius y)
      (fun _ u ↦ ‖u‖ ≤ 1) hfail
  have hexists : ∀ j, ∃ x : Dn (cutoff j),
      u j = operatorGraphNormVector
        (Dn (cutoff j)) (An (cutoff j)) x ∧
      ‖(x : Hn (cutoff j))‖ ^ 2 +
          (ennrealOperatorGraphEnergy
            (Dn (cutoff j)) (An (cutoff j))
            (x : Hn (cutoff j))).toReal ≤ 1 := by
    intro j
    exact operatorGraphNormCarrier_unitBall_exists_energyBound
      (Dn (cutoff j)) (An (cutoff j)) (u j)
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using (hu j).1)
  choose x hx henergy using hexists
  exact ⟨ε, hε, radius, cutoff, x, hradius, hcutoff,
    fun j ↦ ⟨henergy j, by simpa only [← hx j] using (hu j).2⟩⟩

/-- Either the physical resolvents are collectively compact, or graph mass
escapes along cofinal cutoffs through effective-domain vectors satisfying
the exact extended graph-energy unit-ball bound. -/
theorem operatorGraphResolvent_collectivelyCompact_or_energyMassEscape
    (J : System (K := K) (H := H) (Hn := Hn))
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (Rn : ∀ n, Hn n →L[K] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (screen : ℕ → WithLp 2 (H × F) →L[K] WithLp 2 (H × F))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst) :
    J.CollectivelyCompact Rn ∨
      ∃ ε > 0, ∃ radius cutoff : ℕ → ℕ,
        ∃ x : ∀ j, Dn (cutoff j),
          Tendsto radius atTop atTop ∧ Tendsto cutoff atTop atTop ∧
          ∀ j,
            ‖(x j : Hn (cutoff j))‖ ^ 2 +
                (ennrealOperatorGraphEnergy
                  (Dn (cutoff j)) (An (cutoff j))
                  (x j : Hn (cutoff j))).toReal ≤ 1 ∧
            ε ≤ ‖L.embedding (cutoff j)
                (operatorGraphNormInclusion
                  (Dn (cutoff j)) (An (cutoff j))
                  (operatorGraphNormVector
                    (Dn (cutoff j)) (An (cutoff j)) (x j))) -
              screen (radius j)
                (L.embedding (cutoff j)
                  (operatorGraphNormInclusion
                    (Dn (cutoff j)) (An (cutoff j))
                    (operatorGraphNormVector
                      (Dn (cutoff j)) (An (cutoff j)) (x j))))‖ := by
  rcases J.operatorGraphResolvent_collectivelyCompact_or_graphNormMassEscape
      L Dn An Rn lam hlam hEquation screen hcompact hfst with
    hcompactResolvent | hescape
  · exact Or.inl hcompactResolvent
  · right
    obtain ⟨ε, hε, radius, cutoff, u, hradius, hcutoff, hu⟩ := hescape
    have hexists : ∀ j, ∃ x : Dn (cutoff j),
        u j = operatorGraphNormVector
          (Dn (cutoff j)) (An (cutoff j)) x ∧
        ‖(x : Hn (cutoff j))‖ ^ 2 +
            (ennrealOperatorGraphEnergy
              (Dn (cutoff j)) (An (cutoff j))
              (x : Hn (cutoff j))).toReal ≤ 1 := by
      intro j
      exact operatorGraphNormCarrier_unitBall_exists_energyBound
        (Dn (cutoff j)) (An (cutoff j)) (u j)
          (by simpa only [Metric.mem_closedBall, dist_zero_right] using (hu j).1)
    choose x hx henergy using hexists
    refine ⟨ε, hε, radius, cutoff, x, hradius, hcutoff, fun j ↦
      ⟨henergy j, ?_⟩⟩
    simpa only [← hx j] using (hu j).2

end NCG.VaryingHilbert.System
