/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCollectiveCompactness

/-!
# Compact screens imply collective compactness

This file proves the positive compact-screen mechanism on varying Hilbert spaces.  Uniform
approximation of the embedded stage-unit-ball outputs by compact sets makes their union totally
bounded; in a complete common carrier its closure is compact.  A convenient specialization uses
a uniformly bounded output family and compact screen operators whose tails vanish uniformly.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v w v' w'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {G : Type v'} [NormedAddCommGroup G] [InnerProductSpace K G]
variable {Gn : ℕ → Type w'}
variable [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace K (Gn n)]

/-- A set uniformly approximable, to every positive accuracy, by compact sets is totally bounded. -/
theorem totallyBounded_of_compact_approximations {U : Set G}
    (happrox : ∀ ε > 0, ∃ C : Set G, IsCompact C ∧
      ∀ y ∈ U, ∃ z ∈ C, dist y z < ε) :
    TotallyBounded U := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨C, hC, hUC⟩ := happrox (ε / 2) (by positivity)
  obtain ⟨t, ht, hcover⟩ :=
    Metric.totallyBounded_iff.mp hC.totallyBounded (ε / 2) (by positivity)
  refine ⟨t, ht, ?_⟩
  intro y hy
  obtain ⟨c, hcC, hyc⟩ := hUC y hy
  have hcCover := hcover hcC
  obtain ⟨z, hzt, hcz⟩ : ∃ z ∈ t, dist c z < ε / 2 := by
    simpa only [Set.mem_iUnion, exists_prop, Metric.mem_ball] using hcCover
  refine Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hzt, ?_⟩⟩
  calc
    dist y z ≤ dist y c + dist c z := dist_triangle y c z
    _ < ε / 2 + ε / 2 := add_lt_add hyc hcz
    _ = ε := by ring

namespace System

variable (L : System (K := K) (H := G) (Hn := Gn))

/-- The union of all embedded stage-unit-ball outputs. -/
def embeddedUnitBallOutputs (Tn : ∀ n, Hn n →L[K] Gn n) : Set G :=
  ⋃ n, L.embeddedOperator Tn n '' Metric.closedBall 0 1

/-- Compact approximation of the full embedded output union implies collective compactness. -/
theorem collectivelyCompact_of_compact_approximations [CompleteSpace G]
    (Tn : ∀ n, Hn n →L[K] Gn n)
    (happrox : ∀ ε > 0, ∃ C : Set G, IsCompact C ∧
      ∀ y ∈ L.embeddedUnitBallOutputs Tn, ∃ z ∈ C, dist y z < ε) :
    L.CollectivelyCompact Tn := by
  have htb : TotallyBounded (L.embeddedUnitBallOutputs Tn) :=
    totallyBounded_of_compact_approximations happrox
  refine ⟨closure (L.embeddedUnitBallOutputs Tn),
    htb.closure.isCompact_of_isClosed isClosed_closure, ?_⟩
  intro n y hy
  exact subset_closure (Set.mem_iUnion.2 ⟨n, hy⟩)

/-- A uniformly bounded output family with uniformly vanishing tails under compact screen
operators is collectively compact. -/
theorem collectivelyCompact_of_compactOperator_screens [CompleteSpace G]
    (Tn : ∀ n, Hn n →L[K] Gn n) (screen : ℕ → G →L[K] G)
    (B : ℝ)
    (hbounded : L.embeddedUnitBallOutputs Tn ⊆ Metric.closedBall 0 B)
    (hcompact : ∀ R, IsCompactOperator (screen R))
    (htail : ∀ ε > 0, ∃ R, ∀ y ∈ L.embeddedUnitBallOutputs Tn,
      ‖y - screen R y‖ < ε) :
    L.CollectivelyCompact Tn := by
  apply L.collectivelyCompact_of_compact_approximations Tn
  intro ε hε
  obtain ⟨R, hR⟩ := htail ε hε
  obtain ⟨C, hC, hscreenC⟩ := (hcompact R).image_closedBall_subset_compact B
  refine ⟨C, hC, ?_⟩
  intro y hy
  refine ⟨screen R y, hscreenC ⟨y, hbounded hy, rfl⟩, ?_⟩
  simpa [dist_eq_norm] using hR y hy

end System

end NCG.VaryingHilbert

namespace NCG.VaryingHilbert
namespace System
universe u v w v' w'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {G : Type v'} [NormedAddCommGroup G] [InnerProductSpace K G]
variable {Gn : ℕ → Type w'}
variable [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace K (Gn n)]

variable (L : System (K := K) (H := G) (Hn := Gn))
/-- The eventual version used by cutoff limits: every stage operator is compact, the whole output
union is bounded, and compact screens approximate all sufficiently late stage outputs uniformly.
The finitely many early stages are absorbed into the compact carrier separately. -/
theorem collectivelyCompact_of_eventually_compactOperator_screens [CompleteSpace G]
    (Tn : ∀ n, Hn n →L[K] Gn n) (screen : ℕ → G →L[K] G)
    (B : ℝ)
    (hbounded : L.embeddedUnitBallOutputs Tn ⊆ Metric.closedBall 0 B)
    (hstage : ∀ n, IsCompactOperator (L.embeddedOperator Tn n))
    (hcompact : ∀ R, IsCompactOperator (screen R))
    (htail : ∀ ε > 0, ∃ R,
      ∀ᶠ n in atTop, ∀ y ∈
        L.embeddedOperator Tn n '' Metric.closedBall 0 1,
          ‖y - screen R y‖ < ε) :
    L.CollectivelyCompact Tn := by
  apply L.collectivelyCompact_of_compact_approximations Tn
  intro ε hε
  obtain ⟨R, hR⟩ := htail ε hε
  rw [eventually_atTop] at hR
  obtain ⟨N, hN⟩ := hR
  obtain ⟨C, hC, hscreenC⟩ := (hcompact R).image_closedBall_subset_compact B
  have hearly (n : ℕ) :
      ∃ D : Set G, IsCompact D ∧
        L.embeddedOperator Tn n '' Metric.closedBall 0 1 ⊆ D :=
    (hstage n).image_closedBall_subset_compact 1
  choose D hD hDsub using hearly
  let Dearly : Set G := ⋃ n : Fin N, D n
  have hDearly : IsCompact Dearly := by
    dsimp [Dearly]
    exact isCompact_iUnion fun n : Fin N ↦ hD n
  refine ⟨C ∪ Dearly, hC.union hDearly, ?_⟩
  intro y hy
  obtain ⟨n, hyn⟩ := Set.mem_iUnion.mp hy
  by_cases hn : n < N
  · refine ⟨y, Set.mem_union_right C ?_, dist_self y ▸ hε⟩
    exact Set.mem_iUnion.2 ⟨⟨n, hn⟩, hDsub n hyn⟩
  · refine ⟨screen R y, Set.mem_union_left Dearly ?_, ?_⟩
    · exact hscreenC ⟨y, hbounded hy, rfl⟩
    · simpa [dist_eq_norm] using hN n (Nat.le_of_not_gt hn) y hyn

end System

end NCG.VaryingHilbert
