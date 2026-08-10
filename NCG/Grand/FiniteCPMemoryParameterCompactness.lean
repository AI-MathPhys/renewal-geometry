/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CPMemoryCompactness
import NCG.Upstream.PrimitiveWeight

/-!
# Compact parameter space for finite completely positive memory

This file supplies the concrete compact parameter space `Θ_M` used by
`thm:CP-memory-compactness`.  A parameter consists of

* a density matrix on the recurrent memory;
* for every primitive branch, a bounded nonnegative scale and a normalized
  positive Choi direction;
* for every terminal read, a bounded nonnegative scale and a normalized
  positive effect direction.

Thus all positivity constraints are built into the parameter type.  Closed
normalization equations and continuous cylinder evaluations cut out compact
horizon-feasibility sets.  The finite-intersection argument then proves both
exact finite-horizon compactness and its vanishing-error version.
-/

open Filter Matrix Set Topology
open scoped ComplexOrder

namespace NCG

namespace FiniteCPMemory

/-- A normalized positive matrix, used for source states and positive
Choi/effect directions. -/
abbrev DensityMatrix (n : ℕ) :=
  {A : Matrix (Fin n) (Fin n) ℂ //
    A ∈ Upstream.PrimitiveWeight.densitySet n ℂ}

noncomputable instance densityMatrixCompactSpace (n : ℕ) :
    CompactSpace (DensityMatrix n) :=
  isCompact_iff_compactSpace.mp
    Upstream.PrimitiveWeight.isCompact_densitySet

/-- A bounded positive matrix in scale--direction coordinates.  The scale is
bounded by `n`; the represented matrix is therefore positive and uniformly
bounded in this finite-dimensional presentation. -/
abbrev ScaledPositiveMatrix (n : ℕ) :=
  Set.Icc (0 : ℝ) n × DensityMatrix n

/-- The positive matrix represented by scale--direction coordinates. -/
def ScaledPositiveMatrix.value {n : ℕ} (A : ScaledPositiveMatrix n) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((A.1.1 : ℝ) : ℂ) • A.2.1

theorem ScaledPositiveMatrix.value_posSemidef {n : ℕ}
    (A : ScaledPositiveMatrix n) : A.value.PosSemidef := by
  exact Upstream.PrimitiveWeight.posSemidef_real_smul A.2.2.1 A.1.2.1

/-- Concrete finite-dimensional CP-memory parameters with branch alphabet
`Branch` and terminal-read alphabet `Read`. -/
abbrev Parameter (M : ℕ) (Branch Read : Type) :=
  DensityMatrix M ×
    (Branch → ScaledPositiveMatrix (M * M)) ×
    (Read → ScaledPositiveMatrix M)

/-- The concrete CP-memory parameter space is compact. -/
theorem parameterSpace_compact (M : ℕ) (Branch Read : Type) :
    IsCompact (Set.univ : Set (Parameter M Branch Read)) :=
  isCompact_univ

/-- A finite CP presentation: positivity and uniform boundedness are encoded
by `Parameter`; the remaining normalization equations form a closed set, and
each requested cylinder/terminal value is continuous in the parameters. -/
structure Presentation (M : ℕ) (Branch Read : Type) where
  normalized : Set (Parameter M Branch Read)
  normalized_closed : IsClosed normalized
  evaluate : ℕ → Parameter M Branch Read → ℂ
  evaluate_continuous : ∀ k, Continuous (evaluate k)
  target : ℕ → ℂ

variable {M : ℕ} {Branch Read : Type}

/-- Parameters realizing all requested values through horizon `N`. -/
def exactHorizonSet (P : Presentation M Branch Read) (N : ℕ) :
    Set (Parameter M Branch Read) :=
  {p | p ∈ P.normalized ∧ ∀ k ≤ N, P.evaluate k p = P.target k}

theorem exactHorizonSet_closed (P : Presentation M Branch Read) (N : ℕ) :
    IsClosed (exactHorizonSet P N) := by
  have heq (k : ℕ) : IsClosed {p | P.evaluate k p = P.target k} :=
    isClosed_eq (P.evaluate_continuous k) continuous_const
  have hform : exactHorizonSet P N =
      P.normalized ∩ ⋂ k : Fin (N + 1),
        {p | P.evaluate k p = P.target k} := by
    ext p
    simp only [exactHorizonSet, mem_setOf_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hp, hvalues⟩
      exact ⟨hp, fun k ↦ hvalues k (Nat.le_of_lt_succ k.2)⟩
    · rintro ⟨hp, hvalues⟩
      exact ⟨hp, fun k hk ↦ hvalues ⟨k, Nat.lt_succ_iff.mpr hk⟩⟩
  rw [hform]
  exact P.normalized_closed.inter (isClosed_iInter fun k ↦ heq k)

theorem exactHorizonSet_compact (P : Presentation M Branch Read) (N : ℕ) :
    IsCompact (exactHorizonSet P N) :=
  (exactHorizonSet_closed P N).isCompact

theorem exactHorizonSet_antitone (P : Presentation M Branch Read) (N : ℕ) :
    exactHorizonSet P (N + 1) ⊆ exactHorizonSet P N := by
  rintro p ⟨hp, hvalues⟩
  exact ⟨hp, fun k hk ↦ hvalues k (hk.trans (Nat.le_succ N))⟩

/-- A single recurrent CP parameter realizes the full infinite table exactly
iff the same concrete presentation is feasible at every finite horizon. -/
theorem exact_realization_iff_all_finite_horizons
    (P : Presentation M Branch Read) :
    (∃ p ∈ P.normalized, ∀ k, P.evaluate k p = P.target k) ↔
      ∀ N, (exactHorizonSet P N).Nonempty := by
  constructor
  · rintro ⟨p, hp, hvalues⟩ N
    exact ⟨p, hp, fun k _ ↦ hvalues k⟩
  · intro hfinite
    have hcommon : (⋂ N, exactHorizonSet P N).Nonempty :=
      cp_memory_compactness.1 (exactHorizonSet P)
        (exactHorizonSet_compact P) hfinite
        (exactHorizonSet_closed P) (exactHorizonSet_antitone P)
    rcases hcommon with ⟨p, hp⟩
    have hpN : ∀ N, p ∈ exactHorizonSet P N := mem_iInter.mp hp
    exact ⟨p, (hpN 0).1, fun k ↦ (hpN k).2 k le_rfl⟩

/-- Parameters whose values through horizon `N` have error at most `ε N`. -/
def approximateHorizonSet (P : Presentation M Branch Read) (ε : ℕ → ℝ)
    (N : ℕ) : Set (Parameter M Branch Read) :=
  {p | p ∈ P.normalized ∧
    ∀ k ≤ N, dist (P.evaluate k p) (P.target k) ≤ ε N}

theorem approximateHorizonSet_closed (P : Presentation M Branch Read)
    (ε : ℕ → ℝ) (N : ℕ) : IsClosed (approximateHorizonSet P ε N) := by
  have hbound (k : ℕ) :
      IsClosed {p | dist (P.evaluate k p) (P.target k) ≤ ε N} :=
    isClosed_le ((P.evaluate_continuous k).dist continuous_const) continuous_const
  have hform : approximateHorizonSet P ε N =
      P.normalized ∩ ⋂ k : Fin (N + 1),
        {p | dist (P.evaluate k p) (P.target k) ≤ ε N} := by
    ext p
    simp only [approximateHorizonSet, mem_setOf_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hp, hvalues⟩
      exact ⟨hp, fun k ↦ hvalues k (Nat.le_of_lt_succ k.2)⟩
    · rintro ⟨hp, hvalues⟩
      exact ⟨hp, fun k hk ↦ hvalues ⟨k, Nat.lt_succ_iff.mpr hk⟩⟩
  rw [hform]
  exact P.normalized_closed.inter (isClosed_iInter fun k ↦ hbound k)

theorem approximateHorizonSet_compact (P : Presentation M Branch Read)
    (ε : ℕ → ℝ) (N : ℕ) : IsCompact (approximateHorizonSet P ε N) :=
  (approximateHorizonSet_closed P ε N).isCompact

theorem approximateHorizonSet_antitone (P : Presentation M Branch Read)
    {ε : ℕ → ℝ} (hε : Antitone ε) (N : ℕ) :
    approximateHorizonSet P ε (N + 1) ⊆ approximateHorizonSet P ε N := by
  rintro p ⟨hp, hvalues⟩
  exact ⟨hp, fun k hk ↦
    (hvalues k (hk.trans (Nat.le_succ N))).trans (hε (Nat.le_succ N))⟩

/-- Vanishing uniform finite-horizon errors still yield one exact recurrent
CP realization in the same concrete presentation. -/
theorem exact_realization_of_vanishing_horizon_error
    (P : Presentation M Branch Read) (ε : ℕ → ℝ)
    (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (nhds 0))
    (hfinite : ∀ N, (approximateHorizonSet P ε N).Nonempty) :
    ∃ p ∈ P.normalized, ∀ k, P.evaluate k p = P.target k := by
  have hcommon : (⋂ N, approximateHorizonSet P ε N).Nonempty :=
    cp_memory_compactness.1 (approximateHorizonSet P ε)
      (approximateHorizonSet_compact P ε) hfinite
      (approximateHorizonSet_closed P ε)
      (approximateHorizonSet_antitone P hεanti)
  rcases hcommon with ⟨p, hp⟩
  have hpN : ∀ N, p ∈ approximateHorizonSet P ε N := mem_iInter.mp hp
  refine ⟨p, (hpN 0).1, fun k ↦ ?_⟩
  apply dist_eq_zero.mp
  apply le_antisymm
  · apply ge_of_tendsto hεlim
    exact eventually_atTop.2 ⟨k, fun N hk ↦ (hpN N).2 k hk⟩
  · exact dist_nonneg

end FiniteCPMemory

end NCG
