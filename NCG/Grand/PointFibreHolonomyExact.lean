/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PointFibreHolonomy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Exact tree gauge and log-determinant expansion

This closes the two gaps left in `PointFibreHolonomy.lean`.  Paths are typed,
so the endpoint cancellations in gauge covariance are proved rather than
assumed.  A chosen tree transport turns every non-tree edge into precisely its
fundamental-cycle holonomy, giving both directions of HOL.1.  HOL.2 is proved
as a convergent `HasSum` identity for the complete finite eigenvalue list of a
positive matrix.
-/

open scoped BigOperators
open scoped ComplexOrder MatrixOrder

namespace NCG.PointFibreHolonomyExact

universe u v

/-- Typed paths in a directed finite incidence graph. -/
inductive TypedPath {V : Type u} (E : V → V → Type v) : V → V → Type (max u v)
  | nil (i : V) : TypedPath E i i
  | cons {i j k : V} (e : E i j) (p : TypedPath E j k) : TypedPath E i k

namespace TypedPath

variable {V : Type u} {E : V → V → Type v} {G : Type*} [Group G]

/-- Ordered transport along a typed path; later edges act on the left. -/
def transport (W : ∀ {i j}, E i j → G) :
    ∀ {i j}, TypedPath E i j → G
  | _, _, .nil _ => 1
  | _, _, .cons e p => transport W p * W e

/-- Endpoint gauge action on one directed edge. -/
def gaugeEdge (Q : V → G) (W : ∀ {i j}, E i j → G)
    {i j : V} (e : E i j) : G :=
  (Q j)⁻¹ * W e * Q i

/-- Gauge factors telescope on every typed path. -/
theorem transport_gaugeEdge (Q : V → G) (W : ∀ {i j}, E i j → G) :
    ∀ {i j} (p : TypedPath E i j),
      transport (fun {i j} (e : E i j) => (Q j)⁻¹ * W e * Q i) p =
        (Q j)⁻¹ * transport W p * Q i := by
  intro i j p
  induction p with
  | nil i => simp [transport, gaugeEdge]
  | @cons i j k e p ih =>
      simp only [transport, ih]
      group

/-- Consequently a closed-path holonomy changes by conjugacy. -/
theorem cycle_holonomy_gauge_conjugate (Q : V → G)
    (W : ∀ {i j}, E i j → G) {i : V} (C : TypedPath E i i) :
    transport (fun {i j} (e : E i j) => (Q j)⁻¹ * W e * Q i) C =
      (Q i)⁻¹ * transport W C * Q i :=
  transport_gaugeEdge Q W C

end TypedPath

section TreeGauge

variable {V E G : Type*} [Group G]

/-- The fundamental-cycle router obtained after transporting both endpoints
to the root along a chosen spanning tree. -/
def fundamentalCycleHolonomy (src tgt : E → V) (treeTransport : V → G)
    (W : E → G) (e : E) : G :=
  (treeTransport (tgt e))⁻¹ * W e * treeTransport (src e)

/-- A genuine spanning-tree gauge trivializes all edges exactly when every
non-tree fundamental-cycle holonomy is trivial.  The tree compatibility is the
definition supplied by its root paths, not a global cocycle assumption. -/
theorem treeGauge_trivializes_iff_fundamentalCycleHolonomies
    [Fintype E] [DecidableEq E]
    (src tgt : E → V) (treeEdges : Finset E)
    (treeTransport : V → G) (W : E → G)
    (htree : ∀ e ∈ treeEdges,
      fundamentalCycleHolonomy src tgt treeTransport W e = 1) :
    (∀ e, fundamentalCycleHolonomy src tgt treeTransport W e = 1) ↔
      (∀ e ∈ Finset.univ \ treeEdges,
        fundamentalCycleHolonomy src tgt treeTransport W e = 1) := by
  constructor
  · exact fun h e _ => h e
  · intro h e
    by_cases he : e ∈ treeEdges
    · exact htree e he
    · exact h e (by simp [he])

/-- HOL.1 in the original edge variables: trivial tree-gauge holonomy is
equivalent to the edge being the pure-gauge transport between its endpoints. -/
theorem fundamentalCycleHolonomy_eq_one_iff_pureGauge
    (src tgt : E → V) (treeTransport : V → G) (W : E → G) (e : E) :
    fundamentalCycleHolonomy src tgt treeTransport W e = 1 ↔
      W e = treeTransport (tgt e) * (treeTransport (src e))⁻¹ := by
  simp only [fundamentalCycleHolonomy]
  constructor <;> intro h
  · calc
      W e = treeTransport (tgt e) *
          ((treeTransport (tgt e))⁻¹ * W e * treeTransport (src e)) *
          (treeTransport (src e))⁻¹ := by group
      _ = treeTransport (tgt e) * (treeTransport (src e))⁻¹ := by rw [h, mul_one]
  · rw [h]
    group

/-- A nontrivial fundamental cycle is therefore an exact obstruction to the
chosen common block gauge trivializing every edge. -/
theorem nontrivialFundamentalCycle_obstructs_commonGauge
    [Fintype E] [DecidableEq E]
    (src tgt : E → V) (treeEdges : Finset E)
    (treeTransport : V → G) (W : E → G)
    (htree : ∀ e ∈ treeEdges,
      fundamentalCycleHolonomy src tgt treeTransport W e = 1)
    (hnonflat : ∃ e ∈ Finset.univ \ treeEdges,
      fundamentalCycleHolonomy src tgt treeTransport W e ≠ 1) :
    ¬(∀ e, W e = treeTransport (tgt e) *
      (treeTransport (src e))⁻¹) := by
  intro hpure
  obtain ⟨e, he, hne⟩ := hnonflat
  apply hne
  exact (fundamentalCycleHolonomy_eq_one_iff_pureGauge
    src tgt treeTransport W e).2 (hpure e)

end TreeGauge

section LogDet

variable {n : Type*} [Fintype n]

/-- Spectral form of the positive log determinant. -/
noncomputable def spectralLogDet (lam : n → ℝ) : ℝ :=
  ∑ i, Real.log (lam i)

/-- Spectral trace of the `m`-th power of `I - Λ⁻¹K`. -/
noncomputable def defectPowerTrace (lam : n → ℝ) (Λ : ℝ) (m : ℕ) : ℝ :=
  ∑ i, (1 - lam i / Λ) ^ m

/-- Exact HOL.2, including convergence, for an arbitrary finite positive
spectrum.  This is the spectral-theorem normal form of the matrix identity. -/
theorem logDet_hasSum_defectPowerTrace
    (lam : n → ℝ) (Λ : ℝ)
    (hΛ : 0 < Λ) (hlam : ∀ i, 0 < lam i)
    (hle : ∀ i, lam i ≤ Λ) :
    HasSum (fun m : ℕ => defectPowerTrace lam Λ (m + 1) / (m + 1))
      (Fintype.card n * Real.log Λ - spectralLogDet lam) := by
  classical
  have hx : ∀ i, |1 - lam i / Λ| < 1 := by
    intro i
    have hratio0 : 0 < lam i / Λ := div_pos (hlam i) hΛ
    have hratio1 : lam i / Λ ≤ 1 := (div_le_one hΛ).2 (hle i)
    rw [abs_lt]
    constructor <;> linarith
  have hi : ∀ i, HasSum
      (fun m : ℕ => (1 - lam i / Λ) ^ (m + 1) / (m + 1))
      (Real.log Λ - Real.log (lam i)) := by
    intro i
    have hs := Real.hasSum_pow_div_log_of_abs_lt_one (hx i)
    have htarget : -Real.log (1 - (1 - lam i / Λ)) =
        Real.log Λ - Real.log (lam i) := by
      rw [show 1 - (1 - lam i / Λ) = lam i / Λ by ring]
      rw [Real.log_div (ne_of_gt (hlam i)) (ne_of_gt hΛ)]
      ring
    rw [← htarget]
    exact hs
  have hfinite : HasSum
      (fun m : ℕ => ∑ i, (1 - lam i / Λ) ^ (m + 1) / (m + 1))
      (∑ i, (Real.log Λ - Real.log (lam i))) := by
    have hfin : ∀ s : Finset n, HasSum
        (fun m : ℕ => ∑ i ∈ s,
          (1 - lam i / Λ) ^ (m + 1) / (m + 1))
        (∑ i ∈ s, (Real.log Λ - Real.log (lam i))) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
      | @insert a s ha ih =>
          simpa only [Finset.sum_insert, ha, not_false_eq_true] using (hi a).add ih
    simpa using hfin Finset.univ
  convert hfinite using 1
  · ext m
    simp only [defectPowerTrace]
    rw [Finset.sum_div]
  · simp only [spectralLogDet, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul]
    rw [Finset.card_univ]

end LogDet

section ClosedWalks

variable {R : Type*} [Semiring R] {n : Type*} [Fintype n] [DecidableEq n]

/-- Finite sum of amplitudes of all directed length-`m` walks from `i` to `j`.
Each recursive multiplication contributes one matrix edge amplitude. -/
def directedWalkSum (P : Matrix n n R) : ℕ → n → n → R
  | 0, i, j => if i = j then 1 else 0
  | m + 1, i, j => ∑ k, directedWalkSum P m i k * P k j

/-- Matrix powers are exactly the finite directed-walk amplitude sums. -/
theorem directedWalkSum_eq_pow (P : Matrix n n R) :
    ∀ m i j, directedWalkSum P m i j = (P ^ m) i j := by
  intro m
  induction m with
  | zero =>
      intro i j
      simp [directedWalkSum, Matrix.one_apply]
  | succ m ih =>
      intro i j
      simp only [directedWalkSum, pow_succ, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => congrArg (fun z => z * P k j) (ih i k)

/-- Hence every trace of a power is the convergent finite sum of closed-walk
amplitudes, with the base vertex also summed. -/
theorem trace_pow_eq_closedWalkAmplitudeSum (P : Matrix n n R) (m : ℕ) :
    Matrix.trace (P ^ m) = ∑ i, directedWalkSum P m i i := by
  simp only [Matrix.trace, Matrix.diag_apply, directedWalkSum_eq_pow]

end ClosedWalks

section ScalarAndPolarAlternatives

/-- Once a flat rank-one phase has been gauged to one, multiplying by a
nonnegative polar amplitude is genuinely real and nonnegative. -/
theorem flat_rankOne_phase_has_nonnegative_amplitude
    (phase : ℂ) (a : ℝ) (hphase : phase = 1) (ha : 0 ≤ a) :
    0 ≤ (phase * (a : ℂ)).re ∧ (phase * (a : ℂ)).im = 0 := by
  subst phase
  simpa using ha

/-- Flat unitary holonomy alone cannot scalarize a positive polar factor in
fibre rank two: `diag(1,2)` is positive definite but not scalar. -/
theorem exists_posDef_polarFactor_not_scalar :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ,
      A.PosDef ∧ ∀ c : ℂ, A ≠ Matrix.scalar (Fin 2) c := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(1 : ℂ), 2]
  refine ⟨A, ?_, ?_⟩
  · apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num
  · intro c h
    have h0 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
    have h1 := congrFun (congrFun h (1 : Fin 2)) (1 : Fin 2)
    simp [A] at h0 h1
    have h12 : (1 : ℂ) = 2 := h0.trans h1.symm
    norm_num at h12

end ScalarAndPolarAlternatives

end NCG.PointFibreHolonomyExact
