/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.ChoiCriterion
import NCG.Grand.FiniteCPMemoryParameterCompactness
import NCG.Grand.PredictiveCPRadonNikodymEnvelope

/-!
# Concrete recurrent CP-cylinder compactness

This file closes the concrete-evaluation gap in
`thm:CP-memory-compactness`.  A positive matrix in the branch coordinate of
`FiniteCPMemory.Parameter` is reindexed as a Choi matrix and reconstructed as
a completely positive map.  Words act by repeated application of those maps,
and terminal Reads are the trace pairing with the stored positive effects.
The resulting cylinder values are continuous in the single reusable parameter
tuple, so the compact finite-horizon theorem applies to actual CP cylinders.
-/

open Matrix Finset Set Filter Topology
open scoped ComplexOrder

namespace NCG
namespace ConcreteCPMemoryCylinder

open FiniteCPMemory

variable {M : ℕ} {Branch Read : Type}

/-- Reindex the stored `M²`-by-`M²` branch matrix as its Choi matrix. -/
noncomputable def branchChoi
    (p : Parameter M Branch Read) (b : Branch) :
    Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ :=
  (p.2.1 b).value.submatrix finProdFinEquiv finProdFinEquiv

/-- The linear operation reconstructed entrywise from a Choi matrix. -/
noncomputable def choiActionLinear
    (C : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ) :
    Matrix (Fin M) (Fin M) ℂ →ₗ[ℂ] Matrix (Fin M) (Fin M) ℂ where
  toFun := choiMatrixAction C
  map_add' X Y := by
    ext i j
    simp only [choiMatrixAction, Matrix.add_apply]
    simp_rw [add_mul]
    simp only [Finset.sum_add_distrib]
  map_smul' c X := by
    ext i j
    simp [choiMatrixAction, Matrix.smul_apply, Finset.mul_sum, mul_assoc]

@[simp] theorem choiMatrix_choiActionLinear
    (C : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ) :
    choiMatrix (choiActionLinear C) = C := by
  change finiteMapChoi (choiMatrixAction C) = C
  exact finiteMapChoi_choiMatrixAction C

/-- Every stored branch coordinate reconstructs a completely positive map. -/
theorem branch_completelyPositive (p : Parameter M Branch Read) (b : Branch) :
    IsMatrixCompletelyPositive (choiActionLinear (branchChoi p b)) := by
  apply cp_of_choiMatrix_posSemidef
  rw [choiMatrix_choiActionLinear]
  exact (ScaledPositiveMatrix.value_posSemidef (p.2.1 b)).submatrix _

/-- Recurrent memory state after a finite primitive word. -/
noncomputable def wordState (p : Parameter M Branch Read) :
    List Branch → Matrix (Fin M) (Fin M) ℂ
  | [] => p.1.1
  | b :: w => choiActionLinear (branchChoi p b) (wordState p w)

/-- Every finite word preserves the positive memory cone. -/
theorem wordState_posSemidef (p : Parameter M Branch Read) (w : List Branch) :
    (wordState p w).PosSemidef := by
  induction w with
  | nil => exact p.1.2.1
  | cons b w ih =>
      exact matrixCompletelyPositive_positive (branch_completelyPositive p b) ih

/-- The actual cylinder/terminal evaluation represented by a CP parameter. -/
noncomputable def cylinderValue (p : Parameter M Branch Read)
    (q : List Branch × Read) : ℂ :=
  ((p.2.2 q.2).value * wordState p q.1).trace

/-- Actual CP cylinders are nonnegative; this is the cone constraint not
visible to ordinary linear Hankel rank. -/
theorem cylinderValue_nonneg (p : Parameter M Branch Read)
    (q : List Branch × Read) : 0 ≤ cylinderValue p q := by
  exact Upstream.PrimitiveWeight.trace_mul_psd_nonneg
    (ScaledPositiveMatrix.value_posSemidef (p.2.2 q.2))
    (wordState_posSemidef p q.1)

theorem continuous_scaledPositiveValue (n : ℕ) :
    Continuous (fun A : ScaledPositiveMatrix n => A.value) := by
  unfold ScaledPositiveMatrix.value
  fun_prop

theorem continuous_branchChoi (b : Branch) :
    Continuous (fun p : Parameter M Branch Read => branchChoi p b) := by
  have hv : Continuous
      (fun p : Parameter M Branch Read => (p.2.1 b).value) :=
    (continuous_scaledPositiveValue (M * M)).comp
      ((continuous_apply b).comp (continuous_fst.comp continuous_snd))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply (finProdFinEquiv j)).comp
    ((continuous_apply (finProdFinEquiv i)).comp hv)

theorem continuous_choiAction
    {X : Parameter M Branch Read → Matrix (Fin M) (Fin M) ℂ}
    (hX : Continuous X) (b : Branch) :
    Continuous (fun p => choiActionLinear (branchChoi p b) (X p)) := by
  change Continuous (fun p => fun i j =>
    ∑ k, ∑ l, X p k l * branchChoi p b (k, i) (l, j))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_finsetSum Finset.univ fun k _ =>
    continuous_finsetSum Finset.univ fun l _ =>
      ((continuous_apply l).comp ((continuous_apply k).comp hX)).mul
        ((continuous_apply (l, j)).comp
          ((continuous_apply (k, i)).comp (continuous_branchChoi b)))

theorem continuous_wordState (w : List Branch) :
    Continuous (fun p : Parameter M Branch Read => wordState p w) := by
  induction w with
  | nil =>
      exact continuous_subtype_val.comp (continuous_fst)
  | cons b w ih =>
      exact continuous_choiAction ih b

theorem continuous_terminalEffect (r : Read) :
    Continuous (fun p : Parameter M Branch Read => (p.2.2 r).value) :=
  (continuous_scaledPositiveValue M).comp
    ((continuous_apply r).comp (continuous_snd.comp continuous_snd))

/-- Cylinder evaluations are finite polynomial expressions in the Choi,
source, and effect coordinates. -/
theorem continuous_cylinderValue (q : List Branch × Read) :
    Continuous (fun p : Parameter M Branch Read => cylinderValue p q) := by
  exact ((continuous_terminalEffect q.2).matrix_mul
    (continuous_wordState q.1)).matrix_trace

/-- A concrete presentation of a countable requested family of CP cylinders. -/
noncomputable def presentation
    (normalized : Set (Parameter M Branch Read))
    (hclosed : IsClosed normalized)
    (request : ℕ → List Branch × Read) (target : ℕ → ℂ) :
    Presentation M Branch Read where
  normalized := normalized
  normalized_closed := hclosed
  evaluate k p := cylinderValue p (request k)
  evaluate_continuous k := continuous_cylinderValue (request k)
  target := target

/-- Exact finite-horizon feasibility is equivalent to one recurrent CP
parameter realizing the complete requested cylinder table. -/
theorem cp_cylinder_realization_iff_all_finite_horizons
    (normalized : Set (Parameter M Branch Read))
    (hclosed : IsClosed normalized)
    (request : ℕ → List Branch × Read) (target : ℕ → ℂ) :
    (∃ p ∈ normalized, ∀ k, cylinderValue p (request k) = target k) ↔
      ∀ N, (exactHorizonSet
        (presentation normalized hclosed request target) N).Nonempty := by
  exact exact_realization_iff_all_finite_horizons
    (presentation normalized hclosed request target)

/-- Vanishing uniform finite-horizon error also produces one exact recurrent
CP realization in the same presentation. -/
theorem cp_cylinder_realization_of_vanishing_horizon_error
    (normalized : Set (Parameter M Branch Read))
    (hclosed : IsClosed normalized)
    (request : ℕ → List Branch × Read) (target : ℕ → ℂ)
    (ε : ℕ → ℝ) (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (nhds 0))
    (hfinite : ∀ N, (approximateHorizonSet
      (presentation normalized hclosed request target) ε N).Nonempty) :
    ∃ p ∈ normalized, ∀ k, cylinderValue p (request k) = target k := by
  exact exact_realization_of_vanishing_horizon_error
    (presentation normalized hclosed request target) ε hεanti hεlim hfinite

/-! ### Exact numerical obstruction and the positive-cone countermodel -/

/-- Literal manuscript bound: `M ≥ ceil (sqrt d)` whenever a Hankel table of
rank `d` factors through the `M²`-dimensional operator space. -/
theorem ceil_sqrt_rank_le_memory {d M : ℕ} (hd : d ≤ M * M) :
    ⌈Real.sqrt d⌉₊ ≤ M := by
  rw [Nat.ceil_le]
  have hcast : (d : ℝ) ≤ (M * M : ℕ) := by exact_mod_cast hd
  have hsqrt := Real.sqrt_le_sqrt hcast
  simpa [Nat.cast_mul, Real.sqrt_sq (Nat.cast_nonneg M)] using hsqrt

/-- A rank-one linear Hankel table with negative entries.  Its rank is finite,
but it violates the positive cone required of every CP cylinder. -/
noncomputable def negativeRankOneHankel (I J : Type) [Fintype I] [Fintype J] :
    Matrix I J ℂ := fun _ _ => -1

theorem negativeRankOneHankel_rank_le_one
    (I J : Type) [Fintype I] [Fintype J] :
    (negativeRankOneHankel I J).rank ≤ 1 := by
  classical
  let A : Matrix I (Fin 1) ℂ := fun _ _ => -1
  let B : Matrix (Fin 1) J ℂ := fun _ _ => 1
  have hfactor : negativeRankOneHankel I J = A * B := by
    ext i j
    change (-1 : ℂ) = ∑ _k : Fin 1, (-1 : ℂ) * 1
    rw [Fin.sum_univ_one]
    ring
  rw [hfactor]
  simpa using (cp_memory_compactness.2.1 (M := 1) A B)

/-- Finite Hankel rank alone is not sufficient for CP realizability: even the
rank-one negative table cannot equal a positive CP cylinder. -/
theorem finite_hankel_rank_not_sufficient_for_cp
    (q : List Branch × Read) :
    (∀ (I J : Type) [Fintype I] [Fintype J],
        (negativeRankOneHankel I J).rank ≤ 1) ∧
      ¬ ∃ p : Parameter M Branch Read, cylinderValue p q = -1 := by
  refine ⟨fun I J _ _ => negativeRankOneHankel_rank_le_one I J, ?_⟩
  rintro ⟨p, hp⟩
  have hnonneg := cylinderValue_nonneg p q
  rw [hp] at hnonneg
  norm_num at hnonneg

end ConcreteCPMemoryCylinder
end NCG
