/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Lattice.Variational.DiscreteEulerConsistency

/-!
# The spatial Sobolev norm `L²_t H^k_x` on a slab of the periodic box

* `spatialL`: the spatial inclusion `ℝ³ → ℝ⁴`; `dX`: spatial derivatives `D^j_x f`;
* `sobXSq`, `sobX`: the space-time Sobolev norm `‖f‖_{L²_t H^k_x(Q)}`;
* `box`: the periodic box `[0, 2π]⁴`; `sobX_le`: sup-norm bound on a slab of the box.

Split out of `MathPhys.Continuum.NativeTailTransfer` (which re-exports it); names are
unchanged.
-/

open Finset Filter Topology Metric Set NormedSpace MeasureTheory
open scoped ContDiff

namespace MathPhys.NativeTail

open DiscreteEulerConsistency (R4)

noncomputable section

/-! ### The spatial Sobolev norm on a slab of the periodic box -/

section Sobolev

/-- The spatial inclusion `ℝ³ → ℝ⁴`, `x ↦ (0, x)`. -/
def spatialL : (Fin 3 → ℝ) →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun μ : Fin 4 =>
    Fin.cases (motive := fun _ => (Fin 3 → ℝ) →L[ℝ] ℝ) 0
      (fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i) μ

theorem norm_spatialL_le : ‖spatialL‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro μ
  induction μ using Fin.cases with
  | zero => simp [spatialL]
  | succ i => simpa [spatialL] using norm_le_pi_norm v i

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The spatial derivative `D^j_x f(z)` (the `j`-th derivative in the three spatial directions). -/
def dX (j : ℕ) (f : R4 → W) (z : R4) : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin 3 → ℝ) W :=
  (iteratedFDeriv ℝ j f z).compContinuousLinearMap fun _ => spatialL

theorem norm_dX_le (j : ℕ) (f : R4 → W) (z : R4) :
    ‖dX j f z‖ ≤ ‖iteratedFDeriv ℝ j f z‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_spatialL_le)

/-- The squared space-time Sobolev norm `∫_Q Σ_{j ≤ k} ‖D^j_x f‖²` (`L²_t H^k_x(Q)`). -/
def sobXSq (k : ℕ) (Q : Set R4) (f : R4 → W) : ℝ :=
  ∫ z in Q, ∑ j ∈ Finset.range (k + 1), ‖dX j f z‖ ^ 2

/-- The space-time Sobolev norm `‖f‖_{L²_t H^k_x(Q)}`. -/
def sobX (k : ℕ) (Q : Set R4) (f : R4 → W) : ℝ := Real.sqrt (sobXSq k Q f)

/-- The periodic box `[0, 2π]⁴`. -/
def box : Set R4 := Set.Icc 0 fun _ => 2 * Real.pi

theorem volume_box_ne_top : volume box ≠ ⊤ := by
  unfold box; rw [Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

theorem measureReal_box : volume.real box = (2 * Real.pi) ^ 4 := by
  unfold box
  rw [Measure.real, Real.volume_Icc_pi_toReal (fun _ => by positivity)]
  simp

/-- **Sup-norm bound for the space-time Sobolev norm** on a slab of the box. -/
theorem sobX_le {k : ℕ} {Q : Set R4} (hQ : Q ⊆ box) {f : R4 → W} {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z ∈ Q, ∀ j ≤ k, ‖iteratedFDeriv ℝ j f z‖ ≤ b) :
    sobX k Q f ≤ Real.sqrt ((k + 1) * (2 * Real.pi) ^ 4) * b := by
  have hQfin : volume Q < ⊤ := (measure_mono hQ).trans_lt (lt_top_iff_ne_top.mpr volume_box_ne_top)
  have hpt : ∀ z ∈ Q, ‖∑ j ∈ Finset.range (k + 1), ‖dX j f z‖ ^ 2‖ ≤ (k + 1) * b ^ 2 := by
    intro z hz
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
    calc ∑ j ∈ Finset.range (k + 1), ‖dX j f z‖ ^ 2 ≤ ∑ _j ∈ Finset.range (k + 1), b ^ 2 :=
          Finset.sum_le_sum fun j hj => pow_le_pow_left₀ (norm_nonneg _)
            ((norm_dX_le j f z).trans (hb z hz j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))) 2
      _ = (k + 1) * b ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hint := norm_setIntegral_le_of_norm_le_const hQfin hpt
  have hreal : volume.real Q ≤ (2 * Real.pi) ^ 4 := by
    rw [← measureReal_box]; exact measureReal_mono hQ volume_box_ne_top
  have hsq : sobXSq k Q f ≤ (k + 1) * (2 * Real.pi) ^ 4 * b ^ 2 := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine hint.trans ?_
    calc (k + 1 : ℝ) * b ^ 2 * volume.real Q ≤ (k + 1) * b ^ 2 * (2 * Real.pi) ^ 4 := by gcongr
      _ = (k + 1) * (2 * Real.pi) ^ 4 * b ^ 2 := by ring
  unfold sobX
  calc Real.sqrt (sobXSq k Q f) ≤ Real.sqrt ((k + 1) * (2 * Real.pi) ^ 4 * b ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt ((k + 1) * (2 * Real.pi) ^ 4) * b := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb0]

end Sobolev

end

end MathPhys.NativeTail
