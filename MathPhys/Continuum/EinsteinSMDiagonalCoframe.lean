/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Continuum.EinsteinSMReducedTopology

/-!
# The diagonal FLRW coframe `diag(1, α, α, α)`

`frameDiag α = E₀ + α D`, its determinant `α³`, membership in the oriented time-oriented coframe
chart for `α > 0`, and continuity in `α`.

Split out of `MathPhys.Continuum.EinsteinSMHomogeneousSampling` (which re-exports it);
names are unchanged.
-/

open MeasureTheory Filter Topology Set Metric

noncomputable section

namespace MathPhys
namespace EinsteinSM
namespace Comparison

/-- The FLRW coframe `diag(1, α, α, α)`. -/
def frameDiag (α : ℝ) : CoframeFibre := fun i j => if i = j then (if i = 0 then 1 else α) else 0

/-- `frameDiag α = E₀ + α D` with `E₀ = diag(1,0,0,0)`, `D = diag(0,1,1,1)`. -/
def frameE0 : CoframeFibre := fun i j => if i = j ∧ i = 0 then 1 else 0

def frameD : CoframeFibre := fun i j => if i = j ∧ i ≠ 0 then 1 else 0

theorem frameDiag_eq (α : ℝ) : frameDiag α = frameE0 + α • frameD := by
  funext i j
  by_cases hij : i = j
  · subst hij; by_cases hi : i = 0 <;> simp [frameDiag, frameE0, frameD, hi]
  · simp [frameDiag, frameE0, frameD, hij]

theorem det_frameDiag (α : ℝ) : (Matrix.of (frameDiag α)).det = α ^ 3 := by
  have : Matrix.of (frameDiag α) = Matrix.diagonal fun i : Fin 4 => if i = 0 then 1 else α := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [frameDiag]
    · simp [frameDiag, hij]
  rw [this, Matrix.det_diagonal, Fin.prod_univ_four]
  simp; ring

theorem frameDiag_mem_chart {α : ℝ} (hα : 0 < α) : frameDiag α ∈ coframeChart :=
  ⟨by rw [det_frameDiag]; positivity, by simp [frameDiag]⟩

theorem continuous_frameDiag : Continuous frameDiag := by
  have : frameDiag = fun α => frameE0 + α • frameD := funext frameDiag_eq
  rw [this]; fun_prop

end Comparison
end EinsteinSM
end MathPhys
