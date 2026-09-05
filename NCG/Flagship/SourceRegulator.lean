/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniform finite-horizon saturation is regulator stable
  (`thm:source-regulator-master`, flagship manuscript)

* `frame_bound_limit`: the stability half — the cone
  `{X : X ⪰ cI}` is closed under entrywise limits, so a uniform
  frame lower bound `𝒞𝒞* ⪰ cI` along the regulator survives in
  the limit; the limit frame operator is bounded below and hence
  surjective in finite dimension (cyclicity at the same horizon);
* `cyclicity_collapse`: the failure half — for
  `T = diag(0, 1/2)` and the limit source `s = e₁`, the
  two-step frame Gram of `(s, Ts)` is singular (`det = 0`), so
  without a uniform lower bound cyclicity collapses even in
  dimension two.

Rendering disclosed: the norm convergence of the controllability
operators along the regulator is rendered entrywise (equivalent
in finite dimension); the isotypic refinement (character
projectors converging) is the manuscript's additional clause on
top of the same closed-cone argument.
-/

open Filter

namespace NCG

/-- The uniform frame lower bound survives the regulator limit:
the PSD cone `{X ⪰ cI}` is closed under entrywise limits. -/
theorem frame_bound_limit {n : Type*} [Fintype n]
    (M : ℕ → Matrix n n ℝ) (Mlim : Matrix n n ℝ) (c : ℝ)
    (hconv : ∀ i j,
      Tendsto (fun k => M k i j) atTop (nhds (Mlim i j)))
    (hlb : ∀ k (v : n → ℝ),
      c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M k).mulVec v) :
    ∀ v : n → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ Mlim.mulVec v := by
  intro v
  have hq : Tendsto (fun k => v ⬝ᵥ (M k).mulVec v) atTop
      (nhds (v ⬝ᵥ Mlim.mulVec v)) := by
    simp only [dotProduct, Matrix.mulVec]
    exact tendsto_finsetSum _ fun i _ =>
      Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ =>
        (hconv i j).mul_const _)
  exact ge_of_tendsto hq
    (Eventually.of_forall fun k => hlb k v)

/-- Without a uniform lower bound, cyclicity collapses: at the
regulator limit `s = e₁`, the frame Gram of `(s, Ts)` for
`T = diag(0, 1/2)` is singular. -/
theorem cyclicity_collapse :
    (Matrix.of
      ![![(![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0],
          (![1, 0] : Fin 2 → ℝ) ⬝ᵥ
            (Matrix.diagonal ![0, 1/2]).mulVec ![1, 0]],
        ![(Matrix.diagonal ![0, 1/2]).mulVec ![1, 0] ⬝ᵥ ![1, 0],
          (Matrix.diagonal ![0, 1/2]).mulVec ![1, 0] ⬝ᵥ
            (Matrix.diagonal ![0, 1/2]).mulVec ![1, 0]]]).det
    = 0 := by
  have hTs : (Matrix.diagonal ![0, 1/2]).mulVec
      (![1, 0] : Fin 2 → ℝ) = ![0, 0] := by
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.diagonal, dotProduct]
  rw [hTs]
  simp [Matrix.det_fin_two, dotProduct, Fin.sum_univ_two]

end NCG
