/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Reward pressure: action-slope reconstruction and the pressure
  jet (`thm:reward-pressure-reconstruction`,
  `thm:reward-pressure-jet`, Gran-Tensor manuscript)

Finite marked-cycle rendering: cycles `Ω` (rows), reward
directions `V` (columns), score writer `S : Ω×V`, action slope
`G : Ω×V`, duration writer `T : Ω×1`, pressure slope
`π : 1×V`, stationary weight column `w : Ω×1`.

* `slope_reconstruction`: the boxed pair
  `S = -G - Tπ ⟺ G = -S - Tπ` — the normalized score and the
  duration writer reconstruct the complete uncentered
  cycle-action slope;
* `pressure_slope_anchor`: the boxed anchor `π(v) = -γ(v)/τ̄` —
  centering `S*w = 0` and `T*w = τ̄` force `τ̄·π* = -G*w = -γ`;
* `pressure_jet_gram`: the boxed complete mixed action Gram —
  `G*G = S*S + δ*π + π*δ + m₂·π*π` with `δ = T*S` and
  `T*T = m₂`, so one pressure surface reconstructs every
  marginal and mixed action block;
* `pressure_hessian_psd`: the boxed Hessian positivity —
  `D²𝒫(0) = τ̄⁻¹·S*S ⪰ 0`.

Rendering disclosed: the analytic implicit-function step
(existence and uniqueness of the pressure `𝒫_X` solving
`ℒ_X(q, 𝒫_X(q)) = 1` near the origin, and the identification of
its derivatives with the displayed expectations) and the
covariance-rank clause are the manuscript's analytic layer; the
exact matrix identities among the jets are proved here.
-/

open Matrix

namespace NCG

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

omit [Fintype Ω] [Fintype V] in
/-- Boxed slope reconstruction: `S = -G - Tπ` inverts to
`G = -S - Tπ`. -/
theorem slope_reconstruction (S G : Matrix Ω V ℂ)
    (T : Matrix Ω (Fin 1) ℂ) (piX : Matrix (Fin 1) V ℂ)
    (hS : S = -G - T * piX) : G = -S - T * piX := by
  rw [hS]
  abel

omit [Fintype V] in
/-- Boxed pressure anchor: centering `S*w = 0` and duration
normalization `T*w = τ̄` give `τ̄ • π* = -(G*w)`, i.e.
`π(v) = -γ(v)/τ̄` with `γ = G*𝟙`. -/
theorem pressure_slope_anchor (S G : Matrix Ω V ℂ)
    (T w : Matrix Ω (Fin 1) ℂ) (piX : Matrix (Fin 1) V ℂ)
    (τbar : ℂ) (hS : S = -G - T * piX)
    (hcenter : Sᴴ * w = 0)
    (hτ : Tᴴ * w = τbar • (1 : Matrix (Fin 1) (Fin 1) ℂ)) :
    τbar • piXᴴ = -(Gᴴ * w) := by
  have hexp : Sᴴ * w = -(Gᴴ * w) - τbar • piXᴴ := by
    rw [hS]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.neg_mul,
      Matrix.mul_assoc, hτ, Matrix.mul_smul, Matrix.mul_one]
  rw [hcenter] at hexp
  have h0 : -(Gᴴ * w) - τbar • piXᴴ = 0 := hexp.symm
  have h1 : -(Gᴴ * w) = τbar • piXᴴ := sub_eq_zero.mp h0
  exact h1.symm

omit [Fintype V] in
/-- Boxed pressure-jet Gram: with `G = -S - Tπ` and
`T*T = m₂`, the complete mixed action Gram splits as
`G*G = S*S + δ*π + π*δ + m₂·π*π` with `δ = T*S`. -/
theorem pressure_jet_gram (S G : Matrix Ω V ℂ)
    (T : Matrix Ω (Fin 1) ℂ) (piX : Matrix (Fin 1) V ℂ)
    (m2 : ℂ) (hG : G = -S - T * piX)
    (hm2 : Tᴴ * T = m2 • (1 : Matrix (Fin 1) (Fin 1) ℂ)) :
    Gᴴ * G = Sᴴ * S + (Tᴴ * S)ᴴ * piX + piXᴴ * (Tᴴ * S)
      + m2 • (piXᴴ * piX) := by
  have hneg : -S - T * piX = -(S + T * piX) := by abel
  rw [hG, hneg, Matrix.conjTranspose_neg, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg, Matrix.conjTranspose_add,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.conjTranspose_mul]
  have h1 : (Tᴴ * S)ᴴ * piX = Sᴴ * (T * piX) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have h2 : piXᴴ * Tᴴ * (T * piX) = m2 • (piXᴴ * piX) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ T piX, hm2,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  have h3 : piXᴴ * Tᴴ * S = piXᴴ * (Tᴴ * S) := by
    rw [Matrix.mul_assoc]
  rw [h2, h3, ← h1]
  abel

open scoped ComplexOrder in
/-- Boxed Hessian positivity: `D²𝒫(0) = τ̄⁻¹·S*S ⪰ 0`. -/
theorem pressure_hessian_psd [DecidableEq V]
    (S : Matrix Ω V ℂ) (τbar : ℝ) (hτ : 0 < τbar) :
    ((τbar⁻¹ : ℝ) • (Sᴴ * S)).PosSemidef :=
  (Matrix.posSemidef_conjTranspose_mul_self S).smul
    (inv_nonneg.mpr hτ.le)

end NCG
