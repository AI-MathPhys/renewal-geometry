/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Conditional Einstein closure
  (`thm:einstein`, arithmetic manuscript)

The provable core of the horizon-thermodynamics closure:

* `null_cone_polarization`: the key polarization step — a
  symmetric bilinear form on Minkowski space whose quadratic form
  vanishes on every null vector is a scalar multiple of the
  metric (`B = B₀₀ · η`); this is exactly the passage from
  `R_ab k^a k^b = (2π/η) T_ab k^a k^b` for all null `k` to
  `R_ab + Φ g_ab = (2π/η) T_ab`;
* `einstein_assembly`: with the Bianchi/conservation
  identification `Φ = -R/2 + Λ` (displayed), the polarized
  identity rearranges exactly to the boxed Einstein equation
  `G_ab + Λ g_ab = (2π/η) T_ab`;
* `newton_constant`: the boxed coupling identification
  `8πG_N = 2π/η ⟺ G_N = 1/(4η)`.

Rendering disclosed: the Raychaudhuri/Clausius input
`R_ab k^a k^b = (2π/η) T_ab k^a k^b` (assumptions (E1)–(E4): local
Rindler horizons, Unruh temperature, `δS = ηδA`, `δQ = TδS`) and
the divergence step producing `Φ = -R/2 + Λ` from stress
conservation and the contracted Bianchi identity (E5) enter as
the displayed hypotheses — they are the manuscript's conditional
continuum inputs; the polarization and assembly algebra are
proved here.
-/

open Matrix

namespace NCG

/-- The Minkowski metric `η = diag(1,-1,-1,-1)`. -/
def minkEta : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

set_option maxHeartbeats 1000000 in
-- the six null-vector instantiations and the 16-entry final
-- check exceed the default elaboration budget
set_option linter.flexible false in
/-- Null-cone polarization: a symmetric bilinear form whose
quadratic form vanishes on every `η`-null vector is `B₀₀ · η`. -/
theorem null_cone_polarization (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hsym : ∀ i j, B i j = B j i)
    (hnull : ∀ k : Fin 4 → ℝ,
      k ⬝ᵥ minkEta.mulVec k = 0 → k ⬝ᵥ B.mulVec k = 0) :
    B = B 0 0 • minkEta := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hs2' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- pair equations e₀ ± eᵢ
  have e1p := hnull ![1, 1, 0, 0] (by
    simp [minkEta, dotProduct, Matrix.mulVec, Matrix.diagonal,
      Fin.sum_univ_four])
  have e1m := hnull ![1, -1, 0, 0] (by
    simp [minkEta, dotProduct, Matrix.mulVec, Matrix.diagonal,
      Fin.sum_univ_four])
  have e2p := hnull ![1, 0, 1, 0] (by
    simp [minkEta, dotProduct, Matrix.mulVec, Matrix.diagonal,
      Fin.sum_univ_four])
  have e2m := hnull ![1, 0, -1, 0] (by
    simp [minkEta, dotProduct, Matrix.mulVec, Matrix.diagonal,
      Fin.sum_univ_four])
  have e3p := hnull ![1, 0, 0, 1] (by
    simp [minkEta, dotProduct, Matrix.mulVec, Matrix.diagonal,
      Fin.sum_univ_four])
  have e3m := hnull ![1, 0, 0, -1] (by
    simp [minkEta, dotProduct, Matrix.mulVec, Matrix.diagonal,
      Fin.sum_univ_four])
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three] at e1p e1m e2p e2m e3p e3m
  have h01 : B 0 1 = 0 := by
    have hsym10 := hsym 1 0
    nlinarith [e1p, e1m]
  have h11 : B 1 1 = -B 0 0 := by
    have hsym10 := hsym 1 0
    nlinarith [e1p, e1m]
  have h02 : B 0 2 = 0 := by
    have hsym20 := hsym 2 0
    nlinarith [e2p, e2m]
  have h22 : B 2 2 = -B 0 0 := by
    have hsym20 := hsym 2 0
    nlinarith [e2p, e2m]
  have h03 : B 0 3 = 0 := by
    have hsym30 := hsym 3 0
    nlinarith [e3p, e3m]
  have h33 : B 3 3 = -B 0 0 := by
    have hsym30 := hsym 3 0
    nlinarith [e3p, e3m]
  -- cross equations √2·e₀ + eᵢ + eⱼ
  have c12 := hnull ![Real.sqrt 2, 1, 1, 0] (by
    simp [minkEta, dotProduct, Matrix.mulVec, Matrix.diagonal,
      Fin.sum_univ_four]
    nlinarith [hs2])
  have c13 := hnull ![Real.sqrt 2, 1, 0, 1] (by
    simp [minkEta, dotProduct, Matrix.mulVec, Matrix.diagonal,
      Fin.sum_univ_four]
    nlinarith [hs2])
  have c23 := hnull ![Real.sqrt 2, 0, 1, 1] (by
    simp [minkEta, dotProduct, Matrix.mulVec, Matrix.diagonal,
      Fin.sum_univ_four]
    nlinarith [hs2])
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three] at c12 c13 c23
  have hs10 : B 1 0 = 0 := (hsym 1 0).trans h01
  have hs20 : B 2 0 = 0 := (hsym 2 0).trans h02
  have hs30 : B 3 0 = 0 := (hsym 3 0).trans h03
  have h12 : B 1 2 = 0 := by
    rw [h01, hs10, h02, hs20, h11, h22, hsym 2 1] at c12
    ring_nf at c12
    rw [hs2'] at c12
    linarith [c12]
  have h13 : B 1 3 = 0 := by
    rw [h01, hs10, h03, hs30, h11, h33, hsym 3 1] at c13
    ring_nf at c13
    rw [hs2'] at c13
    linarith [c13]
  have h23 : B 2 3 = 0 := by
    rw [h02, hs20, h03, hs30, h22, h33, hsym 3 2] at c23
    ring_nf at c23
    rw [hs2'] at c23
    linarith [c23]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkEta, Matrix.diagonal, Matrix.smul_apply] <;>
    first
      | linarith [h01, h02, h03, h11, h22, h33, h12, h13, h23,
          hsym 1 0, hsym 2 0, hsym 3 0, hsym 2 1, hsym 3 1,
          hsym 3 2]

/-- `thm:einstein`, assembly: the polarized identity
`Ric + Φg = cT` and the Bianchi identification `Φ = -R/2 + Λ`
(displayed) give the boxed Einstein equation `G + Λg = cT`. -/
theorem einstein_assembly {n : Type*}
    (Ric g T : Matrix n n ℝ) (c Φ Rs Λ : ℝ)
    (hR : Ric + Φ • g = c • T)
    (hPhi : Φ = -(1 / 2) * Rs + Λ) :
    Ric - (1 / 2 * Rs) • g + Λ • g = c • T := by
  have hRic : Ric = c • T - Φ • g := by
    rw [← hR]
    abel
  rw [hRic, hPhi]
  module

/-- The boxed coupling identification: `8πG_N = 2π/η` gives
`G_N = 1/(4η)`. -/
theorem newton_constant (η GN : ℝ) (hη : η ≠ 0)
    (h : 8 * Real.pi * GN = 2 * Real.pi / η) :
    GN = 1 / (4 * η) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at h ⊢
  nlinarith [h, Real.pi_pos]

end NCG
