/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Minkowski matrix, coframe metric and the Einstein–Standard-Model coefficient bank

The Minkowski matrix `η = diag(-1,1,1,1)`, the reconstructed Lorentzian metric
`g = eᵀ η e` of a coframe `e`, and the coefficient bank
`(κ, Λ, g₁, g₂, g₃, λ_H, v_H, 𝐘)` of an Einstein–Standard-Model action.
Generic definitions used by the continuum Einstein–Standard-Model action.
-/

open Matrix

namespace MathPhys

/-- The Minkowski matrix `η = diag(-1,1,1,1)`. -/
def minkowskiEta : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![-1, 1, 1, 1]

/-- The reconstructed Lorentzian metric `g = eᵀ η e` of a coframe `e`. -/
def coframeMetric (e : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  eᵀ * minkowskiEta * e

/-- The coefficient bank `θ_h = (κ_h, Λ_h, g_{1,h}, g_{2,h}, g_{3,h}, λ_{H,h},
v_{H,h}, 𝐘_h)` of (I3); the Yukawa matrices are `3 × 3` generation
matrices indexed by the declared Yukawa sectors. -/
structure CoefficientBank (YukawaSector : Type) where
  /-- gravitational coupling `κ` -/
  kappa : ℝ
  /-- cosmological constant `Λ` -/
  Lambda : ℝ
  /-- hypercharge coupling `g₁` -/
  g1 : ℝ
  /-- weak coupling `g₂` -/
  g2 : ℝ
  /-- strong coupling `g₃` -/
  g3 : ℝ
  /-- Higgs self-coupling `λ_H` -/
  lambdaH : ℝ
  /-- Higgs vacuum scale `v_H` -/
  vH : ℝ
  /-- Yukawa generation matrices `𝐘` -/
  yukawa : YukawaSector → Matrix (Fin 3) (Fin 3) ℂ

end MathPhys
