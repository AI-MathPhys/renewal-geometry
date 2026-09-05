/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Quartic-ray non-identifiability
  (`thm:quartic-ray-nonidentifiability-consolidated`, SM_emergence)

An explicit two-field counterexample: two scalar potentials with
identical light-ray restrictions (same light-ray norm and quartic)
but inequivalent mixed quartic couplings produce

* different heavy Hessians along the light ray
  (`quartic_second_deriv` computes `∂²_y V = ρx² + M²`), and
* different tree-matched low-energy quartics
  (`ray_effective_is_min` / `ray_effective_attained` identify the
  Schur-complement tree matching `V_eff = C - B²/(4A)`).

* `quarticPotential` — `V = (λ/4)x⁴ + κx²y + (ρ/2)x²y² + (M²/2)y²`;
* `light_ray_agreement` — the couplings `(κ, ρ)` are invisible on
  the light ray `y = 0`;
* `quartic_ray_nonidentifiability` — the packaged counterexample
  `(κ,ρ) = (0,1)` versus `(1,0)`: same light-ray data, different
  heavy Hessian at every nonzero background, different tree-matched
  quartic.
-/

namespace NCG

/-- The two-field scalar potential
`V = (λ/4)x⁴ + κ·x²y + (ρ/2)·x²y² + (M²/2)·y²`, with `x` the
protected light-ray direction and `y` a heavy direction. -/
noncomputable def quarticPotential (lam kap rho Msq x y : ℝ) : ℝ :=
  lam / 4 * x ^ 4 + kap * x ^ 2 * y + rho / 2 * x ^ 2 * y ^ 2
    + Msq / 2 * y ^ 2

/-- The mixed couplings are invisible on the light ray `y = 0`. -/
theorem light_ray_agreement (lam kap1 rho1 kap2 rho2 Msq x : ℝ) :
    quarticPotential lam kap1 rho1 Msq x 0
      = quarticPotential lam kap2 rho2 Msq x 0 := by
  simp [quarticPotential]

/-- First heavy derivative: `∂_y V = κx² + (ρx² + M²)y`. -/
theorem quartic_first_deriv (lam kap rho Msq x y : ℝ) :
    HasDerivAt (fun y => quarticPotential lam kap rho Msq x y)
      (kap * x ^ 2 + (rho * x ^ 2 + Msq) * y) y := by
  exact ((((hasDerivAt_const y (lam / 4 * x ^ 4)).add
      ((hasDerivAt_id y).const_mul (kap * x ^ 2))).add
      ((hasDerivAt_pow 2 y).const_mul (rho / 2 * x ^ 2))).add
      ((hasDerivAt_pow 2 y).const_mul (Msq / 2))).congr_deriv
    (by push_cast; ring)

/-- Second heavy derivative (the heavy Hessian along the ray):
`∂²_y V = ρx² + M²`. -/
theorem quartic_second_deriv (rho Msq x y kap : ℝ) :
    HasDerivAt (fun y => kap * x ^ 2 + (rho * x ^ 2 + Msq) * y)
      (rho * x ^ 2 + Msq) y := by
  exact ((hasDerivAt_const y (kap * x ^ 2)).add
    ((hasDerivAt_id y).const_mul (rho * x ^ 2 + Msq))).congr_deriv
    (by ring)

/-- The tree-matched (Schur-complement) low-energy potential on the
light ray: `V_eff = (λ/4)x⁴ - (κx²)²/(4A)`, `A = (ρx² + M²)/2`. -/
noncomputable def rayEffective (lam kap rho Msq x : ℝ) : ℝ :=
  lam / 4 * x ^ 4
    - (kap * x ^ 2) ^ 2 / (4 * (rho / 2 * x ^ 2 + Msq / 2))

/-- Completing the square: the potential in canonical
`C + B·y + A·y²` form. -/
theorem quartic_canonical_form (lam kap rho Msq x y : ℝ) :
    quarticPotential lam kap rho Msq x y
      = lam / 4 * x ^ 4 + (kap * x ^ 2) * y
        + (rho / 2 * x ^ 2 + Msq / 2) * y ^ 2 := by
  unfold quarticPotential
  ring

/-- The tree matching is the heavy-direction minimum. -/
theorem ray_effective_is_min (lam kap rho Msq x : ℝ)
    (hA : 0 < rho / 2 * x ^ 2 + Msq / 2) (y : ℝ) :
    rayEffective lam kap rho Msq x
      ≤ quarticPotential lam kap rho Msq x y := by
  rw [quartic_canonical_form]
  set A : ℝ := rho / 2 * x ^ 2 + Msq / 2 with hAdef
  set B : ℝ := kap * x ^ 2 with hBdef
  set C : ℝ := lam / 4 * x ^ 4 with hCdef
  have heff : rayEffective lam kap rho Msq x
      = C - B ^ 2 / (4 * A) := by
    rw [rayEffective]
  rw [heff]
  have hpos : (0 : ℝ) < 4 * A := by linarith
  have h1 : (C + B * y + A * y ^ 2) - (C - B ^ 2 / (4 * A))
      = (2 * A * y + B) ^ 2 / (4 * A) := by
    field_simp
    ring
  have h2 : 0 ≤ (2 * A * y + B) ^ 2 / (4 * A) :=
    div_nonneg (sq_nonneg _) (le_of_lt hpos)
  linarith [h1, h2]

/-- The tree matching is attained at the stationary heavy value
`y* = -B/(2A)`. -/
theorem ray_effective_attained (lam kap rho Msq x : ℝ) :
    quarticPotential lam kap rho Msq x
        (-(kap * x ^ 2) / (2 * (rho / 2 * x ^ 2 + Msq / 2)))
      = rayEffective lam kap rho Msq x := by
  rw [quartic_canonical_form, rayEffective]
  field_simp
  ring

/-- `thm:quartic-ray-nonidentifiability-consolidated`: the packaged
counterexample.  The couplings `(κ,ρ) = (0,1)` and `(1,0)` agree on
all light-ray data but give different heavy Hessians `ρv² + M²`
at every nonzero background and different tree-matched low-energy
quartics. -/
theorem quartic_ray_nonidentifiability :
    ∃ k1 r1 k2 r2 : ℝ,
      ((k1, r1) ≠ (k2, r2))
      ∧ (∀ lam Msq x : ℝ, quarticPotential lam k1 r1 Msq x 0
          = quarticPotential lam k2 r2 Msq x 0)
      ∧ (∀ v : ℝ, v ≠ 0 →
          r1 * v ^ 2 + 1 ≠ r2 * v ^ 2 + 1)
      ∧ rayEffective 1 k1 r1 1 1 ≠ rayEffective 1 k2 r2 1 1 := by
  refine ⟨0, 1, 1, 0, ?_, ?_, ?_, ?_⟩
  · simp
  · intro lam Msq x
    exact light_ray_agreement lam 0 1 1 0 Msq x
  · intro v hv
    have hv2 : 0 < v ^ 2 := by positivity
    intro h
    rw [one_mul, zero_mul] at h
    linarith
  · rw [rayEffective, rayEffective]
    norm_num

end NCG
