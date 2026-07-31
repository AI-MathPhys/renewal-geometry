/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The ground-state transform and the scalar potential
  (`lem:canonical-drift-split`, GR_emergence)

The drift-removal mechanism of the canonical decomposition
`Π₊ℓ₁Π₊ = 𝒜_geo + 𝒜_grad + 𝒜_irr`: conjugating the diffusion
generator by `e^{φ/2}` (with `r_* = e^{-φ}` the stationary density)
removes the gradient drift and produces the boxed real scalar
potential.

* `ground_state_first_order` — the first-order conjugation:
  `e^{φ/2}·(e^{-φ/2}f)' = f' - (φ'/2)f`;
* `ground_state_conjugation` — the full second-order identity: for
  the generator `∂(D∂·)`,
  `e^{φ/2}·(D·(e^{-φ/2}f)')' = Df'' + (D' - Dφ')f'
    + (¼Dφ'² - ½(D'φ' + Dφ''))f`
  — the zeroth-order coefficient is exactly the boxed
  `V = ¼⟨∇φ, D∇φ⟩ - ½ div(D∇φ)` in one dimension.

Together with `NCG.transport_decomp_trace` (the anti-Hermitian
geometric part drops from the real trace) this proves the two
mechanisms of the decomposition; the `L²(r_*)`-orthogonality of the
three parts for the concrete channel is the disclosed
operator-theoretic layer.
-/

namespace NCG

private theorem gsInner {f f' phi phi' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y)
    (hphi : ∀ y, HasDerivAt phi (phi' y) y) (y : ℝ) :
    HasDerivAt (fun z => Real.exp (-phi z / 2) * f z)
      (Real.exp (-phi y / 2) * (f' y - phi' y / 2 * f y)) y := by
  have hexp : HasDerivAt (fun z => Real.exp (-phi z / 2))
      (Real.exp (-phi y / 2) * (-phi' y / 2)) y := by
    have h1 : HasDerivAt (fun z => -phi z / 2) (-phi' y / 2) y :=
      ((hphi y).neg).div_const 2
    exact h1.exp
  exact (hexp.mul (hf y)).congr_deriv (by ring)

/-- First-order conjugation: the ground-state transform removes the
gradient drift. -/
theorem ground_state_first_order {f f' phi phi' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y)
    (hphi : ∀ y, HasDerivAt phi (phi' y) y) (x : ℝ) :
    Real.exp (phi x / 2) *
        deriv (fun z => Real.exp (-phi z / 2) * f z) x
      = f' x - phi' x / 2 * f x := by
  rw [(gsInner hf hphi x).deriv, ← mul_assoc, ← Real.exp_add,
    show phi x / 2 + -phi x / 2 = 0 from by ring, Real.exp_zero,
    one_mul]

/-- The full second-order conjugation identity: the zeroth-order
coefficient is the boxed scalar potential
`V = ¼Dφ'² - ½(D'φ' + Dφ'')`. -/
theorem ground_state_conjugation
    {f f' f'' phi phi' phi'' D D' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hphi : ∀ y, HasDerivAt phi (phi' y) y)
    (hphi' : ∀ y, HasDerivAt phi' (phi'' y) y)
    (hD : ∀ y, HasDerivAt D (D' y) y) (x : ℝ) :
    Real.exp (phi x / 2) *
        deriv (fun y => D y *
          deriv (fun z => Real.exp (-phi z / 2) * f z) y) x
      = D x * f'' x + (D' x - D x * phi' x) * f' x
        + (D x * phi' x ^ 2 / 4
            - (D' x * phi' x + D x * phi'' x) / 2) * f x := by
  have hcongr : (fun y => D y *
        deriv (fun z => Real.exp (-phi z / 2) * f z) y)
      = fun y => D y *
        (Real.exp (-phi y / 2) * (f' y - phi' y / 2 * f y)) := by
    funext y
    rw [(gsInner hf hphi y).deriv]
  rw [hcongr]
  -- the transformed first-order factor and its derivative
  have hG : ∀ y, HasDerivAt (fun z => f' z - phi' z / 2 * f z)
      (f'' y - (phi'' y / 2 * f y + phi' y / 2 * f' y)) y := by
    intro y
    have h1 : HasDerivAt (fun z => phi' z / 2 * f z)
        (phi'' y / 2 * f y + phi' y / 2 * f' y) y := by
      have := ((hphi' y).div_const 2).mul (hf y)
      exact this.congr_deriv (by ring)
    exact (hf' y).fun_sub h1
  have hexpG : ∀ y, HasDerivAt
      (fun z => Real.exp (-phi z / 2) * (f' z - phi' z / 2 * f z))
      (Real.exp (-phi y / 2) *
        ((f'' y - (phi'' y / 2 * f y + phi' y / 2 * f' y))
          - phi' y / 2 * (f' y - phi' y / 2 * f y))) y := by
    intro y
    have hexp : HasDerivAt (fun z => Real.exp (-phi z / 2))
        (Real.exp (-phi y / 2) * (-phi' y / 2)) y := by
      have h1 : HasDerivAt (fun z => -phi z / 2) (-phi' y / 2) y :=
        ((hphi y).neg).div_const 2
      exact h1.exp
    exact (hexp.mul (hG y)).congr_deriv (by ring)
  have houter : HasDerivAt (fun y => D y *
      (Real.exp (-phi y / 2) * (f' y - phi' y / 2 * f y)))
      (Real.exp (-phi x / 2) *
        (D' x * (f' x - phi' x / 2 * f x)
          + D x * ((f'' x - (phi'' x / 2 * f x + phi' x / 2 * f' x))
              - phi' x / 2 * (f' x - phi' x / 2 * f x)))) x := by
    have := (hD x).mul (hexpG x)
    exact this.congr_deriv (by ring)
  rw [houter.deriv, ← mul_assoc, ← Real.exp_add,
    show phi x / 2 + -phi x / 2 = 0 from by ring, Real.exp_zero,
    one_mul]
  ring

/-- `thm:drift-cancellation` (Doob transform of the reversible
generator): conjugating `Lg = Dg'' + (D' + Dφ')g'` (the reversible
diffusion with stationary density `r_* = e^{-φ}` and gradient drift
`Dφ' = -D∇log r_*`) by `e^{φ/2}` removes the first-order drift and
leaves the divergence-form operator minus the boxed real potential
`V = ¼Dφ'² + ½(D'φ' + Dφ'')
   = ¼⟨∇log r_*, D∇log r_*⟩ + ½ div(D∇log r_*^{1/2})`
(in one dimension, with `φ' = -∇log r_*`). -/
theorem doob_drift_cancellation
    {f f' f'' phi phi' phi'' D D' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hphi : ∀ y, HasDerivAt phi (phi' y) y)
    (hphi' : ∀ y, HasDerivAt phi' (phi'' y) y) (x : ℝ) :
    Real.exp (phi x / 2) *
        (D x * deriv (deriv (fun z => Real.exp (-phi z / 2) * f z)) x
          + (D' x + D x * phi' x)
              * deriv (fun z => Real.exp (-phi z / 2) * f z) x)
      = D x * f'' x + D' x * f' x
        - (D x * phi' x ^ 2 / 4
            + (D' x * phi' x + D x * phi'' x) / 2) * f x := by
  have hg1 : deriv (fun z => Real.exp (-phi z / 2) * f z)
      = fun y => Real.exp (-phi y / 2) * (f' y - phi' y / 2 * f y) := by
    funext y
    rw [(gsInner hf hphi y).deriv]
  rw [hg1]
  have hG : ∀ y, HasDerivAt (fun z => f' z - phi' z / 2 * f z)
      (f'' y - (phi'' y / 2 * f y + phi' y / 2 * f' y)) y := by
    intro y
    have h1 : HasDerivAt (fun z => phi' z / 2 * f z)
        (phi'' y / 2 * f y + phi' y / 2 * f' y) y := by
      have := ((hphi' y).div_const 2).mul (hf y)
      exact this.congr_deriv (by ring)
    exact (hf' y).fun_sub h1
  have hexpG : HasDerivAt
      (fun z => Real.exp (-phi z / 2) * (f' z - phi' z / 2 * f z))
      (Real.exp (-phi x / 2) *
        ((f'' x - (phi'' x / 2 * f x + phi' x / 2 * f' x))
          - phi' x / 2 * (f' x - phi' x / 2 * f x))) x := by
    have hexp : HasDerivAt (fun z => Real.exp (-phi z / 2))
        (Real.exp (-phi x / 2) * (-phi' x / 2)) x := by
      have h1 : HasDerivAt (fun z => -phi z / 2) (-phi' x / 2) x :=
        ((hphi x).neg).div_const 2
      exact h1.exp
    exact (hexp.mul (hG x)).congr_deriv (by ring)
  rw [hexpG.deriv]
  rw [show D x * (Real.exp (-phi x / 2) *
        ((f'' x - (phi'' x / 2 * f x + phi' x / 2 * f' x))
          - phi' x / 2 * (f' x - phi' x / 2 * f x)))
      + (D' x + D x * phi' x)
          * (Real.exp (-phi x / 2) * (f' x - phi' x / 2 * f x))
    = Real.exp (-phi x / 2) *
        (D x * ((f'' x - (phi'' x / 2 * f x + phi' x / 2 * f' x))
            - phi' x / 2 * (f' x - phi' x / 2 * f x))
          + (D' x + D x * phi' x) * (f' x - phi' x / 2 * f x))
    from by ring]
  rw [← mul_assoc, ← Real.exp_add,
    show phi x / 2 + -phi x / 2 = 0 from by ring, Real.exp_zero,
    one_mul]
  ring

end NCG
