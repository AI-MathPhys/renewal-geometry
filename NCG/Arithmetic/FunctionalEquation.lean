/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.ImprimitiveEuler

/-!
# Typed primitive functional equation and primitive reduction
  (`thm:v002-functional-equation`,
   `corollary:primitive-reduction-of-dirichlet-grh`,
   arithmetic manuscript)

* `symmLambda`: the symmetrically normalized completed
  L-function `Λ(s,χ) = N^{s/2}·Λ_Mathlib(s,χ)` — multiplying
  Mathlib's completed L-function by `N^{s/2}` absorbs the
  asymmetric conductor power of its functional equation;
* `functional_equation_symmetric`: the boxed scalar identity
  `Λ(1-s,χ) = ε_χ·Λ(s,χ⁻¹)`, from Mathlib's
  `IsPrimitive.completedLFunction_one_sub` by collecting the
  conductor powers `(1-s)/2 + (s - 1/2) = s/2`;
* `functional_equation_deriv`: differentiating the identity gives
  `Λ'(1-s,χ) = -ε_χ·Λ'(s,χ⁻¹)`;
* `functional_equation_logderiv`: the boxed logarithmic-derivative
  antisymmetry `Λ'/Λ(1-s,χ) = -(Λ'/Λ)(s,χ⁻¹)` — the constant root
  number drops out and the minus sign of `1-s` remains;
* `primitive_reduction_of_dirichlet_grh`: GRH for the inducing
  primitive character transfers verbatim to every induced
  character — through the proved strip-zeros identification of
  the imprimitive record (`prop:v002-imprimitive`), so the
  reduction needs no uniformity in the conductor.

Rendering disclosed: Mathlib's inverse character `χ⁻¹` renders the
manuscript's conjugate `χ̄` (they agree on the unit circle); the
unimodularity `|ε_χ| = 1` and hence `ε_χ ≠ 0` is classical
(Gauss-sum evaluation) and enters the log-derivative statement as
the displayed hypothesis `hε`; the conjugation law
`ε_{χ̄} = ε̄_χ` and the doubled-channel matrix form (the
self-adjoint unitary `R_χ`) are the manuscript's displayed
bookkeeping on top of the scalar identity.
-/

open Complex DirichletCharacter

namespace NCG

section FE

variable {N : ℕ} [NeZero N]

/-- Symmetrically normalized completed L-function: Mathlib's
completed L-function carries the conductor power asymmetrically;
`N^{s/2}` symmetrizes it. -/
noncomputable def symmLambda (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * completedLFunction χ s

/-- `thm:v002-functional-equation`, first box: the symmetric
scalar functional equation `Λ(1-s,χ) = ε_χ Λ(s,χ⁻¹)`. -/
theorem functional_equation_symmetric (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (s : ℂ) :
    symmLambda χ (1 - s) = rootNumber χ * symmLambda χ⁻¹ s := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  calc symmLambda χ (1 - s)
      = (N : ℂ) ^ ((1 - s) / 2)
        * ((N : ℂ) ^ (s - 1 / 2) * rootNumber χ
          * completedLFunction χ⁻¹ s) := by
        rw [symmLambda, hχ.completedLFunction_one_sub]
    _ = ((N : ℂ) ^ ((1 - s) / 2) * (N : ℂ) ^ (s - 1 / 2))
        * (rootNumber χ * completedLFunction χ⁻¹ s) := by ring
    _ = (N : ℂ) ^ ((1 - s) / 2 + (s - 1 / 2))
        * (rootNumber χ * completedLFunction χ⁻¹ s) := by
        rw [Complex.cpow_add _ _ hN]
    _ = rootNumber χ * symmLambda χ⁻¹ s := by
        rw [show (1 - s) / 2 + (s - 1 / 2) = s / 2 by ring,
          symmLambda]
        ring

/-- Differentiated functional equation: the reflection `1 - s`
contributes the minus sign. -/
theorem functional_equation_deriv (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (s : ℂ) :
    deriv (symmLambda χ) (1 - s)
      = -(rootNumber χ * deriv (symmLambda χ⁻¹) s) := by
  have h1 : (fun y : ℂ => symmLambda χ (1 - y))
      = fun y => rootNumber χ * symmLambda χ⁻¹ y :=
    funext fun y => functional_equation_symmetric χ hχ y
  have h2 := deriv_comp_const_sub (f := symmLambda χ) (a := 1)
    (x := s)
  rw [h1, deriv_const_mul_field] at h2
  linear_combination h2

/-- `thm:v002-functional-equation`, second box: log-derivative
antisymmetry — the constant root number drops out. -/
theorem functional_equation_logderiv (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (s : ℂ)
    (hε : rootNumber χ ≠ 0) (hval : symmLambda χ⁻¹ s ≠ 0) :
    deriv (symmLambda χ) (1 - s) / symmLambda χ (1 - s)
      = -(deriv (symmLambda χ⁻¹) s / symmLambda χ⁻¹ s) := by
  rw [functional_equation_symmetric χ hχ s,
    functional_equation_deriv χ hχ s]
  field_simp

end FE

section Reduction

variable {M N : ℕ} [NeZero M] [NeZero N]

/-- `corollary:primitive-reduction-of-dirichlet-grh`: the
critical-line assertion for the inducing character transfers to
every induced character, with no uniformity in the conductor. -/
theorem primitive_reduction_of_dirichlet_grh (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M)
    (hGRH : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      LFunction χ s = 0 → s.re = 1 / 2) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → (χ ≠ 1 ∨ s ≠ 1) →
      LFunction (changeLevel hMN χ) s = 0 → s.re = 1 / 2 := by
  intro s hs0 hs1 hne h
  exact hGRH s hs0 hs1
    ((imprimitive_strip_zeros hMN χ hs0 hne).mp h)

end Reduction

end NCG
