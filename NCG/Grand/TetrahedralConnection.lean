/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# One-orbit tetrahedral connection and curvature
  (`thm:tetrahedral-prototype-connection`,
  Gran-Tensor manuscript)

* `tetrahedral_prototype_connection`:
  (i) the boxed prototype-triangle holonomy identity: for an
      order-three rotation `R` (`R³ = 1`) the transported
      routers `U₃₁ = RUR²`, `U₂₃ = R²UR` compose to
      `U₃₁·U₂₃·U₁₂ = (RU)³` in any monoid — one triangle
      carries the whole curvature;
  (ii) the boxed area-scaled curvature coefficient: when the
      orbit sum cancels (`A₁ + A₂ + A₃ = 0`, with
      `A₁ = A`, `A₂ = RAR⁻¹`, `A₃ = R²AR⁻²`), the ordered
      second-order term of the three truncated exponentials
      collapses to the single commutator
      `½(A₁² + A₂² + A₃²) + (A₁A₂ + A₁A₃ + A₂A₃)
        = ½[A₁, A₂]`,
      i.e. `H₁₂₃(h) = I + (h²/2)[A, RAR⁻¹] + O(h³)`;
  (iii) the scalar-fibre impossibility: on a fibre where the
      three orbit copies coincide, the cancellation
      condition reads `3A = 0`, which forces `A = 0` — no
      nonzero dense tetrahedral connection survives on a
      trivial fibre.

The `S₄` representation bookkeeping (stabilizer commutation
`[U, ρ(k)] = 0`, reversal `ρ(s)Uρ(s)* = U*`, conjugacy of
the other oriented triangles, and the explicit
`a = e₃ - e₄` orbit computation on the bare standard fibre)
is the manuscript's finite group-action layer over these
identities.
-/

namespace NCG

/-- `thm:tetrahedral-prototype-connection`. -/
theorem tetrahedral_prototype_connection {M : Type*}
    [Monoid M] {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜]
    {W : Type*} [AddCommGroup W] [Module ℂ W] :
    -- (i) the boxed triangle holonomy identity
    (∀ U R : M, R ^ 3 = 1 →
      (R * U * R ^ 2) * (R ^ 2 * U * R) * U = (R * U) ^ 3)
    -- (ii) the boxed second-order curvature coefficient
    ∧ (∀ A₁ A₂ A₃ : 𝒜, A₁ + A₂ + A₃ = 0 →
        (1 / 2 : ℂ) • (A₁ ^ 2 + A₂ ^ 2 + A₃ ^ 2)
          + (A₁ * A₂ + A₁ * A₃ + A₂ * A₃)
        = (1 / 2 : ℂ) • (A₁ * A₂ - A₂ * A₁))
    -- (iii) scalar-fibre impossibility
    ∧ (∀ v : W, (3 : ℂ) • v = 0 → v = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U R hR
    have h3 : R * R * R = 1 := by
      rw [show R * R * R = R ^ 3 from by
        rw [pow_succ, pow_succ, pow_one]]
      exact hR
    have h3' : ∀ x : M, R * (R * (R * x)) = x := by
      intro x
      rw [← mul_assoc, ← mul_assoc, h3, one_mul]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc, h3']
  · intro A₁ A₂ A₃ hS
    have h3 : A₃ = -(A₁ + A₂) :=
      eq_neg_of_add_eq_zero_right hS
    subst h3
    simp only [pow_two, mul_add, add_mul, mul_neg, neg_mul,
      neg_add, neg_neg, smul_add]
    module
  · intro v hv
    have hv3 : v = (3 : ℂ)⁻¹ • ((3 : ℂ) • v) := by
      rw [smul_smul]
      norm_num
    rw [hv3, hv, smul_zero]

end NCG
