/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HodgeInvariants

/-!
# Finite invariant cohomology quotient

The two representative-level statements below are the surjectivity and
injectivity of the canonical map
`H^k((C^bullet)^G) -> H^k(C^bullet)^G`.  They avoid choosing a presentation of
quotient modules while retaining exactly the equality relation on cohomology
classes: two cycles represent the same class when their difference is a
coboundary.
-/

open Matrix Finset

namespace NCG
namespace HodgeInvariantCohomologyQuotientExact

/-- Representative-level formulation of the canonical cohomology
isomorphism.  The first clause says every Reynolds-invariant cohomology class
has an invariant cycle representative.  The second says an invariant cycle
which is a coboundary already has an invariant primitive. -/
def CohomologyInvariantsCommute
    {G n0 n1 n2 : Type} [Fintype G] [Group G]
    [Fintype n0] [Fintype n1] [Fintype n2]
    (d1 : Matrix n1 n0 ℂ) (d2 : Matrix n2 n1 ℂ)
    (U0 : G → Matrix n0 n0 ℂ) (U1 : G → Matrix n1 n1 ℂ) : Prop :=
  let R0 := (Fintype.card G : ℂ)⁻¹ • ∑ g, U0 g
  let R1 := (Fintype.card G : ℂ)⁻¹ • ∑ g, U1 g
  (∀ {m : Type} [Fintype m] (X : Matrix n1 m ℂ),
      d2 * X = 0 →
      (∃ Y : Matrix n0 m ℂ, R1 * X - X = d1 * Y) →
      ∃ Xinv : Matrix n1 m ℂ, ∃ Y : Matrix n0 m ℂ,
        d2 * Xinv = 0 ∧ R1 * Xinv = Xinv ∧
          Xinv - X = d1 * Y) ∧
  (∀ {m : Type} [Fintype m] (X : Matrix n1 m ℂ)
      (Y : Matrix n0 m ℂ),
      d2 * X = 0 → R1 * X = X → X = d1 * Y →
      ∃ Yinv : Matrix n0 m ℂ, R0 * Yinv = Yinv ∧
        X = d1 * Yinv)

/-- Finite Reynolds averaging proves both directions of
`H^k((C^bullet)^G) ≅ H^k(C^bullet)^G`. -/
theorem finite_invariants_commute_with_cohomology
    {G : Type} [Fintype G] [Group G]
    {n0 n1 n2 : Type} [Fintype n0] [Fintype n1] [Fintype n2]
    (d1 : Matrix n1 n0 ℂ) (d2 : Matrix n2 n1 ℂ)
    (U0 : G → Matrix n0 n0 ℂ) (U1 : G → Matrix n1 n1 ℂ)
    (U2 : G → Matrix n2 n2 ℂ)
    (hU0 : ∀ g h, U0 (g * h) = U0 g * U0 h)
    (hU1 : ∀ g h, U1 (g * h) = U1 g * U1 h)
    (hU0H : ∀ g, (U0 g)ᴴ = U0 g⁻¹)
    (hU1H : ∀ g, (U1 g)ᴴ = U1 g⁻¹)
    (hU2H : ∀ g, (U2 g)ᴴ = U2 g⁻¹)
    (hint1 : ∀ g, U1 g * d1 = d1 * U0 g)
    (hint2 : ∀ g, U2 g * d2 = d2 * U1 g) :
    CohomologyInvariantsCommute d1 d2 U0 U1 := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  let c : ℂ := (Fintype.card G : ℂ)⁻¹
  let R0 : Matrix n0 n0 ℂ := c • ∑ g, U0 g
  let R1 : Matrix n1 n1 ℂ := c • ∑ g, U1 g
  let R2 : Matrix n2 n2 ℂ := c • ∑ g, U2 g
  obtain ⟨hidem1, _hchain1, _hlap, _hharm, hprimitive⟩ :=
    hodge_invariants_cohomology d1 d2 U0 U1 U2
      hU0 hU1 hU0H hU1H hU2H hint1 hint2
  have hchain2 : R2 * d2 = d2 * R1 := by
    dsimp [R2, R1, c]
    rw [Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sum_mul, Matrix.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun g _ => hint2 g
  change
    (∀ {m : Type} [Fintype m] (X : Matrix n1 m ℂ),
      d2 * X = 0 →
      (∃ Y : Matrix n0 m ℂ, R1 * X - X = d1 * Y) →
      ∃ Xinv : Matrix n1 m ℂ, ∃ Y : Matrix n0 m ℂ,
        d2 * Xinv = 0 ∧ R1 * Xinv = Xinv ∧
          Xinv - X = d1 * Y) ∧
    (∀ {m : Type} [Fintype m] (X : Matrix n1 m ℂ)
      (Y : Matrix n0 m ℂ),
      d2 * X = 0 → R1 * X = X → X = d1 * Y →
      ∃ Yinv : Matrix n0 m ℂ, R0 * Yinv = Yinv ∧
        X = d1 * Yinv)
  constructor
  · intro m _ X hcycle hclass
    obtain ⟨Y, hY⟩ := hclass
    refine ⟨R1 * X, Y, ?_, ?_, hY⟩
    · calc
        d2 * (R1 * X) = (R2 * d2) * X := by
          rw [hchain2, Matrix.mul_assoc]
        _ = R2 * (d2 * X) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hcycle, Matrix.mul_zero]
    · rw [← Matrix.mul_assoc]
      exact congrArg (fun A => A * X) hidem1
  · intro m _ X Y _hcycle hinv hcob
    have hp := hprimitive X Y hinv hcob
    exact ⟨R0 * Y, hp.2, hp.1⟩

end HodgeInvariantCohomologyQuotientExact
end NCG
