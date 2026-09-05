/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Primitive-frame chronology polynomials
  (`cor:clock-geometry-chronology-polynomial-master`, flagship
   manuscript)

The finite-group averaging behind the corollary:

* `average_conjugation_invariant`: the averaged coefficient
  `R̄ = |G|⁻¹ Σ_g ρ(g)Rρ(g)⁻¹` commutes with the frame
  representation — conjugating by any `ρ(h)` permutes the
  summands (reindexing by left multiplication);
* `average_preserves_identity`: averaging preserves the source
  identity — if every conjugated coefficient solves the linear
  source equation `L(ρ(g)Rρ(g)⁻¹) = S`, so does the average
  (linearity of `L`).

Rendering disclosed: Schur's lemma for the multiplicity-free
frame representation `1 ⊕ π₅` (identifying the commutant with
`{r₀P₀ + r₅P₅}`) and the resulting chronology polynomials
`q_α(z) = Σ r_{n,α}zⁿ` are the manuscript's representation-theory
bookkeeping on top of the averaging proved here; the exactness
statement (constant polynomial one = same-history identity,
nonconstant = measurable delay filter) is interpretive.
-/

open Matrix

namespace NCG

variable {G : Type*} [Group G] [Fintype G]
  {q : Type*} [Fintype q] [DecidableEq q]

/-- The group average of the conjugates commutes with the
representation: conjugation permutes the summands. -/
theorem average_conjugation_invariant
    (ρ : G → Matrix q q ℂ) (R : Matrix q q ℂ)
    (hmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (_hinv : ∀ g, ρ g * ρ g⁻¹ = 1)
    (h : G) :
    ρ h * ((Fintype.card G : ℂ)⁻¹
        • ∑ g, ρ g * R * ρ g⁻¹) * ρ h⁻¹
      = (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g * R * ρ g⁻¹ := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft]
  have h1 : ρ (h * g) = ρ h * ρ g := hmul h g
  have h2 : ρ ((h * g)⁻¹) = ρ (g⁻¹ * h⁻¹) := by
    rw [_root_.mul_inv_rev]
  have h3 : ρ (g⁻¹ * h⁻¹) = ρ g⁻¹ * ρ h⁻¹ := hmul g⁻¹ h⁻¹
  rw [h1, h2, h3]
  simp only [Matrix.mul_assoc]

omit [DecidableEq q] in
/-- Averaging preserves the linear source identity. -/
theorem average_preserves_identity
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : G → Matrix q q ℂ) (R : Matrix q q ℂ)
    (L : Matrix q q ℂ →ₗ[ℂ] W) (S : W)
    (hsol : ∀ g, L (ρ g * R * ρ g⁻¹) = S) :
    L ((Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g * R * ρ g⁻¹)
      = (Fintype.card G : ℂ)⁻¹ • (Fintype.card G : ℂ) • S := by
  rw [map_smul, map_sum]
  congr 1
  calc ∑ g, L (ρ g * R * ρ g⁻¹) = ∑ _g : G, S :=
      Finset.sum_congr rfl fun g _ => hsol g
    _ = (Fintype.card G : ℂ) • S := by
        rw [Finset.sum_const, Finset.card_univ,
          Nat.cast_smul_eq_nsmul]

end NCG
