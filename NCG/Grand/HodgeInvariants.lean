/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite invariants commute with cohomology
  (`thm:Hodge-invariants-cohomology`,
  Gran-Tensor manuscript)

* `hodge_invariants_cohomology`: for a finite group acting
  by chain maps `Uₖ` on a finite complex
  `C⁰ →d¹ C¹ →d² C²` with a `G`-invariant Hilbert
  structure (unitary action), the Reynolds projector
  `R = |G|⁻¹∑U(g)` satisfies:
  (i) `R` is idempotent (the invariant projection);
  (ii) `R` is a chain map (`R₁d¹ = d¹R₀`, `R₂d² = d²R₁`)
      and commutes with the adjoints, hence
  (iii) `R` commutes with the Hodge Laplacian
      `Δ = d¹(d¹)* + (d²)*d²`;
  (iv) `R` preserves harmonics: `d²X = 0 ∧ (d¹)*X = 0`
      implies the same for `R₁X` — the boxed
      `𝓗ᵏ((C•)^G) = 𝓗ᵏ(C•) ∩ (Cᵏ)^G`; and
  (v) an invariant coboundary has an invariant primitive
      (`R₁X = X ∧ X = d¹Y ⟹ X = d¹(R₀Y)` with `R₀Y`
      invariant) — the mechanism making the boxed
      `Hᵏ((C•)^G) ≅ Hᵏ(C•)^G` an isomorphism (injectivity
      via invariant primitives, surjectivity via averaging
      representatives).

The quotient-space packaging of (v) into the displayed
isomorphism, and the Green-operator clause, are the
manuscript's homological bookkeeping.
-/

open Matrix Finset

namespace NCG

/-- `thm:Hodge-invariants-cohomology` (Reynolds
averaging). -/
theorem hodge_invariants_cohomology {G : Type} [Fintype G]
    [Group G] {n0 n1 n2 : Type} [Fintype n0] [Fintype n1]
    [Fintype n2]
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
    -- (i) the Reynolds projector is idempotent
    (((Fintype.card G : ℂ)⁻¹ • ∑ g, U1 g)
      * ((Fintype.card G : ℂ)⁻¹ • ∑ g, U1 g)
      = (Fintype.card G : ℂ)⁻¹ • ∑ g, U1 g)
    -- (ii) the Reynolds projector is a chain map
    ∧ (((Fintype.card G : ℂ)⁻¹ • ∑ g, U1 g) * d1
      = d1 * ((Fintype.card G : ℂ)⁻¹ • ∑ g, U0 g))
    -- (iii) it commutes with the Hodge Laplacian
    ∧ (((Fintype.card G : ℂ)⁻¹ • ∑ g, U1 g)
        * (d1 * d1ᴴ + d2ᴴ * d2)
      = (d1 * d1ᴴ + d2ᴴ * d2)
        * ((Fintype.card G : ℂ)⁻¹ • ∑ g, U1 g))
    -- (iv) it preserves harmonics
    ∧ (∀ {m : Type} [Fintype m] (X : Matrix n1 m ℂ),
        d2 * X = 0 → d1ᴴ * X = 0 →
        d2 * (((Fintype.card G : ℂ)⁻¹
          • ∑ g, U1 g) * X) = 0
        ∧ d1ᴴ * (((Fintype.card G : ℂ)⁻¹
          • ∑ g, U1 g) * X) = 0)
    -- (v) an invariant coboundary has an invariant
    -- primitive
    ∧ (∀ {m : Type} [Fintype m] (X : Matrix n1 m ℂ)
        (Y : Matrix n0 m ℂ),
        ((Fintype.card G : ℂ)⁻¹ • ∑ g, U1 g) * X = X →
        X = d1 * Y →
        X = d1 * (((Fintype.card G : ℂ)⁻¹
          • ∑ g, U0 g) * Y)
        ∧ ((Fintype.card G : ℂ)⁻¹ • ∑ g, U0 g)
            * (((Fintype.card G : ℂ)⁻¹
              • ∑ g, U0 g) * Y)
          = ((Fintype.card G : ℂ)⁻¹
              • ∑ g, U0 g) * Y) := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  set c : ℂ := (Fintype.card G : ℂ)⁻¹ with hc
  set R0 := c • ∑ g, U0 g with hR0
  set R1 := c • ∑ g, U1 g with hR1
  -- absorption U1 g * R1 = R1
  have habs1 : ∀ g, U1 g * R1 = R1 := by
    intro g
    rw [hR1, Matrix.mul_smul, Matrix.mul_sum]
    congr 1
    calc ∑ h, U1 g * U1 h
        = ∑ h, U1 (g * h) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [hU1]
      _ = ∑ h, U1 h :=
          Fintype.sum_equiv (Equiv.mulLeft g) _ _
            fun h => rfl
  -- idempotence of the Reynolds projector
  have hidem1 : R1 * R1 = R1 := by
    calc R1 * R1
        = c • ∑ g, U1 g * R1 := by
          rw [hR1, Matrix.smul_mul, Matrix.sum_mul]
      _ = c • ∑ _g : G, R1 := by
          exact congrArg _ (Finset.sum_congr rfl
            fun g _ => habs1 g)
      _ = R1 := by
          rw [Finset.sum_const, Finset.card_univ,
            ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc,
            inv_mul_cancel₀ hcard, one_smul]
  have habs0 : ∀ g, U0 g * R0 = R0 := by
    intro g
    rw [hR0, Matrix.mul_smul, Matrix.mul_sum]
    congr 1
    calc ∑ h, U0 g * U0 h
        = ∑ h, U0 (g * h) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [hU0]
      _ = ∑ h, U0 h :=
          Fintype.sum_equiv (Equiv.mulLeft g) _ _
            fun h => rfl
  have hidem0 : R0 * R0 = R0 := by
    calc R0 * R0
        = c • ∑ g, U0 g * R0 := by
          rw [hR0, Matrix.smul_mul, Matrix.sum_mul]
      _ = c • ∑ _g : G, R0 := by
          exact congrArg _ (Finset.sum_congr rfl
            fun g _ => habs0 g)
      _ = R0 := by
          rw [Finset.sum_const, Finset.card_univ,
            ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc,
            inv_mul_cancel₀ hcard, one_smul]
  -- chain-map property
  have hchain1 : R1 * d1 = d1 * R0 := by
    rw [hR1, hR0, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sum_mul, Matrix.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun g _ => hint1 g
  have hchain2 : (c • ∑ g, U2 g) * d2 = d2 * R1 := by
    rw [hR1, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sum_mul, Matrix.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun g _ => hint2 g
  -- adjoint intertwining
  have hint1H : ∀ g, d1ᴴ * U1 g = U0 g * d1ᴴ := by
    intro g
    have h := congrArg conjTranspose (hint1 g⁻¹)
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hU1H, hU0H,
      inv_inv] at h
    exact h
  have hadj1 : d1ᴴ * R1 = R0 * d1ᴴ := by
    rw [hR1, hR0, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sum, Matrix.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun g _ => hint1H g
  have hint2H : ∀ g, d2ᴴ * U2 g = U1 g * d2ᴴ := by
    intro g
    have h := congrArg conjTranspose (hint2 g⁻¹)
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hU1H, hU2H,
      inv_inv] at h
    exact h
  have hadj2 : d2ᴴ * (c • ∑ g, U2 g) = R1 * d2ᴴ := by
    rw [hR1, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sum, Matrix.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun g _ => hint2H g
  -- Laplacian commutation
  have hlap : R1 * (d1 * d1ᴴ + d2ᴴ * d2)
      = (d1 * d1ᴴ + d2ᴴ * d2) * R1 := by
    rw [Matrix.mul_add, Matrix.add_mul]
    congr 1
    · calc R1 * (d1 * d1ᴴ)
          = (R1 * d1) * d1ᴴ := by
            rw [Matrix.mul_assoc]
        _ = d1 * (R0 * d1ᴴ) := by
            rw [hchain1, Matrix.mul_assoc]
        _ = d1 * (d1ᴴ * R1) := by rw [← hadj1]
        _ = (d1 * d1ᴴ) * R1 := by
            rw [Matrix.mul_assoc]
    · calc R1 * (d2ᴴ * d2)
          = (R1 * d2ᴴ) * d2 := by
            rw [Matrix.mul_assoc]
        _ = d2ᴴ * ((c • ∑ g, U2 g) * d2) := by
            rw [← hadj2, Matrix.mul_assoc]
        _ = d2ᴴ * (d2 * R1) := by rw [hchain2]
        _ = (d2ᴴ * d2) * R1 := by
            rw [Matrix.mul_assoc]
  refine ⟨hidem1, hchain1, hlap, ?_, ?_⟩
  · intro m _ X h2 h1
    constructor
    · calc d2 * (R1 * X)
          = ((c • ∑ g, U2 g) * d2) * X := by
            rw [hchain2, Matrix.mul_assoc]
        _ = (c • ∑ g, U2 g) * (d2 * X) := by
            rw [Matrix.mul_assoc]
        _ = 0 := by rw [h2, Matrix.mul_zero]
    · calc d1ᴴ * (R1 * X)
          = (R0 * d1ᴴ) * X := by
            rw [← Matrix.mul_assoc, hadj1]
        _ = R0 * (d1ᴴ * X) := by
            rw [Matrix.mul_assoc]
        _ = 0 := by rw [h1, Matrix.mul_zero]
  · intro m _ X Y hinv hcob
    constructor
    · calc X = R1 * X := hinv.symm
        _ = R1 * (d1 * Y) := by rw [← hcob]
        _ = (d1 * R0) * Y := by
            rw [← Matrix.mul_assoc, hchain1]
        _ = d1 * (R0 * Y) := by
            rw [Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, hidem0]

end NCG
