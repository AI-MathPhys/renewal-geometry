/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Affine Fourier relation and the common source hierarchy
  (`thm:GT-affine-Fourier`, Gran-Tensor manuscript)

* `gt_affine_fourier`: for a character system
  `e : X → G → ℂ` on a finite additive group `G`
  (multiplicative in the group argument, with a Fourier
  inversion formula `g y = |G|⁻¹ ∑ χ, ĝ(χ) e χ y`), and
  affine maps `ψᵢ(x) = Lᵢx + bᵢ` on `G^d`:
  (i) the off-lattice averages vanish — for any character
      tuple outside the dual relation lattice
      `R_Ψ = {(χᵢ) : ∏ᵢ χᵢ(Lᵢx) = 1 ∀x}` the average of
      `∏ᵢ χᵢ(Lᵢx)` over `G^d` is zero (the shift trick:
      the product is itself a character of `G^d`, and a
      nontrivial character sums to zero);
  (ii) the boxed affine Fourier relation
      `𝔼_{x∈G^d} ∏ᵢ fᵢ(ψᵢ(x))
        = |G|^{-t} ∑_{(χᵢ)∈R_Ψ} ∏ᵢ f̂ᵢ(χᵢ) χᵢ(bᵢ)`
      (insert inversion into every factor, expand the
      product of sums over character tuples, and average:
      tuples on the relation lattice contribute one,
      tuples off it are killed by (i)).

Instantiating the character system `(e, f̂, inversion)`
with the concrete dual group of a finite abelian `G`
(existence of the character basis) is the manuscript's
arithmetic loading layer; the final degree-hierarchy
sentence (a nontrivial character is noninvariant at
degree one while `H_χ ⊗ H_χ̄` is neutral at degree two)
is `thm:GT-positive-unitary-tensor-dichotomy`
(`NCG.gt_positive_unitary_dichotomy`).
-/

open Finset

attribute [local instance] Classical.propDecidable

namespace NCG

/-- `thm:GT-affine-Fourier` (off-lattice vanishing and
the boxed relation-lattice Fourier expansion). -/
theorem gt_affine_fourier {G X : Type}
    [AddCommGroup G] [Fintype G] [Fintype X]
    {t d : ℕ}
    (e : X → G → ℂ) (fhat : (G → ℂ) → X → ℂ)
    (L : Fin t → ((Fin d → G) →+ G)) (b : Fin t → G)
    (f : Fin t → G → ℂ)
    (hmul : ∀ χ a a', e χ (a + a') = e χ a * e χ a')
    (hinv : ∀ (g : G → ℂ) (y : G),
      g y = (Fintype.card G : ℂ)⁻¹
        * ∑ χ : X, fhat g χ * e χ y) :
    -- (i) off-lattice averages vanish
    (∀ χ : Fin t → X,
      (¬ ∀ x : Fin d → G, ∏ i, e (χ i) (L i x) = 1) →
      ∑ x : Fin d → G, ∏ i, e (χ i) (L i x) = 0)
    -- (ii) the boxed affine Fourier relation
    ∧ ((Fintype.card (Fin d → G) : ℂ))⁻¹
        * ∑ x : Fin d → G, ∏ i, f i (L i x + b i)
      = ((Fintype.card G : ℂ) ^ t)⁻¹ *
        ∑ χ ∈ Finset.univ.filter
          (fun χ : Fin t → X =>
            ∀ x : Fin d → G, ∏ i, e (χ i) (L i x) = 1),
          ∏ i, fhat (f i) (χ i) * e (χ i) (b i) := by
  -- the product character and its multiplicativity
  set Φ : (Fin t → X) → (Fin d → G) → ℂ :=
    fun χ x => ∏ i, e (χ i) (L i x) with hΦdef
  have hΦmul : ∀ χ x y, Φ χ (x + y) = Φ χ x * Φ χ y := by
    intro χ x y
    simp only [hΦdef, map_add, hmul]
    rw [Finset.prod_mul_distrib]
  -- (i) the shift trick
  have hvan : ∀ χ : Fin t → X,
      (¬ ∀ x : Fin d → G, Φ χ x = 1) →
      ∑ x : Fin d → G, Φ χ x = 0 := by
    intro χ hχ
    push Not at hχ
    obtain ⟨x₀, hx₀⟩ := hχ
    have hshift : Φ χ x₀ * ∑ x : Fin d → G, Φ χ x
        = ∑ x : Fin d → G, Φ χ x := by
      rw [Finset.mul_sum]
      calc ∑ x : Fin d → G, Φ χ x₀ * Φ χ x
          = ∑ x : Fin d → G, Φ χ (x₀ + x) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hΦmul]
        _ = ∑ x : Fin d → G, Φ χ x :=
            Fintype.sum_equiv (Equiv.addLeft x₀)
              (fun x => Φ χ (x₀ + x)) (fun x => Φ χ x)
              (fun x => rfl)
    have hfac : (Φ χ x₀ - 1)
        * ∑ x : Fin d → G, Φ χ x = 0 := by
      rw [sub_mul, one_mul, hshift, sub_self]
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hx₀
    · exact h0
  refine ⟨hvan, ?_⟩
  set c : ℂ := (Fintype.card G : ℂ) with hc
  set N : ℂ := (Fintype.card (Fin d → G) : ℂ) with hN
  have hNne : N ≠ 0 := by
    rw [hN]
    exact_mod_cast Fintype.card_ne_zero
  -- the per-tuple weight
  set W : (Fin t → X) → ℂ := fun χ =>
    ∏ i, fhat (f i) (χ i) * e (χ i) (b i) with hW
  -- expand every factor by Fourier inversion
  have hexp : ∀ x : Fin d → G,
      ∏ i, f i (L i x + b i)
        = (c⁻¹) ^ t * ∑ χ : Fin t → X,
            W χ * Φ χ x := by
    intro x
    calc ∏ i, f i (L i x + b i)
        = ∏ i, (c⁻¹ * ∑ χ : X,
            fhat (f i) χ * e χ (L i x + b i)) :=
          Finset.prod_congr rfl fun i _ =>
            hinv (f i) (L i x + b i)
      _ = (∏ _i : Fin t, c⁻¹) * ∏ i, ∑ χ : X,
            fhat (f i) χ * e χ (L i x + b i) :=
          Finset.prod_mul_distrib
      _ = (c⁻¹) ^ t * ∏ i, ∑ χ : X,
            fhat (f i) χ * e χ (L i x + b i) := by
          rw [Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
      _ = (c⁻¹) ^ t * ∑ χ : Fin t → X, ∏ i,
            fhat (f i) (χ i) * e (χ i) (L i x + b i) := by
          rw [Finset.prod_univ_sum]
          rw [Fintype.piFinset_univ]
      _ = (c⁻¹) ^ t * ∑ χ : Fin t → X,
            W χ * Φ χ x := by
          congr 1
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [hW, hΦdef]
          simp only
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [hmul]
          ring
  -- sum over x, swap, and split over the relation lattice
  have hsum : ∑ x : Fin d → G, ∏ i, f i (L i x + b i)
      = (c⁻¹) ^ t * ∑ χ : Fin t → X,
          W χ * ∑ x : Fin d → G, Φ χ x := by
    calc ∑ x : Fin d → G, ∏ i, f i (L i x + b i)
        = ∑ x : Fin d → G, (c⁻¹) ^ t
            * ∑ χ : Fin t → X, W χ * Φ χ x :=
          Finset.sum_congr rfl fun x _ => hexp x
      _ = (c⁻¹) ^ t * ∑ x : Fin d → G,
            ∑ χ : Fin t → X, W χ * Φ χ x := by
          rw [← Finset.mul_sum]
      _ = (c⁻¹) ^ t * ∑ χ : Fin t → X,
            ∑ x : Fin d → G, W χ * Φ χ x := by
          rw [Finset.sum_comm]
      _ = (c⁻¹) ^ t * ∑ χ : Fin t → X,
            W χ * ∑ x : Fin d → G, Φ χ x := by
          congr 1
          exact Finset.sum_congr rfl fun χ _ =>
            (Finset.mul_sum _ _ _).symm
  -- on the lattice the average is `N`; off it, zero
  have hsplit : ∑ χ : Fin t → X,
      W χ * ∑ x : Fin d → G, Φ χ x
      = N * ∑ χ ∈ Finset.univ.filter
          (fun χ : Fin t → X =>
            ∀ x : Fin d → G, Φ χ x = 1), W χ := by
    rw [← Finset.sum_filter_add_sum_filter_not
      Finset.univ
      (fun χ : Fin t → X =>
        ∀ x : Fin d → G, Φ χ x = 1)
      (fun χ => W χ * ∑ x : Fin d → G, Φ χ x)]
    have h1 : ∑ χ ∈ Finset.univ.filter
        (fun χ : Fin t → X =>
          ∀ x : Fin d → G, Φ χ x = 1),
        W χ * ∑ x : Fin d → G, Φ χ x
        = N * ∑ χ ∈ Finset.univ.filter
            (fun χ : Fin t → X =>
              ∀ x : Fin d → G, Φ χ x = 1), W χ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      have hmem := (Finset.mem_filter.mp hχ).2
      have : ∑ x : Fin d → G, Φ χ x = N := by
        calc ∑ x : Fin d → G, Φ χ x
            = ∑ _x : Fin d → G, (1 : ℂ) :=
              Finset.sum_congr rfl fun x _ => hmem x
          _ = N := by
              rw [Finset.sum_const, Finset.card_univ,
                hN, nsmul_eq_mul, mul_one]
      rw [this]
      ring
    have h2 : ∑ χ ∈ Finset.univ.filter
        (fun χ : Fin t → X =>
          ¬ ∀ x : Fin d → G, Φ χ x = 1),
        W χ * ∑ x : Fin d → G, Φ χ x = 0 := by
      refine Finset.sum_eq_zero fun χ hχ => ?_
      have hmem := (Finset.mem_filter.mp hχ).2
      rw [hvan χ hmem, mul_zero]
    rw [h1, h2, add_zero]
  rw [hsum, hsplit]
  rw [inv_pow]
  field_simp
  ring

end NCG
