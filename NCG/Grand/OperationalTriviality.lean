/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Determining variances and exact operational triviality
  (`thm:operational-triviality`, Gran-Tensor manuscript)

* `operational_triviality`:
  (i) the boxed GNS variance identity
      `ν_ω(a) = ‖(π(a) - ω(a))Ω‖²`: for a unit cyclic
      vector, the variance of any observable direction is
      the squared deviation of its action from the scalar
      `ω(a) = re⟪Ω, aΩ⟫`;
  (ii) zero variance holds exactly when the cyclic vector
      is an eigenvector;
  (iii) a full matrix algebra of size at least two admits
      no character (the character-free selected component);
  (iv) a continuous everywhere-positive panel margin on a
      nonempty compact state space has a uniform positive
      minimum.

The passage from scalar action on the cyclic vector to
one-dimensionality of the GNS space (noncommutative
polynomials + norm density + cyclicity) is the
manuscript's C*-density layer over these identities.
-/

open scoped InnerProductSpace

namespace NCG

/-- `thm:operational-triviality`. -/
theorem operational_triviality {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : Type*} [Fintype n] [DecidableEq n] :
    -- (i) the boxed variance identity
    (∀ v x : H, ‖v‖ = 1 →
      ‖x - (RCLike.re ⟪v, x⟫_ℂ : ℂ) • v‖ ^ 2
        = ‖x‖ ^ 2 - (RCLike.re ⟪v, x⟫_ℂ) ^ 2)
    -- (ii) zero variance exactly at eigenvectors
    ∧ (∀ v x : H,
        (‖x - (RCLike.re ⟪v, x⟫_ℂ : ℂ) • v‖ = 0
          ↔ x = (RCLike.re ⟪v, x⟫_ℂ : ℂ) • v))
    -- (iii) matrix algebras of size ≥ 2 have no character
    ∧ (∀ (_φ : Matrix n n ℂ →ₐ[ℂ] ℂ),
        2 ≤ Fintype.card n → False)
    -- (iv) uniform positive margin on a compact panel
    ∧ (∀ {X : Type} [TopologicalSpace X] (K : Set X)
        (f : X → ℝ), IsCompact K → K.Nonempty →
        ContinuousOn f K → (∀ x ∈ K, 0 < f x) →
        ∃ δ > 0, ∀ x ∈ K, δ ≤ f x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v x hv
    set c : ℝ := RCLike.re ⟪v, x⟫_ℂ with hc
    rw [norm_sub_sq (𝕜 := ℂ)]
    rw [norm_smul, hv, mul_one]
    have h1 : RCLike.re ⟪x, (c : ℂ) • v⟫_ℂ = c * c := by
      rw [inner_smul_right]
      have h2 : RCLike.re ((c : ℂ) * ⟪x, v⟫_ℂ)
          = c * RCLike.re ⟪x, v⟫_ℂ := by
        rw [← Complex.real_smul, RCLike.smul_re]
      rw [h2]
      congr 1
      rw [← inner_conj_symm, RCLike.conj_re]
    rw [h1]
    have h3 : ‖(c : ℂ)‖ = |c| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h3]
    have h4 : |c| ^ 2 = c ^ 2 := sq_abs c
    nlinarith [h4]
  · intro v x
    constructor
    · intro h
      have := norm_eq_zero.mp h
      exact sub_eq_zero.mp this
    · intro h
      rw [← sub_eq_zero] at h
      rw [h, norm_zero]
  · intro φ hcard
    have hnne : Nonempty n :=
      Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i⟩ := hnne
    -- diagonal units all take the same scalar value
    have hsame : ∀ a b : n,
        φ (Matrix.single a a 1)
          = φ (Matrix.single b b 1) := by
      intro a b
      have h1 : Matrix.single a b (1 : ℂ)
          * Matrix.single b a 1 = Matrix.single a a 1 := by
        rw [Matrix.single_mul_single_same, one_mul]
      have h2 : Matrix.single b a (1 : ℂ)
          * Matrix.single a b 1 = Matrix.single b b 1 := by
        rw [Matrix.single_mul_single_same, one_mul]
      calc φ (Matrix.single a a 1)
          = φ (Matrix.single a b 1)
            * φ (Matrix.single b a 1) := by
            rw [← map_mul, h1]
        _ = φ (Matrix.single b a 1)
            * φ (Matrix.single a b 1) := by ring
        _ = φ (Matrix.single b b 1) := by
            rw [← map_mul, h2]
    -- the common diagonal value is idempotent
    have hidem : φ (Matrix.single i i (1 : ℂ))
        * φ (Matrix.single i i 1)
        = φ (Matrix.single i i 1) := by
      rw [← map_mul, Matrix.single_mul_single_same,
        one_mul]
    have hone : (1 : Matrix n n ℂ)
        = ∑ k, Matrix.single k k (1 : ℂ) := by
      ext a b
      simp [Matrix.single, Matrix.one_apply,
        Matrix.sum_apply, ite_and]
    have hsum : (Fintype.card n : ℂ)
        * φ (Matrix.single i i 1) = 1 := by
      have h1 := map_one φ
      rw [hone, map_sum,
        Finset.sum_congr rfl (fun k _ => hsame k i),
        Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul] at h1
      exact h1
    have hc_ne : φ (Matrix.single i i (1 : ℂ)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hsum
      exact one_ne_zero hsum.symm
    have hc1 : φ (Matrix.single i i (1 : ℂ)) = 1 :=
      mul_left_cancel₀ hc_ne
        (hidem.trans (mul_one _).symm)
    rw [hc1, mul_one] at hsum
    have hcard1 : Fintype.card n = 1 := by
      exact_mod_cast hsum
    omega
  · intro X _ K f hK hne hf hpos
    obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne hf
    refine ⟨f x0, hpos x0 hx0, fun x hx => hmin hx⟩

end NCG
