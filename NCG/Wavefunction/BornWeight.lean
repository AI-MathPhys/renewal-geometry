/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The renewal Born disintegration and operational closure
  (`thm:renewal-born-disintegration`,
   `prop:operational-born-closure`, wavefunction)

* `cauchy_add_mul_id` — the regularity-free Cauchy core: a weight
  profile `G` on `ℝ≥0` that is additive, multiplicative, and
  normalized is the identity.  No measurability assumption is
  needed: multiplicativity supplies positivity (`G(x) = G(√x)² ≥ 0`),
  hence monotonicity, and the floor squeeze
  `⌊nx⌋ ≤ n G(x) ≤ ⌊nx⌋ + 1` pins `G` to the identity;
* `weight_additive_of_orthogonal` — orthogonal additivity of a
  norm-dependent weight yields Cauchy additivity of its profile
  (Pythagoras on two orthonormal directions);
* `renewal_born_weight` (`thm:renewal-born-disintegration`): a
  regular predictive weight — norm-dependent (phase/deck
  invariance), additive on orthogonal amplitudes (refinement
  stability), multiplicative under independent renewal composition,
  and normalized on unit amplitudes — is the quadratic norm
  `W(ψ) = ‖ψ‖²`; the record probabilities
  `p_i = ‖Πᵢψ‖²/Σⱼ‖Πⱼψ‖²` follow (`born_probabilities`);
* `second_moment_closure` (`prop:operational-born-closure`): if the
  implemented reset ensemble is second-moment complete — the
  rank-one projectors of its states span the full matrix space (the
  projective two-design hypothesis) — then any sesquilinear
  second-moment functional agreeing with the quadratic weight on the
  ensemble agrees with it on every implementable basis vector:
  `B = 1`.
-/

namespace NCG

open Real

/-- The regularity-free Cauchy core: additive + multiplicative +
normalized on `ℝ≥0` forces the identity. -/
theorem cauchy_add_mul_id {G : ℝ → ℝ}
    (hadd : ∀ x y, 0 ≤ x → 0 ≤ y → G (x + y) = G x + G y)
    (hmul : ∀ x y, 0 ≤ x → 0 ≤ y → G (x * y) = G x * G y)
    (hnorm : G 1 = 1) :
    ∀ x, 0 ≤ x → G x = x := by
  have hG0 : G 0 = 0 := by
    have h := hadd 0 0 le_rfl le_rfl
    simp at h
    linarith
  have hnn : ∀ x, 0 ≤ x → 0 ≤ G x := by
    intro x hx
    have h := hmul (Real.sqrt x) (Real.sqrt x) (Real.sqrt_nonneg x)
      (Real.sqrt_nonneg x)
    rw [Real.mul_self_sqrt hx] at h
    rw [h]
    exact mul_self_nonneg _
  have hmono : ∀ a b, 0 ≤ a → a ≤ b → G a ≤ G b := by
    intro a b ha hab
    have h := hadd a (b - a) ha (by linarith)
    rw [add_sub_cancel] at h
    have := hnn (b - a) (by linarith)
    linarith
  have hnat : ∀ n : ℕ, G n = n := by
    intro n
    induction n with
    | zero => simpa using hG0
    | succ m ih =>
        have h := hadd m 1 (Nat.cast_nonneg m) (by norm_num)
        push_cast
        rw [h, ih, hnorm]
  have hkey : ∀ x, 0 ≤ x → ∀ n : ℕ, 0 < n →
      |G x - x| ≤ 2 / n := by
    intro x hx n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hnx : (0 : ℝ) ≤ n * x := by positivity
    have hfl : ((⌊(n : ℝ) * x⌋₊ : ℝ)) ≤ n * x := Nat.floor_le hnx
    have hfl2 : (n : ℝ) * x < ⌊(n : ℝ) * x⌋₊ + 1 :=
      Nat.lt_floor_add_one _
    have hGnx : G (n * x) = n * G x := by
      have h := hmul n x (Nat.cast_nonneg n) hx
      rw [h, hnat n]
    have hlow : ((⌊(n : ℝ) * x⌋₊ : ℝ)) ≤ n * G x := by
      have h := hmono _ _ (Nat.cast_nonneg _) hfl
      rw [hGnx] at h
      rwa [hnat] at h
    have hhigh : (n : ℝ) * G x ≤ ⌊(n : ℝ) * x⌋₊ + 1 := by
      have h := hmono _ _ hnx (le_of_lt hfl2)
      rw [hGnx] at h
      have h2 : G ((⌊(n : ℝ) * x⌋₊ : ℝ) + 1)
          = (⌊(n : ℝ) * x⌋₊ : ℝ) + 1 := by
        have := hnat (⌊(n : ℝ) * x⌋₊ + 1)
        push_cast at this
        exact_mod_cast this
      rwa [h2] at h
    have hd1 : (n : ℝ) * (G x - x) ≤ 2 := by nlinarith
    have hd2 : (n : ℝ) * (x - G x) ≤ 2 := by nlinarith
    have h2n : 2 / (n : ℝ) * n = 2 := div_mul_cancel₀ _ hnR.ne'
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  intro x hx
  by_contra hne
  have habs : 0 < |G x - x| := by
    rw [abs_pos, sub_ne_zero]
    exact hne
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / |G x - x|)
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      have hpos : 0 < 2 / |G x - x| := by positivity
      simp only [Nat.cast_zero] at hn
      linarith
    · exact h
  have h := hkey x hx n hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have : 2 / |G x - x| < n := hn
  have h2 : 2 / (n : ℝ) < |G x - x| := by
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ habs] at this
    nlinarith
  linarith

set_option linter.flexible false in
/-- Orthogonal additivity of a norm-dependent weight yields Cauchy
additivity of its profile. -/
theorem weight_additive_of_orthogonal {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : H → ℝ} {G : ℝ → ℝ}
    (hW : ∀ ψ, W ψ = G (‖ψ‖ ^ 2))
    (horth : ∀ ψ φ : H, inner ℂ ψ φ = 0 → W (ψ + φ) = W ψ + W φ)
    {e₁ e₂ : H} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (he12 : inner ℂ e₁ e₂ = 0) :
    ∀ x y, 0 ≤ x → 0 ≤ y → G (x + y) = G x + G y := by
  intro x y hx hy
  have h1 : ‖(Real.sqrt x : ℂ) • e₁‖ ^ 2 = x := by
    rw [norm_smul]
    simp [he₁, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg x)]
    exact Real.sq_sqrt hx
  have h2 : ‖(Real.sqrt y : ℂ) • e₂‖ ^ 2 = y := by
    rw [norm_smul]
    simp [he₂, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg y)]
    exact Real.sq_sqrt hy
  have horth' : inner ℂ ((Real.sqrt x : ℂ) • e₁)
      ((Real.sqrt y : ℂ) • e₂) = 0 := by
    rw [inner_smul_left, inner_smul_right, he12]
    ring
  have hpyth : ‖(Real.sqrt x : ℂ) • e₁ + (Real.sqrt y : ℂ) • e₂‖ ^ 2
      = x + y := by
    rw [@norm_add_sq ℂ, horth']
    simp only [map_zero, mul_zero, add_zero]
    rw [h1, h2]
  calc G (x + y) = W ((Real.sqrt x : ℂ) • e₁
        + (Real.sqrt y : ℂ) • e₂) := by rw [hW, hpyth]
  _ = W ((Real.sqrt x : ℂ) • e₁) + W ((Real.sqrt y : ℂ) • e₂) :=
      horth _ _ horth'
  _ = G x + G y := by rw [hW, hW, h1, h2]

/-- `thm:renewal-born-disintegration` (quadratic weight): a regular
predictive weight — norm-dependent, additive on orthogonal
amplitudes, multiplicative under independent renewal composition,
normalized on unit amplitudes — is the quadratic norm. -/
theorem renewal_born_weight {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : H → ℝ} {G : ℝ → ℝ}
    (hW : ∀ ψ, W ψ = G (‖ψ‖ ^ 2))
    (horth : ∀ ψ φ : H, inner ℂ ψ φ = 0 → W (ψ + φ) = W ψ + W φ)
    (hmul : ∀ x y, 0 ≤ x → 0 ≤ y → G (x * y) = G x * G y)
    (hnorm : G 1 = 1)
    {e₁ e₂ : H} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (he12 : inner ℂ e₁ e₂ = 0) :
    ∀ ψ, W ψ = ‖ψ‖ ^ 2 := by
  intro ψ
  have hadd := weight_additive_of_orthogonal hW horth he₁ he₂ he12
  have hid := cauchy_add_mul_id hadd hmul hnorm
  rw [hW]
  exact hid _ (by positivity)

/-- `thm:renewal-born-disintegration` (record probabilities): the
normalized sector weights are the Born ratios. -/
theorem born_probabilities {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : H → ℝ} (hquad : ∀ ψ, W ψ = ‖ψ‖ ^ 2)
    {ι : Type*} [Fintype ι] (amps : ι → H) (i : ι) :
    W (amps i) / ∑ j, W (amps j)
      = ‖amps i‖ ^ 2 / ∑ j, ‖amps j‖ ^ 2 := by
  simp only [hquad]

/-- `prop:operational-born-closure` (second-moment closure): if the
rank-one projectors of the implemented reset ensemble span the full
matrix space (projective two-design completeness), then any
second-moment functional `B` agreeing with the quadratic weight on
the ensemble is the identity — the Born weights extend to every
implementable basis. -/
theorem second_moment_closure {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℂ} {S : Set (Fin n → ℂ)}
    (hspan : Submodule.span ℂ
      ((fun ψ : Fin n → ℂ => Matrix.vecMulVec ψ (star ψ)) '' S) = ⊤)
    (hagree : ∀ ψ ∈ S,
      Matrix.trace (B * Matrix.vecMulVec ψ (star ψ))
        = Matrix.trace (Matrix.vecMulVec ψ (star ψ))) :
    B = 1 := by
  have hvanish : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      Matrix.trace ((B - 1) * M) = 0 := by
    intro M
    have hM : M ∈ Submodule.span ℂ
        ((fun ψ : Fin n → ℂ => Matrix.vecMulVec ψ (star ψ)) '' S) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨ψ, hψ, rfl⟩ := hx
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
          hagree ψ hψ, sub_self]
    | zero => simp
    | add x y _ _ hx hy =>
        rw [Matrix.mul_add, Matrix.trace_add, hx, hy, add_zero]
    | smul c x _ hx =>
        rw [Matrix.mul_smul, Matrix.trace_smul, hx, smul_zero]
  ext i j
  have h := hvanish (Matrix.single j i 1)
  rw [Matrix.sub_mul, Matrix.trace_sub] at h
  have htr : ∀ A : Matrix (Fin n) (Fin n) ℂ,
      Matrix.trace (A * Matrix.single j i 1) = A i j := by
    intro A
    unfold Matrix.trace
    rw [Finset.sum_eq_single i]
    · simp [Matrix.diag, Matrix.mul_apply, Matrix.single_apply,
        Finset.sum_ite_eq]
    · intro b _ hb
      simp [Matrix.diag, Matrix.mul_apply, Ne.symm hb]
    · simp
  rw [htr B, htr 1] at h
  exact sub_eq_zero.mp h

end NCG
