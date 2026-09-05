/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTQuadraticChannelRemainderExact
import NCG.Grand.SharpTrotterCommutator

/-!
# Noisy Klein refocusing (exact)

Exact formalization of `thm:SMST-noisy-Klein-refocusing`: the
`n`-pass Klein-conjugated physical mixer
`𝔗 = [∏_ε Ad_{Z_ε}∘Φ(χ_e(ε)t/4n)∘Ad_{Z_ε}]^n` reconstructs the
ideal edge flow `Ad_{e^{-itH_e}}` through the encoder with error
`|t|·ε_tan + (3M² + κ)·t²/(4n)` — the manuscript's exact boxed
constant.

Derivation structure (every quantitative estimate is derived):

* **Klein character orthogonality** (`klein_edge01`, wave 14):
  the four sign words isolate the edge block
  `∑_ε χ_e(ε)·Z_εDZ_ε = 4·D_e` — a ring identity;
* **sharp four-factor Trotter** (`four_exp_sub_exp_add_le`):
  each ideal pass differs from `e^{(t/n)•D_e}` by at most
  `½·∑_{i<j}‖[Xᵢ,Xⱼ]‖ ≤ 6M²t²/16n² = 3M²t²/8n²` — this sharp
  commutator bound (no exponential prefactor) is what produces
  the manuscript's constant `3M²`;
* **contraction power telescoping** (`pow_sub_pow_bound`):
  `n` passes give `3M²t²/8n` at the unitary level;
* the **Ad-Lipschitz doubling** `‖Ad_U - Ad_V‖⋄ ≤ 2‖U-V‖`
  (framework hypothesis; its algebraic content is
  `NCG.ChannelEstimates.conj_sub_conj_bound`) gives `3M²t²/4n`
  at the channel level;
* **two-sided telescoping** (`intertwine_four_bound`,
  `intertwine_pow_bound`) accumulates the `4n` per-factor
  remainders `(|t|/4n)·ε_tan + κ·t²/16n²` — supplied by the
  quadratic-channel-remainder record — into
  `|t|·ε_tan + κt²/4n`;
* **involution conjugation** (`exp_conj_of_invol`) moves the
  sign words through the exponentials, with `Z_ε² = 1` derived
  from the sharp projection algebra.

Framework hypotheses (disclosed, all structural): the diamond
norms are the Banach-algebra norms of the channel algebra `B`
and matrix algebra `M`; `AdM` is the unital multiplicative
conjugation functor with `‖AdM‖ ≤ 1` on contractions and the
Lipschitz doubling bound; the encoded sign channels intertwine
with the source sign words through the encoder; real spans of
the conjugated generators exponentiate to contractions
(skew-adjointness); and the per-factor remainder is the proven
conclusion of `thm:SMST-quadratic-channel-remainder`.
-/

open Set NormedSpace

namespace NCG
namespace SMSTChannel

/-- The Klein sign characters `χ_{01}` on the four sign words. -/
def kleinSign : Fin 4 → ℝ := ![1, -1, -1, 1]

/-- The four Klein sign words `Z_ε = ε₀P₀ + ε₁P₁ + ε₂P₂` for
`ε ∈ 𝖪 = {(+,+,+), (+,-,-), (-,+,-), (-,-,+)}`. -/
def kleinWord {M : Type} [Ring M] (P₀ P₁ P₂ : M) : Fin 4 → M :=
  ![P₀ + P₁ + P₂, P₀ - P₁ - P₂, -P₀ + P₁ - P₂, -P₀ - P₁ + P₂]

/-- **Noisy Klein refocusing**
(`thm:SMST-noisy-Klein-refocusing`): the `n`-pass sign-conjugated
physical mixer approximates the ideal edge flow through the
encoder with the exact boxed error
`|t|·ε_tan + (3M² + κ)·t²/(4n)`.

`M` is the source matrix algebra (`D = -iH`, `‖D‖ ≤ MH`),
`B` the channel algebra; `Φ` the signed physical channel curve,
`a ε` the encoded sign channels, `ι` the encoder, and
`AdM` the unitary-conjugation functor. -/
theorem noisy_klein_refocusing
    {M B : Type} [NormedRing M] [NormOneClass M]
    [NormedAlgebra ℝ M] [NormedAlgebra ℚ M] [CompleteSpace M]
    [NormedRing B] [NormOneClass B]
    (P₀ P₁ P₂ D : M) (MH : ℝ)
    (Φ : ℝ → B) (a : Fin 4 → B) (ι : B) (AdM : M → B)
    (εtan κ t : ℝ) (n : ℕ) (hn : 0 < n)
    -- source projection algebra and generator bound
    (hD : ‖D‖ ≤ MH)
    (h00 : P₀ * P₀ = P₀) (h11 : P₁ * P₁ = P₁)
    (h22 : P₂ * P₂ = P₂)
    (h01 : P₀ * P₁ = 0) (h10 : P₁ * P₀ = 0)
    (h02 : P₀ * P₂ = 0) (h20 : P₂ * P₀ = 0)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (hsum : P₀ + P₁ + P₂ = 1)
    (hW : ∀ ε : Fin 4, ‖kleinWord P₀ P₁ P₂ ε‖ ≤ 1)
    -- unitarity: skew spans exponentiate to contractions
    (hunit : ∀ (r : Fin 4 → ℝ) (u : ℝ),
      ‖exp (u • ∑ ε : Fin 4, r ε •
        (kleinWord P₀ P₁ P₂ ε * D * kleinWord P₀ P₁ P₂ ε))‖ ≤ 1)
    (hDexp : ∀ v : ℝ, ‖exp (v • D)‖ ≤ 1)
    -- channel-level structure
    (hι : ‖ι‖ ≤ 1) (ha : ∀ ε : Fin 4, ‖a ε‖ ≤ 1)
    (hΦ : ∀ s : ℝ, |s| ≤ |t| / (4 * n) → ‖Φ s‖ ≤ 1)
    (hAd1 : AdM 1 = 1)
    (hAdmul : ∀ x y : M, AdM (x * y) = AdM x * AdM y)
    (hAdnorm : ∀ x : M, ‖x‖ ≤ 1 → ‖AdM x‖ ≤ 1)
    (hAdLip : ∀ x y : M, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖AdM x - AdM y‖ ≤ 2 * ‖x - y‖)
    (hint : ∀ ε : Fin 4,
      a ε * ι = ι * AdM (kleinWord P₀ P₁ P₂ ε))
    -- the per-factor remainder: the proven conclusion of
    -- `thm:SMST-quadratic-channel-remainder`
    (hfac : ∀ s : ℝ, |s| ≤ |t| / (4 * n) →
      ‖Φ s * ι - ι * AdM (exp (s • D))‖
        ≤ |s| * εtan + κ * s ^ 2) :
    ‖((a 0 * Φ (t / (4 * n)) * a 0)
        * (a 1 * Φ (-(t / (4 * n))) * a 1)
        * (a 2 * Φ (-(t / (4 * n))) * a 2)
        * (a 3 * Φ (t / (4 * n)) * a 3)) ^ n * ι
      - ι * AdM (exp (t • (P₀ * D * P₁ + P₁ * D * P₀)))‖
    ≤ |t| * εtan + (3 * MH ^ 2 + κ) * t ^ 2 / (4 * n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have h4n : (0 : ℝ) < 4 * n := by positivity
  have hMH0 : (0 : ℝ) ≤ MH := (norm_nonneg D).trans hD
  set s₄ : ℝ := t / (4 * n) with hs₄def
  have habs4 : |s₄| = |t| / (4 * n) := by
    rw [hs₄def, abs_div, abs_of_pos h4n]
  have habsneg : |(-s₄)| = |t| / (4 * n) := by
    rw [abs_neg, habs4]
  -- ===== the conjugated generators =====
  set T₀ : M := (P₀ + P₁ + P₂) * D * (P₀ + P₁ + P₂) with hT₀
  set T₁ : M := (P₀ - P₁ - P₂) * D * (P₀ - P₁ - P₂) with hT₁
  set T₂ : M := (-P₀ + P₁ - P₂) * D * (-P₀ + P₁ - P₂) with hT₂
  set T₃ : M := (-P₀ - P₁ + P₂) * D * (-P₀ - P₁ + P₂) with hT₃
  set De : M := P₀ * D * P₁ + P₁ * D * P₀ with hDe
  -- word norms in explicit form
  have hW0 : ‖P₀ + P₁ + P₂‖ ≤ 1 := hW 0
  have hW1 : ‖P₀ - P₁ - P₂‖ ≤ 1 := hW 1
  have hW2' : ‖-P₀ + P₁ - P₂‖ ≤ 1 := hW 2
  have hW3 : ‖-P₀ - P₁ + P₂‖ ≤ 1 := hW 3
  -- generator norms
  have hconjn : ∀ w' : M, ‖w'‖ ≤ 1 → ‖w' * D * w'‖ ≤ MH := by
    intro w' hw'
    calc ‖w' * D * w'‖ ≤ ‖w' * D‖ * ‖w'‖ := norm_mul_le _ _
      _ ≤ ‖w'‖ * ‖D‖ * ‖w'‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ 1 * MH * 1 := by
          refine mul_le_mul (mul_le_mul hw' hD
            (norm_nonneg _) zero_le_one) hw'
            (norm_nonneg _) (by positivity)
      _ = MH := by ring
  have hT₀n : ‖T₀‖ ≤ MH := hconjn _ hW0
  have hT₁n : ‖T₁‖ ≤ MH := hconjn _ hW1
  have hT₂n : ‖T₂‖ ≤ MH := hconjn _ hW2'
  have hT₃n : ‖T₃‖ ≤ MH := hconjn _ hW3
  -- ===== contractivity of exponentiated spans =====
  have hcT : ∀ c₀ c₁ c₂ c₃ : ℝ,
      ‖exp (c₀ • T₀ + c₁ • T₁ + c₂ • T₂ + c₃ • T₃)‖ ≤ 1 := by
    intro c₀ c₁ c₂ c₃
    have h := hunit ![c₀, c₁, c₂, c₃] 1
    rw [Fin.sum_univ_four, one_smul] at h
    exact h
  -- ===== Klein isolation of the edge block =====
  have hK : T₀ - T₁ - T₂ + T₃ = 4 * De :=
    klein_edge01 P₀ P₁ P₂ D
  have hDe4 : (4 : ℝ) • De = T₀ - T₁ - T₂ + T₃ := by
    rw [hK]
    have : (4 : M) * De = (4 : ℕ) • De := (nsmul_eq_mul 4 De).symm
    rw [this, ← Nat.cast_smul_eq_nsmul ℝ]
    norm_num
  -- ===== involutivity of the sign words =====
  have hgensq : ∀ Q₀ Q₁ Q₂ : M,
      Q₀ * Q₀ = P₀ → Q₁ * Q₁ = P₁ → Q₂ * Q₂ = P₂ →
      Q₀ * Q₁ = 0 → Q₁ * Q₀ = 0 → Q₀ * Q₂ = 0 →
      Q₂ * Q₀ = 0 → Q₁ * Q₂ = 0 → Q₂ * Q₁ = 0 →
      (Q₀ + Q₁ + Q₂) * (Q₀ + Q₁ + Q₂) = 1 := by
    intro Q₀ Q₁ Q₂ g00 g11 g22 g01 g10 g02 g20 g12 g21
    have hexpand : (Q₀ + Q₁ + Q₂) * (Q₀ + Q₁ + Q₂)
        = Q₀ * Q₀ + Q₀ * Q₁ + Q₀ * Q₂ + Q₁ * Q₀ + Q₁ * Q₁
          + Q₁ * Q₂ + Q₂ * Q₀ + Q₂ * Q₁ + Q₂ * Q₂ := by
      noncomm_ring
    rw [hexpand, g00, g01, g02, g10, g11, g12, g20, g21, g22]
    simp only [add_zero]
    exact hsum
  have hsq0 : (P₀ + P₁ + P₂) * (P₀ + P₁ + P₂) = 1 :=
    hgensq P₀ P₁ P₂ h00 h11 h22 h01 h10 h02 h20 h12 h21
  have hsq1 : (P₀ - P₁ - P₂) * (P₀ - P₁ - P₂) = 1 := by
    have h := hgensq P₀ (-P₁) (-P₂)
      (by rw [h00]) (by rw [neg_mul_neg, h11])
      (by rw [neg_mul_neg, h22])
      (by rw [mul_neg, h01, neg_zero])
      (by rw [neg_mul, h10, neg_zero])
      (by rw [mul_neg, h02, neg_zero])
      (by rw [neg_mul, h20, neg_zero])
      (by rw [neg_mul_neg, h12])
      (by rw [neg_mul_neg, h21])
    have hrw : P₀ + -P₁ + -P₂ = P₀ - P₁ - P₂ := by abel
    rwa [hrw] at h
  have hsq2 : (-P₀ + P₁ - P₂) * (-P₀ + P₁ - P₂) = 1 := by
    have h := hgensq (-P₀) P₁ (-P₂)
      (by rw [neg_mul_neg, h00]) (by rw [h11])
      (by rw [neg_mul_neg, h22])
      (by rw [neg_mul, h01, neg_zero])
      (by rw [mul_neg, h10, neg_zero])
      (by rw [neg_mul_neg, h02])
      (by rw [neg_mul_neg, h20])
      (by rw [mul_neg, h12, neg_zero])
      (by rw [neg_mul, h21, neg_zero])
    have hrw : -P₀ + P₁ + -P₂ = -P₀ + P₁ - P₂ := by abel
    rwa [hrw] at h
  have hsq3 : (-P₀ - P₁ + P₂) * (-P₀ - P₁ + P₂) = 1 := by
    have h := hgensq (-P₀) (-P₁) P₂
      (by rw [neg_mul_neg, h00]) (by rw [neg_mul_neg, h11])
      (by rw [h22])
      (by rw [neg_mul_neg, h01])
      (by rw [neg_mul_neg, h10])
      (by rw [neg_mul, h02, neg_zero])
      (by rw [mul_neg, h20, neg_zero])
      (by rw [neg_mul, h12, neg_zero])
      (by rw [mul_neg, h21, neg_zero])
    have hrw : -P₀ + -P₁ + P₂ = -P₀ - P₁ + P₂ := by abel
    rwa [hrw] at h
  -- ===== the matrix-level ideal pass =====
  set U : M := exp (s₄ • T₀) * exp ((-s₄) • T₁)
    * exp ((-s₄) • T₂) * exp (s₄ • T₃) with hU
  -- contractivity haves for the four-factor product formula
  have hcX₀ : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • (s₄ • T₀))‖ ≤ 1 := by
    intro u _
    have he : u • (s₄ • T₀) = (u * s₄) • T₀ + (0 : ℝ) • T₁
        + (0 : ℝ) • T₂ + (0 : ℝ) • T₃ := by module
    rw [he]; exact hcT _ _ _ _
  have hcX₁ : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • ((-s₄) • T₁))‖ ≤ 1 := by
    intro u _
    have he : u • ((-s₄) • T₁) = (0 : ℝ) • T₀
        + (u * (-s₄)) • T₁ + (0 : ℝ) • T₂ + (0 : ℝ) • T₃ := by
      module
    rw [he]; exact hcT _ _ _ _
  have hcX₂ : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • ((-s₄) • T₂))‖ ≤ 1 := by
    intro u _
    have he : u • ((-s₄) • T₂) = (0 : ℝ) • T₀ + (0 : ℝ) • T₁
        + (u * (-s₄)) • T₂ + (0 : ℝ) • T₃ := by module
    rw [he]; exact hcT _ _ _ _
  have hcX₃ : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • (s₄ • T₃))‖ ≤ 1 := by
    intro u _
    have he : u • (s₄ • T₃) = (0 : ℝ) • T₀ + (0 : ℝ) • T₁
        + (0 : ℝ) • T₂ + (u * s₄) • T₃ := by module
    rw [he]; exact hcT _ _ _ _
  have hcX₀₁ : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • (s₄ • T₀ + (-s₄) • T₁))‖ ≤ 1 := by
    intro u _
    have he : u • (s₄ • T₀ + (-s₄) • T₁)
        = (u * s₄) • T₀ + (u * (-s₄)) • T₁ + (0 : ℝ) • T₂
          + (0 : ℝ) • T₃ := by module
    rw [he]; exact hcT _ _ _ _
  have hcX₀₁₂ : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • (s₄ • T₀ + (-s₄) • T₁ + (-s₄) • T₂))‖ ≤ 1 := by
    intro u _
    have he : u • (s₄ • T₀ + (-s₄) • T₁ + (-s₄) • T₂)
        = (u * s₄) • T₀ + (u * (-s₄)) • T₁ + (u * (-s₄)) • T₂
          + (0 : ℝ) • T₃ := by module
    rw [he]; exact hcT _ _ _ _
  have hcXfull : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • (s₄ • T₀ + (-s₄) • T₁ + (-s₄) • T₂
        + s₄ • T₃))‖ ≤ 1 := by
    intro u _
    have he : u • (s₄ • T₀ + (-s₄) • T₁ + (-s₄) • T₂ + s₄ • T₃)
        = (u * s₄) • T₀ + (u * (-s₄)) • T₁ + (u * (-s₄)) • T₂
          + (u * s₄) • T₃ := by module
    rw [he]; exact hcT _ _ _ _
  -- pairwise commutator bounds
  have hcomm : ∀ (c d : ℝ) (P Q : M), ‖P‖ ≤ MH → ‖Q‖ ≤ MH →
      ‖(c • P) * (d • Q) - (d • Q) * (c • P)‖
        ≤ |c * d| * (2 * MH ^ 2) := by
    intro c d P Q hP hQ
    have h₁ : (c • P) * (d • Q) = (c * d) • (P * Q) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    have h₂ : (d • Q) * (c • P) = (c * d) • (Q * P) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm d c]
    have hid : (c • P) * (d • Q) - (d • Q) * (c • P)
        = (c * d) • (P * Q - Q * P) := by
      rw [h₁, h₂, ← smul_sub]
    rw [hid, norm_smul, Real.norm_eq_abs]
    have hPQ : ‖P * Q - Q * P‖ ≤ 2 * MH ^ 2 := by
      have ha₁ := norm_mul_le P Q
      have ha₂ := norm_mul_le Q P
      have hb₁ : ‖P‖ * ‖Q‖ ≤ MH ^ 2 := by
        nlinarith [norm_nonneg P, norm_nonneg Q]
      have hb₂ : ‖Q‖ * ‖P‖ ≤ MH ^ 2 := by
        nlinarith [norm_nonneg P, norm_nonneg Q]
      have hc₁ := norm_sub_le (P * Q) (Q * P)
      linarith
    exact mul_le_mul_of_nonneg_left hPQ (abs_nonneg _)
  have habsprod : ∀ c d : ℝ, c = s₄ ∨ c = -s₄ →
      d = s₄ ∨ d = -s₄ → |c * d| = s₄ ^ 2 := by
    intro c d hc hd
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
      simp [abs_mul, abs_neg, sq, abs_mul_abs_self]
  -- the four-factor sharp product formula
  have hfour := NCG.SharpTrotter.four_exp_sub_exp_add_le
    (s₄ • T₀) ((-s₄) • T₁) ((-s₄) • T₂) (s₄ • T₃)
    hcX₀ hcX₁ hcX₂ hcX₃ hcX₀₁ hcX₀₁₂ hcXfull
  have hpair : ‖U - exp (s₄ • T₀ + (-s₄) • T₁ + (-s₄) • T₂
      + s₄ • T₃)‖ ≤ 6 * MH ^ 2 * s₄ ^ 2 := by
    have c01 := hcomm s₄ (-s₄) T₀ T₁ hT₀n hT₁n
    have c02 := hcomm s₄ (-s₄) T₀ T₂ hT₀n hT₂n
    have c12 := hcomm (-s₄) (-s₄) T₁ T₂ hT₁n hT₂n
    have c03 := hcomm s₄ s₄ T₀ T₃ hT₀n hT₃n
    have c13 := hcomm (-s₄) s₄ T₁ T₃ hT₁n hT₃n
    have c23 := hcomm (-s₄) s₄ T₂ T₃ hT₂n hT₃n
    rw [habsprod _ _ (Or.inl rfl) (Or.inr rfl)] at c01 c02
    rw [habsprod _ _ (Or.inr rfl) (Or.inr rfl)] at c12
    rw [habsprod _ _ (Or.inl rfl) (Or.inl rfl)] at c03
    rw [habsprod _ _ (Or.inr rfl) (Or.inl rfl)] at c13 c23
    calc ‖U - exp (s₄ • T₀ + (-s₄) • T₁ + (-s₄) • T₂
          + s₄ • T₃)‖
        ≤ (‖(s₄ • T₀) * ((-s₄) • T₁)
              - ((-s₄) • T₁) * (s₄ • T₀)‖
            + (‖(s₄ • T₀) * ((-s₄) • T₂)
                - ((-s₄) • T₂) * (s₄ • T₀)‖
              + ‖((-s₄) • T₁) * ((-s₄) • T₂)
                  - ((-s₄) • T₂) * ((-s₄) • T₁)‖)
            + (‖(s₄ • T₀) * (s₄ • T₃)
                - (s₄ • T₃) * (s₄ • T₀)‖
              + ‖((-s₄) • T₁) * (s₄ • T₃)
                  - (s₄ • T₃) * ((-s₄) • T₁)‖
              + ‖((-s₄) • T₂) * (s₄ • T₃)
                  - (s₄ • T₃) * ((-s₄) • T₂)‖)) / 2 := hfour
      _ ≤ 6 * MH ^ 2 * s₄ ^ 2 := by
          have hs2 : (0 : ℝ) ≤ s₄ ^ 2 := sq_nonneg _
          linarith
  -- rewrite the exponent sum to `(t/n)•De`
  have hsum4 : s₄ • T₀ + (-s₄) • T₁ + (-s₄) • T₂ + s₄ • T₃
      = (t / n) • De := by
    have h₁ : s₄ • T₀ + (-s₄) • T₁ + (-s₄) • T₂ + s₄ • T₃
        = s₄ • (T₀ - T₁ - T₂ + T₃) := by module
    rw [h₁, ← hDe4, smul_smul]
    congr 1
    rw [hs₄def]
    field_simp
  have hUpair : ‖U - exp ((t / n) • De)‖
      ≤ 6 * MH ^ 2 * s₄ ^ 2 := by
    rw [← hsum4]
    exact hpair
  -- norms of the pass and the target
  have hexp₀ : ‖exp (s₄ • T₀)‖ ≤ 1 := by
    have he : s₄ • T₀ = s₄ • T₀ + (0 : ℝ) • T₁ + (0 : ℝ) • T₂
        + (0 : ℝ) • T₃ := by module
    rw [he]; exact hcT _ _ _ _
  have hexp₁ : ‖exp ((-s₄) • T₁)‖ ≤ 1 := by
    have he : (-s₄) • T₁ = (0 : ℝ) • T₀ + (-s₄) • T₁
        + (0 : ℝ) • T₂ + (0 : ℝ) • T₃ := by module
    rw [he]; exact hcT _ _ _ _
  have hexp₂ : ‖exp ((-s₄) • T₂)‖ ≤ 1 := by
    have he : (-s₄) • T₂ = (0 : ℝ) • T₀ + (0 : ℝ) • T₁
        + (-s₄) • T₂ + (0 : ℝ) • T₃ := by module
    rw [he]; exact hcT _ _ _ _
  have hexp₃ : ‖exp (s₄ • T₃)‖ ≤ 1 := by
    have he : s₄ • T₃ = (0 : ℝ) • T₀ + (0 : ℝ) • T₁
        + (0 : ℝ) • T₂ + s₄ • T₃ := by module
    rw [he]; exact hcT _ _ _ _
  have hUn : ‖U‖ ≤ 1 := by
    rw [hU]
    calc ‖exp (s₄ • T₀) * exp ((-s₄) • T₁) * exp ((-s₄) • T₂)
          * exp (s₄ • T₃)‖
        ≤ ‖exp (s₄ • T₀) * exp ((-s₄) • T₁) * exp ((-s₄) • T₂)‖
          * ‖exp (s₄ • T₃)‖ := norm_mul_le _ _
      _ ≤ ‖exp (s₄ • T₀) * exp ((-s₄) • T₁)‖
          * ‖exp ((-s₄) • T₂)‖ * ‖exp (s₄ • T₃)‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ ‖exp (s₄ • T₀)‖ * ‖exp ((-s₄) • T₁)‖
          * ‖exp ((-s₄) • T₂)‖ * ‖exp (s₄ • T₃)‖ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
              (norm_nonneg _)) (norm_nonneg _)
      _ ≤ 1 * 1 * 1 * 1 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hexp₀ hexp₁
            (norm_nonneg _) zero_le_one) hexp₂ (norm_nonneg _)
            (by positivity)) hexp₃ (norm_nonneg _)
            (by positivity)
      _ = 1 := by ring
  have hVexp : ∀ c : ℝ, ‖exp (c • De)‖ ≤ 1 := by
    intro c
    have he : c • De = (c / 4) • ((4 : ℝ) • De) := by
      rw [smul_smul]
      congr 1
      ring
    rw [he, hDe4]
    have he₂ : (c / 4) • (T₀ - T₁ - T₂ + T₃)
        = (c / 4) • T₀ + (-(c / 4)) • T₁ + (-(c / 4)) • T₂
          + (c / 4) • T₃ := by module
    rw [he₂]
    exact hcT _ _ _ _
  -- matrix-level n-pass estimate
  have hUpow : ‖U ^ n - exp ((t / n) • De) ^ n‖
      ≤ n * (6 * MH ^ 2 * s₄ ^ 2) :=
    le_trans (NCG.SharpTrotter.pow_sub_pow_bound U
      (exp ((t / n) • De)) hUn (hVexp _) n)
      (mul_le_mul_of_nonneg_left hUpair (Nat.cast_nonneg n))
  have hVpow : exp ((t / n) • De) ^ n = exp (t • De) := by
    rw [← exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
  have hUfinal : ‖U ^ n - exp (t • De)‖
      ≤ n * (6 * MH ^ 2 * s₄ ^ 2) := by
    rw [← hVpow]
    exact hUpow
  -- ===== channel level =====
  -- the four ideal channel factors
  set q₀ : B := AdM (P₀ + P₁ + P₂) * AdM (exp (s₄ • D))
    * AdM (P₀ + P₁ + P₂) with hq₀
  set q₁ : B := AdM (P₀ - P₁ - P₂) * AdM (exp ((-s₄) • D))
    * AdM (P₀ - P₁ - P₂) with hq₁
  set q₂ : B := AdM (-P₀ + P₁ - P₂) * AdM (exp ((-s₄) • D))
    * AdM (-P₀ + P₁ - P₂) with hq₂
  set q₃ : B := AdM (-P₀ - P₁ + P₂) * AdM (exp (s₄ • D))
    * AdM (-P₀ - P₁ + P₂) with hq₃
  -- generic per-factor bound
  have hpf : ∀ (aε : B) (c : ℝ) (wε : M),
      ‖aε‖ ≤ 1 → ‖wε‖ ≤ 1 → aε * ι = ι * AdM wε →
      |c| = |t| / (4 * n) →
      ‖(aε * Φ c * aε) * ι
        - ι * (AdM wε * AdM (exp (c • D)) * AdM wε)‖
      ≤ |t| / (4 * n) * εtan + κ * c ^ 2 := by
    intro aε c wε haε hwε hintε hcabs
    have h₁ : (aε * Φ c * aε) * ι
        = aε * Φ c * (ι * AdM wε) := by
      rw [mul_assoc (aε * Φ c) aε ι, hintε]
    have h₂ : ι * (AdM wε * AdM (exp (c • D)) * AdM wε)
        = (aε * ι) * AdM (exp (c • D)) * AdM wε := by
      rw [hintε]
      noncomm_ring
    have h₃ : (aε * Φ c * aε) * ι
        - ι * (AdM wε * AdM (exp (c • D)) * AdM wε)
        = aε * (Φ c * ι - ι * AdM (exp (c • D))) * AdM wε := by
      rw [h₁, h₂]
      noncomm_ring
    rw [h₃]
    have hAdw : ‖AdM wε‖ ≤ 1 := hAdnorm wε hwε
    have hmid := hfac c (le_of_eq hcabs)
    calc ‖aε * (Φ c * ι - ι * AdM (exp (c • D))) * AdM wε‖
        ≤ ‖aε * (Φ c * ι - ι * AdM (exp (c • D)))‖
          * ‖AdM wε‖ := norm_mul_le _ _
      _ ≤ ‖aε‖ * ‖Φ c * ι - ι * AdM (exp (c • D))‖
          * ‖AdM wε‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ 1 * (|c| * εtan + κ * c ^ 2) * 1 := by
          refine mul_le_mul ?_ hAdw (norm_nonneg _) ?_
          · refine mul_le_mul haε hmid (norm_nonneg _)
              zero_le_one
          · have h0 : (0 : ℝ) ≤ |c| * εtan + κ * c ^ 2 := by
              have := hmid
              have := norm_nonneg
                (Φ c * ι - ι * AdM (exp (c • D)))
              linarith
            positivity
      _ = |c| * εtan + κ * c ^ 2 := by ring
      _ = |t| / (4 * n) * εtan + κ * c ^ 2 := by rw [hcabs]
  -- per-factor bounds for the four factors
  have hpf₀ := hpf (a 0) s₄ (P₀ + P₁ + P₂) (ha 0) hW0
    (hint 0) habs4
  have hpf₁ := hpf (a 1) (-s₄) (P₀ - P₁ - P₂) (ha 1) hW1
    (hint 1) habsneg
  have hpf₂ := hpf (a 2) (-s₄) (-P₀ + P₁ - P₂) (ha 2) hW2'
    (hint 2) habsneg
  have hpf₃ := hpf (a 3) s₄ (-P₀ - P₁ + P₂) (ha 3) hW3
    (hint 3) habs4
  -- factor norms
  have hfacnorm : ∀ (aε : B) (c : ℝ), ‖aε‖ ≤ 1 →
      |c| = |t| / (4 * n) → ‖aε * Φ c * aε‖ ≤ 1 := by
    intro aε c haε hc
    have hΦc : ‖Φ c‖ ≤ 1 := hΦ c (le_of_eq hc)
    calc ‖aε * Φ c * aε‖ ≤ ‖aε * Φ c‖ * ‖aε‖ := norm_mul_le _ _
      _ ≤ ‖aε‖ * ‖Φ c‖ * ‖aε‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ 1 * 1 * 1 := by
          refine mul_le_mul (mul_le_mul haε hΦc (norm_nonneg _)
            zero_le_one) haε (norm_nonneg _) (by positivity)
      _ = 1 := by ring
  have hf₀n : ‖a 0 * Φ s₄ * a 0‖ ≤ 1 := hfacnorm _ _ (ha 0) habs4
  have hf₁n : ‖a 1 * Φ (-s₄) * a 1‖ ≤ 1 :=
    hfacnorm _ _ (ha 1) habsneg
  have hf₂n : ‖a 2 * Φ (-s₄) * a 2‖ ≤ 1 :=
    hfacnorm _ _ (ha 2) habsneg
  have hf₃n : ‖a 3 * Φ s₄ * a 3‖ ≤ 1 := hfacnorm _ _ (ha 3) habs4
  -- ideal factor norms
  have hqn : ∀ (wε : M) (c : ℝ), ‖wε‖ ≤ 1 →
      ‖AdM wε * AdM (exp (c • D)) * AdM wε‖ ≤ 1 := by
    intro wε c hwε
    have h₁ : ‖AdM wε‖ ≤ 1 := hAdnorm wε hwε
    have h₂ : ‖AdM (exp (c • D))‖ ≤ 1 :=
      hAdnorm _ (hDexp c)
    calc ‖AdM wε * AdM (exp (c • D)) * AdM wε‖
        ≤ ‖AdM wε * AdM (exp (c • D))‖ * ‖AdM wε‖ :=
          norm_mul_le _ _
      _ ≤ ‖AdM wε‖ * ‖AdM (exp (c • D))‖ * ‖AdM wε‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ 1 * 1 * 1 := by
          refine mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _)
            zero_le_one) h₁ (norm_nonneg _) (by positivity)
      _ = 1 := by ring
  have hq₁n : ‖q₁‖ ≤ 1 := hqn _ _ hW1
  have hq₂n : ‖q₂‖ ≤ 1 := hqn _ _ hW2'
  have hq₃n : ‖q₃‖ ≤ 1 := hqn _ _ hW3
  -- pass-level two-sided telescoping
  have hpass := NCG.SharpTrotter.intertwine_four_bound
    (a 0 * Φ s₄ * a 0) (a 1 * Φ (-s₄) * a 1)
    (a 2 * Φ (-s₄) * a 2) (a 3 * Φ s₄ * a 3)
    q₀ q₁ q₂ q₃ ι hf₀n hf₁n hf₂n hq₁n hq₂n hq₃n
  have hpassBound :
      ‖(a 0 * Φ s₄ * a 0) * (a 1 * Φ (-s₄) * a 1)
        * (a 2 * Φ (-s₄) * a 2) * (a 3 * Φ s₄ * a 3) * ι
        - ι * (q₀ * q₁ * q₂ * q₃)‖
      ≤ 4 * (|t| / (4 * n) * εtan) + 4 * (κ * s₄ ^ 2) := by
    have hnegsq : (-s₄) ^ 2 = s₄ ^ 2 := neg_sq s₄
    rw [hnegsq] at hpf₁ hpf₂
    calc ‖(a 0 * Φ s₄ * a 0) * (a 1 * Φ (-s₄) * a 1)
          * (a 2 * Φ (-s₄) * a 2) * (a 3 * Φ s₄ * a 3) * ι
          - ι * (q₀ * q₁ * q₂ * q₃)‖
        ≤ ‖(a 0 * Φ s₄ * a 0) * ι - ι * q₀‖
          + ‖(a 1 * Φ (-s₄) * a 1) * ι - ι * q₁‖
          + ‖(a 2 * Φ (-s₄) * a 2) * ι - ι * q₂‖
          + ‖(a 3 * Φ s₄ * a 3) * ι - ι * q₃‖ := hpass
      _ ≤ 4 * (|t| / (4 * n) * εtan) + 4 * (κ * s₄ ^ 2) := by
          linarith
  -- collapse the ideal pass to `AdM U`
  have hconjD : ∀ (wε : M) (c : ℝ), wε * wε = 1 →
      wε * exp (c • D) * wε = exp (c • (wε * D * wε)) := by
    intro wε c hwsq
    rw [NCG.SharpTrotter.exp_conj_of_invol wε (c • D) hwsq]
    congr 1
    rw [mul_smul_comm, smul_mul_assoc]
  have hQU : q₀ * q₁ * q₂ * q₃ = AdM U := by
    have hm₀ : q₀ = AdM (exp (s₄ • T₀)) := by
      rw [hq₀, ← hAdmul, ← hAdmul, hconjD _ _ hsq0, hT₀]
    have hm₁ : q₁ = AdM (exp ((-s₄) • T₁)) := by
      rw [hq₁, ← hAdmul, ← hAdmul, hconjD _ _ hsq1, hT₁]
    have hm₂ : q₂ = AdM (exp ((-s₄) • T₂)) := by
      rw [hq₂, ← hAdmul, ← hAdmul, hconjD _ _ hsq2, hT₂]
    have hm₃ : q₃ = AdM (exp (s₄ • T₃)) := by
      rw [hq₃, ← hAdmul, ← hAdmul, hconjD _ _ hsq3, hT₃]
    rw [hm₀, hm₁, hm₂, hm₃, ← hAdmul, ← hAdmul, ← hAdmul, hU]
  -- n-pass two-sided telescoping
  have hfpassn : ‖(a 0 * Φ s₄ * a 0) * (a 1 * Φ (-s₄) * a 1)
      * (a 2 * Φ (-s₄) * a 2) * (a 3 * Φ s₄ * a 3)‖ ≤ 1 := by
    calc ‖(a 0 * Φ s₄ * a 0) * (a 1 * Φ (-s₄) * a 1)
          * (a 2 * Φ (-s₄) * a 2) * (a 3 * Φ s₄ * a 3)‖
        ≤ ‖(a 0 * Φ s₄ * a 0) * (a 1 * Φ (-s₄) * a 1)
            * (a 2 * Φ (-s₄) * a 2)‖ * ‖a 3 * Φ s₄ * a 3‖ :=
          norm_mul_le _ _
      _ ≤ ‖(a 0 * Φ s₄ * a 0) * (a 1 * Φ (-s₄) * a 1)‖
          * ‖a 2 * Φ (-s₄) * a 2‖ * ‖a 3 * Φ s₄ * a 3‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ ‖a 0 * Φ s₄ * a 0‖ * ‖a 1 * Φ (-s₄) * a 1‖
          * ‖a 2 * Φ (-s₄) * a 2‖ * ‖a 3 * Φ s₄ * a 3‖ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
              (norm_nonneg _)) (norm_nonneg _)
      _ ≤ 1 * 1 * 1 * 1 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hf₀n hf₁n
            (norm_nonneg _) zero_le_one) hf₂n (norm_nonneg _)
            (by positivity)) hf₃n (norm_nonneg _) (by positivity)
      _ = 1 := by ring
  have hAdUn : ‖AdM U‖ ≤ 1 := hAdnorm U hUn
  have hpow := NCG.SharpTrotter.intertwine_pow_bound
    ((a 0 * Φ s₄ * a 0) * (a 1 * Φ (-s₄) * a 1)
      * (a 2 * Φ (-s₄) * a 2) * (a 3 * Φ s₄ * a 3))
    (AdM U) ι hfpassn hAdUn n
  have hAdpow : ∀ k : ℕ, (AdM U) ^ k = AdM (U ^ k) := by
    intro k
    induction k with
    | zero => simp [hAd1]
    | succ k ih =>
      rw [pow_succ, pow_succ, ih]
      exact (hAdmul (U ^ k) U).symm
  -- Ad-Lipschitz on the accumulated matrix error
  have hUnpow : ‖U ^ n‖ ≤ 1 := by
    calc ‖U ^ n‖ ≤ ‖U‖ ^ n := norm_pow_le _ _
      _ ≤ 1 := pow_le_one₀ (norm_nonneg U) hUn
  have hlip := hAdLip (U ^ n) (exp (t • De)) hUnpow (hVexp t)
  have hlast : ‖ι * AdM (U ^ n) - ι * AdM (exp (t • De))‖
      ≤ 2 * (n * (6 * MH ^ 2 * s₄ ^ 2)) := by
    calc ‖ι * AdM (U ^ n) - ι * AdM (exp (t • De))‖
        = ‖ι * (AdM (U ^ n) - AdM (exp (t • De)))‖ := by
          rw [mul_sub]
      _ ≤ ‖ι‖ * ‖AdM (U ^ n) - AdM (exp (t • De))‖ :=
          norm_mul_le _ _
      _ ≤ 1 * (2 * ‖U ^ n - exp (t • De)‖) := by
          refine mul_le_mul hι hlip (norm_nonneg _) zero_le_one
      _ ≤ 2 * (n * (6 * MH ^ 2 * s₄ ^ 2)) := by
          rw [one_mul]
          linarith
  -- ===== final assembly =====
  have htri : ‖((a 0 * Φ s₄ * a 0) * (a 1 * Φ (-s₄) * a 1)
      * (a 2 * Φ (-s₄) * a 2) * (a 3 * Φ s₄ * a 3)) ^ n * ι
      - ι * AdM (exp (t • De))‖
      ≤ (n : ℝ) * (4 * (|t| / (4 * n) * εtan)
          + 4 * (κ * s₄ ^ 2))
        + 2 * (n * (6 * MH ^ 2 * s₄ ^ 2)) := by
    have hstep : ‖((a 0 * Φ s₄ * a 0) * (a 1 * Φ (-s₄) * a 1)
        * (a 2 * Φ (-s₄) * a 2) * (a 3 * Φ s₄ * a 3)) ^ n * ι
        - ι * (AdM U) ^ n‖
        ≤ (n : ℝ) * (4 * (|t| / (4 * n) * εtan)
            + 4 * (κ * s₄ ^ 2)) := by
      refine le_trans hpow ?_
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
      rw [← hQU]
      exact hpassBound
    have htriangle := norm_sub_le_norm_sub_add_norm_sub
      (((a 0 * Φ s₄ * a 0) * (a 1 * Φ (-s₄) * a 1)
        * (a 2 * Φ (-s₄) * a 2) * (a 3 * Φ s₄ * a 3)) ^ n * ι)
      (ι * (AdM U) ^ n)
      (ι * AdM (exp (t • De)))
    have hmid : ‖ι * (AdM U) ^ n - ι * AdM (exp (t • De))‖
        ≤ 2 * (n * (6 * MH ^ 2 * s₄ ^ 2)) := by
      rw [hAdpow n]
      exact hlast
    linarith
  -- arithmetic: identify the boxed constant
  have harith : (n : ℝ) * (4 * (|t| / (4 * n) * εtan)
      + 4 * (κ * s₄ ^ 2)) + 2 * (n * (6 * MH ^ 2 * s₄ ^ 2))
      = |t| * εtan + (3 * MH ^ 2 + κ) * t ^ 2 / (4 * n) := by
    rw [hs₄def]
    field_simp
    ring
  rw [harith] at htri
  exact htri

end SMSTChannel
end NCG
