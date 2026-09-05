/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ClockQuarterRoot

/-!
# Schur response–Redheffer scattering equivalence
  (`thm:Schur-Redheffer`, Gran-Tensor manuscript)

* `cayley_scattering`: under the wave coordinates
  `a = 2^{-1/2}(j + iu)`, `b = 2^{-1/2}(j - iu)`, the response
  law `j = Λu` is equivalent to `b = 𝒮a` for the Cayley
  transform `𝒮 = (Λ - i)(Λ + i)⁻¹` (forward identity plus
  surjectivity of the wave chart).
* `redheffer_star_solve`: eliminating the internal waves of the
  signed feedback gluing `a₂ = -b₁`, `b₂ = -a₁` produces the
  Redheffer star product blocks.
* `redheffer_star_exists` / `redheffer_star_mulVec`: for every
  exterior datum the internal waves exist (well-posedness), and
  the star-product matrix reproduces the exterior response.
* `redheffer_star_contraction`: the well-posed star product of
  contractions is a contraction (`1 - SᴴS` positive
  semidefinite), by the internal energy balance.
* `redheffer_star_unitary`: the well-posed star product of
  unitaries is unitary, by the internal inner-product balance.
* `redheffer_star_assoc`: on every well-posed solution of a
  three-component chain, both iterated star products reproduce
  the same exterior response — associativity in solved form.

Rendering disclosed: contraction/unitarity are phrased
algebraically (`1 - SᴴS ⪰ 0`, `SᴴS = 1`); associativity is
rendered as the solve characterization (both association orders
reproduce the full chain response whenever all intermediate
feedback problems are well posed, i.e. the displayed
`Invertible` hypotheses hold).
-/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {p : Type*} [Fintype p]

/-- The sesquilinear pairing is the complexified `normSq` sum. -/
lemma star_dot_self (v : p → ℂ) :
    star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]

/-- `normSq` energy of a concatenated wave vector. -/
lemma normSq_sum_elim {m n : Type*} [Fintype m] [Fintype n]
    (x : m → ℂ) (y : n → ℂ) :
    ∑ i, Complex.normSq (Sum.elim x y i)
      = ∑ i, Complex.normSq (x i) + ∑ i, Complex.normSq (y i) := by
  rw [Fintype.sum_sum_type]
  simp

/-- Sesquilinear pairing of concatenated wave vectors. -/
lemma dot_sum_elim {m n : Type*} [Fintype m] [Fintype n]
    (x x' : m → ℂ) (y y' : n → ℂ) :
    star (Sum.elim x y) ⬝ᵥ Sum.elim x' y'
      = star x ⬝ᵥ x' + star y ⬝ᵥ y' := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- A matrix is a contraction (`1 - SᴴS ⪰ 0`) iff it decreases
the `normSq` energy of every vector. -/
lemma contraction_psd_iff [DecidableEq p] (S : Matrix p p ℂ) :
    (1 - Sᴴ * S).PosSemidef
      ↔ ∀ v : p → ℂ,
          ∑ i, Complex.normSq ((S *ᵥ v) i)
            ≤ ∑ i, Complex.normSq (v i) := by
  have hquad : ∀ v : p → ℂ,
      star v ⬝ᵥ ((1 - Sᴴ * S) *ᵥ v)
        = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ)
          - ((∑ i, Complex.normSq ((S *ᵥ v) i) : ℝ) : ℂ) := by
    intro v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
      star_dot_self]
    congr 1
    rw [← star_dot_self]
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  constructor
  · intro h v
    have h2 := h.dotProduct_mulVec_nonneg v
    rw [hquad, ← Complex.ofReal_sub] at h2
    rw [← sub_nonneg]
    exact_mod_cast h2
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Matrix.isHermitian_one).sub
        (Matrix.isHermitian_conjTranspose_mul_self S)) fun v => ?_
    rw [hquad, ← Complex.ofReal_sub]
    exact_mod_cast sub_nonneg.mpr (h v)

/-- An isometry (`SᴴS = 1`) preserves the sesquilinear
pairing. -/
lemma inner_of_isometry [DecidableEq p] (S : Matrix p p ℂ) (h : Sᴴ * S = 1)
    (v w : p → ℂ) :
    star (S *ᵥ v) ⬝ᵥ (S *ᵥ w) = star v ⬝ᵥ w := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

/-- `thm:Schur-Redheffer`, wave-chart clause: the response law
`j = Λu` transports to `b = 𝒮a` under the Cayley transform, and
the wave chart `u ↦ a` is onto. -/
theorem cayley_scattering [DecidableEq p] (Λ : Matrix p p ℂ)
    [Invertible (Λ + Complex.I • 1)] :
    (∀ u : p → ℂ,
      ((Λ - Complex.I • 1) * (Λ + Complex.I • 1)⁻¹) *ᵥ
          (invSqrt2 • (Λ *ᵥ u + Complex.I • u))
        = invSqrt2 • (Λ *ᵥ u - Complex.I • u))
    ∧ (∀ a : p → ℂ, ∃ u : p → ℂ,
        a = invSqrt2 • (Λ *ᵥ u + Complex.I • u)) := by
  have h0 : invSqrt2 ≠ 0 := by
    intro h
    have hsq := invSqrt2_sq
    rw [h] at hsq
    norm_num at hsq
  have hplus : ∀ u : p → ℂ, Λ *ᵥ u + Complex.I • u
      = (Λ + Complex.I • 1) *ᵥ u := by
    intro u
    rw [Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hminus : ∀ u : p → ℂ, Λ *ᵥ u - Complex.I • u
      = (Λ - Complex.I • 1) *ᵥ u := by
    intro u
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  constructor
  · intro u
    rw [hplus, hminus, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.mul_one]
  · intro a
    refine ⟨invSqrt2⁻¹ • ((Λ + Complex.I • 1)⁻¹ *ᵥ a), ?_⟩
    rw [hplus, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_inv_of_invertible, Matrix.one_mulVec,
      smul_smul, mul_inv_cancel₀ h0, one_smul]

section Star

variable {eL c eR : Type*} [Fintype eL] [Fintype c] [Fintype eR]
  [DecidableEq c]

/-- `thm:Schur-Redheffer`, elimination clause: solving the signed
feedback `a₂ = -b₁`, `b₂ = -a₁` between two scattering relations
expresses the exterior outputs through the Redheffer star-product
blocks. -/
theorem redheffer_star_solve
    (A1 : Matrix eL eL ℂ) (B1 : Matrix eL c ℂ)
    (C1 : Matrix c eL ℂ) (D1 : Matrix c c ℂ)
    (A2 : Matrix c c ℂ) (B2 : Matrix c eR ℂ)
    (C2 : Matrix eR c ℂ) (D2 : Matrix eR eR ℂ)
    [Invertible (1 - D1 * A2)]
    (aL bL : eL → ℂ) (a1 b1 a2 b2 : c → ℂ) (aR bR : eR → ℂ)
    (h1L : bL = A1 *ᵥ aL + B1 *ᵥ a1)
    (h1c : b1 = C1 *ᵥ aL + D1 *ᵥ a1)
    (h2c : b2 = A2 *ᵥ a2 + B2 *ᵥ aR)
    (h2R : bR = C2 *ᵥ a2 + D2 *ᵥ aR)
    (hf1 : a2 = -b1) (hf2 : b2 = -a1) :
    bL = (A1 + B1 * A2 * (1 - D1 * A2)⁻¹ * C1) *ᵥ aL
        + (-(B1 * B2)
            - B1 * A2 * (1 - D1 * A2)⁻¹ * D1 * B2) *ᵥ aR
    ∧ bR = (-(C2 * (1 - D1 * A2)⁻¹ * C1)) *ᵥ aL
        + (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2) *ᵥ aR := by
  have ha1 : a1 = A2 *ᵥ b1 - B2 *ᵥ aR := by
    have h := hf2
    rw [h2c, hf1, Matrix.mulVec_neg] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at hi ⊢
    linear_combination hi
  have hkey : (1 - D1 * A2) *ᵥ b1
      = C1 *ᵥ aL - D1 *ᵥ (B2 *ᵥ aR) := by
    have h := h1c
    rw [ha1] at h
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    funext i
    have hi := congrFun h i
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Pi.add_apply, Pi.sub_apply] at hi ⊢
    linear_combination hi
  have hb1 : b1 = ((1 - D1 * A2)⁻¹ * C1) *ᵥ aL
      - ((1 - D1 * A2)⁻¹ * (D1 * B2)) *ᵥ aR := by
    have h := congrArg (fun v => (1 - D1 * A2)⁻¹ *ᵥ v) hkey
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec] at h
    rw [Matrix.inv_mul_of_invertible, Matrix.one_mulVec] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.sub_apply] at hi ⊢
    linear_combination hi
  constructor
  · rw [h1L, ha1, hb1]
    funext i
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.neg_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply]
    ring
  · rw [h2R, hf1, hb1]
    funext i
    simp only [Matrix.add_mulVec,
      Matrix.neg_mulVec, Matrix.mulVec_sub, Matrix.mulVec_neg,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply]
    ring

/-- Well-posedness: for every exterior datum the internal waves
of the signed feedback gluing exist. -/
theorem redheffer_star_exists
    (A1 : Matrix eL eL ℂ) (B1 : Matrix eL c ℂ)
    (C1 : Matrix c eL ℂ) (D1 : Matrix c c ℂ)
    (A2 : Matrix c c ℂ) (B2 : Matrix c eR ℂ)
    (C2 : Matrix eR c ℂ) (D2 : Matrix eR eR ℂ)
    [Invertible (1 - D1 * A2)]
    (aL : eL → ℂ) (aR : eR → ℂ) :
    ∃ (bL : eL → ℂ) (a1 b1 a2 b2 : c → ℂ) (bR : eR → ℂ),
      bL = A1 *ᵥ aL + B1 *ᵥ a1
      ∧ b1 = C1 *ᵥ aL + D1 *ᵥ a1
      ∧ b2 = A2 *ᵥ a2 + B2 *ᵥ aR
      ∧ bR = C2 *ᵥ a2 + D2 *ᵥ aR
      ∧ a2 = -b1 ∧ b2 = -a1 := by
  set b1 : c → ℂ :=
    (1 - D1 * A2)⁻¹ *ᵥ (C1 *ᵥ aL - D1 *ᵥ (B2 *ᵥ aR)) with hb1def
  set a1 : c → ℂ := A2 *ᵥ b1 - B2 *ᵥ aR with ha1def
  have hkey : (1 - D1 * A2) *ᵥ b1
      = C1 *ᵥ aL - D1 *ᵥ (B2 *ᵥ aR) := by
    rw [hb1def, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
      Matrix.one_mulVec]
  refine ⟨A1 *ᵥ aL + B1 *ᵥ a1, a1, b1, -b1, -a1,
    C2 *ᵥ (-b1) + D2 *ᵥ aR, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · rw [ha1def]
    funext i
    have hi := congrFun hkey i
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_mulVec, Pi.add_apply,
      Pi.sub_apply] at hi ⊢
    linear_combination hi
  · rw [ha1def]
    funext i
    simp only [Matrix.mulVec_neg, Pi.add_apply,
      Pi.neg_apply, Pi.sub_apply]
    ring

/-- The Redheffer star-product matrix reproduces the exterior
response of any solved feedback system. -/
theorem redheffer_star_mulVec
    (A1 : Matrix eL eL ℂ) (B1 : Matrix eL c ℂ)
    (C1 : Matrix c eL ℂ) (D1 : Matrix c c ℂ)
    (A2 : Matrix c c ℂ) (B2 : Matrix c eR ℂ)
    (C2 : Matrix eR c ℂ) (D2 : Matrix eR eR ℂ)
    [Invertible (1 - D1 * A2)]
    (aL bL : eL → ℂ) (a1 b1 a2 b2 : c → ℂ) (aR bR : eR → ℂ)
    (h1L : bL = A1 *ᵥ aL + B1 *ᵥ a1)
    (h1c : b1 = C1 *ᵥ aL + D1 *ᵥ a1)
    (h2c : b2 = A2 *ᵥ a2 + B2 *ᵥ aR)
    (h2R : bR = C2 *ᵥ a2 + D2 *ᵥ aR)
    (hf1 : a2 = -b1) (hf2 : b2 = -a1) :
    (Matrix.fromBlocks
        (A1 + B1 * A2 * (1 - D1 * A2)⁻¹ * C1)
        (-(B1 * B2) - B1 * A2 * (1 - D1 * A2)⁻¹ * D1 * B2)
        (-(C2 * (1 - D1 * A2)⁻¹ * C1))
        (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2))
      *ᵥ Sum.elim aL aR = Sum.elim bL bR := by
  obtain ⟨hL, hR⟩ := redheffer_star_solve A1 B1 C1 D1 A2 B2 C2 D2
    aL bL a1 b1 a2 b2 aR bR h1L h1c h2c h2R hf1 hf2
  rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, ← hL, ← hR]

/-- `thm:Schur-Redheffer`, contraction closure: the well-posed
star product of contractions is a contraction. -/
theorem redheffer_star_contraction [DecidableEq eL] [DecidableEq eR]
    (A1 : Matrix eL eL ℂ) (B1 : Matrix eL c ℂ)
    (C1 : Matrix c eL ℂ) (D1 : Matrix c c ℂ)
    (A2 : Matrix c c ℂ) (B2 : Matrix c eR ℂ)
    (C2 : Matrix eR c ℂ) (D2 : Matrix eR eR ℂ)
    [Invertible (1 - D1 * A2)]
    (hc1 : (1 - (Matrix.fromBlocks A1 B1 C1 D1)ᴴ
        * Matrix.fromBlocks A1 B1 C1 D1).PosSemidef)
    (hc2 : (1 - (Matrix.fromBlocks A2 B2 C2 D2)ᴴ
        * Matrix.fromBlocks A2 B2 C2 D2).PosSemidef) :
    (1 - (Matrix.fromBlocks
        (A1 + B1 * A2 * (1 - D1 * A2)⁻¹ * C1)
        (-(B1 * B2) - B1 * A2 * (1 - D1 * A2)⁻¹ * D1 * B2)
        (-(C2 * (1 - D1 * A2)⁻¹ * C1))
        (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2))ᴴ
      * Matrix.fromBlocks
        (A1 + B1 * A2 * (1 - D1 * A2)⁻¹ * C1)
        (-(B1 * B2) - B1 * A2 * (1 - D1 * A2)⁻¹ * D1 * B2)
        (-(C2 * (1 - D1 * A2)⁻¹ * C1))
        (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2)).PosSemidef := by
  rw [contraction_psd_iff] at hc1 hc2 ⊢
  intro v
  obtain ⟨aL, aR, rfl⟩ : ∃ aL aR, v = Sum.elim aL aR :=
    ⟨v ∘ Sum.inl, v ∘ Sum.inr, by funext i; cases i <;> rfl⟩
  obtain ⟨bL, a1, b1, a2, b2, bR, h1L, h1c, h2c, h2R, hf1, hf2⟩ :=
    redheffer_star_exists A1 B1 C1 D1 A2 B2 C2 D2 aL aR
  rw [redheffer_star_mulVec A1 B1 C1 D1 A2 B2 C2 D2
    aL bL a1 b1 a2 b2 aR bR h1L h1c h2c h2R hf1 hf2]
  have hS1v : Matrix.fromBlocks A1 B1 C1 D1 *ᵥ Sum.elim aL a1
      = Sum.elim bL b1 := by
    rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, ← h1L, ← h1c]
  have hS2v : Matrix.fromBlocks A2 B2 C2 D2 *ᵥ Sum.elim a2 aR
      = Sum.elim b2 bR := by
    rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, ← h2c, ← h2R]
  have e1 := hc1 (Sum.elim aL a1)
  have e2 := hc2 (Sum.elim a2 aR)
  rw [hS1v, normSq_sum_elim, normSq_sum_elim] at e1
  rw [hS2v, normSq_sum_elim, normSq_sum_elim] at e2
  rw [normSq_sum_elim, normSq_sum_elim]
  have hn1 : ∑ i, Complex.normSq (a2 i)
      = ∑ i, Complex.normSq (b1 i) := by
    rw [hf1]
    simp [Complex.normSq_neg]
  have hn2 : ∑ i, Complex.normSq (b2 i)
      = ∑ i, Complex.normSq (a1 i) := by
    rw [hf2]
    simp [Complex.normSq_neg]
  rw [hn1] at e2
  rw [hn2] at e2
  linarith

/-- `thm:Schur-Redheffer`, unitary closure: the well-posed star
product of unitaries is unitary. -/
theorem redheffer_star_unitary [DecidableEq eL] [DecidableEq eR]
    (A1 : Matrix eL eL ℂ) (B1 : Matrix eL c ℂ)
    (C1 : Matrix c eL ℂ) (D1 : Matrix c c ℂ)
    (A2 : Matrix c c ℂ) (B2 : Matrix c eR ℂ)
    (C2 : Matrix eR c ℂ) (D2 : Matrix eR eR ℂ)
    [Invertible (1 - D1 * A2)]
    (hu1 : (Matrix.fromBlocks A1 B1 C1 D1)ᴴ
        * Matrix.fromBlocks A1 B1 C1 D1 = 1)
    (hu2 : (Matrix.fromBlocks A2 B2 C2 D2)ᴴ
        * Matrix.fromBlocks A2 B2 C2 D2 = 1) :
    (Matrix.fromBlocks
        (A1 + B1 * A2 * (1 - D1 * A2)⁻¹ * C1)
        (-(B1 * B2) - B1 * A2 * (1 - D1 * A2)⁻¹ * D1 * B2)
        (-(C2 * (1 - D1 * A2)⁻¹ * C1))
        (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2))ᴴ
      * Matrix.fromBlocks
        (A1 + B1 * A2 * (1 - D1 * A2)⁻¹ * C1)
        (-(B1 * B2) - B1 * A2 * (1 - D1 * A2)⁻¹ * D1 * B2)
        (-(C2 * (1 - D1 * A2)⁻¹ * C1))
        (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2) = 1 := by
  set SB := Matrix.fromBlocks
      (A1 + B1 * A2 * (1 - D1 * A2)⁻¹ * C1)
      (-(B1 * B2) - B1 * A2 * (1 - D1 * A2)⁻¹ * D1 * B2)
      (-(C2 * (1 - D1 * A2)⁻¹ * C1))
      (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2) with hSB
  have hinner : ∀ v w : eL ⊕ eR → ℂ,
      star (SB *ᵥ v) ⬝ᵥ (SB *ᵥ w) = star v ⬝ᵥ w := by
    intro v w
    obtain ⟨aL, aR, rfl⟩ : ∃ aL aR, v = Sum.elim aL aR :=
      ⟨v ∘ Sum.inl, v ∘ Sum.inr, by funext i; cases i <;> rfl⟩
    obtain ⟨aL', aR', rfl⟩ : ∃ aL' aR', w = Sum.elim aL' aR' :=
      ⟨w ∘ Sum.inl, w ∘ Sum.inr, by funext i; cases i <;> rfl⟩
    obtain ⟨bL, a1, b1, a2, b2, bR,
      h1L, h1c, h2c, h2R, hf1, hf2⟩ :=
      redheffer_star_exists A1 B1 C1 D1 A2 B2 C2 D2 aL aR
    obtain ⟨bL', a1', b1', a2', b2', bR',
      h1L', h1c', h2c', h2R', hf1', hf2'⟩ :=
      redheffer_star_exists A1 B1 C1 D1 A2 B2 C2 D2 aL' aR'
    rw [hSB, redheffer_star_mulVec A1 B1 C1 D1 A2 B2 C2 D2
        aL bL a1 b1 a2 b2 aR bR h1L h1c h2c h2R hf1 hf2,
      redheffer_star_mulVec A1 B1 C1 D1 A2 B2 C2 D2
        aL' bL' a1' b1' a2' b2' aR' bR'
        h1L' h1c' h2c' h2R' hf1' hf2']
    have hS1v : Matrix.fromBlocks A1 B1 C1 D1 *ᵥ Sum.elim aL a1
        = Sum.elim bL b1 := by
      rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, ← h1L, ← h1c]
    have hS1w : Matrix.fromBlocks A1 B1 C1 D1
        *ᵥ Sum.elim aL' a1' = Sum.elim bL' b1' := by
      rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, ← h1L', ← h1c']
    have hS2v : Matrix.fromBlocks A2 B2 C2 D2 *ᵥ Sum.elim a2 aR
        = Sum.elim b2 bR := by
      rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, ← h2c, ← h2R]
    have hS2w : Matrix.fromBlocks A2 B2 C2 D2
        *ᵥ Sum.elim a2' aR' = Sum.elim b2' bR' := by
      rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, ← h2c', ← h2R']
    have e1 := inner_of_isometry _ hu1
      (Sum.elim aL a1) (Sum.elim aL' a1')
    have e2 := inner_of_isometry _ hu2
      (Sum.elim a2 aR) (Sum.elim a2' aR')
    rw [hS1v, hS1w, dot_sum_elim, dot_sum_elim] at e1
    rw [hS2v, hS2w, dot_sum_elim, dot_sum_elim] at e2
    have hn1 : star a2 ⬝ᵥ a2' = star b1 ⬝ᵥ b1' := by
      rw [hf1, hf1']
      simp [dotProduct]
    have hn2 : star b2 ⬝ᵥ b2' = star a1 ⬝ᵥ a1' := by
      rw [hf2, hf2']
      simp [dotProduct]
    rw [hn1, hn2] at e2
    rw [dot_sum_elim, dot_sum_elim]
    linear_combination e1 + e2
  ext i j
  have hij := hinner (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ))
  have hL : star (SB *ᵥ Pi.single i (1 : ℂ))
        ⬝ᵥ (SB *ᵥ Pi.single j (1 : ℂ))
      = (SBᴴ * SB) i j := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul]
    simp [Matrix.vecMul, dotProduct, Pi.single_apply,
      Finset.sum_ite_eq']
  have hR : star (Pi.single i (1 : ℂ)) ⬝ᵥ Pi.single j (1 : ℂ)
      = (1 : Matrix (eL ⊕ eR) (eL ⊕ eR) ℂ) i j := by
    have hstar : star (Pi.single i (1 : ℂ) : eL ⊕ eR → ℂ)
        = (Pi.single i (1 : ℂ) : eL ⊕ eR → ℂ) := by
      funext k
      rw [Pi.star_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [hstar]
    by_cases h : i = j
    · subst h
      simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq']
    · simp [dotProduct, Pi.single_apply, h,
        Finset.sum_ite_eq', Ne.symm h]
  rw [hL, hR] at hij
  exact hij

/-- `thm:Schur-Redheffer`, associativity clause in solved form:
on every well-posed solution of a three-component chain, both
iterated star products reproduce the same exterior response. -/
theorem redheffer_star_assoc {c2 : Type*} [Fintype c2]
    [DecidableEq c2]
    (A1 : Matrix eL eL ℂ) (B1 : Matrix eL c ℂ)
    (C1 : Matrix c eL ℂ) (D1 : Matrix c c ℂ)
    (A2 : Matrix c c ℂ) (B2 : Matrix c c2 ℂ)
    (C2 : Matrix c2 c ℂ) (D2 : Matrix c2 c2 ℂ)
    (A3 : Matrix c2 c2 ℂ) (B3 : Matrix c2 eR ℂ)
    (C3 : Matrix eR c2 ℂ) (D3 : Matrix eR eR ℂ)
    [Invertible (1 - D1 * A2)]
    [Invertible (1 - (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2) * A3)]
    [Invertible (1 - D2 * A3)]
    [Invertible (1 - D1
      * (A2 + B2 * A3 * (1 - D2 * A3)⁻¹ * C2))]
    (aL bL : eL → ℂ) (a1 b1 a2 b2 : c → ℂ)
    (a3 b3 a4 b4 : c2 → ℂ) (aR bR : eR → ℂ)
    (h1L : bL = A1 *ᵥ aL + B1 *ᵥ a1)
    (h1c : b1 = C1 *ᵥ aL + D1 *ᵥ a1)
    (h2L : b2 = A2 *ᵥ a2 + B2 *ᵥ a3)
    (h2R : b3 = C2 *ᵥ a2 + D2 *ᵥ a3)
    (h3L : b4 = A3 *ᵥ a4 + B3 *ᵥ aR)
    (h3R : bR = C3 *ᵥ a4 + D3 *ᵥ aR)
    (hf1 : a2 = -b1) (hf2 : b2 = -a1)
    (hg1 : a4 = -b3) (hg2 : b4 = -a3) :
    (bL = ((A1 + B1 * A2 * (1 - D1 * A2)⁻¹ * C1)
          + (-(B1 * B2) - B1 * A2 * (1 - D1 * A2)⁻¹ * D1 * B2)
            * A3
            * (1 - (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2)
                * A3)⁻¹
            * (-(C2 * (1 - D1 * A2)⁻¹ * C1))) *ᵥ aL
        + (-((-(B1 * B2)
              - B1 * A2 * (1 - D1 * A2)⁻¹ * D1 * B2) * B3)
            - (-(B1 * B2)
              - B1 * A2 * (1 - D1 * A2)⁻¹ * D1 * B2)
              * A3
              * (1 - (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2)
                  * A3)⁻¹
              * (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2)
              * B3) *ᵥ aR)
    ∧ (bL = (A1 + B1
          * (A2 + B2 * A3 * (1 - D2 * A3)⁻¹ * C2)
          * (1 - D1
              * (A2 + B2 * A3 * (1 - D2 * A3)⁻¹ * C2))⁻¹
          * C1) *ᵥ aL
        + (-(B1 * (-(B2 * B3)
              - B2 * A3 * (1 - D2 * A3)⁻¹ * D2 * B3))
            - B1 * (A2 + B2 * A3 * (1 - D2 * A3)⁻¹ * C2)
              * (1 - D1
                  * (A2 + B2 * A3
                      * (1 - D2 * A3)⁻¹ * C2))⁻¹
              * D1
              * (-(B2 * B3)
                  - B2 * A3 * (1 - D2 * A3)⁻¹ * D2 * B3))
            *ᵥ aR) := by
  constructor
  · -- left association: (S₁ ⋆ S₂) ⋆ S₃
    obtain ⟨h12L, h12R⟩ := redheffer_star_solve
      A1 B1 C1 D1 A2 B2 C2 D2
      aL bL a1 b1 a2 b2 a3 b3 h1L h1c h2L h2R hf1 hf2
    obtain ⟨hL, _⟩ := redheffer_star_solve
      (A1 + B1 * A2 * (1 - D1 * A2)⁻¹ * C1)
      (-(B1 * B2) - B1 * A2 * (1 - D1 * A2)⁻¹ * D1 * B2)
      (-(C2 * (1 - D1 * A2)⁻¹ * C1))
      (D2 + C2 * (1 - D1 * A2)⁻¹ * D1 * B2)
      A3 B3 C3 D3
      aL bL a3 b3 a4 b4 aR bR h12L h12R h3L h3R hg1 hg2
    exact hL
  · -- right association: S₁ ⋆ (S₂ ⋆ S₃)
    obtain ⟨h23L, h23R⟩ := redheffer_star_solve
      A2 B2 C2 D2 A3 B3 C3 D3
      a2 b2 a3 b3 a4 b4 aR bR h2L h2R h3L h3R hg1 hg2
    obtain ⟨hL, _⟩ := redheffer_star_solve
      A1 B1 C1 D1
      (A2 + B2 * A3 * (1 - D2 * A3)⁻¹ * C2)
      (-(B2 * B3) - B2 * A3 * (1 - D2 * A3)⁻¹ * D2 * B3)
      (-(C3 * (1 - D2 * A3)⁻¹ * C2))
      (D3 + C3 * (1 - D2 * A3)⁻¹ * D2 * B3)
      aL bL a1 b1 a2 b2 aR bR h1L h1c h23L h23R hf1 hf2
    exact hL

end Star

end NCG
