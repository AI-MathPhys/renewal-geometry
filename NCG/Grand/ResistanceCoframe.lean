/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Resistance reconstruction and coframe calibration
  (`thm:action-resistance-coframe`, Gran-Tensor manuscript)

* `action_resistance_reconstruction`:
  (i) the resistance entries are the quadratic form of the
      pseudoinverse on edge differences,
      `ℛ_ij = K_ii + K_jj - K_ij - K_ji`;
  (ii) the boxed double-centering reconstruction
      `P₀ℛP₀ = -2K` for a centered symmetric `K` (`K1 = 0`),
      i.e. `H† = -½P₀ℛP₀` — the complete resistance geometry
      reconstructs the positive action.

* `action_coframe_router`:
  (iii) the boxed comparison residual
      `R_{C|A} = G - X*H⁻¹X = C*(I - P_A)C ⪰ 0` with the
      hermitian idempotent `P_A = AH⁻¹A*`;
  (iv) it vanishes exactly when the coframe source factors
      through the action source, on which branch the boxed
      unique router is `T = H⁻¹X` and `G = T*HT`;
  (v) the boxed irreducible-symmetry collapse: if the router
      lies in a scalar commutant then `C = cA` and
      `G = |c|²H`.

The identification of `K` with `H†` for a connected action
Hessian with `Ker H = span{1}` (so that `H†` is centered and
symmetric) and the support-graph reading of the
reconstruction are the manuscript's pseudoinverse layer.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:action-resistance-coframe`, resistance
reconstruction. -/
theorem action_resistance_reconstruction {n : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n]
    (K : Matrix n n ℝ) (hKs : Kᵀ = K)
    (hKc : ∀ i, ∑ j, K i j = 0) :
    -- (i) resistance entries as edge quadratic forms
    (∀ i j : n,
      (Pi.single i (1 : ℝ) - Pi.single j 1)
        ⬝ᵥ (K *ᵥ (Pi.single i (1 : ℝ) - Pi.single j 1))
      = K i i + K j j - K i j - K j i)
    -- (ii) the boxed double-centering reconstruction
    ∧ (∀ P₀ R : Matrix n n ℝ,
        (∀ i j, P₀ i j
          = (if i = j then (1 : ℝ) else 0)
            - ((Fintype.card n : ℝ))⁻¹) →
        (∀ i j, R i j = K i i + K j j - 2 * K i j) →
        ∀ i j, (P₀ * (R * P₀)) i j = -2 * K i j) := by
  have hcard : (0 : ℝ) < (Fintype.card n : ℝ) := by
    have := Fintype.card_pos (α := n)
    exact_mod_cast this
  have hcne : ((Fintype.card n : ℝ)) ≠ 0 := ne_of_gt hcard
  set N : ℝ := (Fintype.card n : ℝ) with hN
  constructor
  · intro i j
    have hmul : ∀ a : n,
        (K *ᵥ (Pi.single i (1 : ℝ) - Pi.single j 1)) a
        = K a i - K a j := by
      intro a
      rw [Matrix.mulVec, dotProduct]
      simp only [Pi.sub_apply, Pi.single_apply, mul_sub,
        mul_ite, mul_one, mul_zero,
        Finset.sum_sub_distrib]
      rw [Finset.sum_ite_eq' Finset.univ i
          (fun x => K a x),
        Finset.sum_ite_eq' Finset.univ j
          (fun x => K a x)]
      simp
    simp [dotProduct, hmul, Pi.single_apply, sub_mul,
      ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
      Finset.sum_ite_eq']
    ring
  · intro P₀ R hP₀ hR i j
    have hleft : ∀ (M : Matrix n n ℝ) (a b : n),
        (P₀ * M) a b = M a b - N⁻¹ * ∑ t, M t b := by
      intro M a b
      rw [Matrix.mul_apply]
      simp only [hP₀, sub_mul, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq
        Finset.univ a (fun t => M t b)]
      simp only [Finset.mem_univ, if_true]
      congr 1
      rw [Finset.mul_sum]
      try exact Finset.sum_congr rfl fun t _ => mul_comm _ _
    have hright : ∀ (M : Matrix n n ℝ) (a b : n),
        (M * P₀) a b = M a b - N⁻¹ * ∑ t, M a t := by
      intro M a b
      rw [Matrix.mul_apply]
      simp only [hP₀, mul_sub, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq'
        Finset.univ b (fun t => M a t)]
      simp only [Finset.mem_univ, if_true]
      congr 1
      rw [Finset.mul_sum]
      try exact Finset.sum_congr rfl fun t _ => mul_comm _ _
    have hrowR : ∀ a : n, ∑ b, R a b
        = N * K a a + ∑ b, K b b := by
      intro a
      simp only [hR]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum, hKc a]
      simp [hN]
    have hKcol : ∀ b : n, ∑ a, K a b = 0 := by
      intro b
      rw [← hKc b]
      exact Finset.sum_congr rfl fun a _ => by
        have := congrFun (congrFun hKs b) a
        simpa [Matrix.transpose_apply] using this
    have hcolR : ∀ b : n, ∑ a, R a b
        = (∑ a, K a a) + N * K b b := by
      intro b
      simp only [hR]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum, hKcol b]
      simp [hN]
    rw [hleft, hright]
    have hinner : ∀ a : n, (R * P₀) a j
        = R a j - N⁻¹ * ∑ b, R a b := fun a => hright R a j
    rw [Finset.sum_congr rfl fun a _ => hinner a,
      Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_congr rfl fun a _ => hrowR a,
      Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hcolR, hrowR]
    simp only [hR, hN]
    field_simp
    ring

/-- `thm:action-resistance-coframe`, coframe comparison and
router. -/
theorem action_coframe_router {w y : Type*} [Fintype w]
    [Fintype y] [DecidableEq w] [DecidableEq y]
    (A C : Matrix y w ℂ) (Hi : Matrix w w ℂ)
    (hHi1 : (Aᴴ * A) * Hi = 1) (_hHi2 : Hi * (Aᴴ * A) = 1)
    (hHiH : Hiᴴ = Hi) :
    -- (iii) the boxed comparison residual and its positivity
    ((Cᴴ * C) - (Aᴴ * C)ᴴ * Hi * (Aᴴ * C)
      = Cᴴ * ((1 : Matrix y y ℂ) - A * Hi * Aᴴ) * C)
    ∧ ((A * Hi * Aᴴ) * (A * Hi * Aᴴ) = A * Hi * Aᴴ)
    ∧ ((A * Hi * Aᴴ)ᴴ = A * Hi * Aᴴ)
    ∧ ((Cᴴ * ((1 : Matrix y y ℂ) - A * Hi * Aᴴ)
        * C).PosSemidef)
    -- (iv) vanishing exactly on the factoring branch
    ∧ (Cᴴ * ((1 : Matrix y y ℂ) - A * Hi * Aᴴ) * C = 0
        ↔ C = A * (Hi * (Aᴴ * C)))
    -- and then the boxed router identity `G = T*HT`
    ∧ (C = A * (Hi * (Aᴴ * C)) →
        Cᴴ * C = (Hi * (Aᴴ * C))ᴴ * (Aᴴ * A)
          * (Hi * (Aᴴ * C)))
    -- (v) the boxed scalar-commutant collapse
    ∧ (∀ c : ℂ, Hi * (Aᴴ * C) = c • 1 →
        C = A * (Hi * (Aᴴ * C)) →
        C = c • A ∧ Cᴴ * C
          = ((starRingEnd ℂ) c * c) • (Aᴴ * A)) := by
  have hproj : (A * Hi * Aᴴ) * (A * Hi * Aᴴ)
      = A * Hi * Aᴴ := by
    calc (A * Hi * Aᴴ) * (A * Hi * Aᴴ)
        = A * (Hi * ((Aᴴ * A) * Hi)) * Aᴴ := by
          simp only [Matrix.mul_assoc]
      _ = A * Hi * Aᴴ := by
          rw [hHi1, Matrix.mul_one]
  have hprojH : (A * Hi * Aᴴ)ᴴ = A * Hi * Aᴴ := by
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hHiH,
      Matrix.mul_assoc]
  have hQH : ((1 : Matrix y y ℂ) - A * Hi * Aᴴ)ᴴ
      = 1 - A * Hi * Aᴴ := by
    rw [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hprojH]
  have hQ2 : ((1 : Matrix y y ℂ) - A * Hi * Aᴴ)
      * (1 - A * Hi * Aᴴ) = 1 - A * Hi * Aᴴ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hproj]
    abel
  have hfac : Cᴴ * ((1 : Matrix y y ℂ) - A * Hi * Aᴴ) * C
      = (((1 : Matrix y y ℂ) - A * Hi * Aᴴ) * C)ᴴ
        * (((1 : Matrix y y ℂ) - A * Hi * Aᴴ) * C) := by
    rw [Matrix.conjTranspose_mul, hQH]
    calc Cᴴ * ((1 : Matrix y y ℂ) - A * Hi * Aᴴ) * C
        = Cᴴ * (((1 : Matrix y y ℂ) - A * Hi * Aᴴ)
          * (((1 : Matrix y y ℂ) - A * Hi * Aᴴ) * C)) := by
          rw [← Matrix.mul_assoc
            ((1 : Matrix y y ℂ) - A * Hi * Aᴴ), hQ2,
            Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨?_, hproj, hprojH, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  · rw [hfac]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [hfac]
    constructor
    · intro h0
      have h := Matrix.conjTranspose_mul_self_eq_zero.mp h0
      have hC : C - A * (Hi * (Aᴴ * C)) = 0 := by
        rw [← h]
        simp only [Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_assoc]
      exact sub_eq_zero.mp hC
    · intro h
      have hz : ((1 : Matrix y y ℂ) - A * Hi * Aᴴ) * C
          = 0 := by
        have hAcan : (A * Hi * Aᴴ) * C = C := by
          calc (A * Hi * Aᴴ) * C
              = A * (Hi * (Aᴴ * C)) := by
                simp only [Matrix.mul_assoc]
            _ = C := h.symm
        rw [Matrix.sub_mul, Matrix.one_mul, hAcan,
          sub_self]
      rw [hz, Matrix.conjTranspose_zero, Matrix.mul_zero]
  · intro h
    conv_lhs => rw [h]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      Matrix.conjTranspose_conjTranspose]
  · intro c hc h
    refine ⟨?_, ?_⟩
    · rw [h, hc, Matrix.mul_smul, Matrix.mul_one]
    · rw [h, hc, Matrix.mul_smul, Matrix.mul_one,
        Matrix.conjTranspose_smul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul]
      rfl

end NCG
