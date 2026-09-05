/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Conditional-source variance, return coherence loss, open
  currents, and fusion Pythagoras
  (`thm:GT-source-record-variance`,
  `thm:GT-return-coherence-loss`, `thm:GT-open-current`,
  `thm:GT-dynamic-fusion`,
  `thm:GT-complete-connected-sector`,
  Gran-Tensor manuscript)

* `gt_source_record_variance`: the boxed exact
  between/within split (matrix law of total variance):
  against any block centering whose weighted cross terms
  vanish (as they do for partition means),
  `∑ν_ω S_ω*S_ω = ∑ν_B S̄_B*S̄_B + ∑∑ν_ω(S_ω-S̄)*(S_ω-S̄)`.

* `gt_return_coherence_loss`: the boxed second-moment
  identity `𝔼‖x_j - Ux_i‖² = ‖x_j - Cx_i‖²
  + ⟨x_i,(I-C*C)x_i⟩` in weighted-average matrix form:
  with mean `C = ∑w_e U_e` and unit weights, the average
  Gram of the differences equals the coherent Gram plus the
  boxed coherence-loss form.

* `gt_open_current`: the boxed open-path compiler — the
  partial-sum current `j_k = -∑_{r≤k}s_r` solves the
  discrete divergence equation, the equation forces the
  formula (uniqueness), and solvability at the terminal
  vertex is exactly the vanishing of the total source.

* `gt_dynamic_fusion`: the boxed Pythagoras of the dynamic
  fusion residual for an isometric fusion.

* `gt_complete_connected_sector`: the boxed complete
  all-support projection `C_t = UQU* + (I-UU*)` is a
  hermitian idempotent orthogonal to every proper-subset
  product source `UΠU*` with `QΠ = 0`.
-/

open Matrix Finset

set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false
set_option linter.unnecessarySeqFocus false

namespace NCG

/-- `thm:GT-source-record-variance`. -/
theorem gt_source_record_variance {Ω E Y : Type}
    [Fintype Ω] [Fintype E] [Fintype Y]
    (ν : Ω → ℂ) (S Sbar : Ω → Matrix Y E ℂ)
    (hcross1 : ∑ ω, ν ω
      • ((S ω - Sbar ω)ᴴ * Sbar ω) = 0)
    (hcross2 : ∑ ω, ν ω
      • ((Sbar ω)ᴴ * (S ω - Sbar ω)) = 0) :
    ∑ ω, ν ω • ((S ω)ᴴ * S ω)
      = (∑ ω, ν ω • ((Sbar ω)ᴴ * Sbar ω))
        + ∑ ω, ν ω
          • ((S ω - Sbar ω)ᴴ * (S ω - Sbar ω)) := by
  have hterm : ∀ ω : Ω, (S ω)ᴴ * S ω
      = (Sbar ω)ᴴ * Sbar ω
        + (Sbar ω)ᴴ * (S ω - Sbar ω)
        + (S ω - Sbar ω)ᴴ * Sbar ω
        + (S ω - Sbar ω)ᴴ * (S ω - Sbar ω) := by
    intro ω
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul,
      Matrix.mul_sub]
    abel
  calc ∑ ω, ν ω • ((S ω)ᴴ * S ω)
      = ∑ ω, (ν ω • ((Sbar ω)ᴴ * Sbar ω)
        + ν ω • ((Sbar ω)ᴴ * (S ω - Sbar ω))
        + ν ω • ((S ω - Sbar ω)ᴴ * Sbar ω)
        + ν ω • ((S ω - Sbar ω)ᴴ * (S ω - Sbar ω))) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [hterm ω]
        simp only [smul_add]
    _ = (∑ ω, ν ω • ((Sbar ω)ᴴ * Sbar ω))
        + (∑ ω, ν ω • ((Sbar ω)ᴴ * (S ω - Sbar ω)))
        + (∑ ω, ν ω • ((S ω - Sbar ω)ᴴ * Sbar ω))
        + ∑ ω, ν ω
          • ((S ω - Sbar ω)ᴴ * (S ω - Sbar ω)) := by
        simp only [Finset.sum_add_distrib]
    _ = _ := by
        rw [hcross1, hcross2]
        abel

/-- `thm:GT-return-coherence-loss` (weighted matrix
form). -/
theorem gt_return_coherence_loss {ι n m : Type}
    [Fintype ι] [Fintype n] [Fintype m] [DecidableEq n]
    (w : ι → ℂ) (U : ι → Matrix n n ℂ)
    (Xi Xj : Matrix n m ℂ)
    (hw : ∑ e, w e = 1)
    (hwr : ∀ e, star (w e) = w e)
    (hC : ∀ e, (U e)ᴴ * U e = 1) :
    ∑ e, w e • ((Xj - U e * Xi)ᴴ * (Xj - U e * Xi))
      = (Xj - (∑ e, w e • U e) * Xi)ᴴ
          * (Xj - (∑ e, w e • U e) * Xi)
        + Xiᴴ * (((1 : Matrix n n ℂ)
          - (∑ e, w e • U e)ᴴ * (∑ e, w e • U e)) * Xi) := by
  set C : Matrix n n ℂ := ∑ e, w e • U e with hCdef
  have hterm : ∀ e : ι,
      w e • ((Xj - U e * Xi)ᴴ * (Xj - U e * Xi))
      = w e • (Xjᴴ * Xj)
        - Xjᴴ * ((w e • U e) * Xi)
        - ((w e • U e) * Xi)ᴴ * Xj
        + w e • (Xiᴴ * Xi) := by
    intro e
    have hexp : (Xj - U e * Xi)ᴴ * (Xj - U e * Xi)
        = Xjᴴ * Xj - Xjᴴ * (U e * Xi)
          - (U e * Xi)ᴴ * Xj + Xiᴴ * Xi := by
      simp only [Matrix.conjTranspose_sub,
        Matrix.conjTranspose_mul, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U e)ᴴ (U e) Xi, hC e,
        Matrix.one_mul]
      abel
    have hm1 : w e • (Xjᴴ * (U e * Xi))
        = Xjᴴ * ((w e • U e) * Xi) := by
      rw [← Matrix.mul_smul, ← Matrix.smul_mul]
    have hm2 : ((w e • U e) * Xi)ᴴ * Xj
        = w e • ((U e * Xi)ᴴ * Xj) := by
      rw [Matrix.smul_mul, Matrix.conjTranspose_smul,
        Matrix.smul_mul, hwr e]
    rw [hexp]
    simp only [smul_sub, smul_add]
    rw [hm1, ← hm2]
  have hsum1 : ∑ e, w e • (Xjᴴ * Xj) = Xjᴴ * Xj := by
    rw [← Finset.sum_smul, hw, one_smul]
  have hsum4 : ∑ e, w e • (Xiᴴ * Xi) = Xiᴴ * Xi := by
    rw [← Finset.sum_smul, hw, one_smul]
  have hsum2 : ∑ e, Xjᴴ * ((w e • U e) * Xi)
      = Xjᴴ * (C * Xi) := by
    rw [hCdef, Matrix.sum_mul, Matrix.mul_sum]
  have hsum3 : ∑ e, ((w e • U e) * Xi)ᴴ * Xj
      = (C * Xi)ᴴ * Xj := by
    have h : ∀ e : ι, ((w e • U e) * Xi)ᴴ * Xj
        = Xiᴴ * ((w e • U e)ᴴ * Xj) := by
      intro e
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun e _ => h e,
      ← Matrix.mul_sum, ← Matrix.sum_mul,
      ← Matrix.conjTranspose_sum, ← hCdef,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  calc ∑ e, w e • ((Xj - U e * Xi)ᴴ * (Xj - U e * Xi))
      = ∑ e, (w e • (Xjᴴ * Xj)
        - Xjᴴ * ((w e • U e) * Xi)
        - ((w e • U e) * Xi)ᴴ * Xj
        + w e • (Xiᴴ * Xi)) :=
        Finset.sum_congr rfl fun e _ => hterm e
    _ = (Xjᴴ * Xj) - Xjᴴ * (C * Xi) - (C * Xi)ᴴ * Xj
        + Xiᴴ * Xi := by
        simp only [Finset.sum_add_distrib,
          Finset.sum_sub_distrib]
        rw [hsum1, hsum2, hsum3, hsum4]
    _ = _ := by
        simp only [Matrix.conjTranspose_sub,
          Matrix.conjTranspose_mul, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
          Matrix.mul_assoc]
        abel

/-- `thm:GT-open-current`. -/
theorem gt_open_current (N : ℕ) (hN : 1 ≤ N)
    (s : ℕ → ℝ) :
    -- the boxed partial-sum current
    (-(-(∑ r ∈ Finset.range (0 + 1), s r)) = s 0)
    -- interior divergence equations
    ∧ (∀ k, 1 ≤ k →
        (-(∑ r ∈ Finset.range ((k - 1) + 1), s r))
          - (-(∑ r ∈ Finset.range (k + 1), s r)) = s k)
    -- uniqueness: the equations force the formula
    ∧ (∀ j' : ℕ → ℝ, -(j' 0) = s 0 →
        (∀ k, 1 ≤ k → j' (k - 1) - j' k = s k) →
        ∀ k, j' k = -(∑ r ∈ Finset.range (k + 1), s r))
    -- terminal solvability ⟺ zero total source
    ∧ ((-(∑ r ∈ Finset.range ((N - 1) + 1), s r)) = s N
        ↔ ∑ r ∈ Finset.range (N + 1), s r = 0) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 :=
      ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ (n := k' + 1)]
    ring
  · intro j' h0 hrec k
    induction k with
    | zero => simp [← h0]
    | succ k ih =>
      have h := hrec (k + 1) (Nat.le_add_left 1 k)
      rw [Nat.add_sub_cancel] at h
      have : j' (k + 1) = j' k - s (k + 1) := by
        linarith
      rw [this, ih, Finset.sum_range_succ (n := k + 1)]
      ring
  · obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 :=
      ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ (n := N' + 1)]
    constructor
    · intro h
      linarith
    · intro h
      linarith

/-- `thm:GT-dynamic-fusion` (the boxed residual
Pythagoras). -/
theorem gt_dynamic_fusion {a b m : Type} [Fintype a]
    [Fintype b] [Fintype m] [DecidableEq a]
    [DecidableEq b]
    (Γ : Matrix a b ℂ) (R : Matrix a m ℂ)
    (hΓ : Γᴴ * Γ = 1) :
    Rᴴ * R = (Γᴴ * R)ᴴ * (Γᴴ * R)
      + (((1 : Matrix a a ℂ) - Γ * Γᴴ) * R)ᴴ
        * (((1 : Matrix a a ℂ) - Γ * Γᴴ) * R) := by
  have hP2 : (Γ * Γᴴ) * (Γ * Γᴴ) = Γ * Γᴴ := by
    calc (Γ * Γᴴ) * (Γ * Γᴴ)
        = Γ * ((Γᴴ * Γ) * Γᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = Γ * Γᴴ := by rw [hΓ, Matrix.one_mul]
  have h1 : (Γᴴ * R)ᴴ * (Γᴴ * R)
      = Rᴴ * ((Γ * Γᴴ) * R) := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have h2 : (((1 : Matrix a a ℂ) - Γ * Γᴴ) * R)ᴴ
      * (((1 : Matrix a a ℂ) - Γ * Γᴴ) * R)
      = Rᴴ * (((1 : Matrix a a ℂ) - Γ * Γᴴ) * R) := by
    have hQH : ((1 : Matrix a a ℂ) - Γ * Γᴴ)ᴴ
        = 1 - Γ * Γᴴ := by
      rw [Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one,
        Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    have hQ2 : ((1 : Matrix a a ℂ) - Γ * Γᴴ)
        * (1 - Γ * Γᴴ) = 1 - Γ * Γᴴ := by
      simp only [Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, hP2]
      abel
    rw [Matrix.conjTranspose_mul, hQH, Matrix.mul_assoc,
      ← Matrix.mul_assoc ((1 : Matrix a a ℂ) - Γ * Γᴴ),
      hQ2]
  rw [h1, h2]
  simp only [Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul]
  abel

/-- `thm:GT-complete-connected-sector`. -/
theorem gt_complete_connected_sector {a b : Type}
    [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b]
    (U : Matrix a b ℂ) (Q Pj : Matrix b b ℂ)
    (hU : Uᴴ * U = 1) (hQH : Qᴴ = Q) (hQ2 : Q * Q = Q) :
    let Ct := U * Q * Uᴴ + ((1 : Matrix a a ℂ) - U * Uᴴ)
    -- hermitian
    (Ctᴴ = Ct)
    -- idempotent
    ∧ (Ct * Ct = Ct)
    -- kills every shorted proper-subset product source
    ∧ (Q * Pj = 0 → Ct * (U * Pj * Uᴴ) = 0) := by
  intro Ct
  have hcanU : ∀ {p : Type} [Fintype p]
      (Z : Matrix b p ℂ), Uᴴ * (U * Z) = Z := by
    intro p _ Z
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Ct, Matrix.conjTranspose_add,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_one, hQH,
      Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  · simp only [Ct, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, hcanU]
    rw [← Matrix.mul_assoc Q Q Uᴴ, hQ2]
    abel
  · intro hQPj
    simp only [Ct, Matrix.add_mul, Matrix.sub_mul,
      Matrix.one_mul, Matrix.mul_assoc, hcanU]
    rw [← Matrix.mul_assoc Q Pj Uᴴ, hQPj,
      Matrix.zero_mul, Matrix.mul_zero]
    abel

end NCG
