/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteRecurrenceAndPredictiveCarriers

/-!
# Assembly before return, rectangular interchange, stopping-front tightness

Exact finite-dimensional proofs of three Gran-Tensor records.

## `thm:GT-assembly-before-return-positivity`
* `posPart_sum_defect` (ER.19): for real signed rows
  `∑ (j a)₊ - (∑ j a)₊ = ½(∑ |j a| - |∑ j a|) ≥ 0`;
* `firstReturn_interface_expansion` (ER.20): `B D^{n-2} B^* = ∑_{a,b} B_a D^{n-2} B_b^*`;
* `firstReturn_cross_terms_cancel` / `_reinforce`: explicit interfaces whose
  first-return kernel is strictly below / above the sum of the diagonal
  channel kernels.

## `thm:GT-rectangular-interchange`
* `future_first_decomposition` / `context_first_decomposition` (PA.7/PA.8);
* `interchange_secant` (PA.9); the ledger difference (PA.10) is
  `FiniteRecurrenceAndPredictiveCarriers.reveal_order_ledger_difference`
  and the curvature Gram (PA.11) is `rectangular_curvature`;
* `commuting_projections_four_range`: commuting orthogonal projections split
  the identity into four mutually orthogonal projections (common,
  future-only, context-only, mixed).

## `thm:GT-stopping-front-tightness`
* `stopping_front_tail_operator` (PA.14 ⇒ PA.15) in Loewner order for
  conjugated graded projections;
* `uniform_tightness_failure_witnesses`: failure of uniform tightness yields,
  beyond every front, a cutoff and a unit coefficient carrying a fixed
  positive mass, and `three_component_pigeonhole` localizes it in one of the
  three frontier components.
-/

open Finset Matrix
open scoped ComplexOrder

namespace NCG
namespace AssemblyRectangularStoppingFront

/-! ### Assembly before return -/

/-- Positive part `x₊ = max x 0`. -/
def posPart (x : ℝ) : ℝ := max x 0

theorem posPart_eq (x : ℝ) : posPart x = (x + |x|) / 2 := by
  unfold posPart
  rcases le_or_gt 0 x with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h.le, abs_of_neg h]; ring

/-- **(ER.19)**: assembling signed rows before taking positive parts loses
exactly half the total-variation defect, which is nonnegative. -/
theorem posPart_sum_defect {ι : Type*} (s : Finset ι) (j : ι → ℝ) :
    (∑ a ∈ s, posPart (j a)) - posPart (∑ a ∈ s, j a)
        = (1 / 2) * ((∑ a ∈ s, |j a|) - |∑ a ∈ s, j a|) ∧
      0 ≤ (∑ a ∈ s, posPart (j a)) - posPart (∑ a ∈ s, j a) := by
  have hid : (∑ a ∈ s, posPart (j a)) - posPart (∑ a ∈ s, j a)
      = (1 / 2) * ((∑ a ∈ s, |j a|) - |∑ a ∈ s, j a|) := by
    simp only [posPart_eq]
    have : ∑ x ∈ s, (j x + |j x|) / 2 = (∑ x ∈ s, j x + ∑ x ∈ s, |j x|) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
    rw [this]
    ring
  refine ⟨hid, ?_⟩
  rw [hid]
  have := Finset.abs_sum_le_sum_abs j s
  linarith

/-- **(ER.20)**: the physical first-return kernel of an assembled interface
is the full double sum over channel pairs. -/
theorem firstReturn_interface_expansion {ι m n : Type*} [Fintype n]
    [DecidableEq n] (s : Finset ι) (B : ι → Matrix m n ℂ) (D : Matrix n n ℂ) (k : ℕ) :
    (∑ a ∈ s, B a) * D ^ k * (∑ a ∈ s, B a)ᴴ
      = ∑ a ∈ s, ∑ b ∈ s, B a * D ^ k * (B b)ᴴ := by
  rw [conjTranspose_sum, Matrix.mul_sum]
  simp only [Matrix.sum_mul]
  rw [Finset.sum_comm]

/-- Cross terms may **cancel**: two opposite channels have zero assembled
return but positive diagonal channel kernels. -/
theorem firstReturn_cross_terms_cancel :
    ∃ B : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ,
      (∑ a, B a) * (∑ a, B a)ᴴ = 0 ∧ ∑ a, B a * (B a)ᴴ ≠ 0 := by
  refine ⟨![1, -1], ?_, ?_⟩
  · simp [Fin.sum_univ_two]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [Fin.sum_univ_two] at this

/-- Cross terms may **reinforce**: two equal channels return four times the
single channel kernel, twice the diagonal sum. -/
theorem firstReturn_cross_terms_reinforce :
    ∃ B : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ,
      (∑ a, B a) * (∑ a, B a)ᴴ = (2 : ℂ) • ∑ a, B a * (B a)ᴴ ∧
        ∑ a, B a * (B a)ᴴ ≠ 0 := by
  refine ⟨![1, 1], ?_, ?_⟩
  · ext i j
    fin_cases i; fin_cases j
    simp [Fin.sum_univ_two, Matrix.mul_apply]
    norm_num
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [Fin.sum_univ_two] at this

/-! ### Rectangular interchange -/

section Rectangular

variable {A : Type*} [AddCommGroup A]

/-- The genuinely mixed corner `E_M = P_□ - P_∨` (PA.6). -/
def mixedCorner (square join : A) : A := square - join

/-- **(PA.7)** future-first decomposition. -/
theorem future_first_decomposition (base future join square : A) :
    square - base = (future - base) + (join - future) + mixedCorner square join := by
  unfold mixedCorner; abel

/-- **(PA.8)** context-first decomposition. -/
theorem context_first_decomposition (base context join square : A) :
    square - base = (context - base) + (join - context) + mixedCorner square join := by
  unfold mixedCorner; abel

/-- The signed interchange secant `Ω_□ = P_F + P_C - P_0 - P_∨` (PA.9). -/
def interchangeSecant (base future context join : A) : A :=
  future + context - base - join

/-- **(PA.9)**: the secant is the difference of the two marginal increments
`(P_F - P_0) - (P_∨ - P_C)`, equivalently `(P_C - P_0) - (P_∨ - P_F)`. -/
theorem interchange_secant (base future context join : A) :
    interchangeSecant base future context join = (future - base) - (join - context) ∧
      interchangeSecant base future context join = (context - base) - (join - future) := by
  unfold interchangeSecant; constructor <;> abel

end Rectangular

/-- An orthogonal projection: Hermitian and idempotent. -/
def IsOrthProj {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) : Prop :=
  Pᴴ = P ∧ P * P = P

/-- **Four-range split**: commuting orthogonal projections `P, Q` give four
mutually orthogonal projections `PQ, P(1-Q), (1-P)Q, (1-P)(1-Q)` summing to
the identity (common / future-only / context-only / mixed). -/
theorem commuting_projections_four_range {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℂ) (hP : IsOrthProj P) (hQ : IsOrthProj Q) (hc : P * Q = Q * P) :
    let R : Fin 4 → Matrix n n ℂ :=
      ![P * Q, P * (1 - Q), (1 - P) * Q, (1 - P) * (1 - Q)]
    (∀ i, IsOrthProj (R i)) ∧ (∀ i j, i ≠ j → R i * R j = 0) ∧ ∑ i, R i = 1 := by
  intro R
  obtain ⟨hPH, hPP⟩ := hP
  obtain ⟨hQH, hQQ⟩ := hQ
  have hc' : (1 - P) * Q = Q * (1 - P) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc]
  have hPQ' : P * (1 - Q) = (1 - Q) * P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc]
  have hc'' : (1 - P) * (1 - Q) = (1 - Q) * (1 - P) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc]
    abel
  have hP' : (1 - P) * (1 - P) = 1 - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hPP]; abel
  have hQ' : (1 - Q) * (1 - Q) = 1 - Q := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hQQ]; abel
  have hPz : P * (1 - P) = 0 := by
    simp only [mul_sub, mul_one, hPP, sub_self]
  have hQz : Q * (1 - Q) = 0 := by
    simp only [mul_sub, mul_one, hQQ, sub_self]
  have hPz' : (1 - P) * P = 0 := by
    simp only [sub_mul, one_mul, hPP, sub_self]
  have hQz' : (1 - Q) * Q = 0 := by
    simp only [sub_mul, one_mul, hQQ, sub_self]
  have hPH' : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hPH]
  have hQH' : (1 - Q)ᴴ = 1 - Q := by rw [conjTranspose_sub, conjTranspose_one, hQH]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · refine ⟨?_, ?_⟩
      · change (P * Q)ᴴ = P * Q
        rw [conjTranspose_mul, hPH, hQH, hc]
      · change P * Q * (P * Q) = P * Q
        calc P * Q * (P * Q) = P * (Q * P) * Q := by simp only [Matrix.mul_assoc]
          _ = P * (P * Q) * Q := by rw [hc]
          _ = (P * P) * (Q * Q) := by simp only [Matrix.mul_assoc]
          _ = P * Q := by rw [hPP, hQQ]
    · refine ⟨?_, ?_⟩
      · change (P * (1 - Q))ᴴ = P * (1 - Q)
        rw [conjTranspose_mul, hPH, hQH', hPQ']
      · change P * (1 - Q) * (P * (1 - Q)) = P * (1 - Q)
        calc P * (1 - Q) * (P * (1 - Q)) = P * ((1 - Q) * P) * (1 - Q) := by
              simp only [Matrix.mul_assoc]
          _ = P * (P * (1 - Q)) * (1 - Q) := by rw [hPQ']
          _ = (P * P) * ((1 - Q) * (1 - Q)) := by simp only [Matrix.mul_assoc]
          _ = P * (1 - Q) := by rw [hPP, hQ']
    · refine ⟨?_, ?_⟩
      · change ((1 - P) * Q)ᴴ = (1 - P) * Q
        rw [conjTranspose_mul, hPH', hQH, hc']
      · change (1 - P) * Q * ((1 - P) * Q) = (1 - P) * Q
        calc (1 - P) * Q * ((1 - P) * Q) = (1 - P) * (Q * (1 - P)) * Q := by
              simp only [Matrix.mul_assoc]
          _ = (1 - P) * ((1 - P) * Q) * Q := by rw [hc']
          _ = ((1 - P) * (1 - P)) * (Q * Q) := by simp only [Matrix.mul_assoc]
          _ = (1 - P) * Q := by rw [hP', hQQ]
    · refine ⟨?_, ?_⟩
      · change ((1 - P) * (1 - Q))ᴴ = (1 - P) * (1 - Q)
        rw [conjTranspose_mul, hPH', hQH', hc'']
      · change (1 - P) * (1 - Q) * ((1 - P) * (1 - Q)) = (1 - P) * (1 - Q)
        calc (1 - P) * (1 - Q) * ((1 - P) * (1 - Q))
            = (1 - P) * ((1 - Q) * (1 - P)) * (1 - Q) := by simp only [Matrix.mul_assoc]
          _ = (1 - P) * ((1 - P) * (1 - Q)) * (1 - Q) := by rw [hc'']
          _ = ((1 - P) * (1 - P)) * ((1 - Q) * (1 - Q)) := by simp only [Matrix.mul_assoc]
          _ = (1 - P) * (1 - Q) := by rw [hP', hQ']
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | skip
    -- the twelve off-diagonal products
    · change P * Q * (P * (1 - Q)) = 0
      calc P * Q * (P * (1 - Q)) = P * (Q * P) * (1 - Q) := by simp only [Matrix.mul_assoc]
        _ = (P * P) * (Q * (1 - Q)) := by rw [← hc]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hQz, Matrix.mul_zero]
    · change P * Q * ((1 - P) * Q) = 0
      calc P * Q * ((1 - P) * Q) = P * (Q * (1 - P)) * Q := by simp only [Matrix.mul_assoc]
        _ = (P * (1 - P)) * (Q * Q) := by rw [← hc']; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPz, Matrix.zero_mul]
    · change P * Q * ((1 - P) * (1 - Q)) = 0
      calc P * Q * ((1 - P) * (1 - Q)) = P * (Q * (1 - P)) * (1 - Q) := by
            simp only [Matrix.mul_assoc]
        _ = (P * (1 - P)) * (Q * (1 - Q)) := by rw [← hc']; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPz, Matrix.zero_mul]
    · change P * (1 - Q) * (P * Q) = 0
      calc P * (1 - Q) * (P * Q) = P * ((1 - Q) * P) * Q := by simp only [Matrix.mul_assoc]
        _ = (P * P) * ((1 - Q) * Q) := by rw [← hPQ']; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hQz', Matrix.mul_zero]
    · change P * (1 - Q) * ((1 - P) * Q) = 0
      calc P * (1 - Q) * ((1 - P) * Q) = P * ((1 - Q) * (1 - P)) * Q := by
            simp only [Matrix.mul_assoc]
        _ = (P * (1 - P)) * ((1 - Q) * Q) := by rw [← hc'']; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPz, Matrix.zero_mul]
    · change P * (1 - Q) * ((1 - P) * (1 - Q)) = 0
      calc P * (1 - Q) * ((1 - P) * (1 - Q)) = P * ((1 - Q) * (1 - P)) * (1 - Q) := by
            simp only [Matrix.mul_assoc]
        _ = (P * (1 - P)) * ((1 - Q) * (1 - Q)) := by
            rw [← hc'']; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPz, Matrix.zero_mul]
    · change (1 - P) * Q * (P * Q) = 0
      calc (1 - P) * Q * (P * Q) = (1 - P) * (Q * P) * Q := by simp only [Matrix.mul_assoc]
        _ = ((1 - P) * P) * (Q * Q) := by rw [← hc]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPz', Matrix.zero_mul]
    · change (1 - P) * Q * (P * (1 - Q)) = 0
      calc (1 - P) * Q * (P * (1 - Q)) = (1 - P) * (Q * P) * (1 - Q) := by
            simp only [Matrix.mul_assoc]
        _ = ((1 - P) * P) * (Q * (1 - Q)) := by rw [← hc]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPz', Matrix.zero_mul]
    · change (1 - P) * Q * ((1 - P) * (1 - Q)) = 0
      calc (1 - P) * Q * ((1 - P) * (1 - Q)) = (1 - P) * (Q * (1 - P)) * (1 - Q) := by
            simp only [Matrix.mul_assoc]
        _ = ((1 - P) * (1 - P)) * (Q * (1 - Q)) := by
            rw [← hc']; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hQz, Matrix.mul_zero]
    · change (1 - P) * (1 - Q) * (P * Q) = 0
      calc (1 - P) * (1 - Q) * (P * Q) = (1 - P) * ((1 - Q) * P) * Q := by
            simp only [Matrix.mul_assoc]
        _ = ((1 - P) * P) * ((1 - Q) * Q) := by rw [← hPQ']; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPz', Matrix.zero_mul]
    · change (1 - P) * (1 - Q) * (P * (1 - Q)) = 0
      calc (1 - P) * (1 - Q) * (P * (1 - Q)) = (1 - P) * ((1 - Q) * P) * (1 - Q) := by
            simp only [Matrix.mul_assoc]
        _ = ((1 - P) * P) * ((1 - Q) * (1 - Q)) := by
            rw [← hPQ']; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPz', Matrix.zero_mul]
    · change (1 - P) * (1 - Q) * ((1 - P) * Q) = 0
      calc (1 - P) * (1 - Q) * ((1 - P) * Q) = (1 - P) * ((1 - Q) * (1 - P)) * Q := by
            simp only [Matrix.mul_assoc]
        _ = ((1 - P) * (1 - P)) * ((1 - Q) * Q) := by
            rw [← hc'']; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hQz', Matrix.mul_zero]
  · rw [Fin.sum_univ_four]
    change P * Q + P * (1 - Q) + (1 - P) * Q + (1 - P) * (1 - Q) = 1
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    abel

/-! ### Stopping-front tightness -/

section StoppingFront

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]

set_option linter.unusedFintypeInType false in
/-- **(PA.14 ⇒ PA.15)**, operator form.  If the weighted graded sum of the
conjugated projections is dominated by `C·I` and the weights are
nondecreasing beyond the front `R`, then the tail beyond `R` is dominated by
`(C / w_{R+1})·I` in Loewner order. -/
theorem stopping_front_tail_operator
    (S : Matrix n m ℂ) (E : ℕ → Matrix n n ℂ) (hE : ∀ k, (E k).PosSemidef)
    (w : ℕ → ℝ) (N R : ℕ) (C : ℝ)
    (hwNonneg : ∀ k, 0 ≤ w k)
    (hwMono : ∀ k, R < k → k < N → w (R + 1) ≤ w k)
    (hwPos : 0 < w (R + 1))
    (hbound : ((C : ℂ) • (1 : Matrix m m ℂ)
      - ∑ k ∈ Finset.range N, (w k : ℂ) • (Sᴴ * E k * S)).PosSemidef) :
    (((C / w (R + 1) : ℝ) : ℂ) • (1 : Matrix m m ℂ)
      - ∑ k ∈ (Finset.range N).filter (fun k => R < k), Sᴴ * E k * S).PosSemidef := by
  set M : ℕ → Matrix m m ℂ := fun k => Sᴴ * E k * S with hM
  have hMpsd : ∀ k, (M k).PosSemidef := fun k => (hE k).conjTranspose_mul_mul_same S
  set T := (Finset.range N).filter (fun k => R < k) with hT
  -- (i) the excess weights beyond the front
  have h1 : (∑ k ∈ T, ((w k - w (R + 1) : ℝ) : ℂ) • M k).PosSemidef := by
    refine Matrix.posSemidef_sum _ fun k hk => ?_
    have hk' := (Finset.mem_filter.mp hk)
    have := hwMono k hk'.2 (Finset.mem_range.mp hk'.1)
    have hnn : (0 : ℂ) ≤ ((w k - w (R + 1) : ℝ) : ℂ) := by
      rw [Complex.zero_le_real]; linarith
    exact (hMpsd k).smul hnn
  -- (ii) the head of the weighted sum
  have h2 : (∑ k ∈ (Finset.range N).filter (fun k => ¬ R < k),
      (w k : ℂ) • M k).PosSemidef := by
    refine Matrix.posSemidef_sum _ fun k _ => ?_
    have hnn : (0 : ℂ) ≤ (w k : ℂ) := by
      rw [Complex.zero_le_real]; exact hwNonneg k
    exact (hMpsd k).smul hnn
  -- assemble: (i) + (ii) + hypothesis = C·I - w_{R+1}·tail
  have hsplit : (∑ k ∈ Finset.range N, (w k : ℂ) • M k)
      = (∑ k ∈ T, (w k : ℂ) • M k)
        + ∑ k ∈ (Finset.range N).filter (fun k => ¬ R < k), (w k : ℂ) • M k := by
    rw [hT, Finset.sum_filter_add_sum_filter_not]
  have hkey : (C : ℂ) • (1 : Matrix m m ℂ) - ((w (R + 1) : ℝ) : ℂ) • ∑ k ∈ T, M k
      = (∑ k ∈ T, ((w k - w (R + 1) : ℝ) : ℂ) • M k)
        + (∑ k ∈ (Finset.range N).filter (fun k => ¬ R < k), (w k : ℂ) • M k)
        + ((C : ℂ) • (1 : Matrix m m ℂ) - ∑ k ∈ Finset.range N, (w k : ℂ) • M k) := by
    rw [hsplit, Finset.smul_sum]
    have : ∀ k ∈ T, ((w k - w (R + 1) : ℝ) : ℂ) • M k
        = (w k : ℂ) • M k - ((w (R + 1) : ℝ) : ℂ) • M k := by
      intro k _
      rw [Complex.ofReal_sub, sub_smul]
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
    abel
  have hw : ((C : ℂ) • (1 : Matrix m m ℂ) - ((w (R + 1) : ℝ) : ℂ) • ∑ k ∈ T, M k).PosSemidef := by
    rw [hkey]
    exact (h1.add h2).add hbound
  -- rescale by `1 / w_{R+1}`
  have hinv : (0 : ℂ) ≤ (((w (R + 1))⁻¹ : ℝ) : ℂ) := by
    rw [Complex.zero_le_real]; positivity
  have := hw.smul hinv
  have hfinal : (((w (R + 1))⁻¹ : ℝ) : ℂ) •
      ((C : ℂ) • (1 : Matrix m m ℂ) - ((w (R + 1) : ℝ) : ℂ) • ∑ k ∈ T, M k)
      = ((C / w (R + 1) : ℝ) : ℂ) • (1 : Matrix m m ℂ) - ∑ k ∈ T, M k := by
    rw [smul_sub, smul_smul, smul_smul]
    have hne : (w (R + 1) : ℂ) ≠ 0 := by exact_mod_cast hwPos.ne'
    have : (((w (R + 1))⁻¹ : ℝ) : ℂ) * ((w (R + 1) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_inv]; exact inv_mul_cancel₀ hne
    rw [this, one_smul]
    congr 1
    rw [Complex.ofReal_div, div_eq_inv_mul, Complex.ofReal_inv]
  rw [hfinal] at this
  exact this

/-- The scalar tail bound used along one unit coefficient is
`FiniteRecurrenceAndPredictiveCarriers.weighted_stopping_front_tail`; the
operator statement above is its Loewner form. -/
theorem stopping_front_tail_scalar
    (weight mass : ℕ → ℝ) (N R : ℕ) (C : ℝ) (hR : R + 1 < N)
    (hmass : ∀ k, 0 ≤ mass k) (hweightNonneg : ∀ k, 0 ≤ weight k)
    (hweight : ∀ k, R < k → k < N → weight (R + 1) ≤ weight k)
    (hweighted : (Finset.range N).sum (fun k => weight k * mass k) ≤ C)
    (hweightPos : 0 < weight (R + 1)) :
    ((Finset.range N).filter (fun k => R < k)).sum mass ≤ C / weight (R + 1) :=
  FiniteRecurrenceAndPredictiveCarriers.weighted_stopping_front_tail weight mass N R C hR
    hmass hweightNonneg hweight hweighted hweightPos

/-- **Failure of uniform tightness** (indexed by cutoffs `X` and unit
coefficients `x`): if no front captures the tail mass `τ X R x` uniformly,
then some fixed `ε > 0` survives beyond every front for a suitable cutoff and
unit coefficient. -/
theorem uniform_tightness_failure_witnesses {Cut Coef : Type*}
    (τ : Cut → ℕ → Coef → ℝ)
    (hfail : ¬ ∀ ε > (0 : ℝ), ∃ R : ℕ, ∀ X x, τ X R x ≤ ε) :
    ∃ ε > (0 : ℝ), ∀ R : ℕ, ∃ X x, ε < τ X R x := by
  push Not at hfail
  obtain ⟨ε, hε, h⟩ := hfail
  exact ⟨ε, hε, fun R => h R⟩

/-- A front of growing grades: the witnesses can be chosen with `R_k = k`,
hence `R_k → ∞`. -/
theorem uniform_tightness_failure_sequence {Cut Coef : Type*}
    (τ : Cut → ℕ → Coef → ℝ)
    (hfail : ¬ ∀ ε > (0 : ℝ), ∃ R : ℕ, ∀ X x, τ X R x ≤ ε) :
    ∃ ε > (0 : ℝ), ∃ (X : ℕ → Cut) (x : ℕ → Coef), ∀ k, ε < τ (X k) k (x k) := by
  obtain ⟨ε, hε, h⟩ := uniform_tightness_failure_witnesses τ hfail
  choose X x hx using h
  exact ⟨ε, hε, X, x, hx⟩

/-- **Three-component pigeonhole**: a surviving tail mass split into
future-only, context-only, and mixed frontier components has one component
carrying at least a third of it. -/
theorem three_component_pigeonhole (a b c ε : ℝ)
    (h : ε < a + b + c) : ε / 3 < a ∨ ε / 3 < b ∨ ε / 3 < c := by
  by_contra hcon
  push Not at hcon
  linarith [hcon.1, hcon.2.1, hcon.2.2]

end StoppingFront

end AssemblyRectangularStoppingFront
end NCG
