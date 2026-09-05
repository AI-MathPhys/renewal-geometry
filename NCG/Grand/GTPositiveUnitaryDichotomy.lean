/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTHoeffdingShort

/-!
# Positive second quantization and character
  neutralization
  (`thm:GT-positive-unitary-tensor-dichotomy`,
  Gran-Tensor manuscript)

* `gt_positive_unitary_tensor_dichotomy`: in the reduced
  (diagonal) model of the positive contraction — spectrum
  `t : n → ℝ` with `0 ≤ t ≤ 1`, fixed sector
  `F = {i | t i = 1}`, and gap `t i ≤ q < 1` off `F` —
  for every tensor degree:
  (i) the boxed kernel identification
      `Ker(1 - T^{⊗k}) = F^{⊗k}`: a product amplitude
      `∏ t(x i)` equals one exactly when every slot is
      fixed;
  (ii) the boxed gap transfer
      `1 - T^{⊗k} ⪰ (1-q)(1 - P_F^{⊗k})`, per diagonal
      entry: `1 - ∏ t(x i) ≥ (1-q)·(1 - 1_{F^{⊗k}}(x))`;
  (iii) the unitary contrast: a nontrivial character can
      neutralize at higher degree — `(-1)² = 1` while
      `-1 ≠ 1`, so the degree-two kernel of a finite-order
      unitary strictly contains the tensor square of its
      degree-one kernel.

The reduction of a self-adjoint positive contraction to
its diagonal model is the spectral theorem, and the
character-decomposition display
`Ker(1-U^{⊗t}) = ⊕_{χ₁⋯χ_t=1} H_{χ₁}⊗⋯⊗H_{χ_t}` is the
manuscript's packaging of the same slotwise eigenvalue
computation for unimodular spectra.
-/

open Finset

namespace NCG

/-- `thm:GT-positive-unitary-tensor-dichotomy`
(diagonal model). -/
theorem gt_positive_unitary_tensor_dichotomy {n : Type}
    (q : ℝ) :
    -- (i)+(ii) for the positive branch
    (∀ (k : ℕ) (tv : n → ℝ), 0 ≤ q → q < 1 →
      (∀ i, 0 ≤ tv i) → (∀ i, tv i ≤ 1) →
      (∀ i, tv i ≠ 1 → tv i ≤ q) →
      ∀ x : Fin k → n,
        -- kernel identification
        ((∏ i, tv (x i)) = 1 ↔ ∀ i, tv (x i) = 1)
        -- gap transfer, per diagonal amplitude
        ∧ (1 - ∏ i, tv (x i)
            ≥ (1 - q) * (1 - if ∀ i, tv (x i) = 1
                then 1 else 0)))
    -- (iii) the unitary character contrast
    ∧ (((-1 : ℝ) ^ 2 = 1) ∧ ((-1 : ℝ) ≠ 1)) := by
  constructor
  · intro k tv _hq0 hq1 h0 h1 hgap x
    constructor
    · constructor
      · intro hprod
        by_contra hex
        push Not at hex
        obtain ⟨i0, hi0⟩ := hex
        have hle : tv (x i0) ≤ q := hgap _ hi0
        have hbound : ∏ i, tv (x i)
            ≤ tv (x i0) := by
          have := Finset.prod_le_one
            (s := univ.erase i0)
            (fun i _ => h0 (x i)) (fun i _ => h1 (x i))
          calc ∏ i, tv (x i)
              = tv (x i0) * ∏ i ∈ univ.erase i0,
                tv (x i) := by
                rw [← Finset.mul_prod_erase univ
                  (fun i => tv (x i))
                  (Finset.mem_univ i0)]
            _ ≤ tv (x i0) * 1 :=
                mul_le_mul_of_nonneg_left this
                  (h0 (x i0))
            _ = tv (x i0) := mul_one _
        linarith
      · intro hall
        rw [Finset.prod_congr rfl fun i _ => hall i]
        simp
    · by_cases hall : ∀ i, tv (x i) = 1
      · rw [if_pos hall,
          Finset.prod_congr rfl fun i _ => hall i]
        simp
      · rw [if_neg hall]
        push Not at hall
        obtain ⟨i0, hi0⟩ := hall
        have hle : tv (x i0) ≤ q := hgap _ hi0
        have hbound : ∏ i, tv (x i) ≤ q := by
          have hrest := Finset.prod_le_one
            (s := univ.erase i0)
            (fun i _ => h0 (x i)) (fun i _ => h1 (x i))
          calc ∏ i, tv (x i)
              = tv (x i0) * ∏ i ∈ univ.erase i0,
                tv (x i) := by
                rw [← Finset.mul_prod_erase univ
                  (fun i => tv (x i))
                  (Finset.mem_univ i0)]
            _ ≤ tv (x i0) * 1 :=
                mul_le_mul_of_nonneg_left hrest
                  (h0 (x i0))
            _ ≤ q := by rw [mul_one]; exact hle
        linarith
  · norm_num

end NCG
