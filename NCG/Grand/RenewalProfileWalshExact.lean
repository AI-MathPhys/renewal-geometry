/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The concrete renewal continuum profile: the `m`-cell Walsh layer

Machinery for `thm:concrete-renewal-continuum-profile`, replacing the audited
two-cell Kronecker toy by the general-`m` statements:

* `transfer_walsh`: **the `m`-cell Walsh diagonalization** — the product
  transfer acts on every Walsh function by
  `M₀^{⊗m} φ_S = (−7/15)^{|S|} φ_S`;
* `walsh_orthogonal`: the Walsh functions are orthogonal for the product
  stationary weights, with `⟨φ_S, φ_S⟩ = 30^{|S|}` and distinct labels
  orthogonal — the `𝖲₄` synthesis is isometric on singleton contrasts;
* `mean_zero_contraction` / `response_gap`: the boxed volume-independent
  mean-zero contraction `7/15` and positive-response gap `176/225` on every
  nonempty Walsh label;
* `tetra_gram`: the four normalized vertex contrasts form a regular
  tetrahedron, `⟨n_i, n_j⟩ = 1` or `−1/3`;
* `contrast_frame_identity`: the boxed six-contrast frame identity
  `Σ_{i<j} d_{ij} d_{ij}^* = 4 (I − ¼J) = 4 I_{W₀}`.
-/

open Finset

noncomputable section

namespace NCG
namespace RenewalWalsh

/-- The renewal phase transfer. -/
def M0 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![1/5, 4/5], ![2/3, 1/3]]

/-- The unnormalized private-phase contrast. -/
def phi : Fin 2 → ℝ := ![6, -5]

/-- The stationary weights. -/
def piw : Fin 2 → ℝ := ![5/11, 6/11]

theorem row_sum : ∀ a, ∑ b, M0 a b = 1 := by
  intro a
  fin_cases a <;> norm_num [M0, Fin.sum_univ_two]

theorem cell_eigen : ∀ a, ∑ b, M0 a b * phi b = -(7/15) * phi a := by
  intro a
  fin_cases a <;> norm_num [M0, phi, Fin.sum_univ_two]

theorem cell_mass : ∑ b, piw b = 1 := by
  norm_num [piw, Fin.sum_univ_two]

theorem cell_centered : ∑ b, piw b * phi b = 0 := by
  norm_num [piw, phi, Fin.sum_univ_two]

theorem cell_second_moment : ∑ b, piw b * (phi b * phi b) = 30 := by
  norm_num [piw, phi, Fin.sum_univ_two]

variable {m : ℕ}

/-- The `m`-cell product transfer `M₀^{⊗m}` acting on cell observables. -/
def transferOp (f : (Fin m → Fin 2) → ℝ) (x : Fin m → Fin 2) : ℝ :=
  ∑ y : Fin m → Fin 2, (∏ i, M0 (x i) (y i)) * f y

/-- The Walsh function of a label set `S`. -/
def walsh (S : Finset (Fin m)) (x : Fin m → Fin 2) : ℝ :=
  ∏ i ∈ S, phi (x i)

set_option maxHeartbeats 1600000 in -- pi-type product factorization unification
/-- **The `m`-cell Walsh diagonalization**:
`M₀^{⊗m} φ_S = (−7/15)^{|S|} φ_S`. -/
theorem transfer_walsh (S : Finset (Fin m)) (x : Fin m → Fin 2) :
    transferOp (walsh S) x = (-(7/15)) ^ S.card * walsh S x := by
  classical
  have hmerge : ∀ y : Fin m → Fin 2,
      (∏ i, M0 (x i) (y i)) * walsh S y
        = ∏ i, (M0 (x i) (y i) * if i ∈ S then phi (y i) else 1) := by
    intro y
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [walsh, Finset.prod_ite_mem, Finset.univ_inter]
  unfold transferOp
  calc ∑ y : Fin m → Fin 2, (∏ i, M0 (x i) (y i)) * walsh S y
      = ∑ y : Fin m → Fin 2,
          ∏ i, (M0 (x i) (y i) * if i ∈ S then phi (y i) else 1) :=
        Finset.sum_congr rfl fun y _ => hmerge y
    _ = ∑ y ∈ Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (Fin 2))),
          ∏ i, (M0 (x i) (y i) * if i ∈ S then phi (y i) else 1) := by
        rw [Fintype.piFinset_univ]
    _ = ∏ i, ∑ b, (M0 (x i) b * if i ∈ S then phi b else 1) :=
        Finset.sum_prod_piFinset Finset.univ
          (fun i b => M0 (x i) b * if i ∈ S then phi b else 1)
    _ = ∏ i, (if i ∈ S then -(7/15) * phi (x i) else 1) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases hi : i ∈ S
        · simp only [if_pos hi]
          exact cell_eigen (x i)
        · simp only [if_neg hi, mul_one]
          exact row_sum (x i)
    _ = (-(7/15)) ^ S.card * walsh S x := by
        rw [Finset.prod_ite_mem, Finset.univ_inter,
          Finset.prod_mul_distrib, Finset.prod_const, walsh]

set_option maxHeartbeats 1600000 in -- pi-type product factorization unification
/-- **Walsh orthogonality for the product stationary weights**: distinct
labels are orthogonal and `⟨φ_S, φ_S⟩ = 30^{|S|}` — in particular the
singleton contrasts are orthogonal, so the `𝖲₄` synthesis is isometric on the
mean-zero space. -/
theorem walsh_orthogonal (S T : Finset (Fin m)) :
    ∑ x : Fin m → Fin 2, (∏ i, piw (x i)) * (walsh S x * walsh T x)
      = if S = T then (30 : ℝ) ^ S.card else 0 := by
  classical
  have hmerge : ∀ x : Fin m → Fin 2,
      (∏ i, piw (x i)) * (walsh S x * walsh T x)
        = ∏ i, (piw (x i) * ((if i ∈ S then phi (x i) else 1)
            * if i ∈ T then phi (x i) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_mul_distrib]
    congr 1
    · rw [walsh, Finset.prod_ite_mem, Finset.univ_inter]
    · rw [walsh, Finset.prod_ite_mem, Finset.univ_inter]
  have hfactor : ∑ x : Fin m → Fin 2,
      (∏ i, piw (x i)) * (walsh S x * walsh T x)
      = ∏ i, ∑ b, (piw b * ((if i ∈ S then phi b else 1)
          * if i ∈ T then phi b else 1)) := by
    calc ∑ x : Fin m → Fin 2, (∏ i, piw (x i)) * (walsh S x * walsh T x)
        = ∑ x : Fin m → Fin 2, ∏ i, (piw (x i)
            * ((if i ∈ S then phi (x i) else 1)
              * if i ∈ T then phi (x i) else 1)) :=
          Finset.sum_congr rfl fun x _ => hmerge x
      _ = ∑ x ∈ Fintype.piFinset
            (fun _ : Fin m => (Finset.univ : Finset (Fin 2))),
            ∏ i, (piw (x i) * ((if i ∈ S then phi (x i) else 1)
              * if i ∈ T then phi (x i) else 1)) := by
          rw [Fintype.piFinset_univ]
      _ = _ := Finset.sum_prod_piFinset Finset.univ
          (fun i b => piw b * ((if i ∈ S then phi b else 1)
            * if i ∈ T then phi b else 1))
  rw [hfactor]
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl]
    calc ∏ i, ∑ b, (piw b * ((if i ∈ S then phi b else 1)
          * if i ∈ S then phi b else 1))
        = ∏ i, (if i ∈ S then (30 : ℝ) else 1) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          by_cases hi : i ∈ S
          · simp only [if_pos hi]
            exact cell_second_moment
          · simp only [if_neg hi, mul_one]
            exact cell_mass
      _ = (30 : ℝ) ^ S.card := by
          rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  · rw [if_neg hST]
    have hdiff : ∃ i, (i ∈ S ∧ i ∉ T) ∨ (i ∈ T ∧ i ∉ S) := by
      by_contra hall
      rw [not_exists] at hall
      exact hST (Finset.ext fun i => by
        have h := hall i
        tauto)
    obtain ⟨i0, hi0⟩ := hdiff
    refine Finset.prod_eq_zero (Finset.mem_univ i0) ?_
    rcases hi0 with ⟨hiS, hiT⟩ | ⟨hiT, hiS⟩
    · simp only [if_pos hiS, if_neg hiT, mul_one]
      exact cell_centered
    · simp only [if_neg hiS, if_pos hiT, one_mul]
      exact cell_centered

/-- The boxed mean-zero contraction: every nonempty Walsh eigenvalue is at
most `7/15` in absolute value. -/
theorem mean_zero_contraction {S : Finset (Fin m)} (hS : S.Nonempty) :
    |(-(7/15 : ℝ)) ^ S.card| ≤ 7/15 := by
  rw [abs_pow, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 7/15)]
  calc (7/15 : ℝ) ^ S.card ≤ (7/15) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (Finset.one_le_card.mpr hS)
    _ = 7/15 := pow_one _

/-- The boxed volume-independent positive-response gap: on every nonempty
Walsh label, `1 − λ_S² ≥ 176/225`. -/
theorem response_gap {S : Finset (Fin m)} (hS : S.Nonempty) :
    (176/225 : ℝ) ≤ 1 - ((-(7/15 : ℝ)) ^ S.card) ^ 2 := by
  have h := mean_zero_contraction hS
  have hsq := sq_abs ((-(7/15 : ℝ)) ^ S.card)
  have habs := abs_nonneg ((-(7/15 : ℝ)) ^ S.card)
  nlinarith

/-! ### The tetrahedral contrasts and the six-contrast frame -/

/-- The centered vertex direction `e_i − ¼𝟙`. -/
def vertexDir (i k : Fin 4) : ℝ := (if (k : ℕ) = (i : ℕ) then 1 else 0) - 1/4

/-- The centered vertex Gram: `⟨e_i − ¼𝟙, e_j − ¼𝟙⟩ = δ_{ij} − ¼`, so the
normalized contrasts `n_i = (2/√3)(e_i − ¼𝟙)` form a regular tetrahedron with
`⟨n_i, n_j⟩ = 1` or `−1/3`. -/
theorem tetra_gram (i j : Fin 4) :
    ∑ k, vertexDir i k * vertexDir j k
      = (if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0) - 1/4 := by
  fin_cases i <;> fin_cases j <;>
    simp only [vertexDir, Fin.sum_univ_four] <;>
    norm_num [Fin.val_ofNat]

/-- One contrast outer-product entry `d_{ij} d_{ij}^*` at position `(k,l)`. -/
def contrastOuter (i j k l : Fin 4) : ℝ :=
  ((if (k : ℕ) = (i : ℕ) then (1:ℝ) else 0)
      - if (k : ℕ) = (j : ℕ) then 1 else 0)
    * ((if (l : ℕ) = (i : ℕ) then (1:ℝ) else 0)
      - if (l : ℕ) = (j : ℕ) then 1 else 0)

/-- **The boxed six-contrast frame identity**: the six contrasts `d_{ij}`,
`i < j`, satisfy `Σ_{i<j} d_{ij} d_{ij}^* = 4(I − ¼J)` — four times the
mean-zero projection `I_{W₀}`. -/
theorem contrast_frame_identity (k l : Fin 4) :
    contrastOuter 0 1 k l + contrastOuter 0 2 k l + contrastOuter 0 3 k l
      + contrastOuter 1 2 k l + contrastOuter 1 3 k l + contrastOuter 2 3 k l
      = 4 * ((if (k : ℕ) = (l : ℕ) then (1:ℝ) else 0) - 1/4) := by
  fin_cases k <;> fin_cases l <;>
    simp only [contrastOuter] <;>
    norm_num [Fin.val_ofNat]

end RenewalWalsh
end NCG

end
