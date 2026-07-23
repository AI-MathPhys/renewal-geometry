/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.PerronPressure

/-!
# Monotonicity of the growth rate under principal submatrices

The lower-bound half of clause (ii) of `prop:terminal-component`
(`manuscripts/renewal_emergence/renewal_emergence.tex`): the Gelfand–Fekete growth rate of every
principal submatrix (in particular, of every strongly connected
component block) is dominated by that of the full nonnegative
matrix,

`pRad (B|_C) ≤ pRad B`  (`pRad_submatrix_le`),

because powers of the submatrix are entrywise dominated by the
corresponding entries of powers of `B` (paths inside `C` are a
subset of all paths, `entry_pow_submatrix_le`), so the entry-sum
gauges compare and the growth limits follow.  The upper-bound half
(`ρ(B) = max_j ρ(B|C_j)` needs the block-triangular first-passage
decomposition) remains open.
-/

namespace NCG

open Filter

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-- Powers of a principal submatrix are entrywise dominated by the
corresponding entries of powers of the matrix. -/
theorem entry_pow_submatrix_le {B : Matrix V V ℝ}
    (hB : EntryNonneg B) (e : S ↪ V) :
    ∀ (k : ℕ) (x y : S),
      ((B.submatrix e e) ^ k) x y ≤ (B ^ k) (e x) (e y) := by
  intro k
  induction k with
  | zero =>
    intro x y
    rw [pow_zero, pow_zero]
    by_cases hxy : x = y
    · rw [hxy, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hxy,
        Matrix.one_apply_ne (fun hc => hxy (e.injective hc))]
  | succ k ih =>
    intro x y
    rw [pow_succ, pow_succ]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have h1 : ∑ z : S, ((B.submatrix e e) ^ k) x z
        * (B.submatrix e e) z y
        ≤ ∑ z : S, (B ^ k) (e x) (e z) * B (e z) (e y) := by
      refine Finset.sum_le_sum fun z _ => ?_
      have h2 : (0 : ℝ) ≤ B (e z) (e y) := hB _ _
      have h3 : ((B.submatrix e e) : Matrix S S ℝ) z y
          = B (e z) (e y) := rfl
      rw [h3]
      exact mul_le_mul_of_nonneg_right (ih x z) h2
    refine le_trans h1 ?_
    have h4 : ∑ z : S, (B ^ k) (e x) (e z) * B (e z) (e y)
        = ∑ w ∈ Finset.univ.map e,
            (B ^ k) (e x) w * B w (e y) := by
      rw [Finset.sum_map]
    rw [h4]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) fun w _ _ => ?_
    exact mul_nonneg (entryNonneg_pow hB k _ _) (hB _ _)

/-- The entry-sum gauges compare. -/
theorem entrySum_pow_submatrix_le {B : Matrix V V ℝ}
    (hB : EntryNonneg B) (e : S ↪ V) (k : ℕ) :
    entrySum ((B.submatrix e e) ^ k) ≤ entrySum (B ^ k) := by
  rw [entrySum, entrySum]
  have h1 : ∑ x : S, ∑ y : S, ((B.submatrix e e) ^ k) x y
      ≤ ∑ x : S, ∑ y : S, (B ^ k) (e x) (e y) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      entry_pow_submatrix_le hB e k x y
  refine le_trans h1 ?_
  have h2 : ∑ x : S, ∑ y : S, (B ^ k) (e x) (e y)
      = ∑ v ∈ Finset.univ.map e, ∑ y : S, (B ^ k) v (e y) := by
    rw [Finset.sum_map]
  rw [h2]
  have h3 : ∑ v ∈ Finset.univ.map e, ∑ y : S, (B ^ k) v (e y)
      ≤ ∑ v : V, ∑ y : S, (B ^ k) v (e y) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) fun v _ _ => ?_
    exact Finset.sum_nonneg fun y _ => entryNonneg_pow hB k _ _
  refine le_trans h3 ?_
  refine Finset.sum_le_sum fun v _ => ?_
  have h4 : ∑ y : S, (B ^ k) v (e y)
      = ∑ w ∈ Finset.univ.map e, (B ^ k) v w := by
    rw [Finset.sum_map]
  rw [h4]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ _) fun w _ _ => entryNonneg_pow hB k _ _

/-- **Growth-rate monotonicity under principal submatrices**
(the lower-bound half of `prop:terminal-component` (ii)):
`pRad (B|_C) ≤ pRad B`. -/
theorem pRad_submatrix_le {B : Matrix V V ℝ}
    (hB : EntryNonneg B) (e : S ↪ V)
    (hw' : HasDiagWitness (B.submatrix e e))
    (hw : HasDiagWitness B) :
    pRad (B.submatrix e e) ≤ pRad B := by
  have hB' : EntryNonneg (B.submatrix e e) :=
    fun x y => hB (e x) (e y)
  have h1 := tendsto_growthSeq hB' hw'
  have h2 := tendsto_growthSeq hB hw
  have h3 : Real.log (pRad (B.submatrix e e))
      ≤ Real.log (pRad B) := by
    refine le_of_tendsto_of_tendsto' h1 h2 fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      rw [div_le_div_iff₀ hkR hkR]
      refine mul_le_mul_of_nonneg_right ?_ hkR.le
      rw [growthSeq, growthSeq]
      refine Real.log_le_log ?_
        (entrySum_pow_submatrix_le hB e k)
      exact entrySum_pow_pos hB' hw' k
  have h4 : pRad (B.submatrix e e)
      = Real.exp (Real.log (pRad (B.submatrix e e))) :=
    (Real.exp_log (pRad_pos _)).symm
  rw [h4, ← Real.exp_log (pRad_pos B)]
  exact Real.exp_le_exp.mpr h3

end NCG
