/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DonskerFiniteDimensional

/-!
# Donsker's theorem in finite-dimensional distributions

The partial-sum process `S_n(t) = n^{-1/2} ∑_{k < ⌊n t⌋} X k` of i.i.d. centred square-integrable
random vectors: along any monotone time grid `0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_m`, the vector
`(S_n(t₁), …, S_n(t_m))` converges in distribution to the vector of partial sums of independent
centred Gaussians with covariances `(t_j - t_{j-1}) S`, i.e. to the finite-dimensional
distributions of the Brownian motion with covariance `S = covMatrix X P`.

* `floorBlock`: the increment blocks `[⌊n t_{j-1}⌋, ⌊n t_j⌋)` are pairwise disjoint
  (`floorBlock_disjoint`) with sizes `~ (t_j - t_{j-1}) n` (`tendsto_floorBlock_size`);
* `tendstoInDistribution_increments`: the increments converge to the independent Gaussian
  increments;
* `cumSum`: the continuous cumulative-sum map; `partialSum_eq_cumSum_increments`;
* `tendstoInDistribution_partialSums` (**Donsker, f.d.d.**).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open scoped InnerProductSpace

namespace NCG
namespace DonskerPartialSums

open MultivariateCLT DonskerFiniteDimensional

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Floor blocks of a time grid -/

/-- The left endpoint `⌊n t_{j}⌋` of the `j`-th increment block (`t : Fin (m+1) → ℝ`). -/
noncomputable def floorLeft {m : ℕ} (t : Fin (m + 1) → ℝ) (n : ℕ) (j : Fin m) : ℕ :=
  ⌊(n : ℝ) * t j.castSucc⌋₊

/-- The right endpoint `⌊n t_{j+1}⌋` of the `j`-th increment block. -/
noncomputable def floorRight {m : ℕ} (t : Fin (m + 1) → ℝ) (n : ℕ) (j : Fin m) : ℕ :=
  ⌊(n : ℝ) * t j.succ⌋₊

theorem floorLeft_le_floorRight {m : ℕ} {t : Fin (m + 1) → ℝ} (ht : Monotone t) (n : ℕ)
    (j : Fin m) : floorLeft t n j ≤ floorRight t n j := by
  unfold floorLeft floorRight
  exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left (ht (Fin.castSucc_le_succ j))
    (Nat.cast_nonneg n))

theorem floorRight_le_floorLeft_succ {m : ℕ} {t : Fin (m + 1) → ℝ} (ht : Monotone t) (n : ℕ)
    {i j : Fin m} (hij : i < j) : floorRight t n i ≤ floorLeft t n j := by
  unfold floorLeft floorRight
  refine Nat.floor_le_floor (mul_le_mul_of_nonneg_left (ht ?_) (Nat.cast_nonneg n))
  exact Fin.succ_le_castSucc_iff.mpr hij

/-- Two intervals `[a, b)` and `[c, d)` with `b ≤ c` are disjoint. -/
theorem Ico_disjoint_of_le {a b c d : ℕ} (h : b ≤ c) :
    Disjoint (Finset.Ico a b) (Finset.Ico c d) := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  rw [Finset.mem_Ico] at hk hk'
  omega

/-- The increment blocks of a monotone grid are pairwise disjoint. -/
theorem floorBlock_disjoint {m : ℕ} {t : Fin (m + 1) → ℝ} (ht : Monotone t) (n : ℕ) :
    Pairwise fun i j : Fin m =>
      Disjoint (Finset.Ico (floorLeft t n i) (floorRight t n i))
        (Finset.Ico (floorLeft t n j) (floorRight t n j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact Ico_disjoint_of_le (floorRight_le_floorLeft_succ ht n h)
  · exact (Ico_disjoint_of_le (floorRight_le_floorLeft_succ ht n h)).symm

/-- `⌊n a⌋ / n → a` along the naturals. -/
theorem tendsto_floor_natCast_mul_div {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) * a⌋₊ : ℝ) / n) atTop (𝓝 a) := by
  have := (tendsto_nat_floor_mul_div_atTop ha).comp tendsto_natCast_atTop_atTop
  refine this.congr fun n => ?_
  simp [mul_comm]

/-- The block sizes satisfy `(⌊n t_{j+1}⌋ - ⌊n t_j⌋) / n → t_{j+1} - t_j`. -/
theorem tendsto_floorBlock_size {m : ℕ} {t : Fin (m + 1) → ℝ} (ht : Monotone t)
    (h0 : 0 ≤ t 0) (j : Fin m) :
    Tendsto (fun n : ℕ => ((floorRight t n j - floorLeft t n j : ℕ) : ℝ) / n) atTop
      (𝓝 (t j.succ - t j.castSucc)) := by
  have hl : 0 ≤ t j.castSucc := h0.trans (ht (Fin.zero_le _))
  have hr : 0 ≤ t j.succ := h0.trans (ht (Fin.zero_le _))
  have h := (tendsto_floor_natCast_mul_div hr).sub (tendsto_floor_natCast_mul_div hl)
  refine h.congr fun n => ?_
  rw [Nat.cast_sub (floorLeft_le_floorRight ht n j), sub_div]
  rfl

/-! ### Increments and partial sums -/

/-- The cumulative-sum map on `PiLp 2 (Fin m → E)`. -/
def cumSum {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : PiLp 2 (fun _ : Fin m => E)) : PiLp 2 (fun _ : Fin m => E) :=
  WithLp.toLp 2 fun j => ∑ i ∈ Finset.Iic j, z i

theorem continuous_cumSum {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Continuous (cumSum (m := m) (E := E)) := by
  unfold cumSum
  fun_prop

/-- The partial sum up to `⌊n t_{j+1}⌋` is the cumulative sum of the increment blocks. -/
theorem partialSum_eq_cumSum_increments {m : ℕ} {t : Fin (m + 1) → ℝ} (ht : Monotone t)
    (hzero : t 0 = 0) (n : ℕ) (X : ℕ → Ω → EuclideanSpace ℝ ι) (r : ℝ) (ω : Ω) (j : Fin m) :
    r • ∑ k ∈ Finset.range (floorRight t n j), X k ω
      = ∑ i ∈ Finset.Iic j, r • ∑ k ∈ Finset.Ico (floorLeft t n i) (floorRight t n i), X k ω := by
  rw [← Finset.smul_sum]
  congr 1
  -- telescoping of consecutive intervals, by induction on the index
  obtain ⟨k, hk⟩ := j
  induction k with
  | zero =>
    have hl : floorLeft t n ⟨0, hk⟩ = 0 := by
      simp [floorLeft, hzero]
    have hIic : Finset.Iic (⟨0, hk⟩ : Fin m) = {⟨0, hk⟩} := by
      ext i
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    rw [hIic, Finset.sum_singleton, hl, Finset.range_eq_Ico]
  | succ k ih =>
    have hk' : k < m := by omega
    have hIic : Finset.Iic (⟨k + 1, hk⟩ : Fin m) = insert ⟨k + 1, hk⟩ (Finset.Iic ⟨k, hk'⟩) := by
      ext i
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
      omega
    have hnot : (⟨k + 1, hk⟩ : Fin m) ∉ Finset.Iic (⟨k, hk'⟩ : Fin m) := by
      simp [Fin.le_def]
    rw [hIic, Finset.sum_insert hnot, ← ih hk']
    have hleft : floorLeft t n ⟨k + 1, hk⟩ = floorRight t n ⟨k, hk'⟩ := rfl
    have hle : floorRight t n ⟨k, hk'⟩ ≤ floorRight t n ⟨k + 1, hk⟩ :=
      floorLeft_le_floorRight ht n ⟨k + 1, hk⟩
    rw [hleft, Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact ((add_comm _ _).trans (Finset.sum_Ico_consecutive _ (Nat.zero_le _) hle)).symm

/-- **Donsker's theorem in finite-dimensional distributions.** Along a monotone time grid
`0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_m`, the vector `(S_n(t_1), …, S_n(t_m))` of the partial-sum process
`S_n(t) = n^{-1/2} ∑_{k < ⌊n t⌋} X k` converges in distribution to the cumulative sums of
independent centred Gaussian increments with covariances `(t_{j} - t_{j-1}) S`. -/
theorem tendstoInDistribution_partialSums [DecidableEq ι] {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → EuclideanSpace ℝ ι}
    (hX : MemLp (X 0) 2 P) (h0 : P[X 0] = 0) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {m : ℕ} {t : Fin (m + 1) → ℝ} (ht : Monotone t)
    (hzero : t 0 = 0) {Y : Ω' → PiLp 2 (fun _ : Fin m => EuclideanSpace ℝ ι)}
    (hYmeas : AEMeasurable Y P') (hYindep : iIndepFun (fun j ω => Y ω j) P')
    (hYlaw : ∀ j, HasLaw (fun ω => Y ω j)
      (multivariateGaussian 0 ((t j.succ - t j.castSucc) • covMatrix (X 0) P)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (WithLp.toLp 2 fun j : Fin m =>
        (√(n : ℝ))⁻¹ • ∑ k ∈ Finset.range (floorRight t n j), X k ω :
          PiLp 2 (fun _ : Fin m => EuclideanSpace ℝ ι))) atTop (fun ω => cumSum (Y ω))
      (fun _ => P) P' := by
  have hinc := tendstoInDistribution_jointBlocks hX h0 hindep hident (floorLeft t) (floorRight t)
    (floorBlock_disjoint ht) (fun j => t j.succ - t j.castSucc)
    (tendsto_floorBlock_size ht hzero.ge) hYmeas hYindep hYlaw
  have := hinc.continuous_comp continuous_cumSum
  refine this.congr (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => rfl)
  simp only [Function.comp_def, cumSum]
  congr 1
  funext j
  exact (partialSum_eq_cumSum_increments ht hzero n X _ ω j).symm

end DonskerPartialSums
end NCG
