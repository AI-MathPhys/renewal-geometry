/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact total-variance clock decomposition
  (`thm:semantic-total-variance-master`, flagship manuscript)

For the clock defect `𝔇(t) = log (p₀(t)p₂(t)/p₁(t)²)` built from
the centered even expansion `A(th) = I - t²/2·Q + t⁴·B + o(t⁴)`:

* the unknown fourth-order term `ω(B)` cancels exactly from
  `p₀p₂/p₁²` (`clock_defect_cancellation`, a polynomial identity);
* the fourth-order coefficient of the defect is
  `(ω(Q²) - ω(Q)²)/4` — the boxed fourth-derivative formula
  `d⁴/dt⁴|₀ 𝔇 = 6·Var_ω(Q)` after `4!` normalization — proved as
  the limit `𝔇(t)/t⁴ → Var_ω(Q)/4` along `t → 0`
  (`clock_defect_fourth_order`), with the `log` remainder
  controlled by `|log(1+y) - y| ≤ 2y²`;
* block diagonality reduces the state moments to block moments
  (`omega_block_sum`), and the boxed law of total variance
  `Var_ω(Q) = Σⱼwⱼ·Varⱼ/w* + Σⱼwⱼ(νⱼ - ν̄)²/w*` is proved
  exactly (`total_variance_decomposition`); the combination is
  `semantic_total_variance_fourth_order`.

Rendering disclosed: the scalar reductions `p₁(th)/w*`,
`p₂(th)/w*` are taken as the manuscript's displayed quartics with
the `o(t⁴)` remainder dropped, and the boxed fourth derivative is
rendered as the fourth-order Taylor coefficient (its `1/4!`
normalization), i.e. as the limit of `𝔇(th)/t⁴`.
-/

open Filter Topology Finset

namespace NCG

/-- The `ω(B)`-cancellation: the clock-defect numerator minus its
fourth-order model starts at `t⁶`, uniformly in the unknown
fourth-order coefficient `b`. -/
theorem clock_defect_cancellation (ω1 ω2 b t : ℝ) :
    (1 - t ^ 2 * ω1 + t ^ 4 * (ω2 / 4 + 2 * b))
      - (1 - t ^ 2 / 2 * ω1 + t ^ 4 * b) ^ 2
    = t ^ 4 * ((ω2 - ω1 ^ 2) / 4 + t ^ 2 * (ω1 * b)
        - t ^ 4 * b ^ 2) := by
  ring

/-- Quadratic remainder bound for the logarithm:
`|log(1+y) - y| ≤ 2y²` for `|y| ≤ 1/2`. -/
theorem abs_log_one_add_sub_le {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |Real.log (1 + y) - y| ≤ 2 * y ^ 2 := by
  have h1 : |(-y : ℝ)| < 1 := by
    rw [abs_neg]; linarith [abs_nonneg y]
  have h2 := Real.abs_log_sub_add_sum_range_le h1 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add,
    pow_one, Nat.cast_zero, div_one, sub_neg_eq_add,
    abs_neg] at h2
  have h3 : -y + Real.log (1 + y) = Real.log (1 + y) - y := by
    ring
  rw [h3] at h2
  have h4 : (1 : ℝ) / 2 ≤ 1 - |y| := by linarith
  have h5 : |y| ^ (1 + 1) / (1 - |y|)
      ≤ |y| ^ (1 + 1) / (1 / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) h4
  calc |Real.log (1 + y) - y|
      ≤ |y| ^ (1 + 1) / (1 - |y|) := h2
    _ ≤ |y| ^ (1 + 1) / (1 / 2) := h5
    _ = 2 * y ^ 2 := by
        norm_num
        ring

/-- The boxed fourth-order formula, rendered as the fourth Taylor
coefficient: `𝔇(t)/t⁴ → (ω(Q²) - ω(Q)²)/4` as `t → 0` (so that
`d⁴/dt⁴|₀ 𝔇 = 4!·Var/4 = 6·Var_ω(Q)`), uniformly in the unknown
fourth-order coefficient `b = ω(B)`. -/
theorem clock_defect_fourth_order (ω1 ω2 b : ℝ) :
    Tendsto (fun t : ℝ =>
      Real.log ((1 - t ^ 2 * ω1 + t ^ 4 * (ω2 / 4 + 2 * b))
          / (1 - t ^ 2 / 2 * ω1 + t ^ 4 * b) ^ 2) / t ^ 4)
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ)
      (nhds ((ω2 - ω1 ^ 2) / 4)) := by
  set P1 : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 * ω1 + t ^ 4 * b
    with hP1
  set P2 : ℝ → ℝ := fun t =>
    1 - t ^ 2 * ω1 + t ^ 4 * (ω2 / 4 + 2 * b) with hP2
  set Nf : ℝ → ℝ := fun t => (ω2 - ω1 ^ 2) / 4
    + t ^ 2 * (ω1 * b) - t ^ 4 * b ^ 2 with hNf
  set g : ℝ → ℝ := fun t => t ^ 4 * Nf t / (P1 t) ^ 2 with hg
  have hP1c : Continuous P1 := by
    simp only [hP1]; fun_prop
  have hP2c : Continuous P2 := by
    simp only [hP2]; fun_prop
  have hNfc : Continuous Nf := by
    simp only [hNf]; fun_prop
  have hP10 : P1 0 = 1 := by simp [hP1]
  have hP20 : P2 0 = 1 := by simp [hP2]
  have hP1sq : Tendsto (fun t : ℝ => (P1 t) ^ 2) (nhds 0)
      (nhds 1) := by
    have hc : Continuous (fun t : ℝ => (P1 t) ^ 2) := by
      fun_prop
    have h := hc.tendsto (0 : ℝ)
    simpa [hP10] using h
  -- eventual positivity of the polynomial factors near 0
  have hP1ev : ∀ᶠ t in nhds (0 : ℝ), 1 / 2 < P1 t := by
    have h1 : Tendsto P1 (nhds 0) (nhds 1) := by
      simpa [hP10] using hP1c.tendsto 0
    exact h1.eventually (eventually_gt_nhds (by norm_num))
  have hP2ev : ∀ᶠ t in nhds (0 : ℝ), 1 / 2 < P2 t := by
    have h1 : Tendsto P2 (nhds 0) (nhds 1) := by
      simpa [hP20] using hP2c.tendsto 0
    exact h1.eventually (eventually_gt_nhds (by norm_num))
  -- g tends to 0, hence is eventually at most 1/2 in magnitude
  have hgt : Tendsto g (nhds 0) (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ 4 * Nf t) (nhds 0)
        (nhds 0) := by
      have hc : Continuous (fun t : ℝ => t ^ 4 * Nf t) := by
        fun_prop
      have h := hc.tendsto (0 : ℝ)
      simpa using h
    have h3 := Filter.Tendsto.div h1 hP1sq one_ne_zero
    have h4 : ((fun t : ℝ => t ^ 4 * Nf t)
        / fun t : ℝ => (P1 t) ^ 2)
        = fun t : ℝ => t ^ 4 * Nf t / (P1 t) ^ 2 := rfl
    rw [h4] at h3
    simpa [hg] using h3
  have hgev : ∀ᶠ t in nhds (0 : ℝ), |g t| ≤ 1 / 2 := by
    have h1 : Tendsto (fun t => |g t|) (nhds 0) (nhds 0) := by
      simpa using hgt.abs
    exact h1.eventually (eventually_le_nhds (by norm_num))
  -- the main-part limit
  have hA : Tendsto (fun t : ℝ => Nf t / (P1 t) ^ 2)
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ)
      (nhds ((ω2 - ω1 ^ 2) / 4)) := by
    have h2 : Tendsto Nf (nhds 0)
        (nhds ((ω2 - ω1 ^ 2) / 4)) := by
      have h := hNfc.tendsto (0 : ℝ)
      simpa [hNf] using h
    have h4 := Filter.Tendsto.div h2 hP1sq one_ne_zero
    have h5 : (Nf / fun t : ℝ => (P1 t) ^ 2)
        = fun t : ℝ => Nf t / (P1 t) ^ 2 := rfl
    rw [h5] at h4
    have h6 : Tendsto (fun t : ℝ => Nf t / (P1 t) ^ 2)
        (nhds 0) (nhds ((ω2 - ω1 ^ 2) / 4)) := by
      simpa using h4
    exact h6.mono_left nhdsWithin_le_nhds
  -- pointwise identity `g t / t^4 = Nf t / P1 t ^ 2` off zero
  have hgt4 : ∀ t : ℝ, t ≠ 0 → P1 t ≠ 0 →
      g t / t ^ 4 = Nf t / (P1 t) ^ 2 := by
    intro t ht0 hP1ne
    have ht4 : (t : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 ht0
    simp only [hg]
    rw [div_div, mul_comm ((P1 t) ^ 2) (t ^ 4),
      mul_div_mul_left _ _ ht4]
  -- the remainder limit, by the quadratic log bound and squeezing
  have hB : Tendsto (fun t : ℝ =>
      (Real.log (1 + g t) - g t) / t ^ 4)
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine squeeze_zero_norm' (a := fun t : ℝ =>
      2 * g t * (Nf t / (P1 t) ^ 2)) ?_ ?_
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        hgev, eventually_nhdsWithin_of_eventually_nhds hP1ev,
        self_mem_nhdsWithin] with t hgt2 hP1t ht0
      have ht0' : (t : ℝ) ≠ 0 := ht0
      have hP1ne : P1 t ≠ 0 := by positivity
      have ht4pos : (0 : ℝ) < t ^ 4 := by positivity
      calc ‖(Real.log (1 + g t) - g t) / t ^ 4‖
          = |Real.log (1 + g t) - g t| / t ^ 4 := by
            rw [Real.norm_eq_abs, abs_div, abs_of_pos ht4pos]
        _ ≤ 2 * (g t) ^ 2 / t ^ 4 := by
            gcongr
            exact abs_log_one_add_sub_le hgt2
        _ = 2 * g t * (g t / t ^ 4) := by ring
        _ = 2 * g t * (Nf t / (P1 t) ^ 2) := by
            rw [hgt4 t ht0' hP1ne]
    · have h1 : Tendsto (fun t : ℝ => 2 * g t)
          (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds 0) := by
        have h2 := (hgt.mono_left
          (nhdsWithin_le_nhds
            (s := ({(0 : ℝ)}ᶜ : Set ℝ)))).const_mul (2 : ℝ)
        simpa using h2
      have h3 := h1.mul hA
      simpa using h3
  -- combine and transfer along the eventual equality
  have hsum := hA.add hB
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hP1ev,
    eventually_nhdsWithin_of_eventually_nhds hP2ev,
    self_mem_nhdsWithin] with t hP1t hP2t ht0
  have ht0' : (t : ℝ) ≠ 0 := ht0
  have hP1ne : P1 t ≠ 0 := by positivity
  have ht4 : (t : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 ht0'
  -- the quotient equals 1 + g t
  have hquot : P2 t / (P1 t) ^ 2 = 1 + g t := by
    simp only [hg]
    have hkey : P2 t - (P1 t) ^ 2 = t ^ 4 * Nf t := by
      simp only [hP1, hP2, hNf]; ring
    field_simp
    linarith [hkey]
  rw [hquot, ← hgt4 t ht0' hP1ne, ← add_div]
  congr 1
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Block diagonality reduces the state moment to block moments:
`⟨Z, T Z⟩ = Σⱼ ⟨zⱼ, T zⱼ⟩` when the blocks do not couple. -/
theorem omega_block_sum {s : ℕ} (z : Fin s → E) (T : E →ₗ[ℝ] E)
    (horth : ∀ i j, i ≠ j → inner ℝ (z i) (T (z j)) = (0 : ℝ)) :
    inner ℝ (∑ j, z j) (T (∑ j, z j))
      = ∑ j, inner ℝ (z j) (T (z j)) := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  rw [Finset.sum_eq_single i
    (fun j _ hj => horth i j (Ne.symm hj))
    (fun h => absurd (Finset.mem_univ i) h)]

/-- `thm:semantic-total-variance-master`, boxed law of total
variance: `Var_ω(Q) = Σⱼwⱼ·Varⱼ/w* + Σⱼwⱼ(νⱼ - ν̄)²/w*`. -/
theorem total_variance_decomposition {s : ℕ}
    (w ν m2 : Fin s → ℝ) (hstar : 0 < ∑ j, w j) :
    (∑ j, w j * m2 j) / (∑ j, w j)
      - ((∑ j, w j * ν j) / (∑ j, w j)) ^ 2
    = (∑ j, w j * (m2 j - ν j ^ 2)) / (∑ j, w j)
      + (∑ j, w j * (ν j - (∑ i, w i * ν i) / (∑ i, w i)) ^ 2)
        / (∑ j, w j) := by
  have hW : (∑ j, w j) ≠ 0 := ne_of_gt hstar
  have h1 : ∑ j, w j * (m2 j - ν j ^ 2)
      = (∑ j, w j * m2 j) - ∑ j, w j * ν j ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, w j * (ν j - (∑ i, w i * ν i)
        / (∑ i, w i)) ^ 2
      = (∑ j, w j * ν j ^ 2)
        - 2 * ((∑ i, w i * ν i) / (∑ i, w i))
          * (∑ j, w j * ν j)
        + ((∑ i, w i * ν i) / (∑ i, w i)) ^ 2
          * (∑ j, w j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2]
  field_simp
  ring

/-- Combination of the two boxed formulas: the fourth-order clock
coefficient equals one quarter of the total-variance
decomposition. -/
theorem semantic_total_variance_fourth_order {s : ℕ}
    (w ν m2 : Fin s → ℝ) (b : ℝ) (hstar : 0 < ∑ j, w j) :
    Tendsto (fun t : ℝ =>
      Real.log ((1 - t ^ 2 * ((∑ j, w j * ν j) / (∑ j, w j))
          + t ^ 4 * ((∑ j, w j * m2 j) / (∑ j, w j) / 4 + 2 * b))
          / (1 - t ^ 2 / 2 * ((∑ j, w j * ν j) / (∑ j, w j))
            + t ^ 4 * b) ^ 2) / t ^ 4)
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ)
      (nhds (((∑ j, w j * (m2 j - ν j ^ 2)) / (∑ j, w j)
        + (∑ j, w j * (ν j - (∑ i, w i * ν i) / (∑ i, w i)) ^ 2)
          / (∑ j, w j)) / 4)) := by
  have h := clock_defect_fourth_order
    ((∑ j, w j * ν j) / (∑ j, w j))
    ((∑ j, w j * m2 j) / (∑ j, w j)) b
  rw [← total_variance_decomposition w ν m2 hstar]
  exact h

end NCG
