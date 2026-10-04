/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Lipschitz square partitions of unity with small supports on the torus

For the localisation step of `thm:supp-general-Wilson-ellipticity` (paper
`predictive_spectral_geometry`: "choose a partition with supports of fixed small diameter `r`
… a fixed finite partition with `Σ χ² = 1`"), we construct, for every `M ≥ 2`, explicit
cutoffs `χ_α` (`α : Fin d → Fin M`) on the torus `𝕋ᵈ = UnitAddTorus (Fin d)` with

* `sum_sq_bump`: `Σ_α χ_α(y)² = 1` for every `y`;
* `bump_ne_zero`: `χ_α(y) ≠ 0 → ‖y_i - α_i/M‖ < 1/M` for every coordinate `i` (support of
  diameter `≤ 2/M` around the centre `centre α`);
* `abs_bump_add_lineVec_sub_le`: `|χ_α(y + t e_j) - χ_α(y)| ≤ (π M / 2) |t|` (Lipschitz along the
  coordinate lines, with a constant independent of everything but `M`);
* `abs_bump_le_one`.

The one-dimensional building block is `bump1 M i y = cos(π/2 · min(M ‖y - i/M‖, 1))`, whose
squares sum to one (`sum_sq_bump1`: on `[p/M, (p+1)/M]` only the neighbours `p` and `p + 1`
contribute, with `cos²` and `sin²`); the `d`-dimensional cutoffs are products.
-/

open Real Finset

noncomputable section

namespace RenewalGeometry.TorusPartition

/-! ### One dimension -/

/-- The centre `i/M` of the `i`-th one-dimensional patch. -/
def centre1 (M : ℕ) (i : Fin M) : UnitAddCircle := (((i : ℕ) : ℝ) / M : ℝ)

/-- The one-dimensional cutoff `cos(π/2 · min(M ‖y - i/M‖, 1))`. -/
def bump1 (M : ℕ) (i : Fin M) (y : UnitAddCircle) : ℝ :=
  Real.cos (π / 2 * min ((M : ℝ) * ‖y - centre1 M i‖) 1)

theorem abs_bump1_le_one (M : ℕ) (i : Fin M) (y : UnitAddCircle) : |bump1 M i y| ≤ 1 :=
  abs_cos_le_one _

theorem bump1_ne_zero {M : ℕ} {i : Fin M} {y : UnitAddCircle} (h : bump1 M i y ≠ 0) :
    (M : ℝ) * ‖y - centre1 M i‖ < 1 := by
  by_contra hc
  push Not at hc
  apply h
  unfold bump1
  rw [min_eq_right hc, mul_one, cos_pi_div_two]

/-- Lipschitz bound of the one-dimensional cutoff. -/
theorem abs_bump1_sub_le (M : ℕ) (i : Fin M) (y y' : UnitAddCircle) :
    |bump1 M i y - bump1 M i y'| ≤ π / 2 * M * ‖y - y'‖ := by
  unfold bump1
  refine (abs_cos_sub_cos_le _ _).trans ?_
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < π / 2), mul_assoc]
  gcongr
  refine (abs_inf_sub_inf_le_abs _ _ _).trans ?_
  rw [← mul_sub, abs_mul, Nat.abs_cast]
  gcongr
  have := abs_norm_sub_norm_le (y - centre1 M i) (y' - centre1 M i)
  rwa [sub_sub_sub_cancel_right] at this

theorem coe_intCast_unitAddCircle (k : ℤ) : ((k : ℝ) : UnitAddCircle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]; exact ⟨k, by simp⟩

/-- Every point of the circle has a representative in `[0, 1)`. -/
theorem exists_rep (y : UnitAddCircle) : ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ (t : UnitAddCircle) = y := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
  refine ⟨Int.fract t, Int.fract_nonneg t, Int.fract_lt_one t, ?_⟩
  rw [Int.fract, AddCircle.coe_sub, coe_intCast_unitAddCircle, sub_zero]

/-- `‖x‖_{𝕋} = |x|` for `|x| ≤ 1/2`. -/
theorem norm_coe_of_abs_le {x : ℝ} (hx : |x| ≤ 1 / 2) : ‖(x : UnitAddCircle)‖ = |x| :=
  (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 (by simpa using hx)

/-- If `M x` is at distance at least one from every integer `≡ i (mod M)`, …: the far patches. -/
theorem le_norm_coe_far (M : ℕ) (hM : 0 < M) (t : ℝ) (p : ℕ) (hp : (p : ℝ) ≤ M * t)
    (hp1 : M * t < p + 1) (i : ℕ) (hfar : ∀ q : ℤ, (q : ℤ) ≡ i [ZMOD M] → q ≠ p ∧ q ≠ p + 1) :
    1 / (M : ℝ) ≤ ‖((t - (i : ℝ) / M : ℝ) : UnitAddCircle)‖ := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [UnitAddCircle.norm_eq]
  set r := round (t - (i : ℝ) / M)
  set q : ℤ := i + M * r
  have hq : q ≡ i [ZMOD M] := by
    simp only [q, Int.ModEq, Int.add_mul_emod_self_left]
  obtain ⟨hq1, hq2⟩ := hfar q hq
  have e : t - (i : ℝ) / M - r = (M * t - q) / M := by
    simp only [q]; push_cast; field_simp; ring
  rw [e, abs_div, abs_of_pos hMr, div_le_div_iff_of_pos_right hMr]
  rcases lt_or_gt_of_ne hq1 with h | h
  · have : (q : ℝ) ≤ p - 1 := by
      have : q ≤ (p : ℤ) - 1 := by omega
      exact_mod_cast this
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (p : ℝ) + 2 ≤ q := by
      have : (p : ℤ) + 2 ≤ q := by omega
      exact_mod_cast this
    rw [abs_of_nonpos (by linarith)]; linarith

/-- **`Σ_i bump1(y)² = 1`** for `M ≥ 2`. -/
theorem sum_sq_bump1 (M : ℕ) (hM : 2 ≤ M) (y : UnitAddCircle) :
    ∑ i : Fin M, bump1 M i y ^ 2 = 1 := by
  have hM0 : 0 < M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨t, ht0, ht1, rfl⟩ := exists_rep y
  set p := ⌊(M : ℝ) * t⌋₊ with hpdef
  have hp : (p : ℝ) ≤ M * t := Nat.floor_le (by positivity)
  have hp1 : (M : ℝ) * t < p + 1 := Nat.lt_floor_add_one _
  have hpM : p < M := by
    have : (p : ℝ) < M := by nlinarith
    exact_mod_cast this
  set s := (M : ℝ) * t - p with hs
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s < 1 := by linarith
  set a : Fin M := ⟨p, hpM⟩
  set b : Fin M := ⟨(p + 1) % M, Nat.mod_lt _ hM0⟩
  have hab : a ≠ b := by
    intro h
    have h' := congrArg Fin.val h
    simp only [a, b] at h'
    by_cases hlt : p + 1 < M
    · rw [Nat.mod_eq_of_lt hlt] at h'; omega
    · have : p + 1 = M := by omega
      rw [this, Nat.mod_self] at h'; omega
  have hdiff : ∀ i : Fin M, ((t : ℝ) : UnitAddCircle) - centre1 M i =
      ((t - ((i : ℕ) : ℝ) / M : ℝ) : UnitAddCircle) := by
    intro i; rw [centre1, AddCircle.coe_sub]
  -- the patch `a`
  have ha : ‖((t : ℝ) : UnitAddCircle) - centre1 M a‖ = s / M := by
    rw [hdiff]
    have e : t - ((a : ℕ) : ℝ) / M = s / M := by
      simp only [a, hs]; field_simp
    rw [e, norm_coe_of_abs_le, abs_of_nonneg (by positivity)]
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hMr]; nlinarith
  -- the patch `b`
  have hb : ‖((t : ℝ) : UnitAddCircle) - centre1 M b‖ = (1 - s) / M := by
    rw [hdiff]
    have e : ((t - ((b : ℕ) : ℝ) / M : ℝ) : UnitAddCircle) = (((s - 1) / M : ℝ) : UnitAddCircle) := by
      by_cases hlt : p + 1 < M
      · have hbv : ((b : ℕ) : ℝ) = p + 1 := by
          simp only [b, Nat.mod_eq_of_lt hlt]; push_cast; ring
        rw [hbv]; congr 1; simp only [hs]; field_simp; ring
      · have hpM' : p + 1 = M := by omega
        have hbv : ((b : ℕ) : ℝ) = 0 := by simp only [b, hpM', Nat.mod_self]; simp
        rw [hbv, zero_div, sub_zero]
        have : ((s - 1) / M : ℝ) = t - ((1 : ℤ) : ℝ) := by
          have hpM'' : (p : ℝ) + 1 = M := by exact_mod_cast hpM'
          simp only [hs]; field_simp; push_cast; linarith
        rw [this, AddCircle.coe_sub, coe_intCast_unitAddCircle, sub_zero]
    rw [e, norm_coe_of_abs_le, abs_div, abs_of_pos hMr, abs_of_nonpos (by linarith)]
    · ring
    · rw [abs_div, abs_of_pos hMr, abs_of_nonpos (by linarith), div_le_iff₀ hMr]; nlinarith
  -- the far patches
  have hfar : ∀ i : Fin M, i ≠ a ∧ i ≠ b → bump1 M i ((t : ℝ) : UnitAddCircle) ^ 2 = 0 := by
    rintro i ⟨hia, hib⟩
    have hge : 1 / (M : ℝ) ≤ ‖((t : ℝ) : UnitAddCircle) - centre1 M i‖ := by
      rw [hdiff]
      refine le_norm_coe_far M hM0 t p hp hp1 i fun q hq => ⟨fun hqp => ?_, fun hqp => ?_⟩
      · apply hia
        ext
        simp only [a]
        have := hq.symm
        rw [hqp] at this
        have h2 : ((i : ℕ) : ℤ) % M = (p : ℤ) % M := this
        have h3 : ((i : ℕ) : ℤ) % M = (i : ℕ) := Int.emod_eq_of_lt (by positivity)
          (by exact_mod_cast i.2)
        have h4 : (p : ℤ) % M = p := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hpM)
        omega
      · apply hib
        ext
        simp only [b]
        have := hq.symm
        rw [hqp] at this
        have h2 : ((i : ℕ) : ℤ) % M = ((p : ℤ) + 1) % M := this
        have h3 : ((i : ℕ) : ℤ) % M = (i : ℕ) := Int.emod_eq_of_lt (by positivity)
          (by exact_mod_cast i.2)
        have h5 : (((p + 1) % M : ℕ) : ℤ) = ((p : ℤ) + 1) % M := by push_cast; rfl
        omega
    have : 1 ≤ (M : ℝ) * ‖((t : ℝ) : UnitAddCircle) - centre1 M i‖ := by
      rw [div_le_iff₀' hMr] at hge; exact hge
    unfold bump1
    rw [min_eq_right this, mul_one, cos_pi_div_two]; ring
  rw [Fintype.sum_eq_add a b hab hfar]
  unfold bump1
  rw [ha, hb, mul_div_cancel₀ _ hMr.ne', mul_div_cancel₀ _ hMr.ne', min_eq_left hs1.le,
    min_eq_left (by linarith)]
  have : π / 2 * (1 - s) = π / 2 - π / 2 * s := by ring
  rw [this, cos_pi_div_two_sub]
  exact cos_sq_add_sin_sq _

/-! ### The torus -/

variable {d : ℕ}

/-- The point `t e_j` of the torus. -/
def lineVec (j : Fin d) (t : ℝ) : UnitAddTorus (Fin d) := Pi.single j (t : UnitAddCircle)

/-- The centre `(α_i / M)_i` of the patch `α`. -/
def centre (M : ℕ) (α : Fin d → Fin M) : UnitAddTorus (Fin d) := fun i => centre1 M (α i)

/-- **The product cutoff** `χ_α(y) = Π_i bump1(α_i)(y_i)`. -/
def bump (M : ℕ) (α : Fin d → Fin M) (y : UnitAddTorus (Fin d)) : ℝ :=
  ∏ i, bump1 M (α i) (y i)

theorem abs_bump_le_one (M : ℕ) (α : Fin d → Fin M) (y : UnitAddTorus (Fin d)) :
    |bump M α y| ≤ 1 := by
  rw [bump, Finset.abs_prod]
  exact Finset.prod_le_one (fun i _ => abs_nonneg _) fun i _ => abs_bump1_le_one _ _ _

/-- **`Σ_α χ_α² = 1`**. -/
theorem sum_sq_bump (M : ℕ) (hM : 2 ≤ M) (y : UnitAddTorus (Fin d)) :
    ∑ α : Fin d → Fin M, bump M α y ^ 2 = 1 := by
  classical
  simp only [bump, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i (a : Fin M) => bump1 M a (y i) ^ 2)]
  exact Finset.prod_eq_one fun i _ => sum_sq_bump1 M hM (y i)

/-- **Support**: `χ_α(y) ≠ 0` forces every coordinate within `1/M` of the centre. -/
theorem bump_ne_zero {M : ℕ} {α : Fin d → Fin M} {y : UnitAddTorus (Fin d)}
    (h : bump M α y ≠ 0) (i : Fin d) : (M : ℝ) * ‖y i - centre M α i‖ < 1 := by
  apply bump1_ne_zero
  intro h0
  exact h (Finset.prod_eq_zero (Finset.mem_univ i) h0)

/-- Telescoping for products of real numbers bounded by one. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (hb : ∀ i, |b i| ≤ 1) : |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj]
    have hsplit : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |∏ i ∈ s, b i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _) fun i _ => hb i
    have h2 : |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| :=
      (mul_le_of_le_one_left (abs_nonneg _) (ha j)).trans ih
    have h3 : |a j - b j| * |∏ i ∈ s, b i| ≤ |a j - b j| :=
      mul_le_of_le_one_right (abs_nonneg _) h1
    linarith

/-- **Lipschitz bound along the coordinate lines**: `|χ_α(y + t e_j) - χ_α(y)| ≤ (π M/2) |t|`. -/
theorem abs_bump_add_lineVec_sub_le (M : ℕ) (α : Fin d → Fin M) (y : UnitAddTorus (Fin d))
    (j : Fin d) (t : ℝ) : |bump M α (y + lineVec j t) - bump M α y| ≤ π / 2 * M * |t| := by
  classical
  unfold bump
  refine (abs_prod_sub_prod_le _ _ _ (fun i => abs_bump1_le_one _ _ _)
    (fun i => abs_bump1_le_one _ _ _)).trans ?_
  rw [Finset.sum_eq_single j]
  · refine (abs_bump1_sub_le M (α j) _ _).trans ?_
    simp only [lineVec, Pi.add_apply, Pi.single_eq_same, add_sub_cancel_left]
    gcongr
    rw [UnitAddCircle.norm_eq]
    simpa using round_le t 0
  · intro i _ hij
    simp [lineVec, Pi.single_eq_of_ne hij]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- A continuous version: each cutoff is continuous. -/
theorem continuous_bump (M : ℕ) (α : Fin d → Fin M) : Continuous (bump M α) := by
  unfold bump bump1
  refine continuous_finsetProd _ fun i _ => ?_
  refine continuous_cos.comp (continuous_const.mul (Continuous.min ?_ continuous_const))
  exact continuous_const.mul (((continuous_apply i).sub continuous_const).norm)

end RenewalGeometry.TorusPartition
