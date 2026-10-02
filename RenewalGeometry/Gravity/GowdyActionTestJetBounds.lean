/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdyActionTestEulerLagrange

/-!
# First-jet comparison for the midpoint/centered discretization on a periodic slab
  (infrastructure for `eq:supp-gowdy-action-test`, `thm:main-gowdy-regulator` (G4);
  emergent-spacetime supplement)

For a `C²` function `F` on `ℝ × ℝ`, `2π`-periodic in `θ`, and the slab `t ∈ [t₀, t₁]`:

* `exists_lipschitz_slab`: a `C¹` periodic function is Lipschitz on the slab.
* `exists_cellJet_error`: on every cell `[τ, τ + h] × [θ, θ + ℓ]` inside the slab, the midpoint
  time sample `(F(τ,θ) + F(τ+h,θ))/2`, the forward time quotient `(F(τ+h,θ) - F(τ,θ))/h` and the
  centered space difference of the time average are within `M (h + ℓ)` of `F`, `∂_t F`, `∂_θ F`
  at every point of the cell (Taylor/mean-value comparison).
* `sampleField`, `exists_sampleField_jet_error`: the same for the grid sampling
  `F(τ₀ + n h, θ_j)` on `ZMod N`, `ℓ = 2π/N` (wrap-around handled by periodicity), stated for the
  grid operators `gridAvg`, `gridDt`, `gridDθ` of the discrete action.
* `abs_gridAvg_le`, `abs_gridDt_le`, `abs_gridDθ_le`: the grid operators applied to an error
  field bounded in `C¹_ℓ` (values and forward space differences) and in time differences.
-/

open Set Finset
open scoped BigOperators ContDiff

namespace RenewalGeometry.GowdyStaggered.ActionTest

noncomputable section

/-! ### Periodicity of derivatives and Lipschitz bounds on the slab -/

theorem fderiv_periodic {F : ℝ × ℝ → ℝ}
    (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 2 * Real.pi) = F p) (p : ℝ × ℝ) :
    fderiv ℝ F (p.1, p.2 + 2 * Real.pi) = fderiv ℝ F p := by
  have hfun : (fun x : ℝ × ℝ => F (x + ((0 : ℝ), 2 * Real.pi))) = F := by
    funext x; rw [← hper x]; congr 1; ext <;> simp
  have e : ((p.1, p.2 + 2 * Real.pi) : ℝ × ℝ) = p + ((0 : ℝ), 2 * Real.pi) := by ext <;> simp
  rw [e, ← fderiv_comp_add_right, hfun]

theorem dT_periodic {F : ℝ × ℝ → ℝ} (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 2 * Real.pi) = F p)
    (p : ℝ × ℝ) : dT F (p.1, p.2 + 2 * Real.pi) = dT F p := by
  simp only [dT, fderiv_periodic hper]

theorem dΘ_periodic {F : ℝ × ℝ → ℝ} (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 2 * Real.pi) = F p)
    (p : ℝ × ℝ) : dΘ F (p.1, p.2 + 2 * Real.pi) = dΘ F p := by
  simp only [dΘ, fderiv_periodic hper]

theorem contDiff_dT {F : ℝ × ℝ → ℝ} {m : ℕ} (hF : ContDiff ℝ (m + 1) F) :
    ContDiff ℝ m (fun p => dT F p) :=
  (hF.fderiv_right (by exact_mod_cast le_rfl)).clm_apply contDiff_const

theorem contDiff_dΘ {F : ℝ × ℝ → ℝ} {m : ℕ} (hF : ContDiff ℝ (m + 1) F) :
    ContDiff ℝ m (fun p => dΘ F p) :=
  (hF.fderiv_right (by exact_mod_cast le_rfl)).clm_apply contDiff_const

/-- A `C¹` function, `2π`-periodic in `θ`, is Lipschitz on the slab `[t₀, t₁] × ℝ`. -/
theorem exists_lipschitz_slab {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    (hper : ∀ p : ℝ × ℝ, G (p.1, p.2 + 2 * Real.pi) = G p) (t₀ t₁ : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ p q : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → q.1 ∈ Icc t₀ t₁ →
      |G p - G q| ≤ M * ‖p - q‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_periodic (fderiv ℝ G)
    (hG.continuous_fderiv one_ne_zero) (fderiv_periodic hper) t₀ t₁
  refine ⟨C, hC0, fun p q hp hq => ?_⟩
  have hconv : Convex ℝ (Icc t₀ t₁ ×ˢ (univ : Set ℝ)) := (convex_Icc _ _).prod convex_univ
  have := hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hG.differentiable one_ne_zero) x) (fun x hx => hC x hx.1)
    (⟨hq, mem_univ _⟩ : q ∈ Icc t₀ t₁ ×ˢ (univ : Set ℝ)) ⟨hp, mem_univ _⟩
  rwa [Real.norm_eq_abs] at this

theorem norm_cell_le {τ θ h ℓ t ϑ s ζ : ℝ} (ht : t ∈ Icc τ (τ + h)) (hs : s ∈ Icc τ (τ + h))
    (hϑ : ϑ ∈ Icc θ (θ + ℓ)) (hζ : |ζ - θ| ≤ ℓ) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ) :
    ‖((s, ζ) : ℝ × ℝ) - (t, ϑ)‖ ≤ 2 * (h + ℓ) := by
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · simp only [Prod.fst_sub, Real.norm_eq_abs]
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
  · simp only [Prod.snd_sub, Real.norm_eq_abs]
    rw [abs_le] at hζ ⊢; constructor <;> linarith [hϑ.1, hϑ.2, hζ.1, hζ.2]

/-! ### Cell jets of a smooth function -/

/-- **Cell jet comparison.**  For `F ∈ C²`, `2π`-periodic in `θ`, there is `M ≥ 0` such that on
every cell `[τ, τ + h] × [θ, θ + ℓ]` with `[τ, τ + h] ⊆ [t₀, t₁]` the midpoint time sample, the
forward time quotient and the centered space difference of the time average are within
`M (h + ℓ)` of `F`, `∂_t F` and `∂_θ F` at every point `(t, ϑ)` of the cell. -/
theorem exists_cellJet_error {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 2 * Real.pi) = F p) (t₀ t₁ : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ τ θ h ℓ : ℝ, 0 < h → 0 < ℓ → t₀ ≤ τ → τ + h ≤ t₁ →
      ∀ t ∈ Icc τ (τ + h), ∀ ϑ ∈ Icc θ (θ + ℓ),
        |(F (τ, θ) + F (τ + h, θ)) / 2 - F (t, ϑ)| ≤ M * (h + ℓ) ∧
        |(F (τ + h, θ) - F (τ, θ)) / h - dT F (t, ϑ)| ≤ M * (h + ℓ) ∧
        |((F (τ, θ + ℓ) + F (τ + h, θ + ℓ)) / 2 - (F (τ, θ - ℓ) + F (τ + h, θ - ℓ)) / 2) /
            (2 * ℓ) - dΘ F (t, ϑ)| ≤ M * (h + ℓ) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hT1 : ContDiff ℝ 1 (fun p => dT F p) := contDiff_dT (m := 1) (hF.of_le (by norm_num))
  have hΘ1 : ContDiff ℝ 1 (fun p => dΘ F p) := contDiff_dΘ (m := 1) (hF.of_le (by norm_num))
  obtain ⟨M0, hM0, hL0⟩ := exists_lipschitz_slab hF1 hper t₀ t₁
  obtain ⟨M1, hM1, hL1⟩ := exists_lipschitz_slab hT1 (dT_periodic hper) t₀ t₁
  obtain ⟨M2, hM2, hL2⟩ := exists_lipschitz_slab hΘ1 (dΘ_periodic hper) t₀ t₁
  have hdiff : Differentiable ℝ F := hF1.differentiable one_ne_zero
  refine ⟨2 * (M0 + M1 + M2), by positivity, ?_⟩
  intro τ θ h ℓ hh hℓ hτ hτh t ht ϑ hϑ
  have htslab : t ∈ Icc t₀ t₁ := ⟨hτ.trans ht.1, ht.2.trans hτh⟩
  have hτslab : τ ∈ Icc t₀ t₁ := ⟨hτ, by linarith⟩
  have hτhslab : τ + h ∈ Icc t₀ t₁ := ⟨by linarith, hτh⟩
  have hτcell : τ ∈ Icc τ (τ + h) := ⟨le_rfl, by linarith⟩
  have hτhcell : τ + h ∈ Icc τ (τ + h) := ⟨by linarith, le_rfl⟩
  have hθ0 : |θ - θ| ≤ ℓ := by simp [hℓ.le]
  have hsum : 0 ≤ h + ℓ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- the midpoint time sample
    have h1 := (hL0 (τ, θ) (t, ϑ) hτslab htslab).trans (mul_le_mul_of_nonneg_left
      (norm_cell_le ht hτcell hϑ hθ0 hh.le hℓ.le) hM0)
    have h2 := (hL0 (τ + h, θ) (t, ϑ) hτhslab htslab).trans (mul_le_mul_of_nonneg_left
      (norm_cell_le ht hτhcell hϑ hθ0 hh.le hℓ.le) hM0)
    have e : (F (τ, θ) + F (τ + h, θ)) / 2 - F (t, ϑ) =
        ((F (τ, θ) - F (t, ϑ)) + (F (τ + h, θ) - F (t, ϑ))) / 2 := by ring
    rw [e, abs_div, abs_two, div_le_iff₀ two_pos]
    refine (abs_add_le _ _).trans ?_
    nlinarith [mul_nonneg hM1 hsum, mul_nonneg hM2 hsum]
  · -- the forward time quotient: mean value theorem in `t`
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun s => F (s, θ)) (fun s => dT F (s, θ))
      (by linarith : τ < τ + h)
      (hF1.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun s _ => hasDerivAt_dT (p := (s, θ)) (hdiff _))
    have hcd' : (F (τ + h, θ) - F (τ, θ)) / h = dT F (c, θ) := by
      rw [hcd]; ring_nf
    rw [hcd']
    have hccell : c ∈ Icc τ (τ + h) := ⟨hc.1.le, hc.2.le⟩
    have := (hL1 (c, θ) (t, ϑ) ⟨hτ.trans hccell.1, hccell.2.trans hτh⟩ htslab).trans
      (mul_le_mul_of_nonneg_left (norm_cell_le ht hccell hϑ hθ0 hh.le hℓ.le) hM1)
    nlinarith [mul_nonneg hM0 hsum, mul_nonneg hM2 hsum]
  · -- the centered space difference: mean value theorem in `θ` at both time levels
    have hcen : ∀ s ∈ Icc τ (τ + h), |(F (s, θ + ℓ) - F (s, θ - ℓ)) / (2 * ℓ) - dΘ F (t, ϑ)| ≤
        M2 * (2 * (h + ℓ)) := by
      intro s hs
      obtain ⟨ζ, hζ, hζd⟩ := exists_hasDerivAt_eq_slope (fun z => F (s, z))
        (fun z => dΘ F (s, z)) (by linarith : θ - ℓ < θ + ℓ)
        (hF1.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
        (fun z _ => hasDerivAt_dΘ (p := (s, z)) (hdiff _))
      have e : (F (s, θ + ℓ) - F (s, θ - ℓ)) / (2 * ℓ) = dΘ F (s, ζ) := by
        rw [hζd]; ring_nf
      rw [e]
      have hζθ : |ζ - θ| ≤ ℓ := by rw [abs_le]; constructor <;> linarith [hζ.1, hζ.2]
      exact (hL2 (s, ζ) (t, ϑ) ⟨hτ.trans hs.1, hs.2.trans hτh⟩ htslab).trans
        (mul_le_mul_of_nonneg_left (norm_cell_le ht hs hϑ hζθ hh.le hℓ.le) hM2)
    have h1 := hcen τ hτcell
    have h2 := hcen (τ + h) hτhcell
    have e : ((F (τ, θ + ℓ) + F (τ + h, θ + ℓ)) / 2 - (F (τ, θ - ℓ) + F (τ + h, θ - ℓ)) / 2) /
        (2 * ℓ) - dΘ F (t, ϑ) =
        (((F (τ, θ + ℓ) - F (τ, θ - ℓ)) / (2 * ℓ) - dΘ F (t, ϑ)) +
          ((F (τ + h, θ + ℓ) - F (τ + h, θ - ℓ)) / (2 * ℓ) - dΘ F (t, ϑ))) / 2 := by
      field_simp; ring
    rw [e, abs_div, abs_two, div_le_iff₀ two_pos]
    refine (abs_add_le _ _).trans ?_
    nlinarith [mul_nonneg hM0 hsum, mul_nonneg hM1 hsum]

/-! ### Grid sampling -/

variable {N : ℕ}

/-- The grid sampling `F(τ₀ + n h, θ_j)` of a function on the periodic grid `ZMod N`. -/
def sampleField (F : ℝ × ℝ → ℝ) (τ₀ h : ℝ) (N : ℕ) : ℕ → ZMod N → ℝ :=
  fun n j => F (τ₀ + n * h, sampleAngle N j)

/-- **Grid jet comparison for sampled smooth functions**: the grid operators `gridAvg`, `gridDt`,
`gridDθ` of the sampling `F(τ₀ + n h, θ_j)` (`ℓ = 2π/N`) are within `M (h + ℓ)` of `F`,
`∂_t F`, `∂_θ F` on the whole cell `[τ₀ + n h, τ₀ + n h + h] × [θ_j, θ_j + ℓ]`. -/
theorem exists_sampleField_jet_error {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 2 * Real.pi) = F p) (t₀ t₁ : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ (N : ℕ) [NeZero N] (τ₀ h : ℝ) (n : ℕ), 0 < h → t₀ ≤ τ₀ + n * h →
      τ₀ + n * h + h ≤ t₁ → ∀ (j : ZMod N), ∀ t ∈ Icc (τ₀ + n * h) (τ₀ + n * h + h),
      ∀ ϑ ∈ Icc (sampleAngle N j) (sampleAngle N j + 2 * Real.pi / N),
        |gridAvg (sampleField F τ₀ h N) n j - F (t, ϑ)| ≤ M * (h + 2 * Real.pi / N) ∧
        |gridDt h (sampleField F τ₀ h N) n j - dT F (t, ϑ)| ≤ M * (h + 2 * Real.pi / N) ∧
        |gridDθ (2 * Real.pi / N) (sampleField F τ₀ h N) n j - dΘ F (t, ϑ)| ≤
          M * (h + 2 * Real.pi / N) := by
  obtain ⟨M, hM, hcell⟩ := exists_cellJet_error hF hper t₀ t₁
  refine ⟨M, hM, fun N _ τ₀ h n hh hτ hτh j t ht ϑ hϑ => ?_⟩
  have hℓ : 0 < 2 * Real.pi / N := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  obtain ⟨h1, h2, h3⟩ := hcell (τ₀ + n * h) (sampleAngle N j) h (2 * Real.pi / N) hh hℓ hτ hτh
    t ht ϑ hϑ
  have hsucc : ((n + 1 : ℕ) : ℝ) * h = n * h + h := by push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [gridAvg, sampleField, hsucc, ← add_assoc]
    exact h1
  · simp only [gridDt, sampleField, hsucc, ← add_assoc]
    exact h2
  · simp only [gridDθ, gridAvg, sampleField, hsucc, ← add_assoc]
    rw [sample_succ F hper N, sample_succ F hper N, sample_pred F hper N, sample_pred F hper N]
    exact h3

/-! ### Grid operators on error fields -/

theorem gridAvg_add (v w : ℕ → ZMod N → ℝ) (n : ℕ) (j : ZMod N) :
    gridAvg (fun m i => v m i + w m i) n j = gridAvg v n j + gridAvg w n j := by
  simp only [gridAvg]; ring

theorem gridDt_add (h : ℝ) (v w : ℕ → ZMod N → ℝ) (n : ℕ) (j : ZMod N) :
    gridDt h (fun m i => v m i + w m i) n j = gridDt h v n j + gridDt h w n j := by
  simp only [gridDt]; ring

theorem gridDθ_add (ℓ : ℝ) (v w : ℕ → ZMod N → ℝ) (n : ℕ) (j : ZMod N) :
    gridDθ ℓ (fun m i => v m i + w m i) n j = gridDθ ℓ v n j + gridDθ ℓ w n j := by
  simp only [gridDθ, gridAvg]; ring

theorem abs_gridAvg_le {e : ℕ → ZMod N → ℝ} {E : ℝ} {n : ℕ} {j : ZMod N} (h0 : |e n j| ≤ E)
    (h1 : |e (n + 1) j| ≤ E) : |gridAvg e n j| ≤ E := by
  unfold gridAvg
  rw [abs_div, abs_two, div_le_iff₀ two_pos]
  linarith [abs_add_le (e n j) (e (n + 1) j)]

theorem abs_gridDt_le {e : ℕ → ZMod N → ℝ} {h T : ℝ} (hh : 0 < h) {n : ℕ} {j : ZMod N}
    (hT : |e (n + 1) j - e n j| / h ≤ T) : |gridDt h e n j| ≤ T := by
  unfold gridDt
  rwa [abs_div, abs_of_pos hh]

/-- The centered space difference of the time average of an error field whose forward space
differences are bounded by `E` (at both time levels) is bounded by `E`. -/
theorem abs_gridDθ_le {e : ℕ → ZMod N → ℝ} {ℓ E : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {j : ZMod N}
    (hD : ∀ m ∈ ({n, n + 1} : Finset ℕ), ∀ k : ZMod N, |e m (k + 1) - e m k| / ℓ ≤ E) :
    |gridDθ ℓ e n j| ≤ E := by
  have a1 := hD n (by simp) j
  have a2 := hD n (by simp) (j - 1)
  have a3 := hD (n + 1) (by simp) j
  have a4 := hD (n + 1) (by simp) (j - 1)
  rw [sub_add_cancel] at a2 a4
  rw [div_le_iff₀ hℓ] at a1 a2 a3 a4
  unfold gridDθ gridAvg
  have heq : ((e n (j + 1) + e (n + 1) (j + 1)) / 2 - (e n (j - 1) + e (n + 1) (j - 1)) / 2) /
      (2 * ℓ) = (((e n (j + 1) - e n j) + (e n j - e n (j - 1))) +
        ((e (n + 1) (j + 1) - e (n + 1) j) + (e (n + 1) j - e (n + 1) (j - 1)))) / (4 * ℓ) := by
    field_simp; ring
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * ℓ), div_le_iff₀ (by positivity)]
  have := abs_add_le ((e n (j + 1) - e n j) + (e n j - e n (j - 1)))
    ((e (n + 1) (j + 1) - e (n + 1) j) + (e (n + 1) j - e (n + 1) (j - 1)))
  have := abs_add_le (e n (j + 1) - e n j) (e n j - e n (j - 1))
  have := abs_add_le (e (n + 1) (j + 1) - e (n + 1) j) (e (n + 1) j - e (n + 1) (j - 1))
  linarith

end

end RenewalGeometry.GowdyStaggered.ActionTest
