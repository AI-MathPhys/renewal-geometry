/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# L² consistency of the covariant central difference

The varying-coefficient covariant-consistency **estimate** left open
by `thm:curved-limit` (flagship) / `lem:covariant-consistency`
(lorentzian ledger): the midpoint-link central difference applied to
a compactly supported differentiable spinor is close to the covariant
derivative `(∂ + Ω)ψ`, **pointwise at rate `h`** and hence **in
squared L² norm at rate `h²`**:

* `centered_step_bound` — the one-sided mean-value bound
  `‖ψ(x+h) − ψ(x) − h ψ'(x)‖ ≤ L h²` for an `L`-Lipschitz
  derivative;
* `centered_difference_pointwise` — the centered rate
  `‖(2h)⁻¹(ψ(x+h) − ψ(x−h)) − ψ'(x)‖ ≤ 2 L h`;
* `centered_difference_sq_integral` — the full-line squared-L² form
  for compactly supported data:
  `∫ ‖(2h)⁻¹(ψ(x+h) − ψ(x−h)) − ψ'(x)‖² ≤ (2Lh)² (2R + 2h)`;
* `covariant_difference_pointwise` /
  `covariant_difference_sq_integral` — the same with link fields
  `A(x) = 1 + h Ω(x) + O(h²)`, `B(x) = 1 − h Ω(x) + O(h²)`
  (satisfied to second order by the exponential midpoint links of the
  discrete Levi–Civita transport): the covariant central difference
  converges to `(∂ + Ω)ψ` with explicit rate
  `(2L + MΩ K + C Mψ) h`, pointwise and in squared L² norm.

Together with the algebraic cancellation
`covariant_central_difference` (`NCG/Lorentz/CovariantConsistency.lean`)
and the strong-resolvent criterion (`NCG/Lorentz/CoreResolvent.lean`),
this supplies the varying-coefficient L² consistency clause of
`ass:scaling-package` (A5) on the common smooth core.
-/

namespace NCG

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Pointwise rates -/

omit [NormedSpace ℝ E] in
/-- Lipschitz constants are nonnegative (extracted from any two
distinct points). -/
theorem lipschitz_const_nonneg {ψ' : ℝ → E} {L : ℝ}
    (hLip : ∀ x y, ‖ψ' x - ψ' y‖ ≤ L * |x - y|) : 0 ≤ L := by
  have h := hLip 1 0
  simp only [sub_zero, abs_one, mul_one] at h
  exact le_trans (norm_nonneg _) h

/-- **One-sided mean-value bound**: an `L`-Lipschitz derivative gives
the first-order Taylor estimate `‖ψ(x+h) − ψ(x) − h ψ'(x)‖ ≤ L h²`. -/
theorem centered_step_bound {ψ ψ' : ℝ → E} {L : ℝ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hLip : ∀ x y, ‖ψ' x - ψ' y‖ ≤ L * |x - y|)
    (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ‖ψ (x + h) - ψ x - h • ψ' x‖ ≤ L * h ^ 2 := by
  have hL0 : 0 ≤ L := lipschitz_const_nonneg hLip
  set g : ℝ → E := fun t => ψ (x + t) - t • ψ' x with hg
  have hgderiv : ∀ t ∈ Icc (0:ℝ) h,
      HasDerivWithinAt g (ψ' (x + t) - ψ' x) (Icc 0 h) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => ψ (x + t)) (ψ' (x + t)) t :=
      HasDerivAt.comp_const_add x t (hψ (x + t))
    have h2 : HasDerivAt (fun t : ℝ => t • ψ' x) (ψ' x) t := by
      simpa using (hasDerivAt_id t).smul_const (ψ' x)
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0:ℝ) h,
      ‖ψ' (x + t) - ψ' x‖ ≤ L * h := by
    intro t ht
    calc ‖ψ' (x + t) - ψ' x‖ ≤ L * |x + t - x| := hLip _ _
      _ = L * |t| := by ring_nf
      _ ≤ L * h := by
          rw [abs_of_nonneg ht.1]
          exact mul_le_mul_of_nonneg_left ht.2.le hL0
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    hgderiv hbound h (right_mem_Icc.mpr hh)
  have hg0 : g 0 = ψ x := by simp [hg]
  have hgh : g h = ψ (x + h) - h • ψ' x := by simp [hg]
  rw [hg0, hgh, sub_zero] at hmvt
  calc ‖ψ (x + h) - ψ x - h • ψ' x‖
      = ‖ψ (x + h) - h • ψ' x - ψ x‖ := by
        congr 1
        abel
    _ ≤ L * h * h := hmvt
    _ = L * h ^ 2 := by ring

/-- Backward variant: `‖ψ(x−h) − ψ(x) + h ψ'(x)‖ ≤ 2 L h²`. -/
theorem centered_step_bound_back {ψ ψ' : ℝ → E} {L : ℝ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hLip : ∀ x y, ‖ψ' x - ψ' y‖ ≤ L * |x - y|)
    (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ‖ψ (x - h) - ψ x + h • ψ' x‖ ≤ 2 * (L * h ^ 2) := by
  have hL0 : 0 ≤ L := lipschitz_const_nonneg hLip
  have h1 := centered_step_bound hψ hLip (x - h) hh
  rw [sub_add_cancel] at h1
  have h2 : ‖h • ψ' (x - h) - h • ψ' x‖ ≤ L * h ^ 2 := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    calc h * ‖ψ' (x - h) - ψ' x‖
        ≤ h * (L * |x - h - x|) :=
          mul_le_mul_of_nonneg_left (hLip _ _) hh
      _ = h * (L * h) := by
          rw [show x - h - x = -h by ring, abs_neg,
            abs_of_nonneg hh]
      _ = L * h ^ 2 := by ring
  calc ‖ψ (x - h) - ψ x + h • ψ' x‖
      = ‖(ψ x - ψ (x - h) - h • ψ' (x - h))
          + (h • ψ' (x - h) - h • ψ' x)‖ := by
        rw [← norm_neg]
        congr 1
        abel
    _ ≤ ‖ψ x - ψ (x - h) - h • ψ' (x - h)‖
          + ‖h • ψ' (x - h) - h • ψ' x‖ := norm_add_le _ _
    _ ≤ L * h ^ 2 + L * h ^ 2 := add_le_add h1 h2
    _ = 2 * (L * h ^ 2) := by ring

/-- **Centered-difference pointwise rate**
(`ass:scaling-package` (A5), pointwise core): for an `L`-Lipschitz
derivative, `‖(2h)⁻¹ • (ψ(x+h) − ψ(x−h)) − ψ'(x)‖ ≤ 2 L h`. -/
theorem centered_difference_pointwise {ψ ψ' : ℝ → E} {L : ℝ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hLip : ∀ x y, ‖ψ' x - ψ' y‖ ≤ L * |x - y|)
    (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖(2 * h)⁻¹ • (ψ (x + h) - ψ (x - h)) - ψ' x‖ ≤ 2 * L * h := by
  have hL0 : 0 ≤ L := lipschitz_const_nonneg hLip
  have hfwd := centered_step_bound hψ hLip x hh.le
  have hbwd := centered_step_bound_back hψ hLip x hh.le
  have hnum : ‖ψ (x + h) - ψ (x - h) - (2 * h) • ψ' x‖
      ≤ 3 * (L * h ^ 2) := by
    calc ‖ψ (x + h) - ψ (x - h) - (2 * h) • ψ' x‖
        = ‖(ψ (x + h) - ψ x - h • ψ' x)
            - (ψ (x - h) - ψ x + h • ψ' x)‖ := by
          congr 1
          rw [show ((2:ℝ) * h) • ψ' x = h • ψ' x + h • ψ' x by
            rw [← add_smul]; ring_nf]
          abel
      _ ≤ ‖ψ (x + h) - ψ x - h • ψ' x‖
            + ‖ψ (x - h) - ψ x + h • ψ' x‖ := norm_sub_le _ _
      _ ≤ L * h ^ 2 + 2 * (L * h ^ 2) := add_le_add hfwd hbwd
      _ = 3 * (L * h ^ 2) := by ring
  have h2h : (0:ℝ) < 2 * h := by linarith
  have hkey : (2 * h)⁻¹ • (ψ (x + h) - ψ (x - h)) - ψ' x
      = (2 * h)⁻¹ • (ψ (x + h) - ψ (x - h) - (2 * h) • ψ' x) := by
    match_scalars <;> (field_simp; try ring)
  rw [hkey, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr h2h)]
  calc (2 * h)⁻¹ * ‖ψ (x + h) - ψ (x - h) - (2 * h) • ψ' x‖
      ≤ (2 * h)⁻¹ * (3 * (L * h ^ 2)) :=
        mul_le_mul_of_nonneg_left hnum (inv_pos.mpr h2h).le
    _ = (3 / 2) * (L * h) := by field_simp
    _ ≤ 2 * L * h := by nlinarith

/-! ## The squared-L² estimate -/

/-- **Centered-difference L² consistency**
(`ass:scaling-package` (A5), flat-coefficient case): for compactly
supported data with `L`-Lipschitz derivative, the squared L² distance
of the centered difference from the derivative is `O(h²)` with the
explicit constant `(2Lh)²(2R + 2h)`. -/
theorem centered_difference_sq_integral {ψ ψ' : ℝ → E} {L R : ℝ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hLip : ∀ x y, ‖ψ' x - ψ' y‖ ≤ L * |x - y|)
    (hsuppψ : ∀ x, x ∉ Icc (-R) R → ψ x = 0)
    (hsuppψ' : ∀ x, x ∉ Icc (-R) R → ψ' x = 0)
    (hR : 0 ≤ R) {h : ℝ} (hh : 0 < h) :
    (∫ x : ℝ, ‖(2 * h)⁻¹ • (ψ (x + h) - ψ (x - h)) - ψ' x‖ ^ 2)
      ≤ (2 * L * h) ^ 2 * (2 * R + 2 * h) := by
  have hL0 : 0 ≤ L := lipschitz_const_nonneg hLip
  set F : ℝ → ℝ := fun x =>
    ‖(2 * h)⁻¹ • (ψ (x + h) - ψ (x - h)) - ψ' x‖ ^ 2 with hF
  -- pointwise bound
  have hFbound : ∀ x, F x ≤ (2 * L * h) ^ 2 := fun x =>
    pow_le_pow_left₀ (norm_nonneg _)
      (centered_difference_pointwise hψ hLip x hh) 2
  -- vanishing outside the fattened support
  have hmemψ : ∀ y : ℝ, (y < -R ∨ R < y) → ψ y = 0 := by
    intro y hy
    apply hsuppψ
    intro hmem
    obtain ⟨h1, h2⟩ := mem_Icc.mp hmem
    rcases hy with hy | hy <;> linarith
  have hmemψ' : ∀ y : ℝ, (y < -R ∨ R < y) → ψ' y = 0 := by
    intro y hy
    apply hsuppψ'
    intro hmem
    obtain ⟨h1, h2⟩ := mem_Icc.mp hmem
    rcases hy with hy | hy <;> linarith
  have hFzero : ∀ x, x ∉ Icc (-(R + h)) (R + h) → F x = 0 := by
    intro x hx
    have hx' : x < -(R + h) ∨ R + h < x := by
      by_cases h1 : -(R + h) ≤ x
      · right
        by_contra h2
        push Not at h2
        exact hx (mem_Icc.mpr ⟨h1, h2⟩)
      · left
        linarith
    have hzero : ψ (x + h) = 0 ∧ ψ (x - h) = 0 ∧ ψ' x = 0 := by
      rcases hx' with hc | hc
      · exact ⟨hmemψ _ (Or.inl (by linarith)),
          hmemψ _ (Or.inl (by linarith)),
          hmemψ' _ (Or.inl (by linarith))⟩
      · exact ⟨hmemψ _ (Or.inr (by linarith)),
          hmemψ _ (Or.inr (by linarith)),
          hmemψ' _ (Or.inr (by linarith))⟩
    rw [hF]
    simp [hzero.1, hzero.2.1, hzero.2.2]
  -- continuity and integrability of `F`
  have hψc : Continuous ψ :=
    continuous_iff_continuousAt.mpr
      fun x => (hψ x).differentiableAt.continuousAt
  have hψ'c : Continuous ψ' := by
    rw [Metric.continuous_iff]
    intro x ε hε
    by_cases hL : L = 0
    · refine ⟨1, one_pos, fun y _ => ?_⟩
      have hy := hLip y x
      rw [hL, zero_mul] at hy
      have h0 : ψ' y = ψ' x := by
        have := le_antisymm hy (norm_nonneg _)
        rwa [norm_sub_eq_zero_iff] at this
      rw [dist_eq_norm, h0]
      simpa using hε
    · have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
      refine ⟨ε / L, by positivity, fun y hy => ?_⟩
      rw [dist_eq_norm]
      calc ‖ψ' y - ψ' x‖ ≤ L * |y - x| := hLip y x
        _ < L * (ε / L) := by
            refine mul_lt_mul_of_pos_left ?_ hLpos
            rwa [← Real.dist_eq]
        _ = ε := by field_simp
  have hFc : Continuous F := by
    refine Continuous.pow ?_ 2
    exact ((continuous_const.smul
      ((hψc.comp (continuous_id.add continuous_const)).sub
        (hψc.comp (continuous_id.sub continuous_const)))).sub
          hψ'c).norm
  have hFsupp : HasCompactSupport F :=
    HasCompactSupport.intro isCompact_Icc hFzero
  have hFint : Integrable F :=
    hFc.integrable_of_hasCompactSupport hFsupp
  -- domination by the indicator constant
  set G : ℝ → ℝ :=
    (Icc (-(R + h)) (R + h)).indicator
      fun _ => (2 * L * h) ^ 2 with hG
  have hGint : Integrable G := by
    rw [hG, integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hle : ∀ x, F x ≤ G x := by
    intro x
    by_cases hx : x ∈ Icc (-(R + h)) (R + h)
    · rw [hG]
      simp only [indicator_of_mem hx]
      exact hFbound x
    · rw [hFzero x hx, hG]
      exact Set.indicator_nonneg (fun _ _ => by positivity) x
  calc (∫ x : ℝ, F x) ≤ ∫ x : ℝ, G x := integral_mono hFint hGint hle
    _ = (volume (Icc (-(R + h)) (R + h))).toReal
          • ((2 * L * h) ^ 2 : ℝ) :=
        integral_indicator_const _ measurableSet_Icc
    _ = (2 * L * h) ^ 2 * (2 * R + 2 * h) := by
        rw [Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring

/-! ## The covariant (link-field) estimates -/

/-- **Covariant central-difference pointwise rate**
(`ass:scaling-package` (A5), varying-coefficient core): with link
fields `A(x) = 1 + h Ω(x) + O(h²)`, `B(x) = 1 − h Ω(x) + O(h²)`, a
Lipschitz differentiable spinor satisfies
`‖(2h)⁻¹(A ψ(x+h) − B ψ(x−h)) − (ψ' + Ω ψ)(x)‖
  ≤ (2L + MΩ K + C Mψ) h`. -/
theorem covariant_difference_pointwise
    {ψ ψ' : ℝ → E} {Ω A B : ℝ → E →L[ℝ] E}
    {L K MΩ Mψ C : ℝ} (hC : 0 ≤ C) (_hMψ0 : 0 ≤ Mψ)
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hLip : ∀ x y, ‖ψ' x - ψ' y‖ ≤ L * |x - y|)
    (hK : ∀ x y, ‖ψ x - ψ y‖ ≤ K * |x - y|)
    (hMψ : ∀ x, ‖ψ x‖ ≤ Mψ)
    (hMΩ : ∀ x, ‖Ω x‖ ≤ MΩ)
    (x : ℝ) {h : ℝ} (hh : 0 < h)
    (hA : ‖A x - (1 + h • Ω x)‖ ≤ C * h ^ 2)
    (hB : ‖B x - (1 - h • Ω x)‖ ≤ C * h ^ 2) :
    ‖(2 * h)⁻¹ • (A x (ψ (x + h)) - B x (ψ (x - h)))
        - (ψ' x + Ω x (ψ x))‖
      ≤ (2 * L + MΩ * K + C * Mψ) * h := by
  have hMΩ0 : 0 ≤ MΩ := le_trans (norm_nonneg _) (hMΩ x)
  -- the link errors
  set EA : E →L[ℝ] E := A x - (1 + h • Ω x) with hEA
  set EB : E →L[ℝ] E := B x - (1 - h • Ω x) with hEB
  have hAapp : A x (ψ (x + h))
      = EA (ψ (x + h)) + ψ (x + h) + h • Ω x (ψ (x + h)) := by
    rw [hEA]
    simp only [sub_apply, add_apply, one_apply_eq_self,
      smul_apply]
    abel
  have hBapp : B x (ψ (x - h))
      = EB (ψ (x - h)) + ψ (x - h) - h • Ω x (ψ (x - h)) := by
    rw [hEB]
    simp only [sub_apply, one_apply_eq_self, smul_apply]
    abel
  -- the three-term decomposition
  have hsplit : (2 * h)⁻¹ • (A x (ψ (x + h)) - B x (ψ (x - h)))
        - (ψ' x + Ω x (ψ x))
      = ((2 * h)⁻¹ • (ψ (x + h) - ψ (x - h)) - ψ' x)
        + (2 : ℝ)⁻¹ • ((Ω x (ψ (x + h)) - Ω x (ψ x))
            + (Ω x (ψ (x - h)) - Ω x (ψ x)))
        + (2 * h)⁻¹ • (EA (ψ (x + h)) - EB (ψ (x - h))) := by
    rw [hAapp, hBapp]
    match_scalars <;> (field_simp; try ring)
  -- bound each term
  have hT1 : ‖(2 * h)⁻¹ • (ψ (x + h) - ψ (x - h)) - ψ' x‖
      ≤ 2 * L * h := centered_difference_pointwise hψ hLip x hh
  have hOmp : ‖Ω x (ψ (x + h)) - Ω x (ψ x)‖ ≤ MΩ * (K * h) := by
    rw [← map_sub]
    calc ‖Ω x (ψ (x + h) - ψ x)‖
        ≤ ‖Ω x‖ * ‖ψ (x + h) - ψ x‖ := (Ω x).le_opNorm _
      _ ≤ MΩ * (K * h) := by
          have h1 : ‖ψ (x + h) - ψ x‖ ≤ K * h := by
            have := hK (x + h) x
            rwa [show x + h - x = h by ring,
              abs_of_pos hh] at this
          exact mul_le_mul (hMΩ x) h1 (norm_nonneg _) hMΩ0
  have hOmm : ‖Ω x (ψ (x - h)) - Ω x (ψ x)‖ ≤ MΩ * (K * h) := by
    rw [← map_sub]
    calc ‖Ω x (ψ (x - h) - ψ x)‖
        ≤ ‖Ω x‖ * ‖ψ (x - h) - ψ x‖ := (Ω x).le_opNorm _
      _ ≤ MΩ * (K * h) := by
          have h1 : ‖ψ (x - h) - ψ x‖ ≤ K * h := by
            have := hK (x - h) x
            rwa [show x - h - x = -h by ring, abs_neg,
              abs_of_pos hh] at this
          exact mul_le_mul (hMΩ x) h1 (norm_nonneg _) hMΩ0
  have hT2 : ‖(2 : ℝ)⁻¹ • ((Ω x (ψ (x + h)) - Ω x (ψ x))
        + (Ω x (ψ (x - h)) - Ω x (ψ x)))‖ ≤ MΩ * K * h := by
    rw [norm_smul, Real.norm_eq_abs,
      show |(2 : ℝ)⁻¹| = 2⁻¹ by norm_num]
    have h3 : ‖(Ω x (ψ (x + h)) - Ω x (ψ x))
          + (Ω x (ψ (x - h)) - Ω x (ψ x))‖
        ≤ 2 * (MΩ * (K * h)) := by
      calc ‖(Ω x (ψ (x + h)) - Ω x (ψ x))
              + (Ω x (ψ (x - h)) - Ω x (ψ x))‖
          ≤ ‖Ω x (ψ (x + h)) - Ω x (ψ x)‖
              + ‖Ω x (ψ (x - h)) - Ω x (ψ x)‖ := norm_add_le _ _
        _ ≤ MΩ * (K * h) + MΩ * (K * h) := add_le_add hOmp hOmm
        _ = 2 * (MΩ * (K * h)) := by ring
    calc (2 : ℝ)⁻¹ * ‖(Ω x (ψ (x + h)) - Ω x (ψ x))
            + (Ω x (ψ (x - h)) - Ω x (ψ x))‖
        ≤ (2 : ℝ)⁻¹ * (2 * (MΩ * (K * h))) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = MΩ * K * h := by ring
  have hEAp : ‖EA (ψ (x + h))‖ ≤ C * h ^ 2 * Mψ :=
    le_trans (EA.le_opNorm _)
      (mul_le_mul hA (hMψ _) (norm_nonneg _) (by positivity))
  have hEBm : ‖EB (ψ (x - h))‖ ≤ C * h ^ 2 * Mψ :=
    le_trans (EB.le_opNorm _)
      (mul_le_mul hB (hMψ _) (norm_nonneg _) (by positivity))
  have hT3 : ‖(2 * h)⁻¹ • (EA (ψ (x + h)) - EB (ψ (x - h)))‖
      ≤ C * Mψ * h := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < (2 * h)⁻¹)]
    have h3 : ‖EA (ψ (x + h)) - EB (ψ (x - h))‖
        ≤ 2 * (C * h ^ 2 * Mψ) := by
      calc ‖EA (ψ (x + h)) - EB (ψ (x - h))‖
          ≤ ‖EA (ψ (x + h))‖ + ‖EB (ψ (x - h))‖ := norm_sub_le _ _
        _ ≤ C * h ^ 2 * Mψ + C * h ^ 2 * Mψ := add_le_add hEAp hEBm
        _ = 2 * (C * h ^ 2 * Mψ) := by ring
    calc (2 * h)⁻¹ * ‖EA (ψ (x + h)) - EB (ψ (x - h))‖
        ≤ (2 * h)⁻¹ * (2 * (C * h ^ 2 * Mψ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = C * Mψ * h := by field_simp
  rw [hsplit]
  calc ‖((2 * h)⁻¹ • (ψ (x + h) - ψ (x - h)) - ψ' x)
        + (2 : ℝ)⁻¹ • ((Ω x (ψ (x + h)) - Ω x (ψ x))
            + (Ω x (ψ (x - h)) - Ω x (ψ x)))
        + (2 * h)⁻¹ • (EA (ψ (x + h)) - EB (ψ (x - h)))‖
      ≤ ‖((2 * h)⁻¹ • (ψ (x + h) - ψ (x - h)) - ψ' x)
          + (2 : ℝ)⁻¹ • ((Ω x (ψ (x + h)) - Ω x (ψ x))
              + (Ω x (ψ (x - h)) - Ω x (ψ x)))‖
        + ‖(2 * h)⁻¹ • (EA (ψ (x + h)) - EB (ψ (x - h)))‖ :=
        norm_add_le _ _
    _ ≤ ‖(2 * h)⁻¹ • (ψ (x + h) - ψ (x - h)) - ψ' x‖
          + ‖(2 : ℝ)⁻¹ • ((Ω x (ψ (x + h)) - Ω x (ψ x))
              + (Ω x (ψ (x - h)) - Ω x (ψ x)))‖
          + ‖(2 * h)⁻¹ • (EA (ψ (x + h)) - EB (ψ (x - h)))‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 2 * L * h + MΩ * K * h + C * Mψ * h :=
        add_le_add (add_le_add hT1 hT2) hT3
    _ = (2 * L + MΩ * K + C * Mψ) * h := by ring

/-- **Covariant central-difference L² consistency**
(`ass:scaling-package` (A5), varying-coefficient case): for compactly
supported Lipschitz data and continuous link/connection fields with
second-order link proximity, the squared L² distance of the covariant
central difference from `(∂ + Ω)ψ` is `O(h²)` with explicit
constant. -/
theorem covariant_difference_sq_integral
    {ψ ψ' : ℝ → E} {Ω A B : ℝ → E →L[ℝ] E}
    {L K MΩ Mψ C R : ℝ} (hC : 0 ≤ C) (hMψ0 : 0 ≤ Mψ)
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hLip : ∀ x y, ‖ψ' x - ψ' y‖ ≤ L * |x - y|)
    (hK : ∀ x y, ‖ψ x - ψ y‖ ≤ K * |x - y|)
    (hMψ : ∀ x, ‖ψ x‖ ≤ Mψ)
    (hMΩ : ∀ x, ‖Ω x‖ ≤ MΩ)
    (hAc : Continuous A) (hBc : Continuous B) (hΩc : Continuous Ω)
    (hsuppψ : ∀ x, x ∉ Icc (-R) R → ψ x = 0)
    (hsuppψ' : ∀ x, x ∉ Icc (-R) R → ψ' x = 0)
    (hR : 0 ≤ R) {h : ℝ} (hh : 0 < h)
    (hA : ∀ x, ‖A x - (1 + h • Ω x)‖ ≤ C * h ^ 2)
    (hB : ∀ x, ‖B x - (1 - h • Ω x)‖ ≤ C * h ^ 2) :
    (∫ x : ℝ, ‖(2 * h)⁻¹ • (A x (ψ (x + h)) - B x (ψ (x - h)))
        - (ψ' x + Ω x (ψ x))‖ ^ 2)
      ≤ ((2 * L + MΩ * K + C * Mψ) * h) ^ 2 * (2 * R + 2 * h) := by
  have hL0 : 0 ≤ L := lipschitz_const_nonneg hLip
  set F : ℝ → ℝ := fun x =>
    ‖(2 * h)⁻¹ • (A x (ψ (x + h)) - B x (ψ (x - h)))
      - (ψ' x + Ω x (ψ x))‖ ^ 2 with hF
  have hFbound : ∀ x, F x ≤ ((2 * L + MΩ * K + C * Mψ) * h) ^ 2 :=
    fun x => pow_le_pow_left₀ (norm_nonneg _)
      (covariant_difference_pointwise hC hMψ0 hψ hLip hK hMψ hMΩ
        x hh (hA x) (hB x)) 2
  have hmemψ : ∀ y : ℝ, (y < -R ∨ R < y) → ψ y = 0 := by
    intro y hy
    apply hsuppψ
    intro hmem
    obtain ⟨h1, h2⟩ := mem_Icc.mp hmem
    rcases hy with hy | hy <;> linarith
  have hmemψ' : ∀ y : ℝ, (y < -R ∨ R < y) → ψ' y = 0 := by
    intro y hy
    apply hsuppψ'
    intro hmem
    obtain ⟨h1, h2⟩ := mem_Icc.mp hmem
    rcases hy with hy | hy <;> linarith
  have hFzero : ∀ x, x ∉ Icc (-(R + h)) (R + h) → F x = 0 := by
    intro x hx
    have hx' : x < -(R + h) ∨ R + h < x := by
      by_cases h1 : -(R + h) ≤ x
      · right
        by_contra h2
        push Not at h2
        exact hx (mem_Icc.mpr ⟨h1, h2⟩)
      · left
        linarith
    have hzero : ψ (x + h) = 0 ∧ ψ (x - h) = 0 ∧ ψ' x = 0
        ∧ ψ x = 0 := by
      rcases hx' with hc | hc
      · exact ⟨hmemψ _ (Or.inl (by linarith)),
          hmemψ _ (Or.inl (by linarith)),
          hmemψ' _ (Or.inl (by linarith)),
          hmemψ _ (Or.inl (by linarith))⟩
      · exact ⟨hmemψ _ (Or.inr (by linarith)),
          hmemψ _ (Or.inr (by linarith)),
          hmemψ' _ (Or.inr (by linarith)),
          hmemψ _ (Or.inr (by linarith))⟩
    rw [hF]
    simp [hzero.1, hzero.2.1, hzero.2.2.1, hzero.2.2.2]
  have hψc : Continuous ψ :=
    continuous_iff_continuousAt.mpr
      fun x => (hψ x).differentiableAt.continuousAt
  have hψ'c : Continuous ψ' := by
    rw [Metric.continuous_iff]
    intro x ε hε
    by_cases hL : L = 0
    · refine ⟨1, one_pos, fun y _ => ?_⟩
      have hy := hLip y x
      rw [hL, zero_mul] at hy
      have h0 : ψ' y = ψ' x := by
        have := le_antisymm hy (norm_nonneg _)
        rwa [norm_sub_eq_zero_iff] at this
      rw [dist_eq_norm, h0]
      simpa using hε
    · have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
      refine ⟨ε / L, by positivity, fun y hy => ?_⟩
      rw [dist_eq_norm]
      calc ‖ψ' y - ψ' x‖ ≤ L * |y - x| := hLip y x
        _ < L * (ε / L) := by
            refine mul_lt_mul_of_pos_left ?_ hLpos
            rwa [← Real.dist_eq]
        _ = ε := by field_simp
  have hFc : Continuous F := by
    refine Continuous.pow ?_ 2
    refine Continuous.norm ?_
    refine Continuous.sub ?_ ?_
    · exact continuous_const.smul
        ((hAc.clm_apply
            (hψc.comp (continuous_id.add continuous_const))).sub
          (hBc.clm_apply
            (hψc.comp (continuous_id.sub continuous_const))))
    · exact hψ'c.add (hΩc.clm_apply hψc)
  have hFsupp : HasCompactSupport F :=
    HasCompactSupport.intro isCompact_Icc hFzero
  have hFint : Integrable F :=
    hFc.integrable_of_hasCompactSupport hFsupp
  set G : ℝ → ℝ :=
    (Icc (-(R + h)) (R + h)).indicator
      fun _ => ((2 * L + MΩ * K + C * Mψ) * h) ^ 2 with hG
  have hGint : Integrable G := by
    rw [hG, integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hle : ∀ x, F x ≤ G x := by
    intro x
    by_cases hx : x ∈ Icc (-(R + h)) (R + h)
    · rw [hG]
      simp only [indicator_of_mem hx]
      exact hFbound x
    · rw [hFzero x hx, hG]
      exact Set.indicator_nonneg (fun _ _ => by positivity) x
  calc (∫ x : ℝ, F x) ≤ ∫ x : ℝ, G x := integral_mono hFint hGint hle
    _ = (volume (Icc (-(R + h)) (R + h))).toReal
          • (((2 * L + MΩ * K + C * Mψ) * h) ^ 2 : ℝ) :=
        integral_indicator_const _ measurableSet_Icc
    _ = ((2 * L + MΩ * K + C * Mψ) * h) ^ 2 * (2 * R + 2 * h) := by
        rw [Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring

end NCG
