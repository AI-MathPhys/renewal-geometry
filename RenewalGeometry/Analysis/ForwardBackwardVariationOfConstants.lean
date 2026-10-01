/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Forward–backward variation of constants and the Green operator of a dichotomy

General machinery for the boundary-value contraction of the emergent-spacetime manuscript
(`eq:supp-exact-green`, `prop:supp-exact-boundary-residual`), on top of
`Analysis/AposterioriContractionResidual.lean`.

For a bounded operator `D` on a Banach space `E` and complementary projections `Π₊ + Π₋ = 1`
commuting with `D`, the forward–backward Green operator on `[0, S]` is
`(𝒢_S f)(s) = ∫₀ˢ e^{(s-r)D} Π₋ f(r) dr - ∫ₛˢ e^{(s-r)D} Π₊ f(r) dr`.

* `FBVariation.variation_of_constants`: every solution of `e' = D e + F` on `[0, S]`
  (continuous on `[0, S]`, differentiable inside, `F` continuous) satisfies
  `e(s) = e^{sD} Π₋ e(0) + e^{(s-S)D} Π₊ e(S) + (𝒢_S F)(s)`.
* `FBVariation.norm_green_le`: under the dichotomy bounds `‖e^{tD} Π₋‖ ≤ M_D`,
  `‖e^{-tD} Π₊‖ ≤ M_D` (`t ≥ 0`), `‖(𝒢_S f)(s)‖ ≤ M_D S sup‖f‖ ≤ M_D (1 + S) sup‖f‖`.
* `FBVariation.norm_boundary_le`: `‖e^{sD} Π₋ d₋ + e^{(s-S)D} Π₊ d₊‖ ≤ M_D(|d₋| + |d₊|)`.
* `FBVariation.aposteriori_sup_bound`: the sup-norm a-posteriori estimate
  `sup‖ẽ - e_*‖ ≤ (B + Γ sup‖r‖)/(1 - q)` for an exact solution `e_* = 𝒢(f + N e_*)` and an
  approximate one `ẽ = b + 𝒢(f + N ẽ + r)`, by iteration (no function-space completeness needed).
-/

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

namespace RenewalGeometry
namespace FBVariation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The exponential propagator `e^{tD}`. -/
noncomputable def prop (D : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E := NormedSpace.exp (t • D)

/-- The forward–backward Green operator `eq:supp-exact-green`. -/
noncomputable def green (D Pp Pm : E →L[ℝ] E) (S : ℝ) (f : ℝ → E) (s : ℝ) : E :=
  (∫ r in (0 : ℝ)..s, prop D (s - r) (Pm (f r))) - ∫ r in s..S, prop D (s - r) (Pp (f r))

theorem hasDerivAt_prop (D : E →L[ℝ] E) (t : ℝ) :
    HasDerivAt (prop D) (prop D t * D) t := by
  unfold prop
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) D t

theorem continuous_prop (D : E →L[ℝ] E) : Continuous (prop D) := by
  refine continuous_iff_continuousAt.mpr fun t => (hasDerivAt_prop D t).continuousAt

theorem prop_commute (D P : E →L[ℝ] E) (hP : Commute D P) (t : ℝ) :
    prop D t * P = P * prop D t := by
  unfold prop
  exact (hP.smul_left t).exp_left.eq

/-- Derivative of `r ↦ e^{(s-r)D} P e(r)` along a solution of `e' = D e + F`. -/
theorem hasDerivAt_conj (D P : E →L[ℝ] E) (hP : Commute D P) (s : ℝ) {e F : ℝ → E} {r : ℝ}
    (he : HasDerivAt e (D (e r) + F r) r) :
    HasDerivAt (fun r => prop D (s - r) (P (e r))) (prop D (s - r) (P (F r))) r := by
  have h1 : HasDerivAt (fun r => prop D (s - r)) (-(prop D (s - r) * D)) r := by
    have := (hasDerivAt_prop D (s - r)).scomp r ((hasDerivAt_id r).const_sub s)
    exact this.congr_deriv (by simp)
  have h2 : HasDerivAt (fun r => P (e r)) (P (D (e r) + F r)) r :=
    P.hasFDerivAt.comp_hasDerivAt r he
  have h3 := h1.clm_apply h2
  convert h3 using 1
  have hc : P * D = D * P := hP.eq.symm
  have : P (D (e r)) = D (P (e r)) := by
    rw [← ContinuousLinearMap.mul_apply, hc, ContinuousLinearMap.mul_apply]
  simp only [map_add, ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply, this]
  abel

/-- **Forward–backward variation of constants.** -/
theorem variation_of_constants (D Pp Pm : E →L[ℝ] E) (hsum : Pp + Pm = 1)
    (hp : Commute D Pp) (hm : Commute D Pm) {S : ℝ} {e F : ℝ → E}
    (hcont : ContinuousOn e (Icc 0 S)) (hF : ContinuousOn F (Icc 0 S))
    (hde : ∀ r ∈ Ioo 0 S, HasDerivAt e (D (e r) + F r) r) {s : ℝ} (hs : s ∈ Icc 0 S) :
    e s = prop D s (Pm (e 0)) + prop D (s - S) (Pp (e S)) + green D Pp Pm S F s := by
  have hint : ∀ (P : E →L[ℝ] E) (a b : ℝ), Icc a b ⊆ Icc 0 S → a ≤ b →
      IntervalIntegrable (fun r => prop D (s - r) (P (F r))) volume a b := by
    intro P a b hsub hab
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    have hc1 : ContinuousOn (fun r => prop D (s - r)) (Icc a b) :=
      ((continuous_prop D).comp (continuous_const.sub continuous_id)).continuousOn
    exact hc1.clm_apply ((P.continuous.comp_continuousOn (hF.mono hsub)))
  have hftc : ∀ (P : E →L[ℝ] E), Commute D P → ∀ a b, 0 ≤ a → a ≤ b → b ≤ S →
      ∫ r in a..b, prop D (s - r) (P (F r))
        = prop D (s - b) (P (e b)) - prop D (s - a) (P (e a)) := by
    intro P hP a b ha hab hb
    have hsub : Icc a b ⊆ Icc 0 S := Icc_subset_Icc ha hb
    refine integral_eq_sub_of_hasDeriv_right_of_le (f := fun r => prop D (s - r) (P (e r))) hab
      ?_ ?_ (hint P a b hsub hab)
    · have hc1 : ContinuousOn (fun r => prop D (s - r)) (Icc a b) :=
        ((continuous_prop D).comp (continuous_const.sub continuous_id)).continuousOn
      exact hc1.clm_apply (P.continuous.comp_continuousOn (hcont.mono hsub))
    · intro x hx
      have hx' : x ∈ Ioo 0 S := ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩
      exact (hasDerivAt_conj D P hP s (hde x hx')).hasDerivWithinAt
  have h1 := hftc Pm hm 0 s le_rfl hs.1 hs.2
  have h2 := hftc Pp hp s S hs.1 hs.2 le_rfl
  have hp0 : prop D 0 = 1 := by simp [prop]
  rw [green, h1, h2, sub_self, hp0, sub_zero]
  have hsplit : e s = Pp (e s) + Pm (e s) := by
    rw [← ContinuousLinearMap.add_apply, hsum, ContinuousLinearMap.one_apply]
  simp only [ContinuousLinearMap.one_apply]
  conv_lhs => rw [hsplit]
  abel

theorem intervalIntegrable_conj (D P : E →L[ℝ] E) {S s a b : ℝ} {f : ℝ → E}
    (hf : ContinuousOn f (Icc 0 S)) (hsub : Icc a b ⊆ Icc 0 S) (hab : a ≤ b) :
    IntervalIntegrable (fun r => prop D (s - r) (P (f r))) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  have hc1 : ContinuousOn (fun r => prop D (s - r)) (Icc a b) :=
    ((continuous_prop D).comp (continuous_const.sub continuous_id)).continuousOn
  exact hc1.clm_apply ((P.continuous.comp_continuousOn (hf.mono hsub)))

/-- Linearity of the Green operator on functions continuous on `[0, S]`. -/
theorem green_sub (D Pp Pm : E →L[ℝ] E) {S : ℝ} {f g : ℝ → E} (hf : ContinuousOn f (Icc 0 S))
    (hg : ContinuousOn g (Icc 0 S)) {s : ℝ} (hs : s ∈ Icc 0 S) :
    green D Pp Pm S f s - green D Pp Pm S g s = green D Pp Pm S (fun r => f r - g r) s := by
  have h1 := intervalIntegral.integral_sub
    (intervalIntegrable_conj D Pm (s := s) hf (Icc_subset_Icc le_rfl hs.2) hs.1)
    (intervalIntegrable_conj D Pm (s := s) hg (Icc_subset_Icc le_rfl hs.2) hs.1)
  have h2 := intervalIntegral.integral_sub
    (intervalIntegrable_conj D Pp (s := s) hf (Icc_subset_Icc hs.1 le_rfl) hs.2)
    (intervalIntegrable_conj D Pp (s := s) hg (Icc_subset_Icc hs.1 le_rfl) hs.2)
  simp only [green, map_sub]
  rw [h1, h2]
  abel

/-- **Green bound.**  Under `‖e^{tD} Π₋‖ ≤ M` and `‖e^{-tD} Π₊‖ ≤ M` for `t ≥ 0`, and
`‖f‖ ≤ K` on `[0, S]`, `‖(𝒢_S f)(s)‖ ≤ M S K` for `s ∈ [0, S]`. -/
theorem norm_green_le (D Pp Pm : E →L[ℝ] E) {S M K : ℝ}
    (hm : ∀ t, 0 ≤ t → ‖prop D t * Pm‖ ≤ M) (hp : ∀ t, 0 ≤ t → ‖prop D (-t) * Pp‖ ≤ M)
    {f : ℝ → E} (hf : ∀ r ∈ Icc 0 S, ‖f r‖ ≤ K) {s : ℝ} (hs : s ∈ Icc 0 S) :
    ‖green D Pp Pm S f s‖ ≤ M * S * K := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hf s hs)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hm 0 le_rfl)
  have b1 : ‖∫ r in (0 : ℝ)..s, prop D (s - r) (Pm (f r))‖ ≤ M * K * (s - 0) := by
    rw [← abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s - 0)]
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro r hr
    rw [uIoc_of_le hs.1] at hr
    have hr' : r ∈ Icc 0 S := ⟨hr.1.le, hr.2.trans hs.2⟩
    calc ‖prop D (s - r) (Pm (f r))‖ = ‖(prop D (s - r) * Pm) (f r)‖ := rfl
      _ ≤ ‖prop D (s - r) * Pm‖ * ‖f r‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * K := mul_le_mul (hm _ (by linarith [hr.2])) (hf r hr') (norm_nonneg _) hM
  have b2 : ‖∫ r in s..S, prop D (s - r) (Pp (f r))‖ ≤ M * K * (S - s) := by
    rw [← abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ S - s)]
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro r hr
    rw [uIoc_of_le hs.2] at hr
    have hr' : r ∈ Icc 0 S := ⟨hs.1.trans hr.1.le, hr.2⟩
    have : s - r = -(r - s) := by ring
    calc ‖prop D (s - r) (Pp (f r))‖ = ‖(prop D (-(r - s)) * Pp) (f r)‖ := by rw [this]; rfl
      _ ≤ ‖prop D (-(r - s)) * Pp‖ * ‖f r‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * K := mul_le_mul (hp _ (by linarith [hr.1])) (hf r hr') (norm_nonneg _) hM
  unfold green
  calc ‖(∫ r in (0 : ℝ)..s, prop D (s - r) (Pm (f r))) - ∫ r in s..S, prop D (s - r) (Pp (f r))‖
      ≤ M * K * (s - 0) + M * K * (S - s) := (norm_sub_le _ _).trans (add_le_add b1 b2)
    _ = M * S * K := by ring

/-- **Boundary terms.**  `‖e^{sD} Π₋ d₋ + e^{(s-S)D} Π₊ d₊‖ ≤ M (‖d₋‖ + ‖d₊‖)` on `[0, S]`. -/
theorem norm_boundary_le (D Pp Pm : E →L[ℝ] E) {S M : ℝ}
    (hm : ∀ t, 0 ≤ t → ‖prop D t * Pm‖ ≤ M) (hp : ∀ t, 0 ≤ t → ‖prop D (-t) * Pp‖ ≤ M)
    (dm dp : E) {s : ℝ} (hs : s ∈ Icc 0 S) :
    ‖prop D s (Pm dm) + prop D (s - S) (Pp dp)‖ ≤ M * (‖dm‖ + ‖dp‖) := by
  have h1 : ‖prop D s (Pm dm)‖ ≤ M * ‖dm‖ :=
    ((prop D s * Pm).le_opNorm dm).trans
      (mul_le_mul_of_nonneg_right (hm s hs.1) (norm_nonneg _))
  have h2 : ‖prop D (s - S) (Pp dp)‖ ≤ M * ‖dp‖ := by
    have : s - S = -(S - s) := by ring
    rw [this]
    exact ((prop D (-(S - s)) * Pp).le_opNorm dp).trans
      (mul_le_mul_of_nonneg_right (hp _ (by linarith [hs.2])) (norm_nonneg _))
  calc _ ≤ ‖prop D s (Pm dm)‖ + ‖prop D (s - S) (Pp dp)‖ := norm_add_le _ _
    _ ≤ M * ‖dm‖ + M * ‖dp‖ := add_le_add h1 h2
    _ = M * (‖dm‖ + ‖dp‖) := by ring

/-- **Sup-norm a-posteriori estimate by iteration.**  Let `Δ(s) = ‖ẽ(s) - e_*(s)‖` be bounded
on a set `I` by `Δ₀`, and suppose that whenever `Δ ≤ c` on `I`, then `Δ ≤ B + q c` on `I`
(the contraction step: boundary terms `B`, residual included in `B`, Lipschitz factor `q < 1`).
Then `Δ ≤ B / (1 - q)` on `I`. -/
theorem aposteriori_sup_bound {I : Set ℝ} {Δ : ℝ → ℝ} {B q Δ₀ : ℝ} (hq0 : 0 ≤ q) (hq : q < 1)
    (h0 : ∀ s ∈ I, Δ s ≤ Δ₀) (hstep : ∀ c, (∀ s ∈ I, Δ s ≤ c) → ∀ s ∈ I, Δ s ≤ B + q * c) :
    ∀ s ∈ I, Δ s ≤ B / (1 - q) := by
  -- after `n` steps: `Δ ≤ B (1 - qⁿ)/(1 - q) + qⁿ Δ₀`
  have hiter : ∀ n : ℕ, ∀ s ∈ I, Δ s ≤ B * (1 - q ^ n) / (1 - q) + q ^ n * Δ₀ := by
    intro n
    induction n with
    | zero => intro s hs; simpa using h0 s hs
    | succ n ih =>
      intro s hs
      have := hstep _ ih s hs
      have h1q : (1 - q) ≠ 0 := by linarith
      calc Δ s ≤ B + q * (B * (1 - q ^ n) / (1 - q) + q ^ n * Δ₀) := this
        _ = B * (1 - q ^ (n + 1)) / (1 - q) + q ^ (n + 1) * Δ₀ := by
            field_simp; ring
  intro s hs
  have hlim : Tendsto (fun n : ℕ => B * (1 - q ^ n) / (1 - q) + q ^ n * Δ₀) atTop
      (𝓝 (B * (1 - 0) / (1 - q) + 0 * Δ₀)) := by
    have hqn := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq
    exact (((tendsto_const_nhds.sub hqn).const_mul B).div_const _).add (hqn.mul_const _)
  simp only [sub_zero, mul_one, zero_mul, add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => hiter n s hs)

/-- **`eq:supp-exact-residual-bound`, abstract form.**  Let `e_*` solve the Green fixed-point
equation `e_* = 𝒢_S(f + N e_*)` and let `ẽ` satisfy `ẽ' = Dẽ + f + N ẽ + r` on `[0, S]`
(the equation of `w̃ - w_ref` for an approximate history `w̃` with residual `r`).  If `N` is
`L`-Lipschitz on the values of both curves, the dichotomy bounds hold with constant `M`, and
`q = M S L < 1`, then with `d₋ = Π₋ ẽ(0)`, `d₊ = Π₊ ẽ(S)` (and idempotent projections)
`sup ‖ẽ - e_*‖ ≤ (M(|d₋| + |d₊|) + M S sup‖r‖)/(1 - q)`. -/
theorem boundary_residual_bound (D Pp Pm : E →L[ℝ] E) (hsum : Pp + Pm = 1)
    (hpc : Commute D Pp) (hmc : Commute D Pm) (hPp : Pp * Pp = Pp) (hPm : Pm * Pm = Pm)
    {S M L Kr Δ₀ : ℝ} (hS : 0 ≤ S) (hm : ∀ t, 0 ≤ t → ‖prop D t * Pm‖ ≤ M)
    (hp : ∀ t, 0 ≤ t → ‖prop D (-t) * Pp‖ ≤ M) (hL : 0 ≤ L) (hq : M * S * L < 1)
    {f : ℝ → E} {N : ℝ → E → E} {es et res : ℝ → E}
    (hfix : ∀ s ∈ Icc 0 S, es s = green D Pp Pm S (fun r => f r + N r (es r)) s)
    (hcont : ContinuousOn et (Icc 0 S))
    (hFc : ContinuousOn (fun s => f s + N s (et s) + res s) (Icc 0 S))
    (hde : ∀ s ∈ Ioo 0 S, HasDerivAt et (D (et s) + (f s + N s (et s) + res s)) s)
    (hNL : ∀ s ∈ Icc 0 S, ‖N s (et s) - N s (es s)‖ ≤ L * ‖et s - es s‖)
    (hr : ∀ s ∈ Icc 0 S, ‖res s‖ ≤ Kr)
    (hFs : ContinuousOn (fun s => f s + N s (es s)) (Icc 0 S))
    (h0 : ∀ s ∈ Icc 0 S, ‖et s - es s‖ ≤ Δ₀) :
    ∀ s ∈ Icc 0 S, ‖et s - es s‖
      ≤ (M * (‖Pm (et 0)‖ + ‖Pp (et S)‖) + M * S * Kr) / (1 - M * S * L) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hm 0 le_rfl)
  refine aposteriori_sup_bound (by positivity) hq h0 ?_
  intro c hc s hs
  have hvoc := variation_of_constants D Pp Pm hsum hpc hmc hcont hFc hde hs
  -- idempotence rewrites the boundary terms through `d₋, d₊`
  have hb1 : Pm (et 0) = Pm (Pm (et 0)) := by
    rw [← ContinuousLinearMap.mul_apply, hPm]
  have hb2 : Pp (et S) = Pp (Pp (et S)) := by
    rw [← ContinuousLinearMap.mul_apply, hPp]
  have hdiff : et s - es s = (prop D s (Pm (Pm (et 0))) + prop D (s - S) (Pp (Pp (et S))))
      + green D Pp Pm S (fun r => (N r (et r) - N r (es r)) + res r) s := by
    have hlin := green_sub D Pp Pm hFc hFs hs
    have hfun : (fun r => (f r + N r (et r) + res r) - (f r + N r (es r)))
        = fun r => (N r (et r) - N r (es r)) + res r := by
      funext r; abel
    rw [hfun] at hlin
    rw [hvoc, hfix s hs, ← hb1, ← hb2, ← hlin]
    abel
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc s hs)
  have hg : ‖green D Pp Pm S (fun r => (N r (et r) - N r (es r)) + res r) s‖
      ≤ M * S * (L * c + Kr) := by
    refine norm_green_le D Pp Pm hm hp (fun r hr' => ?_) hs
    exact (norm_add_le _ _).trans (add_le_add ((hNL r hr').trans
      (mul_le_mul_of_nonneg_left (hc r hr') hL)) (hr r hr'))
  rw [hdiff]
  calc _ ≤ ‖prop D s (Pm (Pm (et 0))) + prop D (s - S) (Pp (Pp (et S)))‖
        + ‖green D Pp Pm S (fun r => (N r (et r) - N r (es r)) + res r) s‖ := norm_add_le _ _
    _ ≤ M * (‖Pm (et 0)‖ + ‖Pp (et S)‖) + M * S * (L * c + Kr) :=
        add_le_add (norm_boundary_le D Pp Pm hm hp _ _ hs) hg
    _ = M * (‖Pm (et 0)‖ + ‖Pp (et S)‖) + M * S * Kr + M * S * L * c := by ring

end FBVariation
end RenewalGeometry
