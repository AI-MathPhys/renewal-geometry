/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.AposterioriPhysicalShadow

/-!
# A transparent data-centred rate (`cor:aposteriori-shadow-rate`)

Einstein–Standard-Model action-closure manuscript, `cor:aposteriori-shadow-rate`: for `k = 4`,
`s = 10`, `q ≥ 15` and one certified reader-energy radius, `s_h = O(h)` and `β_h = O(h^{1/2})` give
`ε_h = O_R(h)`, `η_{h,4} = O_R(h^{1/2})`, `𝔡_h = O_R(h^{1/2})` (`eq:aposteriori-rate-output`), and
the
exact physical shadow differs from the normalized record by `O_R(h^{1/2})`.

## Exponent bookkeeping (standalone, proved)

* `shadowEta` — `η_{h,k} = C_R(ε^{1-k/s} + ε^{1-(k+1)/s})` (`eq:shadow-eta`); `shadowEta_mono`
  (monotone in `ε` for `s ≥ k + 1`), `shadowEta_nonneg`.
* `rate_indices` — `(k, s, q) = (4, 10, 15)` satisfies `eq:shadow-regularity-indices`
  (`q > s + 4`, `s > k + 1`, `k ≥ 4`), and the interpolation exponents are `1 - 4/10 = 3/5`
  (bosonic) and `1 - 5/10 = 1/2` (Dirac).
* `eps_le_of_rate` — `ε_h ≤ C_R(s_h + h)` and `s_h ≤ C_s h` give `ε_h ≤ C_R(C_s + 1) h`.
* `shadowEta_four_ten_le` — `0 ≤ ε ≤ A h`, `0 < h ≤ 1` give
  `η_{h,4} ≤ C_R(A^{3/5} + A^{1/2}) h^{1/2}` (`O(h^{3/5} + h^{1/2}) = O(h^{1/2})`).
* `shadowBudget_le_of_rate` — `β_h ≤ C_β h^{1/2}`, `η ≤ C_η h^{1/2}` give `𝔡_h ≤ C h^{1/2}`.
* `aposteriori_rate_isBigO` — the three `O`-statements of `eq:aposteriori-rate-output` along any
  filter.

## Composition

* `aposteriori_shadow_rate` — along `h → 0⁺`: the shadow theorem
  (`AposterioriShadow.aposteriori_physical_shadow`, conditional on the conclusion of the open
  `prop:coupled-bootstrap`) applies eventually (the budget tends to zero, so it eventually lies
  below
  the uniform stability radius) and the shadow distance is `≤ C h^{1/2}`.
-/

open Filter Topology Asymptotics Metric

namespace RenewalGeometry.AposterioriShadowRate

open AposterioriShadow

noncomputable section

/-- `η_{h,k} = C_R(ε^{1-k/s} + ε^{1-(k+1)/s})` (`eq:shadow-eta`). -/
def shadowEta (CR k s ε : ℝ) : ℝ := CR * (ε ^ (1 - k / s) + ε ^ (1 - (k + 1) / s))

theorem shadowEta_nonneg {CR k s ε : ℝ} (hCR : 0 ≤ CR) (hε : 0 ≤ ε) : 0 ≤ shadowEta CR k s ε :=
  mul_nonneg hCR (add_nonneg (Real.rpow_nonneg hε _) (Real.rpow_nonneg hε _))

/-- `η_{h,k}` is monotone in `ε ≥ 0` when `0 ≤ k`, `k + 1 ≤ s` (both exponents are `≥ 0`); so an
upper bound `ε_h ≤ C_R(s_h + h)` can be inserted in `eq:shadow-eta`. -/
theorem shadowEta_mono {CR k s ε ε' : ℝ} (hCR : 0 ≤ CR) (hk : 0 ≤ k) (hks : k + 1 ≤ s)
    (hε : 0 ≤ ε) (hεε' : ε ≤ ε') : shadowEta CR k s ε ≤ shadowEta CR k s ε' := by
  have hs : 0 < s := by linarith
  have h1 : 0 ≤ 1 - k / s := by rw [sub_nonneg, div_le_one hs]; linarith
  have h2 : 0 ≤ 1 - (k + 1) / s := by rw [sub_nonneg, div_le_one hs]; linarith
  unfold shadowEta
  exact mul_le_mul_of_nonneg_left (add_le_add (Real.rpow_le_rpow hε hεε' h1)
    (Real.rpow_le_rpow hε hεε' h2)) hCR

/-- **The indices and exponents of `cor:aposteriori-shadow-rate`**: `(k, s, q) = (4, 10, 15)`
satisfies `eq:shadow-regularity-indices` and the interpolation exponents are `3/5` and `1/2`. -/
theorem rate_indices :
    (10 + 4 < 15 ∧ 4 + 1 < 10 ∧ 4 ≤ 4) ∧
      (1 : ℝ) - (4 : ℝ) / 10 = 3 / 5 ∧ (1 : ℝ) - ((4 : ℝ) + 1) / 10 = 1 / 2 := by
  refine ⟨⟨by norm_num, by norm_num, le_rfl⟩, by norm_num, by norm_num⟩

theorem shadowEta_four_ten (CR ε : ℝ) :
    shadowEta CR 4 10 ε = CR * (ε ^ (3 / 5 : ℝ) + ε ^ (1 / 2 : ℝ)) := by
  unfold shadowEta; norm_num

/-- `ε_h ≤ C_R(s_h + h)` with `s_h ≤ C_s h` gives `ε_h ≤ C_R(C_s + 1)h` (`ε_h = O_R(h)`). -/
theorem eps_le_of_rate {CR Cs s h ε : ℝ} (hCR : 0 ≤ CR) (hε : ε ≤ CR * (s + h))
    (hs : s ≤ Cs * h) : ε ≤ CR * (Cs + 1) * h := by
  calc ε ≤ CR * (s + h) := hε
    _ ≤ CR * (Cs * h + h) := mul_le_mul_of_nonneg_left (by linarith) hCR
    _ = CR * (Cs + 1) * h := by ring

/-- **`η_{h,4} = O(h^{3/5} + h^{1/2}) = O(h^{1/2})`** pointwise: for `0 ≤ ε ≤ A h`,
`0 < h ≤ 1`, `η_{h,4} ≤ C_R(A^{3/5} + A^{1/2}) h^{1/2}`. -/
theorem shadowEta_four_ten_le {CR A h ε : ℝ} (hCR : 0 ≤ CR) (hA : 0 ≤ A) (hh0 : 0 < h)
    (hh1 : h ≤ 1) (hε : 0 ≤ ε) (hεA : ε ≤ A * h) :
    shadowEta CR 4 10 ε ≤ CR * (A ^ (3 / 5 : ℝ) + A ^ (1 / 2 : ℝ)) * h ^ (1 / 2 : ℝ) := by
  rw [shadowEta_four_ten]
  have h35 : ε ^ (3 / 5 : ℝ) ≤ A ^ (3 / 5 : ℝ) * h ^ (1 / 2 : ℝ) := by
    calc ε ^ (3 / 5 : ℝ) ≤ (A * h) ^ (3 / 5 : ℝ) := Real.rpow_le_rpow hε hεA (by norm_num)
      _ = A ^ (3 / 5 : ℝ) * h ^ (3 / 5 : ℝ) := Real.mul_rpow hA hh0.le
      _ ≤ A ^ (3 / 5 : ℝ) * h ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hh0 hh1 (by norm_num))
          (Real.rpow_nonneg hA _)
  have h12 : ε ^ (1 / 2 : ℝ) ≤ A ^ (1 / 2 : ℝ) * h ^ (1 / 2 : ℝ) := by
    calc ε ^ (1 / 2 : ℝ) ≤ (A * h) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hε hεA (by norm_num)
      _ = A ^ (1 / 2 : ℝ) * h ^ (1 / 2 : ℝ) := Real.mul_rpow hA hh0.le
  calc CR * (ε ^ (3 / 5 : ℝ) + ε ^ (1 / 2 : ℝ))
      ≤ CR * (A ^ (3 / 5 : ℝ) * h ^ (1 / 2 : ℝ) + A ^ (1 / 2 : ℝ) * h ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add h35 h12) hCR
    _ = CR * (A ^ (3 / 5 : ℝ) + A ^ (1 / 2 : ℝ)) * h ^ (1 / 2 : ℝ) := by ring

/-- **`𝔡_h = O(h^{1/2})`** pointwise: `β_h ≤ C_β h^{1/2}`, `η ≤ C_η h^{1/2}` give
`𝔡_h = 2B_*γ_*⁻¹β_h + C_R√T η ≤ (2B_*γ_*⁻¹C_β + C_R√T C_η) h^{1/2}`. -/
theorem shadowBudget_le_of_rate {B γ β c τ η Cβ Cη h : ℝ} (hB : 0 ≤ B) (hγ : 0 ≤ γ) (hc : 0 ≤ c)
    (hβ : β ≤ Cβ * h ^ (1 / 2 : ℝ)) (hη : η ≤ Cη * h ^ (1 / 2 : ℝ)) :
    shadowBudget B γ β c τ η ≤ (2 * B * γ⁻¹ * Cβ + c * Real.sqrt τ * Cη) * h ^ (1 / 2 : ℝ) := by
  unfold shadowBudget
  have h1 : 2 * B * γ⁻¹ * β ≤ 2 * B * γ⁻¹ * (Cβ * h ^ (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hβ (by positivity)
  have h2 : c * Real.sqrt τ * η ≤ c * Real.sqrt τ * (Cη * h ^ (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hη (by positivity)
  nlinarith

/-- **`eq:aposteriori-rate-output`** along any filter: if eventually `0 < h ≤ 1`,
`0 ≤ s_h ≤ C_s h` (`s_h = O(h)`), `0 ≤ ε_h ≤ C_R(s_h + h)` (`eq:shadow-zero-residual`) and
`0 ≤ β_h ≤ C_β h^{1/2}` (`β_h = O(h^{1/2})`), then `ε_h = O(h)`, `η_{h,4} = O(h^{1/2})` and
`𝔡_h = O(h^{1/2})`. -/
theorem aposteriori_rate_isBigO {ι : Type*} {l : Filter ι} {h s ε β : ι → ℝ}
    {CR Cs Cβ B γ c τ : ℝ} (hCR : 0 ≤ CR) (hCs : 0 ≤ Cs) (hB : 0 ≤ B) (hγ : 0 ≤ γ) (hc : 0 ≤ c)
    (hev : ∀ᶠ i in l, 0 < h i ∧ h i ≤ 1 ∧ 0 ≤ s i ∧ s i ≤ Cs * h i ∧ 0 ≤ ε i ∧
      ε i ≤ CR * (s i + h i) ∧ 0 ≤ β i ∧ β i ≤ Cβ * h i ^ (1 / 2 : ℝ)) :
    ε =O[l] h ∧ (fun i => shadowEta CR 4 10 (ε i)) =O[l] (fun i => h i ^ (1 / 2 : ℝ)) ∧
      (fun i => shadowBudget B γ (β i) c τ (shadowEta CR 4 10 (ε i))) =O[l]
        (fun i => h i ^ (1 / 2 : ℝ)) := by
  set A := CR * (Cs + 1) with hAdef
  have hA : 0 ≤ A := by positivity
  set Cη := CR * (A ^ (3 / 5 : ℝ) + A ^ (1 / 2 : ℝ)) with hCη
  refine ⟨?_, ?_, ?_⟩
  · refine IsBigO.of_bound A ?_
    filter_upwards [hev] with i hi
    obtain ⟨hh0, -, -, hs, hε0, hε, -, -⟩ := hi
    rw [Real.norm_of_nonneg hε0, Real.norm_of_nonneg hh0.le]
    exact eps_le_of_rate hCR hε hs
  · refine IsBigO.of_bound Cη ?_
    filter_upwards [hev] with i hi
    obtain ⟨hh0, hh1, -, hs, hε0, hε, -, -⟩ := hi
    rw [Real.norm_of_nonneg (shadowEta_nonneg hCR hε0),
      Real.norm_of_nonneg (Real.rpow_nonneg hh0.le _)]
    exact shadowEta_four_ten_le hCR hA hh0 hh1 hε0 (eps_le_of_rate hCR hε hs)
  · refine IsBigO.of_bound (|2 * B * γ⁻¹ * Cβ + c * Real.sqrt τ * Cη|) ?_
    filter_upwards [hev] with i hi
    obtain ⟨hh0, hh1, -, hs, hε0, hε, hβ0, hβ⟩ := hi
    have hη := shadowEta_four_ten_le hCR hA hh0 hh1 hε0 (eps_le_of_rate hCR hε hs)
    have hle := shadowBudget_le_of_rate (τ := τ) hB hγ hc hβ hη
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hh0.le _)]
    have hη0 : 0 ≤ shadowEta CR 4 10 (ε i) := shadowEta_nonneg hCR hε0
    have hb0 : 0 ≤ shadowBudget B γ (β i) c τ (shadowEta CR 4 10 (ε i)) := by
      unfold shadowBudget; positivity
    rw [Real.norm_of_nonneg hb0]
    exact hle.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hh0.le _))

/-! ### Composition with the shadow theorem -/

/-- **`cor:aposteriori-shadow-rate`** (conditional on the conclusion of the open
`prop:coupled-bootstrap`, through `AposterioriShadow.aposteriori_physical_shadow`).  Take `k = 4`,
`s = 10` (`rate_indices`), a family of normalized records `ẑ_h` (admissible, harmonic) with the
forcing output of `prop:shadow-residual-upgrade`, `‖𝓡_B‖ + ‖𝓡_D‖ ≤ η_{h,4} = C_R(ε_h^{3/5} +
ε_h^{1/2})`,
`0 ≤ ε_h ≤ C_R(s_h + h)`, the exact reductions with uniform retraction margins, `s_h = O(h)`
(`0 ≤ s_h ≤ C_s h`) and `β_h = O(h^{1/2})`.  Along `h → 0⁺` the budget `𝔡_h = O(h^{1/2})` tends to
zero, so it eventually lies below the uniform stability radius, and the exact physical shadow
differs from the normalized record by `O(h^{1/2})` in the norms of
`eq:aposteriori-physical-shadow`. -/
theorem aposteriori_shadow_rate {Z X O : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [PseudoMetricSpace O] {Y : Type*} [AddCommGroup Y] [Module ℝ Y] (M : SlabModel Z X O)
    {Ck : X → Y} (T : CauchyTube M Ck)
    (hboot : CoupledBootstrapConclusion M T.family T.dstar T.Cstar)
    {ι : Type*} {l : Filter ι} {h s ε β : ι → ℝ} (hh : Tendsto h l (𝓝[>] 0))
    (zh : ι → Z) (hadm : ∀ i, M.Admissible (zh i)) (hharm : ∀ i, M.harm (zh i) = 0)
    {m : ι → ℕ} {r B γ CR Cs Cβ c τ : ℝ}
    (R : ∀ i, ExactInitialConstraintReduction Ck (M.init (zh i)) (m i) r B) (hγ : 0 < γ)
    (hA : ∀ i, ∀ v, γ * ‖v‖ ≤ ‖fderivWithin ℝ (R i).retained (closedBall 0 r) 0 v‖)
    (hmargin : ∀ i, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (m i))) r,
      ‖fderivWithin ℝ (R i).retained (closedBall 0 r) x -
        fderivWithin ℝ (R i).retained (closedBall 0 r) 0‖ ≤ γ / 2)
    (hres : ∀ i, ‖(R i).retained 0‖ ≤ β i) (hrad : ∀ i, 2 * γ⁻¹ * β i ≤ r) (hB : 0 ≤ B)
    (htube : ∀ i, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (m i))) (2 * γ⁻¹ * β i),
      (R i).retained x = 0 → (R i).corr x ∈ T.Creg ∩ T.nbhd)
    (hc : 0 < c) (hτ : 0 < τ) (hCR : 0 ≤ CR) (hCs : 0 ≤ Cs)
    (hrate : ∀ᶠ i in l, 0 ≤ s i ∧ s i ≤ Cs * h i ∧ 0 ≤ ε i ∧ ε i ≤ CR * (s i + h i) ∧
      β i ≤ Cβ * h i ^ (1 / 2 : ℝ))
    (hforce : ∀ i, M.resB (zh i) + M.resD (zh i) ≤ shadowEta CR 4 10 (ε i)) :
    ∃ C : ℝ, ∀ᶠ i in l, ∃ x : EuclideanSpace ℝ (Fin (m i)), (R i).retained x = 0 ∧
      Ck ((R i).corr x) = 0 ∧ M.IsExact (T.evolve ((R i).corr x)) ∧
      (∀ z, M.IsExact z → M.init z = (R i).corr x → z = T.evolve ((R i).corr x)) ∧
      dist (M.obs (zh i)) (M.obs (T.evolve ((R i).corr x))) ≤ C * h i ^ (1 / 2 : ℝ) := by
  set A := CR * (Cs + 1) with hAdef
  have hA0 : 0 ≤ A := by positivity
  set Cη := CR * (A ^ (3 / 5 : ℝ) + A ^ (1 / 2 : ℝ)) with hCη
  set Cb := 2 * B * γ⁻¹ * Cβ + c * Real.sqrt τ * Cη with hCb
  -- eventually `0 < h ≤ 1` and `|C_b| h^{1/2}` is below the stability radius
  have hpos : ∀ᶠ i in l, 0 < h i := (tendsto_nhdsWithin_iff.mp hh).2
  have h0 : Tendsto h l (𝓝 0) := (tendsto_nhdsWithin_iff.mp hh).1
  have hle1 : ∀ᶠ i in l, h i ≤ 1 := h0.eventually (ge_mem_nhds one_pos)
  have hsq : Tendsto (fun i => |Cb| * h i ^ (1 / 2 : ℝ)) l (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 (1 / 2 : ℝ) (Or.inr (by norm_num))).tendsto.comp
      h0).const_mul |Cb|
    simpa [Function.comp_def, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using this
  have hsmallev : ∀ᶠ i in l, |Cb| * h i ^ (1 / 2 : ℝ) < T.stabilityRadius c τ :=
    hsq.eventually (gt_mem_nhds (T.stabilityRadius_pos hc hτ))
  refine ⟨T.shadowConst c τ * |Cb|, ?_⟩
  filter_upwards [hpos, hle1, hrate, hsmallev] with i hh0 hh1 hr hsm
  obtain ⟨hs0, hs, hε0, hε, hβ⟩ := hr
  have hη := shadowEta_four_ten_le hCR hA0 hh0 hh1 hε0 (eps_le_of_rate hCR hε hs)
  have hbud : shadowBudget B γ (β i) c τ (shadowEta CR 4 10 (ε i)) ≤ |Cb| * h i ^ (1 / 2 : ℝ) :=
    (shadowBudget_le_of_rate (τ := τ) hB hγ.le hc.le hβ hη).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hh0.le _))
  obtain ⟨x, ⟨-, hx0⟩, -, hC, -, hex, -, hun, hdist⟩ :=
    aposteriori_physical_shadow M T hboot (hadm i) (hharm i) (R i) hγ (hA i) (hmargin i) (hres i)
      (hrad i) hB (htube i) hc hτ (hforce i) (hbud.trans hsm.le)
  refine ⟨x, hx0, hC, hex, hun, hdist.trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hbud (T.shadowConst_nonneg c τ)

end

end RenewalGeometry.AposterioriShadowRate
