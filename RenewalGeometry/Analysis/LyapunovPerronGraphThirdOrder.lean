/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.LyapunovPerronTrajectoryDerivatives

/-!
# `C³` regularity of the Lyapunov–Perron invariant graph

Last layer of the forward invariant-graph construction (`lem:supp-exact-graph-criterion`,
emergent-spacetime manuscript), on top of `Analysis/LyapunovPerronTrajectoryDerivatives.lean`.

The manuscript assumes a `C³` field with **bounded** nonlinear derivatives through order three, the
three inequalities `j = 1, 2, 3` of `eq:supp-exact-graph-contraction` and `3ν < β`.  The third
derivative `D³N` is then bounded and continuous but not Lipschitz, so the quadratic-defect route
of the `C¹`/`C²` layers cannot be iterated (it would need the weight `4ν`).  Instead:

* `LittleODefect`, `contDiff_one_of_littleODefect` (general analysis): a Lipschitz map whose
  three-point defects `Σ aᵢ (G(n+vᵢ) - G(n))` (`Σ aᵢvᵢ = 0`) are `o(Σ|aᵢ|‖vᵢ‖)` locally uniformly
  in the base point is `C¹`;
* `taylor_modulus_le`, `third_comp_fine_le`, `third_comp_crude_le`: pointwise algebra of the
  third-level source, `O(‖v‖² e^{4νr}) + ω(D³N)·O(‖v‖ e^{3νr})` and `O(‖v‖ e^{3νr})`;
* `third_level_identity`, `third_level_le`: for `Σ aᵢvᵢ = 0`, `Z = Σ aᵢ (Y₂(n+vᵢ) - Y₂(n)) e d`
  solves the linearised Lyapunov–Perron equation with that source, and the a priori bound in a
  weight `κ ∈ (3ν, β)` with `q_κ < 1` (available by the *strict* `j = 3` inequality) controls
  `Z(0)`;
* `traj2_littleODefect`: splitting time into `[0, T]` (uniform continuity of `D³N` on the compact
  set of trajectory values, Heine–Cantor) and `[T, ∞)` (the factor `e^{-(κ-3ν)T}`) gives the
  locally uniform little-o defect of `n₀ ↦ D²h(n₀)`;
* `graphMap_contDiff_three`: **the invariant graph is `C³`**.
-/

open Filter Set MeasureTheory intervalIntegral Real
open scoped Topology BoundedContinuousFunction

namespace RenewalGeometry
namespace LyapunovPerron

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ### Locally uniform little-o three-point defects give `C¹` -/

section LittleO

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-- The little-o defect condition at a base point `n₀`, with tolerance `ε` and radius `δ`:
for every base point `n` with `‖n - n₀‖ ≤ δ` and every combination `Σ aᵢvᵢ = 0` with `‖vᵢ‖ ≤ δ`,
`‖Σ aᵢ (G(n+vᵢ) - G(n))‖ ≤ ε Σ |aᵢ| ‖vᵢ‖`. -/
def DefectAt (G : E → F) (n₀ : E) (ε δ : ℝ) : Prop :=
  ∀ n : E, ‖n - n₀‖ ≤ δ → ∀ (v₁ v₂ v₃ : E) (a₁ a₂ a₃ : ℝ),
    a₁ • v₁ + a₂ • v₂ + a₃ • v₃ = 0 → ‖v₁‖ ≤ δ → ‖v₂‖ ≤ δ → ‖v₃‖ ≤ δ →
    ‖a₁ • (G (n + v₁) - G n) + a₂ • (G (n + v₂) - G n) + a₃ • (G (n + v₃) - G n)‖ ≤
      ε * (|a₁| * ‖v₁‖ + |a₂| * ‖v₂‖ + |a₃| * ‖v₃‖)

/-- **Locally uniform little-o three-point defects.** -/
def LittleODefect (G : E → F) : Prop :=
  ∀ (n₀ : E) (ε : ℝ), 0 < ε → ∃ δ > 0, DefectAt G n₀ ε δ

variable {G : E → F}

theorem DefectAt.diffQuot_sub_le {n₀ : E} {ε δ : ℝ} (hG : DefectAt G n₀ ε δ) (hδ : 0 ≤ δ)
    {n : E} (hn : ‖n - n₀‖ ≤ δ) (d : E) {ℓ ℓ' : ℝ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ')
    (hℓd : ℓ * ‖d‖ ≤ δ) (hℓd' : ℓ' * ‖d‖ ≤ δ) :
    ‖diffQuot G n d ℓ - diffQuot G n d ℓ'‖ ≤ 2 * ε * ‖d‖ := by
  have hnl : ‖ℓ • d‖ = ℓ * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
  have hnl' : ‖ℓ' • d‖ = ℓ' * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ']
  have h := hG n hn (ℓ • d) (ℓ' • d) 0 ℓ⁻¹ (-ℓ'⁻¹) 0 (by
      rw [smul_smul, smul_smul, inv_mul_cancel₀ hℓ.ne', neg_mul, inv_mul_cancel₀ hℓ'.ne']
      simp) (by rw [hnl]; exact hℓd) (by rw [hnl']; exact hℓd') (by simpa using hδ)
  simp only [zero_smul, add_zero, abs_zero, zero_mul, abs_neg, abs_inv, abs_of_pos hℓ,
    abs_of_pos hℓ', hnl, hnl'] at h
  unfold diffQuot
  rw [sub_eq_add_neg, ← neg_smul]
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- The derivative candidate `D(n) d = lim ℓ⁻¹ (G(n + ℓd) - G(n))`. -/
def oDeriv (G : E → F) (n d : E) : F :=
  limUnder atTop fun k : ℕ => diffQuot G n d (1 / ((k : ℝ) + 1))

theorem eventually_small_step (d : E) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) * ‖d‖ ≤ δ := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat).mul_const ‖d‖
  rw [zero_mul] at h
  exact h.eventually (ge_mem_nhds hδ)

theorem tendsto_oDeriv (hG : LittleODefect G) (n d : E) :
    Tendsto (fun k : ℕ => diffQuot G n d (1 / ((k : ℝ) + 1))) atTop (𝓝 (oDeriv G n d)) := by
  refine CauchySeq.tendsto_limUnder ?_
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨δ, hδ, hD⟩ := hG n (ε / (2 * (‖d‖ + 1))) (by positivity)
  obtain ⟨N, hN⟩ := (eventually_small_step d hδ).exists_forall_of_atTop
  refine ⟨N, fun k hk => ?_⟩
  rw [dist_eq_norm]
  refine (hD.diffQuot_sub_le hδ.le (by simpa using hδ.le) d (by positivity) (by positivity)
    (hN k hk) (hN N le_rfl)).trans_lt ?_
  have : 2 * (ε / (2 * (‖d‖ + 1))) * ‖d‖ = ε * (‖d‖ / (‖d‖ + 1)) := by field_simp
  rw [this]
  have h1 : ‖d‖ / (‖d‖ + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  nlinarith

/-- Quantitative convergence of the difference quotients at base points near `n₀`. -/
theorem DefectAt.diffQuot_sub_oDeriv_le (hG : LittleODefect G) {n₀ : E} {ε δ : ℝ}
    (hD : DefectAt G n₀ ε δ) (hδ : 0 < δ) {n : E} (hn : ‖n - n₀‖ ≤ δ) (d : E) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hℓd : ℓ * ‖d‖ ≤ δ) :
    ‖diffQuot G n d ℓ - oDeriv G n d‖ ≤ 2 * ε * ‖d‖ := by
  have ht := tendsto_oDeriv hG n d
  have hlim : Tendsto (fun k : ℕ => ‖diffQuot G n d ℓ - diffQuot G n d (1 / ((k : ℝ) + 1))‖)
      atTop (𝓝 ‖diffQuot G n d ℓ - oDeriv G n d‖) := (tendsto_const_nhds.sub ht).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_small_step d hδ] with k hk
  exact hD.diffQuot_sub_le hδ.le hn d hℓ (by positivity) hℓd hk

/-- **Uniform little-o Taylor bound**: `‖G(n+v) - G(n) - D(n)v‖ ≤ 2ε‖v‖` for `‖n - n₀‖ ≤ δ`,
`‖v‖ ≤ δ`. -/
theorem DefectAt.taylor_le (hG : LittleODefect G) {n₀ : E} {ε δ : ℝ} (hD : DefectAt G n₀ ε δ)
    (hδ : 0 < δ) {n : E} (hn : ‖n - n₀‖ ≤ δ) {v : E} (hv : ‖v‖ ≤ δ) :
    ‖G (n + v) - G n - oDeriv G n v‖ ≤ 2 * ε * ‖v‖ := by
  have ht := tendsto_oDeriv hG n v
  have hlim : Tendsto (fun k : ℕ => ‖G (n + v) - G n - diffQuot G n v (1 / ((k : ℝ) + 1))‖)
      atTop (𝓝 ‖G (n + v) - G n - oDeriv G n v‖) := (tendsto_const_nhds.sub ht).norm
  refine le_of_tendsto hlim (Eventually.of_forall fun k => ?_)
  set ℓ : ℝ := 1 / ((k : ℝ) + 1) with hℓdef
  have hℓ : 0 < ℓ := by positivity
  have hℓ1 : ℓ ≤ 1 := by
    rw [hℓdef, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hnl : ‖ℓ • v‖ = ℓ * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
  have h := hD n hn v (ℓ • v) 0 1 (-ℓ⁻¹) 0 (by
      rw [smul_smul, neg_mul, inv_mul_cancel₀ hℓ.ne']; simp)
    hv (by rw [hnl]; nlinarith [norm_nonneg v]) (by simpa using hδ.le)
  simp only [zero_smul, add_zero, abs_zero, zero_mul, abs_neg, abs_inv, abs_of_pos hℓ, hnl,
    one_smul, abs_one, one_mul] at h
  unfold diffQuot
  rw [sub_eq_add_neg (G (n + v) - G n), ← neg_smul]
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- Linearity of the derivative candidate. -/
theorem oDeriv_comb (hG : LittleODefect G) (n d e : E) (a b : ℝ) :
    oDeriv G n (a • d + b • e) = a • oDeriv G n d + b • oDeriv G n e := by
  set X := oDeriv G n (a • d + b • e) - (a • oDeriv G n d + b • oDeriv G n e)
  set S := ‖a • d + b • e‖ + |a| * ‖d‖ + |b| * ‖e‖ with hSdef
  have hS : 0 ≤ S := by positivity
  have hX : ‖X‖ ≤ 0 := by
    refine le_of_forall_pos_le_add_mul (C := 3 * S) fun η hη => ?_
    obtain ⟨δ, hδ, hD⟩ := hG n η hη
    set ℓ := δ / (‖a • d + b • e‖ + ‖d‖ + ‖e‖ + 1) with hℓdef
    have hden : 0 < ‖a • d + b • e‖ + ‖d‖ + ‖e‖ + 1 := by positivity
    have hℓ : 0 < ℓ := div_pos hδ hden
    have hsm : ∀ x : ℝ, 0 ≤ x → x ≤ ‖a • d + b • e‖ + ‖d‖ + ‖e‖ + 1 → ℓ * x ≤ δ := by
      intro x hx0 hx
      calc ℓ * x ≤ ℓ * (‖a • d + b • e‖ + ‖d‖ + ‖e‖ + 1) := mul_le_mul_of_nonneg_left hx hℓ.le
        _ = δ := by rw [hℓdef]; field_simp
    have h1 := hsm ‖a • d + b • e‖ (norm_nonneg _) (by linarith [norm_nonneg d, norm_nonneg e])
    have hnd := norm_nonneg d
    have hne := norm_nonneg e
    have hnde := norm_nonneg (a • d + b • e)
    have h2 := hsm ‖d‖ (norm_nonneg _) (by linarith)
    have h3 := hsm ‖e‖ (norm_nonneg _) (by linarith)
    have hn0 : ‖n - n‖ ≤ δ := by simpa using hδ.le
    have hnl : ∀ x : E, ‖ℓ • x‖ = ℓ * ‖x‖ := fun x => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
    have hcomb := hD n hn0 (ℓ • (a • d + b • e)) (ℓ • d) (ℓ • e) ℓ⁻¹ (-(a * ℓ⁻¹)) (-(b * ℓ⁻¹))
      (by
        simp only [smul_smul, smul_add]
        rw [show ℓ⁻¹ * (ℓ * a) = a by field_simp, show ℓ⁻¹ * (ℓ * b) = b by field_simp,
          show -(a * ℓ⁻¹) * ℓ = -a by field_simp, show -(b * ℓ⁻¹) * ℓ = -b by field_simp]
        simp only [neg_smul]; abel)
      (by rw [hnl]; exact h1) (by rw [hnl]; exact h2) (by rw [hnl]; exact h3)
    have e3 : ℓ⁻¹ • (G (n + ℓ • (a • d + b • e)) - G n) + -(a * ℓ⁻¹) • (G (n + ℓ • d) - G n) +
        -(b * ℓ⁻¹) • (G (n + ℓ • e) - G n) =
        diffQuot G n (a • d + b • e) ℓ - (a • diffQuot G n d ℓ + b • diffQuot G n e ℓ) := by
      simp only [diffQuot, neg_smul, smul_smul, mul_comm a, mul_comm b]
      abel
    rw [e3] at hcomb
    have hR : η * (|ℓ⁻¹| * ‖ℓ • (a • d + b • e)‖ + |-(a * ℓ⁻¹)| * ‖ℓ • d‖ +
        |-(b * ℓ⁻¹)| * ‖ℓ • e‖) = η * S := by
      simp only [hnl, abs_neg, abs_mul, abs_inv, abs_of_pos hℓ, hSdef]
      field_simp
    rw [hR] at hcomb
    have hd1 := hD.diffQuot_sub_oDeriv_le hG hδ hn0 (a • d + b • e) hℓ h1
    have hd2 := hD.diffQuot_sub_oDeriv_le hG hδ hn0 d hℓ h2
    have hd3 := hD.diffQuot_sub_oDeriv_le hG hδ hn0 e hℓ h3
    have eX : X = (diffQuot G n (a • d + b • e) ℓ - (a • diffQuot G n d ℓ + b • diffQuot G n e ℓ))
        - (diffQuot G n (a • d + b • e) ℓ - oDeriv G n (a • d + b • e))
        + a • (diffQuot G n d ℓ - oDeriv G n d) + b • (diffQuot G n e ℓ - oDeriv G n e) := by
      simp only [X, smul_sub]; abel
    have hnorm : ‖X‖ ≤ ‖diffQuot G n (a • d + b • e) ℓ - (a • diffQuot G n d ℓ +
        b • diffQuot G n e ℓ)‖ + ‖diffQuot G n (a • d + b • e) ℓ - oDeriv G n (a • d + b • e)‖
        + |a| * ‖diffQuot G n d ℓ - oDeriv G n d‖ + |b| * ‖diffQuot G n e ℓ - oDeriv G n e‖ := by
      rw [eX]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        (norm_sub_le _ _) (by rw [norm_smul, Real.norm_eq_abs]))) (by rw [norm_smul, Real.norm_eq_abs]))
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    calc ‖X‖ ≤ _ := hnorm
      _ ≤ η * S + 2 * η * ‖a • d + b • e‖ + |a| * (2 * η * ‖d‖) + |b| * (2 * η * ‖e‖) := by
          gcongr
      _ ≤ 0 + 3 * S * η := by
          have : 2 * η * ‖a • d + b • e‖ + |a| * (2 * η * ‖d‖) + |b| * (2 * η * ‖e‖) =
              2 * η * S := by rw [hSdef]; ring
          nlinarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hX)

theorem oDeriv_norm_le (hG : LittleODefect G) {C₀ : ℝ}
    (hlip : ∀ n n', ‖G n - G n'‖ ≤ C₀ * ‖n - n'‖) (n d : E) : ‖oDeriv G n d‖ ≤ C₀ * ‖d‖ := by
  have ht := (tendsto_oDeriv hG n d).norm
  refine le_of_tendsto ht (Eventually.of_forall fun k => ?_)
  set ℓ : ℝ := 1 / ((k : ℝ) + 1)
  have hℓ : 0 < ℓ := by positivity
  unfold diffQuot
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ]
  have := hlip (n + ℓ • d) n
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] at this
  rw [inv_mul_le_iff₀ hℓ]
  linarith

/-- The derivative candidate as a continuous linear map. -/
def oDerivCLM (hG : LittleODefect G) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hlip : ∀ n n', ‖G n - G n'‖ ≤ C₀ * ‖n - n'‖) (n : E) : E →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := oDeriv G n
      map_add' := fun d e => by simpa using oDeriv_comb hG n d e 1 1
      map_smul' := fun c d => by simpa using oDeriv_comb hG n d 0 c 0 }
    C₀ (fun d => oDeriv_norm_le hG hlip n d)

theorem oDerivCLM_apply (hG : LittleODefect G) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hlip : ∀ n n', ‖G n - G n'‖ ≤ C₀ * ‖n - n'‖) (n d : E) :
    oDerivCLM hG hC₀ hlip n d = oDeriv G n d := rfl

theorem oDerivCLM_hasFDerivAt (hG : LittleODefect G) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hlip : ∀ n n', ‖G n - G n'‖ ≤ C₀ * ‖n - n'‖) (n : E) :
    HasFDerivAt G (oDerivCLM hG hC₀ hlip n) n := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hD⟩ := hG n (c / 2) (by positivity)
  filter_upwards [Metric.closedBall_mem_nhds (0 : E) hδ] with v hv
  rw [Metric.mem_closedBall, dist_zero_right] at hv
  rw [oDerivCLM_apply]
  have := hD.taylor_le hG hδ (n := n) (by simpa using hδ.le) hv
  calc _ ≤ 2 * (c / 2) * ‖v‖ := this
    _ = c * ‖v‖ := by ring

theorem oDerivCLM_continuous (hG : LittleODefect G) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hlip : ∀ n n', ‖G n - G n'‖ ≤ C₀ * ‖n - n'‖) : Continuous (oDerivCLM hG hC₀ hlip) := by
  rw [Metric.continuous_iff]
  intro n₀ η hη
  obtain ⟨δ, hδ, hD⟩ := hG n₀ (η / 16) (by positivity)
  refine ⟨δ / 2, by positivity, fun n hn => ?_⟩
  rw [dist_eq_norm] at hn ⊢
  set v := n - n₀ with hvdef
  have hn' : n = n₀ + v := by simp [hvdef]
  have hv : ‖v‖ < δ / 2 := hn
  set D := oDerivCLM hG hC₀ hlip
  have hbound : ‖D n - D n₀‖ ≤ η / 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    rw [ContinuousLinearMap.sub_apply, hn']
    rcases eq_or_ne v 0 with hv0 | hv0
    · simp only [hv0, add_zero, sub_self, norm_zero]; positivity
    rcases eq_or_ne x 0 with hx0 | hx0
    · simp [hx0]
    have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    set c : ℝ := ‖v‖ / ‖x‖ with hcdef
    have hc : 0 < c := div_pos hvn hxn
    have hcx : ‖c • x‖ = ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, hcdef]; field_simp
    have hb1 : ‖(n₀ + v) - n₀‖ ≤ δ := by rw [add_sub_cancel_left]; linarith
    have hb0 : ‖n₀ - n₀‖ ≤ δ := by simpa using hδ.le
    have hvx : ‖v + c • x‖ ≤ 2 * ‖v‖ := (norm_add_le _ _).trans (by rw [hcx]; linarith)
    have hA := hD.taylor_le hG hδ hb1 (v := c • x) (by rw [hcx]; linarith)
    have hB := hD.taylor_le hG hδ hb0 (v := v + c • x) (by linarith)
    have hC := hD.taylor_le hG hδ hb0 (v := v) (by linarith)
    have hlin : oDeriv G n₀ (v + c • x) = oDeriv G n₀ v + oDeriv G n₀ (c • x) := by
      simpa using oDeriv_comb hG n₀ v (c • x) 1 1
    have e1 : D (n₀ + v) (c • x) - D n₀ (c • x) =
        -(G (n₀ + v + c • x) - G (n₀ + v) - oDeriv G (n₀ + v) (c • x)) +
          (G (n₀ + (v + c • x)) - G n₀ - oDeriv G n₀ (v + c • x)) -
          (G (n₀ + v) - G n₀ - oDeriv G n₀ v) := by
      simp only [D, oDerivCLM_apply]
      rw [hlin, ← add_assoc]; abel
    have hmain : ‖D (n₀ + v) (c • x) - D n₀ (c • x)‖ ≤ 8 * (η / 16) * ‖v‖ := by
      rw [e1]
      calc _ ≤ ‖G (n₀ + v + c • x) - G (n₀ + v) - oDeriv G (n₀ + v) (c • x)‖ +
            ‖G (n₀ + (v + c • x)) - G n₀ - oDeriv G n₀ (v + c • x)‖ +
            ‖G (n₀ + v) - G n₀ - oDeriv G n₀ v‖ := by
            refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
              (add_le_add (by rw [norm_neg]) le_rfl)) le_rfl)
        _ ≤ 2 * (η / 16) * ‖c • x‖ + 2 * (η / 16) * ‖v + c • x‖ + 2 * (η / 16) * ‖v‖ :=
            add_le_add (add_le_add hA hB) hC
        _ ≤ 8 * (η / 16) * ‖v‖ := by
            rw [hcx]; nlinarith [hvx]
    rw [map_smul, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hmain
    have h3 : ‖D (n₀ + v) x - D n₀ x‖ ≤ 8 * (η / 16) * ‖v‖ / c := by
      rw [le_div_iff₀ hc, mul_comm]; exact hmain
    refine h3.trans (le_of_eq ?_)
    rw [hcdef]; field_simp; ring
  linarith

/-- **A Lipschitz map with locally uniform little-o three-point defects is `C¹`.** -/
theorem contDiff_one_of_littleODefect (hG : LittleODefect G) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hlip : ∀ n n', ‖G n - G n'‖ ≤ C₀ * ‖n - n'‖) : ContDiff ℝ 1 G := by
  have hD : ∀ n, HasFDerivAt G (oDerivCLM hG hC₀ hlip n) n := oDerivCLM_hasFDerivAt hG hC₀ hlip
  have hfd : fderiv ℝ G = oDerivCLM hG hC₀ hlip := funext fun n => (hD n).fderiv
  refine contDiff_one_iff_fderiv.mpr ⟨fun n => (hD n).differentiableAt, ?_⟩
  rw [hfd]
  exact oDerivCLM_continuous hG hC₀ hlip

end LittleO

/-! ### Pointwise algebra of the third-level source -/

section Pointwise3

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- First-order Taylor bound with a modulus of continuity of the derivative:
`‖g(y+w) - g(y) - Dg(y)w‖ ≤ ω‖w‖` if `‖Dg z - Dg y‖ ≤ ω` on the ball `B(y, ‖w‖)`. -/
theorem taylor_modulus_le {g : E → G} {Dg : E → E →L[ℝ] G} (hg : ∀ x, HasFDerivAt g (Dg x) x)
    (y w : E) {ω : ℝ} (hω : ∀ z ∈ Metric.closedBall y ‖w‖, ‖Dg z - Dg y‖ ≤ ω) :
    ‖g (y + w) - g y - Dg y w‖ ≤ ω * ‖w‖ := by
  have hconv : Convex ℝ (Metric.closedBall y ‖w‖) := convex_closedBall _ _
  have hder : ∀ z ∈ Metric.closedBall y ‖w‖, HasFDerivWithinAt (fun z => g z - Dg y z)
      (Dg z - Dg y) (Metric.closedBall y ‖w‖) z :=
    fun z _ => ((hg z).sub (Dg y).hasFDerivAt).hasFDerivWithinAt
  have hyw : y + w ∈ Metric.closedBall y ‖w‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hω
    (Metric.mem_closedBall_self (norm_nonneg w)) hyw
  rw [add_sub_cancel_left, map_add] at this
  calc ‖g (y + w) - g y - Dg y w‖ = ‖g (y + w) - (Dg y y + Dg y w) - (g y - Dg y y)‖ := by
        congr 1; abel
    _ ≤ ω * ‖w‖ := this

theorem lin_le' (A : E →L[ℝ] G) {x : E} {b1 b2 : ℝ} (h1 : ‖A‖ ≤ b1) (h2 : ‖x‖ ≤ b2) :
    ‖A x‖ ≤ b1 * b2 :=
  (A.le_opNorm x).trans (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))

theorem bil_le' (B : E →L[ℝ] E →L[ℝ] G) {x y : E} {b1 b2 b3 : ℝ} (h1 : ‖B‖ ≤ b1)
    (h2 : ‖x‖ ≤ b2) (h3 : ‖y‖ ≤ b3) : ‖B x y‖ ≤ b1 * b2 * b3 :=
  (B.le_opNorm₂ x y).trans (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _)
    ((norm_nonneg B).trans h1)) h3 (norm_nonneg _)
    (mul_nonneg ((norm_nonneg B).trans h1) ((norm_nonneg _).trans h2)))

theorem tri_le' (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] G) {x y z : E} {b1 b2 b3 b4 : ℝ}
    (h1 : ‖T‖ ≤ b1) (h2 : ‖x‖ ≤ b2) (h3 : ‖y‖ ≤ b3) (h4 : ‖z‖ ≤ b4) :
    ‖T x y z‖ ≤ b1 * b2 * b3 * b4 := by
  have hb1 : 0 ≤ b1 := (norm_nonneg T).trans h1
  have hb2 : 0 ≤ b2 := (norm_nonneg _).trans h2
  have hTx : ‖T x‖ ≤ b1 * b2 := lin_le' T h1 h2
  exact bil_le' (T x) hTx h3 h4

/-- The pointwise third-level source `X` (variation of the second variational source) minus its
linear part `Lin` (linear in the increment `v`). -/
def thirdErr (f : E → E →L[ℝ] G) (Df : E → E →L[ℝ] E →L[ℝ] G)
    (D2f : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] G) (y w Av Ae Ad Ae' Ad' Bve Bvd Bed Bed' : E) : G :=
  ((f (y + w) - f y) Bed' + (Df (y + w) Ae' Ad' - Df y Ae Ad)) -
    (Df y Av Bed + D2f y Av Ae Ad + Df y Bve Ad + Df y Ae Bvd)

variable {f : E → E →L[ℝ] G} {Df : E → E →L[ℝ] E →L[ℝ] G}
  {D2f : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] G}

/-- **Fine bound** of the third-level source: `O(s² E⁴) + ω O(s E³)` (times `‖e‖‖d‖`). -/
theorem thirdErr_fine_le {Cb ω s E' pe pd : ℝ} (hCb : 1 ≤ Cb) (hs : 0 ≤ s) (hE : 1 ≤ E')
    (hpe : 0 ≤ pe) (hpd : 0 ≤ pd) (hω0 : 0 ≤ ω)
    (y w Av Ae Ad Ae' Ad' Bve Bvd Bed Bed' : E)
    (hfT : ‖f (y + w) - f y - Df y w‖ ≤ Cb * ‖w‖ ^ 2)
    (hDfM : ‖Df (y + w) - Df y - D2f y w‖ ≤ ω * ‖w‖)
    (hDfb : ‖Df y‖ ≤ Cb) (hD2fb : ‖D2f y‖ ≤ Cb)
    (hw : ‖w‖ ≤ Cb * s * E') (hwl : ‖w - Av‖ ≤ Cb * s ^ 2 * E' ^ 2) (hAv : ‖Av‖ ≤ Cb * s * E')
    (hAe : ‖Ae‖ ≤ Cb * E' * pe) (hAe' : ‖Ae'‖ ≤ Cb * E' * pe) (hAd' : ‖Ad'‖ ≤ Cb * E' * pd)
    (hdAe : ‖Ae' - Ae‖ ≤ Cb * s * E' ^ 2 * pe) (hdAd : ‖Ad' - Ad‖ ≤ Cb * s * E' ^ 2 * pd)
    (hRe : ‖Ae' - Ae - Bve‖ ≤ Cb * s ^ 2 * E' ^ 3 * pe)
    (hRd : ‖Ad' - Ad - Bvd‖ ≤ Cb * s ^ 2 * E' ^ 3 * pd)
    (hBve : ‖Bve‖ ≤ Cb * s * E' ^ 2 * pe) (hBed' : ‖Bed'‖ ≤ Cb * E' ^ 2 * pe * pd)
    (hdB : ‖Bed' - Bed‖ ≤ Cb * s * E' ^ 3 * pe * pd) :
    ‖thirdErr f Df D2f y w Av Ae Ad Ae' Ad' Bve Bvd Bed Bed'‖ ≤
      (9 * Cb ^ 4 * s * E' + Cb ^ 3 * ω) * s * E' ^ 3 * pe * pd := by
  have hCb0 : 0 ≤ Cb := by linarith
  have hE0 : 0 ≤ E' := by linarith
  set P := s ^ 2 * E' ^ 4 * pe * pd with hPdef
  have hP : 0 ≤ P := by positivity
  have hc34 : Cb ^ 3 * P ≤ Cb ^ 4 * P := by
    refine mul_le_mul_of_nonneg_right ?_ hP
    calc Cb ^ 3 = Cb ^ 3 * 1 := by ring
      _ ≤ Cb ^ 3 * Cb := mul_le_mul_of_nonneg_left hCb (by positivity)
      _ = Cb ^ 4 := by ring
  have e : thirdErr f Df D2f y w Av Ae Ad Ae' Ad' Bve Bvd Bed Bed' =
      (f (y + w) - f y - Df y w) Bed' + Df y (w - Av) Bed' + Df y Av (Bed' - Bed) +
      (Df (y + w) - Df y - D2f y w) Ae' Ad' + D2f y (w - Av) Ae' Ad' +
      D2f y Av (Ae' - Ae) Ad' + D2f y Av Ae (Ad' - Ad) +
      Df y (Ae' - Ae - Bve) Ad' + Df y Bve (Ad' - Ad) + Df y Ae (Ad' - Ad - Bvd) := by
    simp only [thirdErr, map_sub, ContinuousLinearMap.sub_apply]
    abel
  have hw2 : ‖w‖ ^ 2 ≤ (Cb * s * E') ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  have t1 : ‖(f (y + w) - f y - Df y w) Bed'‖ ≤ Cb ^ 4 * P := by
    refine (lin_le' _ (hfT.trans (mul_le_mul_of_nonneg_left hw2 hCb0)) hBed').trans
      (le_of_eq ?_)
    rw [hPdef]; ring
  have t2 : ‖Df y (w - Av) Bed'‖ ≤ Cb ^ 4 * P :=
    (bil_le' _ hDfb hwl hBed').trans ((le_of_eq (by rw [hPdef]; ring)).trans hc34)
  have t3 : ‖Df y Av (Bed' - Bed)‖ ≤ Cb ^ 4 * P :=
    (bil_le' _ hDfb hAv hdB).trans ((le_of_eq (by rw [hPdef]; ring)).trans hc34)
  have t4 : ‖(Df (y + w) - Df y - D2f y w) Ae' Ad'‖ ≤ Cb ^ 3 * ω * s * E' ^ 3 * pe * pd :=
    (bil_le' _ (hDfM.trans (mul_le_mul_of_nonneg_left hw hω0)) hAe' hAd').trans
      (le_of_eq (by ring))
  have t5 : ‖D2f y (w - Av) Ae' Ad'‖ ≤ Cb ^ 4 * P :=
    (tri_le' _ hD2fb hwl hAe' hAd').trans (le_of_eq (by rw [hPdef]; ring))
  have t6 : ‖D2f y Av (Ae' - Ae) Ad'‖ ≤ Cb ^ 4 * P :=
    (tri_le' _ hD2fb hAv hdAe hAd').trans (le_of_eq (by rw [hPdef]; ring))
  have t7 : ‖D2f y Av Ae (Ad' - Ad)‖ ≤ Cb ^ 4 * P :=
    (tri_le' _ hD2fb hAv hAe hdAd).trans (le_of_eq (by rw [hPdef]; ring))
  have t8 : ‖Df y (Ae' - Ae - Bve) Ad'‖ ≤ Cb ^ 4 * P :=
    (bil_le' _ hDfb hRe hAd').trans ((le_of_eq (by rw [hPdef]; ring)).trans hc34)
  have t9 : ‖Df y Bve (Ad' - Ad)‖ ≤ Cb ^ 4 * P :=
    (bil_le' _ hDfb hBve hdAd).trans ((le_of_eq (by rw [hPdef]; ring)).trans hc34)
  have t10 : ‖Df y Ae (Ad' - Ad - Bvd)‖ ≤ Cb ^ 4 * P :=
    (bil_le' _ hDfb hAe hRd).trans ((le_of_eq (by rw [hPdef]; ring)).trans hc34)
  rw [e]
  have htri : ∀ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : G,
      ‖a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10‖ ≤ ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖a4‖ + ‖a5‖ +
        ‖a6‖ + ‖a7‖ + ‖a8‖ + ‖a9‖ + ‖a10‖ := by
    intro a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  refine (htri _ _ _ _ _ _ _ _ _ _).trans ?_
  have hfin : (9 * Cb ^ 4 * s * E' + Cb ^ 3 * ω) * s * E' ^ 3 * pe * pd =
      9 * (Cb ^ 4 * P) + Cb ^ 3 * ω * s * E' ^ 3 * pe * pd := by rw [hPdef]; ring
  rw [hfin]
  linarith

/-- **Crude bound** of the third-level source: `O(s E³)` (times `‖e‖‖d‖`). -/
theorem thirdErr_crude_le {Cb s E' pe pd : ℝ} (hCb : 1 ≤ Cb) (hs : 0 ≤ s) (hE : 1 ≤ E')
    (hpe : 0 ≤ pe) (hpd : 0 ≤ pd)
    (y w Av Ae Ad Ae' Ad' Bve Bvd Bed Bed' : E)
    (hfL : ‖f (y + w) - f y‖ ≤ Cb * ‖w‖) (hDfL : ‖Df (y + w) - Df y‖ ≤ Cb * ‖w‖)
    (hDfb : ‖Df y‖ ≤ Cb) (hD2fb : ‖D2f y‖ ≤ Cb)
    (hw : ‖w‖ ≤ Cb * s * E') (hAv : ‖Av‖ ≤ Cb * s * E')
    (hAe : ‖Ae‖ ≤ Cb * E' * pe) (hAd : ‖Ad‖ ≤ Cb * E' * pd)
    (hAe' : ‖Ae'‖ ≤ Cb * E' * pe) (hAd' : ‖Ad'‖ ≤ Cb * E' * pd)
    (hdAe : ‖Ae' - Ae‖ ≤ Cb * s * E' ^ 2 * pe) (hdAd : ‖Ad' - Ad‖ ≤ Cb * s * E' ^ 2 * pd)
    (hBve : ‖Bve‖ ≤ Cb * s * E' ^ 2 * pe) (hBvd : ‖Bvd‖ ≤ Cb * s * E' ^ 2 * pd)
    (hBed : ‖Bed‖ ≤ Cb * E' ^ 2 * pe * pd) (hBed' : ‖Bed'‖ ≤ Cb * E' ^ 2 * pe * pd) :
    ‖thirdErr f Df D2f y w Av Ae Ad Ae' Ad' Bve Bvd Bed Bed'‖ ≤
      8 * Cb ^ 4 * s * E' ^ 3 * pe * pd := by
  have hCb0 : 0 ≤ Cb := by linarith
  have hE0 : 0 ≤ E' := by linarith
  set Q := s * E' ^ 3 * pe * pd with hQdef
  have hQ : 0 ≤ Q := by positivity
  have hc34 : Cb ^ 3 * Q ≤ Cb ^ 4 * Q := by
    refine mul_le_mul_of_nonneg_right ?_ hQ
    calc Cb ^ 3 = Cb ^ 3 * 1 := by ring
      _ ≤ Cb ^ 3 * Cb := mul_le_mul_of_nonneg_left hCb (by positivity)
      _ = Cb ^ 4 := by ring
  have hwb : Cb * ‖w‖ ≤ Cb * (Cb * s * E') := mul_le_mul_of_nonneg_left hw hCb0
  have e : thirdErr f Df D2f y w Av Ae Ad Ae' Ad' Bve Bvd Bed Bed' =
      (f (y + w) - f y) Bed' + (Df (y + w) - Df y) Ae' Ad' + Df y (Ae' - Ae) Ad' +
        Df y Ae (Ad' - Ad) - Df y Av Bed - D2f y Av Ae Ad - Df y Bve Ad - Df y Ae Bvd := by
    simp only [thirdErr, map_sub, ContinuousLinearMap.sub_apply]
    abel
  have t1 : ‖(f (y + w) - f y) Bed'‖ ≤ Cb ^ 4 * Q :=
    (lin_le' _ (hfL.trans hwb) hBed').trans ((le_of_eq (by rw [hQdef]; ring)).trans hc34)
  have t2 : ‖(Df (y + w) - Df y) Ae' Ad'‖ ≤ Cb ^ 4 * Q :=
    (bil_le' _ (hDfL.trans hwb) hAe' hAd').trans (le_of_eq (by rw [hQdef]; ring))
  have t3 : ‖Df y (Ae' - Ae) Ad'‖ ≤ Cb ^ 4 * Q :=
    (bil_le' _ hDfb hdAe hAd').trans ((le_of_eq (by rw [hQdef]; ring)).trans hc34)
  have t4 : ‖Df y Ae (Ad' - Ad)‖ ≤ Cb ^ 4 * Q :=
    (bil_le' _ hDfb hAe hdAd).trans ((le_of_eq (by rw [hQdef]; ring)).trans hc34)
  have t5 : ‖Df y Av Bed‖ ≤ Cb ^ 4 * Q :=
    (bil_le' _ hDfb hAv hBed).trans ((le_of_eq (by rw [hQdef]; ring)).trans hc34)
  have t6 : ‖D2f y Av Ae Ad‖ ≤ Cb ^ 4 * Q :=
    (tri_le' _ hD2fb hAv hAe hAd).trans (le_of_eq (by rw [hQdef]; ring))
  have t7 : ‖Df y Bve Ad‖ ≤ Cb ^ 4 * Q :=
    (bil_le' _ hDfb hBve hAd).trans ((le_of_eq (by rw [hQdef]; ring)).trans hc34)
  have t8 : ‖Df y Ae Bvd‖ ≤ Cb ^ 4 * Q :=
    (bil_le' _ hDfb hAe hBvd).trans ((le_of_eq (by rw [hQdef]; ring)).trans hc34)
  rw [e]
  have htri : ∀ a1 a2 a3 a4 a5 a6 a7 a8 : G,
      ‖a1 + a2 + a3 + a4 - a5 - a6 - a7 - a8‖ ≤ ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖a4‖ + ‖a5‖ +
        ‖a6‖ + ‖a7‖ + ‖a8‖ := by
    intro a1 a2 a3 a4 a5 a6 a7 a8
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  refine (htri _ _ _ _ _ _ _ _).trans ?_
  have hfin : 8 * Cb ^ 4 * s * E' ^ 3 * pe * pd = 8 * (Cb ^ 4 * Q) := by rw [hQdef]; ring
  rw [hfin]
  linarith

end Pointwise3

end

end LyapunovPerron
end RenewalGeometry
