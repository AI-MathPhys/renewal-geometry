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
-- trilinear maps `E →L E →L E →L G` (the third derivative `D³N`) need a deeper instance search
set_option maxSynthPendingDepth 3

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

/-! ### The third level along the trajectories -/

section Third

variable {U Nn : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Nn] [NormedSpace ℝ Nn] [CompleteSpace Nn]
variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn} {h : GraphHyp Pu Pn M α β ν L Nu Nv}
  {DNu : U × Nn → (U × Nn) →L[ℝ] U} {DNv : U × Nn → (U × Nn) →L[ℝ] Nn} {L₂ : ℝ}
  {D2Nu : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] U)}
  {D2Nv : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] Nn)} {L₃ : ℝ}
  {D3Nu : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] U))}
  {D3Nv : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] Nn))}

/-- Hypotheses of the `C³` layer of `lem:supp-exact-graph-criterion`: `D²N` is differentiable
with **continuous** derivative `D³N`.  `D³N` is bounded by `L₃` because `D²N` is `L₃`-Lipschitz
(`GraphC2Hyp`); no Lipschitz bound on `D³N` is assumed.  Together with `GraphHyp`,
`GraphC1Hyp`, `GraphC2Hyp` this is the manuscript's packet: a `C³` nonlinearity with bounded
derivatives through order three, the `j = 1, 2, 3` inequalities and `3ν < β`. -/
structure GraphC3Hyp {hd : GraphC1Hyp h DNu DNv L₂} (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (D3Nu : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] U)))
    (D3Nv : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] Nn))) : Prop where
  hasDeriv3_u : ∀ x, HasFDerivAt D2Nu (D3Nu x) x
  hasDeriv3_v : ∀ x, HasFDerivAt D2Nv (D3Nv x) x
  cont3_u : Continuous D3Nu
  cont3_v : Continuous D3Nv

/-- The third-level source along `y_*(n₀)`: the variation of the second variational source in the
direction `v`, minus its linearised part `DN(y_*)(Y₂(n₀+v) - Y₂(n₀)) e d`. -/
def thirdSrc (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) (bu : U)
    (bn : Nn) (n e d v : Nn) : ℝ → U × Nn :=
  var2Src hd hd2 bu bn (n + v) e d - var2Src hd hd2 bu bn n e d -
    linSrc DNu DNv (yStar h bu bn n)
      (fun r => traj2 hd hd2 bu bn r (n + v) e d - traj2 hd hd2 bu bn r n e d)

/-- The part of the third-level source that is linear in the increment `v`. -/
def linThird (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (D3Nu : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] U)))
    (D3Nv : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] Nn)))
    (bu : U) (bn : Nn) (n e d : Nn) (r : ℝ) (v : Nn) : U × Nn :=
  (D2Nu (yStar h bu bn n r) (traj1 hd bu bn r n v) (traj2 hd hd2 bu bn r n e d) +
      D3Nu (yStar h bu bn n r) (traj1 hd bu bn r n v) (traj1 hd bu bn r n e)
        (traj1 hd bu bn r n d) +
      D2Nu (yStar h bu bn n r) (traj2 hd hd2 bu bn r n v e) (traj1 hd bu bn r n d) +
      D2Nu (yStar h bu bn n r) (traj1 hd bu bn r n e) (traj2 hd hd2 bu bn r n v d),
    D2Nv (yStar h bu bn n r) (traj1 hd bu bn r n v) (traj2 hd hd2 bu bn r n e d) +
      D3Nv (yStar h bu bn n r) (traj1 hd bu bn r n v) (traj1 hd bu bn r n e)
        (traj1 hd bu bn r n d) +
      D2Nv (yStar h bu bn n r) (traj2 hd hd2 bu bn r n v e) (traj1 hd bu bn r n d) +
      D2Nv (yStar h bu bn n r) (traj1 hd bu bn r n e) (traj2 hd hd2 bu bn r n v d))

theorem linThird_add (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (n e d : Nn) (r : ℝ) (v v' : Nn) :
    linThird hd hd2 D3Nu D3Nv bu bn n e d r (v + v') =
      linThird hd hd2 D3Nu D3Nv bu bn n e d r v + linThird hd hd2 D3Nu D3Nv bu bn n e d r v' := by
  simp only [linThird, map_add, ContinuousLinearMap.add_apply, Prod.mk_add_mk]
  congr 1 <;> abel

theorem linThird_smul (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (n e d : Nn) (r : ℝ) (c : ℝ) (v : Nn) :
    linThird hd hd2 D3Nu D3Nv bu bn n e d r (c • v) =
      c • linThird hd hd2 D3Nu D3Nv bu bn n e d r v := by
  simp only [linThird, map_smul, ContinuousLinearMap.smul_apply, Prod.smul_mk, smul_add]

/-- The linear part cancels in combinations with `Σ aᵢvᵢ = 0`. -/
theorem linThird_comb (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (n e d : Nn) (r : ℝ) (a : Fin 3 → ℝ) (v : Fin 3 → Nn)
    (hsum : ∑ i, a i • v i = 0) :
    ∑ i, a i • linThird hd hd2 D3Nu D3Nv bu bn n e d r (v i) = 0 := by
  have h0 : linThird hd hd2 D3Nu D3Nv bu bn n e d r 0 = 0 := by
    have := linThird_smul (D3Nu := D3Nu) (D3Nv := D3Nv) hd hd2 bu bn n e d r 0 0
    simpa using this
  rw [Fin.sum_univ_three] at hsum ⊢
  rw [← linThird_smul, ← linThird_smul, ← linThird_smul, ← linThird_add, ← linThird_add, hsum, h0]

/-- The uniform constant of the third level. -/
def GraphC2Hyp.Cb {hd : GraphC1Hyp h DNu DNv L₂} (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) : ℝ :=
  max 1 (max (M / (1 - h.q)) (max (6 * hd.K1) (max (6 * hd2.Kd) (max L₂ L₃))))

section CbFacts

variable {hd : GraphC1Hyp h DNu DNv L₂} (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)

theorem GraphC2Hyp.one_le_Cb : 1 ≤ hd2.Cb := le_max_left _ _
theorem GraphC2Hyp.C1_le_Cb : M / (1 - h.q) ≤ hd2.Cb :=
  (le_max_left _ _).trans (le_max_right _ _)
theorem GraphC2Hyp.K1_le_Cb : 6 * hd.K1 ≤ hd2.Cb :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
theorem GraphC2Hyp.Kd_le_Cb : 6 * hd2.Kd ≤ hd2.Cb :=
  (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
theorem GraphC2Hyp.L₂_le_Cb : L₂ ≤ hd2.Cb :=
  ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
theorem GraphC2Hyp.L₃_le_Cb : L₃ ≤ hd2.Cb :=
  ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
theorem GraphC2Hyp.K1'_le_Cb : hd.K1 ≤ hd2.Cb := by
  have := hd.K1_nonneg; linarith [hd2.K1_le_Cb]
theorem GraphC2Hyp.Kd'_le_Cb : hd2.Kd ≤ hd2.Cb := by
  have := hd2.Kd_nonneg; linarith [hd2.Kd_le_Cb]

end CbFacts

theorem le_mul_cb {y a Cb X Y : ℝ} (hy : y ≤ a * X) (ha : a ≤ Cb) (hX : 0 ≤ X)
    (hY : Cb * X = Y) : y ≤ Y := hY ▸ hy.trans (mul_le_mul_of_nonneg_right ha hX)

theorem clm_sub_apply_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A B : E →L[ℝ] F) (x : E) {c : ℝ}
    (hc : ‖A - B‖ ≤ c) : ‖A x - B x‖ ≤ c * ‖x‖ := by
  rw [← ContinuousLinearMap.sub_apply]
  exact ((A - B).le_opNorm x).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

theorem clm_sub3_apply_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A B C : E →L[ℝ] F) (x : E) {c : ℝ}
    (hc : ‖A - B - C‖ ≤ c) : ‖A x - B x - C x‖ ≤ c * ‖x‖ := by
  rw [← ContinuousLinearMap.sub_apply, ← ContinuousLinearMap.sub_apply]
  exact ((A - B - C).le_opNorm x).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

theorem clm2_sub_apply_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A B : E →L[ℝ] E →L[ℝ] F) (x y : E) {c : ℝ}
    (hc : ‖A - B‖ ≤ c) : ‖A x y - B x y‖ ≤ c * ‖x‖ * ‖y‖ := by
  rw [← ContinuousLinearMap.sub_apply, ← ContinuousLinearMap.sub_apply]
  exact ((A - B).le_opNorm₂ x y).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) (norm_nonneg _))

/-- The third-level source minus its linear part, componentwise, is `thirdErr`. -/
theorem thirdSrc_sub_linThird (hd : GraphC1Hyp h DNu DNv L₂)
    (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) (bu : U) (bn : Nn) (n e d v : Nn) (r : ℝ) :
    thirdSrc hd hd2 bu bn n e d v r - linThird hd hd2 D3Nu D3Nv bu bn n e d r v =
      (thirdErr DNu D2Nu D3Nu (yStar h bu bn n r) (trajDiff h bu bn n v r)
          (traj1 hd bu bn r n v) (traj1 hd bu bn r n e) (traj1 hd bu bn r n d)
          (traj1 hd bu bn r (n + v) e) (traj1 hd bu bn r (n + v) d)
          (traj2 hd hd2 bu bn r n v e) (traj2 hd hd2 bu bn r n v d)
          (traj2 hd hd2 bu bn r n e d) (traj2 hd hd2 bu bn r (n + v) e d),
        thirdErr DNv D2Nv D3Nv (yStar h bu bn n r) (trajDiff h bu bn n v r)
          (traj1 hd bu bn r n v) (traj1 hd bu bn r n e) (traj1 hd bu bn r n d)
          (traj1 hd bu bn r (n + v) e) (traj1 hd bu bn r (n + v) d)
          (traj2 hd hd2 bu bn r n v e) (traj2 hd hd2 bu bn r n v d)
          (traj2 hd hd2 bu bn r n e d) (traj2 hd hd2 bu bn r (n + v) e d)) := by
  have hy := yStar_add_eq (h := h) bu bn n v r
  simp only [thirdSrc, linThird, thirdErr, var2Src, linSrc, Pi.sub_apply, Prod.mk_sub_mk, hy,
    map_sub, ContinuousLinearMap.sub_apply]
  congr 1 <;> abel

/-- The two bounds of `thirdErr` for one component `f = DN`, `Df = D²N`, `D2f = D³N`, from the
regularity of the nonlinearity and the trajectory bounds. -/
theorem thirdErr_both_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → E →L[ℝ] G}
    {Df : E → E →L[ℝ] E →L[ℝ] G} {D2f : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] G}
    {L₂ L₃ Cb ω s E' pe pd : ℝ} (hL₂0 : 0 ≤ L₂) (hL₃0 : 0 ≤ L₃) (hL₂ : L₂ ≤ Cb) (hL₃ : L₃ ≤ Cb)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hDf : ∀ x, HasFDerivAt Df (D2f x) x)
    (hfl : ∀ x x', ‖f x - f x'‖ ≤ L₂ * ‖x - x'‖) (hDfl : ∀ x x', ‖Df x - Df x'‖ ≤ L₃ * ‖x - x'‖)
    (hCb : 1 ≤ Cb) (hs : 0 ≤ s) (hE : 1 ≤ E') (hpe : 0 ≤ pe) (hpd : 0 ≤ pd) (hω0 : 0 ≤ ω)
    (y w Av Ae Ad Ae' Ad' Bve Bvd Bed Bed' : E)
    (hωf : ∀ z ∈ Metric.closedBall y ‖w‖, ‖D2f z - D2f y‖ ≤ ω)
    (hw : ‖w‖ ≤ Cb * s * E') (hwl : ‖w - Av‖ ≤ Cb * s ^ 2 * E' ^ 2) (hAv : ‖Av‖ ≤ Cb * s * E')
    (hAe : ‖Ae‖ ≤ Cb * E' * pe) (hAd : ‖Ad‖ ≤ Cb * E' * pd)
    (hAe' : ‖Ae'‖ ≤ Cb * E' * pe) (hAd' : ‖Ad'‖ ≤ Cb * E' * pd)
    (hdAe : ‖Ae' - Ae‖ ≤ Cb * s * E' ^ 2 * pe) (hdAd : ‖Ad' - Ad‖ ≤ Cb * s * E' ^ 2 * pd)
    (hRe : ‖Ae' - Ae - Bve‖ ≤ Cb * s ^ 2 * E' ^ 3 * pe)
    (hRd : ‖Ad' - Ad - Bvd‖ ≤ Cb * s ^ 2 * E' ^ 3 * pd)
    (hBve : ‖Bve‖ ≤ Cb * s * E' ^ 2 * pe) (hBvd : ‖Bvd‖ ≤ Cb * s * E' ^ 2 * pd)
    (hBed : ‖Bed‖ ≤ Cb * E' ^ 2 * pe * pd) (hBed' : ‖Bed'‖ ≤ Cb * E' ^ 2 * pe * pd)
    (hdB : ‖Bed' - Bed‖ ≤ Cb * s * E' ^ 3 * pe * pd) :
    ‖thirdErr f Df D2f y w Av Ae Ad Ae' Ad' Bve Bvd Bed Bed'‖ ≤
        8 * Cb ^ 4 * s * E' ^ 3 * pe * pd ∧
      ‖thirdErr f Df D2f y w Av Ae Ad Ae' Ad' Bve Bvd Bed Bed'‖ ≤
        (9 * Cb ^ 4 * s * E' + Cb ^ 3 * ω) * s * E' ^ 3 * pe * pd := by
  have hDfb : ‖Df y‖ ≤ Cb := (norm_D2_le hL₂0 hfl hf y).trans hL₂
  have hD2fb : ‖D2f y‖ ≤ Cb := (norm_D2_le hL₃0 hDfl hDf y).trans hL₃
  have hfL : ‖f (y + w) - f y‖ ≤ Cb * ‖w‖ := by
    have := hfl (y + w) y
    rw [add_sub_cancel_left] at this
    exact this.trans (mul_le_mul_of_nonneg_right hL₂ (norm_nonneg _))
  have hDfL : ‖Df (y + w) - Df y‖ ≤ Cb * ‖w‖ := by
    have := hDfl (y + w) y
    rw [add_sub_cancel_left] at this
    exact this.trans (mul_le_mul_of_nonneg_right hL₃ (norm_nonneg _))
  have hfT : ‖f (y + w) - f y - Df y w‖ ≤ Cb * ‖w‖ ^ 2 :=
    (GraphC1Hyp.taylor_le hL₃0 hf hDfl y w).trans
      (mul_le_mul_of_nonneg_right hL₃ (by positivity))
  have hDfM := taylor_modulus_le hDf y w hωf
  exact ⟨thirdErr_crude_le hCb hs hE hpe hpd _ _ _ _ _ _ _ _ _ _ _ hfL hDfL hDfb hD2fb hw
    hAv hAe hAd hAe' hAd' hdAe hdAd hBve hBvd hBed hBed',
    thirdErr_fine_le hCb hs hE hpe hpd hω0 _ _ _ _ _ _ _ _ _ _ _ hfT hDfM hDfb hD2fb
      hw hwl hAv hAe hAe' hAd' hdAe hdAd hRe hRd hBve hBed' hdB⟩

/-- **Per-direction bounds of the third-level source** at time `r ≥ 0` (`E = e^{νr}`): the crude
bound `8 C_b⁴ ‖v‖ E³ ‖e‖‖d‖`, and, if `‖D³N(z) - D³N(y)‖ ≤ ω` on the ball `B(y, ‖w‖)`, the fine
bound `(9 C_b⁴ ‖v‖ E + C_b³ ω) ‖v‖ E³ ‖e‖‖d‖`. -/
theorem third_err_le (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (hd3 : GraphC3Hyp hd2 D3Nu D3Nv) (bu : U) (bn : Nn) (n e d v : Nn) {r : ℝ} (hr : 0 ≤ r)
    {ω : ℝ} (hω0 : 0 ≤ ω)
    (hωu : ∀ z ∈ Metric.closedBall (yStar h bu bn n r) ‖trajDiff h bu bn n v r‖,
      ‖D3Nu z - D3Nu (yStar h bu bn n r)‖ ≤ ω)
    (hωv : ∀ z ∈ Metric.closedBall (yStar h bu bn n r) ‖trajDiff h bu bn n v r‖,
      ‖D3Nv z - D3Nv (yStar h bu bn n r)‖ ≤ ω) :
    ‖thirdSrc hd hd2 bu bn n e d v r - linThird hd hd2 D3Nu D3Nv bu bn n e d r v‖ ≤
        8 * hd2.Cb ^ 4 * ‖v‖ * exp (ν * r) ^ 3 * ‖e‖ * ‖d‖ ∧
      ‖thirdSrc hd hd2 bu bn n e d v r - linThird hd hd2 D3Nu D3Nv bu bn n e d r v‖ ≤
        (9 * hd2.Cb ^ 4 * ‖v‖ * exp (ν * r) + hd2.Cb ^ 3 * ω) * ‖v‖ * exp (ν * r) ^ 3 *
          ‖e‖ * ‖d‖ := by
  have hν := h.ν_pos
  have hCb1 : 1 ≤ hd2.Cb := hd2.one_le_Cb
  have hC1 := hd2.C1_le_Cb
  have hK1 := hd2.K1_le_Cb
  have hK1' := hd2.K1'_le_Cb
  have hKd := hd2.Kd_le_Cb
  have hKd' := hd2.Kd'_le_Cb
  have hE1 : 1 ≤ exp (ν * r) := one_le_exp (by positivity)
  have hE0 : 0 ≤ exp (ν * r) := (exp_pos _).le
  have hE2 : exp (2 * ν * r) = exp (ν * r) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have hE3 : exp (3 * ν * r) = exp (ν * r) ^ 3 := by rw [← exp_nat_mul]; ring_nf
  have hmr : max r 0 = r := max_eq_left hr
  have hs := norm_nonneg v
  -- trajectory bounds
  have hw : ‖trajDiff h bu bn n v r‖ ≤ hd2.Cb * ‖v‖ * exp (ν * r) :=
    le_mul_cb (X := ‖v‖ * exp (ν * r))
      ((norm_trajDiff_le (h := h) bu bn n v r).trans (le_of_eq (by ring))) hC1 (by positivity)
      (by ring)
  have hwl : ‖trajDiff h bu bn n v r - traj1 hd bu bn r n v‖ ≤
      hd2.Cb * ‖v‖ ^ 2 * exp (ν * r) ^ 2 := by
    have h0 := traj1_taylor hd bu bn r n v
    rw [hmr, hE2] at h0
    have e0 : trajAt h bu bn r (n + v) - trajAt h bu bn r n = trajDiff h bu bn n v r := by
      simp [trajAt, hmr, trajDiff]
    rw [e0] at h0
    exact le_mul_cb (X := ‖v‖ ^ 2 * exp (ν * r) ^ 2) (h0.trans (le_of_eq (by ring))) hK1'
      (by positivity) (by ring)
  have hA : ∀ m x, ‖traj1 hd bu bn r m x‖ ≤ hd2.Cb * exp (ν * r) * ‖x‖ := fun m x =>
    le_mul_cb (X := exp (ν * r) * ‖x‖)
      ((traj1_apply_le hd bu bn hr m x).trans (le_of_eq (by ring))) hC1 (by positivity) (by ring)
  have hAv : ‖traj1 hd bu bn r n v‖ ≤ hd2.Cb * ‖v‖ * exp (ν * r) :=
    (hA n v).trans (le_of_eq (by ring))
  have hdA : ∀ x, ‖traj1 hd bu bn r (n + v) x - traj1 hd bu bn r n x‖ ≤
      hd2.Cb * ‖v‖ * exp (ν * r) ^ 2 * ‖x‖ := fun x => by
    have h0 := traj1_lip hd bu bn r (n + v) n
    rw [add_sub_cancel_left, hmr, hE2] at h0
    exact le_mul_cb (X := ‖v‖ * exp (ν * r) ^ 2 * ‖x‖)
      ((clm_sub_apply_le _ _ x h0).trans (le_of_eq (by ring))) hK1 (by positivity) (by ring)
  have hR : ∀ x, ‖traj1 hd bu bn r (n + v) x - traj1 hd bu bn r n x -
      traj2 hd hd2 bu bn r n v x‖ ≤ hd2.Cb * ‖v‖ ^ 2 * exp (ν * r) ^ 3 * ‖x‖ := fun x => by
    have h0 := traj2_taylor hd hd2 bu bn r n v
    rw [hmr, hE3] at h0
    exact le_mul_cb (X := ‖v‖ ^ 2 * exp (ν * r) ^ 3 * ‖x‖)
      ((clm_sub3_apply_le _ _ _ x h0).trans (le_of_eq (by ring))) hKd' (by positivity) (by ring)
  have hB : ∀ m x z, ‖traj2 hd hd2 bu bn r m x z‖ ≤
      hd2.Cb * exp (ν * r) ^ 2 * ‖x‖ * ‖z‖ := fun m x z =>
    le_mul_cb (X := exp (ν * r) ^ 2 * ‖x‖ * ‖z‖)
      ((traj2_apply_le hd hd2 bu bn hr m x z).trans (le_of_eq (by rw [hE2]; ring))) hK1
      (by positivity) (by ring)
  have hBv : ∀ x, ‖traj2 hd hd2 bu bn r n v x‖ ≤ hd2.Cb * ‖v‖ * exp (ν * r) ^ 2 * ‖x‖ :=
    fun x => (hB n v x).trans (le_of_eq (by ring))
  have hdB : ‖traj2 hd hd2 bu bn r (n + v) e d - traj2 hd hd2 bu bn r n e d‖ ≤
      hd2.Cb * ‖v‖ * exp (ν * r) ^ 3 * ‖e‖ * ‖d‖ := by
    have h0 := traj2_lip hd hd2 bu bn r (n + v) n
    rw [add_sub_cancel_left, hmr, hE3] at h0
    exact le_mul_cb (X := ‖v‖ * exp (ν * r) ^ 3 * ‖e‖ * ‖d‖)
      ((clm2_sub_apply_le _ _ e d h0).trans (le_of_eq (by ring))) hKd (by positivity) (by ring)
  have hu := thirdErr_both_le hd.L₂_nonneg hd2.L₃_nonneg hd2.L₂_le_Cb hd2.L₃_le_Cb
    hd2.hasDeriv2_u hd3.hasDeriv3_u hd.Du_lip hd2.D2u_lip hCb1 hs hE1 (norm_nonneg e)
    (norm_nonneg d) hω0 _ _ _ _ _ _ _ _ _ _ _ hωu hw hwl hAv (hA n e) (hA n d) (hA _ e) (hA _ d)
    (hdA e) (hdA d) (hR e) (hR d) (hBv e) (hBv d) (hB n e d) (hB _ e d) hdB
  have hv := thirdErr_both_le hd.L₂_nonneg hd2.L₃_nonneg hd2.L₂_le_Cb hd2.L₃_le_Cb
    hd2.hasDeriv2_v hd3.hasDeriv3_v hd.Dv_lip hd2.D2v_lip hCb1 hs hE1 (norm_nonneg e)
    (norm_nonneg d) hω0 _ _ _ _ _ _ _ _ _ _ _ hωv hw hwl hAv (hA n e) (hA n d) (hA _ e) (hA _ d)
    (hdA e) (hdA d) (hR e) (hR d) (hBv e) (hBv d) (hB n e d) (hB _ e d) hdB
  rw [thirdSrc_sub_linThird]
  exact ⟨norm_prod_le_of_le hu.1 hv.1, norm_prod_le_of_le hu.2 hv.2⟩

/-- **Third-level a priori bound.** For any increments `vᵢ`, `Z = Σ aᵢ (Y₂(n+vᵢ) - Y₂(n)) e d`
solves `Z = 𝒮[DN(y_*) Z] + 𝒮[Σ aᵢ S_{vᵢ}]` (`S_v = thirdSrc`, by the second variational equation
at the base points `n + vᵢ` and `n`); if the combined source has growth `σ e^{κr}` in an admissible
weight `κ ≥ 3ν` (`κ < β`, `q_κ < 1`), then `‖Z(0)‖ ≤ M σ c_κ / (1 - q_κ)`. -/
theorem third_level_le (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (n e d : Nn) (a : Fin 3 → ℝ) (v : Fin 3 → Nn) {κ σ : ℝ}
    (h3κ : 3 * ν ≤ κ) (hκβ : κ < β) (hq : M * L * ((κ - α)⁻¹ + (β - κ)⁻¹) < 1) (hσ : 0 ≤ σ)
    (hS : ∀ r, 0 ≤ r → ‖∑ i, a i • thirdSrc hd hd2 bu bn n e d (v i) r‖ ≤ σ * exp (κ * r)) :
    ‖∑ i, a i • (traj2 hd hd2 bu bn 0 (n + v i) e d - traj2 hd hd2 bu bn 0 n e d)‖ ≤
      M * σ * ((κ - α)⁻¹ + (β - κ)⁻¹) / (1 - M * L * ((κ - α)⁻¹ + (β - κ)⁻¹)) := by
  have hν := h.ν_pos
  have h3β := hd2.three_lt
  have hακ : α < κ := by linarith [h.α_lt]
  set z : Fin 3 → ℝ → U × Nn := fun i r =>
    traj2 hd hd2 bu bn r (n + v i) e d - traj2 hd hd2 bu bn r n e d with hzdef
  set Z : ℝ → U × Nn := ∑ i, a i • z i with hZdef
  have hzc : ∀ i, Continuous (z i) := fun i =>
    (traj2_apply_continuous hd hd2 bu bn _ e d).sub (traj2_apply_continuous hd hd2 bu bn n e d)
  have hZfun : Z = fun r => ∑ i, a i • z i r := by funext r; simp [hZdef, Finset.sum_apply]
  have hZc : Continuous Z := by
    rw [hZfun]; exact continuous_finsetSum _ fun i _ => (hzc i).const_smul (a i)
  have hzb : ∀ i r, 0 ≤ r → ‖z i r‖ ≤ (6 * hd2.Kd * ‖v i‖ * ‖e‖ * ‖d‖) * exp (3 * ν * r) :=
    fun i r hr => by
      have h0 := traj2_lip hd hd2 bu bn r (n + v i) n
      rw [add_sub_cancel_left, max_eq_left hr] at h0
      exact (clm2_sub_apply_le _ _ e d h0).trans (le_of_eq (by ring))
  have hZb : ∀ r, 0 ≤ r → ‖Z r‖ ≤
      (∑ i, |a i| * (6 * hd2.Kd * ‖v i‖ * ‖e‖ * ‖d‖)) * exp (κ * r) := fun r hr => by
    rw [hZfun, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((hzb i r hr).trans ?_) (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left (exp_mul_le_exp_mul h3κ hr)
      (by have := hd2.Kd_nonneg; positivity)
  set W : Fin 3 → ℝ → U × Nn := fun i => linSrc DNu DNv (yStar h bu bn n) (z i) with hWdef
  have hWc : ∀ i, Continuous (W i) := fun i => linSrc_continuous hd bu bn n (hzc i)
  have hWb : ∀ i r, 0 ≤ r → ‖W i r‖ ≤
      (L * (6 * hd2.Kd * ‖v i‖ * ‖e‖ * ‖d‖)) * exp (3 * ν * r) := fun i r hr =>
    (norm_linSrc_le hd _ _ r).trans (by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hzb i r hr) h.L_nonneg)
  have hVc : ∀ i, Continuous (var2Src hd hd2 bu bn (n + v i) e d - var2Src hd hd2 bu bn n e d) :=
    fun i => (var2Src_continuous hd hd2 bu bn _ e d).sub (var2Src_continuous hd hd2 bu bn n e d)
  set CV := (L * (6 * hd.K1) + L₂ * (M / (1 - h.q)) ^ 2) * ‖e‖ * ‖d‖ with hCV
  have hVb : ∀ i r, 0 ≤ r →
      ‖(var2Src hd hd2 bu bn (n + v i) e d - var2Src hd hd2 bu bn n e d) r‖ ≤
        (CV + CV) * exp (3 * ν * r) := fun i r hr => by
    rw [Pi.sub_apply, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add (var2Src_le hd hd2 bu bn _ e d hr)
      (var2Src_le hd hd2 bu bn n e d hr))
  have hTc : ∀ i, Continuous (thirdSrc hd hd2 bu bn n e d (v i)) := fun i => (hVc i).sub (hWc i)
  have hTb : ∀ i r, 0 ≤ r → ‖thirdSrc hd hd2 bu bn n e d (v i) r‖ ≤
      (CV + CV + L * (6 * hd2.Kd * ‖v i‖ * ‖e‖ * ‖d‖)) * exp (3 * ν * r) := fun i r hr => by
    have e0 : thirdSrc hd hd2 bu bn n e d (v i) r =
        (var2Src hd hd2 bu bn (n + v i) e d - var2Src hd hd2 bu bn n e d) r - W i r := rfl
    rw [e0, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hVb i r hr) (hWb i r hr))
  -- per-direction identity
  have hid : ∀ i t, 0 ≤ t → z i t =
      srcOp Pu Pn (thirdSrc hd hd2 bu bn n e d (v i)) t + srcOp Pu Pn (W i) t := by
    intro i t ht
    have e1 : z i t = srcOp Pu Pn (var2Src hd hd2 bu bn (n + v i) e d) t -
        srcOp Pu Pn (var2Src hd hd2 bu bn n e d) t := by
      simp only [hzdef]
      rw [traj2_eq hd hd2 bu bn (n + v i) e d ht, traj2_eq hd hd2 bu bn n e d ht]
    have e2 : srcOp Pu Pn (thirdSrc hd hd2 bu bn n e d (v i)) t =
        (srcOp Pu Pn (var2Src hd hd2 bu bn (n + v i) e d) t -
          srcOp Pu Pn (var2Src hd hd2 bu bn n e d) t) - srcOp Pu Pn (W i) t := by
      have e3 : thirdSrc hd hd2 bu bn n e d (v i) =
          (var2Src hd hd2 bu bn (n + v i) e d - var2Src hd hd2 bu bn n e d) - W i := rfl
      rw [e3, srcOp_sub' h.Pu_cont h.Pn_cont h3β h.M_nonneg h.Pu_bound (hVc i) (hWc i)
        (hVb i) (hWb i) ht, srcOp_sub' h.Pu_cont h.Pn_cont h3β h.M_nonneg h.Pu_bound
        (var2Src_continuous hd hd2 bu bn _ e d) (var2Src_continuous hd hd2 bu bn n e d)
        (fun r hr => var2Src_le hd hd2 bu bn _ e d hr) (fun r hr => var2Src_le hd hd2 bu bn n e d hr)
        ht]
    rw [e1, e2]; abel
  -- the combined equation
  have hE : ∀ t, 0 ≤ t → ‖Z t - srcOp Pu Pn (fun r => (DNu (yStar h bu bn n r) (Z r),
      DNv (yStar h bu bn n r) (Z r))) t‖ ≤
        (M * σ * ((κ - α)⁻¹ + (β - κ)⁻¹)) * exp (κ * t) := by
    intro t ht
    have hlin : (fun r => (DNu (yStar h bu bn n r) (Z r), DNv (yStar h bu bn n r) (Z r))) =
        ∑ i, a i • W i := by
      have : (fun r => (DNu (yStar h bu bn n r) (Z r), DNv (yStar h bu bn n r) (Z r))) =
          linSrc DNu DNv (yStar h bu bn n) Z := rfl
      rw [this, hZdef, linSrc_sum]
    have hsum1 := srcOp_sum h.Pu_cont h.Pn_cont h3β h.M_nonneg h.Pu_bound Finset.univ a
      (fun i => thirdSrc hd hd2 bu bn n e d (v i)) hTc _ hTb ht
    have hsum2 := srcOp_sum h.Pu_cont h.Pn_cont h3β h.M_nonneg h.Pu_bound Finset.univ a W hWc _
      hWb ht
    have hZt : Z t = ∑ i, a i • z i t := by rw [hZfun]
    have hkey : Z t - srcOp Pu Pn (fun r => (DNu (yStar h bu bn n r) (Z r),
        DNv (yStar h bu bn n r) (Z r))) t =
        srcOp Pu Pn (∑ i, a i • thirdSrc hd hd2 bu bn n e d (v i)) t := by
      rw [hlin, hsum1, hsum2, hZt]
      simp only [hid _ t ht, smul_add, Finset.sum_add_distrib]
      abel
    rw [hkey]
    have hSc : Continuous (∑ i, a i • thirdSrc hd hd2 bu bn n e d (v i)) := by
      have : (∑ i, a i • thirdSrc hd hd2 bu bn n e d (v i)) =
          fun r => ∑ i, a i • thirdSrc hd hd2 bu bn n e d (v i) r := by
        funext r; simp [Finset.sum_apply]
      rw [this]; exact continuous_finsetSum _ fun i _ => (hTc i).const_smul (a i)
    refine (srcOp_norm_le h.Pu_cont h.Pn_cont hακ hκβ h.M_nonneg h.Pu_bound h.Pn_bound hSc
      (fun r hr => by rw [Finset.sum_apply]; exact hS r hr) ht).trans (le_of_eq (by ring))
  have hσ' : 0 ≤ M * σ * ((κ - α)⁻¹ + (β - κ)⁻¹) := by
    have h1 : 0 < κ - α := by linarith
    have h2 : 0 < β - κ := by linarith
    have := h.M_nonneg
    positivity
  have hap := apriori_le h.Pu_cont h.Pn_cont hακ hκβ h.M_nonneg h.L_nonneg h.Pu_bound h.Pn_bound
    hq (hd.continuous_DNu.comp (yStar_continuous h bu bn n))
    (hd.continuous_DNv.comp (yStar_continuous h bu bn n)) (fun r => hd.norm_DNu_le _)
    (fun r => hd.norm_DNv_le _) hZc hZb hσ' hE (le_refl (0 : ℝ))
  have hZ0 : Z 0 = ∑ i, a i • (traj2 hd hd2 bu bn 0 (n + v i) e d - traj2 hd hd2 bu bn 0 n e d) := by
    rw [hZfun]
  rw [← hZ0]
  refine hap.trans (le_of_eq ?_)
  rw [mul_zero, exp_zero, mul_one]

/-- An admissible weight strictly above `3ν`: by continuity, the strict `j = 3` inequality
persists for some `κ ∈ (3ν, β)`. -/
theorem exists_weight_gt {M L α β ν : ℝ} (h3α : α < 3 * ν) (h3β : 3 * ν < β)
    (hq : M * L * ((3 * ν - α)⁻¹ + (β - 3 * ν)⁻¹) < 1) :
    ∃ κ, 3 * ν < κ ∧ κ < β ∧ M * L * ((κ - α)⁻¹ + (β - κ)⁻¹) < 1 := by
  have h1 : 3 * ν - α ≠ 0 := by linarith
  have h2 : β - 3 * ν ≠ 0 := by linarith
  have hc : ContinuousAt (fun κ : ℝ => M * L * ((κ - α)⁻¹ + (β - κ)⁻¹)) (3 * ν) :=
    continuousAt_const.mul (((continuousAt_id.sub continuousAt_const).inv₀ h1).add
      ((continuousAt_const.sub continuousAt_id).inv₀ h2))
  have hmem : (fun κ : ℝ => M * L * ((κ - α)⁻¹ + (β - κ)⁻¹)) ⁻¹' Iio 1 ∩ Iio β ∈ 𝓝 (3 * ν) :=
    Filter.inter_mem (hc.preimage_mem_nhds (Iio_mem_nhds hq)) (Iio_mem_nhds h3β)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  have hin : 3 * ν + ε / 2 ∈ Metric.ball (3 * ν) ε := by
    rw [Metric.mem_ball, Real.dist_eq, show 3 * ν + ε / 2 - 3 * ν = ε / 2 by ring,
      abs_of_pos (by positivity)]
    linarith
  obtain ⟨hA, hB⟩ := hball hin
  exact ⟨3 * ν + ε / 2, by linarith, hB, hA⟩

/-- Heine–Cantor at a compact set: `F` is uniformly continuous *at* `K`. -/
theorem uc_compact {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {K : Set X}
    (hK : IsCompact K) {F : X → Y} (hF : Continuous F) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ x ∈ K, ∀ z, dist x z < ρ → dist (F x) (F z) < η := by
  have := hK.uniformContinuousAt_of_continuousAt F (fun a _ => hF.continuousAt)
    (Metric.dist_mem_uniformity hη)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_uniformity_dist.1 this
  exact ⟨ρ, hρ, fun x hx z hxz => hball hxz hx⟩

theorem D3_sub_le_two {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {D2f : U × Nn → (U × Nn) →L[ℝ] (U × Nn) →L[ℝ] G}
    {D3f : U × Nn → (U × Nn) →L[ℝ] (U × Nn) →L[ℝ] (U × Nn) →L[ℝ] G} {L₃ C : ℝ} (hL₃ : 0 ≤ L₃)
    (hLC : L₃ ≤ C) (hD : ∀ x, HasFDerivAt D2f (D3f x) x)
    (hL : ∀ x x', ‖D2f x - D2f x'‖ ≤ L₃ * ‖x - x'‖) (z y : U × Nn) :
    ‖D3f z - D3f y‖ ≤ 2 * C := by
  have h1 := (norm_D2_le hL₃ hL hD z).trans hLC
  have h2 := (norm_D2_le hL₃ hL hD y).trans hLC
  exact (norm_sub_le _ _).trans (by linarith)

/-- **Crude case `r ≥ T`** of the third-level source bound: if `8C_b⁴ ≤ η e^{(κ-3ν)T}`, the
third-level error is `≤ η ‖v‖‖e‖‖d‖ e^{κr}` for `r ≥ T`. -/
theorem third_err_late (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (hd3 : GraphC3Hyp hd2 D3Nu D3Nv) (bu : U) (bn : Nn) (n e d v : Nn) {κ η T r : ℝ}
    (hη : 0 < η) (hT : 0 ≤ T) (hTr : T ≤ r)
    (hTbig : 8 * hd2.Cb ^ 4 ≤ η * exp ((κ - 3 * ν) * T)) (h3κ : 3 * ν ≤ κ) :
    ‖thirdSrc hd hd2 bu bn n e d v r - linThird hd hd2 D3Nu D3Nv bu bn n e d r v‖ ≤
      (η * ‖v‖ * ‖e‖ * ‖d‖) * exp (κ * r) := by
  have hr : 0 ≤ r := hT.trans hTr
  have hCb1 : 1 ≤ hd2.Cb := hd2.one_le_Cb
  have hcrude := (third_err_le hd hd2 hd3 bu bn n e d v hr (ω := 2 * hd2.Cb) (by positivity)
    (fun z _ => D3_sub_le_two hd2.L₃_nonneg hd2.L₃_le_Cb hd3.hasDeriv3_u hd2.D2u_lip z _)
    (fun z _ => D3_sub_le_two hd2.L₃_nonneg hd2.L₃_le_Cb hd3.hasDeriv3_v hd2.D2v_lip z _)).1
  have hE3 : exp (ν * r) ^ 3 = exp (3 * ν * r) := by rw [← exp_nat_mul]; ring_nf
  have hk : exp (κ * r) = exp (3 * ν * r) * exp ((κ - 3 * ν) * r) := by
    rw [← exp_add]; ring_nf
  have hεT : exp ((κ - 3 * ν) * T) ≤ exp ((κ - 3 * ν) * r) :=
    exp_le_exp.2 (mul_le_mul_of_nonneg_left hTr (by linarith))
  have hP : 0 ≤ ‖v‖ * ‖e‖ * ‖d‖ := by positivity
  calc _ ≤ 8 * hd2.Cb ^ 4 * ‖v‖ * exp (ν * r) ^ 3 * ‖e‖ * ‖d‖ := hcrude
    _ = (8 * hd2.Cb ^ 4) * (‖v‖ * ‖e‖ * ‖d‖) * exp (3 * ν * r) := by rw [hE3]; ring
    _ ≤ (η * exp ((κ - 3 * ν) * T)) * (‖v‖ * ‖e‖ * ‖d‖) * exp (3 * ν * r) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hTbig hP) (exp_pos _).le
    _ ≤ (η * exp ((κ - 3 * ν) * r)) * (‖v‖ * ‖e‖ * ‖d‖) * exp (3 * ν * r) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hεT hη.le) hP) (exp_pos _).le
    _ = (η * ‖v‖ * ‖e‖ * ‖d‖) * exp (κ * r) := by rw [hk]; ring

/-- **Fine case `r ≤ T`** of the third-level source bound: if `‖D³N(z) - D³N(x)‖ < ω₀/2` for `x`
on the compact set `y_*(n₀)([0, T])` and `dist(x, z) < ρ`, and the base point and increment are
small (`‖n - n₀‖, ‖v‖ ≤ ρ/(2(C_b e^{νT} + 1))`, `‖v‖ ≤ η/(18 C_b⁴ e^{νT})`, `ω₀ = η/(2C_b³)`),
the third-level error is `≤ η ‖v‖‖e‖‖d‖ e^{κr}` for `0 ≤ r ≤ T`. -/
theorem third_err_early (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (hd3 : GraphC3Hyp hd2 D3Nu D3Nv) (bu : U) (bn : Nn) (n₀ n e d v : Nn) {κ η T r ρ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hr : 0 ≤ r) (hrT : r ≤ T) (h3κ : 3 * ν ≤ κ)
    (huc : ∀ x ∈ (fun s => yStar h bu bn n₀ s) '' Icc 0 T, ∀ z, dist x z < ρ →
      dist (D3Nu x, D3Nv x) (D3Nu z, D3Nv z) < η / (2 * hd2.Cb ^ 3) / 2)
    (hn : ‖n - n₀‖ ≤ ρ / (2 * (hd2.Cb * exp (ν * T) + 1)))
    (hv₂ : ‖v‖ ≤ ρ / (2 * (hd2.Cb * exp (ν * T) + 1)))
    (hv₁ : ‖v‖ ≤ η / (18 * hd2.Cb ^ 4 * exp (ν * T))) :
    ‖thirdSrc hd hd2 bu bn n e d v r - linThird hd hd2 D3Nu D3Nv bu bn n e d r v‖ ≤
      (η * ‖v‖ * ‖e‖ * ‖d‖) * exp (κ * r) := by
  have hν := h.ν_pos
  have hCb1 : 1 ≤ hd2.Cb := hd2.one_le_Cb
  have hCb0 : 0 < hd2.Cb := by linarith
  have hC1 := hd2.C1_le_Cb
  have hET : 1 ≤ exp (ν * T) := one_le_exp (by nlinarith)
  set ω₀ := η / (2 * hd2.Cb ^ 3) with hω₀def
  have hω₀ : 0 < ω₀ := by positivity
  set δ₂ := ρ / (2 * (hd2.Cb * exp (ν * T) + 1)) with hδ₂def
  have hx : yStar h bu bn n₀ r ∈ (fun s => yStar h bu bn n₀ s) '' Icc 0 T := ⟨r, ⟨hr, hrT⟩, rfl⟩
  have hEr : exp (ν * r) ≤ exp (ν * T) := exp_le_exp.2 (mul_le_mul_of_nonneg_left hrT hν.le)
  have hdy : ‖yStar h bu bn n r - yStar h bu bn n₀ r‖ ≤ hd2.Cb * δ₂ * exp (ν * T) := by
    refine (norm_yStar_sub_le h bu bn n n₀ r).trans ?_
    have h1 : M / (1 - h.q) * ‖n - n₀‖ ≤ hd2.Cb * δ₂ :=
      mul_le_mul hC1 hn (norm_nonneg _) hCb0.le
    exact mul_le_mul h1 hEr (exp_pos _).le (by positivity)
  have hdw : ‖trajDiff h bu bn n v r‖ ≤ hd2.Cb * δ₂ * exp (ν * T) := by
    refine (norm_trajDiff_le (h := h) bu bn n v r).trans ?_
    have h1 : M / (1 - h.q) * ‖v‖ ≤ hd2.Cb * δ₂ := mul_le_mul hC1 hv₂ (norm_nonneg _) hCb0.le
    exact mul_le_mul h1 hEr (exp_pos _).le (by positivity)
  have hρ2 : 2 * (hd2.Cb * δ₂ * exp (ν * T)) < ρ := by
    have hq : hd2.Cb * exp (ν * T) / (hd2.Cb * exp (ν * T) + 1) < 1 :=
      (div_lt_one (by positivity)).2 (by linarith)
    calc 2 * (hd2.Cb * δ₂ * exp (ν * T)) =
          ρ * (hd2.Cb * exp (ν * T) / (hd2.Cb * exp (ν * T) + 1)) := by
          rw [hδ₂def]; field_simp
      _ < ρ * 1 := mul_lt_mul_of_pos_left hq hρ
      _ = ρ := mul_one ρ
  have hd0 : 0 ≤ hd2.Cb * δ₂ * exp (ν * T) := (norm_nonneg _).trans hdy
  have hωF : ∀ z ∈ Metric.closedBall (yStar h bu bn n r) ‖trajDiff h bu bn n v r‖,
      dist (D3Nu z, D3Nv z) (D3Nu (yStar h bu bn n r), D3Nv (yStar h bu bn n r)) ≤ ω₀ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h1 : dist (yStar h bu bn n₀ r) z < ρ := by
      rw [dist_eq_norm]
      calc ‖yStar h bu bn n₀ r - z‖
          ≤ ‖yStar h bu bn n₀ r - yStar h bu bn n r‖ + ‖yStar h bu bn n r - z‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ hd2.Cb * δ₂ * exp (ν * T) + hd2.Cb * δ₂ * exp (ν * T) := by
            refine add_le_add (by rw [norm_sub_rev]; exact hdy) ?_
            rw [norm_sub_rev]; exact hz.trans hdw
        _ < ρ := by linarith
    have h2 : dist (yStar h bu bn n₀ r) (yStar h bu bn n r) < ρ := by
      rw [dist_eq_norm, norm_sub_rev]; linarith
    have hz1 := huc _ hx z h1
    have hz2 := huc _ hx _ h2
    rw [dist_comm] at hz1
    calc dist (D3Nu z, D3Nv z) (D3Nu (yStar h bu bn n r), D3Nv (yStar h bu bn n r))
        ≤ dist (D3Nu z, D3Nv z) (D3Nu (yStar h bu bn n₀ r), D3Nv (yStar h bu bn n₀ r)) +
          dist (D3Nu (yStar h bu bn n₀ r), D3Nv (yStar h bu bn n₀ r))
            (D3Nu (yStar h bu bn n r), D3Nv (yStar h bu bn n r)) := dist_triangle _ _ _
      _ ≤ ω₀ / 2 + ω₀ / 2 := add_le_add hz1.le hz2.le
      _ = ω₀ := by ring
  have hωu : ∀ z ∈ Metric.closedBall (yStar h bu bn n r) ‖trajDiff h bu bn n v r‖,
      ‖D3Nu z - D3Nu (yStar h bu bn n r)‖ ≤ ω₀ := fun z hz => by
    have := hωF z hz
    rw [Prod.dist_eq] at this
    rw [← dist_eq_norm]; exact (le_max_left _ _).trans this
  have hωv : ∀ z ∈ Metric.closedBall (yStar h bu bn n r) ‖trajDiff h bu bn n v r‖,
      ‖D3Nv z - D3Nv (yStar h bu bn n r)‖ ≤ ω₀ := fun z hz => by
    have := hωF z hz
    rw [Prod.dist_eq] at this
    rw [← dist_eq_norm]; exact (le_max_right _ _).trans this
  have hfine := (third_err_le hd hd2 hd3 bu bn n e d v hr hω₀.le hωu hωv).2
  have hc : 9 * hd2.Cb ^ 4 * ‖v‖ * exp (ν * r) + hd2.Cb ^ 3 * ω₀ ≤ η := by
    have h1 : 9 * hd2.Cb ^ 4 * ‖v‖ * exp (ν * r) ≤
        9 * hd2.Cb ^ 4 * (η / (18 * hd2.Cb ^ 4 * exp (ν * T))) * exp (ν * T) := by
      have := mul_le_mul hv₁ hEr (exp_pos _).le (by positivity)
      calc 9 * hd2.Cb ^ 4 * ‖v‖ * exp (ν * r) = 9 * hd2.Cb ^ 4 * (‖v‖ * exp (ν * r)) := by ring
        _ ≤ 9 * hd2.Cb ^ 4 * (η / (18 * hd2.Cb ^ 4 * exp (ν * T)) * exp (ν * T)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have h2 : 9 * hd2.Cb ^ 4 * (η / (18 * hd2.Cb ^ 4 * exp (ν * T))) * exp (ν * T) = η / 2 := by
      field_simp; ring
    have h3 : hd2.Cb ^ 3 * ω₀ = η / 2 := by rw [hω₀def]; field_simp
    linarith
  have hE3 : exp (ν * r) ^ 3 = exp (3 * ν * r) := by rw [← exp_nat_mul]; ring_nf
  have hκr : exp (3 * ν * r) ≤ exp (κ * r) := exp_mul_le_exp_mul h3κ hr
  have hP : 0 ≤ ‖v‖ * ‖e‖ * ‖d‖ := by positivity
  calc _ ≤ (9 * hd2.Cb ^ 4 * ‖v‖ * exp (ν * r) + hd2.Cb ^ 3 * ω₀) * ‖v‖ *
        exp (ν * r) ^ 3 * ‖e‖ * ‖d‖ := hfine
    _ = (9 * hd2.Cb ^ 4 * ‖v‖ * exp (ν * r) + hd2.Cb ^ 3 * ω₀) *
        (‖v‖ * ‖e‖ * ‖d‖) * exp (3 * ν * r) := by rw [hE3]; ring
    _ ≤ η * (‖v‖ * ‖e‖ * ‖d‖) * exp (κ * r) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hc hP) hκr (exp_pos _).le (by positivity)
    _ = (η * ‖v‖ * ‖e‖ * ‖d‖) * exp (κ * r) := by ring

/-- **The second derivative of the time-0 value map has locally uniform little-o three-point
defects.**  Given `ε`, choose an admissible weight `κ ∈ (3ν, β)`, a time `T` with
`8C_b⁴ e^{-(κ-3ν)T} ≤ η`, a radius `ρ` of uniform continuity of `D³N` around the compact set of
trajectory values `y_*(n₀)([0, T])`, and `δ` small: on `[T, ∞)` the crude bound and on `[0, T]` the
fine bound give a third-level source of size `η ‖v‖‖e‖‖d‖ e^{κr}`. -/
theorem traj2_littleODefect (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (hd3 : GraphC3Hyp hd2 D3Nu D3Nv) (bu : U) (bn : Nn) :
    LittleODefect (traj2 hd hd2 bu bn 0) := by
  intro n₀ ε hε
  have hν := h.ν_pos
  have hCb1 : 1 ≤ hd2.Cb := hd2.one_le_Cb
  have hCb0 : 0 < hd2.Cb := by linarith
  obtain ⟨κ, h3κ, hκβ, hqκ⟩ := exists_weight_gt (M := M) (L := L)
    (by linarith [h.α_lt] : α < 3 * ν) hd2.three_lt hd2.contr3
  have hακ : α < κ := by linarith [h.α_lt]
  obtain ⟨Kκ, hKκdef⟩ : ∃ K, K = M * ((κ - α)⁻¹ + (β - κ)⁻¹) /
      (1 - M * L * ((κ - α)⁻¹ + (β - κ)⁻¹)) := ⟨_, rfl⟩
  have hKκ : 0 ≤ Kκ := by
    have h1 : 0 < κ - α := by linarith
    have h2 : 0 < β - κ := by linarith
    have h3 : 0 < 1 - M * L * ((κ - α)⁻¹ + (β - κ)⁻¹) := by linarith
    have := h.M_nonneg
    rw [hKκdef]; positivity
  obtain ⟨η, hηdef⟩ : ∃ η, η = ε / (Kκ + 1) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hKη : Kκ * η ≤ ε := by
    rw [hηdef, mul_div_assoc', div_le_iff₀ (by positivity)]
    have : ε * (Kκ + 1) = Kκ * ε + ε := by ring
    linarith
  have hε₀ : 0 < κ - 3 * ν := by linarith
  obtain ⟨T, hTdef⟩ : ∃ T, T = 8 * hd2.Cb ^ 4 / ((κ - 3 * ν) * η) := ⟨_, rfl⟩
  have hT : 0 ≤ T := by rw [hTdef]; positivity
  have hTbig : 8 * hd2.Cb ^ 4 ≤ η * exp ((κ - 3 * ν) * T) := by
    have h1 := add_one_le_exp ((κ - 3 * ν) * T)
    have h2 : η * ((κ - 3 * ν) * T) = 8 * hd2.Cb ^ 4 := by rw [hTdef]; field_simp
    calc 8 * hd2.Cb ^ 4 = η * ((κ - 3 * ν) * T) := h2.symm
      _ ≤ η * ((κ - 3 * ν) * T + 1) := by linarith
      _ ≤ η * exp ((κ - 3 * ν) * T) := mul_le_mul_of_nonneg_left h1 hη.le
  have hK : IsCompact ((fun s => yStar h bu bn n₀ s) '' Icc 0 T) :=
    isCompact_Icc.image (yStar_continuous h bu bn n₀)
  obtain ⟨ρ, hρ, huc⟩ := uc_compact hK (hd3.cont3_u.prodMk hd3.cont3_v)
    (show 0 < η / (2 * hd2.Cb ^ 3) / 2 by positivity)
  have hET : 1 ≤ exp (ν * T) := one_le_exp (by positivity)
  obtain ⟨δ₁, hδ₁def⟩ : ∃ δ, δ = η / (18 * hd2.Cb ^ 4 * exp (ν * T)) := ⟨_, rfl⟩
  obtain ⟨δ₂, hδ₂def⟩ : ∃ δ, δ = ρ / (2 * (hd2.Cb * exp (ν * T) + 1)) := ⟨_, rfl⟩
  have hδ₁ : 0 < δ₁ := by rw [hδ₁def]; positivity
  have hδ₂ : 0 < δ₂ := by rw [hδ₂def]; positivity
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro n hn v₁ v₂ v₃ a₁ a₂ a₃ hsum hv₁ hv₂ hv₃
  have hS0 : 0 ≤ |a₁| * ‖v₁‖ + |a₂| * ‖v₂‖ + |a₃| * ‖v₃‖ := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun d => ?_
  have hsum' : ∑ i, (![a₁, a₂, a₃] : Fin 3 → ℝ) i • (![v₁, v₂, v₃] : Fin 3 → Nn) i = 0 := by
    simpa [Fin.sum_univ_three] using hsum
  have hvδ : ∀ i, ‖(![v₁, v₂, v₃] : Fin 3 → Nn) i‖ ≤ min δ₁ δ₂ := by
    intro i; fin_cases i
    · simpa using hv₁
    · simpa using hv₂
    · simpa using hv₃
  have happ : (a₁ • (traj2 hd hd2 bu bn 0 (n + v₁) - traj2 hd hd2 bu bn 0 n) +
      a₂ • (traj2 hd hd2 bu bn 0 (n + v₂) - traj2 hd hd2 bu bn 0 n) +
      a₃ • (traj2 hd hd2 bu bn 0 (n + v₃) - traj2 hd hd2 bu bn 0 n)) e d =
      ∑ i, (![a₁, a₂, a₃] : Fin 3 → ℝ) i • (traj2 hd hd2 bu bn 0
        (n + (![v₁, v₂, v₃] : Fin 3 → Nn) i) e d - traj2 hd hd2 bu bn 0 n e d) := by
    simp [Fin.sum_univ_three]
  rw [happ]
  have hnδ : ‖n - n₀‖ ≤ δ₂ := hn.trans (min_le_right _ _)
  have herr : ∀ i r, 0 ≤ r → ‖thirdSrc hd hd2 bu bn n e d ((![v₁, v₂, v₃] : Fin 3 → Nn) i) r -
      linThird hd hd2 D3Nu D3Nv bu bn n e d r ((![v₁, v₂, v₃] : Fin 3 → Nn) i)‖ ≤
        (η * ‖(![v₁, v₂, v₃] : Fin 3 → Nn) i‖ * ‖e‖ * ‖d‖) * exp (κ * r) := by
    intro i r hr
    rcases le_or_gt r T with hrT | hrT
    · exact third_err_early hd hd2 hd3 bu bn n₀ n e d _ hη hρ hr hrT h3κ.le huc
        (hδ₂def ▸ hnδ) (hδ₂def ▸ (hvδ i).trans (min_le_right _ _))
        (hδ₁def ▸ (hvδ i).trans (min_le_left _ _))
    · exact third_err_late hd hd2 hd3 bu bn n e d _ hη hT hrT.le hTbig h3κ.le
  have hS : ∀ r, 0 ≤ r → ‖∑ i, (![a₁, a₂, a₃] : Fin 3 → ℝ) i •
      thirdSrc hd hd2 bu bn n e d ((![v₁, v₂, v₃] : Fin 3 → Nn) i) r‖ ≤
      (η * (|a₁| * ‖v₁‖ + |a₂| * ‖v₂‖ + |a₃| * ‖v₃‖) * ‖e‖ * ‖d‖) * exp (κ * r) := by
    intro r hr
    have hlin := linThird_comb (D3Nu := D3Nu) (D3Nv := D3Nv) hd hd2 bu bn n e d r _ _ hsum'
    have e0 : ∑ i, (![a₁, a₂, a₃] : Fin 3 → ℝ) i •
        thirdSrc hd hd2 bu bn n e d ((![v₁, v₂, v₃] : Fin 3 → Nn) i) r =
        ∑ i, (![a₁, a₂, a₃] : Fin 3 → ℝ) i •
          (thirdSrc hd hd2 bu bn n e d ((![v₁, v₂, v₃] : Fin 3 → Nn) i) r -
          linThird hd hd2 D3Nu D3Nv bu bn n e d r ((![v₁, v₂, v₃] : Fin 3 → Nn) i)) := by
      simp only [smul_sub, Finset.sum_sub_distrib, hlin, sub_zero]
    rw [e0]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i, ‖(![a₁, a₂, a₃] : Fin 3 → ℝ) i •
        (thirdSrc hd hd2 bu bn n e d ((![v₁, v₂, v₃] : Fin 3 → Nn) i) r -
          linThird hd hd2 D3Nu D3Nv bu bn n e d r ((![v₁, v₂, v₃] : Fin 3 → Nn) i))‖ ≤
        |(![a₁, a₂, a₃] : Fin 3 → ℝ) i| *
          ((η * ‖(![v₁, v₂, v₃] : Fin 3 → Nn) i‖ * ‖e‖ * ‖d‖) * exp (κ * r)) := fun i => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (herr i r hr) (abs_nonneg _)
    refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hmain := third_level_le hd hd2 bu bn n e d _ _ h3κ.le hκβ hqκ (by positivity) hS
  refine hmain.trans ?_
  have e1 : M * (η * (|a₁| * ‖v₁‖ + |a₂| * ‖v₂‖ + |a₃| * ‖v₃‖) * ‖e‖ * ‖d‖) *
      ((κ - α)⁻¹ + (β - κ)⁻¹) / (1 - M * L * ((κ - α)⁻¹ + (β - κ)⁻¹)) =
      (Kκ * η) * ((|a₁| * ‖v₁‖ + |a₂| * ‖v₂‖ + |a₃| * ‖v₃‖) * ‖e‖ * ‖d‖) := by
    rw [hKκdef]; ring
  rw [e1]
  calc (Kκ * η) * ((|a₁| * ‖v₁‖ + |a₂| * ‖v₂‖ + |a₃| * ‖v₃‖) * ‖e‖ * ‖d‖)
      ≤ ε * ((|a₁| * ‖v₁‖ + |a₂| * ‖v₂‖ + |a₃| * ‖v₃‖) * ‖e‖ * ‖d‖) :=
        mul_le_mul_of_nonneg_right hKη (by positivity)
    _ = ε * (|a₁| * ‖v₁‖ + |a₂| * ‖v₂‖ + |a₃| * ‖v₃‖) * ‖e‖ * ‖d‖ := by ring

/-- `n₀ ↦ D²(y_*(n₀)(0))` is `C¹`. -/
theorem traj2_zero_contDiff_one (hd : GraphC1Hyp h DNu DNv L₂)
    (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) (hd3 : GraphC3Hyp hd2 D3Nu D3Nv) (bu : U) (bn : Nn) :
    ContDiff ℝ 1 (traj2 hd hd2 bu bn 0) :=
  contDiff_one_of_littleODefect (traj2_littleODefect hd hd2 hd3 bu bn)
    (by have := Kde_nonneg hd2 0; positivity) (traj2_lip hd hd2 bu bn 0)

/-- **The invariant graph is `C³`** (`lem:supp-exact-graph-criterion`): under `GraphHyp`
(`j = 1`), `GraphC1Hyp` (`j = 2`), `GraphC2Hyp` (`j = 3`, `3ν < β`, bounded third derivatives)
and `GraphC3Hyp` (`D³N` continuous), the graph `h = graphMap` of the forward weighted
trajectories is `C³`. -/
theorem graphMap_contDiff_three (hd : GraphC1Hyp h DNu DNv L₂)
    (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) (hd3 : GraphC3Hyp hd2 D3Nu D3Nv) (bu : U) (bn : Nn) :
    ContDiff ℝ 3 (graphMap h bu bn) := by
  have h2 : ContDiff ℝ 1 (traj2 hd hd2 bu bn 0) := traj2_zero_contDiff_one hd hd2 hd3 bu bn
  have h1 : ContDiff ℝ 2 (traj1 hd bu bn 0) := by
    have hfd : fderiv ℝ (traj1 hd bu bn 0) = traj2 hd hd2 bu bn 0 :=
      funext fun n => (traj2_hasFDerivAt hd hd2 bu bn 0 n).fderiv
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
    refine ⟨fun n => (traj2_hasFDerivAt hd hd2 bu bn 0 n).differentiableAt,
      fun h1 => absurd h1 (by decide), ?_⟩
    rw [hfd]; exact h2
  have h0 : ContDiff ℝ 3 (trajAt h bu bn 0) := by
    have hfd : fderiv ℝ (trajAt h bu bn 0) = traj1 hd bu bn 0 :=
      funext fun n => (traj1_hasFDerivAt hd bu bn 0 n).fderiv
    rw [show (3 : WithTop ℕ∞) = 2 + 1 by norm_num, contDiff_succ_iff_fderiv]
    refine ⟨fun n => (traj1_hasFDerivAt hd bu bn 0 n).differentiableAt,
      fun h1 => absurd h1 (by decide), ?_⟩
    rw [hfd]; exact h1
  have hgm : graphMap h bu bn = fun n => (trajAt h bu bn 0 n).1 := by
    funext n; simp [graphMap, trajAt]
  rw [hgm]
  exact contDiff_fst.comp h0

end Third

/-! ### Non-vacuity and the manuscript's formulation -/

section Final

variable {U Nn : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Nn] [NormedSpace ℝ Nn] [CompleteSpace Nn]

/-- Non-vacuity of the `C³` layer: the example of `graphC2Hyp_nonvacuous` (`ν = 1`, `β = 4`,
`3ν < β`, zero nonlinearities) with `D³N = 0`. -/
theorem graphC3Hyp_nonvacuous :
    ∃ (h : GraphHyp (U := ℝ) (Nn := ℝ) (fun t => exp (4 * t) • ContinuousLinearMap.id ℝ ℝ)
        (fun _ => ContinuousLinearMap.id ℝ ℝ) 1 0 4 1 0 (fun _ => 0) (fun _ => 0))
      (hd : GraphC1Hyp h (fun _ => 0) (fun _ => 0) 0)
      (hd2 : GraphC2Hyp hd (fun _ => 0) (fun _ => 0) 0),
      GraphC3Hyp hd2 (fun _ => 0) (fun _ => 0) := by
  obtain ⟨h, hd, hd2⟩ := graphC2Hyp_nonvacuous
  exact ⟨h, hd, hd2,
    { hasDeriv3_u := fun _ => hasFDerivAt_const _ _
      hasDeriv3_v := fun _ => hasFDerivAt_const _ _
      cont3_u := continuous_const
      cont3_v := continuous_const }⟩

/-- A bounded derivative gives a global Lipschitz bound (mean value inequality). -/
theorem lip_of_hasFDerivAt_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E → E →L[ℝ] F} {C : ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hb : ∀ x, ‖f' x‖ ≤ C) (x y : E) :
    ‖f x - f y‖ ≤ C * ‖x - y‖ :=
  convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hf z).hasFDerivWithinAt) (fun z _ => hb z) (mem_univ y) (mem_univ x)

/-- **`lem:supp-exact-graph-criterion` in the manuscript's formulation.**  Let
`N = (N_u, N_n)` be a `C³` nonlinearity (derivatives `DN, D²N, D³N`, with `D³N` continuous) with
bounded derivatives through order three, `‖DN‖ ≤ L`, `‖D²N‖ ≤ L₂`, `‖D³N‖ ≤ L₃`; let
`‖e^{-sA_u}‖ ≤ M e^{-βs}`, `‖e^{sA_n}‖ ≤ M e^{αs}` (`s ≥ 0`), `max{0, α} < ν`, `3ν < β`, and
`max_{j=1,2,3} M L ((jν-α)⁻¹ + (β-jν)⁻¹) < 1`.  Then the forward weighted trajectories of
`u̇ = A_u u + b_u + N_u(u, n)`, `ṅ = A_n n + b_n + N_n(u, n)` define a graph `u = h(n)` that is
`C³` and forward invariant (`u(τ) = h(n(τ))` along every forward weighted trajectory).  The
localization clause is `flow_mem_graph_of_local`. -/
theorem invariantGraph_contDiff_three_of_exp (Au : U →L[ℝ] U) (An : Nn →L[ℝ] Nn)
    {M α β ν L L₂ L₃ : ℝ} {Nu : U × Nn → U} {Nv : U × Nn → Nn}
    {DNu : U × Nn → (U × Nn) →L[ℝ] U} {DNv : U × Nn → (U × Nn) →L[ℝ] Nn}
    {D2Nu : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] U)}
    {D2Nv : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] Nn)}
    {D3Nu : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] U))}
    {D3Nv : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] Nn))}
    (hν : 0 < ν) (hαν : α < ν) (h3β : 3 * ν < β) (hM : 0 ≤ M) (hL : 0 ≤ L) (hL₂ : 0 ≤ L₂)
    (hL₃ : 0 ≤ L₃)
    (hPu : ∀ s, 0 ≤ s → ‖NormedSpace.exp ((-s) • Au)‖ ≤ M * exp (-β * s))
    (hPn : ∀ s, 0 ≤ s → ‖NormedSpace.exp (s • An)‖ ≤ M * exp (α * s))
    (hDu : ∀ x, HasFDerivAt Nu (DNu x) x) (hDv : ∀ x, HasFDerivAt Nv (DNv x) x)
    (hD2u : ∀ x, HasFDerivAt DNu (D2Nu x) x) (hD2v : ∀ x, HasFDerivAt DNv (D2Nv x) x)
    (hD3u : ∀ x, HasFDerivAt D2Nu (D3Nu x) x) (hD3v : ∀ x, HasFDerivAt D2Nv (D3Nv x) x)
    (hc3u : Continuous D3Nu) (hc3v : Continuous D3Nv)
    (hb1u : ∀ x, ‖DNu x‖ ≤ L) (hb1v : ∀ x, ‖DNv x‖ ≤ L)
    (hb2u : ∀ x, ‖D2Nu x‖ ≤ L₂) (hb2v : ∀ x, ‖D2Nv x‖ ≤ L₂)
    (hb3u : ∀ x, ‖D3Nu x‖ ≤ L₃) (hb3v : ∀ x, ‖D3Nv x‖ ≤ L₃)
    (hc1 : M * L * ((ν - α)⁻¹ + (β - ν)⁻¹) < 1)
    (hc2 : M * L * ((2 * ν - α)⁻¹ + (β - 2 * ν)⁻¹) < 1)
    (hc3 : M * L * ((3 * ν - α)⁻¹ + (β - 3 * ν)⁻¹) < 1) (bu : U) (bn : Nn) :
    ∃ hG : GraphHyp (fun t => NormedSpace.exp (t • Au)) (fun t => NormedSpace.exp (t • An))
        M α β ν L Nu Nv,
      ContDiff ℝ 3 (graphMap hG bu bn) ∧
        ∀ (n₀ : Nn) (τ : ℝ), 0 ≤ τ →
          (yStar hG bu bn n₀ τ).1 = graphMap hG bu bn (yStar hG bu bn n₀ τ).2 := by
  have hG := graphHyp_of_exp Au An hν hαν (by linarith) hM hL hPu hPn
    (lip_of_hasFDerivAt_bound hDu hb1u) (lip_of_hasFDerivAt_bound hDv hb1v) hc1
  have hd : GraphC1Hyp hG DNu DNv L₂ :=
    { hasDeriv_u := hDu
      hasDeriv_v := hDv
      L₂_nonneg := hL₂
      Du_lip := lip_of_hasFDerivAt_bound hD2u hb2u
      Dv_lip := lip_of_hasFDerivAt_bound hD2v hb2v
      two_lt := by linarith
      contr2 := hc2 }
  have hd2 : GraphC2Hyp hd D2Nu D2Nv L₃ :=
    { hasDeriv2_u := hD2u
      hasDeriv2_v := hD2v
      L₃_nonneg := hL₃
      D2u_lip := lip_of_hasFDerivAt_bound hD3u hb3u
      D2v_lip := lip_of_hasFDerivAt_bound hD3v hb3v
      three_lt := h3β
      contr3 := hc3 }
  have hd3 : GraphC3Hyp hd2 D3Nu D3Nv :=
    { hasDeriv3_u := hD3u
      hasDeriv3_v := hD3v
      cont3_u := hc3u
      cont3_v := hc3v }
  exact ⟨hG, graphMap_contDiff_three hd hd2 hd3 bu bn,
    fun n₀ τ hτ => yStar_mem_graph hG bu bn n₀ hτ⟩

end Final

end

end LyapunovPerron
end RenewalGeometry
