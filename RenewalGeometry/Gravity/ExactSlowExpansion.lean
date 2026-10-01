/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.AnalyticRayExpansion
import RenewalGeometry.Gravity.ExactSlowBranchData

/-!
# Exact anisotropic slow expansion (`lem:supp-exact-slow-expansion`;
  emergent-spacetime manuscript)

The unbalanced constrained field (`eq:supp-exact-unbalanced-field`, item (C3) of
`ass:supp-graded-exact-chart`) is, in rapid time `s = t/a³`,
`v_s' = a³ b_s + R_s(a, v)`, `v_f' = C_red v_s + B v_f + a³ b_w + R_f(a, v)`,
with analytic remainders obeying the graded bounds `eq:supp-exact-graded-remainders`
`|R_s| ≤ C(a⁴ + a²|v| + a|v|²)`, `|R_f| ≤ C(a⁴ + a|v| + |v|²)`.  As for the other records
that use `ass:supp-graded-exact-chart`, its data enter as hypotheses; the lemma is abstract in
them ("the graded analytic remainders ... give exactly ...").

Notation (paper → Lean): the slow space `ℝ²⁹⁴` → `Xs`, the weak space `ℝ²⁹` → `W`,
`v = (v_s, v_f)`, `ξ = (x, z) : Xs × W`; `R_s, R_f : ℝ × (Xs × W) → Xs, W` (functions of
`(a, v)`); the mixed partial derivatives at `(0, 0)` are read off the iterated Fréchet
derivative on `ℝ × (Xs × W)` along the amplitude direction `e = (1, 0)` and the slow
direction `(0, ξ)`:
`D_a²D_vR_s(0,0)[ξ] = D³R_s(0)[e, e, (0,ξ)]`, `D_aD_v²R_s(0,0)[ξ,ξ] = D³R_s(0)[e, (0,ξ), (0,ξ)]`,
`D_aD_vR_f(0,0)[ξ] = D²R_f(0)[e, (0,ξ)]`, `D_v²R_f(0,0)[ξ,ξ] = D²R_f(0)[(0,ξ), (0,ξ)]`
(the order of the slots is irrelevant by symmetry of iterated derivatives of analytic maps).

Main results.
* `sigma0_eq_coeff`, `phi1_eq_coeff`: the paper's coefficients `Σ₀`, `Φ₁`
  (`eq:supp-exact-slow-coefficients`) are exactly the third, resp. second, Taylor coefficient
  of `a ↦ R_s(a, aξ)`, resp. `a ↦ R_f(a, aξ)`; the graded bounds kill all lower coefficients.
* `slow_expansion` (**`lem:supp-exact-slow-expansion`**): with
  `Σ₁(a,ξ) = a⁻⁴(R_s(a,aξ) - a³Σ₀(ξ))`, `Φ₂(a,ξ) = a⁻³(R_f(a,aξ) - a²Φ₁(ξ))`,
  `R_s(a,aξ) = a³Σ₀(ξ) + a⁴Σ₁(a,ξ)`, `R_f(a,aξ) = a²Φ₁(ξ) + a³Φ₂(a,ξ)`, the remainders are
  uniformly bounded on every bounded `ξ`-set for sufficiently small `a > 0`, the substitution
  `ξ(τ) = a⁻¹ v(τ/a²)` turns every solution of the unbalanced field into a solution of the slow
  system `eq:main-exact-slow-system` (with `Φ₀(x,z) = C_red x + B z`), `Σ₀(0) = Φ₁(0) = 0`, and
  `Σ₀`, `Φ₁` are polynomials of degree at most two (linear plus quadratic part).
-/

open Filter Set
open scoped Topology NNReal ENNReal

namespace RenewalGeometry
namespace ExactSlowExpansion

open AnalyticRay ExactSlowBranch

variable {Xs W : Type*} [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [CompleteSpace Xs]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-! ### Coefficients -/

/-- The amplitude direction `e = (1, 0)` of the `(a, v)`-space. -/
def ampDir : ℝ × (Xs × W) := (1, 0)

/-- The slow direction `(0, ξ)` of the `(a, v)`-space. -/
def slowDir (ξ : Xs × W) : ℝ × (Xs × W) := (0, ξ)

/-- `Σ₀(ξ) = ½ D_a²D_vR_s(0,0)[ξ] + ½ D_aD_v²R_s(0,0)[ξ,ξ]`
(`eq:supp-exact-slow-coefficients`). -/
noncomputable def sigma0 (Rs : ℝ × (Xs × W) → Xs) (ξ : Xs × W) : Xs :=
  (1 / 2 : ℝ) • iteratedFDeriv ℝ 3 Rs 0 ![ampDir, ampDir, slowDir ξ]
    + (1 / 2 : ℝ) • iteratedFDeriv ℝ 3 Rs 0 ![ampDir, slowDir ξ, slowDir ξ]

/-- `Φ₁(ξ) = D_aD_vR_f(0,0)[ξ] + ½ D_v²R_f(0,0)[ξ,ξ]` (`eq:supp-exact-slow-coefficients`). -/
noncomputable def phi1 (Rf : ℝ × (Xs × W) → W) (ξ : Xs × W) : W :=
  iteratedFDeriv ℝ 2 Rf 0 ![ampDir, slowDir ξ]
    + (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 Rf 0 ![slowDir ξ, slowDir ξ]

/-- The regular slow remainder `Σ₁(a, ξ) = a⁻⁴ (R_s(a, aξ) - a³ Σ₀(ξ))`. -/
noncomputable def sigma1 (Rs : ℝ × (Xs × W) → Xs) (a : ℝ) (ξ : Xs × W) : Xs :=
  (a ^ 4)⁻¹ • (Rs (a, a • ξ) - a ^ 3 • sigma0 Rs ξ)

/-- The weak remainder `Φ₂(a, ξ) = a⁻³ (R_f(a, aξ) - a² Φ₁(ξ))`. -/
noncomputable def phi2 (Rf : ℝ × (Xs × W) → W) (a : ℝ) (ξ : Xs × W) : W :=
  (a ^ 3)⁻¹ • (Rf (a, a • ξ) - a ^ 2 • phi1 Rf ξ)

theorem smul_ampDir_add_slowDir (a : ℝ) (ξ : Xs × W) :
    a • (ampDir + slowDir ξ : ℝ × (Xs × W)) = (a, a • ξ) := by
  simp [ampDir, slowDir]

theorem norm_ampDir_add_slowDir_le (ξ : Xs × W) :
    ‖(ampDir + slowDir ξ : ℝ × (Xs × W))‖ ≤ ‖ξ‖ + 1 := by
  have h1 : ‖(ampDir : ℝ × (Xs × W))‖ = 1 := by simp [ampDir, Prod.norm_mk]
  have h2 : ‖slowDir ξ‖ = ‖ξ‖ := by simp [slowDir, Prod.norm_mk]
  calc ‖(ampDir + slowDir ξ : ℝ × (Xs × W))‖ ≤ ‖(ampDir : ℝ × (Xs × W))‖ + ‖slowDir ξ‖ :=
        norm_add_le _ _
    _ = ‖ξ‖ + 1 := by rw [h1, h2, add_comm]

/-! ### Vanishing of the low coefficients forced by the graded bounds -/

section Vanishing

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Along the slow ray `(a, aξ)`, a remainder with `‖R(a, v)‖ ≤ C(a⁴ + aʲ|v| + aⁱ|v|²)`
(`i, j ≥ k - 1`, `k ≤ 4` as for `R_s` with `k = 3` and `R_f` with `k = 2`) is `O(a^k)`. -/
theorem ray_bound {R : ℝ × (Xs × W) → G} {k i j : ℕ} (hk : k ≤ 4) (hj : k ≤ j + 1)
    (hi : k ≤ i + 2) {δ C : ℝ} (hδ : 0 < δ)
    (hb : ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖R (a, v)‖ ≤ C * (a ^ 4 + a ^ j * ‖v‖ + a ^ i * ‖v‖ ^ 2)) (ξ : Xs × W) :
    ∀ a : ℝ, 0 < a → a < min 1 (δ / (‖ξ‖ + 1)) →
      ‖R (a • (ampDir + slowDir ξ))‖ ≤ (|C| * (1 + ‖ξ‖ + ‖ξ‖ ^ 2)) * a ^ k := by
  intro a ha hamin
  have ha1 : a < 1 := hamin.trans_le (min_le_left _ _)
  have haδ' : a < δ / (‖ξ‖ + 1) := hamin.trans_le (min_le_right _ _)
  have hn1 : 0 < ‖ξ‖ + 1 := by positivity
  have hav : ‖a • ξ‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    have : a * (‖ξ‖ + 1) < δ := (lt_div_iff₀ hn1).mp haδ'
    nlinarith [norm_nonneg ξ]
  have haδ : a < δ := by
    have : δ / (‖ξ‖ + 1) ≤ δ := div_le_self hδ.le (by linarith [norm_nonneg ξ])
    linarith
  rw [smul_ampDir_add_slowDir]
  have h := hb a (a • ξ) ha haδ hav
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at h
  have hpow : ∀ n, k ≤ n → a ^ n ≤ a ^ k := fun n hn =>
    pow_le_pow_of_le_one ha.le ha1.le hn
  have e4 : a ^ 4 ≤ a ^ k := hpow 4 hk
  have ej : a ^ j * (a * ‖ξ‖) ≤ a ^ k * ‖ξ‖ := by
    rw [← mul_assoc, ← pow_succ]
    exact mul_le_mul_of_nonneg_right (hpow _ hj) (norm_nonneg _)
  have ei : a ^ i * (a * ‖ξ‖) ^ 2 ≤ a ^ k * ‖ξ‖ ^ 2 := by
    rw [mul_pow, ← mul_assoc, ← pow_add]
    exact mul_le_mul_of_nonneg_right (hpow _ hi) (by positivity)
  calc ‖R (a, a • ξ)‖ ≤ C * (a ^ 4 + a ^ j * (a * ‖ξ‖) + a ^ i * (a * ‖ξ‖) ^ 2) := h
    _ ≤ |C| * (a ^ 4 + a ^ j * (a * ‖ξ‖) + a ^ i * (a * ‖ξ‖) ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (a ^ k + a ^ k * ‖ξ‖ + a ^ k * ‖ξ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
    _ = (|C| * (1 + ‖ξ‖ + ‖ξ‖ ^ 2)) * a ^ k := by ring

/-- A remainder with `‖R(a, v)‖ ≤ C(a⁴ + aʲ|v| + a|v|²)`, `j ≥ 1`, (as `R_s`) vanishes on
`a = 0` near `v = 0`, by continuity of the analytic map. -/
theorem eq_zero_at_zero_amp {R : ℝ × (Xs × W) → G} (hR : AnalyticAt ℝ R 0) {j i : ℕ}
    (hj : 1 ≤ j) (hi : 1 ≤ i) {δ C : ℝ} (hδ : 0 < δ)
    (hb : ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖R (a, v)‖ ≤ C * (a ^ 4 + a ^ j * ‖v‖ + a ^ i * ‖v‖ ^ 2)) :
    ∃ δ' > 0, ∀ v : Xs × W, ‖v‖ < δ' → R (0, v) = 0 := by
  obtain ⟨ε, hε, hεan⟩ := Metric.eventually_nhds_iff.mp hR.eventually_analyticAt
  refine ⟨min δ ε, lt_min hδ hε, fun v hv => ?_⟩
  have hvδ : ‖v‖ < δ := hv.trans_le (min_le_left _ _)
  have hcont : ContinuousAt R (0, v) := by
    refine (hεan ?_).continuousAt
    rw [dist_zero_right, Prod.norm_def, norm_zero]
    exact max_lt hε (hv.trans_le (min_le_right _ _))
  have hlim1 : Tendsto (fun a : ℝ => R (a, v)) (𝓝[>] 0) (𝓝 (R (0, v))) := by
    have : Tendsto (fun a : ℝ => ((a, v) : ℝ × (Xs × W))) (𝓝 0) (𝓝 (0, v)) :=
      (continuous_id.prodMk continuous_const).tendsto 0
    exact (hcont.tendsto.comp this).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun a : ℝ => R (a, v)) (𝓝[>] 0) (𝓝 0) := by
    have hg : Tendsto (fun a : ℝ => C * (a ^ 4 + a ^ j * ‖v‖ + a ^ i * ‖v‖ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous fun a : ℝ => C * (a ^ 4 + a ^ j * ‖v‖ + a ^ i * ‖v‖ ^ 2) := by
        fun_prop
      have := hc.tendsto 0
      rw [show C * ((0 : ℝ) ^ 4 + 0 ^ j * ‖v‖ + 0 ^ i * ‖v‖ ^ 2) = 0 by
        simp [zero_pow (by omega : j ≠ 0), zero_pow (by omega : i ≠ 0)]] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [Ioo_mem_nhdsGT hδ] with a ha
    exact hb a v ha.1 ha.2 hvδ
  exact tendsto_nhds_unique hlim1 hlim2

end Vanishing

/-! ### Identification of the leading coefficients -/

/-- **The leading slow coefficient.**  Under the graded bound on `R_s`, `Σ₀(ξ)` is the third
Taylor coefficient `p₃((1,ξ)³)` of the ray `a ↦ R_s(a, aξ)`, and all lower coefficients
vanish. -/
theorem sigma0_eq_coeff {Rs : ℝ × (Xs × W) → Xs} {p : FormalMultilinearSeries ℝ (ℝ × (Xs × W)) Xs}
    {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall Rs p 0 r) {δ C : ℝ} (hδ : 0 < δ)
    (hb : ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖Rs (a, v)‖ ≤ C * (a ^ 4 + a ^ 2 * ‖v‖ + a ^ 1 * ‖v‖ ^ 2)) (ξ : Xs × W) :
    (∀ m < 3, p m (fun _ => ampDir + slowDir ξ) = 0) ∧
      sigma0 Rs ξ = p 3 (fun _ => ampDir + slowDir ξ) := by
  have hRs : AnalyticAt ℝ Rs 0 := hp.analyticAt
  refine ⟨?_, ?_⟩
  · refine coeff_eq_zero_of_norm_le hp _ 3 (lt_min one_pos (div_pos hδ (by positivity)))
      (ray_bound (k := 3) (by norm_num) (by norm_num) (by norm_num) hδ hb ξ)
  -- `p₃(e³) = 0` from `‖R_s(a, 0)‖ ≤ C a⁴`
  have hee : p 3 (fun _ => (ampDir : ℝ × (Xs × W))) = 0 := by
    refine coeff_eq_zero_of_norm_le hp ampDir 4 (δ := min 1 δ) (C := |C|)
      (lt_min one_pos hδ) ?_ 3 (by norm_num)
    intro a ha haδ
    have h := hb a 0 ha (haδ.trans_le (min_le_right _ _)) (by simpa using hδ)
    have hsm : a • (ampDir : ℝ × (Xs × W)) = (a, 0) := by simp [ampDir]
    rw [hsm]
    simp only [norm_zero, mul_zero, add_zero, zero_pow two_ne_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  -- `p₃((0,ξ)³) = 0` from `R_s(0, v) = 0` near `v = 0`
  have huu : p 3 (fun _ => slowDir ξ) = 0 := by
    obtain ⟨δ', hδ', hz⟩ := eq_zero_at_zero_amp hRs (j := 2) (i := 1) (by norm_num) le_rfl hδ hb
    refine coeff_eq_zero_of_norm_le hp (slowDir ξ) 4 (δ := δ' / (‖ξ‖ + 1)) (C := 0)
      (div_pos hδ' (by positivity)) ?_ 3 (by norm_num)
    intro a ha haδ
    have hsm : a • slowDir ξ = ((0 : ℝ), a • ξ) := by simp [slowDir]
    rw [hsm, hz]
    · simp
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      have hn1 : 0 < ‖ξ‖ + 1 := by positivity
      have : a * (‖ξ‖ + 1) < δ' := (lt_div_iff₀ hn1).mp haδ
      nlinarith [norm_nonneg ξ]
  -- expand `D³R_s(0)[(e+u)³]`
  have hexp := iteratedFDeriv_three_add hRs (ampDir : ℝ × (Xs × W)) (slowDir ξ)
  have hd : ∀ v : ℝ × (Xs × W), iteratedFDeriv ℝ 3 Rs 0 ![v, v, v]
      = (6 : ℝ) • p 3 (fun _ => v) := by
    intro v
    rw [← diag_three, iteratedFDeriv_eq_factorial_coeff hp]
    norm_num [Nat.factorial]
  rw [hd, hd, hd, hee, huu, smul_zero, zero_add, add_zero] at hexp
  -- solve for `p₃((e+u)³)`
  have h6 : p 3 (fun _ => ampDir + slowDir ξ) = (1 / 6 : ℝ) • ((6 : ℝ) • p 3 (fun _ => ampDir + slowDir ξ)) := by
    rw [smul_smul]; norm_num
  rw [h6, hexp, sigma0, smul_add, smul_smul, smul_smul]
  norm_num

/-- **The leading weak coefficient.**  Under the graded bound on `R_f`, `Φ₁(ξ)` is the second
Taylor coefficient `p₂((1,ξ)²)` of the ray `a ↦ R_f(a, aξ)`, and the lower ones vanish. -/
theorem phi1_eq_coeff {Rf : ℝ × (Xs × W) → W} {p : FormalMultilinearSeries ℝ (ℝ × (Xs × W)) W}
    {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall Rf p 0 r) {δ C : ℝ} (hδ : 0 < δ)
    (hb : ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖Rf (a, v)‖ ≤ C * (a ^ 4 + a ^ 1 * ‖v‖ + a ^ 0 * ‖v‖ ^ 2)) (ξ : Xs × W) :
    (∀ m < 2, p m (fun _ => ampDir + slowDir ξ) = 0) ∧
      phi1 Rf ξ = p 2 (fun _ => ampDir + slowDir ξ) := by
  have hRf : AnalyticAt ℝ Rf 0 := hp.analyticAt
  refine ⟨?_, ?_⟩
  · refine coeff_eq_zero_of_norm_le hp _ 2 (lt_min one_pos (div_pos hδ (by positivity)))
      (ray_bound (k := 2) (by norm_num) (by norm_num) (by norm_num) hδ hb ξ)
  have hee : p 2 (fun _ => (ampDir : ℝ × (Xs × W))) = 0 := by
    refine coeff_eq_zero_of_norm_le hp ampDir 4 (δ := min 1 δ) (C := |C|)
      (lt_min one_pos hδ) ?_ 2 (by norm_num)
    intro a ha haδ
    have h := hb a 0 ha (haδ.trans_le (min_le_right _ _)) (by simpa using hδ)
    have hsm : a • (ampDir : ℝ × (Xs × W)) = (a, 0) := by simp [ampDir]
    rw [hsm]
    simp only [norm_zero, mul_zero, add_zero, zero_pow two_ne_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hexp := iteratedFDeriv_two_add hRf (ampDir : ℝ × (Xs × W)) (slowDir ξ)
  have hd : ∀ v : ℝ × (Xs × W), iteratedFDeriv ℝ 2 Rf 0 ![v, v]
      = (2 : ℝ) • p 2 (fun _ => v) := by
    intro v
    rw [← diag_two, iteratedFDeriv_eq_factorial_coeff hp]
    norm_num [Nat.factorial]
  rw [hd, hd, hee, smul_zero, zero_add] at hexp
  have h2 : p 2 (fun _ => ampDir + slowDir ξ) = (1 / 2 : ℝ) • ((2 : ℝ) • p 2 (fun _ => ampDir + slowDir ξ)) := by
    rw [smul_smul]; norm_num
  rw [h2, hexp, phi1, hd, smul_add, smul_smul, smul_smul]
  norm_num

/-! ### Exact identities, uniform remainders, polynomial structure -/

theorem rs_identity (Rs : ℝ × (Xs × W) → Xs) {a : ℝ} (ha : a ≠ 0) (ξ : Xs × W) :
    Rs (a, a • ξ) = a ^ 3 • sigma0 Rs ξ + a ^ 4 • sigma1 Rs a ξ := by
  rw [sigma1, smul_smul, mul_inv_cancel₀ (pow_ne_zero 4 ha), one_smul]; abel

theorem rf_identity (Rf : ℝ × (Xs × W) → W) {a : ℝ} (ha : a ≠ 0) (ξ : Xs × W) :
    Rf (a, a • ξ) = a ^ 2 • phi1 Rf ξ + a ^ 3 • phi2 Rf a ξ := by
  rw [phi2, smul_smul, mul_inv_cancel₀ (pow_ne_zero 3 ha), one_smul]; abel

theorem sigma0_zero (Rs : ℝ × (Xs × W) → Xs) : sigma0 Rs 0 = 0 := by
  have h : slowDir (0 : Xs × W) = (0 : ℝ) • slowDir (0 : Xs × W) := by simp [slowDir]
  rw [sigma0, h, three_smul_2, three_smul_1]; simp

theorem phi1_zero (Rf : ℝ × (Xs × W) → W) : phi1 Rf 0 = 0 := by
  have h : slowDir (0 : Xs × W) = (0 : ℝ) • slowDir (0 : Xs × W) := by simp [slowDir]
  rw [phi1, h, two_smul_right, two_smul_left]; simp

/-- `Σ₀` has degree at most two: a linear plus a quadratic part. -/
theorem sigma0_degree_le_two (Rs : ℝ × (Xs × W) → Xs) :
    ∃ (L : (Xs × W) →ₗ[ℝ] Xs) (Q : (Xs × W) →ₗ[ℝ] (Xs × W) →ₗ[ℝ] Xs),
      ∀ ξ, sigma0 Rs ξ = L ξ + Q ξ ξ := by
  refine ⟨(1 / 2 : ℝ) • linOfThree (iteratedFDeriv ℝ 3 Rs 0) ampDir ampDir
      (LinearMap.inr ℝ ℝ (Xs × W)),
    (1 / 2 : ℝ) • bilOfThree (iteratedFDeriv ℝ 3 Rs 0) ampDir (LinearMap.inr ℝ ℝ (Xs × W)),
    fun ξ => ?_⟩
  simp [sigma0, slowDir]

/-- `Φ₁` has degree at most two: a linear plus a quadratic part. -/
theorem phi1_degree_le_two (Rf : ℝ × (Xs × W) → W) :
    ∃ (L : (Xs × W) →ₗ[ℝ] W) (Q : (Xs × W) →ₗ[ℝ] (Xs × W) →ₗ[ℝ] W),
      ∀ ξ, phi1 Rf ξ = L ξ + Q ξ ξ := by
  refine ⟨linOfTwo (iteratedFDeriv ℝ 2 Rf 0) ampDir (LinearMap.inr ℝ ℝ (Xs × W)),
    (1 / 2 : ℝ) • bilOfTwo (iteratedFDeriv ℝ 2 Rf 0) (LinearMap.inr ℝ ℝ (Xs × W)),
    fun ξ => ?_⟩
  simp [phi1, slowDir]

/-- **Uniform boundedness of the remainders** on bounded `ξ`-sets for small `a > 0`. -/
theorem remainders_bounded {Rs : ℝ × (Xs × W) → Xs} {Rf : ℝ × (Xs × W) → W}
    (hRs : AnalyticAt ℝ Rs 0) (hRf : AnalyticAt ℝ Rf 0)
    (hbs : ∃ δ > 0, ∃ C, ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖Rs (a, v)‖ ≤ C * (a ^ 4 + a ^ 2 * ‖v‖ + a * ‖v‖ ^ 2))
    (hbf : ∃ δ > 0, ∃ C, ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖Rf (a, v)‖ ≤ C * (a ^ 4 + a * ‖v‖ + ‖v‖ ^ 2)) (ρ : ℝ) :
    ∃ a₀ > 0, ∃ K, ∀ a : ℝ, 0 < a → a < a₀ → ∀ ξ : Xs × W, ‖ξ‖ ≤ ρ →
      ‖sigma1 Rs a ξ‖ ≤ K ∧ ‖phi2 Rf a ξ‖ ≤ K := by
  obtain ⟨ps, rs, hps⟩ := hRs
  obtain ⟨pf, rf, hpf⟩ := hRf
  obtain ⟨δs, hδs, Cs, hCs⟩ := hbs
  obtain ⟨δf, hδf, Cf, hCf⟩ := hbf
  have hCs' : ∀ a v, 0 < a → a < δs → ‖v‖ < δs →
      ‖Rs (a, v)‖ ≤ Cs * (a ^ 4 + a ^ 2 * ‖v‖ + a ^ 1 * ‖v‖ ^ 2) := by
    intro a v h1 h2 h3; simpa using hCs a v h1 h2 h3
  have hCf' : ∀ a v, 0 < a → a < δf → ‖v‖ < δf →
      ‖Rf (a, v)‖ ≤ Cf * (a ^ 4 + a ^ 1 * ‖v‖ + a ^ 0 * ‖v‖ ^ 2) := by
    intro a v h1 h2 h3; simpa using hCf a v h1 h2 h3
  set S : Set (ℝ × (Xs × W)) := Set.range fun ξ : Xs × W => ampDir + slowDir ξ
  obtain ⟨a₁, ha₁, K₁, hK₁⟩ := ray_remainder_bound hps 3 S
    (by rintro _ ⟨ξ, rfl⟩; exact (sigma0_eq_coeff hps hδs hCs' ξ).1) (ρ + 1)
  obtain ⟨a₂, ha₂, K₂, hK₂⟩ := ray_remainder_bound hpf 2 S
    (by rintro _ ⟨ξ, rfl⟩; exact (phi1_eq_coeff hpf hδf hCf' ξ).1) (ρ + 1)
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, max K₁ K₂, fun a ha haa ξ hξ => ?_⟩
  have hηρ : ‖(ampDir + slowDir ξ : ℝ × (Xs × W))‖ ≤ ρ + 1 :=
    (norm_ampDir_add_slowDir_le ξ).trans (by linarith)
  have habs : ∀ b, a < b → |a| < b := fun b hb => by rwa [abs_of_pos ha]
  have h1 := hK₁ a ha.ne' (habs _ (haa.trans_le (min_le_left _ _))) _ ⟨ξ, rfl⟩ hηρ
  have h2 := hK₂ a ha.ne' (habs _ (haa.trans_le (min_le_right _ _))) _ ⟨ξ, rfl⟩ hηρ
  rw [smul_ampDir_add_slowDir, ← (sigma0_eq_coeff hps hδs hCs' ξ).2] at h1
  rw [smul_ampDir_add_slowDir, ← (phi1_eq_coeff hpf hδf hCf' ξ).2] at h2
  exact ⟨h1.trans (le_max_left _ _), h2.trans (le_max_right _ _)⟩

/-! ### The unbalanced field and the slow system -/

/-- The unbalanced constrained field `eq:supp-exact-unbalanced-field` in rapid time:
`(a³ b_s + R_s(a, v), C_red v_s + B v_f + a³ b_w + R_f(a, v))`. -/
def unbalancedField (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (bs : Xs) (bw : W)
    (Rs : ℝ × (Xs × W) → Xs) (Rf : ℝ × (Xs × W) → W) (a : ℝ) (v : Xs × W) : Xs × W :=
  (a ^ 3 • bs + Rs (a, v), Cred v.1 + B v.2 + a ^ 3 • bw + Rf (a, v))

/-- The slow system `eq:main-exact-slow-system`:
`x_τ = b_s + Σ₀(ξ) + aΣ₁(a, ξ)`, `z_τ = a⁻²Φ₀(ξ) + a⁻¹Φ₁(ξ) + b_w + Φ₂(a, ξ)`. -/
noncomputable def slowField (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (bs : Xs) (bw : W)
    (Rs : ℝ × (Xs × W) → Xs) (Rf : ℝ × (Xs × W) → W) (a : ℝ) (ξ : Xs × W) : Xs × W :=
  (bs + sigma0 Rs ξ + a • sigma1 Rs a ξ,
    (a ^ 2)⁻¹ • leadingConstraint Cred B ξ + a⁻¹ • phi1 Rf ξ + bw + phi2 Rf a ξ)

/-- The substitution `v = aξ`, `s = τ/a²` maps the unbalanced field to the slow system:
`slowField a ξ = a⁻³ • unbalancedField a (a ξ)`. -/
theorem slowField_eq (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (bs : Xs) (bw : W)
    (Rs : ℝ × (Xs × W) → Xs) (Rf : ℝ × (Xs × W) → W) {a : ℝ} (ha : a ≠ 0) (ξ : Xs × W) :
    slowField Cred B bs bw Rs Rf a ξ
      = (a ^ 3)⁻¹ • unbalancedField Cred B bs bw Rs Rf a (a • ξ) := by
  have h3 : (a ^ 3)⁻¹ * a ^ 3 = 1 := inv_mul_cancel₀ (pow_ne_zero 3 ha)
  have h4 : (a ^ 3)⁻¹ * a ^ 4 = a := by field_simp
  have h2 : (a ^ 3)⁻¹ * a ^ 2 = a⁻¹ := by field_simp
  have h1 : (a ^ 3)⁻¹ * a = (a ^ 2)⁻¹ := by field_simp
  rw [unbalancedField, rs_identity Rs ha, rf_identity Rf ha]
  ext
  · simp only [slowField, Prod.smul_mk, Prod.smul_fst, smul_add, smul_smul, h3, h4, one_smul]
    abel
  · simp only [slowField, leadingConstraint_apply, Prod.smul_mk, Prod.smul_snd, Prod.smul_fst,
      map_smul, smul_add, smul_smul, h3, h2, h1, one_smul]
    abel

/-- **Trajectory form.**  If `v` solves the unbalanced field on `[0, T/a²]` (rapid time), then
`ξ(τ) = a⁻¹ v(τ/a²)` solves the slow system on `[0, T]`. -/
theorem slow_system_of_unbalanced (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (bs : Xs) (bw : W)
    (Rs : ℝ × (Xs × W) → Xs) (Rf : ℝ × (Xs × W) → W) {a : ℝ} (ha : a ≠ 0) {T : ℝ}
    (v : ℝ → Xs × W)
    (hv : ∀ s ∈ Icc 0 (T / a ^ 2),
      HasDerivWithinAt v (unbalancedField Cred B bs bw Rs Rf a (v s)) (Icc 0 (T / a ^ 2)) s) :
    ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun τ => a⁻¹ • v (τ / a ^ 2))
      (slowField Cred B bs bw Rs Rf a (a⁻¹ • v (τ / a ^ 2))) (Icc 0 T) τ := by
  intro τ hτ
  have ha2 : 0 < a ^ 2 := by positivity
  have hmaps : MapsTo (fun τ : ℝ => τ / a ^ 2) (Icc 0 T) (Icc 0 (T / a ^ 2)) := by
    intro x hx
    exact ⟨div_nonneg hx.1 ha2.le, div_le_div_of_nonneg_right hx.2 ha2.le⟩
  have hin : HasDerivWithinAt (fun τ : ℝ => τ / a ^ 2) (1 / a ^ 2) (Icc 0 T) τ :=
    (hasDerivWithinAt_id τ _).div_const (a ^ 2)
  have hcomp := (hv (τ / a ^ 2) (hmaps hτ)).scomp τ hin hmaps
  have hfin := hcomp.const_smul a⁻¹
  refine hfin.congr_deriv ?_
  rw [slowField_eq Cred B bs bw Rs Rf ha, smul_smul, smul_inv_smul₀ ha]
  congr 1
  field_simp

/-- **`lem:supp-exact-slow-expansion`.**  Let `R_s, R_f` be analytic at `(a, v) = 0` with
the graded bounds `eq:supp-exact-graded-remainders`
`|R_s| ≤ C(a⁴ + a²|v| + a|v|²)`, `|R_f| ≤ C(a⁴ + a|v| + |v|²)` (for `0 < a`, `|v|` small).
Then, with `Σ₀, Φ₁` given by the mixed derivatives of `eq:supp-exact-slow-coefficients` and
`Φ₀(x,z) = C_red x + B z`:
1. `R_s(a, aξ) = a³Σ₀(ξ) + a⁴Σ₁(a, ξ)`, `R_f(a, aξ) = a²Φ₁(ξ) + a³Φ₂(a, ξ)` for `a ≠ 0`;
2. `Σ₁, Φ₂` are uniformly bounded on every bounded `ξ`-set for sufficiently small `a > 0`;
3. the substitution `v = aξ`, `s = τ/a²` turns the unbalanced field exactly into the slow
   system `eq:main-exact-slow-system`, both as vector fields and along solutions;
4. `Σ₀(0) = Φ₁(0) = 0`, and both maps are polynomials of degree at most two;
5. `Σ₀(ξ)` and `Φ₁(ξ)` are the leading Taylor coefficients of the rays `a ↦ R_s(a, aξ)`,
   `a ↦ R_f(a, aξ)` (orders three and two), all lower coefficients vanishing. -/
theorem slow_expansion (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (bs : Xs) (bw : W)
    (Rs : ℝ × (Xs × W) → Xs) (Rf : ℝ × (Xs × W) → W)
    (hRs : AnalyticAt ℝ Rs 0) (hRf : AnalyticAt ℝ Rf 0)
    (hbs : ∃ δ > 0, ∃ C, ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖Rs (a, v)‖ ≤ C * (a ^ 4 + a ^ 2 * ‖v‖ + a * ‖v‖ ^ 2))
    (hbf : ∃ δ > 0, ∃ C, ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖Rf (a, v)‖ ≤ C * (a ^ 4 + a * ‖v‖ + ‖v‖ ^ 2)) :
    (∀ a : ℝ, a ≠ 0 → ∀ ξ, Rs (a, a • ξ) = a ^ 3 • sigma0 Rs ξ + a ^ 4 • sigma1 Rs a ξ) ∧
    (∀ a : ℝ, a ≠ 0 → ∀ ξ, Rf (a, a • ξ) = a ^ 2 • phi1 Rf ξ + a ^ 3 • phi2 Rf a ξ) ∧
    (∀ ρ : ℝ, ∃ a₀ > 0, ∃ K, ∀ a : ℝ, 0 < a → a < a₀ → ∀ ξ : Xs × W, ‖ξ‖ ≤ ρ →
      ‖sigma1 Rs a ξ‖ ≤ K ∧ ‖phi2 Rf a ξ‖ ≤ K) ∧
    (∀ a : ℝ, a ≠ 0 → ∀ ξ, slowField Cred B bs bw Rs Rf a ξ
      = (a ^ 3)⁻¹ • unbalancedField Cred B bs bw Rs Rf a (a • ξ)) ∧
    (∀ a : ℝ, a ≠ 0 → ∀ (T : ℝ) (v : ℝ → Xs × W),
      (∀ s ∈ Icc 0 (T / a ^ 2),
        HasDerivWithinAt v (unbalancedField Cred B bs bw Rs Rf a (v s)) (Icc 0 (T / a ^ 2)) s) →
      ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun τ => a⁻¹ • v (τ / a ^ 2))
        (slowField Cred B bs bw Rs Rf a (a⁻¹ • v (τ / a ^ 2))) (Icc 0 T) τ) ∧
    sigma0 Rs 0 = 0 ∧ phi1 Rf 0 = 0 ∧
    (∃ (L : (Xs × W) →ₗ[ℝ] Xs) (Q : (Xs × W) →ₗ[ℝ] (Xs × W) →ₗ[ℝ] Xs),
      ∀ ξ, sigma0 Rs ξ = L ξ + Q ξ ξ) ∧
    (∃ (L : (Xs × W) →ₗ[ℝ] W) (Q : (Xs × W) →ₗ[ℝ] (Xs × W) →ₗ[ℝ] W),
      ∀ ξ, phi1 Rf ξ = L ξ + Q ξ ξ) ∧
    (∃ (ps : FormalMultilinearSeries ℝ (ℝ × (Xs × W)) Xs)
      (pf : FormalMultilinearSeries ℝ (ℝ × (Xs × W)) W), ∀ ξ : Xs × W,
      (∀ m < 3, ps m (fun _ => (1, ξ)) = 0) ∧ sigma0 Rs ξ = ps 3 (fun _ => (1, ξ)) ∧
      (∀ m < 2, pf m (fun _ => (1, ξ)) = 0) ∧ phi1 Rf ξ = pf 2 (fun _ => (1, ξ))) := by
  refine ⟨fun a ha ξ => rs_identity Rs ha ξ, fun a ha ξ => rf_identity Rf ha ξ,
    remainders_bounded hRs hRf hbs hbf, fun a ha ξ => slowField_eq Cred B bs bw Rs Rf ha ξ,
    fun a ha T v hv => slow_system_of_unbalanced Cred B bs bw Rs Rf ha v hv,
    sigma0_zero Rs, phi1_zero Rf, sigma0_degree_le_two Rs, phi1_degree_le_two Rf, ?_⟩
  obtain ⟨ps, rs, hps⟩ := hRs
  obtain ⟨pf, rf, hpf⟩ := hRf
  obtain ⟨δs, hδs, Cs, hCs⟩ := hbs
  obtain ⟨δf, hδf, Cf, hCf⟩ := hbf
  have hCs' : ∀ a v, 0 < a → a < δs → ‖v‖ < δs →
      ‖Rs (a, v)‖ ≤ Cs * (a ^ 4 + a ^ 2 * ‖v‖ + a ^ 1 * ‖v‖ ^ 2) := by
    intro a v h1 h2 h3; simpa using hCs a v h1 h2 h3
  have hCf' : ∀ a v, 0 < a → a < δf → ‖v‖ < δf →
      ‖Rf (a, v)‖ ≤ Cf * (a ^ 4 + a ^ 1 * ‖v‖ + a ^ 0 * ‖v‖ ^ 2) := by
    intro a v h1 h2 h3; simpa using hCf a v h1 h2 h3
  have he : ∀ ξ : Xs × W, (ampDir + slowDir ξ : ℝ × (Xs × W)) = (1, ξ) := fun ξ => by
    simp [ampDir, slowDir]
  refine ⟨ps, pf, fun ξ => ?_⟩
  have hs := sigma0_eq_coeff hps hδs hCs' ξ
  have hf := phi1_eq_coeff hpf hδf hCf' ξ
  rw [he] at hs hf
  exact ⟨hs.1, hs.2, hf.1, hf.2⟩

/-! ### Non-vacuity -/

/-- The hypothesis packet of `slow_expansion` is satisfiable by a nonzero pair of
remainders: `R_s(a, v) = a² v_s`, `R_f(a, v) = a v_f` (on `Xs = W = ℝ`). -/
example : (∃ δ > 0, ∃ C, ∀ (a : ℝ) (v : ℝ × ℝ), 0 < a → a < δ → ‖v‖ < δ →
      ‖(fun y : ℝ × (ℝ × ℝ) => y.1 ^ 2 * y.2.1) (a, v)‖
        ≤ C * (a ^ 4 + a ^ 2 * ‖v‖ + a * ‖v‖ ^ 2)) ∧
    (∃ δ > 0, ∃ C, ∀ (a : ℝ) (v : ℝ × ℝ), 0 < a → a < δ → ‖v‖ < δ →
      ‖(fun y : ℝ × (ℝ × ℝ) => y.1 * y.2.2) (a, v)‖ ≤ C * (a ^ 4 + a * ‖v‖ + ‖v‖ ^ 2)) ∧
    AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ) => y.1 ^ 2 * y.2.1) 0 ∧
    AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ) => y.1 * y.2.2) 0 := by
  refine ⟨⟨1, one_pos, 1, fun a v ha _ _ => ?_⟩, ⟨1, one_pos, 1, fun a v ha _ _ => ?_⟩,
    (analyticAt_fst.pow 2).mul (analyticAt_fst.comp analyticAt_snd),
    analyticAt_fst.mul (analyticAt_snd.comp analyticAt_snd)⟩
  · have h1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
    have hn : ‖a ^ 2 * v.1‖ = a ^ 2 * ‖v.1‖ := by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos ha]
    rw [hn]
    have : a ^ 2 * ‖v.1‖ ≤ a ^ 2 * ‖v‖ := mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith [pow_pos ha 4, mul_nonneg ha.le (sq_nonneg ‖v‖)]
  · have h1 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
    have hn : ‖a * v.2‖ = a * ‖v.2‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos ha]
    rw [hn]
    have : a * ‖v.2‖ ≤ a * ‖v‖ := mul_le_mul_of_nonneg_left h1 ha.le
    nlinarith [pow_pos ha 4, sq_nonneg ‖v‖]

end ExactSlowExpansion
end RenewalGeometry
