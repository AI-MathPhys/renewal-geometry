/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.AnalyticSourceSobolevUpgrade
import RenewalGeometry.Analysis.DyadicRateAsymptotics
import RenewalGeometry.Analysis.TrigonometricTailBounds
import RenewalGeometry.Continuum.TorusTrigReconstruction

/-!
# Forcing-budget assembly and full-record residual interpolation

Einstein–Standard-Model action-closure manuscript: the bookkeeping steps of
`thm:native-source` (proof of `eq:native-strong-source`) and of `prop:shadow-residual-upgrade`.

## `thm:native-source`: assembly of the forcing budget

`native_source_assembly`: let `ε_{c,h}`, `L_{h,k}` and `F_{h,k}` be as in
`eq:native-forcing-budget` (`NativeRate.epsc`, `logFactor`, `forcingBudget`, any constant
`C_k > 0`).  Assume, as numbered inputs,
1. the zero-order physical estimate `eq:native-zero-source`
   `‖R_B(z_h)‖_{L²} + ‖R_D(z_h)‖_{L²} ≤ C₀ ε_{0,h}` — the **single input that depends on the
   open `prop:native-consistency`** (with `lem:nodal-source-transfer`);
2. the zero-order clause of `lem:native-tail-transfer` (low field residuals differ by
   `≤ C₁K²τ_{h,2}`);
3. the output of `lem:log-source-upgrade` (`AnalyticSourceUpgrade.log_source_upgrade`, proved)
   for the low-frequency residuals with amplitudes `C_A K²` (bosonic, `j = k`) and `C_A K` (Dirac,
   `j = k+1`), valid for every `L²` bound `ε`;
4. the source-tail transfer `eq:native-source-tail` (cost `C_t K^{k+2} τ_{h,k+2}`).
Then `𝒴_k(z_h) ≤ C F_{h,k}` with an explicit `C` (`eq:native-strong-source`).  The only analytic
step done here is the comparison of logarithmic factors (`one_add_log_two_add_mul_le`:
`1 + log(2 + λx) ≤ (1 + log max(1,λ))(1 + log(2 + x))`), which absorbs every constant into the
budget's `L_{h,k}`.

## `lem:native-tail-transfer`: the record's measured tails

* `trigInterp_eq_trigPoly`: the reconstruction `z_h = 𝓘_h^trig u_h`
  (`TorusTrigReconstruction.trigInterp`) is the trigonometric polynomial over the represented
  frequency set `Λ_h` with the record's coefficients;
* `record_tail_derivatives` (`eq:native-tail-derivatives` for the record):
  `z_h - z_h^lo` is the measured tail and `‖∂^α(z_h - z_h^lo)‖_∞ ≤ (2πK)^{|α|} τ_{h,j}(K)` for
  `|α| ≤ j` (`TrigTail.norm_deriv_tail_le`).

## `prop:shadow-residual-upgrade`: interpolation

* `shadow_residual_interpolation`: for residual families `R_B(t)`, `R_D(t)` on `𝕋^d` with
  `‖R‖_{L²(Q)} ≤ ε` (the zero residual `eq:shadow-zero-residual`, an input) and a cutoff-independent
  `L²_t H^s_x` bound `M` (the reader-reserve bound, an input), and `s > k + 1`,
  `‖R_B‖²_{L²_t H^k_x} ≤ (C_R ε^{1-k/s})²`, `‖R_D‖²_{L²_t H^{k+1}_x} ≤ (C_R ε^{1-(k+1)/s})²`,
  `C_R = max(1, M)` — the interpolation step, in the mixed `L²_t H^k_x` norm (time slab any finite
  measure space; time derivatives not included).
* `shadow_eta_le`: for `ε ≤ 1`, `η_{h,k} = C_R(ε^{1-k/s} + ε^{1-(k+1)/s}) ≤ 2 C_R ε^{1-(k+1)/s}`.
-/

open MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace RenewalGeometry.NativeSourceBudget

set_option linter.unusedSectionVars false

noncomputable section

open NativeRate

/-! ### Comparison of logarithmic factors -/

/-- `1 + log(2 + λx) ≤ (1 + log max(1,λ)) (1 + log(2 + x))` for `λ > 0`, `x ≥ 0`. -/
theorem one_add_log_two_add_mul_le {lam x : ℝ} (hl : 0 < lam) (hx : 0 ≤ x) :
    1 + Real.log (2 + lam * x) ≤ (1 + Real.log (max 1 lam)) * (1 + Real.log (2 + x)) := by
  have hm : 1 ≤ max 1 lam := le_max_left _ _
  have hlm : 0 ≤ Real.log (max 1 lam) := Real.log_nonneg hm
  have hl2 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  have hpos : 0 < 2 + lam * x := by positivity
  have hle : 2 + lam * x ≤ max 1 lam * (2 + x) := by
    have h1 : lam ≤ max 1 lam := le_max_right _ _
    have h2 : lam * x ≤ max 1 lam * x := mul_le_mul_of_nonneg_right h1 hx
    nlinarith
  have hlog : Real.log (2 + lam * x) ≤ Real.log (max 1 lam) + Real.log (2 + x) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log hpos hle
  nlinarith

/-! ### `thm:native-source`: the budget assembly -/

/-- **Assembly of `eq:native-strong-source`** (`thm:native-source`, last paragraph of the proof).
All quantities are reals for one record: `eB, eD` the `L²(Q)` norms of the full bosonic and Dirac
residuals, `eBlo, eDlo` those of the low-frequency comparison field, `YB, YD` the strong norms
`‖R_B‖_{L²_tH^k_x}`, `‖R_D‖_{L²_tH^{k+1}_x}` of the full field and `YBlo, YDlo` those of the low
field.  Inputs `(h0)`–`(h3)` are the four steps listed in the module docstring; `(h0)` is the
zero-order conclusion that rests on `prop:native-consistency`.  Conclusion: `YB + YD ≤ C F_{h,k}`. -/
theorem native_source_assembly (k : ℕ) {Ck σ h K τ₂ τm : ℝ} {C₀ C₁ Cj CA Ct : ℝ}
    {eB eD eBlo eDlo YB YD YBlo YDlo : ℝ}
    (hCk : 0 < Ck) (hh : 0 < h) (hK : 1 ≤ K) (hσ : 0 ≤ σ) (hτ₂ : 0 ≤ τ₂) (hτm : 0 ≤ τm)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCj : 0 < Cj) (hCA : 0 < CA)
    (heB : 0 ≤ eB) (heD : 0 ≤ eD)
    -- (h0) zero-order source (`eq:native-zero-source`, from `prop:native-consistency`)
    (h0 : eB + eD ≤ C₀ * eps0 σ h K)
    -- (h1) zero-order tail transfer (`lem:native-tail-transfer`, last sentence)
    (h1B : eBlo ≤ eB + C₁ * (K ^ 2 * τ₂)) (h1D : eDlo ≤ eD + C₁ * (K ^ 2 * τ₂))
    -- (h2) logarithmic upgrade of the low-frequency residuals (`lem:log-source-upgrade`)
    (h2B : ∀ ε : ℝ, 0 < ε → eBlo ≤ ε →
      YBlo ≤ Cj * ε * K ^ k * (1 + Real.log (2 + Cj * (CA * K ^ 2) * K ^ (k + 3) / ε)) ^ k)
    (h2D : ∀ ε : ℝ, 0 < ε → eDlo ≤ ε →
      YDlo ≤ Cj * ε * K ^ (k + 1) *
        (1 + Real.log (2 + Cj * (CA * K) * K ^ (k + 1 + 3) / ε)) ^ (k + 1))
    -- (h3) restoration of the measured tail (`eq:native-source-tail`)
    (h3B : YB ≤ YBlo + Ct * (K ^ (k + 2) * τm)) (h3D : YD ≤ YDlo + Ct * (K ^ (k + 2) * τm)) :
    YB + YD ≤
      max (2 * Cj * (C₀ + C₁ + 1) *
          (1 + Real.log (max 1 (Cj * CA / ((C₀ + C₁ + 1) * Ck)))) ^ (k + 1)) (2 * Ct) *
        forcingBudget k Ck σ h K τ₂ τm := by
  set Ĉ : ℝ := C₀ + C₁ + 1 with hĈ
  have hĈ0 : 0 < Ĉ := by positivity
  set ec : ℝ := epsc σ h K τ₂
  have hK0 : 0 < K := by linarith
  have hec : h * K ^ 3 ≤ ec := le_epsc hσ hτ₂
  have hec0 : 0 < ec := lt_of_lt_of_le (by positivity) hec
  have he0 : eps0 σ h K ≤ ec := by
    simp only [ec, epsc]; have : 0 ≤ K ^ 2 * τ₂ := by positivity
    linarith
  -- the common `L²` bound `E = Ĉ ε_c` for both low residuals
  set E : ℝ := Ĉ * ec
  have hE : 0 < E := by positivity
  have hlowB : eBlo ≤ E := by
    have : C₀ * eps0 σ h K ≤ C₀ * ec := mul_le_mul_of_nonneg_left he0 hC₀
    have h2 : C₁ * (K ^ 2 * τ₂) ≤ C₁ * ec := by
      refine mul_le_mul_of_nonneg_left ?_ hC₁
      simp only [ec, epsc]; have : 0 ≤ eps0 σ h K := by unfold eps0; positivity
      linarith
    simp only [E, Ĉ]; nlinarith
  have hlowD : eDlo ≤ E := by
    have : C₀ * eps0 σ h K ≤ C₀ * ec := mul_le_mul_of_nonneg_left he0 hC₀
    have h2 : C₁ * (K ^ 2 * τ₂) ≤ C₁ * ec := by
      refine mul_le_mul_of_nonneg_left ?_ hC₁
      simp only [ec, epsc]; have : 0 ≤ eps0 σ h K := by unfold eps0; positivity
      linarith
    simp only [E, Ĉ]; nlinarith
  -- comparison of the logarithmic factors with `L_{h,k}`
  set L : ℝ := logFactor k Ck K ec
  set x : ℝ := Ck * K ^ (k + 5) / ec
  have hx : 0 ≤ x := by positivity
  have hL1 : 1 ≤ L := by
    simp only [L, logFactor]
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + x)
    linarith
  set lam : ℝ := Cj * CA / (Ĉ * Ck)
  have hlam : 0 < lam := by positivity
  set cl : ℝ := 1 + Real.log (max 1 lam)
  have hcl : 1 ≤ cl := by have := Real.log_nonneg (le_max_left 1 lam); simp only [cl]; linarith
  have hlogcmp : 1 + Real.log (2 + lam * x) ≤ cl * L := one_add_log_two_add_mul_le hlam hx
  have hlog0 : 0 ≤ 1 + Real.log (2 + lam * x) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + lam * x by have : 0 ≤ lam * x := by positivity
                                                           linarith)
    linarith
  have hKk : K ^ k ≤ K ^ (k + 1) := pow_le_pow_right₀ hK (Nat.le_succ k)
  have hclL : 1 ≤ cl * L := one_le_mul_of_one_le_of_one_le hcl hL1
  -- bosonic low field (`j = k`, amplitude `C_A K²`)
  have hYBlo : YBlo ≤ Cj * Ĉ * cl ^ (k + 1) * (ec * K ^ (k + 1) * L ^ (k + 1)) := by
    have h := h2B E hE hlowB
    have harg : Cj * (CA * K ^ 2) * K ^ (k + 3) / E = lam * x := by
      simp only [E, lam, x]
      rw [show K ^ (k + 5) = K ^ 2 * K ^ (k + 3) by rw [← pow_add]; ring_nf]
      field_simp
    rw [harg] at h
    have h3 : (1 + Real.log (2 + lam * x)) ^ k ≤ (cl * L) ^ (k + 1) :=
      (pow_le_pow_left₀ hlog0 hlogcmp k).trans (pow_le_pow_right₀ hclL (Nat.le_succ k))
    calc YBlo ≤ Cj * E * K ^ k * (1 + Real.log (2 + lam * x)) ^ k := h
      _ ≤ Cj * E * K ^ (k + 1) * (cl * L) ^ (k + 1) := by gcongr
      _ = Cj * Ĉ * cl ^ (k + 1) * (ec * K ^ (k + 1) * L ^ (k + 1)) := by
          simp only [E]; rw [mul_pow]; ring
  -- Dirac low field (`j = k + 1`, amplitude `C_A K`)
  have hYDlo : YDlo ≤ Cj * Ĉ * cl ^ (k + 1) * (ec * K ^ (k + 1) * L ^ (k + 1)) := by
    have h := h2D E hE hlowD
    have harg : Cj * (CA * K) * K ^ (k + 1 + 3) / E = lam * x := by
      simp only [E, lam, x]
      rw [show K ^ (k + 5) = K * K ^ (k + 1 + 3) by rw [← pow_succ']]
      field_simp
    rw [harg] at h
    calc YDlo ≤ Cj * E * K ^ (k + 1) * (1 + Real.log (2 + lam * x)) ^ (k + 1) := h
      _ ≤ Cj * E * K ^ (k + 1) * (cl * L) ^ (k + 1) := by gcongr
      _ = Cj * Ĉ * cl ^ (k + 1) * (ec * K ^ (k + 1) * L ^ (k + 1)) := by
          simp only [E]; rw [mul_pow]; ring
  have hF : forcingBudget k Ck σ h K τ₂ τm = ec * K ^ (k + 1) * L ^ (k + 1) + K ^ (k + 2) * τm :=
    rfl
  rw [hF]
  set T1 : ℝ := ec * K ^ (k + 1) * L ^ (k + 1)
  set T2 : ℝ := K ^ (k + 2) * τm
  have hT1 : 0 ≤ T1 := by positivity
  have hT2 : 0 ≤ T2 := by positivity
  set M : ℝ := max (2 * Cj * Ĉ * cl ^ (k + 1)) (2 * Ct)
  have hM1 : 2 * Cj * Ĉ * cl ^ (k + 1) ≤ M := le_max_left _ _
  have hM2 : 2 * Ct ≤ M := le_max_right _ _
  calc YB + YD ≤ (YBlo + Ct * T2) + (YDlo + Ct * T2) := add_le_add h3B h3D
    _ ≤ 2 * Cj * Ĉ * cl ^ (k + 1) * T1 + 2 * Ct * T2 := by nlinarith
    _ ≤ M * T1 + M * T2 := by gcongr
    _ = M * (T1 + T2) := by ring

/-! ### `prop:shadow-residual-upgrade`: interpolation of the residuals -/

section Shadow

open TorusSobolev UnitAddTorus

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

variable {d : Type*} [Fintype d]

/-- `M^θ ≤ max(1, M)` for `M ≥ 0`, `0 ≤ θ ≤ 1`. -/
theorem rpow_le_max_one {M θ : ℝ} (hM : 0 ≤ M) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    M ^ θ ≤ max 1 M := by
  rcases le_or_gt M 1 with h | h
  · exact (Real.rpow_le_one hM h hθ0).trans (le_max_left _ _)
  · calc M ^ θ ≤ M ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le hθ1
      _ = M := Real.rpow_one M
      _ ≤ max 1 M := le_max_right _ _

/-- **One residual family, `L²_t H^k_x` interpolation with explicit budget**: if
`∫ ‖u(t)‖²_{L²} ≤ ε²` and `∫ ‖u(t)‖²_{H^s} ≤ M²` then
`∫ ‖u(t)‖²_{H^k} ≤ (max(1,M) ε^{1-k/s})²` for `0 ≤ k ≤ s`, `s > 0`. -/
theorem lintegral_sobSq_le_interp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {k s ε M : ℝ} (hk : 0 ≤ k) (hks : k ≤ s) (hs : 0 < s) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (u : α → Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (hu : ∀ t, MemH s (u t))
    (h0m : AEMeasurable (fun t => ENNReal.ofReal (sobSq 0 (u t))) μ)
    (hSm : AEMeasurable (fun t => ENNReal.ofReal (sobSq s (u t))) μ)
    (h0 : ∫⁻ t, ENNReal.ofReal (sobSq 0 (u t)) ∂μ ≤ ENNReal.ofReal (ε ^ 2))
    (hS : ∫⁻ t, ENNReal.ofReal (sobSq s (u t)) ∂μ ≤ ENNReal.ofReal (M ^ 2)) :
    ∫⁻ t, ENNReal.ofReal (sobSq k (u t)) ∂μ ≤
      ENNReal.ofReal ((max 1 M * ε ^ (1 - k / s)) ^ 2) := by
  set θ := k / s with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hk hs.le
  have hθ1 : θ ≤ 1 := (div_le_one hs).mpr hks
  have hI := lintegral_sobSq_interpolation μ hk hks hs u hu h0m hSm
  rw [← hθ] at hI
  refine hI.trans ?_
  calc (∫⁻ t, ENNReal.ofReal (sobSq 0 (u t)) ∂μ) ^ (1 - θ) *
        (∫⁻ t, ENNReal.ofReal (sobSq s (u t)) ∂μ) ^ θ
      ≤ ENNReal.ofReal (ε ^ 2) ^ (1 - θ) * ENNReal.ofReal (M ^ 2) ^ θ := by
        gcongr
    _ = ENNReal.ofReal ((ε ^ 2) ^ (1 - θ) * (M ^ 2) ^ θ) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ0,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    _ ≤ ENNReal.ofReal ((max 1 M * ε ^ (1 - θ)) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : (ε ^ 2) ^ (1 - θ) = (ε ^ (1 - θ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hε,
            ← Real.rpow_mul hε, mul_comm]
        have e2 : (M ^ 2) ^ θ = (M ^ θ) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hM,
            ← Real.rpow_mul hM, mul_comm]
        rw [e1, e2, mul_pow, mul_comm]
        have h1 : M ^ θ ≤ max 1 M := rpow_le_max_one hM hθ0 hθ1
        have h2 : 0 ≤ M ^ θ := Real.rpow_nonneg hM _
        gcongr

/-- **`prop:shadow-residual-upgrade`, interpolation step** (mixed `L²_t H^k_x` norms): for
bosonic and Dirac residual families with `‖R_B‖_{L²(Q)}, ‖R_D‖_{L²(Q)} ≤ ε` (the zero residual
`eq:shadow-zero-residual`, taken as input) and a cutoff-independent `L²_t H^s_x` bound `M` (the
reader-reserve bound, taken as input), `s > k + 1`, `k ≥ 0`:
`‖R_B‖²_{L²_t H^k_x} ≤ (C_R ε^{1-k/s})²` and `‖R_D‖²_{L²_t H^{k+1}_x} ≤ (C_R ε^{1-(k+1)/s})²`
with `C_R = max(1, M)`; the sum of the two norms is therefore at most `η_{h,k}` of
`eq:shadow-eta` (`shadow_eta_le` for `ε ≤ 1`). -/
theorem shadow_residual_interpolation {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {k s ε M : ℝ} (hk : 0 ≤ k) (hks : k + 1 < s) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (RB RD : α → Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hRB : ∀ t, MemH s (RB t)) (hRD : ∀ t, MemH s (RD t))
    (hB0m : AEMeasurable (fun t => ENNReal.ofReal (sobSq 0 (RB t))) μ)
    (hBSm : AEMeasurable (fun t => ENNReal.ofReal (sobSq s (RB t))) μ)
    (hD0m : AEMeasurable (fun t => ENNReal.ofReal (sobSq 0 (RD t))) μ)
    (hDSm : AEMeasurable (fun t => ENNReal.ofReal (sobSq s (RD t))) μ)
    (hB0 : ∫⁻ t, ENNReal.ofReal (sobSq 0 (RB t)) ∂μ ≤ ENNReal.ofReal (ε ^ 2))
    (hD0 : ∫⁻ t, ENNReal.ofReal (sobSq 0 (RD t)) ∂μ ≤ ENNReal.ofReal (ε ^ 2))
    (hBS : ∫⁻ t, ENNReal.ofReal (sobSq s (RB t)) ∂μ ≤ ENNReal.ofReal (M ^ 2))
    (hDS : ∫⁻ t, ENNReal.ofReal (sobSq s (RD t)) ∂μ ≤ ENNReal.ofReal (M ^ 2)) :
    ∫⁻ t, ENNReal.ofReal (sobSq k (RB t)) ∂μ ≤
        ENNReal.ofReal ((max 1 M * ε ^ (1 - k / s)) ^ 2) ∧
      ∫⁻ t, ENNReal.ofReal (sobSq (k + 1) (RD t)) ∂μ ≤
        ENNReal.ofReal ((max 1 M * ε ^ (1 - (k + 1) / s)) ^ 2) := by
  have hs : 0 < s := by linarith
  exact ⟨lintegral_sobSq_le_interp μ hk (by linarith) hs hε hM RB hRB hB0m hBSm hB0 hBS,
    lintegral_sobSq_le_interp μ (by linarith) hks.le hs hε hM RD hRD hD0m hDSm hD0 hDS⟩

/-- **`η_{h,k} ≤ 2 C_R ε^{1-(k+1)/s}` for `ε ≤ 1`** (`prop:shadow-residual-upgrade`, last
sentence; the manuscript's "`η_{h,k} ≤ C_R ε^{1-(k+1)/s}`" with the constant renamed): the Dirac
exponent `1-(k+1)/s` is the smaller one and dominates. -/
theorem shadow_eta_le {CR k s ε : ℝ} (hCR : 0 ≤ CR) (hk : 0 ≤ k) (hks : k + 1 < s)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    CR * (ε ^ (1 - k / s) + ε ^ (1 - (k + 1) / s)) ≤ 2 * CR * ε ^ (1 - (k + 1) / s) := by
  have hs : 0 < s := by linarith
  have hz : 0 ≤ 1 - (k + 1) / s := by
    rw [sub_nonneg, div_le_one hs]; linarith
  have hyz : 1 - (k + 1) / s ≤ 1 - k / s := by
    have : k / s ≤ (k + 1) / s := div_le_div_of_nonneg_right (by linarith) hs.le
    linarith
  have h := Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hz hyz
  nlinarith

end Shadow

/-! ### Non-vacuity -/

/-- The hypotheses of `native_source_assembly` are jointly satisfiable (vanishing residuals,
`h = K = 1`, unit constants), and the conclusion is then a genuine inequality against the
positive budget `F_{1,4} = 1` (`σ = τ = 0`, `ε_c = 1`). -/
example : (0 : ℝ) + 0 ≤ max (2 * 1 * (1 + 1 + 1) *
    (1 + Real.log (max 1 (1 * 1 / ((1 + 1 + 1) * 1)))) ^ (4 + 1)) (2 * 1) *
      forcingBudget 4 1 0 1 1 0 0 := by
  have hlog : ∀ y : ℝ, 0 ≤ y → 0 ≤ 1 + Real.log (2 + y) := fun y hy => by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + y by linarith); linarith
  refine native_source_assembly 4 (C₀ := 1) (C₁ := 1) (Cj := 1) (CA := 1) (Ct := 1)
    (eB := 0) (eD := 0) (eBlo := 0) (eDlo := 0) (YBlo := 0) (YDlo := 0)
    one_pos one_pos le_rfl le_rfl le_rfl le_rfl zero_le_one zero_le_one one_pos one_pos le_rfl
    le_rfl (by simp [eps0]) (by simp) (by simp) ?_ ?_ (by simp) (by simp)
  · intro ε hε _
    have := hlog (1 * (1 * 1 ^ 2) * 1 ^ (4 + 3) / ε) (by positivity)
    positivity
  · intro ε hε _
    have := hlog (1 * (1 * 1) * 1 ^ (4 + 1 + 3) / ε) (by positivity)
    positivity

/-! ### The record's reconstruction and its measured tails (`eq:native-tail`) -/

section RecordTails

open TorusTrigReconstruction LatticeTorusPlancherel TorusCellEmbedding TrigTail TorusSobolev

variable {d N : ℕ} [NeZero N]

/-- The trigonometric reconstruction `z_h = 𝓘_h^trig u_h` of a grid record is the trigonometric
polynomial over the represented frequency set `Λ_h = signedRep((ℤ/N)^d)` (the cube
`{|ℓ_μ| ≤ (N-1)/2}` for odd `N`) with the record's coefficients `û_h` (`coef u`). -/
theorem trigInterp_eq_trigPoly (u : Grid d N → ℂ) :
    trigInterp u = trigPoly ((Finset.univ : Finset (Grid d N)).image signedRep) (coef u) := by
  unfold trigPoly trigInterp
  rw [Finset.sum_image (fun k _ k' _ h => signedRep_injective h)]
  exact Finset.sum_congr rfl fun k _ => by rw [coef_signedRep]

/-- **`eq:native-tail-derivatives` for the record** (first display of
`lem:native-tail-transfer`, unit-torus rendering): with `z_h = 𝓘_h^trig u_h`,
`z_h^lo = 𝓘_h^trig P_{≤K} u_h` and `τ_{h,j}(K)` the measured tail of `eq:native-tail`, for every
`K > 0` and `|α| ≤ j`, `‖∂^α (z_h - z_h^lo)‖_∞ ≤ (2πK)^{|α|} τ_{h,j}(K)`; here
`∂^α(z_h - z_h^lo) = trigPoly Λ_h (derivCoeff α (tailPart K û))` is the classical derivative
(`TrigTail.isLineDeriv_trigPoly_derivCoeff`), and `z_h - z_h^lo` is its `α = 0` case. -/
theorem record_tail_derivatives (u : Grid d N → ℂ) {K : ℝ} (hK : 0 < K) {α : Fin d → ℕ} {j : ℕ}
    (hα : mOrder α ≤ j) :
    trigInterp u - trigPoly ((Finset.univ : Finset (Grid d N)).image signedRep)
        (lowPart K (coef u)) =
      trigPoly ((Finset.univ : Finset (Grid d N)).image signedRep) (tailPart K (coef u)) ∧
    ‖trigPoly ((Finset.univ : Finset (Grid d N)).image signedRep)
        (derivCoeff α (tailPart K (coef u)))‖ ≤
      (2 * π * K) ^ mOrder α * tau ((Finset.univ : Finset (Grid d N)).image signedRep) K j
        (coef u) := by
  refine ⟨?_, norm_deriv_tail_le _ hK _ hα⟩
  rw [trigInterp_eq_trigPoly]
  exact sub_low_eq_tail _ _ _

end RecordTails

end

end RenewalGeometry.NativeSourceBudget
