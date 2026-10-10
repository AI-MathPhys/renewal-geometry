/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSelectedClosed
import RenewalGeometry.Continuum.NativeRateClosed
import RenewalGeometry.Action.SelectedPolynomialRegime

/-!
# The selected closure on one record and the polynomial selected regime

Einstein–Standard-Model action-closure manuscript, `thm:native-selected-closure`
(`eq:selected-closure` on a single successful record) and `cor:selected-polynomial`
(`eq:selected-polynomial-rate` and the dyadic Borel–Cantelli clause).

* **`selected_record_bound`** — the deterministic closure: a legal native record with
  `σ ≤ s_h`, `V ≤ R_h²`, `i_{h,k} + γ_{h,k} ≤ α_h` and reader certificates
  `τ_{h,j} ≤ t_{h,j} + c_{h,j}√V` (`j = 2, k+2`) satisfies
  `‖𝒰 - 𝒰_*‖_{C_tH^k} + ‖Riem‖_{L²H^{k-1}} + ‖T^{SM}‖_{L²H^k} ≤ C_*(α_h + C₁e(k+1)!F̄_{h,k})`
  once the right side is `≤ d_*`, `hK ≤ c_res` and `T_{h,k+2} ≤ τ_*`.
* **`selected_polynomial_record`** — `eq:selected-polynomial-rate`: with `s_h = h^b`,
  `R_h = h^{-a}`, `α_h = h^c`, `c₁h^{-β} ≤ K_h ≤ c₂h^{-β}`, the polynomial reader budget
  `T_{h,j} ≤ C_Th^{-a}K_h^{2-q}` (`eq:app-polynomial-tail`) and the window
  `eq:selected-polynomial-window`, there are `h₀ > 0` and `C` such that every successful record on a
  grid with `h = 2π/n ≤ h₀` satisfies `left side of eq:selected-closure ≤ C h^ρ(1+|log h|)^{k+1}`.
* **`selected_polynomial_bc`** — along any chain with `c₁'2^{-n} ≤ h_n ≤ c₂'2^{-n}` (`h_n ≍ 2^{-n}`;
  odd grids, e.g. `n = 2^j + 1`), failure bounds `C_f(h_n^{2a} + h_n^{2ε})` and the success bound of
  `selected_polynomial_record` give, under any common coupling, eventual success and summable
  adjacent differences almost surely.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped Real Nat ENNReal

namespace RenewalGeometry.RecordTuple

open DiscreteEulerConsistency (R4)
open NativeScaling (Mat)
open ShiftedJetAction (Grid)
open NativeDensity DiscreteEulerConsistency NativeModel SlabData ActualJetState
  ActualJetCompleteForcing ActualJetBridge CoupledBootstrap ActualJetSmooth
open TrigInterp (recon reconLow tau)
open NativeRate (eps0 forcingBudget)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- **The deterministic selected closure on one record** (`eq:selected-closure`). -/
theorem selected_record_bound {δ : ℝ} (hδ : 0 < δ) {nX na nb : ℕ}
    (eX : (Fin nX → ℝ) ≃L[ℝ] StateP m (HSp M) 𝓢 (CoSpinor 𝓢))
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    (hAsym : ∀ j a b v, Aco (toSMData M δ) eX j a b v = Aco (toSMData M δ) eX j b a v)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin nX → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ C₁ cr τs Cst dst : ℝ, 0 ≤ C₁ ∧ 0 < cr ∧ 0 < τs ∧ 0 ≤ Cst ∧ 0 < dst ∧
    ∀ zs ∈ refSet (toSMData M δ) eX k (slabT t₀ t₁) Kr R₁,
    ∀ (n : ℕ) [NeZero n], Odd n → ∀ (u : Grid n → Field 𝔄 𝓗 𝓢) (K V sh Rr α t₂ c₂ tm cm : ℝ),
      1 ≤ K → 2 * π / n * K ≤ cr → LegalRec M δ Ke A t₀ n u K → 0 ≤ V → 0 < sh → 0 ≤ Rr →
      0 ≤ c₂ → 0 ≤ cm →
      tau n K 2 u ≤ t₂ + c₂ * Real.sqrt V → tau n K (k + 2) u ≤ tm + cm * Real.sqrt V →
      tm + cm * Rr ≤ τs → rowNorm M t₀ t₁ b n u ≤ sh → V ≤ Rr ^ 2 →
      ‖(nSlab M hδ eX eY eYD k h01).init (recTuple M hδ t₀ n u zs) -
          (nSlab M hδ eX eY eYD k h01).init zs‖ +
        (nSlab M hδ eX eY eYD k h01).harm (recTuple M hδ t₀ n u zs) ≤ α →
      α + C₁ * (Real.exp 1 * (k + 1)! *
        forcingBudget k Ck sh (2 * π / n) K (t₂ + c₂ * Rr) (tm + cm * Rr)) ≤ dst →
      dist ((nSlab M hδ eX eY eYD k h01).obs (recTuple M hδ t₀ n u zs))
          ((nSlab M hδ eX eY eYD k h01).obs zs) ≤
        Cst * (α + C₁ * (Real.exp 1 * (k + 1)! *
          forcingBudget k Ck sh (2 * π / n) K (t₂ + c₂ * Rr) (tm + cm * Rr))) := by
  obtain ⟨C₁, cr, τs, hC₁, hcr, hτs, hsrc⟩ :=
    native_source_tuple M hδ eY eYD hKe hdet A k (by omega) hCk hb h0 h1 h01.le
  obtain ⟨dst, Cst, hdst, hCst, hconc⟩ := coupled_bootstrap (toSMData M δ) eX eY eYD
    (toSMData_smooth M hδ) hAsym hk (slabT_pos h01) hKr hKO hR₁
  refine ⟨C₁, cr, τs, Cst, dst, hC₁, hcr, hτs, hCst, hdst, ?_⟩
  intro zs hzs n _ hn u K V sh Rr α t₂ c₂ tm cm hK hres hleg hV hsh hRr hc₂ hcm hr₂ hrm hT
    hrow hVR hal hsmall
  set S := nSlab M hδ eX eY eYD k h01 with hS
  have hK0 : 0 < K := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh : 0 < 2 * π / n := by positivity
  have hT₂ := SelectedClosure.reader_tail_le hc₂ hRr hr₂ hVR
  have hTm := SelectedClosure.reader_tail_le hcm hRr hrm hVR
  have hY : S.resB (recTuple M hδ t₀ n u zs) + S.resD (recTuple M hδ t₀ n u zs) ≤
      C₁ * forcingBudget k Ck sh (2 * π / n) K (tau n K 2 u) (tau n K (k + 2) u) := by
    rw [recTuple_eq M hδ t₀ zs hleg.tuple]
    exact hsrc n hn u K sh hK hres (hTm.trans hT) hleg.low_chart hleg.low_amp hleg.chart
      hleg.amp hsh.le (sq_le_of_rowNorm_le M hrow) hleg.tuple
  have hF := SelectedClosure.forcingBudget_le_of_le k hCk.le hsh.le hh hK0
    (TrigInterp.tau_nonneg n hK0 2 u) hT₂ (TrigInterp.tau_nonneg n hK0 _ u) hTm
  have hY' := hY.trans (mul_le_mul_of_nonneg_left hF hC₁)
  have hd : S.mismatch (recTuple M hδ t₀ n u zs) zs ≤ α + C₁ * (Real.exp 1 * (k + 1)! *
      forcingBudget k Ck sh (2 * π / n) K (t₂ + c₂ * Rr) (tm + cm * Rr)) := by
    unfold AposterioriShadow.SlabModel.mismatch
    linarith
  exact (hconc zs hzs _ trivial (hd.trans hsmall)).trans (mul_le_mul_of_nonneg_left hd hCst)

/-- Extraction of a threshold `h₀` from an eventual property at `0⁺`. -/
theorem exists_threshold {P : ℝ → Prop} (hP : ∀ᶠ h in 𝓝[>] (0 : ℝ), P h) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h, 0 < h → h ≤ h₀ → P h := by
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hP
  refine ⟨u / 2, by have : (0 : ℝ) < u := hu; linarith, fun h hh0 hh => hsub ⟨hh0, ?_⟩⟩
  have : (0 : ℝ) < u := hu
  linarith

/-- **`eq:selected-polynomial-rate` on every successful record of a fine grid.** -/
theorem selected_polynomial_record {δ : ℝ} (hδ : 0 < δ) {nX na nb : ℕ}
    (eX : (Fin nX → ℝ) ≃L[ℝ] StateP m (HSp M) 𝓢 (CoSpinor 𝓢))
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    (hAsym : ∀ j a b v, Aco (toSMData M δ) eX j a b v = Aco (toSMData M δ) eX j b a v)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin nX → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁)
    {q a bs c β c₁ c₂ CT : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (hβb : β < bs / (k + 1))
    (hβk : β < 1 / (k + 4)) (ha : a < β * (q - k - 5)) (hc₁ : 0 < c₁)
    (hCT : 0 ≤ CT) :
    ∃ h₀ Cr : ℝ, 0 < h₀ ∧ ∀ zs ∈ refSet (toSMData M δ) eX k (slabT t₀ t₁) Kr R₁,
    ∀ (n : ℕ) [NeZero n], Odd n → 2 * π / n ≤ h₀ →
    ∀ (u : Grid n → Field 𝔄 𝓗 𝓢) (K V t₂ c₂r tm cm : ℝ), 1 ≤ K →
      c₁ * (2 * π / n) ^ (-β) ≤ K → K ≤ c₂ * (2 * π / n) ^ (-β) →
      LegalRec M δ Ke A t₀ n u K → 0 ≤ V → 0 ≤ c₂r → 0 ≤ cm →
      tau n K 2 u ≤ t₂ + c₂r * Real.sqrt V → tau n K (k + 2) u ≤ tm + cm * Real.sqrt V →
      t₂ + c₂r * (2 * π / n) ^ (-a) ≤ CT * (2 * π / n) ^ (-a) * K ^ (2 - q) →
      tm + cm * (2 * π / n) ^ (-a) ≤ CT * (2 * π / n) ^ (-a) * K ^ (2 - q) →
      rowNorm M t₀ t₁ b n u ≤ (2 * π / n) ^ bs → V ≤ ((2 * π / n) ^ (-a)) ^ 2 →
      ‖(nSlab M hδ eX eY eYD k h01).init (recTuple M hδ t₀ n u zs) -
          (nSlab M hδ eX eY eYD k h01).init zs‖ +
        (nSlab M hδ eX eY eYD k h01).harm (recTuple M hδ t₀ n u zs) ≤ (2 * π / n) ^ c →
      dist ((nSlab M hδ eX eY eYD k h01).obs (recTuple M hδ t₀ n u zs))
          ((nSlab M hδ eX eY eYD k h01).obs zs) ≤
        Cr * ((2 * π / n) ^ SelectedPolynomial.rho k q a bs c β *
          (1 + |Real.log (2 * π / n)|) ^ (k + 1)) := by
  obtain ⟨C₁, cr, τs, Cst, dst, hC₁, hcr, hτs, hCst, hdst, H⟩ :=
    selected_record_bound M hδ eX eY eYD hAsym hKe hdet A hk hCk hb h0 h1 h01 hKr hKO hR₁
  obtain ⟨Cr0, hCr0⟩ := SelectedPolynomial.budget_rate_le k (q := q) (a := a) (b := bs) (c := c)
    (c₂ := c₂) hc₁ hCT hCk.le hβ0.le
  set ρ := SelectedPolynomial.rho k q a bs c β with hρ_def
  set E : ℝ := Real.exp 1 * (k + 1)! with hE
  have hE0 : 0 ≤ E := by positivity
  set Cm : ℝ := max 1 (C₁ * E) with hCm
  have hCm1 : 1 ≤ Cm := le_max_left _ _
  set Cp : ℝ := max Cr0 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  -- the exponents
  have hk4 : (0 : ℝ) < k + 4 := by positivity
  have hβ1 : β * (k + 4) < 1 := by rwa [lt_div_iff₀ hk4] at hβk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hβ' : β < 1 := by nlinarith
  have hq : 0 < β * (q - 2) - a := by nlinarith
  have hρ : 0 < ρ := SelectedPolynomial.rho_pos k hc hβb hβk ha
  set Mw : ℝ := max (c₁ ^ (2 - q)) (c₂ ^ (2 - q)) with hMw
  -- the threshold
  have ev1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), |c₂| * h ^ (1 - β) ≤ cr := by
    have := (tendsto_rpow_of_nhdsGT (h := fun x : ℝ => x) tendsto_id
      (show 0 < 1 - β by linarith)).const_mul |c₂|
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds hcr)
  have ev2 : ∀ᶠ h in 𝓝[>] (0 : ℝ), CT * Mw * h ^ (β * (q - 2) - a) ≤ τs := by
    have := (tendsto_rpow_of_nhdsGT (h := fun x : ℝ => x) tendsto_id hq).const_mul (CT * Mw)
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds hτs)
  have ev3 : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      Cm * Cp * (h ^ ρ * (1 + |Real.log h|) ^ (k + 1)) ≤ dst := by
    have := (NativeRate.tendsto_rpow_mul_one_add_abs_log_pow hρ (k + 1)).const_mul (Cm * Cp)
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds hdst)
  have ev4 : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < 1 :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) fun x hx => hx.2
  obtain ⟨h₀, hh₀, hthr⟩ := exists_threshold (ev1.and (ev2.and (ev3.and ev4)))
  refine ⟨h₀, Cst * Cm * Cp, hh₀, ?_⟩
  intro zs hzs n _ hn hnh u K V t₂ c₂r tm cm hK hlo hup hleg hV hc₂r hcm hr₂ hrm hT₂ hTm hrow
    hVR hal
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set h : ℝ := 2 * π / n with hh_def
  have hp : 0 < h := by positivity
  obtain ⟨t1, t2, t3, t4⟩ := hthr h hp hnh
  have hK0 : 0 < K := by linarith
  have hRa : 0 ≤ h ^ (-a) := Real.rpow_nonneg hp.le _
  -- resolution
  have hres : h * K ≤ cr := by
    refine (mul_le_rpow_of_le hp hup).trans (le_trans ?_ t1)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hp.le _)
  -- tail threshold
  have hKw := SelectedPolynomial.rpow_le_of_window hp hc₁ hlo hup (2 - q)
  have hTτ : tm + cm * h ^ (-a) ≤ τs := by
    refine hTm.trans (le_trans ?_ t2)
    have e : h ^ (-a) * h ^ (-β * (2 - q)) = h ^ (β * (q - 2) - a) := by
      rw [← Real.rpow_add hp]; congr 1; ring
    calc CT * h ^ (-a) * K ^ (2 - q) ≤ CT * h ^ (-a) * (Mw * h ^ (-β * (2 - q))) :=
          mul_le_mul_of_nonneg_left hKw (mul_nonneg hCT hRa)
      _ = CT * Mw * (h ^ (-a) * h ^ (-β * (2 - q))) := by ring
      _ = CT * Mw * h ^ (β * (q - 2) - a) := by rw [e]
  -- the budgets
  have hτ2 := SelectedClosure.reader_tail_le hc₂r hRa hr₂ hVR
  have hτm := SelectedClosure.reader_tail_le hcm hRa hrm hVR
  have hT₂0 : 0 ≤ t₂ + c₂r * h ^ (-a) := (TrigInterp.tau_nonneg n hK0 2 u).trans hτ2
  have hTm0 : 0 ≤ tm + cm * h ^ (-a) := (TrigInterp.tau_nonneg n hK0 _ u).trans hτm
  have hrate := hCr0 h K (t₂ + c₂r * h ^ (-a)) (tm + cm * h ^ (-a)) hp t4.le hK hlo hup hT₂0 hT₂
    hTm
  have hFb0 : 0 ≤ forcingBudget k Ck (h ^ bs) h K (t₂ + c₂r * h ^ (-a)) (tm + cm * h ^ (-a)) :=
    SourceCompare.forcingBudget_nonneg k hCk.le (Real.rpow_nonneg hp.le _) hp.le hK hT₂0 hTm0
  have hα0 : 0 ≤ h ^ c := Real.rpow_nonneg hp.le _
  have hrt0 : 0 ≤ h ^ ρ * (1 + |Real.log h|) ^ (k + 1) := by
    have := Real.rpow_nonneg hp.le ρ; positivity
  have hcomb : h ^ c + C₁ * (E * forcingBudget k Ck (h ^ bs) h K (t₂ + c₂r * h ^ (-a))
      (tm + cm * h ^ (-a))) ≤ Cm * Cp * (h ^ ρ * (1 + |Real.log h|) ^ (k + 1)) := by
    have h1' : h ^ c ≤ Cm * h ^ c := le_mul_of_one_le_left hα0 hCm1
    have h2' : C₁ * (E * forcingBudget k Ck (h ^ bs) h K (t₂ + c₂r * h ^ (-a))
        (tm + cm * h ^ (-a))) ≤ Cm * forcingBudget k Ck (h ^ bs) h K (t₂ + c₂r * h ^ (-a))
          (tm + cm * h ^ (-a)) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hFb0
    have h3' : h ^ c + forcingBudget k Ck (h ^ bs) h K (t₂ + c₂r * h ^ (-a))
        (tm + cm * h ^ (-a)) ≤ Cp * (h ^ ρ * (1 + |Real.log h|) ^ (k + 1)) :=
      hrate.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrt0)
    have hCm0 : 0 ≤ Cm := le_trans zero_le_one hCm1
    calc _ ≤ Cm * h ^ c + Cm * forcingBudget k Ck (h ^ bs) h K (t₂ + c₂r * h ^ (-a))
          (tm + cm * h ^ (-a)) := add_le_add h1' h2'
      _ = Cm * (h ^ c + forcingBudget k Ck (h ^ bs) h K (t₂ + c₂r * h ^ (-a))
          (tm + cm * h ^ (-a))) := by ring
      _ ≤ Cm * (Cp * (h ^ ρ * (1 + |Real.log h|) ^ (k + 1))) :=
          mul_le_mul_of_nonneg_left h3' hCm0
      _ = _ := by ring
  have hmain := H zs hzs n hn u K V (h ^ bs) (h ^ (-a)) (h ^ c) t₂ c₂r tm cm hK hres hleg hV
    (Real.rpow_pos_of_pos hp _) hRa hc₂r hcm hr₂ hrm hTτ hrow hVR hal (hcomb.trans t3)
  refine hmain.trans ?_
  calc Cst * (h ^ c + C₁ * (E * forcingBudget k Ck (h ^ bs) h K (t₂ + c₂r * h ^ (-a))
        (tm + cm * h ^ (-a)))) ≤ Cst * (Cm * Cp * (h ^ ρ * (1 + |Real.log h|) ^ (k + 1))) :=
        mul_le_mul_of_nonneg_left hcomb hCst
    _ = _ := by ring

/-- **The Borel–Cantelli clause of `cor:selected-polynomial` along `h_n ≍ 2^{-n}`**: with failure
bounds `μ(Fail_n) ≤ C_f(h_n^{2a} + h_n^{2ε})` (`SelectedPolynomial.failure_le`) and the success
bound `dist ≤ C_s h_n^ρ(1+|log h_n|)^{k+1}` (`selected_polynomial_record`), under any common
coupling the selected branch eventually succeeds and has summable adjacent differences a.s. -/
theorem selected_polynomial_bc {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    {E : Type*} [PseudoMetricSpace E] (k : ℕ) {ρ a ε c₁' c₂' Cf Cs : ℝ} (hρ : 0 < ρ)
    (ha : 0 < a) (hε : 0 < ε) (hc₁' : 0 < c₁') (hCf : 0 ≤ Cf) (hs : ℕ → ℝ)
    (hlo : ∀ n, c₁' * (1 / 2) ^ n ≤ hs n) (hup : ∀ n, hs n ≤ c₂' * (1 / 2) ^ n)
    (Fail : ℕ → Set Ω') (hμ : ∀ n, μ (Fail n) ≤ ENNReal.ofReal (Cf * (hs n ^ (2 * a) +
      hs n ^ (2 * ε))))
    (x : ℕ → Ω' → E) (x₀ : E)
    (hsucc : ∀ n ω, ω ∉ Fail n → dist (x n ω) x₀ ≤
      Cs * (hs n ^ ρ * (1 + |Real.log (hs n)|) ^ (k + 1))) :
    ∀ᵐ ω ∂μ, (∀ᶠ n in atTop, ω ∉ Fail n) ∧
      Summable (fun n => dist (x (n + 1) ω) (x n ω)) := by
  have hpos : ∀ n, 0 < hs n := fun n => lt_of_lt_of_le (by positivity) (hlo n)
  have hsa : Summable (fun n => hs n ^ (2 * a)) := by
    simpa using summable_rate_of_dyadic (by linarith : 0 < 2 * a) 0 hc₁' hlo hup
  have hse : Summable (fun n => hs n ^ (2 * ε)) := by
    simpa using summable_rate_of_dyadic (by linarith : 0 < 2 * ε) 0 hc₁' hlo hup
  refine SelectedClosure.selected_borel_cantelli μ Fail (fun n => Cf * (hs n ^ (2 * a) +
    hs n ^ (2 * ε))) (fun n => by
      have := Real.rpow_nonneg (hpos n).le (2 * a)
      have := Real.rpow_nonneg (hpos n).le (2 * ε)
      positivity) ((hsa.add hse).mul_left Cf) hμ x x₀
    (fun n => hs n ^ ρ * (1 + |Real.log (hs n)|) ^ (k + 1))
    (summable_rate_of_dyadic hρ (k + 1) hc₁' hlo hup) Cs hsucc

/-- **Borel–Cantelli with an eventual success bound** (`thm:native-selected-closure`, last
clause): as `SelectedClosure.selected_borel_cantelli`, but the closure bound on success is only
required from some stage `n₀` on (where the smallness condition of the one-cutoff closure holds,
e.g. once `D̄_n ≤ d_*`, which is eventual for summable `D̄`). -/
theorem selected_borel_cantelli_eventually {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    {E : Type*} [PseudoMetricSpace E] (Fail : ℕ → Set Ω') (p : ℕ → ℝ) (hp0 : ∀ n, 0 ≤ p n)
    (hp : Summable p) (hμ : ∀ n, μ (Fail n) ≤ ENNReal.ofReal (p n))
    (x : ℕ → Ω' → E) (x₀ : E) (D : ℕ → ℝ) (hD : Summable D) (C : ℝ) (n₀ : ℕ)
    (hsucc : ∀ n, n₀ ≤ n → ∀ ω, ω ∉ Fail n → dist (x n ω) x₀ ≤ C * D n) :
    ∀ᵐ ω ∂μ, (∀ᶠ n in atTop, ω ∉ Fail n) ∧
      Summable (fun n => dist (x (n + 1) ω) (x n ω)) := by
  have H := SelectedClosure.selected_borel_cantelli μ (fun n => Fail (n + n₀))
    (fun n => p (n + n₀)) (fun n => hp0 _) ((summable_nat_add_iff n₀).2 hp) (fun n => hμ _)
    (fun n => x (n + n₀)) x₀ (fun n => D (n + n₀)) ((summable_nat_add_iff n₀).2 hD) C
    (fun n ω hω => hsucc (n + n₀) (Nat.le_add_left _ _) ω hω)
  filter_upwards [H] with ω ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h1
    refine Filter.eventually_atTop.2 ⟨N + n₀, fun m hm => ?_⟩
    have := hN (m - n₀) (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  · refine (summable_nat_add_iff n₀).1 ?_
    refine h2.congr fun n => ?_
    simp only [Nat.add_right_comm n 1 n₀]

end

end RenewalGeometry.RecordTuple
