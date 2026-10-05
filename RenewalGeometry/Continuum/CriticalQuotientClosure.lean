/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientDefect

/-!
# Critical gauge-quotient closure: coframe/bank extraction and the Vitali clause
  (`thm:critical-quotient-defect`, Einstein–Standard-Model action-closure manuscript)

Continuation of `CriticalQuotientDefect.lean` (box rendering of the chart `K = box a b ⊂ ℝ⁴`,
smooth unitary connections of rank `m`, matter sections in the defining representation, the
gauges of the named Uhlenbeck theorem `UhlenbeckSmallEnergyGauge m`).  Steps of
"Full proof of critical gauge-quotient closure" composed here, on top of the quotient
compactness `critical_quotient_compactness_of_gauge`:

* (Q1) **coframe and bank extraction**: `CoframeLimit` (convergence `e_h → e` in `L^∞(K) ∩ H¹(K)`)
  under sequential precompactness, and convergence of the coefficient banks in a compact set,
  along the same subsequence as the Coulomb-chart limits;
* the **Vitali clause** ("uniform integrability of `|H_h|⁴` together with convergence in measure
  gives strong `L⁴` convergence by Vitali, so the quartic concentration measure vanishes"):
  `unifIntegrable_restrict_subset`, `unifIntegrable_transp` (uniform integrability is preserved by
  the unitary gauges, `|(R u)_c| ≤ Σ_e |u_e|`), `memLp_four_of_memW12_box` (Sobolev),
  `tendsto_L4_of_L2_of_unifIntegrable` (Vitali on a cube), `quotientLimitL4_of`;
* **`critical_quotient_closure_of_gauge`**: all of the above with one subsequence, conditional
  only on `UhlenbeckSmallEnergyGauge m`.

Not composed (see the ledger note): the passage of the matter Euler rows with the equivariant
budgets (Q5) and the metric equation `eq:critical-quotient-einstein`.  These need the
Standard-Model action and the regulator budgets (`EinsteinSMRegulatorSequence`, slab rendering,
structure group `G_SM = S(U(3)×U(2))`), which are equivariant only under `G_SM`-valued gauges,
whereas the named theorem `UhlenbeckSmallEnergyGauge m` produces `U(m)`-valued gauges; pulling the
tests back through the Coulomb gauges therefore requires the `G`-equivariant form of Uhlenbeck's
theorem (gauges in the structure group), which is a different statement from the present gap.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.CriticalQuotientClosure

open SobolevOpen CriticalGauge CriticalQuotient

set_option linter.unusedSectionVars false

/-! ### Uniform integrability on sub-boxes and under unitary transport -/

section UI

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Uniform `L^p`-integrability on `K` passes to measurable subsets `Q ⊆ K`. -/
theorem unifIntegrable_restrict_subset {ι F : Type*} [NormedAddCommGroup F] {f : ι → X → F}
    {p : ℝ≥0∞} {K Q : Set X} (hQ : MeasurableSet Q) (hQK : Q ⊆ K)
    (hf : UnifIntegrable f p (μ.restrict K)) : UnifIntegrable f p (μ.restrict Q) := by
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf hε
  refine ⟨δ, hδ, fun i s hs hμs => ?_⟩
  have h1 : eLpNorm (s.indicator (f i)) p (μ.restrict Q) =
      eLpNorm ((s ∩ Q).indicator (f i)) p (μ.restrict K) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs, eLpNorm_indicator_eq_eLpNorm_restrict (hs.inter hQ),
      Measure.restrict_restrict hs, Measure.restrict_restrict (hs.inter hQ),
      Set.inter_assoc, Set.inter_eq_left.mpr hQK]
  rw [h1]
  refine hfδ i (s ∩ Q) (hs.inter hQ) ?_
  rw [Measure.restrict_apply (hs.inter hQ), Set.inter_assoc, Set.inter_eq_left.mpr hQK,
    ← Measure.restrict_apply hs]
  exact hμs

end UI

section Transport

variable {m : ℕ}

/-- **Uniform integrability is preserved by unitary transport**: if all components of the
sections `u_h` are uniformly `L⁴`-integrable on `Q` and the gauges are unitary on `Q`, then the
components of the transported sections `R_h u_h` are uniformly `L⁴`-integrable on `Q`
(`|(R u)_c| ≤ Σ_e |u_e|`). -/
theorem unifIntegrable_transp {Q : Set (Fin 4 → ℝ)} (hQ : MeasurableSet Q)
    {R : ℕ → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hR : ∀ h, ∀ y ∈ Q, R h y ∈ unitaryGroup (Fin m) ℂ) {u : ℕ → (Fin 4 → ℝ) → Fin m → ℂ}
    (hu : ∀ h e, AEStronglyMeasurable (fun y => u h y e) (volume.restrict Q))
    (hUI : UnifIntegrable (fun p : ℕ × Fin m => fun y => u p.1 y p.2) 4 (volume.restrict Q))
    (c : Fin m) : UnifIntegrable (fun h => transp (R h) (u h) c) 4 (volume.restrict Q) := by
  intro ε hε
  obtain ⟨δ, hδ, hUIδ⟩ := hUI (show 0 < ε / (m + 1) by positivity)
  refine ⟨δ, hδ, fun h s hs hμs => ?_⟩
  have hpt : ∀ᵐ y ∂(volume.restrict Q), ‖s.indicator (transp (R h) (u h) c) y‖ ≤
      ‖∑ e, s.indicator (fun y => ‖u h y e‖) y‖ := by
    filter_upwards [ae_restrict_mem hQ] with y hy
    by_cases hys : y ∈ s
    · simp only [Set.indicator_of_mem hys]
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun e _ => norm_nonneg _)]
      exact norm_mulVec_unitary_le (hR h y hy) (u h y) c
    · simp [Set.indicator_of_notMem hys]
  refine (eLpNorm_mono_ae hpt).trans ?_
  have hsum : (fun y => ∑ e, s.indicator (fun y => ‖u h y e‖) y) =
      ∑ e, s.indicator (fun y => ‖u h y e‖) := by
    funext y; simp [Finset.sum_apply]
  rw [hsum]
  refine (eLpNorm_sum_le (fun e _ => ((hu h e).norm).indicator hs) (by norm_num)).trans ?_
  have he : ∀ e, eLpNorm (s.indicator fun y => ‖u h y e‖) 4 (volume.restrict Q) ≤
      ENNReal.ofReal (ε / (m + 1)) := by
    intro e
    have : (s.indicator fun y => ‖u h y e‖) = fun y => ‖s.indicator (fun y => u h y e) y‖ := by
      funext y; by_cases hy : y ∈ s <;> simp [hy]
    rw [this, eLpNorm_norm]
    exact hUIδ (h, e) s hs hμs
  calc ∑ e, eLpNorm (s.indicator fun y => ‖u h y e‖) 4 (volume.restrict Q)
      ≤ ∑ _e : Fin m, ENNReal.ofReal (ε / (m + 1)) := Finset.sum_le_sum fun e _ => he e
    _ = ENNReal.ofReal (m * (ε / (m + 1))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

end Transport

/-! ### The Vitali clause on a Coulomb cube -/

section Vitali

/-- On a box, `W^{1,2}` functions are in `L⁴` (critical Sobolev embedding). -/
theorem memLp_four_of_memW12_box {lo hi : Fin 4 → ℝ} (hlh : ∀ i, lo i < hi i)
    {f : (Fin 4 → ℝ) → ℂ} {g : Fin 4 → (Fin 4 → ℝ) → ℂ} (hW : MemW12 (box lo hi) f g) :
    MemLp f 4 (volume.restrict (box lo hi)) := by
  obtain ⟨C, hC⟩ := exists_sobolev_L4_box (ι := Fin 4) (by simp) hlh
  refine ⟨hW.memLp.1, (hC f g hW).trans_lt ?_⟩
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  exact ENNReal.add_lt_top.mpr ⟨hW.memLp.2, ENNReal.sum_lt_top.mpr fun i _ =>
    (hW.memLp_grad i).2⟩

/-- **Vitali step** (`thm:critical-quotient-defect`, last sentence): on a box, if `f_k → f` in
`L²`, `f ∈ W^{1,2}`, the `f_k` are measurable and uniformly `L⁴`-integrable, then `f_k → f` in
`L⁴` (convergence in measure + uniform integrability). -/
theorem tendsto_L4_of_L2_of_unifIntegrable {lo hi : Fin 4 → ℝ} (hlh : ∀ i, lo i < hi i)
    {f : ℕ → (Fin 4 → ℝ) → ℂ} {f₀ : (Fin 4 → ℝ) → ℂ} {g₀ : Fin 4 → (Fin 4 → ℝ) → ℂ}
    (hf : ∀ k, AEStronglyMeasurable (f k) (volume.restrict (box lo hi)))
    (hW : MemW12 (box lo hi) f₀ g₀)
    (hL2 : Tendsto (fun k => eLpNorm (f k - f₀) 2 (volume.restrict (box lo hi))) atTop (𝓝 0))
    (hUI : UnifIntegrable f 4 (volume.restrict (box lo hi))) :
    Tendsto (fun k => eLpNorm (f k - f₀) 4 (volume.restrict (box lo hi))) atTop (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict (box lo hi)) :=
    isFiniteMeasure_restrict.mpr (volume_box_ne_top lo hi)
  exact tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by norm_num) hf
    (memLp_four_of_memW12_box hlh hW) hUI
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hf hW.memLp.1 hL2)

end Vitali

/-! ### Coframe extraction (Q1), the quartic clause, and the composed theorem -/

section Closure

/-- **(Q1) convergence of the coframes along `φ`** in `L^∞(K) ∩ H¹(K)`: `e_{φ k} → e₀` uniformly
(`L^∞`) and in `L²`, and the classical partials `∂_μ e_{φ k}` converge in `L²` to `de₀` (the weak
gradient of the limit). -/
def CoframeLimit (K : Set (Fin 4 → ℝ)) (e : ℕ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (φ : ℕ → ℕ) : Prop :=
  ∃ (e₀ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (de₀ : Fin 4 → Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℝ),
    ∀ i ν, Tendsto (fun k => eLpNorm (fun y => e (φ k) y i ν - e₀ y i ν) ⊤ (volume.restrict K))
        atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (fun y => e (φ k) y i ν - e₀ y i ν) 2 (volume.restrict K))
        atTop (𝓝 0) ∧
      ∀ μ, Tendsto (fun k => eLpNorm (fun y => pd (fun y => e (φ k) y i ν) μ y - de₀ i ν μ y) 2
        (volume.restrict K)) atTop (𝓝 0)

theorem CoframeLimit.comp {K : Set (Fin 4 → ℝ)} {e : ℕ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ}
    {φ ψ : ℕ → ℕ} (h : CoframeLimit K e φ) (hψ : StrictMono ψ) : CoframeLimit K e (φ ∘ ψ) := by
  obtain ⟨e₀, de₀, h⟩ := h
  exact ⟨e₀, de₀, fun i ν => ⟨(h i ν).1.comp hψ.tendsto_atTop, (h i ν).2.1.comp hψ.tendsto_atTop,
    fun μ => ((h i ν).2.2 μ).comp hψ.tendsto_atTop⟩⟩

/-- The quotient limits on a cube together with **strong `L⁴` convergence of the designated
(Higgs) sections** `s ∈ SH` (`H_h → H` in `L⁴`: no quartic concentration). -/
def QuotientLimitL4 {m : ℕ} {S : Type} [Fintype S] (Q : Set (Fin 4 → ℝ)) (C : ℕ → MConn m)
    (uT : ℕ → S → Fin m → (Fin 4 → ℝ) → ℂ) (gT : ℕ → S → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ)
    (φ : ℕ → ℕ) (SH : Set S) : Prop :=
  ∃ (Ainf : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (GA : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ)
    (uinf : S → Fin m → (Fin 4 → ℝ) → ℂ) (Gu : S → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
    (∀ ν c e, MemW12 Q (Ainf ν c e) (GA ν c e)) ∧
    (∀ ν c e (q : ℝ≥0∞), 1 ≤ q → q < 4 → Tendsto (fun k => eLpNorm
      (entries (C (φ k)) ν c e - Ainf ν c e) q (volume.restrict Q)) atTop (𝓝 0)) ∧
    (∀ ν c e μ (w : (Fin 4 → ℝ) → ℝ), MemLp w 2 (volume.restrict Q) →
      Tendsto (fun k => ∫ x, w x • entryGrad (C (φ k)) ν c e μ x ∂(volume.restrict Q)) atTop
        (𝓝 (∫ x, w x • GA ν c e μ x ∂(volume.restrict Q)))) ∧
    (∀ μ ν c e (w : (Fin 4 → ℝ) → ℝ), MemLp w ⊤ (volume.restrict Q) →
      Tendsto (fun k => ∫ x, w x • curvatureW (entries (C (φ k))) (entryGrad (C (φ k))) μ ν c e x
        ∂(volume.restrict Q)) atTop
        (𝓝 (∫ x, w x • curvatureW Ainf GA μ ν c e x ∂(volume.restrict Q)))) ∧
    (∀ s c, MemW12 Q (uinf s c) (Gu s c)) ∧
    (∀ s c (q : ℝ≥0∞), 1 ≤ q → q < 4 → Tendsto (fun k => eLpNorm
      (uT (φ k) s c - uinf s c) q (volume.restrict Q)) atTop (𝓝 0)) ∧
    (∀ s c μ (w : (Fin 4 → ℝ) → ℝ), MemLp w 2 (volume.restrict Q) →
      Tendsto (fun k => ∫ x, w x • gT (φ k) s c μ x ∂(volume.restrict Q)) atTop
        (𝓝 (∫ x, w x • Gu s c μ x ∂(volume.restrict Q)))) ∧
    (∀ s c μ (w : (Fin 4 → ℝ) → ℝ), MemLp w ⊤ (volume.restrict Q) →
      Tendsto (fun k => ∫ x, w x • (gT (φ k) s c μ x +
          ∑ e, entries (C (φ k)) μ c e x * uT (φ k) s e x) ∂(volume.restrict Q)) atTop
        (𝓝 (∫ x, w x • (Gu s c μ x + ∑ e, Ainf μ c e x * uinf s e x) ∂(volume.restrict Q)))) ∧
    (∀ s ∈ SH, ∀ c, Tendsto (fun k => eLpNorm (uT (φ k) s c - uinf s c) 4 (volume.restrict Q))
      atTop (𝓝 0))

/-- `QuotientLimitL4` refines `QuotientLimit`. -/
theorem QuotientLimitL4.quotientLimit {m : ℕ} {S : Type} [Fintype S] {Q : Set (Fin 4 → ℝ)}
    {C : ℕ → MConn m} {uT : ℕ → S → Fin m → (Fin 4 → ℝ) → ℂ}
    {gT : ℕ → S → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} {φ : ℕ → ℕ} {SH : Set S}
    (h : QuotientLimitL4 Q C uT gT φ SH) : QuotientLimit Q C uT gT φ := by
  obtain ⟨Ainf, GA, uinf, Gu, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := h
  exact ⟨Ainf, GA, uinf, Gu, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **The Vitali clause on a Coulomb cube**: a quotient limit plus uniform `L⁴`-integrability of
the designated transported sections upgrades to strong `L⁴` convergence of those sections. -/
theorem quotientLimitL4_of {m : ℕ} {S : Type} [Fintype S] {lo hi : Fin 4 → ℝ}
    (hlh : ∀ i, lo i < hi i) {C : ℕ → MConn m} {uT : ℕ → S → Fin m → (Fin 4 → ℝ) → ℂ}
    {gT : ℕ → S → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} {φ : ℕ → ℕ} {SH : Set S}
    (h : QuotientLimit (box lo hi) C uT gT φ)
    (hmeas : ∀ k s c, AEStronglyMeasurable (uT k s c) (volume.restrict (box lo hi)))
    (hUI : ∀ s ∈ SH, ∀ c, UnifIntegrable (fun k => uT k s c) 4 (volume.restrict (box lo hi))) :
    QuotientLimitL4 (box lo hi) C uT gT φ SH := by
  obtain ⟨Ainf, GA, uinf, Gu, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨Ainf, GA, uinf, Gu, h1, h2, h3, h4, h5, h6, h7, h8, fun s hs c => ?_⟩
  have hUIφ : UnifIntegrable (fun k => uT (φ k) s c) 4 (volume.restrict (box lo hi)) :=
    fun ε hε => let ⟨δ, hδ, hδ'⟩ := hUI s hs c hε; ⟨δ, hδ, fun i => hδ' (φ i)⟩
  exact tendsto_L4_of_L2_of_unifIntegrable hlh (fun k => hmeas (φ k) s c) (h5 s c)
    (h6 s c 2 one_le_two (by norm_num)) hUIφ

/-- **`thm:critical-quotient-defect`, composed compactness and Vitali clauses, conditional on the
named Uhlenbeck gap `UhlenbeckSmallEnergyGauge m`** (box rendering of the chart `K = box a b`).
Hypotheses: (Q1) the coframes `e_h` are (sequentially) precompact in `L^∞(K) ∩ H¹(K)` and the
coefficient banks `θ_h` lie in a compact set; (Q2) smooth unitary connections with bounded and
uniformly integrable critical curvature energy; (Q3)/(Q4) the gauge-invariant bounds
`sup_h(‖u_{h,s}‖_2 + ‖∇^{A_h}u_{h,s}‖_2) < ∞` for the matter sections (Higgs, spinors, dual
spinors, in the defining representation); optionally, uniform `L⁴`-integrability of the
components of the designated Higgs sections `s ∈ SH` (`|H_h|⁴` uniformly integrable).
Conclusion: for every compact `K' ⊂ K` and `η > 0`, a finite cover of `K'` by Coulomb cubes with
cutoff-dependent unitary gauges (Coulomb condition, `L⁴` norms `≤ η`) and **one** subsequence
along which `e_h → e` in `L^∞ ∩ H¹`, `θ_h → θ₀` in the compact bank set, and on every cube all the
limits of `eq:critical-quotient-convergence` hold (`QuotientLimit`), with in addition strong
`L⁴` convergence of the Higgs sections `s ∈ SH` (`H_h → H` in `L⁴`; since `|R u| = |u|` the
quartic densities `|H_h|⁴` then converge in `L¹`: the quartic concentration measure vanishes). -/
theorem critical_quotient_closure_of_gauge {m : ℕ} (hU : UhlenbeckSmallEnergyGauge m)
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (_hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (A h) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {S : Type} [Fintype S] (u : ℕ → S → (Fin 4 → ℝ) → Fin m → ℂ)
    (hu : ∀ h s, ContDiff ℝ ∞ (u h s))
    (hQ3 : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h s,
      ∑ e, eLpNorm (fun y => u h s y e) 2 (volume.restrict (box a b)) +
        ∑ e, ∑ μ, eLpNorm (fun y => covDerV (A h) (u h s) μ y e) 2 (volume.restrict (box a b))
          ≤ B)
    (e : ℕ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hQ1 : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      CoframeLimit (box a b) e (φ ∘ ψ))
    {P : Type*} [MetricSpace P] {Pset : Set P} (hPset : IsCompact Pset) (θ : ℕ → P)
    (hθ : ∀ h, θ h ∈ Pset)
    (SH : Set S)
    (hUI4 : ∀ s ∈ SH, UnifIntegrable (fun p : ℕ × Fin m => fun y => u p.1 s y p.2) 4
      (volume.restrict (box a b)))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧
      (∀ j, innerCube (ctr j) r ⊆ box a b) ∧ K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ unitaryGroup (Fin m) ℂ) ∧
        (∀ h j, ∀ x ∈ innerCube (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (innerCube (ctr j) r)) ≤ η) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ CoframeLimit (box a b) e φ ∧
          (∃ θ₀ ∈ Pset, Tendsto (θ ∘ φ) atTop (𝓝 θ₀)) ∧ ∀ j,
          QuotientLimitL4 (innerCube (ctr j) r) (fun h => gaugeConn (R h j) (A h))
            (fun h s => transp (R h j) (u h s)) (fun h s => tgrad (R h j) (u h s)) φ SH := by
  obtain ⟨N, ctr, r, hr, hball, hcover, R, hRu, hRs, hdiv, ⟨BA, hBAt, hAW⟩, hA4⟩ :=
    uhlenbeck_ball_cover hU A hA hUI hK' hK'Q hη
  obtain ⟨B, hBt, hB⟩ := hQ3
  choose C hC using fun j => transported_bound (ctr j) hr m
  have hT := fun h j s => hC j (R h j) (hRu h j) (hRs h j) (A h) (hA h) (u h s) (hu h s) η (hA4 h j)
  have hQK : ∀ j, innerCube (ctr j) r ⊆ box a b := fun j =>
    (innerCube_subset_eBall (ctr j) hr).trans (hball j)
  have hRQ : ∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ unitaryGroup (Fin m) ℂ :=
    fun h j y hy => hRu h j y (innerCube_subset_eBall _ hr hy)
  refine ⟨N, ctr, r, hr, hQK, hcover, R, hRQ,
    fun h j x hx => hdiv h j x (innerCube_subset_eBall _ hr hx), fun h j ν c e =>
      (eLpNorm_mono_measure _ (Measure.restrict_mono (innerCube_subset_eBall _ hr) le_rfl)).trans
        (hA4 h j ν c e), ?_⟩
  -- uniform `W^{1,2}` bounds on every cube
  set Bj : Fin N → ℝ≥0∞ := fun j => BA + (C j : ℝ≥0∞) * (1 + (η : ℝ≥0∞)) * (m * B + m * B)
  have hBjt : ∀ j, Bj j ≠ ⊤ := fun j => ENNReal.add_ne_top.mpr ⟨hBAt, ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp)) (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by simp) hBt, ENNReal.mul_ne_top (by simp) hBt⟩)⟩
  have hsum1 : ∀ j h s, ∑ e, eLpNorm (fun y => u h s y e) 2 (volume.restrict (innerCube (ctr j) r))
      ≤ B := fun j h s =>
    (Finset.sum_le_sum fun e _ => eLpNorm_mono_measure _ (Measure.restrict_mono (hQK j) le_rfl)).trans
      (le_add_right le_rfl |>.trans (hB h s))
  have hsum2 : ∀ j h s, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (A h) (u h s) μ y e) 2
      (volume.restrict (innerCube (ctr j) r)) ≤ B := fun j h s =>
    (Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun μ _ =>
      eLpNorm_mono_measure _ (Measure.restrict_mono (hQK j) le_rfl)).trans
      (le_add_left le_rfl |>.trans (hB h s))
  have hBu : ∀ j h s c, w12Norm (innerCube (ctr j) r) (transp (R h j) (u h s) c)
      (tgrad (R h j) (u h s) c) ≤ Bj j := by
    intro j h s c
    refine ((hT h j s).2 c).trans (le_add_left ?_)
    gcongr
    · exact hsum1 j h s
    · exact hsum2 j h s
  have hBA : ∀ j h ν c e, w12Norm (innerCube (ctr j) r) (entries (gaugeConn (R h j) (A h)) ν c e)
      (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ Bj j := fun j h ν c e =>
    (w12Norm_mono (innerCube_subset_eBall _ hr) _ _).trans ((hAW h j ν c e).2.trans le_self_add)
  -- the common extraction for the quotient limits
  obtain ⟨φ₀, hφ₀, hQL⟩ := exists_common_subseq (fun j φ => QuotientLimit (innerCube (ctr j) r)
    (fun h => gaugeConn (R h j) (A h)) (fun h s => transp (R h j) (u h s))
    (fun h s => tgrad (R h j) (u h s)) φ) (fun j φ _ => exists_quotientLimit (fun i => by linarith)
      (fun h ν c e => (hAW h j ν c e).1.mono (innerCube_subset_eBall _ hr))
      (fun h s c => (hT h j s).1 c) (hBjt j) (fun h ν c e => hBA j h ν c e)
      (fun h s c => hBu j h s c) φ) (fun j φ ψ hψ hP => hP.comp hψ)
  -- (Q1): coframes, then the compact banks
  obtain ⟨ψ₁, hψ₁, hcf⟩ := hQ1 φ₀ hφ₀
  obtain ⟨θ₀, hθ₀, ψ₂, hψ₂, hθlim⟩ := hPset.tendsto_subseq (fun k => hθ ((φ₀ ∘ ψ₁) k))
  refine ⟨φ₀ ∘ ψ₁ ∘ ψ₂, hφ₀.comp (hψ₁.comp hψ₂), ?_, ⟨θ₀, hθ₀, hθlim⟩, fun j => ?_⟩
  · exact hcf.comp hψ₂
  -- the Vitali clause on every cube
  have hQL' := (hQL j).comp (hψ₁.comp hψ₂)
  have hcube : innerCube (ctr j) r = box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4) :=
    innerCube_eq_box _ _
  have hQm : MeasurableSet (innerCube (ctr j) r) := by
    rw [hcube]; exact (isOpen_box _ _).measurableSet
  rw [hcube] at hQL' ⊢
  refine quotientLimitL4_of (fun i => by linarith) hQL' (fun k s c => ?_) (fun s hs c => ?_)
  · have := ((hT k j s).1 c).memLp.1
    rwa [hcube] at this
  · have hUIQ := unifIntegrable_restrict_subset hQm (hQK j) (hUI4 s hs)
    rw [hcube] at hUIQ hQm
    have hmeasu : ∀ h e', AEStronglyMeasurable (fun y => u h s y e')
        (volume.restrict (box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4))) :=
      fun h e' => ((continuous_apply e').comp (hu h s).continuous).aestronglyMeasurable
    have hRQ' : ∀ h, ∀ y ∈ box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4),
        R h j y ∈ unitaryGroup (Fin m) ℂ := fun h y hy => hRQ h j y (by rwa [hcube])
    exact unifIntegrable_transp (R := fun h => R h j) (u := fun h => u h s) hQm hRQ' hmeasu hUIQ c

/-- **Non-vacuity** of the extra hypotheses of `critical_quotient_closure_of_gauge` (beyond those of
`critical_quotient_compactness_of_gauge`, whose non-vacuity is shown there): constant coframes are
precompact in `L^∞ ∩ H¹`, and the zero Higgs section is uniformly `L⁴`-integrable. -/
example : (∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      CoframeLimit (box (0 : Fin 4 → ℝ) 1) (fun _ _ _ _ => (0 : ℝ)) (φ ∘ ψ)) ∧
    UnifIntegrable (fun _p : ℕ × Fin 1 => fun _y : Fin 4 → ℝ => (0 : ℂ)) 4
      (volume.restrict (box (0 : Fin 4 → ℝ) 1)) := by
  have hpd : ∀ μ, (fun y : Fin 4 → ℝ => pd (fun _ : Fin 4 → ℝ => (0 : ℝ)) μ y) = 0 := by
    intro μ; funext y; simp [pd]
  refine ⟨fun φ _ => ⟨id, strictMono_id, fun _ _ _ => 0, fun _ _ _ _ => 0, fun i ν =>
    ⟨by simp; exact Filter.EventuallyEq.rfl, by simp, fun μ => ?_⟩⟩, fun ε hε => ⟨1, one_pos, fun _ s _ _ => by simp⟩⟩
  simp [hpd μ]

end Closure

end RenewalGeometry.CriticalQuotientClosure
