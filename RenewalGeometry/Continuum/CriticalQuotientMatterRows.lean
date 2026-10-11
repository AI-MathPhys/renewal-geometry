/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientCubeLimit

/-!
# The distributional Yang–Mills, Higgs, Dirac and dual-Dirac equations in the critical quotient
  (`thm:critical-quotient-defect`, `app:critical-quotient-proof`; Einstein–Standard-Model
  action-closure manuscript)

Helpers for the assembly of the matter Euler rows:

* `testJet_regular`: the jet of a smooth compactly supported test is continuous, bounded and
  Lipschitz;
* `boxVariation`: the complete first variation `D𝒮_θ(z)[v] = ∫_K Cov(j z)(j¹ v)` on the chart (for
  smooth fields the first variation of the action; the covector is the derivative of the complete
  jet density, `SMGaugeJet.fderiv_fullPt_redVar`);
* `bank_tendsto_all`: under bank convergence inside a compact physical set all couplings
  converge (and the mass of the defining carrier, if it is a continuous function of the bank).
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.CriticalQuotientRows

open SobolevOpen CriticalGauge CriticalQuotient CriticalQuotientClosure
  BallAnalysis.SMGaugeStructure SMGaugeLie EinsteinSM SMGaugeJet CurvatureCovariance
  FirstVariationCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ### Regularity of test jets -/

theorem lipschitz_of_test {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F}
    (hf : ContDiff ℝ ∞ f) {Kc : Set E4} (hKc : IsCompact Kc) (h0 : ∀ y ∉ Kc, f y = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖ := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hd0 : ∀ y ∉ Kc, fderiv ℝ f y = 0 := fun y hy => by
    have hev : f =ᶠ[𝓝 y] fun _ => 0 := Filter.mem_of_superset
      (hKc.isClosed.isOpen_compl.mem_nhds hy) fun y' hy' => h0 y' hy'
    rw [hev.fderiv_eq]; simp
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_test hfd hKc hd0
  refine ⟨M, hM0, fun x y => ?_⟩
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.differentiable (by simp)) z) (fun z _ => hM z) (mem_univ y) (mem_univ x)

theorem pd_test_props {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F}
    (hf : ContDiff ℝ ∞ f) {Kc : Set E4} (hKc : IsCompact Kc) (h0 : ∀ y ∉ Kc, f y = 0) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x => pd f i x) ∧ ∀ y ∉ Kc, pd f i y = 0 := by
  refine ⟨?_, fun y hy => ?_⟩
  · exact (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  · exact pd_eq_zero_of_eventually (Filter.mem_of_superset
      (hKc.isClosed.isOpen_compl.mem_nhds hy) fun y' hy' => h0 y' hy') i

/-- **The jet of a smooth compactly supported test is continuous, bounded and Lipschitz.** -/
theorem testJet_regular {S : Set E4} {v : FieldTuple (Fin 5)} (hv : IsSetTest S v) :
    Continuous (testJet v) ∧ (∃ C : ℝ, ∀ x, ‖testJet v x‖ ≤ C) ∧
      ∃ L : ℝ, ∀ x y, ‖testJet v x - testJet v y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨Kc, hKc, -, h0⟩ := hv.supp
  have he0 : ∀ y ∉ Kc, v.e y = 0 := fun y hy => (h0 y hy).1
  have hA0 : ∀ y ∉ Kc, v.A y = 0 := fun y hy => (h0 y hy).2.1
  have hH0 : ∀ y ∉ Kc, v.H y = 0 := fun y hy => (h0 y hy).2.2.1
  have hΨ0 : ∀ y ∉ Kc, v.Ψ y = 0 := fun y hy => (h0 y hy).2.2.2.1
  have hΨb0 : ∀ y ∉ Kc, v.Ψb y = 0 := fun y hy => (h0 y hy).2.2.2.2
  -- the derivative families
  have hpdfam : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F},
      ContDiff ℝ ∞ f → (∀ y ∉ Kc, f y = 0) →
      ContDiff ℝ ∞ (fun x => fun i => pd f i x) ∧ ∀ y ∉ Kc, (fun i => pd f i y) = 0 := by
    intro F _ _ f hf hf0
    exact ⟨contDiff_pi.mpr fun i => (pd_test_props hf hKc hf0 i).1,
      fun y hy => funext fun i => (pd_test_props hf hKc hf0 i).2 y hy⟩
  obtain ⟨de, de0⟩ := hpdfam hv.smooth_e he0
  obtain ⟨dA, dA0⟩ := hpdfam hv.smooth_A hA0
  obtain ⟨dH, dH0⟩ := hpdfam hv.smooth_H hH0
  obtain ⟨dΨ, dΨ0⟩ := hpdfam hv.smooth_Ψ hΨ0
  obtain ⟨dΨb, dΨb0⟩ := hpdfam hv.smooth_Ψb hΨb0
  have hcont : Continuous (testJet v) := by
    unfold testJet RJet.mk
    exact hv.smooth_e.continuous.prodMk (de.continuous.prodMk (hv.smooth_A.continuous.prodMk
      (dA.continuous.prodMk (hv.smooth_H.continuous.prodMk (dH.continuous.prodMk
        (hv.smooth_Ψ.continuous.prodMk (dΨ.continuous.prodMk (hv.smooth_Ψb.continuous.prodMk
          dΨb.continuous))))))))
  refine ⟨hcont, ?_, ?_⟩
  · have h0' : ∀ y ∉ Kc, testJet v y = 0 := fun y hy => by
      simp only [testJet, RJet.mk, he0 y hy, hA0 y hy, hH0 y hy, hΨ0 y hy, hΨb0 y hy]
      rw [show (fun i => pd v.e i y) = 0 from de0 y hy, show (fun i => pd v.A i y) = 0 from dA0 y hy,
        show (fun i => pd v.H i y) = 0 from dH0 y hy, show (fun i => pd v.Ψ i y) = 0 from dΨ0 y hy,
        show (fun i => pd v.Ψb i y) = 0 from dΨb0 y hy]
      rfl
    obtain ⟨C, -, hC⟩ := exists_bound_of_test hcont hKc h0'
    exact ⟨C, hC⟩
  · obtain ⟨L1, h1, hL1⟩ := lipschitz_of_test hv.smooth_e hKc he0
    obtain ⟨L2, h2, hL2⟩ := lipschitz_of_test de hKc de0
    obtain ⟨L3, h3, hL3⟩ := lipschitz_of_test hv.smooth_A hKc hA0
    obtain ⟨L4, h4, hL4⟩ := lipschitz_of_test dA hKc dA0
    obtain ⟨L5, h5, hL5⟩ := lipschitz_of_test hv.smooth_H hKc hH0
    obtain ⟨L6, h6, hL6⟩ := lipschitz_of_test dH hKc dH0
    obtain ⟨L7, h7, hL7⟩ := lipschitz_of_test hv.smooth_Ψ hKc hΨ0
    obtain ⟨L8, h8, hL8⟩ := lipschitz_of_test dΨ hKc dΨ0
    obtain ⟨L9, h9, hL9⟩ := lipschitz_of_test hv.smooth_Ψb hKc hΨb0
    obtain ⟨L10, h10, hL10⟩ := lipschitz_of_test dΨb hKc dΨb0
    set L := L1 + L2 + L3 + L4 + L5 + L6 + L7 + L8 + L9 + L10
    refine ⟨L, fun x y => ?_⟩
    have hb : ∀ {Lk : ℝ}, 0 ≤ Lk → Lk ≤ L → ∀ {a : ℝ}, a ≤ Lk * ‖x - y‖ → a ≤ L * ‖x - y‖ :=
      fun h0 hle a ha => ha.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))
    simp only [testJet, RJet.mk, Prod.mk_sub_mk, norm_prod_le_iff]
    refine ⟨hb h1 (by simp only [L]; linarith) (hL1 x y), hb h2 (by simp only [L]; linarith)
      (hL2 x y), hb h3 (by simp only [L]; linarith) (hL3 x y), hb h4 (by simp only [L]; linarith)
      (hL4 x y), hb h5 (by simp only [L]; linarith) (hL5 x y), hb h6 (by simp only [L]; linarith)
      (hL6 x y), hb h7 (by simp only [L]; linarith) (hL7 x y), hb h8 (by simp only [L]; linarith)
      (hL8 x y), hb h9 (by simp only [L]; linarith) (hL9 x y), hb h10 (by simp only [L]; linarith)
      (hL10 x y)⟩

/-! ### The complete first variation on the chart -/

/-- **`D𝒮_θ(z)[v]` on the chart** `K`: the integral of the complete first-variation covector
(first-order gravitational representative + Yang–Mills + Higgs + Dirac–Yukawa on the defining
carrier) at the jet of `z`, applied to the jet of the test. -/
def boxVariation {Ysec : Type} (mY : CoefficientBank Ysec → ℂ) (θ : CoefficientBank Ysec)
    (K : Set E4) (z v : FieldTuple (Fin 5)) : ℝ :=
  ∫ x in K, fullCov mY θ (redJet z x) (testJet v x)

/-! ### Banks -/

theorem bank_tendsto_all {Ysec : Type} [Fintype Ysec] (mY : CoefficientBank Ysec → ℂ)
    (hmY : ∃ f : (Fin 7 → ℝ) × (Ysec → Matrix (Fin 3) (Fin 3) ℂ) → ℂ, Continuous f ∧
      ∀ θ, mY θ = f (bankCoords θ))
    {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hP : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P) (ht : BankTendsto θ θ₀) :
    (∀ j, Tendsto (fun n => gaugeScalars (θ n) j) atTop (𝓝 (gaugeScalars θ₀ j))) ∧
      Tendsto (fun n => (θ n).lambdaH) atTop (𝓝 θ₀.lambdaH) ∧
      Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH) ∧
      Tendsto (fun n => (2 * (θ n).kappa)⁻¹) atTop (𝓝 (2 * θ₀.kappa)⁻¹) ∧
      Tendsto (fun n => -(2 * (θ n).Lambda)) atTop (𝓝 (-(2 * θ₀.Lambda))) ∧
      Tendsto (fun n => mY (θ n)) atTop (𝓝 (mY θ₀)) := by
  obtain ⟨hs, hl, hv⟩ := bank_couplings_tendsto hP ht
  obtain ⟨hk, hΛ⟩ := bank_gravity_tendsto hP ht
  obtain ⟨f, hf, hfm⟩ := hmY
  refine ⟨hs, hl, hv, hk, hΛ, ?_⟩
  simp only [hfm]
  exact (hf.tendsto _).comp ht


/-! ### The equivariant budgets along pulled-back tests -/

/-- **The first variations of the Coulomb-chart fields along a fixed test vanish in the limit**
(`app:critical-quotient-proof`: "Fix now a smooth test in a normalized chart and pull it back through
the cutoff-dependent gauge.  [Its] test size [stays] uniformly bounded, so the finite first
variation tends to zero without differentiating the gauge"): if the equivariant consistency and
stationarity budgets `c_h^eq + ε_h^eq → 0` (Q5) hold on the chart `S` with the covariant test size
`𝔫_{z_h}`, then for every fixed test `v` supported in a compact subset of the Coulomb cube `Q`,
`∫_Q Cov(j(R_n·z_{Φ n}))(j¹ v) → 0`. -/
theorem budget_pullback_tendsto {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    {S B : Set E4} {lo hi : E4} (hlh : ∀ i, lo i < hi i) (hS : MeasurableSet S)
    (hB : IsOpen B) (hQB : box lo hi ⊆ B) (hQS : box lo hi ⊆ S)
    {z : ℕ → FieldTuple (Fin 5)} (hz : ∀ n x, DiffAt (z n) x)
    (hGL : ∀ n, ∀ x ∈ S, (z n).e x ∈ coframeGL)
    {θ : ℕ → CoefficientBank Ysec} {Φ : ℕ → ℕ} (hΦ : StrictMono Φ)
    {R : ℕ → E4 → M5} (hRs : ∀ n c e, ContDiffOn ℝ ∞ (fun y => R n y c e) B)
    (hRG : ∀ n, ∀ y ∈ B, R n y ∈ GSM)
    (hWA : ∀ n ν c e, MemW12 (box lo hi) (entries (gaugeConn (R n) (connM (z (Φ n)).A)) ν c e)
      (entryGrad (gaugeConn (R n) (connM (z (Φ n)).A)) ν c e))
    {BA : ℝ≥0∞} (hBA : BA ≠ ⊤)
    (hBA' : ∀ n ν c e, w12Norm (box lo hi) (entries (gaugeConn (R n) (connM (z (Φ n)).A)) ν c e)
      (entryGrad (gaugeConn (R n) (connM (z (Φ n)).A)) ν c e) ≤ BA)
    (Dfin : ℕ → FieldTuple (Fin 5) → ℝ) (c ε : ℕ → ℝ)
    (hcons : ∀ h v, IsSetTest S v →
      |Dfin h v - boxVariation mY (θ h) S (z h) v| ≤ c h * (nSize (volume.restrict S) (z h).A v).toReal)
    (hstat : ∀ h v, IsSetTest S v →
      |Dfin h v| ≤ ε h * (nSize (volume.restrict S) (z h).A v).toReal)
    (hce : Tendsto (fun h => c h + ε h) atTop (𝓝 0))
    {v : FieldTuple (Fin 5)} (hv : IsSetTest (box lo hi) v) :
    Tendsto (fun n => ∫ x in box lo hi, fullCov mY (θ (Φ n))
      (redJet (gaugeTuple (R n) (z (Φ n))) x) (testJet v x)) atTop (𝓝 0) := by
  set μQ := volume.restrict (box lo hi)
  have : IsFiniteMeasure μQ := isFiniteMeasure_restrict.mpr (volume_box_ne_top lo hi)
  obtain ⟨C₀, C₁, hC₀, hC₁, hsize⟩ := nSize_le_of_L2 hv (μ := μQ)
  -- the Coulomb connections are bounded in `L²(Q)`
  have hA2 : ∀ n, eLpNorm (gaugeTuple (R n) (z (Φ n))).A 2 μQ ≤ 100 * BA := by
    intro n
    have hcomp : ∀ ν c e, eLpNorm (fun x => (gaugeTuple (R n) (z (Φ n))).A x ν c e) 2 μQ ≤ BA :=
      fun ν c e => le_add_right le_rfl |>.trans (hBA' n ν c e)
    have hm : ∀ ν c e, AEStronglyMeasurable (fun x => (gaugeTuple (R n) (z (Φ n))).A x ν c e) μQ :=
      fun ν c e => (hWA n ν c e).memLp.1
    calc _ ≤ ∑ ν, eLpNorm (fun x => (gaugeTuple (R n) (z (Φ n))).A x ν) 2 μQ :=
          eLpNorm_pi_le (fun ν => aesm_pi fun c => aesm_pi fun e => hm ν c e) (by norm_num)
      _ ≤ ∑ _ν : Fin 4, ∑ _c : Fin 5, ∑ _e : Fin 5, BA := Finset.sum_le_sum fun ν _ =>
          (eLpNorm_pi_le (fun c => aesm_pi fun e => hm ν c e) (by norm_num)).trans
            (Finset.sum_le_sum fun c _ => (eLpNorm_pi_le (fun e => hm ν c e) (by norm_num)).trans
              (Finset.sum_le_sum fun e _ => hcomp ν c e))
      _ = 100 * BA := by simp; ring
  have hAm : ∀ n, AEStronglyMeasurable (gaugeTuple (R n) (z (Φ n))).A μQ := fun n =>
    aesm_pi fun ν => aesm_pi fun c => aesm_pi fun e => (hWA n ν c e).memLp.1
  set N : ℝ≥0∞ := ENNReal.ofReal 25 * (C₀ + C₁ * (100 * BA))
  have hN : N ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
    ⟨hC₀, ENNReal.mul_ne_top hC₁ (ENNReal.mul_ne_top (by simp) hBA)⟩)
  have hQm : MeasurableSet (box lo hi) := (isOpen_box lo hi).measurableSet
  -- each first variation is controlled by the budgets
  have hbound : ∀ n, |∫ x in box lo hi, fullCov mY (θ (Φ n))
      (redJet (gaugeTuple (R n) (z (Φ n))) x) (testJet v x)| ≤ |c (Φ n) + ε (Φ n)| * N.toReal := by
    intro n
    have hpullQ := isSetTest_pullTest hB (hRs n) (hRG n) hv hQB
    have hpull : IsSetTest S (pullTest (R n) v) := hpullQ.mono hQS
    have e := integral_pullTest mY (θ (Φ n)) hB (hRs n) (hRG n) (z := z (Φ n))
      (fun x _ => hz (Φ n) x) (hGL (Φ n)) hv hQB hQS hS
    rw [← e]
    have hsz : (nSize (volume.restrict S) (z (Φ n)).A (pullTest (R n) v)).toReal ≤ N.toReal := by
      refine ENNReal.toReal_mono hN ?_
      calc nSize (volume.restrict S) (z (Φ n)).A (pullTest (R n) v) ≤
            ENNReal.ofReal 25 * nSize μQ (gaugeTuple (R n) (z (Φ n))).A v :=
            nSize_pullTest_le hB (hRs n) (hRG n) (z (Φ n)) hv hQB hQS hS hQm
        _ ≤ N := mul_le_mul_of_nonneg_left ((hsize _ (hAm n)).trans
            (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hA2 n) bot_le))) bot_le
    have h1 := hcons (Φ n) (pullTest (R n) v) hpull
    have h2 := hstat (Φ n) (pullTest (R n) v) hpull
    set D := boxVariation mY (θ (Φ n)) S (z (Φ n)) (pullTest (R n) v)
    set ns := (nSize (volume.restrict S) (z (Φ n)).A (pullTest (R n) v)).toReal
    have hns : 0 ≤ ns := ENNReal.toReal_nonneg
    have hD : |D| ≤ (c (Φ n) + ε (Φ n)) * ns := by
      calc |D| = |(D - Dfin (Φ n) (pullTest (R n) v)) + Dfin (Φ n) (pullTest (R n) v)| := by ring_nf
        _ ≤ |D - Dfin (Φ n) (pullTest (R n) v)| + |Dfin (Φ n) (pullTest (R n) v)| := abs_add_le _ _
        _ ≤ c (Φ n) * ns + ε (Φ n) * ns := by rw [abs_sub_comm]; exact add_le_add h1 h2
        _ = (c (Φ n) + ε (Φ n)) * ns := by ring
    calc |D| ≤ (c (Φ n) + ε (Φ n)) * ns := hD
      _ ≤ |c (Φ n) + ε (Φ n)| * ns := mul_le_mul_of_nonneg_right (le_abs_self _) hns
      _ ≤ |c (Φ n) + ε (Φ n)| * N.toReal := mul_le_mul_of_nonneg_left hsz (abs_nonneg _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (Real.norm_eq_abs _).trans_le (hbound n)) ?_
  have := ((continuous_abs.tendsto 0).comp (hce.comp hΦ.tendsto_atTop)).mul_const N.toReal
  simpa using this

end RenewalGeometry.CriticalQuotientRows
