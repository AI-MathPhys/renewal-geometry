/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientEinsteinEquation

/-!
# `thm:critical-quotient-defect`: the assembled critical-energy quotient defect closure
  (Einstein–Standard-Model action-closure manuscript)

**`critical_quotient_defect_SM`** — under (Q1)–(Q5) (box rendering of the chart `K`,
defining-carrier matter, structure group `G_SM = S(U(3) × U(2))`), for every compact `K' ⊂ K`:
a finite cover of `K'` by Coulomb cubes with cutoff-dependent smooth `G_SM`-valued gauges, **one**
subsequence and a limit bank such that on every cube
* the critical convergences `eq:critical-quotient-convergence` hold (`CubeConv`);
* the limit packet solves the Yang–Mills, Higgs, Dirac and dual-Dirac equations in distributions;
* the curvature, covariant-Higgs-gradient and quartic packets have covariance measures
  `𝖰_F, 𝖰_K, 𝖰_Y` (`lem:positive-packet-defect`, `IsDefect`), positive semidefinite, and the
  **metric equation `eq:critical-quotient-einstein`** holds:
  `∫_Q Cov_{θ₀}(j L)(j¹ v) + 𝔖(j¹ v) = 0` for every smooth test `v` supported in the cube, where
  `𝔖 = 𝔖_YM + 𝔖_H` is the contraction of the covariance measures with the metric variations of the
  Yang–Mills, Higgs-kinetic and potential densities at the (continuous) limit coframe.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.CriticalQuotientRows

open SobolevOpen CriticalGauge CriticalQuotient CriticalQuotientClosure
  BallAnalysis.SMGaugeStructure SMGaugeLie EinsteinSM SMGaugeJet FirstVariationCalculus
  QuadraticPacketDefect BosonicStressDefectBox CurvatureCovariance

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ### Extraction of the covariance measures -/

section Extraction

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {V₀ : Measure K} [IsFiniteMeasure V₀]

theorem isDefect_comp {ι : Type*} [Fintype ι] {Y : ℕ → ι → K → ℝ} {Y₀ : ι → K → ℝ}
    {Q : StrongDual ℝ C(K, ι → ι → ℝ)} (hQ : IsDefect V₀ Y Y₀ Q) {σ : ℕ → ℕ}
    (hσ : StrictMono σ) : IsDefect V₀ (fun n => Y (σ n)) Y₀ Q :=
  fun P => (hQ P).comp hσ.tendsto_atTop

/-- **Joint extraction of three covariance measures** (`lem:positive-packet-defect` three times). -/
theorem exists_three_defects {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    {Y₁ : ℕ → ι₁ → K → ℝ} {Y₁₀ : ι₁ → K → ℝ} {Y₂ : ℕ → ι₂ → K → ℝ} {Y₂₀ : ι₂ → K → ℝ}
    {Y₃ : ℕ → ι₃ → K → ℝ} {Y₃₀ : ι₃ → K → ℝ} (h₁ : WeakL2 V₀ Y₁ Y₁₀) (h₂ : WeakL2 V₀ Y₂ Y₂₀)
    (h₃ : WeakL2 V₀ Y₃ Y₃₀) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (Q₁ : StrongDual ℝ C(K, ι₁ → ι₁ → ℝ))
      (Q₂ : StrongDual ℝ C(K, ι₂ → ι₂ → ℝ)) (Q₃ : StrongDual ℝ C(K, ι₃ → ι₃ → ℝ)),
      IsDefect V₀ (fun n => Y₁ (ψ n)) Y₁₀ Q₁ ∧ IsDefect V₀ (fun n => Y₂ (ψ n)) Y₂₀ Q₂ ∧
        IsDefect V₀ (fun n => Y₃ (ψ n)) Y₃₀ Q₃ := by
  obtain ⟨σ₁, hσ₁, Q₁, hQ₁⟩ := exists_isDefect h₁
  obtain ⟨σ₂, hσ₂, Q₂, hQ₂⟩ := exists_isDefect (h₂.comp hσ₁)
  obtain ⟨σ₃, hσ₃, Q₃, hQ₃⟩ := exists_isDefect (h₃.comp (hσ₁.comp hσ₂))
  exact ⟨σ₁ ∘ σ₂ ∘ σ₃, hσ₁.comp (hσ₂.comp hσ₃), Q₁, Q₂, Q₃,
    isDefect_comp hQ₁ (hσ₂.comp hσ₃), isDefect_comp hQ₂ hσ₃, hQ₃⟩

/-- Positivity of a covariance measure on pointwise positive semidefinite coefficient fields. -/
theorem isDefect_nonneg_psd {ι : Type*} [Fintype ι] {Y : ℕ → ι → K → ℝ} {Y₀ : ι → K → ℝ}
    {Q : StrongDual ℝ C(K, ι → ι → ℝ)} (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    {P : C(K, ι → ι → ℝ)} (hP : ∀ x w, 0 ≤ qf (P x) w) : 0 ≤ Q P :=
  hQ.nonneg hY (S := fun _ => univ) (fun _ => Eventually.of_forall fun _ => mem_univ _)
    fun x w _ => hP x w

end Extraction

/-! ### The three weak packets on a Coulomb cube -/

section CubePackets

variable {lo hi a b : E4}

/-- **Weak `L²(V0)` convergence of the three packets** (curvature, covariant Higgs gradient,
quartic) of the gauge-transformed fields on a Coulomb cube. -/
theorem cube_packets_weakL2 (hlh : ∀ i, lo i < hi i) {z : ℕ → FieldTuple (Fin 5)}
    {R : ℕ → E4 → M5}
    (hzA : ∀ n, ContDiff ℝ ∞ (z n).A) (hzH : ∀ n, ContDiff ℝ ∞ (z n).H)
    (hz : ∀ n x, DiffAt (z n) x)
    (hlie : ∀ n x μ, (z n).A x μ ∈ smLie) (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x)
    (e₀ : E4 → CoframeFibre) (de₀ : Fin 4 → Fin 4 → Fin 4 → E4 → ℝ)
    (hWA : ∀ n ν c e, MemW12 (box lo hi) (entries (gaugeConn (R n) (connM (z n).A)) ν c e)
      (entryGrad (gaugeConn (R n) (connM (z n).A)) ν c e))
    (hWu : ∀ n s c, MemW12 (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c))
    {Bu : ℝ≥0∞} (hBu : Bu ≠ ⊤)
    (hBu' : ∀ n s c, w12Norm (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c) ≤ Bu)
    {Ainf : Fin 4 → Fin 5 → Fin 5 → E4 → ℂ} {GA : Fin 4 → Fin 5 → Fin 5 → Fin 4 → E4 → ℂ}
    {uinf : MIdx → Fin 5 → E4 → ℂ} {Gu : MIdx → Fin 5 → Fin 4 → E4 → ℂ}
    (q1 : ∀ ν c e, MemW12 (box lo hi) (Ainf ν c e) (GA ν c e))
    (q2 : ∀ ν c e, Tendsto (fun n => eLpNorm (entries (gaugeConn (R n) (connM (z n).A)) ν c e -
      Ainf ν c e) 2 (volume.restrict (box lo hi))) atTop (𝓝 0))
    (q4 : ∀ μ ν c e (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • curvatureW (entries (gaugeConn (R n) (connM (z n).A)))
        (entryGrad (gaugeConn (R n) (connM (z n).A))) μ ν c e x ∂(volume.restrict (box lo hi)))
        atTop (𝓝 (∫ x, w x • curvatureW Ainf GA μ ν c e x ∂(volume.restrict (box lo hi)))))
    (q5 : ∀ s c, MemW12 (box lo hi) (uinf s c) (Gu s c))
    (q6 : ∀ s c, Tendsto (fun n => eLpNorm (transp (R n) (matterSec (z n) s) c - uinf s c) 2
      (volume.restrict (box lo hi))) atTop (𝓝 0))
    (q8 : ∀ s c μ (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • (tgrad (R n) (matterSec (z n) s) c μ x +
          ∑ e, entries (gaugeConn (R n) (connM (z n).A)) μ c e x *
            transp (R n) (matterSec (z n) s) e x) ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • (Gu s c μ x + ∑ e, Ainf μ c e x * uinf s e x)
          ∂(volume.restrict (box lo hi)))))
    {MF : ℝ≥0∞} (hMF : MF ≠ ⊤)
    (hE : ∀ n, curvEnergy (gaugeConn (R n) (connM (z n).A)) (box lo hi) ≤ MF)
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hQ3c : ∀ n, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM (z n).A) (matterSec (z n) none) μ y e)
      2 (volume.restrict (box lo hi)) ≤ B)
    {Ysec : Type} {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hv : Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH)) :
    WeakL2 (V0 lo hi) (fun n => pk lo hi (fun x => (redJet (gaugeTuple (R n) (z n)) x).F))
        (pk lo hi (fun x => (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x).F)) ∧
      WeakL2 (V0 lo hi) (fun n => pk lo hi (fun x => (redJet (gaugeTuple (R n) (z n)) x).K))
        (pk lo hi (fun x => (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x).K)) ∧
      WeakL2 (V0 lo hi)
        (fun n => pk lo hi (fun x => quartY (θ n) (redJet (gaugeTuple (R n) (z n)) x)))
        (pk lo hi (fun x => quartY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x))) := by
  have hF := weak_F_cube hlh hR (fun n x => (hz n x).A) hWA q1 q4 hMF hE
  have hK := weak_K_cube hlh hR hz hzA hzH hlie hWA hWu q1 q5 q8 hB hQ3c
  obtain ⟨-, hH, -, -, M, hM, hM4⟩ := strong_fields_cube hlh hWA hWu hBu hBu' q1
    (fun ν c e => q2 ν c e) q5 (fun s c => q6 s c)
  have hY := weakL2Data_quart hH hM (fun n => (hM4 n).1) (memLp_four_limit_higgs hlh q5) hv
  exact ⟨weakL2_pk hF, weakL2_pk hK, weakL2_pk hY⟩

end CubePackets


/-! ### Common extraction over finitely many cubes -/

section Common

/-- **Common extraction of the covariance measures on finitely many charts.** -/
theorem exists_common_defects {N : ℕ} {Kc : Fin N → Type*} [∀ j, MetricSpace (Kc j)]
    [∀ j, CompactSpace (Kc j)] [∀ j, MeasurableSpace (Kc j)] [∀ j, BorelSpace (Kc j)]
    (V : ∀ j, Measure (Kc j)) [∀ j, IsFiniteMeasure (V j)]
    {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (Y₁ : ∀ j, ℕ → ι₁ → Kc j → ℝ) (Y₁₀ : ∀ j, ι₁ → Kc j → ℝ)
    (Y₂ : ∀ j, ℕ → ι₂ → Kc j → ℝ) (Y₂₀ : ∀ j, ι₂ → Kc j → ℝ)
    (Y₃ : ∀ j, ℕ → ι₃ → Kc j → ℝ) (Y₃₀ : ∀ j, ι₃ → Kc j → ℝ)
    (h : ∀ j, WeakL2 (V j) (Y₁ j) (Y₁₀ j) ∧ WeakL2 (V j) (Y₂ j) (Y₂₀ j) ∧
      WeakL2 (V j) (Y₃ j) (Y₃₀ j)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, ∃ (Q₁ : StrongDual ℝ C(Kc j, ι₁ → ι₁ → ℝ))
      (Q₂ : StrongDual ℝ C(Kc j, ι₂ → ι₂ → ℝ)) (Q₃ : StrongDual ℝ C(Kc j, ι₃ → ι₃ → ℝ)),
      IsDefect (V j) (fun n => Y₁ j (σ n)) (Y₁₀ j) Q₁ ∧
        IsDefect (V j) (fun n => Y₂ j (σ n)) (Y₂₀ j) Q₂ ∧
        IsDefect (V j) (fun n => Y₃ j (σ n)) (Y₃₀ j) Q₃ := by
  refine exists_common_subseq (fun j σ => ∃ (Q₁ : StrongDual ℝ C(Kc j, ι₁ → ι₁ → ℝ))
      (Q₂ : StrongDual ℝ C(Kc j, ι₂ → ι₂ → ℝ)) (Q₃ : StrongDual ℝ C(Kc j, ι₃ → ι₃ → ℝ)),
      IsDefect (V j) (fun n => Y₁ j (σ n)) (Y₁₀ j) Q₁ ∧
        IsDefect (V j) (fun n => Y₂ j (σ n)) (Y₂₀ j) Q₂ ∧
        IsDefect (V j) (fun n => Y₃ j (σ n)) (Y₃₀ j) Q₃) (fun j σ hσ => ?_) (fun j σ τ hτ hP => ?_)
  · obtain ⟨w1, w2, w3⟩ := h j
    obtain ⟨ψ, hψ, Q₁, Q₂, Q₃, h1, h2, h3⟩ := exists_three_defects (V₀ := V j)
      (Y₁ := fun n => Y₁ j (σ n)) (Y₂ := fun n => Y₂ j (σ n)) (Y₃ := fun n => Y₃ j (σ n))
      (WeakL2.comp w1 hσ) (WeakL2.comp w2 hσ) (WeakL2.comp w3 hσ)
    exact ⟨ψ, hψ, Q₁, Q₂, Q₃, h1, h2, h3⟩
  · obtain ⟨Q₁, Q₂, Q₃, h1, h2, h3⟩ := hP
    exact ⟨Q₁, Q₂, Q₃, isDefect_comp h1 hτ, isDefect_comp h2 hτ, isDefect_comp h3 hτ⟩

end Common

/-! ### Everything on one Coulomb cube -/

section CubeAll

variable {lo hi a b : E4}

set_option maxHeartbeats 2000000 in
/-- **All conclusions on one Coulomb cube**: convergences, matter equations, positivity of the
covariance measures and the metric equation. -/
theorem cube_all {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    (hlh : ∀ i, lo i < hi i) (hQK : box lo hi ⊆ box a b) {z : ℕ → FieldTuple (Fin 5)}
    {R : ℕ → E4 → M5}
    (hzA : ∀ n, ContDiff ℝ ∞ (z n).A) (hzH : ∀ n, ContDiff ℝ ∞ (z n).H)
    (hze : ∀ n, ContDiff ℝ ∞ (z n).e) (hz : ∀ n x, DiffAt (z n) x)
    (hlie : ∀ n x μ, (z n).A x μ ∈ smLie) (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x)
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL)
    (heK : ∀ n, ∀ x ∈ box a b, (z n).e x ∈ Ke)
    {e₀ : E4 → CoframeFibre} {de₀ : Fin 4 → Fin 4 → Fin 4 → E4 → ℝ}
    (he₀ : ∀ i ν, MemLp (fun y => e₀ y i ν) ⊤ (volume.restrict (box a b)))
    (hde₀ : ∀ i ν μ, MemLp (de₀ i ν μ) 2 (volume.restrict (box a b)))
    (hLinf : ∀ i ν, Tendsto (fun k => eLpNorm (fun y => (z k).e y i ν - e₀ y i ν) ⊤
      (volume.restrict (box a b))) atTop (𝓝 0))
    (hL2 : ∀ i ν, Tendsto (fun k => eLpNorm (fun y => (z k).e y i ν - e₀ y i ν) 2
      (volume.restrict (box a b))) atTop (𝓝 0))
    (hd : ∀ i ν μ, Tendsto (fun k => eLpNorm (fun y => pd (fun y => (z k).e y i ν) μ y -
      de₀ i ν μ y) 2 (volume.restrict (box a b))) atTop (𝓝 0))
    (hWA : ∀ n ν c e, MemW12 (box lo hi) (entries (gaugeConn (R n) (connM (z n).A)) ν c e)
      (entryGrad (gaugeConn (R n) (connM (z n).A)) ν c e))
    (hWu : ∀ n s c, MemW12 (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c))
    {Bu : ℝ≥0∞} (hBu : Bu ≠ ⊤)
    (hBu' : ∀ n s c, w12Norm (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c) ≤ Bu)
    {Ainf : Fin 4 → Fin 5 → Fin 5 → E4 → ℂ} {GA : Fin 4 → Fin 5 → Fin 5 → Fin 4 → E4 → ℂ}
    {uinf : MIdx → Fin 5 → E4 → ℂ} {Gu : MIdx → Fin 5 → Fin 4 → E4 → ℂ}
    (q1 : ∀ ν c e, MemW12 (box lo hi) (Ainf ν c e) (GA ν c e))
    (q2 : ∀ ν c e (q : ℝ≥0∞), 1 ≤ q → q < 4 → Tendsto (fun n => eLpNorm
      (entries (gaugeConn (R n) (connM (z n).A)) ν c e - Ainf ν c e) q
      (volume.restrict (box lo hi))) atTop (𝓝 0))
    (q4 : ∀ μ ν c e (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • curvatureW (entries (gaugeConn (R n) (connM (z n).A)))
        (entryGrad (gaugeConn (R n) (connM (z n).A))) μ ν c e x ∂(volume.restrict (box lo hi)))
        atTop (𝓝 (∫ x, w x • curvatureW Ainf GA μ ν c e x ∂(volume.restrict (box lo hi)))))
    (q5 : ∀ s c, MemW12 (box lo hi) (uinf s c) (Gu s c))
    (q6 : ∀ s c (q : ℝ≥0∞), 1 ≤ q → q < 4 → Tendsto (fun n => eLpNorm
      (transp (R n) (matterSec (z n) s) c - uinf s c) q (volume.restrict (box lo hi))) atTop
      (𝓝 0))
    (q7 : ∀ s c μ (w : E4 → ℝ), MemLp w 2 (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • tgrad (R n) (matterSec (z n) s) c μ x
        ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • Gu s c μ x ∂(volume.restrict (box lo hi)))))
    (q8 : ∀ s c μ (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • (tgrad (R n) (matterSec (z n) s) c μ x +
          ∑ e, entries (gaugeConn (R n) (connM (z n).A)) μ c e x *
            transp (R n) (matterSec (z n) s) e x) ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • (Gu s c μ x + ∑ e, Ainf μ c e x * uinf s e x)
          ∂(volume.restrict (box lo hi)))))
    {MF : ℝ≥0∞} (hMF : MF ≠ ⊤)
    (hE : ∀ n, curvEnergy (gaugeConn (R n) (connM (z n).A)) (box lo hi) ≤ MF)
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hQ3c : ∀ n, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM (z n).A) (matterSec (z n) none) μ y e)
      2 (volume.restrict (box lo hi)) ≤ B)
    {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hs : ∀ j, Tendsto (fun n => gaugeScalars (θ n) j) atTop (𝓝 (gaugeScalars θ₀ j)))
    (hl : Tendsto (fun n => (θ n).lambdaH) atTop (𝓝 θ₀.lambdaH))
    (hv : Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH))
    (hk : Tendsto (fun n => (2 * (θ n).kappa)⁻¹) atTop (𝓝 (2 * θ₀.kappa)⁻¹))
    (hΛ : Tendsto (fun n => -(2 * (θ n).Lambda)) atTop (𝓝 (-(2 * θ₀.Lambda))))
    (hm : Tendsto (fun n => mY (θ n)) atTop (𝓝 (mY θ₀)))
    (hzero : ∀ v, IsSetTest (box lo hi) v → Tendsto (fun n => ∫ x in box lo hi,
      fullCov mY (θ n) (redJet (gaugeTuple (R n) (z n)) x) (testJet v x)) atTop (𝓝 0))
    {QF : StrongDual ℝ C(Icc lo hi, PIdx (Fin 4 → ConnFibre) → PIdx (Fin 4 → ConnFibre) → ℝ)}
    {QK : StrongDual ℝ C(Icc lo hi, PIdx (Fin 4 → HiggsFibre) → PIdx (Fin 4 → HiggsFibre) → ℝ)}
    {QY : StrongDual ℝ C(Icc lo hi, PIdx ℝ → PIdx ℝ → ℝ)}
    (dF : IsDefect (V0 lo hi) (fun n => pk lo hi (fun x => (redJet (gaugeTuple (R n) (z n)) x).F))
      (pk lo hi (fun x => (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x).F)) QF)
    (dK : IsDefect (V0 lo hi) (fun n => pk lo hi (fun x => (redJet (gaugeTuple (R n) (z n)) x).K))
      (pk lo hi (fun x => (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x).K)) QK)
    (dY : IsDefect (V0 lo hi)
      (fun n => pk lo hi (fun x => quartY (θ n) (redJet (gaugeTuple (R n) (z n)) x)))
      (pk lo hi (fun x => quartY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x))) QY) :
    CubeConv lo hi (fun n x => redJet (gaugeTuple (R n) (z n)) x)
        (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu)) ∧
      (∀ v, IsSetTest (box lo hi) v → v.e = 0 →
        ∫ x in box lo hi, fullCov mY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x)
          (testJet v x) = 0) ∧
      (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QF P) ∧
      (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QK P) ∧
      (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QY P) ∧
      ∃ (ec : C(Icc lo hi, CoframeFibre)) (hec : ∀ y, ec y ∈ Ke),
        (∀ᵐ y ∂(V0 lo hi), ec y = e₀ y.val) ∧
        ∀ v, IsSetTest (box lo hi) v → ∀ hc : Continuous (testJet v),
          (∫ x in box lo hi, fullCov mY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x)
              (testJet v x)) +
            smDefect QF QK QY θ₀ ec (fun y => hKeGL (hec y))
              ⟨fun y => testJet v y.val, hc.comp continuous_subtype_val⟩ = 0 := by
  have q2' := fun ν c e => q2 ν c e 2 one_le_two (by norm_num)
  have q6' := fun s c => q6 s c 2 one_le_two (by norm_num)
  obtain ⟨w1, w2, w3⟩ := cube_packets_weakL2 hlh hzA hzH hz hlie hR e₀ de₀ hWA hWu hBu hBu' q1 q2'
    q4 q5 q6' q8 hMF hE hB hQ3c hv
  refine ⟨cube_conv hlh hQK hzA hzH hze hz hlie hR hKe hKeGL heK he₀ hde₀ hL2 hd hWA hWu hBu hBu'
      q1 q2 q4 q5 q6 q7 q8 hMF hE hB hQ3c,
    fun v hvT hve => cube_matter_equations mY hlh hQK hzA hzH hze hz hlie hR hKe hKeGL heK he₀ hde₀
      hL2 hd hWA hWu hBu hBu' q1 q2' q4 q5 q6' q7 q8 hMF hE hB hQ3c hs hl hv hk hΛ hm hzero hvT hve,
    fun P hP => isDefect_nonneg_psd w1 dF hP, fun P hP => isDefect_nonneg_psd w2 dK hP,
    fun P hP => isDefect_nonneg_psd w3 dY hP, ?_⟩
  exact cube_einstein_equation mY hlh hQK hzA hzH hze hz hlie hR hKe hKeGL heK he₀ hde₀ hLinf hL2
    hd hWA hWu hBu hBu' q1 q2' q4 q5 q6' q7 q8 hMF hE hB hQ3c hs hl hv hk hΛ hm hzero dF dK dY

end CubeAll

/-! ### The assembled theorem -/

/-- Lower corner of the inner Coulomb cube. -/
def cubeLo (c : E4) (r : ℝ) : E4 := fun i => c i - r / 4

/-- Upper corner of the inner Coulomb cube. -/
def cubeHi (c : E4) (r : ℝ) : E4 := fun i => c i + r / 4

theorem innerCube_eq (c : E4) (r : ℝ) : innerCube c r = box (cubeLo c r) (cubeHi c r) := rfl

set_option maxHeartbeats 8000000 in
/-- **`thm:critical-quotient-defect`, matter and metric equations** (Standard-Model structure group, box rendering of the chart
`K = box a b`, defining-carrier matter).  Hypotheses (Q1)–(Q5): smooth reconstructed fields
`z_h = (e_h, A_h, H_h, Ψ_h, Ψ̄_h)` with `𝔰(𝔲(3) ⊕ 𝔲(2))`-valued connections and coefficient banks
`θ_h` in a compact physical set; coframes with values in a compact subset of the nondegenerate
chart and precompact in `L^∞ ∩ H¹`; bounded and uniformly integrable curvature energy;
gauge-invariant `L²` bounds of the matter sections and of their covariant derivatives; equivariant
consistency and stationarity budgets `c_h + ε_h → 0` with the covariant test size.  Conclusion:
for every compact `K' ⊂ K`, Coulomb cubes covering `K'` with smooth `G_SM`-valued gauges
(`𝔰(𝔲(3) ⊕ 𝔲(2))`-valued Coulomb connections, small `L⁴` norm), one subsequence `Φ` and a limit
bank `θ₀` such that on every cube: the critical convergences (`CubeConv`); the Yang–Mills, Higgs,
Dirac and dual-Dirac equations in distributions; positive semidefinite covariance measures
`𝖰_F, 𝖰_K, 𝖰_Y` of the curvature, covariant Higgs gradient and quartic packets; a continuous
representative `ec` of the limit coframe on the closed cube; and the **metric equation**
`∫_Q Cov_{θ₀}(j L)(j¹ v) + 𝔖(j¹ v) = 0` for every smooth test `v` supported in the cube
(`eq:critical-quotient-einstein` in the first-variation normalisation, `𝔖 = 𝔖_YM + 𝔖_H`). -/
theorem critical_quotient_einstein_SM {Ysec : Type} [Fintype Ysec] (mY : CoefficientBank Ysec → ℂ)
    (hmY : ∃ f : (Fin 7 → ℝ) × (Ysec → Matrix (Fin 3) (Fin 3) ℂ) → ℂ, Continuous f ∧
      ∀ θ, mY θ = f (bankCoords θ))
    {a b : E4} (z : ℕ → FieldTuple (Fin 5))
    (hze : ∀ h, ContDiff ℝ ∞ (z h).e) (hzA : ∀ h, ContDiff ℝ ∞ (z h).A)
    (hzH : ∀ h, ContDiff ℝ ∞ (z h).H) (hzΨ : ∀ h, ContDiff ℝ ∞ (z h).Ψ)
    (hzΨb : ∀ h, ContDiff ℝ ∞ (z h).Ψb) (hlie : ∀ h y μ, (z h).A y μ ∈ smLie)
    (θ : ℕ → CoefficientBank Ysec)
    (hP : ∃ P, IsCompactBankSet P ∧ ∀ h, θ h ∈ P)
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL)
    (heK : ∀ h, ∀ x ∈ box a b, (z h).e x ∈ Ke)
    (hQ1 : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      CoframeLimitH1 (box a b) (fun h => (z h).e) (φ ∘ ψ))
    (hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (connM (z h).A) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (connM (z h).A) x))
    (hQ3 : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h s,
      ∑ e, eLpNorm (fun y => matterSec (z h) s y e) 2 (volume.restrict (box a b)) +
        ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM (z h).A) (matterSec (z h) s) μ y e) 2
          (volume.restrict (box a b)) ≤ B)
    (Dfin : ℕ → FieldTuple (Fin 5) → ℝ) (c ε : ℕ → ℝ)
    (hcons : ∀ h v, IsSetTest (box a b) v →
      |Dfin h v - boxVariation mY (θ h) (box a b) (z h) v| ≤
        c h * (nSize (volume.restrict (box a b)) (z h).A v).toReal)
    (hstat : ∀ h v, IsSetTest (box a b) v →
      |Dfin h v| ≤ ε h * (nSize (volume.restrict (box a b)) (z h).A v).toReal)
    (hce : Tendsto (fun h => c h + ε h) atTop (𝓝 0))
    {K' : Set E4} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → E4) (r : ℝ), 0 < r ∧ (∀ j, eBall (ctr j) r ⊆ box a b) ∧
      (∀ j, innerCube (ctr j) r ⊆ eBall (ctr j) r) ∧ K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → E4 → M5,
        (∀ h j, ∀ y ∈ eBall (ctr j) r, R h j y ∈ GSM) ∧
        (∀ h j c e, ContDiffOn ℝ ∞ (fun y => R h j y c e) (eBall (ctr j) r)) ∧
        (∀ h j, ∀ y ∈ eBall (ctr j) r, ∀ μ,
          Matrix.of.symm (gaugeConn (R h j) (connM (z h).A) μ y) ∈ smLie) ∧
        (∀ h j, ∀ x ∈ innerCube (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (connM (z h).A)) μ c e μ x = 0) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (connM (z h).A)) ν c e) 4
          (volume.restrict (innerCube (ctr j) r)) ≤ η) ∧
        ∃ Φ : ℕ → ℕ, StrictMono Φ ∧ ∃ θ₀ : CoefficientBank Ysec,
          BankTendsto (fun n => θ (Φ n)) θ₀ ∧ ∀ j, ∃ L : LimitFields (Fin 5),
            CubeConv (cubeLo (ctr j) r) (cubeHi (ctr j) r)
              (fun n x => redJet (gaugeTuple (R (Φ n) j) (z (Φ n))) x) (limitJet L) ∧
            (∀ v, IsSetTest (innerCube (ctr j) r) v → v.e = 0 →
              ∫ x in innerCube (ctr j) r, fullCov mY θ₀ (limitJet L x) (testJet v x) = 0) ∧
            ∃ (QF : StrongDual ℝ C(Icc (cubeLo (ctr j) r) (cubeHi (ctr j) r),
                  PIdx (Fin 4 → ConnFibre) → PIdx (Fin 4 → ConnFibre) → ℝ))
              (QK : StrongDual ℝ C(Icc (cubeLo (ctr j) r) (cubeHi (ctr j) r),
                  PIdx (Fin 4 → HiggsFibre) → PIdx (Fin 4 → HiggsFibre) → ℝ))
              (QY : StrongDual ℝ C(Icc (cubeLo (ctr j) r) (cubeHi (ctr j) r),
                  PIdx ℝ → PIdx ℝ → ℝ)),
              IsDefect (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
                (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
                  (fun x => (redJet (gaugeTuple (R (Φ n) j) (z (Φ n))) x).F))
                (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r) (fun x => (limitJet L x).F)) QF ∧
              IsDefect (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
                (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
                  (fun x => (redJet (gaugeTuple (R (Φ n) j) (z (Φ n))) x).K))
                (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r) (fun x => (limitJet L x).K)) QK ∧
              IsDefect (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
                (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
                  (fun x => quartY (θ (Φ n)) (redJet (gaugeTuple (R (Φ n) j) (z (Φ n))) x)))
                (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r) (fun x => quartY θ₀ (limitJet L x)))
                QY ∧
              (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QF P) ∧
              (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QK P) ∧
              (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QY P) ∧
              ∃ (ec : C(Icc (cubeLo (ctr j) r) (cubeHi (ctr j) r), CoframeFibre))
                (hec : ∀ y, ec y ∈ Ke),
                (∀ᵐ y ∂(V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r)), ec y = L.e y.val) ∧
                ∀ v, IsSetTest (innerCube (ctr j) r) v → ∀ hc : Continuous (testJet v),
                  (∫ x in innerCube (ctr j) r, fullCov mY θ₀ (limitJet L x) (testJet v x)) +
                    smDefect QF QK QY θ₀ ec (fun y => hKeGL (hec y))
                      ⟨fun y => testJet v y.val, hc.comp continuous_subtype_val⟩ = 0 := by
  set A : ℕ → MConn 5 := fun h => connM (z h).A
  have hA : ∀ h, IsSmoothUnitaryConn (A h) := fun h => isSmoothUnitaryConn_connM (hzA h) (hlie h)
  have hsm : ∀ h μ y, Matrix.of.symm (A h μ y) ∈ smLie := fun h μ y => hlie h y μ
  have hu : ∀ h s, ContDiff ℝ ∞ (matterSec (z h) s) := fun h s =>
    contDiff_matterSec (hzH h) (hzΨ h) (hzΨb h) s
  obtain ⟨N, ctr, r, hr, hball, hQB, hcover, R, hRG, hRs, hlieC, hdiv, hA4, ⟨BA, hBAt, hAW⟩,
    ⟨Bu, hBut, hUW⟩, φ, hφ, hcf, hQL⟩ :=
    critical_quotient_chart_SM A hA hsm hUI (fun h => matterSec (z h)) hu hQ3
      (fun h => (z h).e) hQ1 (∅ : Set MIdx) (by simp) hK' hK'Q hη
  obtain ⟨P, hPc, hθP⟩ := hP
  obtain ⟨ψ, hψ, θ₀, -, hbank⟩ := bank_extract hPc hθP φ
  obtain ⟨hs, hl, hv, hk, hΛ, hm⟩ := bank_tendsto_all mY hmY ⟨P, hPc, fun n => hθP (φ (ψ n))⟩
    hbank
  obtain ⟨e₀, de₀, he₀, hde₀, hcfl⟩ := hcf.comp hψ
  obtain ⟨M, hM⟩ := hbd
  obtain ⟨B, hBt, hB⟩ := hQ3
  have hz : ∀ n x, DiffAt (z n) x := fun n x =>
    ⟨((hze n).differentiable (by simp)) x, ((hzA n).differentiable (by simp)) x,
      ((hzH n).differentiable (by simp)) x, ((hzΨ n).differentiable (by simp)) x,
      ((hzΨb n).differentiable (by simp)) x⟩
  choose Ainf GA uinf Gu hq using fun j =>
    QuotientLimit.comp (QuotientLimitL4.quotientLimit (hQL j)) hψ
  have hlhj : ∀ j, ∀ i, cubeLo (ctr j) r i < cubeHi (ctr j) r i := fun j i => by
    simp only [cubeLo, cubeHi]; linarith
  have hQKj : ∀ j, box (cubeLo (ctr j) r) (cubeHi (ctr j) r) ⊆ box a b := fun j =>
    (hQB j).trans (hball j)
  have hRj : ∀ j k, ∀ x ∈ box (cubeLo (ctr j) r) (cubeHi (ctr j) r), GaugeAt (R k j) x :=
    fun j k x hx => gaugeAt_of_ball (isOpen_eBall _ _) (hRs _ j) (hRG _ j) (hQB j hx)
  have hEj : ∀ j k, curvEnergy (gaugeConn (R k j) (connM (z k).A))
      (box (cubeLo (ctr j) r) (cubeHi (ctr j) r)) ≤ (M : ℝ≥0∞) := by
    intro j k
    have hopen := isOpen_box (cubeLo (ctr j) r) (cubeHi (ctr j) r)
    rw [curvEnergy_gaugeConn hopen (fun y hy => (hRG _ j y (hQB j hy)).1)
      (fun c e => ((hRs _ j c e).mono (hQB j)).of_le (WithTop.coe_le_coe.mpr le_top)) (hA _)]
    exact (lintegral_mono_set (hQKj j)).trans (hM _)
  have hQ3j : ∀ j k, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM (z k).A)
      (matterSec (z k) none) μ y e) 2
      (volume.restrict (box (cubeLo (ctr j) r) (cubeHi (ctr j) r))) ≤ B :=
    fun j k => (Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun μ _ =>
      eLpNorm_restrict_mono_set (hQKj j)).trans (le_add_left le_rfl |>.trans (hB _ none))
  -- weak packets along `φ ∘ ψ` on every cube
  have hWL : ∀ j, WeakL2 (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
        (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x).F))
        (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x).F)) ∧
      WeakL2 (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
        (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x).K))
        (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x).K)) ∧
      WeakL2 (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
        (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => quartY (θ (φ (ψ n))) (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x)))
        (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => quartY θ₀ (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x))) := by
    intro j
    obtain ⟨q1, q2, -, q4, q5, q6, -, q8⟩ := hq j
    exact cube_packets_weakL2 (z := fun n => z (φ (ψ n))) (R := fun n => R (φ (ψ n)) j)
      (θ := fun n => θ (φ (ψ n))) (hlhj j) (fun n => hzA _) (fun n => hzH _) (fun n => hz _)
      (fun n => hlie _) (fun n => hRj j _) e₀ de₀ (fun n => (hAW _ j · · · |>.1))
      (fun n => (hUW _ j · · |>.1)) hBut (fun n s c => (hUW _ j s c).2) q1
      (fun ν c e => q2 ν c e 2 one_le_two (by norm_num)) q4 q5
      (fun s c => q6 s c 2 one_le_two (by norm_num)) q8 (by simp) (fun n => hEj j _) hBt
      (fun n => hQ3j j _) hv
  -- common extraction of the covariance measures on all cubes
  obtain ⟨σ, hσ, hdef⟩ := exists_common_defects
    (fun j => V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
    (fun j n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x).F))
    (fun j => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x).F))
    (fun j n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x).K))
    (fun j => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x).K))
    (fun j n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => quartY (θ (φ (ψ n))) (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x)))
    (fun j => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => quartY θ₀ (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x)))
    hWL
  have hΦ : StrictMono (fun n => φ (ψ (σ n))) := hφ.comp (hψ.comp hσ)
  have ht := hσ.tendsto_atTop
  refine ⟨N, ctr, r, hr, hball, hQB, hcover, R, hRG, hRs, hlieC, hdiv, hA4,
    fun n => φ (ψ (σ n)), hΦ, θ₀, hbank.comp ht, fun j => ?_⟩
  obtain ⟨q1, q2, -, q4, q5, q6, q7, q8⟩ := hq j
  obtain ⟨QF, QK, QY, dF, dK, dY⟩ := hdef j
  have hWA : ∀ n ν c e, MemW12 (box (cubeLo (ctr j) r) (cubeHi (ctr j) r))
      (entries (gaugeConn (R (φ (ψ (σ n))) j) (connM (z (φ (ψ (σ n)))).A)) ν c e)
      (entryGrad (gaugeConn (R (φ (ψ (σ n))) j) (connM (z (φ (ψ (σ n)))).A)) ν c e) :=
    fun n ν c e => (hAW _ j ν c e).1
  have hWu : ∀ n s c, MemW12 (box (cubeLo (ctr j) r) (cubeHi (ctr j) r))
      (transp (R (φ (ψ (σ n))) j) (matterSec (z (φ (ψ (σ n)))) s) c)
      (tgrad (R (φ (ψ (σ n))) j) (matterSec (z (φ (ψ (σ n)))) s) c) :=
    fun n s c => (hUW _ j s c).1
  have hzero : ∀ v, IsSetTest (box (cubeLo (ctr j) r) (cubeHi (ctr j) r)) v →
      Tendsto (fun n => ∫ x in box (cubeLo (ctr j) r) (cubeHi (ctr j) r),
        fullCov mY (θ (φ (ψ (σ n)))) (redJet (gaugeTuple (R (φ (ψ (σ n))) j)
          (z (φ (ψ (σ n))))) x) (testJet v x)) atTop (𝓝 0) := fun v hv' =>
    budget_pullback_tendsto mY (S := box a b) (B := eBall (ctr j) r) (z := z) (θ := θ)
      (Φ := fun n => φ (ψ (σ n))) (hlhj j) (isOpen_box a b).measurableSet (isOpen_eBall _ _)
      (hQB j) (hQKj j) hz (fun n x hx => hKeGL (heK n x hx)) hΦ
      (R := fun n => R (φ (ψ (σ n))) j) (fun n => hRs _ j) (fun n => hRG _ j) hWA hBAt
      (fun n ν c e => (hAW _ j ν c e).2) Dfin c ε hcons hstat hce hv'
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := cube_all mY (z := fun n => z (φ (ψ (σ n))))
    (R := fun n => R (φ (ψ (σ n))) j) (θ := fun n => θ (φ (ψ (σ n)))) (hlhj j) (hQKj j)
    (fun n => hzA _) (fun n => hzH _) (fun n => hze _) (fun n => hz _) (fun n => hlie _)
    (fun n => hRj j _) hKe hKeGL (fun n => heK _) he₀ hde₀
    (fun i ν => ((hcfl i ν).1).comp ht) (fun i ν => ((hcfl i ν).2.1).comp ht)
    (fun i ν μ => ((hcfl i ν).2.2 μ).comp ht) hWA hWu hBut (fun n s c => (hUW _ j s c).2) q1
    (fun ν c e q h1 h4 => (q2 ν c e q h1 h4).comp ht)
    (fun μ ν c e w hw => (q4 μ ν c e w hw).comp ht) q5
    (fun s c q h1 h4 => (q6 s c q h1 h4).comp ht) (fun s c μ w hw => (q7 s c μ w hw).comp ht)
    (fun s c μ w hw => (q8 s c μ w hw).comp ht) (by simp) (fun n => hEj j _) hBt
    (fun n => hQ3j j _) (fun j' => (hs j').comp ht) (hl.comp ht) (hv.comp ht) (hk.comp ht)
    (hΛ.comp ht) (hm.comp ht) hzero dF dK dY
  exact ⟨limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j), hc1, hc2, QF, QK, QY, dF, dK, dY, hc3, hc4,
    hc5, hc6⟩

end RenewalGeometry.CriticalQuotientRows
