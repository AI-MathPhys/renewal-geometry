/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientMatterRows
import RenewalGeometry.Continuum.EinsteinSMReducedExtraction

/-!
# `thm:critical-quotient-defect`: the matter Euler equations in the critical gauge quotient
  (Einstein–Standard-Model action-closure manuscript)

**`critical_quotient_matter_SM`** — under the hypotheses (Q1)–(Q5) of `thm:critical-quotient-defect`
(box rendering of the chart `K`, defining-carrier matter, `G_SM = S(U(3) × U(2))`), for every compact
`K' ⊂ K` there are a finite cover of `K'` by Coulomb cubes `Q_j`, cutoff-dependent `G_SM`-valued smooth
gauges `R_{h,j}` (Coulomb, small `L⁴`, `𝔰(𝔲(3) ⊕ 𝔲(2))`-valued Coulomb connections), one subsequence
`Φ` and a limit coefficient bank `θ₀` such that on every cube the gauge-transformed fields converge
to a limit packet `L_j` (`CubeConv`: coframes in measure and `∂e` in `L²`; `A, H, Ψ, Ψ̄` strongly in
every `L^q`, `q < 4`; `F_A`, `D_AH`, `∂Ψ`, `∂Ψ̄` weakly in `L²`), and **the limit packet solves the
Yang–Mills, Higgs, Dirac and dual-Dirac equations in distributions on `Q_j`**:
`∫_{Q_j} Cov_{θ₀}(j L_j)(j¹ v) = 0` for every smooth matter test `v = (0, a, η_H, η, η̄)` supported
in `Q_j` (`a` `𝔰(𝔲(3) ⊕ 𝔲(2))`-valued); `Cov` is the complete first-variation covector (on matter
tests the gravitational part vanishes).  The proof follows `app:critical-quotient-proof`: pull the
fixed test back through the Coulomb gauge (`integral_pullTest`, gauge invariance of the complete
covector `fullCov_gauge`), use the equivariant budgets with the uniformly bounded test size
(`budget_pullback_tendsto`), and pass the rows by weak–strong pairings (`cube_limit_tendsto`).
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

/-- **The convergences of `eq:critical-quotient-convergence` on a cube** `box lo hi`, for jets `Jn`
of the gauge-transformed fields and the limit jet `J₀`. -/
structure CubeConv (lo hi : E4) (Jn : ℕ → E4 → RJet (Fin 5)) (J₀ : E4 → RJet (Fin 5)) : Prop where
  coframe : ∃ Ke : Set CoframeFibre, CoframeConv (volume.restrict (box lo hi)) Ke
    (fun n x => (Jn n x).e) (fun x => (J₀ x).e)
  dcoframe : RenewalGeometry.LpTendsto (volume.restrict (box lo hi)) 2 (fun n x => (Jn n x).de)
    (fun x => (J₀ x).de)
  conn : ∀ q : ℝ≥0∞, 1 ≤ q → q < 4 → Tendsto (fun n => eLpNorm (fun x => (Jn n x).A - (J₀ x).A) q
    (volume.restrict (box lo hi))) atTop (𝓝 0)
  higgs : ∀ q : ℝ≥0∞, 1 ≤ q → q < 4 → Tendsto (fun n => eLpNorm (fun x => (Jn n x).H - (J₀ x).H) q
    (volume.restrict (box lo hi))) atTop (𝓝 0)
  spinor : ∀ q : ℝ≥0∞, 1 ≤ q → q < 4 → Tendsto (fun n => eLpNorm (fun x => (Jn n x).Ψ - (J₀ x).Ψ) q
    (volume.restrict (box lo hi))) atTop (𝓝 0)
  cospinor : ∀ q : ℝ≥0∞, 1 ≤ q → q < 4 → Tendsto (fun n => eLpNorm
    (fun x => (Jn n x).Ψb - (J₀ x).Ψb) q (volume.restrict (box lo hi))) atTop (𝓝 0)
  curv : WeakL2Data lo hi (fun n x => (Jn n x).F) (fun x => (J₀ x).F)
  covHiggs : WeakL2Data lo hi (fun n x => (Jn n x).K) (fun x => (J₀ x).K)
  spinGrad : WeakL2Data lo hi (fun n x => ((Jn n x).dΨ, (Jn n x).dΨb))
    (fun x => ((J₀ x).dΨ, (J₀ x).dΨb))

theorem tendsto_eLpNorm_pi {X ι F : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype ι]
    [NormedAddCommGroup F] {f : ℕ → X → ι → F} {f₀ : X → ι → F} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (hm : ∀ n i, AEStronglyMeasurable (fun x => f n x i - f₀ x i) μ)
    (h : ∀ i, Tendsto (fun n => eLpNorm (fun x => f n x i - f₀ x i) q μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => f n x - f₀ x) q μ) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using tendsto_finset_sum (Finset.univ : Finset ι) fun i _ => h i)
    (fun _ => bot_le) fun n => ?_
  exact eLpNorm_pi_le (f := fun x => f n x - f₀ x) (fun i => hm n i) hq


/-! ### The limit on one Coulomb cube -/

section Cube

variable {lo hi a b : E4} {z : ℕ → FieldTuple (Fin 5)} {R : ℕ → E4 → M5}

/-- **`eq:critical-quotient-convergence` on a Coulomb cube** for the limit packet `limitOf …`. -/
theorem cube_conv (hlh : ∀ i, lo i < hi i) (hQK : box lo hi ⊆ box a b)
    (hzA : ∀ n, ContDiff ℝ ∞ (z n).A) (hzH : ∀ n, ContDiff ℝ ∞ (z n).H)
    (hze : ∀ n, ContDiff ℝ ∞ (z n).e) (hz : ∀ n x, DiffAt (z n) x)
    (hlie : ∀ n x μ, (z n).A x μ ∈ smLie) (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x)
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL)
    (heK : ∀ n, ∀ x ∈ box a b, (z n).e x ∈ Ke)
    {e₀ : E4 → CoframeFibre} {de₀ : Fin 4 → Fin 4 → Fin 4 → E4 → ℝ}
    (he₀ : ∀ i ν, MemLp (fun y => e₀ y i ν) ⊤ (volume.restrict (box a b)))
    (hde₀ : ∀ i ν μ, MemLp (de₀ i ν μ) 2 (volume.restrict (box a b)))
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
      2 (volume.restrict (box lo hi)) ≤ B) :
    CubeConv lo hi (fun n x => redJet (gaugeTuple (R n) (z n)) x)
      (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu)) := by
  set μQ := volume.restrict (box lo hi)
  obtain ⟨hcf, hde⟩ := coframe_cube hQK hze hKe hKeGL heK he₀ hde₀ hL2 (fun i ν μ => hd i ν μ)
  have hmA : ∀ n ν c e, AEStronglyMeasurable (fun x =>
      entries (gaugeConn (R n) (connM (z n).A)) ν c e x - Ainf ν c e x) μQ := fun n ν c e =>
    (hWA n ν c e).memLp.1.sub (q1 ν c e).memLp.1
  have hmu : ∀ n s c, AEStronglyMeasurable (fun x =>
      transp (R n) (matterSec (z n) s) c x - uinf s c x) μQ := fun n s c =>
    (hWu n s c).memLp.1.sub (q5 s c).memLp.1
  have hH : ∀ n x i, (redJet (gaugeTuple (R n) (z n)) x).H i =
      transp (R n) (matterSec (z n) none) (Fin.natAdd 3 i) x := fun n x i => by
    show (gaugeTuple (R n) (z n)).H x i = _
    rw [gaugeTuple_H_eq]; rfl
  refine ⟨⟨Ke, hcf⟩, hde, fun q hq hq4 => ?_, fun q hq hq4 => ?_, fun q hq hq4 => ?_,
    fun q hq hq4 => ?_, weak_F_cube hlh hR (fun n x => (hz n x).A) hWA q1 q4 hMF hE,
    weak_K_cube hlh hR hz hzA hzH hlie hWA hWu q1 q5 q8 hB hQ3c,
    weak_D_cube hR hz hWu hBu hBu' q5 q7⟩
  · exact tendsto_eLpNorm_pi hq (fun n μ => aesm_pi fun c => aesm_pi fun e => hmA n μ c e)
      fun μ => tendsto_eLpNorm_pi hq (fun n c => aesm_pi fun e => hmA n μ c e)
        fun c => tendsto_eLpNorm_pi hq (fun n e => hmA n μ c e) fun e => q2 μ c e q hq hq4
  · refine tendsto_eLpNorm_pi hq (fun n i => (hmu n none (Fin.natAdd 3 i)).congr
      (Eventually.of_forall fun x => by simp only [hH]; rfl)) fun i => ?_
    refine (q6 none (Fin.natAdd 3 i) q hq hq4).congr fun n => ?_
    congr 1; funext x; simp only [Pi.sub_apply, hH]; rfl
  · exact tendsto_eLpNorm_pi hq (fun n s => aesm_pi fun c => hmu n (some (Sum.inl s)) c)
      fun s => tendsto_eLpNorm_pi hq (fun n c => hmu n (some (Sum.inl s)) c)
        fun c => q6 (some (Sum.inl s)) c q hq hq4
  · have hst : ∀ n s c, (fun x => (redJet (gaugeTuple (R n) (z n)) x).Ψb s c -
        (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x).Ψb s c) =
        fun x => star (transp (R n) (matterSec (z n) (some (Sum.inr s))) c x -
          uinf (some (Sum.inr s)) c x) := fun n s c => by
      funext x
      show (gaugeTuple (R n) (z n)).Ψb x s c - star (uinf (some (Sum.inr s)) c x) = _
      rw [gaugeTuple_Ψb_eq, star_sub]
    have hm' : ∀ n s c, AEStronglyMeasurable (fun x => (redJet (gaugeTuple (R n) (z n)) x).Ψb s c -
        (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x).Ψb s c) μQ := fun n s c => by
      rw [hst]; exact Complex.continuous_conj.comp_aestronglyMeasurable (hmu n _ c)
    refine tendsto_eLpNorm_pi hq (fun n s => aesm_pi fun c => hm' n s c) fun s =>
      tendsto_eLpNorm_pi hq (fun n c => hm' n s c) fun c => ?_
    refine (q6 (some (Sum.inr s)) c q hq hq4).congr fun n => ?_
    rw [hst]
    exact (eLpNorm_congr_norm_ae (Eventually.of_forall fun x => norm_star _)).symm

/-- **The distributional Yang–Mills, Higgs, Dirac and dual-Dirac equations on a Coulomb cube**:
if the first variations of the transformed fields along every fixed matter test tend to zero
(the pulled-back equivariant budgets), the limit packet satisfies
`∫_Q Cov_{θ₀}(j L)(j¹ v) = 0` for every matter test `v` (`k = 0`). -/
theorem cube_matter_equations {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    (hlh : ∀ i, lo i < hi i) (hQK : box lo hi ⊆ box a b)
    (hzA : ∀ n, ContDiff ℝ ∞ (z n).A) (hzH : ∀ n, ContDiff ℝ ∞ (z n).H)
    (hze : ∀ n, ContDiff ℝ ∞ (z n).e) (hz : ∀ n x, DiffAt (z n) x)
    (hlie : ∀ n x μ, (z n).A x μ ∈ smLie) (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x)
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL)
    (heK : ∀ n, ∀ x ∈ box a b, (z n).e x ∈ Ke)
    {e₀ : E4 → CoframeFibre} {de₀ : Fin 4 → Fin 4 → Fin 4 → E4 → ℝ}
    (he₀ : ∀ i ν, MemLp (fun y => e₀ y i ν) ⊤ (volume.restrict (box a b)))
    (hde₀ : ∀ i ν μ, MemLp (de₀ i ν μ) 2 (volume.restrict (box a b)))
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
    (q2 : ∀ ν c e, Tendsto (fun n => eLpNorm (entries (gaugeConn (R n) (connM (z n).A)) ν c e -
      Ainf ν c e) 2 (volume.restrict (box lo hi))) atTop (𝓝 0))
    (q4 : ∀ μ ν c e (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • curvatureW (entries (gaugeConn (R n) (connM (z n).A)))
        (entryGrad (gaugeConn (R n) (connM (z n).A))) μ ν c e x ∂(volume.restrict (box lo hi)))
        atTop (𝓝 (∫ x, w x • curvatureW Ainf GA μ ν c e x ∂(volume.restrict (box lo hi)))))
    (q5 : ∀ s c, MemW12 (box lo hi) (uinf s c) (Gu s c))
    (q6 : ∀ s c, Tendsto (fun n => eLpNorm (transp (R n) (matterSec (z n) s) c - uinf s c) 2
      (volume.restrict (box lo hi))) atTop (𝓝 0))
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
    {v : FieldTuple (Fin 5)} (hv0 : IsSetTest (box lo hi) v) (hve : v.e = 0) :
    ∫ x in box lo hi, fullCov mY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x)
      (testJet v x) = 0 := by
  obtain ⟨hτc, ⟨C, hC⟩, L, hL⟩ := testJet_regular hv0
  have hT : ∀ x, (testJet v x).e = 0 := fun x => by simp [testJet, hve]
  have hlim := cube_limit_tendsto mY hlh hQK hzA hzH hze hz hlie hR hKe hKeGL heK he₀ hde₀ hL2 hd
    hWA hWu hBu hBu' q1 q2 q4 q5 q6 q7 q8 hMF hE hB hQ3c hs hl hv hk hΛ hm hτc hC hL |>.2.2
  simp only [quadMet_matter _ _ _ (hT _), sub_zero] at hlim
  exact tendsto_nhds_unique hlim (hzero v hv0)

end Cube


/-! ### The assembled matter clause -/

theorem isSmoothUnitaryConn_connM {A : E4 → ConnFibre} (hA : ContDiff ℝ ∞ A)
    (hlie : ∀ y μ, A y μ ∈ smLie) : IsSmoothUnitaryConn (connM A) := by
  refine ⟨fun μ c e => ?_, fun μ y => ?_⟩
  · exact (contDiff_apply ℝ ℂ e).comp ((contDiff_apply ℝ _ c).comp ((contDiff_apply ℝ _ μ).comp hA))
  · ext i j
    simp only [connM, star_apply, of_apply, Matrix.neg_apply]
    rw [(hlie y μ).1 j i, neg_neg]

theorem gaugeAt_of_ball {R : E4 → M5} {B : Set E4} (hB : IsOpen B)
    (hRs : ∀ c e, ContDiffOn ℝ ∞ (fun y => R y c e) B) (hRG : ∀ y ∈ B, R y ∈ GSM) {x : E4}
    (hx : x ∈ B) : GaugeAt R x :=
  ⟨fun c e => (show ContDiffAt ℝ 2 (fun y => R y c e) x from
    ((hRs c e).contDiffAt (hB.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top)),
    Filter.mem_of_superset (hB.mem_nhds hx) fun y hy => hRG y hy⟩

set_option maxHeartbeats 1000000 in
/-- **`thm:critical-quotient-defect`, the matter Euler equations in the critical gauge quotient**
(Standard-Model structure group, box rendering, defining-carrier matter).  Hypotheses: smooth
reconstructed fields `z_h = (e_h, A_h, H_h, Ψ_h, Ψ̄_h)` on `ℝ⁴` with `𝔰(𝔲(3) ⊕ 𝔲(2))`-valued
connections and coefficient banks `θ_h`; (Q1) banks in a compact physical set, coframes with values
in a compact subset of the nondegenerate chart and precompact in `L^∞ ∩ H¹`; (Q2) bounded and
uniformly integrable curvature energy; (Q3)/(Q4) the gauge-invariant `L²` bounds of the matter
sections and of their covariant derivatives (flat reference connection); (Q5) equivariant
consistency and stationarity budgets `c_h + ε_h → 0` for the complete first variation
`boxVariation` with the covariant test size `nSize` (`eq:equivariant-consistency`,
`eq:equivariant-stationarity`).  Conclusion: Coulomb cubes covering `K'`, smooth `G_SM`-valued
gauges, one subsequence, a limit bank, and on every cube a limit packet with the convergences
`CubeConv` that solves the Yang–Mills, Higgs, Dirac and dual-Dirac equations in distributions. -/
theorem critical_quotient_matter_SM {Ysec : Type} [Fintype Ysec] (mY : CoefficientBank Ysec → ℂ)
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
            CubeConv (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4)
              (fun n x => redJet (gaugeTuple (R (Φ n) j) (z (Φ n))) x) (limitJet L) ∧
            ∀ v, IsSetTest (innerCube (ctr j) r) v → v.e = 0 →
              ∫ x in innerCube (ctr j) r, fullCov mY θ₀ (limitJet L x) (testJet v x) = 0 := by
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
  have hΦ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  obtain ⟨hs, hl, hv, hk, hΛ, hm⟩ := bank_tendsto_all mY hmY ⟨P, hPc, fun n => hθP (φ (ψ n))⟩
    hbank
  obtain ⟨e₀, de₀, he₀, hde₀, hcfl⟩ := hcf.comp hψ
  obtain ⟨M, hM⟩ := hbd
  obtain ⟨B, hBt, hB⟩ := hQ3
  have hz : ∀ n x, DiffAt (z n) x := fun n x =>
    ⟨((hze n).differentiable (by simp)) x, ((hzA n).differentiable (by simp)) x,
      ((hzH n).differentiable (by simp)) x, ((hzΨ n).differentiable (by simp)) x,
      ((hzΨb n).differentiable (by simp)) x⟩
  refine ⟨N, ctr, r, hr, hball, hQB, hcover, R, hRG, hRs, hlieC, hdiv, hA4, φ ∘ ψ, hΦ, θ₀,
    hbank, fun j => ?_⟩
  obtain ⟨Ainf, GA, uinf, Gu, q1, q2, -, q4, q5, q6, q7, q8⟩ :=
    QuotientLimit.comp (QuotientLimitL4.quotientLimit (hQL j)) hψ
  have hcube : innerCube (ctr j) r = box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4) :=
    rfl
  have hlh : ∀ i, (fun i => ctr j i - r / 4) i < (fun i => ctr j i + r / 4) i := fun i => by
    simp only; linarith
  have hQK : box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4) ⊆ box a b :=
    (hQB j).trans (hball j)
  have hRj : ∀ n, ∀ x ∈ box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4),
      GaugeAt (R (φ (ψ n)) j) x := fun n x hx =>
    gaugeAt_of_ball (isOpen_eBall _ _) (hRs _ j) (hRG _ j) (hQB j hx)
  have hE : ∀ n, curvEnergy (gaugeConn (R (φ (ψ n)) j) (connM (z (φ (ψ n))).A))
      (box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4)) ≤ (M : ℝ≥0∞) := by
    intro n
    have hopen := isOpen_box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4)
    rw [curvEnergy_gaugeConn hopen (fun y hy => (hRG _ j y (hQB j hy)).1)
      (fun c e => ((hRs _ j c e).mono (hQB j)).of_le (WithTop.coe_le_coe.mpr le_top)) (hA _)]
    exact (lintegral_mono_set hQK).trans (hM _)
  have hQ3c : ∀ n, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM (z (φ (ψ n))).A)
      (matterSec (z (φ (ψ n))) none) μ y e) 2
      (volume.restrict (box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4))) ≤ B :=
    fun n => (Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun μ _ =>
      eLpNorm_restrict_mono_set hQK).trans (le_add_left le_rfl |>.trans (hB _ none))
  have hWA : ∀ n ν c e, MemW12 (box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4))
      (entries (gaugeConn (R (φ (ψ n)) j) (connM (z (φ (ψ n))).A)) ν c e)
      (entryGrad (gaugeConn (R (φ (ψ n)) j) (connM (z (φ (ψ n))).A)) ν c e) :=
    fun n ν c e => (hAW _ j ν c e).1
  have hWu : ∀ n s c, MemW12 (box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4))
      (transp (R (φ (ψ n)) j) (matterSec (z (φ (ψ n))) s) c)
      (tgrad (R (φ (ψ n)) j) (matterSec (z (φ (ψ n))) s) c) := fun n s c => (hUW _ j s c).1
  refine ⟨limitOf e₀ de₀ Ainf GA uinf Gu, ?_, fun v hvT hve => ?_⟩
  · exact cube_conv (z := fun n => z (φ (ψ n))) (R := fun n => R (φ (ψ n)) j) hlh hQK
      (fun n => hzA _) (fun n => hzH _) (fun n => hze _) (fun n => hz _) (fun n => hlie _)
      hRj hKe hKeGL (fun n => heK _) he₀ hde₀ (fun i ν => (hcfl i ν).2.1)
      (fun i ν μ => (hcfl i ν).2.2 μ) hWA hWu hBut (fun n s c => (hUW _ j s c).2) q1 q2 q4 q5
      q6 q7 q8 (by simp) hE hBt hQ3c
  · have hzero : ∀ v, IsSetTest (box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4)) v →
        Tendsto (fun n => ∫ x in box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4),
          fullCov mY (θ (φ (ψ n))) (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x)
            (testJet v x)) atTop (𝓝 0) := fun v hv =>
      budget_pullback_tendsto mY (S := box a b) (B := eBall (ctr j) r) (z := z) (θ := θ)
        (Φ := φ ∘ ψ) hlh (isOpen_box a b).measurableSet (isOpen_eBall _ _) (hQB j)
        hQK hz (fun n x hx => hKeGL (heK n x hx)) hΦ (R := fun n => R (φ (ψ n)) j)
        (fun n => hRs _ j) (fun n => hRG _ j) hWA hBAt (fun n ν c e => (hAW _ j ν c e).2)
        Dfin c ε hcons hstat hce hv
    exact cube_matter_equations mY (z := fun n => z (φ (ψ n))) (R := fun n => R (φ (ψ n)) j)
      (θ := fun n => θ (φ (ψ n))) hlh hQK (fun n => hzA _) (fun n => hzH _) (fun n => hze _)
      (fun n => hz _) (fun n => hlie _) hRj hKe hKeGL (fun n => heK _) he₀ hde₀
      (fun i ν => (hcfl i ν).2.1) (fun i ν μ => (hcfl i ν).2.2 μ) hWA hWu hBut
      (fun n s c => (hUW _ j s c).2) q1 (fun ν c e => q2 ν c e 2 one_le_two (by norm_num)) q4 q5
      (fun s c => q6 s c 2 one_le_two (by norm_num)) q7 q8 (by simp) hE hBt hQ3c hs hl hv hk hΛ
      hm hzero hvT hve

end RenewalGeometry.CriticalQuotientRows
