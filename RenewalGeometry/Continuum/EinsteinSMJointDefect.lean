/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMWeakMatterEquations
import RenewalGeometry.Gravity.BosonicStressDefectExact

/-!
# The joint matter-defect Einstein limit
  (`thm:joint-defect`, Einstein–Standard-Model action-closure manuscript)

`BosonicStressDefect.joint_defect_einstein` proves the Einstein clause of `thm:joint-defect` with
the fermionic stress pairing `Ferm_h(k) → FermLim(k)` as an explicit hypothesis.  Here that
hypothesis is **discharged**: the fermionic stress pairing is the complete fermionic metric first
variation of the reconstructed fields (Hilbert convention `⟨T^F_h dV_{g_h}, k⟩ = -2 D𝒮_F(z_h)[k]`,
`eq:stress-definition`), and its convergence to the covector formula at the limit fields is
`diracVariation_weak_tendsto` (the last clause of `prop:weak-matter-equations`, under the compatible
coframe and weak-`H¹` spinor hypotheses).  The conservation clause is composed from
`lem:defect-conservation-transport` exactly as `higgs_defect_conserved`, with the total reconstructed
stress `(T^{YM}_h + T^H_h) dV_{g_h} + 𝖱_h`.

Renderings (as for `thm:higgs-defect` / `prop:YM-defect`): the bosonic stress densities live on a
compact chart `K` with a finite reference measure `V₀` (components of the curvature / covariant
gradient in orthonormal bases, continuous metric fields converging uniformly); the fermionic
first variation lives on the slab box `Q ⊇` time support of the test region `Kc`
(`EinsteinSMWeakMatterEquations.lean`); the test tensor of a physical test `v` on the chart is any
assignment `tens v : Fin 4 → Fin 4 → C(K, ℝ)` (its metric component `k`); the gravitational first
variations `Grav_h(v)` and their intended limit `Ein(v) = ⟨(Ein(g) + Λg)dV_g, k⟩` are given data, the
hypothesis being their convergence (the paper's "convergence of the gravitational first variation").
The bosonic data need not be linked to the fermionic fields: the theorem holds for arbitrary
bosonic data in the hypotheses of `prop:YM-defect` / `thm:higgs-defect`, in particular for those of
the same regulator sequence.

* `joint_defect_einstein_weak` (`eq:joint-defect-Einstein`).
* `joint_defect_conserved` (conservation clause: `𝔖_{YM} + 𝔖_H` is distributionally conserved under
  `C¹` metric convergence, bounded total stress with vanishing tested conservation residual, and the
  Noether identity of the regular limiting stress).
* `joint_defect_weak`: both clauses with a common extraction on a chart `K ⊆ ℝ⁴`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace EinsteinSM

open BosonicStress QuadraticPacketDefect SignedMeasureWeakCompactness BosonicStressDefect

/-! ### Pointwise convergence from dual-norm convergence -/

theorem tendsto_of_dual {V : Type*} [SeminormedAddCommGroup V] {a : ℕ → V → ℝ} {b : V → ℝ}
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v, |a n v - b v| ≤ ε * ‖v‖) (v : V) :
    Tendsto (fun n => a n v) atTop (𝓝 (b v)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h (ε / (‖v‖ + 1)) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  calc |a n v - b v| ≤ ε / (‖v‖ + 1) * ‖v‖ := hN n hn v
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]

/-! ### The Einstein clause -/

section JointEinstein

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κG : Type*} [Fintype κG] [DecidableEq κG]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {Ysec : Type} (FC : FermionCarrier Ysec) {T : ℝ}

/-- The fermionic stress pairing of the reconstructed fields along a test (Hilbert convention):
`⟨T^F_h dV_{g_h}, k⟩ = -2 D𝒮_F(z_h)[v]`. -/
def fermStress (θ : CoefficientBank Ysec) (z : SmoothFields T FC.left) {r : ℕ} {Kc : CylRegion T}
    (v : CrTest FC.left r Kc) : ℝ :=
  -2 * actionVariation T (diracSectorDensity FC θ) z.z (variationDirection z.z v.val)

/-- The intended limit of the fermionic stress pairing: `-2` times the covector formula of the
complete fermionic first variation at the limit fields. -/
def fermStressLim (θ : CoefficientBank Ysec) (Q : ChartBox T) (L : LimitFields FC.C) {r : ℕ}
    {Kc : CylRegion T} (v : CrTest FC.left r Kc) : ℝ :=
  -2 * diracLimitVariation FC θ Q L v

/-- **`thm:joint-defect`, Einstein clause `eq:joint-defect-Einstein`, with the fermionic limit
discharged.**  Assume the Yang–Mills hypotheses of `prop:YM-defect` and the critical Higgs
hypotheses of `thm:higgs-defect` on a compact chart, and the compatible-coframe / weak-`H¹` spinor
hypotheses of `prop:weak-matter-equations` (`WeakMatterConvergence` on the slab box, convergent
Yukawa coefficients) for the reconstructed fields.  After a common extraction the defects
`𝔖_{YM}`, `𝔖_H` exist, and for every Einstein constant `κ > 0`, every test `v` (test tensor
`k = tens v`) along which the gravitational first variation converges to its intended limit and
the operational metric residual
`Grav_h(v)/(2κ) - ½(⟨T^{YM}_h dV, k⟩ + ⟨T^H_h dV, k⟩ + ⟨T^F_h dV, k⟩)` vanishes, with the fermionic
stress pairing `⟨T^F_h dV, k⟩ = -2 D𝒮_F(z_h)[v]` of the reconstructed fields:
`Ein(v) = κ(⟨T^{SM} dV_g, k⟩ + 𝔖_{YM}(k) + 𝔖_H(k))`, where the fermionic part of `T^{SM}` is the
intended limit `-2 D𝒮_F(z)[v]` — no separate stress-convergence assumption is made. -/
theorem joint_defect_einstein_weak
    {g : ℕ → MetricField K} {g₀ : MetricField K} (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {w : ℕ → κG → ℝ} {w₀ : κG → ℝ} (hw : ∀ a, Tendsto (fun h => w h a) atTop (𝓝 (w₀ a)))
    {F : ℕ → Fin 4 → Fin 4 → κG → K → ℝ} {F₀ : Fin 4 → Fin 4 → κG → K → ℝ}
    (hF : WeakL2 V₀ (fun h => Fp (F h)) (Fp F₀))
    {H : ℕ → K → E} {H₀ : K → E} (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C)
    {Y : ℕ → Fin 4 → κ → K → ℝ} {Y₀ : Fin 4 → κ → K → ℝ}
    (hY : WeakL2 V₀ (fun h => Yp (Y h)) (Yp Y₀))
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀))
    {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {Kc : CylRegion T}
    (hK : ∀ p ∈ Kc.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (hr : 1 ≤ r)
    {z : ℕ → SmoothFields T FC.left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields FC.C}
    {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    (tens : CrTest FC.left r Kc → Fin 4 → Fin 4 → C(K, ℝ)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ SYM SH : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ),
      IsYMDefect V₀ g g₀ w w₀ F F₀ σ SYM ∧ IsHiggsDefect V₀ g g₀ lam vH lam₀ vH₀ Y Y₀ H H₀ σ SH ∧
      ∀ (κE : ℝ) (Grav : ℕ → CrTest FC.left r Kc → ℝ) (Ein : CrTest FC.left r Kc → ℝ),
        0 < κE → ∀ v : CrTest FC.left r Kc,
        Tendsto (fun h => Grav h v) atTop (𝓝 (Ein v)) →
        Tendsto (fun h => Grav h v / (2 * κE) - (1 / 2) * (
          (∑ μ, ∑ ν, ∫ x, tens v μ ν x * (ymStress (g h x) (w h) (Fval (F h) x) μ ν *
            vol (g h x)) ∂V₀) +
          (∑ μ, ∑ ν, ∫ x, tens v μ ν x * (higgsStress (g h x) (lam h) (vH h) (Yval (Y h) x)
            (‖H h x‖ ^ 2) μ ν * vol (g h x)) ∂V₀) + fermStress FC (θ h) (z h) v)) atTop (𝓝 0) →
        Ein v = κE * ((∑ μ, ∑ ν, ∫ x, tens v μ ν x *
            (ymStress (g₀ x) w₀ (Fval F₀ x) μ ν * vol (g₀ x)) ∂V₀) +
          (∑ μ, ∑ ν, ∫ x, tens v μ ν x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x)
            (‖H₀ x‖ ^ 2) μ ν * vol (g₀ x)) ∂V₀) +
          fermStressLim FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v +
          pairT SYM (tens v) + pairT SH (tens v)) := by
  obtain ⟨σ, hσ, SYM, SH, hSYM, hSH, -⟩ := joint_defect_einstein (V₀ := V₀) hg hdet hdet₀ hw hF
    hHm hae hL4 hY hlam hvH
  refine ⟨σ, hσ, SYM, SH, hSYM, hSH, fun κE Grav Ein hκ v hGrav hres => ?_⟩
  -- the fermionic stress pairing converges (`prop:weak-matter-equations`)
  have hFerm : Tendsto (fun h => fermStress FC (θ h) (z h) v) atTop
      (𝓝 (fermStressLim FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v)) :=
    (tendsto_of_dual (fun ε hε => diracVariation_weak_tendsto FC h0 h01 h1 hK hr hW hyL hy0 hε)
      v).const_mul (-2)
  set k := tens v
  have hσt := hσ.tendsto_atTop
  have hYM : Tendsto (fun h => ∑ μ, ∑ ν, ∫ x, k μ ν x * (ymStress (g (σ h) x) (w (σ h))
      (Fval (F (σ h)) x) μ ν * vol (g (σ h) x)) ∂V₀) atTop
      (𝓝 (∑ μ, ∑ ν, (∫ x, k μ ν x * (ymStress (g₀ x) w₀ (Fval F₀ x) μ ν * vol (g₀ x)) ∂V₀ +
        SYM μ ν (k μ ν)))) :=
    tendsto_finsetSum _ fun μ _ => tendsto_finsetSum _ fun ν _ => hSYM μ ν (k μ ν)
  have hHg : Tendsto (fun h => ∑ μ, ∑ ν, ∫ x, k μ ν x * (higgsStress (g (σ h) x) (lam (σ h))
      (vH (σ h)) (Yval (Y (σ h)) x) (‖H (σ h) x‖ ^ 2) μ ν * vol (g (σ h) x)) ∂V₀) atTop
      (𝓝 (∑ μ, ∑ ν, (∫ x, k μ ν x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν *
        vol (g₀ x)) ∂V₀ + SH μ ν (k μ ν)))) :=
    tendsto_finsetSum _ fun μ _ => tendsto_finsetSum _ fun ν _ => hSH μ ν (k μ ν)
  have hlim := (hGrav.comp hσt |>.div_const (2 * κE)).sub
    (((hYM.add hHg).add (hFerm.comp hσt)).const_mul (1 / 2))
  have h0' := tendsto_nhds_unique hlim (hres.comp hσt)
  simp only [Finset.sum_add_distrib] at h0'
  unfold pairT
  set A := ∑ μ, ∑ ν, ∫ x, k μ ν x * (ymStress (g₀ x) w₀ (Fval F₀ x) μ ν * vol (g₀ x)) ∂V₀
  set B := ∑ μ, ∑ ν, ∫ x, k μ ν x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν *
    vol (g₀ x)) ∂V₀
  set P := ∑ μ, ∑ ν, SYM μ ν (k μ ν)
  set P' := ∑ μ, ∑ ν, SH μ ν (k μ ν)
  set Fl := fermStressLim FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v
  have e1 : Ein v / (2 * κE) = 1 / 2 * (A + P + (B + P') + Fl) := by linarith
  have e2 : Ein v = 2 * κE * (Ein v / (2 * κE)) := by field_simp
  rw [e2, e1]
  ring

end JointEinstein

/-! ### The conservation clause -/

section JointConservation

open DefectConservationTransport

variable {Ks : Set (Fin 4 → ℝ)} [CompactSpace Ks] {V₀ : Measure Ks} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κG : Type*} [Fintype κG] [DecidableEq κG]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The Yang–Mills stress density `T^{YM} dV_g` is integrable for `L²` curvatures. -/
theorem integrable_ymStress {G : MetricField Ks} (hdet : ∀ x, (mat (G x)).det ≠ 0) (w : κG → ℝ)
    {F : Fin 4 → Fin 4 → κG → Ks → ℝ} (hF : ∀ p, MemLp (Fp F p) 2 V₀) (μ ν : Fin 4) :
    Integrable (fun x => ymStress (G x) w (Fval F x) μ ν * vol (G x)) V₀ :=
  (integrable_qf (ymCoefF G w μ ν) hF).congr
    (Eventually.of_forall fun x => qf_ymCoefF hdet w F μ ν x)

/-- **`thm:joint-defect`, conservation clause**: on a compact chart `K ⊆ ℝ⁴`, along an extraction
carrying the Yang–Mills and Higgs defects, if the metrics converge in `C¹`, the total reconstructed
stress `𝖳_h = (T^{YM}_h + T^H_h) dV_{g_h} + 𝖱_h` (the remaining contributions `𝖱_h` having their
intended regular limits) is uniformly bounded with vanishing tested conservation residual
(`lem:defect-conservation-transport`), then the limiting stress
`T^{SM} dV_g + 𝔖_{YM} + 𝔖_H` is conserved, and if the regular limiting matter stress satisfies its
Noether identity, `𝔖_{YM} + 𝔖_H` is distributionally conserved (tested on `X`). -/
theorem joint_defect_conserved
    {g : ℕ → MetricField Ks} {g₀ : MetricField Ks}
    (gf : ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (gf₀ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (hgf : ∀ h i j, ContDiff ℝ 1 fun x => gf h x i j) (hgf₀ : ∀ i j, ContDiff ℝ 1 fun x => gf₀ x i j)
    (hdetf : ∀ x ∈ Ks, (gf₀ x).det ≠ 0)
    (hC0 : ∀ i j, TendstoUniformlyOn (fun h x => gf h x i j) (fun x => gf₀ x i j) atTop Ks)
    (hC1 : ∀ k i j, TendstoUniformlyOn (fun h => pd k fun x => gf h x i j)
      (pd k fun x => gf₀ x i j) atTop Ks)
    (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {w : ℕ → κG → ℝ} {w₀ : κG → ℝ}
    {F : ℕ → Fin 4 → Fin 4 → κG → Ks → ℝ} {F₀ : Fin 4 → Fin 4 → κG → Ks → ℝ}
    (hF₀ : ∀ p, MemLp (Fp F₀ p) 2 V₀)
    {H : ℕ → Ks → E} {H₀ : Ks → E} (hH₀ : MemLp H₀ 4 V₀)
    {Y : ℕ → Fin 4 → κ → Ks → ℝ} {Y₀ : Fin 4 → κ → Ks → ℝ}
    (hY₀ : ∀ p, MemLp (Yp Y₀ p) 2 V₀)
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {SYM SH : Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ)}
    (hSYM : IsYMDefect V₀ g g₀ w w₀ F F₀ σ SYM)
    (hSH : IsHiggsDefect V₀ g g₀ lam vH lam₀ vH₀ Y Y₀ H H₀ σ SH)
    (R : ℕ → Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ)) (Rlim : Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ))
    (hR : ∀ μ ν φ, Tendsto (fun h => R h μ ν φ) atTop (𝓝 (Rlim μ ν φ)))
    (Tt : ℕ → Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ))
    (hTdef : ∀ h μ ν φ, Tt h μ ν φ =
      ∫ x, φ x * (ymStress (g h x) (w h) (Fval (F h) x) μ ν * vol (g h x)) ∂V₀ +
      ∫ x, φ x * (higgsStress (g h x) (lam h) (vH h) (Yval (Y h) x) (‖H h x‖ ^ 2) μ ν *
        vol (g h x)) ∂V₀ + R h μ ν φ)
    {CT : ℝ} (hT : ∀ h μ ν, ‖Tt h μ ν‖ ≤ CT)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ)
    (htest : Tendsto (fun h => ∑ μ, ∑ ν, Tt h μ ν (covSym Ks (gf h) X μ ν)) atTop (𝓝 0)) :
    let Treg : Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ) := fun μ ν =>
      densityCLM V₀ (fun x => ymStress (g₀ x) w₀ (Fval F₀ x) μ ν * vol (g₀ x)) +
      densityCLM V₀ (fun x => higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν *
        vol (g₀ x)) + Rlim μ ν
    (∑ μ, ∑ ν, (Treg μ ν + (SYM μ ν + SH μ ν)) (covSym Ks gf₀ X μ ν) = 0) ∧
    (∑ μ, ∑ ν, Treg μ ν (covSym Ks gf₀ X μ ν) = 0 →
      ∑ μ, ∑ ν, (SYM μ ν + SH μ ν) (covSym Ks gf₀ X μ ν) = 0) := by
  intro Treg
  have hσt := hσ.tendsto_atTop
  have hlim : ∀ μ ν φ, Tendsto (fun h => Tt (σ h) μ ν φ) atTop
      (𝓝 ((Treg μ ν + (SYM μ ν + SH μ ν)) φ)) := by
    intro μ ν φ
    have hiY := integrable_ymStress (V₀ := V₀) hdet₀ w₀ hF₀ μ ν
    have hiH := integrable_higgsStress (V₀ := V₀) hdet₀ hY₀ hH₀ lam₀ vH₀ μ ν
    have := ((hSYM μ ν φ).add (hSH μ ν φ)).add ((hR μ ν φ).comp hσt)
    refine Tendsto.congr (fun h => (hTdef (σ h) μ ν φ).symm) ?_
    convert this using 2
    · rfl
    · simp only [Treg, ContinuousLinearMap.add_apply, densityCLM_apply V₀ hiY,
        densityCLM_apply V₀ hiH]
      ring
  have hcons := defect_conservation_transport (K := Ks) (g := fun h => gf (σ h)) (g₀ := gf₀)
    (fun h => hgf (σ h)) hgf₀ hdetf
    (fun i j u hu => hσt.eventually (hC0 i j u hu))
    (fun k i j u hu => hσt.eventually (hC1 k i j u hu))
    (fun h => Tt (σ h)) (fun μ ν => Treg μ ν + (SYM μ ν + SH μ ν)) (fun h => hT (σ h)) hlim X
    (htest.comp hσt)
  refine ⟨hcons, fun hN => ?_⟩
  exact defect_conservation_split gf₀ X (fun μ ν => Treg μ ν + (SYM μ ν + SH μ ν)) Treg
    (fun μ ν => SYM μ ν + SH μ ν) (fun μ ν => rfl) hcons hN

end JointConservation

/-! ### Both clauses with a common extraction -/

section JointBoth

open DefectConservationTransport

variable {Ks : Set (Fin 4 → ℝ)} [CompactSpace Ks] {V₀ : Measure Ks} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κG : Type*} [Fintype κG] [DecidableEq κG]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {Ysec : Type} (FC : FermionCarrier Ysec) {T : ℝ}

/-- **`thm:joint-defect`** (both clauses, chart `K ⊆ ℝ⁴`).  Under the Yang–Mills hypotheses of
`prop:YM-defect`, the critical Higgs hypotheses of `thm:higgs-defect` and the compatible-coframe /
weak-`H¹` spinor hypotheses of `prop:weak-matter-equations`, after a common extraction:
(i) the defects `𝔖_{YM}` and `𝔖_H` exist;
(ii) `eq:joint-defect-Einstein` holds along every test whose gravitational first variation
converges and whose operational metric residual vanishes, the fermionic stress being the complete
fermionic metric first variation of the reconstructed fields (no stress-convergence assumption);
(iii) if additionally `g_h → g` in `C¹`, the total reconstructed stress is uniformly bounded with
vanishing tested conservation residual, then `T^{SM} dV_g + 𝔖_{YM} + 𝔖_H` is conserved, and if the
regular limiting stress satisfies its Noether identity, `𝔖_{YM} + 𝔖_H` is distributionally
conserved. -/
theorem joint_defect_weak
    {g : ℕ → MetricField Ks} {g₀ : MetricField Ks} (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {w : ℕ → κG → ℝ} {w₀ : κG → ℝ} (hw : ∀ a, Tendsto (fun h => w h a) atTop (𝓝 (w₀ a)))
    {F : ℕ → Fin 4 → Fin 4 → κG → Ks → ℝ} {F₀ : Fin 4 → Fin 4 → κG → Ks → ℝ}
    (hF : WeakL2 V₀ (fun h => Fp (F h)) (Fp F₀))
    {H : ℕ → Ks → E} {H₀ : Ks → E} (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C)
    {Y : ℕ → Fin 4 → κ → Ks → ℝ} {Y₀ : Fin 4 → κ → Ks → ℝ}
    (hY : WeakL2 V₀ (fun h => Yp (Y h)) (Yp Y₀))
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀))
    {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {Kc : CylRegion T}
    (hK : ∀ p ∈ Kc.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (hr : 1 ≤ r)
    {z : ℕ → SmoothFields T FC.left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields FC.C}
    {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    (tens : CrTest FC.left r Kc → Fin 4 → Fin 4 → C(Ks, ℝ)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ SYM SH : Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ),
      IsYMDefect V₀ g g₀ w w₀ F F₀ σ SYM ∧ IsHiggsDefect V₀ g g₀ lam vH lam₀ vH₀ Y Y₀ H H₀ σ SH ∧
      (∀ (κE : ℝ) (Grav : ℕ → CrTest FC.left r Kc → ℝ) (Ein : CrTest FC.left r Kc → ℝ),
        0 < κE → ∀ v : CrTest FC.left r Kc,
        Tendsto (fun h => Grav h v) atTop (𝓝 (Ein v)) →
        Tendsto (fun h => Grav h v / (2 * κE) - (1 / 2) * (
          (∑ μ, ∑ ν, ∫ x, tens v μ ν x * (ymStress (g h x) (w h) (Fval (F h) x) μ ν *
            vol (g h x)) ∂V₀) +
          (∑ μ, ∑ ν, ∫ x, tens v μ ν x * (higgsStress (g h x) (lam h) (vH h) (Yval (Y h) x)
            (‖H h x‖ ^ 2) μ ν * vol (g h x)) ∂V₀) + fermStress FC (θ h) (z h) v)) atTop (𝓝 0) →
        Ein v = κE * ((∑ μ, ∑ ν, ∫ x, tens v μ ν x *
            (ymStress (g₀ x) w₀ (Fval F₀ x) μ ν * vol (g₀ x)) ∂V₀) +
          (∑ μ, ∑ ν, ∫ x, tens v μ ν x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x)
            (‖H₀ x‖ ^ 2) μ ν * vol (g₀ x)) ∂V₀) +
          fermStressLim FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v +
          pairT SYM (tens v) + pairT SH (tens v))) ∧
      (∀ (gf : ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
        (gf₀ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ),
        (∀ h i j, ContDiff ℝ 1 fun x => gf h x i j) → (∀ i j, ContDiff ℝ 1 fun x => gf₀ x i j) →
        (∀ x ∈ Ks, (gf₀ x).det ≠ 0) →
        (∀ i j, TendstoUniformlyOn (fun h x => gf h x i j) (fun x => gf₀ x i j) atTop Ks) →
        (∀ k i j, TendstoUniformlyOn (fun h => pd k fun x => gf h x i j)
          (pd k fun x => gf₀ x i j) atTop Ks) →
        MemLp H₀ 4 V₀ →
        ∀ (R : ℕ → Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ))
          (Rlim : Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ)),
        (∀ μ ν φ, Tendsto (fun h => R h μ ν φ) atTop (𝓝 (Rlim μ ν φ))) →
        ∀ (Tt : ℕ → Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ)),
        (∀ h μ ν φ, Tt h μ ν φ =
          ∫ x, φ x * (ymStress (g h x) (w h) (Fval (F h) x) μ ν * vol (g h x)) ∂V₀ +
          ∫ x, φ x * (higgsStress (g h x) (lam h) (vH h) (Yval (Y h) x) (‖H h x‖ ^ 2) μ ν *
            vol (g h x)) ∂V₀ + R h μ ν φ) →
        ∀ {CT : ℝ}, (∀ h μ ν, ‖Tt h μ ν‖ ≤ CT) → ∀ (X : (Fin 4 → ℝ) → Fin 4 → ℝ),
        Tendsto (fun h => ∑ μ, ∑ ν, Tt h μ ν (covSym Ks (gf h) X μ ν)) atTop (𝓝 0) →
        let Treg : Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ) := fun μ ν =>
          densityCLM V₀ (fun x => ymStress (g₀ x) w₀ (Fval F₀ x) μ ν * vol (g₀ x)) +
          densityCLM V₀ (fun x => higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν *
            vol (g₀ x)) + Rlim μ ν
        (∑ μ, ∑ ν, (Treg μ ν + (SYM μ ν + SH μ ν)) (covSym Ks gf₀ X μ ν) = 0) ∧
        (∑ μ, ∑ ν, Treg μ ν (covSym Ks gf₀ X μ ν) = 0 →
          ∑ μ, ∑ ν, (SYM μ ν + SH μ ν) (covSym Ks gf₀ X μ ν) = 0)) := by
  obtain ⟨σ, hσ, SYM, SH, hSYM, hSH, hEin⟩ := joint_defect_einstein_weak (V₀ := V₀) FC hg hdet
    hdet₀ hw hF hHm hae hL4 hY hlam hvH h0 h01 h1 hK hr hW hyL hy0 tens
  refine ⟨σ, hσ, SYM, SH, hSYM, hSH, hEin, ?_⟩
  intro gf gf₀ hgf hgf₀ hdetf hC0 hC1 hH₀ R Rlim hR Tt hTdef CT hT X htest
  exact joint_defect_conserved gf gf₀ hgf hgf₀ hdetf hC0 hC1 hdet₀ hF.memLp_lim hH₀ hY.memLp_lim
    hσ hSYM hSH R Rlim hR Tt hTdef hT X htest

end JointBoth

/-! ### Non-vacuity -/

/-- **Non-vacuity of `joint_defect_einstein_weak`**: the complete hypothesis packet is satisfied by
the Minkowski metric with constant bosonic fields on a one-point chart and the flat regulator
(trivial carrier, physical bank) for the fermionic part. -/
example {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {Kc : CylRegion T}
    (hK : ∀ p ∈ Kc.carrier, p.1 ∈ Icc t₀ t₁) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ SYM SH : Fin 4 → Fin 4 → StrongDual ℝ C(Unit, ℝ),
      IsYMDefect (Measure.dirac ()) (fun _ => minkField) minkField (fun _ _ => (1 : ℝ))
        (fun _ : Fin 1 => 1) (fun _ _ _ _ _ => (0 : ℝ)) (fun _ _ _ _ => 0) σ SYM := by
  obtain ⟨σ, hσ, SYM, SH, hSYM, -, -⟩ := joint_defect_einstein_weak (V₀ := Measure.dirac ())
    (E := ℝ) (κG := Fin 1) (κ := Fin 1) (trivialCarrier Unit)
    (g := fun _ => minkField) (g₀ := minkField) tendsto_const_nhds (fun _ => minkField_det)
    minkField_det (w := fun _ _ => (1 : ℝ)) (w₀ := fun _ => 1) (fun _ => tendsto_const_nhds)
    (weakL2_const _ (Fp fun _ _ _ _ => (0 : ℝ))) (H := fun _ _ => (1 : ℝ)) (H₀ := fun _ => 1)
    (fun _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => tendsto_const_nhds)
    (C := 1) (fun _ => by
      refine (eLpNorm_le_of_ae_bound (C := 1) (Eventually.of_forall fun _ => by simp)).trans ?_
      simp)
    (weakL2_const _ (Yp fun _ _ _ => (0 : ℝ))) (lam := fun _ => 1) (vH := fun _ => 0)
    tendsto_const_nhds tendsto_const_nhds h0 h01 h1 hK (r := 4) (by norm_num)
    (flatRegulator_weakMatterConvergence T _) tendsto_const_nhds tendsto_const_nhds
    (fun _ _ _ => 0)
  exact ⟨σ, hσ, SYM, SH, hSYM⟩

end EinsteinSM
end RenewalGeometry
