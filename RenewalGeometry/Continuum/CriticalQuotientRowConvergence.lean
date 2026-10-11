/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SMGaugeCovector

/-!
# Passage of the first-variation rows under critical (subcritical-strong, weak-`L²`) convergence
  (`thm:critical-quotient-defect`, `app:critical-quotient-proof`; Einstein–Standard-Model
  action-closure manuscript)

On a chart box `Q`, for a fixed bounded test jet `τ` (the jet of a fixed smooth test), the
complete first-variation covector `fullCov` (gravity first-order representative + Yang–Mills +
Higgs + Dirac–Yukawa on the defining carrier) splits as (`fullCov_split`)

* a **strong part** `gravCovF + potStrongCov + diracStrongField`, which converges in `L¹` when the
  coframes converge in measure inside a compact chart set, `∂e_h → ∂e` in `L²`, the connections,
  Higgs fields and spinors converge in `L²` with uniform `L⁴` bounds on the Higgs and spinor fields
  (`app:critical-quotient-proof`: "the cubic potential force ... and `A_h Ψ̄_hΨ_h`, `H_h Ψ̄_hΨ_h`
  converge strongly in `L¹`"; no strong `L⁴` convergence of `A_h` is used);
* a **weak–strong part** `ymWeakCoeff(F) + higgsWeakCoeff(K) + diracWeakField(∂Ψ, ∂Ψ̄)`, linear in
  the weakly convergent curvature, covariant Higgs gradient and spinor gradients, with
  coefficients converging strongly in `L²` (`D_{A_h}a → D_Aa`, `D_{A_h}η_H → D_Aη_H`, ...);
* the **quadratic metric part** `quadMet` (Yang–Mills and Higgs-kinetic Hilbert stresses and the
  quartic potential through the volume factor), which vanishes on matter tests.

`weak_pairing_tendsto` is the fixed-test weak–strong pairing (dual-basis expansion);
**`cube_rows_tendsto`**: under the critical convergences, `∫_Q (fullCov - quadMet)_h(τ)` converges
to the same expression at the limit jet; `quadMet_matter`: on matter tests the quadratic part
vanishes, so the complete first variation converges along matter tests.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.CriticalQuotientRows

open SobolevOpen EinsteinSM SMGaugeJet FirstVariationCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ### Pairings with a fixed bounded field -/

section Pairing

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- **`L¹`-strong pairing with a fixed bounded field.** -/
theorem strong_pairing_tendsto {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Λ : ℕ → X → V →L[ℝ] ℝ} {Λ₀ : X → V →L[ℝ] ℝ} (hΛ : RenewalGeometry.LpTendsto μ 1 Λ Λ₀)
    {τ : X → V} (hτ : AEStronglyMeasurable τ μ) {C : ℝ} (hC : ∀ x, ‖τ x‖ ≤ C) :
    Tendsto (fun n => ∫ x, Λ n x (τ x) ∂μ) atTop (𝓝 (∫ x, Λ₀ x (τ x) ∂μ)) := by
  have hmem : ∀ {L : X → V →L[ℝ] ℝ}, MemLp L 1 μ → Integrable (fun x => L x (τ x)) μ := by
    intro L hL
    have hm : AEStronglyMeasurable (fun x => L x (τ x)) μ :=
      Continuous.comp_aestronglyMeasurable₂ (g := fun (L : V →L[ℝ] ℝ) (t : V) => L t)
        (by fun_prop) hL.1 hτ
    refine Integrable.mono' ((memLp_one_iff_integrable.mp hL).norm.mul_const C) hm
      (Eventually.of_forall fun x => ?_)
    exact ((L x).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n, ‖∫ x, Λ n x (τ x) ∂μ - ∫ x, Λ₀ x (τ x) ∂μ‖ ≤
      C * (eLpNorm (Λ n - Λ₀) 1 μ).toReal := by
    intro n
    have hd : MemLp (Λ n - Λ₀) 1 μ := (hΛ.memLp n).sub hΛ.memLp_lim
    rw [← integral_sub (hmem (hΛ.memLp n)) (hmem hΛ.memLp_lim)]
    calc ‖∫ x, (Λ n x (τ x) - Λ₀ x (τ x)) ∂μ‖ ≤ ∫ x, ‖(Λ n - Λ₀) x‖ * C ∂μ := by
          refine norm_integral_le_of_norm_le ((memLp_one_iff_integrable.mp hd).norm.mul_const C)
            (Eventually.of_forall fun x => ?_)
          rw [show Λ n x (τ x) - Λ₀ x (τ x) = (Λ n - Λ₀) x (τ x) by simp]
          exact ((Λ n - Λ₀) x).le_opNorm _ |>.trans
            (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))
      _ = C * (eLpNorm (Λ n - Λ₀) 1 μ).toReal := by
          rw [integral_mul_const, mul_comm, eLpNorm_one_eq_lintegral_enorm,
            integral_norm_eq_lintegral_enorm hd.1]
  refine squeeze_zero (fun n => norm_nonneg _) hb ?_
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hΛ.tendsto
  simpa using this.const_mul C

end Pairing

/-- **Weak–strong pairing with a fixed bounded Lipschitz test field** on a box: if `Ω_n → Ω` in
`L²` (operator-valued) and `W_n ⇀ W` weakly in `L²` with a uniform bound, then for a fixed
continuous, bounded, Lipschitz `τ`, `∫ Ω_n(τ)(W_n) → ∫ Ω(τ)(W)` (a special case of the finite-net
lemma `FirstVariationCalculus.uniform_weak_strong_op`, after scaling `τ`). -/
theorem weak_pairing_tendsto {a b : E4} {TV WV : Type*} [NormedAddCommGroup TV]
    [NormedSpace ℝ TV] [FiniteDimensional ℝ TV] [NormedAddCommGroup WV] [NormedSpace ℝ WV]
    [FiniteDimensional ℝ WV]
    {Ω : ℕ → E4 → TV →L[ℝ] WV →L[ℝ] ℝ} {Ω₀ : E4 → TV →L[ℝ] WV →L[ℝ] ℝ}
    (hΩ : RenewalGeometry.LpTendsto (volume.restrict (box a b)) 2 Ω Ω₀)
    {W : ℕ → E4 → WV} {W₀ : E4 → WV} (hW : ∀ n, MemLp (W n) 2 (volume.restrict (box a b)))
    (hW₀ : MemLp W₀ 2 (volume.restrict (box a b))) {B : ℝ}
    (hWB : ∀ n, (eLpNorm (W n) 2 (volume.restrict (box a b))).toReal ≤ B)
    (hweak : WeakL2Tendsto a b W W₀) {τ : E4 → TV} (hτc : Continuous τ) {C L : ℝ}
    (hC : ∀ x, ‖τ x‖ ≤ C) (hL : ∀ x y, ‖τ x - τ y‖ ≤ L * ‖x - y‖) :
    Tendsto (fun n => ∫ x, Ω n x (τ x) (W n x) ∂(volume.restrict (box a b))) atTop
      (𝓝 (∫ x, Ω₀ x (τ x) (W₀ x) ∂(volume.restrict (box a b)))) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set c : ℝ := C + 1
  have hc : 0 < c := by positivity
  set σ : E4 → TV := fun x => c⁻¹ • τ x
  have hσc : Continuous σ := continuous_const.smul hτc
  have hσ1 : ∀ x, ‖σ x‖ ≤ 1 := fun x => by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le, inv_mul_le_iff₀ hc, mul_one]
    exact (hC x).trans (by linarith)
  have hσL : ∀ x y, ‖σ x - σ y‖ ≤ (c⁻¹ * L) * ‖x - y‖ := fun x y => by
    rw [← smul_sub, norm_smul, norm_inv, Real.norm_of_nonneg hc.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hL x y) (inv_nonneg.mpr hc.le)
  have hscale : ∀ (Λ : E4 → TV →L[ℝ] WV →L[ℝ] ℝ) (V : E4 → WV),
      ∫ x, Λ x (τ x) (V x) ∂(volume.restrict (box a b)) =
        c * ∫ x, Λ x (σ x) (V x) ∂(volume.restrict (box a b)) := by
    intro Λ V
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [σ, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (uniform_weak_strong_op hΩ hW hW₀ hWB hweak (c⁻¹ * L)
    (div_pos hε (by positivity : (0 : ℝ) < c + 1)))
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn σ hσc hσ1 hσL
  rw [Real.dist_eq, hscale, hscale, ← mul_sub, abs_mul, abs_of_pos hc]
  calc c * |_| ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left h hc.le
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith

/-! ### The decomposition of the complete covector -/

section Split

variable {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)

/-- **The quadratic metric part** of the bosonic covector: Yang–Mills and Higgs-kinetic Hilbert
stresses (`(F, F)` and `(K, K)` through the metric lift of `k`) and the potential through the
volume factor. -/
def quadMet (θ : CoefficientBank Ysec) (J : RJet (Fin 5)) : RJet (Fin 5) →L[ℝ] ℝ :=
  (∑ j, gaugeScalars θ j • ymMetCoeff j J.e J.F J.F) + higgsMetCoeff J.e J.K J.K +
    θ.lambdaH • potVCoeff J.e ((higgsQuad J.H - θ.vH ^ 2) ^ 2)

/-- The strong part (gravity + Higgs force + strong Dirac part). -/
def strongPart (θ : CoefficientBank Ysec) (J : RJet (Fin 5)) : RJet (Fin 5) →L[ℝ] ℝ :=
  gravCovF θ J.e J.de + potStrongCov θ J.e J.H +
    diracStrongField (defCarrier Ysec mY) θ J.e J.de J.A J.H J.Ψb J.Ψ

/-- **Decomposition of the complete covector** into the strong part, the three weak–strong
pairings and the quadratic metric part. -/
theorem fullCov_split (θ : CoefficientBank Ysec) (J T : RJet (Fin 5)) :
    fullCov mY θ J T = strongPart mY θ J T + ymWeakCoeff θ J.e J.A T J.F +
      higgsWeakCoeff J.e J.H J.A T J.K +
      diracWeakField (defCarrier Ysec mY) J.e J.Ψb J.Ψ (πτ T) (J.dΨ, J.dΨb) +
      quadMet θ J T := by
  have hd := diracCov_eq (defCarrier Ysec mY) θ J T
  simp only [fullCov, strongPart, quadMet, ContinuousLinearMap.add_apply, gravCov, hd,
    bosonCov, ymWeakCoeff, higgsWeakCoeff, potStrongCov, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, flipCov_apply, ContinuousLinearMap.flip_apply, smul_eq_mul,
    Finset.sum_add_distrib, mul_add]
  ring

/-- On matter tests (`k = 0`) the quadratic metric part vanishes. -/
theorem quadMet_matter (θ : CoefficientBank Ysec) (J T : RJet (Fin 5)) (hT : T.e = 0) :
    quadMet θ J T = 0 := by
  simp only [quadMet, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ymMetCoeff, higgsMetCoeff, potVCoeff, mkCov1_apply,
    mkCov2_apply, hT, map_zero, ContinuousLinearMap.zero_apply, smul_eq_mul, mul_zero,
    Finset.sum_const_zero, add_zero, neg_zero]

end Split


/-! ### Convergence of the rows on a box -/

/-- Weak `L²` convergence data on a box: `L²` membership, a uniform bound, weak convergence. -/
def WeakL2Data {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a b : E4)
    (W : ℕ → E4 → V) (W₀ : E4 → V) : Prop :=
  (∀ n, MemLp (W n) 2 (volume.restrict (box a b))) ∧ MemLp W₀ 2 (volume.restrict (box a b)) ∧
    (∃ B : ℝ, ∀ n, (eLpNorm (W n) 2 (volume.restrict (box a b))).toReal ≤ B) ∧
    WeakL2Tendsto a b W W₀

/-- The linear part of the Yukawa coupling of the defining carrier vanishes. -/
theorem yukL_defCarrier {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    (θ : CoefficientBank Ysec) : yukL (defCarrier Ysec mY) θ = 0 := by
  unfold yukL
  rw [show (defCarrier Ysec mY).yukawa θ = AffineMap.const ℝ HiggsFibre (scalarM (mY θ)) from rfl,
    AffineMap.const_linear]
  rfl

/-- **Convergence of the complete first-variation rows on a box** under the critical
convergences.  Hypotheses (on `Q = box a b`): coframes converging in measure inside a compact
chart set and `∂e_h → ∂e` in `L²`; `A_h, H_h, Ψ_h, Ψ̄_h → A, H, Ψ, Ψ̄` strongly in `L²` with uniform
`L⁴` bounds on `H_h, Ψ_h, Ψ̄_h` (no `L⁴` convergence of `A_h`); the curvatures, covariant Higgs
gradients and spinor gradients converging weakly in `L²` with uniform bounds; convergent
couplings.  Then for every continuous, bounded, Lipschitz test jet `τ`,
`∫_Q (fullCov - quadMet)_h(τ) → ∫_Q (fullCov - quadMet)_∞(τ)`. -/
theorem cube_rows_tendsto {Ysec : Type} (mY : CoefficientBank Ysec → ℂ) {a b : E4}
    {Jn : ℕ → E4 → RJet (Fin 5)} {J₀ : E4 → RJet (Fin 5)} {Ke : Set CoframeFibre}
    (hcf : CoframeConv (volume.restrict (box a b)) Ke (fun n x => (Jn n x).e) (fun x => (J₀ x).e))
    (hde : RenewalGeometry.LpTendsto (volume.restrict (box a b)) 2 (fun n x => (Jn n x).de)
      (fun x => (J₀ x).de))
    (hA : RenewalGeometry.LpTendsto (volume.restrict (box a b)) 2 (fun n x => (Jn n x).A)
      (fun x => (J₀ x).A))
    (hH : RenewalGeometry.LpTendsto (volume.restrict (box a b)) 2 (fun n x => (Jn n x).H)
      (fun x => (J₀ x).H))
    (hΨ : RenewalGeometry.LpTendsto (volume.restrict (box a b)) 2 (fun n x => (Jn n x).Ψ)
      (fun x => (J₀ x).Ψ))
    (hΨb : RenewalGeometry.LpTendsto (volume.restrict (box a b)) 2 (fun n x => (Jn n x).Ψb)
      (fun x => (J₀ x).Ψb))
    {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hH4 : ∀ n, eLpNorm (fun x => (Jn n x).H) 4 (volume.restrict (box a b)) ≤ M)
    (hΨ4 : ∀ n, eLpNorm (fun x => (Jn n x).Ψ) 4 (volume.restrict (box a b)) ≤ M)
    (hΨb4 : ∀ n, eLpNorm (fun x => (Jn n x).Ψb) 4 (volume.restrict (box a b)) ≤ M)
    (hF : WeakL2Data a b (fun n x => (Jn n x).F) (fun x => (J₀ x).F))
    (hK : WeakL2Data a b (fun n x => (Jn n x).K) (fun x => (J₀ x).K))
    (hD : WeakL2Data a b (fun n x => ((Jn n x).dΨ, (Jn n x).dΨb))
      (fun x => ((J₀ x).dΨ, (J₀ x).dΨb)))
    {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hs : ∀ j, Tendsto (fun n => gaugeScalars (θ n) j) atTop (𝓝 (gaugeScalars θ₀ j)))
    (hl : Tendsto (fun n => (θ n).lambdaH) atTop (𝓝 θ₀.lambdaH))
    (hv : Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH))
    (hk : Tendsto (fun n => (2 * (θ n).kappa)⁻¹) atTop (𝓝 (2 * θ₀.kappa)⁻¹))
    (hΛ : Tendsto (fun n => -(2 * (θ n).Lambda)) atTop (𝓝 (-(2 * θ₀.Lambda))))
    (hm : Tendsto (fun n => mY (θ n)) atTop (𝓝 (mY θ₀)))
    {τ : E4 → RJet (Fin 5)} (hτc : Continuous τ) {C L : ℝ} (hC : ∀ x, ‖τ x‖ ≤ C)
    (hL : ∀ x y, ‖τ x - τ y‖ ≤ L * ‖x - y‖) :
    (∀ n, Integrable (fun x => fullCov mY (θ n) (Jn n x) (τ x) - quadMet (θ n) (Jn n x) (τ x))
        (volume.restrict (box a b))) ∧
    Integrable (fun x => fullCov mY θ₀ (J₀ x) (τ x) - quadMet θ₀ (J₀ x) (τ x))
        (volume.restrict (box a b)) ∧
    Tendsto (fun n => ∫ x, (fullCov mY (θ n) (Jn n x) (τ x) - quadMet (θ n) (Jn n x) (τ x))
        ∂(volume.restrict (box a b))) atTop
      (𝓝 (∫ x, (fullCov mY θ₀ (J₀ x) (τ x) - quadMet θ₀ (J₀ x) (τ x))
        ∂(volume.restrict (box a b)))) := by
  set μ := volume.restrict (box a b)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (volume_box_ne_top a b)
  -- the strong part converges in `L¹`
  have hY : RenewalGeometry.LpTendsto μ 2
      (fun n x => (((Jn n x).de, (Jn n x).A, (defCarrier Ysec mY).yukawa (θ n) (Jn n x).H, (1 : ℝ)),
        yukL (defCarrier Ysec mY) (θ n)) : ℕ → E4 → PotVar' (defCarrier Ysec mY))
      (fun x => (((J₀ x).de, (J₀ x).A, (defCarrier Ysec mY).yukawa θ₀ (J₀ x).H, (1 : ℝ)), yukL (defCarrier Ysec mY) θ₀)) := by
    have hMc : Tendsto (fun n => ((defCarrier Ysec mY).yukawa (θ n) 0)) atTop (𝓝 ((defCarrier Ysec mY).yukawa θ₀ 0)) := by
      show Tendsto (fun n => scalarM (mY (θ n))) atTop (𝓝 (scalarM (mY θ₀)))
      exact tendsto_pi_nhds.mpr fun c => tendsto_pi_nhds.mpr fun c' => by
        simp only [scalarM]; split_ifs
        · exact hm
        · exact tendsto_const_nhds
    have hMt : RenewalGeometry.LpTendsto μ 2 (fun n x => (defCarrier Ysec mY).yukawa (θ n) (Jn n x).H)
        (fun x => (defCarrier Ysec mY).yukawa θ₀ (J₀ x).H) :=
      (FirstVariationCalculus.LpTendsto.const_seq (μ := μ) (p := 2) hMc).congr
        (fun n => Eventually.of_forall fun x => rfl)
        (Eventually.of_forall fun x => rfl)
    exact LpTendsto.prodMk' (by norm_num) (LpTendsto.prodMk' (by norm_num) hde
      (LpTendsto.prodMk' (by norm_num) hA (LpTendsto.prodMk' (by norm_num) hMt
        (FirstVariationCalculus.LpTendsto.const_seq (tendsto_const_nhds (x := (1 : ℝ)))))))
      (FirstVariationCalculus.LpTendsto.const_seq (μ := μ) (p := 2)
        (by simp only [yukL_defCarrier]; exact tendsto_const_nhds))
  have hdirS := diracStrong_tendsto (defCarrier Ysec mY) hcf hY hΨb hΨ hM hΨb4 hΨ4
  have hgrav := gravCov_tendsto (C := Fin 5) hcf hde hk hΛ
  have hpot := potStrongCov_tendsto (C := Fin 5) hcf hH hM hH4 hl hv
  have hstrong : RenewalGeometry.LpTendsto μ 1 (fun n x => strongPart mY (θ n) (Jn n x))
      (fun x => strongPart mY θ₀ (J₀ x)) :=
    ((hgrav.add hpot).add hdirS).congr (fun n => Eventually.of_forall fun x => rfl)
      (Eventually.of_forall fun x => rfl)
  -- the weak–strong parts
  have hym : RenewalGeometry.LpTendsto μ 2
      (fun n x => ymWeakCoeff (C := Fin 5) (θ n) (Jn n x).e (Jn n x).A)
      (fun x => ymWeakCoeff θ₀ (J₀ x).e (J₀ x).A) := ymWeakCoeff_tendsto hcf hA hs
  have hhig : RenewalGeometry.LpTendsto μ 2
      (fun n x => higgsWeakCoeff (C := Fin 5) (Jn n x).e (Jn n x).H (Jn n x).A)
      (fun x => higgsWeakCoeff (J₀ x).e (J₀ x).H (J₀ x).A) := higgsWeakCoeff_tendsto hcf hH hA
  have hdw := diracWeak_tendsto (defCarrier Ysec mY) hcf hΨb hΨ
  have hπc : Continuous fun x => πτ (τ x) := (πτ (C := Fin 5)).continuous.comp hτc
  have hπb : ∀ x, ‖πτ (τ x)‖ ≤ ‖(πτ (C := Fin 5))‖ * C := fun x =>
    ((πτ (C := Fin 5)).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))
  have hπL : ∀ x y, ‖πτ (τ x) - πτ (τ y)‖ ≤ (‖(πτ (C := Fin 5))‖ * L) * ‖x - y‖ := fun x y => by
    rw [← map_sub, mul_assoc]
    exact ((πτ (C := Fin 5)).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hL x y) (norm_nonneg _))
  obtain ⟨hFm, hF₀, ⟨BF, hBF⟩, hFw⟩ := hF
  obtain ⟨hKm, hK₀, ⟨BK, hBK⟩, hKw⟩ := hK
  obtain ⟨hDm, hD₀, ⟨BD, hBD⟩, hDw⟩ := hD
  have t1 := strong_pairing_tendsto hstrong hτc.aestronglyMeasurable hC
  have t2 := weak_pairing_tendsto hym hFm hF₀ hBF hFw hτc hC hL
  have t3 := weak_pairing_tendsto hhig hKm hK₀ hBK hKw hτc hC hL
  have t4 := weak_pairing_tendsto hdw hDm hD₀ hBD hDw hπc hπb hπL
  -- splitting the integrals
  have hsplit : ∀ (θ' : CoefficientBank Ysec) (J : E4 → RJet (Fin 5)),
      MemLp (fun x => strongPart mY θ' (J x)) 1 μ →
      MemLp (fun x => ymWeakCoeff (C := Fin 5) θ' (J x).e (J x).A) 2 μ → MemLp (fun x => (J x).F) 2 μ →
      MemLp (fun x => higgsWeakCoeff (C := Fin 5) (J x).e (J x).H (J x).A) 2 μ →
      MemLp (fun x => (J x).K) 2 μ →
      MemLp (fun x => diracWeakField (defCarrier Ysec mY) (J x).e (J x).Ψb (J x).Ψ) 2 μ →
      MemLp (fun x => ((J x).dΨ, (J x).dΨb)) 2 μ →
      Integrable (fun x => fullCov mY θ' (J x) (τ x) - quadMet θ' (J x) (τ x)) μ ∧
      ∫ x, (fullCov mY θ' (J x) (τ x) - quadMet θ' (J x) (τ x)) ∂μ =
        ∫ x, strongPart mY θ' (J x) (τ x) ∂μ +
          ∫ x, ymWeakCoeff θ' (J x).e (J x).A (τ x) (J x).F ∂μ +
          ∫ x, higgsWeakCoeff (J x).e (J x).H (J x).A (τ x) (J x).K ∂μ +
          ∫ x, diracWeakField (defCarrier Ysec mY) (J x).e (J x).Ψb (J x).Ψ (πτ (τ x)) ((J x).dΨ, (J x).dΨb) ∂μ := by
    intro θ' J h1 h2 h3 h4 h5 h6 h7
    have i1 := integrable_clm_apply h1 hτc hC
    have i2 := integrable_bilin_apply h2 hτc hC h3
    have i3 := integrable_bilin_apply h4 hτc hC h5
    have i4 := integrable_bilin_apply h6 hπc hπb h7
    have i12 : Integrable (fun x => strongPart mY θ' (J x) (τ x) +
        ymWeakCoeff θ' (J x).e (J x).A (τ x) (J x).F) μ := i1.add i2
    have i123 : Integrable (fun x => strongPart mY θ' (J x) (τ x) +
        ymWeakCoeff θ' (J x).e (J x).A (τ x) (J x).F +
        higgsWeakCoeff (J x).e (J x).H (J x).A (τ x) (J x).K) μ := i12.add i3
    have hpt : (fun x => fullCov mY θ' (J x) (τ x) - quadMet θ' (J x) (τ x)) =
        fun x => strongPart mY θ' (J x) (τ x) + ymWeakCoeff θ' (J x).e (J x).A (τ x) (J x).F +
          higgsWeakCoeff (J x).e (J x).H (J x).A (τ x) (J x).K +
          diracWeakField (defCarrier Ysec mY) (J x).e (J x).Ψb (J x).Ψ (πτ (τ x))
            ((J x).dΨ, (J x).dΨb) := by
      funext x
      simp only [fullCov_split mY θ' (J x) (τ x)]
      ring
    refine ⟨hpt ▸ i123.add i4, ?_⟩
    rw [← integral_add i1 i2, ← integral_add i12 i3, ← integral_add i123 i4, hpt]
  have e1 := fun n => hsplit (θ n) (Jn n) (hstrong.memLp n) (hym.memLp n) (hFm n) (hhig.memLp n)
    (hKm n) (hdw.memLp n) (hDm n)
  have e0 := hsplit θ₀ J₀ hstrong.memLp_lim hym.memLp_lim hF₀ hhig.memLp_lim hK₀ hdw.memLp_lim hD₀
  refine ⟨fun n => (e1 n).1, e0.1, ?_⟩
  simp only [fun n => (e1 n).2, e0.2]
  exact ((t1.add t2).add t3).add t4

end RenewalGeometry.CriticalQuotientRows
