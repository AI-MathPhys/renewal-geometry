/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMFermionicContinuity

/-!
# The matter Euler equations survive the bosonic weak limit
  (`prop:weak-matter-equations`, Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMFirstVariationContinuity.lean` / `EinsteinSMFermionicContinuity.lean`:
one slab chart box `Q = (t₀,t₁) × (0,1)³` containing the time support of the test region `K`,
coframes with values a.e. in a fixed compact subset of the (oriented, time-oriented) coframe chart
(the rendering of "`L^∞` with uniformly bounded inverse, in compatible spin frames"), the limit
first variation given by the covector formula evaluated on the limit jet (`smLimitVariation`).

## The weak Yang–Mills / Higgs class (`WeakMatterConvergence`)

Unlike the reduced action topology (`ReducedConvergence`), the curvatures `F_{A_h}` and the
covariant Higgs gradients `D_{A_h}H_h` converge only **weakly** in `L²(Q)` (with their weak limits
identified with `F_A` and `D_AH`), and the Higgs fields converge only **weakly in `H¹(Q)`**;
`A_h → A` in `L⁴(Q)`, `e_h → e` in `H¹(Q)`, `Ψ_h, Ψ̄_h ⇀ Ψ, Ψ̄` weakly in `H¹(Q)`, and the
parameters converge in the physical region.

## Results

* `norm_testJet_sub_le`: for `r ≥ 2` the whole test jet `(k, ∂k, a, ∂a, η_H, ∂η_H, …)` is
  `‖v‖_{C^r}`-Lipschitz; `dual_tendsto_weak_jet`: the finite-net weak–strong pairing in the dual
  test norm, with the full test jet as test value.
* `bosonCov_matter`: on matter tests (`k = 0`) the bosonic covector is
  `ymWeakCoeff(e, A)[T](F) + higgsWeakCoeff(e, H, A)[T](K) + potStrongCov(e, H)[T]` — linear in
  the weakly convergent packets `F`, `K`, with strongly convergent coefficients.
* `higgs_chart_data`: weak `H¹(Q)` convergence gives strong `L²(Q)` convergence (Rellich) and a
  uniform `L⁴(Q)` bound (Sobolev); `cubic_tendsto`: the Higgs force `(|H|²-v²)H` then converges in
  `L¹(Q)` (critical product).
* `bosonMatterVariation_dual_tendsto`: the Yang–Mills + Higgs first variations along matter tests
  converge in the dual norm of `𝒱_K^r` (`r ≥ 2`) under weak curvature / covariant-gradient
  convergence.
* `smMatterVariation_dual_tendsto`: the complete Standard-Model first variation along matter tests
  converges; `diracVariation_weak_tendsto`: the complete fermionic first variation (including the
  metric variation through the spin connection) converges along all tests.
* **`weak_matter_equations`** (`prop:weak-matter-equations`): if first-variation consistency and
  physical stationarity hold for all matter tests along a regulator sequence in the weak class, the
  limiting Yang–Mills, Higgs and Dirac–Yukawa equations hold in distributions
  (`smLimitVariation = 0` on all matter tests), and the complete fermionic metric first variation
  has its intended limit.  `weak_matter_equations_of_regulator` derives the matter hypotheses from
  `FirstVariationConsistent` and `PhysicallyStationary`.
* Non-vacuity: the flat regulator satisfies the complete hypothesis packet.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Lipschitz control of the whole test jet (`r ≥ 2`) -/

section JetLipschitz

variable {T : ℝ} {K : CylRegion T} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_fderiv_fderiv_le_crNorm {f : E4 → F} (hf : IsCylTest K f) {r : ℕ} (hr : 2 ≤ r)
    (x : E4) : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ crNorm r f := by
  refine le_trans ?_ (iSup_le_crNorm hf hr)
  rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), norm_iteratedFDeriv_fderiv]
  exact le_ciSup (hf.bddAbove_norm_iteratedFDeriv 2) x

/-- The derivative of a test section is `‖f‖_{C^r}`-Lipschitz (`r ≥ 2`). -/
theorem norm_fderiv_sub_le_crNorm {f : E4 → F} (hf : IsCylTest K f) {r : ℕ} (hr : 2 ≤ r)
    (x y : E4) : ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ crNorm r f * ‖x - y‖ :=
  convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ((hf.smooth.fderiv_right (m := 1) (by norm_cast)).differentiable
      one_ne_zero) z)
    (fun z _ => norm_fderiv_fderiv_le_crNorm hf hr z) (mem_univ y) (mem_univ x)

theorem norm_pd_sub_le_crNorm {f : E4 → F} (hf : IsCylTest K f) {r : ℕ} (hr : 2 ≤ r)
    (i : Fin 4) (x y : E4) : ‖pd f i x - pd f i y‖ ≤ crNorm r f * ‖x - y‖ := by
  unfold pd
  rw [← sub_apply]
  refine ((fderiv ℝ f x - fderiv ℝ f y).le_opNorm _).trans ?_
  refine (mul_le_mul_of_nonneg_left (norm_single_E4_le i) (norm_nonneg _)).trans ?_
  rw [mul_one]
  exact norm_fderiv_sub_le_crNorm hf hr x y

theorem norm_pd_family_sub_le {f : E4 → F} (hf : IsCylTest K f) {r : ℕ} (hr : 2 ≤ r)
    {c : ℝ} (hc : crNorm r f ≤ c) (x y : E4) :
    ‖(fun i => pd f i x) - (fun i => pd f i y)‖ ≤ c * ‖x - y‖ :=
  (pi_norm_le_iff_of_nonneg (mul_nonneg ((crNorm_nonneg r f).trans hc) (norm_nonneg _))).mpr
    fun i =>
    (norm_pd_sub_le_crNorm hf hr i x y).trans
      (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

theorem norm_sub_le_of_crNorm {f : E4 → F} (hf : IsCylTest K f) {r : ℕ} (hr : 2 ≤ r)
    {c : ℝ} (hc : crNorm r f ≤ c) (x y : E4) : ‖f x - f y‖ ≤ c * ‖x - y‖ :=
  (norm_sub_le_crNorm hf (by omega) x y).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

variable {C : Type} [Fintype C] {left : C → Bool} {r : ℕ}

/-- **The whole test jet is `‖v‖_{C^r}`-Lipschitz** for `r ≥ 2`. -/
theorem norm_testJet_sub_le (hr : 2 ≤ r) (v : CrTest left r K) (x y : E4) :
    ‖testJet v.val x - testJet v.val y‖ ≤ ‖v‖ * ‖x - y‖ := by
  have ke := isCylTest_e v; have kA := isCylTest_A v; have kH := isCylTest_H v
  have kΨ := isCylTest_Ψ v; have kΨb := isCylTest_Ψb v
  simp only [testJet, RJet.mk, Prod.mk_sub_mk, norm_prod_le_iff]
  exact ⟨norm_sub_le_of_crNorm ke hr (crNorm_e_le v) x y,
    norm_pd_family_sub_le ke hr (crNorm_e_le v) x y,
    norm_sub_le_of_crNorm kA hr (crNorm_A_le v) x y,
    norm_pd_family_sub_le kA hr (crNorm_A_le v) x y,
    norm_sub_le_of_crNorm kH hr (crNorm_H_le v) x y,
    norm_pd_family_sub_le kH hr (crNorm_H_le v) x y,
    norm_sub_le_of_crNorm kΨ hr (crNorm_Ψ_le v) x y,
    norm_pd_family_sub_le kΨ hr (crNorm_Ψ_le v) x y,
    norm_sub_le_of_crNorm kΨb hr (crNorm_Ψb_le v) x y,
    norm_pd_family_sub_le kΨb hr (crNorm_Ψb_le v) x y⟩

end JetLipschitz

/-! ### Weak–strong pairings with the full test jet -/

section DualJet

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool} {r : ℕ} {K : CylRegion T}
variable {WV : Type*} [NormedAddCommGroup WV] [NormedSpace ℝ WV] [FiniteDimensional ℝ WV]

/-- **Dual-norm convergence of weak–strong pairings with the full test jet** (`r ≥ 2`): if
`Ω_n → Ω` in `L²(Q)` (operator norm) and `W_n ⇀ W` weakly in `L²(Q)` with a uniform bound, then
`v ↦ ∫_Q Ω_n(j¹v)(W_n)` converges in the dual norm of `𝒱_K^r` (finite-net argument,
`uniform_weak_strong_op`, the jet being `‖v‖`-Lipschitz by `norm_testJet_sub_le`). -/
theorem dual_tendsto_weak_jet (hr : 2 ≤ r) (Q : ChartBox T)
    {Ω : ℕ → E4 → RJet C →L[ℝ] WV →L[ℝ] ℝ} {Ω₀ : E4 → RJet C →L[ℝ] WV →L[ℝ] ℝ}
    (hΩ : RenewalGeometry.LpTendsto Q.μ 2 Ω Ω₀) {W : ℕ → E4 → WV} {W₀ : E4 → WV}
    (hW : ∀ n, MemLp (W n) 2 Q.μ) (hW₀ : MemLp W₀ 2 Q.μ) {B : ℝ}
    (hWB : ∀ n, (eLpNorm (W n) 2 Q.μ).toReal ≤ B)
    (hweak : FirstVariationCalculus.WeakL2Tendsto Q.a Q.b W W₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest left r K,
      |(∫ x in Q.set, Ω n x (testJet v.val x) (W n x)) -
        ∫ x in Q.set, Ω₀ x (testJet v.val x) (W₀ x)| ≤ ε * ‖v‖ := by
  filter_upwards [FirstVariationCalculus.uniform_weak_strong_op hΩ hW hW₀ hWB hweak 1 hε]
    with n hn v
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · have h' : ∀ x, testJet v.val x = 0 := fun x =>
      norm_le_zero_iff.mp ((norm_testJet_le (by omega) v x).trans h0.symm.le)
    simp [h', ← h0]
  · have hτc : Continuous fun x => ‖v‖⁻¹ • testJet v.val x := by
      have := continuous_testJet v
      fun_prop
    have hτ1 : ∀ x, ‖‖v‖⁻¹ • testJet v.val x‖ ≤ 1 := fun x => by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hpos, mul_one]
      exact norm_testJet_le (by omega) v x
    have hτL : ∀ x y, ‖‖v‖⁻¹ • testJet v.val x - ‖v‖⁻¹ • testJet v.val y‖ ≤ 1 * ‖x - y‖ :=
      fun x y => by
      rw [← smul_sub, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hpos, one_mul]
      exact norm_testJet_sub_le hr v x y
    have h2 := hn _ hτc hτ1 hτL
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, integral_const_mul,
      ← mul_sub, abs_mul, abs_inv, abs_norm] at h2
    rw [inv_mul_le_iff₀ hpos, mul_comm] at h2
    simpa only [ChartBox.set] using h2

end DualJet

/-! ### The bosonic covector along matter tests -/

section MatterCovector

variable {C : Type} [Fintype C]

/-- Flipping the arguments of covector-valued maps, as a continuous linear map. -/
def flipCov (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (C : Type) [Fintype C] :
    (V →L[ℝ] RJet C →L[ℝ] ℝ) →L[ℝ] (RJet C →L[ℝ] V →L[ℝ] ℝ) :=
  (ContinuousLinearMap.flipₗᵢ ℝ V (RJet C) ℝ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem flipCov_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] RJet C →L[ℝ] ℝ) : flipCov V C L = L.flip := rfl

/-- The Yang–Mills gauge-variation coefficient, paired with the curvature:
`T ↦ F ↦ Σ_j g_j^{-2}(DYM_j(e)[∂a](F) + DYM_j(e)[[A,a]](F))` (both slots of the quadratic
form). -/
def ymWeakCoeff {Y : Type} (θ : CoefficientBank Y) (e : CoframeFibre) (A : ConnFibre) :
    RJet C →L[ℝ] (Fin 4 → ConnFibre) →L[ℝ] ℝ :=
  flipCov _ C (∑ j, gaugeScalars θ j • (ymDaCoeff j e + ymACoeff j e A))

/-- The Higgs-kinetic matter-variation coefficient, paired with the covariant gradient:
`T ↦ K ↦ Dh(e)[∂η + ρ_H(a)H + ρ_H(A)η](K)`. -/
def higgsWeakCoeff (e : CoframeFibre) (H : HiggsFibre) (A : ConnFibre) :
    RJet C →L[ℝ] (Fin 4 → HiggsFibre) →L[ℝ] ℝ :=
  flipCov _ C (higgsDCoeff e + higgsHCoeff e H + higgsACoeff e A)

/-- The Higgs force `T ↦ -2λ_H(|H|²-v_H²)(Re⟨η,H⟩ + Re⟨H,η⟩)√|g|`. -/
def potStrongCov {Y : Type} (θ : CoefficientBank Y) (e : CoframeFibre) (H : HiggsFibre) :
    RJet C →L[ℝ] ℝ :=
  θ.lambdaH • potHCoeff e ((higgsQuad H - θ.vH ^ 2) • H)

/-- **The bosonic covector along matter tests** (`T.e = 0`, i.e. `k = 0`): the metric terms
drop out and the covector is linear in the curvature and covariant-gradient packets. -/
theorem bosonCov_matter {Y : Type} (θ : CoefficientBank Y) (R T : RJet C) (hT : T.e = 0) :
    bosonCov θ R T = ymWeakCoeff θ R.e R.A T R.F + higgsWeakCoeff R.e R.H R.A T R.K +
      potStrongCov θ R.e R.H T := by
  simp only [bosonCov, ymWeakCoeff, higgsWeakCoeff, potStrongCov, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, flipCov_apply,
    ContinuousLinearMap.flip_apply, ymMetCoeff, higgsMetCoeff, potVCoeff, mkCov1_apply,
    mkCov2_apply, hT, map_zero, ContinuousLinearMap.zero_apply, mul_zero, neg_zero, add_zero,
    zero_add, smul_eq_mul]

end MatterCovector

/-! ### Strong convergence of the matter coefficients -/

section MatterCoeffConvergence

variable {C : Type} [Fintype C] {X : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsFiniteMeasure μ]

open FirstVariationCalculus

/-- Coefficients depending continuously on the coframe converge in every `L^p`, `p < ∞`. -/
theorem CoframeConv.coeff {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (h : CoframeConv μ Ke e e₀) {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] {Ψ : CoframeFibre → W}
    (hΨ : ContinuousOn Ψ coframeGL) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    RenewalGeometry.LpTendsto μ p (fun n x => Ψ (e n x)) (fun x => Ψ (e₀ x)) := by
  have hc : ContinuousOn (fun e => (ContinuousLinearMap.toSpanSingletonCLE (Ψ e) : ℝ →L[ℝ] W))
      coframeGL :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := W)).continuous.comp_continuousOn hΨ
  have := h.apply hc hp (LpTendsto.const_seq (μ := μ) (p := p) (X := X)
    (tendsto_const_nhds (x := (1 : ℝ))))
  refine this.congr (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · simp
  · simp

/-- **`L²` convergence of the Yang–Mills matter coefficient** (`A_h → A` in `L²`). -/
theorem ymWeakCoeff_tendsto {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (he : CoframeConv μ Ke e e₀) {A : ℕ → X → ConnFibre}
    {A₀ : X → ConnFibre} (hA : RenewalGeometry.LpTendsto μ 2 A A₀) {Y : Type}
    {θ : ℕ → CoefficientBank Y} {θ₀ : CoefficientBank Y}
    (hs : ∀ j, Tendsto (fun n => gaugeScalars (θ n) j) atTop (𝓝 (gaugeScalars θ₀ j))) :
    RenewalGeometry.LpTendsto μ 2 (fun n x => ymWeakCoeff (C := C) (θ n) (e n x) (A n x))
      (fun x => ymWeakCoeff (θ₀) (e₀ x) (A₀ x)) := by
  have h := LpTendsto.finset_sum (μ := μ) (p := 2) Finset.univ fun j _ =>
    LpTendsto.smul_seq (hs j)
      ((he.coeff (W := (Fin 4 → ConnFibre) →L[ℝ] RJet C →L[ℝ] ℝ) (continuousOn_ymDaCoeff j)
        (p := 2) (by norm_num)).add
      (he.apply (W := (Fin 4 → ConnFibre) →L[ℝ] RJet C →L[ℝ] ℝ) (continuousOn_ymACoeff j)
        (p := 2) (by norm_num) hA))
  exact (LpTendsto.clm_comp (by norm_num) (flipCov _ C) h).congr
    (fun n => Eventually.of_forall fun x => rfl) (Eventually.of_forall fun x => rfl)

/-- **`L²` convergence of the Higgs matter coefficient** (`H_h → H`, `A_h → A` in `L²`). -/
theorem higgsWeakCoeff_tendsto {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (he : CoframeConv μ Ke e e₀) {H : ℕ → X → HiggsFibre}
    {H₀ : X → HiggsFibre} (hH : RenewalGeometry.LpTendsto μ 2 H H₀) {A : ℕ → X → ConnFibre}
    {A₀ : X → ConnFibre} (hA : RenewalGeometry.LpTendsto μ 2 A A₀) :
    RenewalGeometry.LpTendsto μ 2 (fun n x => higgsWeakCoeff (C := C) (e n x) (H n x) (A n x))
      (fun x => higgsWeakCoeff (e₀ x) (H₀ x) (A₀ x)) := by
  have h := ((he.coeff (W := (Fin 4 → HiggsFibre) →L[ℝ] RJet C →L[ℝ] ℝ)
    continuousOn_higgsDCoeff (p := 2) (by norm_num)).add
    (he.apply (W := (Fin 4 → HiggsFibre) →L[ℝ] RJet C →L[ℝ] ℝ) continuousOn_higgsHCoeff
      (p := 2) (by norm_num) hH)).add
    (he.apply (W := (Fin 4 → HiggsFibre) →L[ℝ] RJet C →L[ℝ] ℝ) continuousOn_higgsACoeff
      (p := 2) (by norm_num) hA)
  exact (LpTendsto.clm_comp (by norm_num) (flipCov _ C) h).congr
    (fun n => Eventually.of_forall fun x => rfl) (Eventually.of_forall fun x => rfl)

/-- The trilinear map `(a, b, c) ↦ Re⟨a, b⟩ c` on the Higgs fibre. -/
def cubicTrilin : HiggsFibre →L[ℝ] HiggsFibre →L[ℝ] HiggsFibre →L[ℝ] HiggsFibre :=
  (ContinuousLinearMap.compL ℝ HiggsFibre ℝ (HiggsFibre →L[ℝ] HiggsFibre)
    (ContinuousLinearMap.lsmul ℝ ℝ)).comp hInnerReL

theorem cubicTrilin_apply (a b c : HiggsFibre) : cubicTrilin a b c = hInnerReL a b • c := rfl

/-- **The Higgs force converges in `L¹`** from strong `L²` convergence with a uniform `L⁴` bound
(the critical product `L² × L⁴ × L⁴ → L¹`), and convergent couplings. -/
theorem potStrongCov_tendsto {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (he : CoframeConv μ Ke e e₀) {H : ℕ → X → HiggsFibre}
    {H₀ : X → HiggsFibre} (hH : RenewalGeometry.LpTendsto μ 2 H H₀) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hH4 : ∀ n, eLpNorm (H n) 4 μ ≤ M) {Y : Type} {θ : ℕ → CoefficientBank Y}
    {θ₀ : CoefficientBank Y} (hl : Tendsto (fun n => (θ n).lambdaH) atTop (𝓝 θ₀.lambdaH))
    (hv : Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH)) :
    RenewalGeometry.LpTendsto μ 1 (fun n x => potStrongCov (C := C) (θ n) (e n x) (H n x))
      (fun x => potStrongCov θ₀ (e₀ x) (H₀ x)) := by
  have hcub := tendsto_trilin_critical cubicTrilin hH hH hH hM hH4 hH4
  have hlin : RenewalGeometry.LpTendsto μ 1 (fun n x => (θ n).vH ^ 2 • H n x)
      (fun x => θ₀.vH ^ 2 • H₀ x) :=
    (LpTendsto.smul_seq (hv.pow 2) hH).mono (by norm_num) (by norm_num)
  have hY : RenewalGeometry.LpTendsto μ 1 (fun n x => (higgsQuad (H n x) - (θ n).vH ^ 2) • H n x)
      (fun x => (higgsQuad (H₀ x) - θ₀.vH ^ 2) • H₀ x) :=
    (hcub.sub hlin).congr (fun n => Eventually.of_forall fun x => by
      simp [cubicTrilin_apply, higgsQuad, sub_smul])
      (Eventually.of_forall fun x => by simp [cubicTrilin_apply, higgsQuad, sub_smul])
  exact LpTendsto.smul_seq hl (he.apply (continuousOn_potHCoeff (C := C)) (p := 1) (by norm_num) hY)

end MatterCoeffConvergence

/-! ### Weak `H¹` data on a chart box -/

section WeakH1Chart

variable {T : ℝ} {ι : Type} [Fintype ι]

theorem w12Norm_le_of_h1' (Q : ChartBox T) {u : E4 → ι → ℂ} {g : E4 → Fin 4 → ι → ℂ} (p : ι) :
    SobolevOpen.w12Norm Q.set (fun x => u x p) (fun i x => g x i p) ≤
      h1Norm Q u g + 4 * h1Norm Q u g := by
  unfold SobolevOpen.w12Norm h1Norm
  gcongr
  · exact (eLpNorm_apply_le u p 2).trans le_self_add
  · calc ∑ i, eLpNorm (fun x => g x i p) 2 Q.μ ≤ ∑ _i : Fin 4, (eLpNorm u 2 Q.μ + eLpNorm g 2 Q.μ) :=
          Finset.sum_le_sum fun i _ => ((eLpNorm_apply_le (fun x => g x i) p 2).trans
            (eLpNorm_apply_le g i 2)).trans le_add_self
      _ = 4 * (eLpNorm u 2 Q.μ + eLpNorm g 2 Q.μ) := by simp [mul_add]

/-- **Weak `H¹(Q)` convergence on a chart box** gives strong `L²(Q)` convergence (Rellich,
componentwise) and a uniform `L⁴(Q)` bound (the critical Sobolev embedding `H¹ ⊂ L⁴` in four
dimensions). -/
theorem weakH1_chart_data (Q : ChartBox T) {u : ℕ → E4 → ι → ℂ} {g : ℕ → E4 → Fin 4 → ι → ℂ}
    {u₀ : E4 → ι → ℂ} {g₀ : E4 → Fin 4 → ι → ℂ} (hw : WeakH1Tendsto Q u g u₀ g₀) :
    RenewalGeometry.LpTendsto Q.μ 2 u u₀ ∧
      ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n, eLpNorm (u n) 4 Q.μ ≤ M := by
  obtain ⟨hmem, hmem₀, ⟨B, hBt, hB⟩, hpair, -⟩ := hw
  set B' := B + 4 * B with hB'
  have hB't : B' ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hBt, ENNReal.mul_ne_top (by simp) hBt⟩
  have hw12 : ∀ n p, SobolevOpen.w12Norm Q.set (fun x => u n x p) (fun i x => g n x i p) ≤ B' :=
    fun n p => (w12Norm_le_of_h1' Q (u := u n) p).trans
      (add_le_add (hB n) (by gcongr; exact hB n))
  have hL2c : ∀ p : ι, Tendsto (fun n => eLpNorm (fun x => u n x p - u₀ x p) 2 Q.μ) atTop
      (𝓝 0) := fun p =>
    SobolevOpen.tendsto_L2_box_of_weak Q.lt (fun n x => u n x p) (fun n i x => g n x i p)
      (fun x => u₀ x p) (fun n => hmem n p) hB't (fun n => hw12 n p) (hmem₀ p).memLp
      (fun φ hφ => hpair φ hφ p)
  have hmemC : ∀ n, MemLp (u n) 2 Q.μ := fun n => memLp_pi_iff.mpr fun p => (hmem n p).memLp
  have hmemC₀ : MemLp u₀ 2 Q.μ := memLp_pi_iff.mpr fun p => (hmem₀ p).memLp
  refine ⟨⟨hmemC, hmemC₀, tendsto_eLpNorm_of_apply (by norm_num)
    (fun n p => ((hmem n p).memLp.1.sub (hmem₀ p).memLp.1)) hL2c⟩, ?_⟩
  obtain ⟨Cs, hCs⟩ := SobolevOpen.exists_sobolev_L4_box (ι := Fin 4) (by simp) Q.lt
  refine ⟨∑ _p : ι, (Cs : ℝ≥0∞) * B', ENNReal.sum_ne_top.mpr fun _ _ =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top hB't, fun n => ?_⟩
  refine (eLpNorm_le_sum_apply (by norm_num) fun p => (hmem n p).memLp.1).trans
    (Finset.sum_le_sum fun p _ => ?_)
  exact (hCs _ _ (hmem n p)).trans (by gcongr; exact hw12 n p)

end WeakH1Chart

/-! ### The weak Yang–Mills / Higgs class -/

section WeakClass

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- **The weak Yang–Mills / Higgs class of `prop:weak-matter-equations`** on a compact chart `Q`
(slab-box rendering): coframes with values a.e. in a fixed compact subset of the coframe chart,
converging strongly in `H¹(Q)`; `A_h → A` in `L⁴(Q)` (`ad P`-valued limit); `F_{A_h} ⇀ F` and
`D_{A_h}H_h ⇀ K` weakly in `L²(Q)` (bounded), with the weak limits identified as `F = F_A` and
`K = D_AH` in `𝒟'(Q)`; `H_h ⇀ H` weakly in `H¹(Q)`; `Ψ_h, Ψ̄_h ⇀ Ψ, Ψ̄` weakly in `H¹(Q)`; the
banks converge inside a compact subset of the physical parameter region. -/
structure WeakMatterConvergence (Q : ChartBox T) (z : ℕ → SmoothFields T left)
    (θ : ℕ → CoefficientBank Ysec) (L : LimitFields C) (θ₀ : CoefficientBank Ysec) : Prop where
  coframe_chart : ∃ Ke, IsCompactCoframeSet Ke ∧ (∀ n, ∀ᵐ x ∂Q.μ, (z n).z.e x ∈ Ke) ∧
    ∀ᵐ x ∂Q.μ, L.e x ∈ Ke
  coframe_mem : MemH1 Q (coframeC L.e) L.de
  coframe_tendsto : H1Tendsto Q (fun n => coframeC (z n).z.e) (fun n => coframeGrad (z n).z.e)
    (coframeC L.e) L.de
  conn_lie : ∀ᵐ x ∂Q.μ, ∀ μ, L.A x μ ∈ smLie
  conn_mem : MemLp L.A 4 Q.μ
  /-- `A_h → A` in `L⁴` -/
  conn_tendsto : LpTendsto 4 Q.μ (fun n => (z n).z.A) L.A
  curv_mem : MemLp L.F 2 Q.μ
  /-- the weak curvature limit is `F_A` -/
  curv_weak : HasWeakCurvature Q L.A L.F
  curv_bounded : LpBounded 2 Q.μ (fun n => curvatureF (z n).z.A)
  /-- `F_{A_h} ⇀ F_A` weakly in `L²` -/
  curv_wtendsto : FirstVariationCalculus.WeakL2Tendsto Q.a Q.b (fun n => curvatureF (z n).z.A) L.F
  /-- `H_h ⇀ H` weakly in `H¹` -/
  higgs_weak : ∃ dH : E4 → Fin 4 → Fin 2 → ℂ,
    WeakH1Tendsto Q (fun n => (z n).z.H) (fun n => higgsGrad (z n).z.H) L.H dH
  covgrad_mem : MemLp L.K 2 Q.μ
  /-- the weak covariant-gradient limit is `D_AH` -/
  covgrad_weak : HasWeakCovGrad Q L.A L.H L.K
  covgrad_bounded : LpBounded 2 Q.μ (fun n => covDerivHiggs (z n).z.A (z n).z.H)
  /-- `D_{A_h}H_h ⇀ D_AH` weakly in `L²` -/
  covgrad_wtendsto : FirstVariationCalculus.WeakL2Tendsto Q.a Q.b
    (fun n => covDerivHiggs (z n).z.A (z n).z.H) L.K
  /-- `Ψ_h ⇀ Ψ` weakly in `H¹` -/
  spinor_weak : WeakH1Tendsto Q (fun n => spinorC (z n).z.Ψ) (fun n => spinorGrad (z n).z.Ψ)
    (spinorC L.Ψ) L.dΨ
  /-- `Ψ̄_h ⇀ Ψ̄` weakly in `H¹` -/
  cospinor_weak : WeakH1Tendsto Q (fun n => spinorC (z n).z.Ψb)
    (fun n => spinorGrad (z n).z.Ψb) (spinorC L.Ψb) L.dΨb
  bank_compact : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P
  bank_tendsto : BankTendsto θ θ₀

theorem LpBounded.toReal_bound {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {μ : Measure E4}
    {u : ℕ → E4 → F} (h : LpBounded p μ u) : ∃ B : ℝ, ∀ n, (eLpNorm (u n) p μ).toReal ≤ B := by
  obtain ⟨B, hB, hle⟩ := h
  exact ⟨B.toReal, fun n => ENNReal.toReal_mono hB (hle n)⟩

end WeakClass

/-! ### The bosonic matter variations under weak curvature convergence -/

section BosonMatter

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool} {Ysec : Type}

theorem testJet_e_eq_zero {v : FieldTuple C} (hv : v.e = 0) (x : E4) : (testJet v x).e = 0 := by
  simp [testJet, hv]

/-- **The bosonic matter data in the weak class**: strong `L²` convergence of the Yang–Mills and
Higgs matter coefficients, strong `L¹` convergence of the Higgs force, and the weakly convergent
curvature and covariant-gradient packets with their `L²` bounds. -/
theorem boson_matter_data {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C}
    {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀) :
    RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 2
      (fun n x => ymWeakCoeff (C := C) (θ n) ((z n).z.e x) ((z n).z.A x))
      (fun x => ymWeakCoeff θ₀ (L.e x) (L.A x)) ∧
    RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 2
      (fun n x => higgsWeakCoeff (C := C) ((z n).z.e x) ((z n).z.H x) ((z n).z.A x))
      (fun x => higgsWeakCoeff (L.e x) (L.H x) (L.A x)) ∧
    RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 1
      (fun n x => potStrongCov (C := C) (θ n) ((z n).z.e x) ((z n).z.H x))
      (fun x => potStrongCov θ₀ (L.e x) (L.H x)) ∧
    (∀ n, MemLp (curvatureF (z n).z.A) 2 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ) ∧
    (∀ n, MemLp (covDerivHiggs (z n).z.A (z n).z.H) 2 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ) ∧
    (∃ B : ℝ, ∀ n, (eLpNorm (curvatureF (z n).z.A) 2
      (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ).toReal ≤ B) ∧
    (∃ B : ℝ, ∀ n, (eLpNorm (covDerivHiggs (z n).z.A (z n).z.H) 2
      (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ).toReal ≤ B) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQdef
  have hO : IsOpen Q.set := SobolevOpen.isOpen_box Q.a Q.b
  have hclS : closure Q.set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have hc : IsCompact (closure Q.set) := isCompact_closure_slabChart h0 h01 h1
  obtain ⟨Ke, hKe, hzKe, hLKe⟩ := hW.coframe_chart
  obtain ⟨-, -, he⟩ := coframe_slab_data h0 h01 h1 hKe hzKe hLKe hW.coframe_mem
    hW.coframe_tendsto
  have hA2 := RenewalGeometry.LpTendsto.mono (ν := Q.μ) (p := 2) (q := 4) (by norm_num)
    (by norm_num) ⟨fun n => memLp_of_continuousOn_closure hO hc
      ((z n).smooth_A.continuousOn.mono hclS) 4, hW.conn_mem, hW.conn_tendsto⟩
  obtain ⟨dH, hHw⟩ := hW.higgs_weak
  obtain ⟨hH2, M, hMt, hH4⟩ := weakH1_chart_data Q hHw
  obtain ⟨hs, hl, hv⟩ := bank_couplings_tendsto hW.bank_compact hW.bank_tendsto
  exact ⟨ymWeakCoeff_tendsto (C := C) he hA2 hs, higgsWeakCoeff_tendsto (C := C) he hH2 hA2,
    potStrongCov_tendsto (C := C) he hH2 hMt hH4 hl hv,
    fun n => memLp_of_continuousOn_closure hO hc
      ((continuousOn_curvatureF (z n).smooth_A).mono hclS) 2,
    fun n => memLp_of_continuousOn_closure hO hc
      ((continuousOn_covDerivHiggs (z n).smooth_A (z n).smooth_H).mono hclS) 2,
    hW.curv_bounded.toReal_bound, hW.covgrad_bounded.toReal_bound⟩

set_option maxHeartbeats 2000000 in
/-- Integrability of the bosonic covector integrands along matter tests (fields and limit). -/
theorem boson_matter_integrable {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} {r : ℕ} (hr : 1 ≤ r) {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C} {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    (v : CrTest left r K) (hv0 : v.val.e = 0) :
    (∀ n, Integrable (fun x => bosonCov (θ n) (redJet (z n).z x) (testJet v.val x))
      (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ) ∧
    Integrable (fun x => bosonCov θ₀ (limitJet L x) (testJet v.val x))
      (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ := by
  obtain ⟨hΩF, hΩK, hΛ, hFm, hKm, -, -⟩ := boson_matter_data h0 h01 h1 hW
  have hT0 := testJet_e_eq_zero hv0
  have hb := fun x => norm_testJet_le (left := left) (K := K) (r := r) hr v x
  refine ⟨fun n => ?_, ?_⟩
  · refine (((integrable_bilin_apply (hΩF.memLp n) (continuous_testJet v) hb (hFm n)).add
      (integrable_bilin_apply (hΩK.memLp n) (continuous_testJet v) hb (hKm n))).add
      (integrable_clm_apply (hΛ.memLp n) (continuous_testJet v) hb)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [bosonCov_matter (θ n) (redJet (z n).z x) (testJet v.val x) (hT0 x)]
    rfl
  · refine (((integrable_bilin_apply hΩF.memLp_lim (continuous_testJet v) hb hW.curv_mem).add
      (integrable_bilin_apply hΩK.memLp_lim (continuous_testJet v) hb hW.covgrad_mem)).add
      (integrable_clm_apply hΛ.memLp_lim (continuous_testJet v) hb)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [bosonCov_matter θ₀ (limitJet L x) (testJet v.val x) (hT0 x)]
    rfl

set_option maxHeartbeats 2000000 in
/-- **The Yang–Mills and Higgs matter variations pass to the weak limit** (`prop:weak-matter-equations`,
bosonic part).  In the weak class on the slab box `Q ⊇` time support of `K`, for `r ≥ 2` the first
variations of the Yang–Mills + Higgs action along matter tests (`k = 0`) converge in the dual norm
of `𝒱_K^r` to the covector formula at the limit fields: gauge variations pair the weakly convergent
curvature with the strongly convergent `∂a + [A_h, a]`, Higgs variations pair the weakly convergent
covariant gradient with `∂η + ρ_H(a)H_h + ρ_H(A_h)η` (strong by Rellich), and the cubic force
converges strongly in `L¹` (critical product). -/
theorem bosonMatterVariation_dual_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁)
    (h1 : t₁ < T) {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ}
    (hr : 2 ≤ r) {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C}
    {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest left r K, v.val.e = 0 →
      |actionVariation T (bosonDensity (θ n)) (z n).z (variationDirection (z n).z v.val) -
        bosonLimitVariation θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖ := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQdef
  obtain ⟨Ke, hKe, hzKe, hLKe⟩ := hW.coframe_chart
  obtain ⟨hcl, -, -⟩ := coframe_slab_data h0 h01 h1 hKe hzKe hLKe hW.coframe_mem
    hW.coframe_tendsto
  obtain ⟨hΩF, hΩK, hΛ, hFm, hKm, ⟨BF, hBF⟩, ⟨BK, hBK⟩⟩ := boson_matter_data h0 h01 h1 hW
  have hε3 : 0 < ε / 3 := by positivity
  filter_upwards [dual_tendsto_of_L1 (left := left) (K := K) (r := r) (by omega) hΛ hε3,
    dual_tendsto_weak_jet (left := left) (K := K) hr Q hΩF hFm hW.curv_mem hBF
      hW.curv_wtendsto hε3,
    dual_tendsto_weak_jet (left := left) (K := K) hr Q hΩK hKm hW.covgrad_mem hBK
      hW.covgrad_wtendsto hε3] with n hn1 hn2 hn3 v hv0
  rw [bosonVariation_eq_cov (θ n) h0 h01 h1 hK (z n) v hKe.1
    (hKe.2.trans coframeChart_subset_GL) (hcl n)]
  unfold bosonLimitVariation
  rw [← hQdef]
  have hT0 := testJet_e_eq_zero hv0
  have hb := fun x => norm_testJet_le (left := left) (K := K) (r := r) (by omega) v x
  have e1 : ∀ x, bosonCov (θ n) (redJet (z n).z x) (testJet v.val x) =
      ymWeakCoeff (θ n) ((z n).z.e x) ((z n).z.A x) (testJet v.val x)
        (curvatureF (z n).z.A x) +
      higgsWeakCoeff ((z n).z.e x) ((z n).z.H x) ((z n).z.A x) (testJet v.val x)
        (covDerivHiggs (z n).z.A (z n).z.H x) +
      potStrongCov (θ n) ((z n).z.e x) ((z n).z.H x) (testJet v.val x) := fun x =>
    bosonCov_matter _ _ _ (hT0 x)
  have e2 : ∀ x, bosonCov θ₀ (limitJet L x) (testJet v.val x) =
      ymWeakCoeff θ₀ (L.e x) (L.A x) (testJet v.val x) (L.F x) +
      higgsWeakCoeff (L.e x) (L.H x) (L.A x) (testJet v.val x) (L.K x) +
      potStrongCov θ₀ (L.e x) (L.H x) (testJet v.val x) := fun x =>
    bosonCov_matter _ _ _ (hT0 x)
  simp only [e1, e2]
  have i1 := integrable_bilin_apply (μ := Q.μ) (hΩF.memLp n) (continuous_testJet v) hb (hFm n)
  have i2 := integrable_bilin_apply (μ := Q.μ) (hΩK.memLp n) (continuous_testJet v) hb (hKm n)
  have i3 := integrable_clm_apply (μ := Q.μ) (hΛ.memLp n) (continuous_testJet v) hb
  have j1 := integrable_bilin_apply (μ := Q.μ) hΩF.memLp_lim (continuous_testJet v) hb
    hW.curv_mem
  have j2 := integrable_bilin_apply (μ := Q.μ) hΩK.memLp_lim (continuous_testJet v) hb
    hW.covgrad_mem
  have j3 := integrable_clm_apply (μ := Q.μ) hΛ.memLp_lim (continuous_testJet v) hb
  have hsplit : ∀ {f g h : E4 → ℝ}, Integrable f Q.μ → Integrable g Q.μ → Integrable h Q.μ →
      ∫ x, (f x + g x + h x) ∂Q.μ = ∫ x, f x ∂Q.μ + ∫ x, g x ∂Q.μ + ∫ x, h x ∂Q.μ :=
    fun {f g h} hf hg hh => by
      rw [integral_add (μ := Q.μ) (f := fun x => f x + g x) (g := h) (hf.add hg) hh,
        integral_add hf hg]
  rw [hsplit i1 i2 i3, hsplit j1 j2 j3]
  have k1 := hn2 v
  have k2 := hn3 v
  have k3 := hn1 v
  have eq : ∀ a b c a' b' c' : ℝ, a + b + c - (a' + b' + c') = (a - a') + (b - b') + (c - c') :=
    fun _ _ _ _ _ _ => by ring
  rw [eq]
  calc _ ≤ |_| + |_| + |_| := abs_add_three _ _ _
    _ ≤ ε / 3 * ‖v‖ + ε / 3 * ‖v‖ + ε / 3 * ‖v‖ := add_le_add (add_le_add k1 k2) k3
    _ = ε * ‖v‖ := by ring

end BosonMatter

/-! ### The complete Standard-Model matter variations and the fermionic first variation -/

section SMMatter

variable {Ysec : Type} (FC : FermionCarrier Ysec) {T : ℝ}

/-- The Dirac data of `prop:weak-fermion` in the weak class: the connections converge in `L²`
(from `L⁴`), the Higgs fields in `L²` (Rellich, from weak `H¹`). -/
theorem weak_class_L2 {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {z : ℕ → SmoothFields T FC.left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields FC.C}
    {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀) :
    RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 2 (fun n => (z n).z.A) L.A ∧
    RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 2 (fun n => (z n).z.H)
      L.H := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQdef
  have hO : IsOpen Q.set := SobolevOpen.isOpen_box Q.a Q.b
  have hclS : closure Q.set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have hc : IsCompact (closure Q.set) := isCompact_closure_slabChart h0 h01 h1
  obtain ⟨dH, hHw⟩ := hW.higgs_weak
  exact ⟨RenewalGeometry.LpTendsto.mono (ν := Q.μ) (p := 2) (q := 4) (by norm_num)
    (by norm_num) ⟨fun n => memLp_of_continuousOn_closure hO hc
      ((z n).smooth_A.continuousOn.mono hclS) 4, hW.conn_mem, hW.conn_tendsto⟩,
    (weakH1_chart_data Q hHw).1⟩

/-- **The complete fermionic first variation has its intended limit in the weak class**
(`prop:weak-matter-equations`, last sentence): the complete Dirac–Yukawa first variation —
metric variation through the symmetric coframe lift including the spin-connection chain, gauge,
Higgs and spinor variations — converges in the dual norm of `𝒱_K^r` (`r ≥ 1`), with no stress
convergence assumption (`prop:weak-fermion` with `A_h → A`, `H_h → H` in `L²`, the latter by
Rellich from the weak `H¹` Higgs convergence). -/
theorem diracVariation_weak_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (hr : 1 ≤ r)
    {z : ℕ → SmoothFields T FC.left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields FC.C}
    {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest FC.left r K,
      |actionVariation T (diracSectorDensity FC (θ n)) (z n).z (variationDirection (z n).z v.val) -
        diracLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖ := by
  obtain ⟨hA2, hH2⟩ := weak_class_L2 FC h0 h01 h1 hW
  exact diracVariation_dual_tendsto FC h0 h01 h1 hK hr hW.coframe_chart hW.coframe_mem
    hW.coframe_tendsto hA2.memLp_lim hA2.tendsto hH2.memLp_lim hH2.tendsto hW.spinor_weak
    hW.cospinor_weak hyL hy0 hε

/-- Integrability of the Dirac covector integrands under the weak-class hypotheses. -/
theorem dirac_integrable {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} {r : ℕ} (hr : 1 ≤ r) {z : ℕ → SmoothFields T FC.left}
    {θ : ℕ → CoefficientBank Ysec} {L : LimitFields FC.C} {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    (v : CrTest FC.left r K) :
    (∀ n, Integrable (fun x => diracCov FC (θ n) (redJet (z n).z x) (testJet v.val x))
      (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ) ∧
    Integrable (fun x => diracCov FC θ₀ (limitJet L x) (testJet v.val x))
      (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ := by
  obtain ⟨hA2, hH2⟩ := weak_class_L2 FC h0 h01 h1 hW
  obtain ⟨Ke, hKe, hzKe, hLKe⟩ := hW.coframe_chart
  obtain ⟨hS, hΩ, hWm, hW₀, -, -⟩ := dirac_data FC h0 h01 h1 hKe hzKe hLKe hW.coframe_mem
    hW.coframe_tendsto hA2.memLp_lim hA2.tendsto hH2.memLp_lim hH2.tendsto hW.spinor_weak
    hW.cospinor_weak hyL hy0
  have hb := fun x => norm_testJet_le (left := FC.left) (K := K) (r := r) hr v x
  have hτb := norm_πτ_testJet_le v
  refine ⟨fun n => ?_, ?_⟩
  · refine ((integrable_clm_apply (hS.memLp n) (continuous_testJet v) hb).add
      (integrable_bilin_apply (hΩ.memLp n) (continuous_πτ_testJet v) hτb (hWm n))).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [diracCov_redJet FC (θ n) (z n).z x (testJet v.val x)]
  · refine ((integrable_clm_apply hS.memLp_lim (continuous_testJet v) hb).add
      (integrable_bilin_apply hΩ.memLp_lim (continuous_πτ_testJet v) hτb hW₀)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [diracCov_limitJet FC θ₀ L x (testJet v.val x)]

set_option maxHeartbeats 2000000 in
/-- **The complete Standard-Model first variation along matter tests passes to the weak limit**
(`r ≥ 2`): Yang–Mills, Higgs and Dirac–Yukawa matter variations converge in the dual norm of
`𝒱_K^r` to the covector formula at the limit fields. -/
theorem smMatterVariation_dual_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (hr : 2 ≤ r)
    {z : ℕ → SmoothFields T FC.left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields FC.C}
    {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest FC.left r K, v.val.e = 0 →
      |firstVariation T FC (θ n) .standardModel (z n).z v.val -
        smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖ := by
  obtain ⟨Ke, hKe, hzKe, hLKe⟩ := hW.coframe_chart
  obtain ⟨hcl, -, -⟩ := coframe_slab_data h0 h01 h1 hKe hzKe hLKe hW.coframe_mem
    hW.coframe_tendsto
  filter_upwards [bosonMatterVariation_dual_tendsto h0 h01 h1 hK hr hW (half_pos hε),
    diracVariation_weak_tendsto FC h0 h01 h1 hK (r := r) (by omega) hW hyL hy0 (half_pos hε)]
    with n hb hd v hv0
  have hbv := hb v hv0
  have hdv := hd v
  obtain ⟨ib, ib₀⟩ := boson_matter_integrable h0 h01 h1 (by omega) hW v hv0
  obtain ⟨id, id₀⟩ := dirac_integrable FC h0 h01 h1 (by omega) hW hyL hy0 v
  have hKGL := hKe.2.trans coframeChart_subset_GL
  rw [bosonVariation_eq_cov (θ n) h0 h01 h1 hK (z n) v hKe.1 hKGL (hcl n)] at hbv
  rw [diracVariation_eq_cov FC (θ n) h0 h01 h1 hK (z n) v hKe.1 hKGL (hcl n)] at hdv
  rw [smVariation_eq_cov FC (θ n) h0 h01 h1 hK (z n) v hKe.1 hKGL (hcl n)]
  unfold bosonLimitVariation at hbv
  unfold diracLimitVariation at hdv
  unfold smLimitVariation
  simp only [ContinuousLinearMap.add_apply]
  rw [integral_add (ib n) (id n), integral_add ib₀ id₀]
  have eq : ∀ a b a' b' : ℝ, a + b - (a' + b') = (a - a') + (b - b') := fun _ _ _ _ => by ring
  rw [eq]
  calc _ ≤ |_| + |_| := abs_add_le _ _
    _ ≤ ε / 2 * ‖v‖ + ε / 2 * ‖v‖ := add_le_add hbv hdv
    _ = ε * ‖v‖ := by ring

end SMMatter

/-! ### The limiting matter Euler equations -/

section Euler

variable {Ysec : Type} (FC : FermionCarrier Ysec) {T : ℝ}

/-- Along a matter test (`k = 0`) the coframe is not varied, so the gravitational first variation
vanishes identically. -/
theorem firstVariation_gravity_matter (θ : CoefficientBank Ysec) (z v : FieldTuple FC.C)
    (hv : v.e = 0) : firstVariation T FC θ .gravity z v = 0 := by
  have he : ∀ ε : ℝ, (z + ε • variationDirection z v).e = z.e := by
    intro ε
    have hv' : v.1 = 0 := hv
    funext x a μ
    simp [FieldTuple.e, variationDirection, FieldTuple.mk, metricLift, hv']
  simp only [firstVariation, actionVariation, sectorDensity, he, sub_self, integral_zero,
    deriv_const']

theorem pd_smul_test {T' : ℝ} {K : CylRegion T'} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E4 → F} (hf : IsCylTest K f) (c : ℝ) (i : Fin 4) (x : E4) :
    pd (c • f) i x = c • pd f i x := by
  unfold pd
  rw [show (c • f) = fun y => c • f y from rfl,
    fderiv_fun_const_smul ((hf.smooth.differentiable (by simp)) x)]
  rfl

theorem testJet_smul_matter {C : Type} [Fintype C] {left : C → Bool} {r : ℕ} {T' : ℝ}
    {K : CylRegion T'} (v : CrTest left r K) (c : ℝ) (x : E4) :
    testJet (c • v).val x = c • testJet v.val x := by
  rw [CrTest.val_smul]
  simp only [testJet, RJet.mk]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_
    (Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))))))))
  · funext i; exact pd_smul_test (isCylTest_e v) c i x
  · funext i; exact pd_smul_test (isCylTest_A v) c i x
  · funext i; exact pd_smul_test (isCylTest_H v) c i x
  · funext i; exact pd_smul_test (isCylTest_Ψ v) c i x
  · funext i; exact pd_smul_test (isCylTest_Ψb v) c i x

theorem smLimitVariation_smul_matter (θ : CoefficientBank Ysec) (Q : ChartBox T) (L : LimitFields FC.C)
    {r : ℕ} {K : CylRegion T} (v : CrTest FC.left r K) (c : ℝ) :
    smLimitVariation FC θ Q L (c • v) = c * smLimitVariation FC θ Q L v := by
  unfold smLimitVariation
  simp only [testJet_smul_matter, map_smul, smul_eq_mul]
  exact integral_const_mul c _

/-- **Matter Euler equations from vanishing matter residuals.**  In the weak class (`r ≥ 2`), if
the Standard-Model first variations of the approximate fields along matter tests of `C^r` norm
`≤ 1` tend to zero uniformly, then the limit fields satisfy the Yang–Mills, Higgs and
Dirac–Yukawa Euler equations in distributions: `D𝒮_{SM,θ}(z)[v] = 0` for every matter test `v`
(`k = 0`; `v = (0, a, 0, 0, 0)` is the Yang–Mills equation, `(0, 0, η_H, 0, 0)` the Higgs equation,
`(0, 0, 0, η, η̄)` the Dirac–Yukawa equations). -/
theorem matter_euler_of_residual {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (hr : 2 ≤ r)
    {z : ℕ → SmoothFields T FC.left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields FC.C}
    {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    (hres : ∀ δ > 0, ∀ᶠ n in atTop, ∀ v : CrTest FC.left r K, v.val.e = 0 → ‖v‖ ≤ 1 →
      |firstVariation T FC (θ n) .standardModel (z n).z v.val| ≤ δ) :
    ∀ v : CrTest FC.left r K, v.val.e = 0 →
      smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v = 0 := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQdef
  -- the unit-ball case
  have hunit : ∀ v : CrTest FC.left r K, v.val.e = 0 → ‖v‖ ≤ 1 →
      smLimitVariation FC θ₀ Q L v = 0 := by
    intro v hv0 hv1
    have hconv : Tendsto (fun n => firstVariation T FC (θ n) .standardModel (z n).z v.val) atTop
        (𝓝 (smLimitVariation FC θ₀ Q L v)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp
        (smMatterVariation_dual_tendsto FC h0 h01 h1 hK hr hW hyL hy0 (half_pos hε))
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq]
      calc _ ≤ ε / 2 * ‖v‖ := hN n hn v hv0
        _ ≤ ε / 2 * 1 := by gcongr
        _ < ε := by linarith
    have hzero : Tendsto (fun n => firstVariation T FC (θ n) .standardModel (z n).z v.val) atTop
        (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hres (ε / 2) (half_pos hε))
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq, sub_zero]
      exact (hN n hn v hv0 hv1).trans_lt (half_lt_self hε)
    exact tendsto_nhds_unique hconv hzero
  intro v hv0
  rcases eq_or_ne v 0 with rfl | hne
  · have := smLimitVariation_smul_matter FC θ₀ Q L (0 : CrTest FC.left r K) 0
    rw [zero_smul, zero_mul] at this
    exact this
  · have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hne
    have hw0 : (‖v‖⁻¹ • v).val.e = 0 := by
      rw [CrTest.val_smul]
      show ‖v‖⁻¹ • v.val.e = 0
      rw [hv0, smul_zero]
    have hw1 : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    have h := hunit _ hw0 hw1
    rw [smLimitVariation_smul_matter] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hpos.ne')

end Euler

/-! ### Regulator sequences: consistency and stationarity on matter tests -/

section Regulator

variable {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec} {T : ℝ}

/-- **First-variation consistency on matter tests** (`eq:C1-consistency` restricted to the matter
tests `k = 0` of the `C^{r₀}` unit ball of `𝒱_K`), uniformly in the sector. -/
def RegulatorSequence.MatterConsistent (reg : RegulatorSequence T FC) (K : CylRegion T) : Prop :=
  ∀ δ > 0, ∀ᶠ n in atTop, ∀ v : ↥(testSubmodule FC.left K), v.1.e = 0 →
    testNorm reg.r0 v.1 ≤ 1 → ∀ b : Sector,
      |reg.finiteSectorVariation n b (reg.lift n K v) -
        firstVariation T FC (reg.bank n) b (reg.fields n).z v.1| ≤ δ

/-- **Physical stationarity on matter tests** (`eq:stationarity` restricted to matter tests). -/
def RegulatorSequence.MatterStationary (reg : RegulatorSequence T FC) (K : CylRegion T) : Prop :=
  ∀ δ > 0, ∀ᶠ n in atTop, ∀ v : ↥(testSubmodule FC.left K), v.1.e = 0 →
    testNorm reg.r0 v.1 ≤ 1 → |fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)| ≤ δ

/-- First-variation consistency (`c_h(K) → 0`) implies consistency on matter tests. -/
theorem RegulatorSequence.matterConsistent_of (reg : RegulatorSequence T FC)
    (h : reg.FirstVariationConsistent) (K : CylRegion T) : reg.MatterConsistent K := by
  intro δ hδ
  have hK := ENNReal.tendsto_nhds_zero.mp (h K) (ENNReal.ofReal δ) (by simpa using hδ)
  filter_upwards [hK] with n hn v _ hv1 b
  have h1 : ENNReal.ofReal |reg.finiteSectorVariation n b (reg.lift n K v) -
      firstVariation T FC (reg.bank n) b (reg.fields n).z v.1| ≤ reg.consistencyDefect n K := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun b : Sector => ⨆ (v : ↥(testSubmodule
      FC.left K)) (_ : testNorm reg.r0 v.1 ≤ 1), ENNReal.ofReal |reg.finiteSectorVariation n b
        (reg.lift n K v) - firstVariation T FC (reg.bank n) b (reg.fields n).z v.1|)
      (fun _ _ => bot_le) (Finset.mem_univ b))
    exact le_iSup₂ (f := fun (v : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 v.1 ≤ 1) =>
      ENNReal.ofReal |reg.finiteSectorVariation n b (reg.lift n K v) -
        firstVariation T FC (reg.bank n) b (reg.fields n).z v.1|) v hv1
  exact (ENNReal.ofReal_le_ofReal_iff hδ.le).mp (h1.trans hn)

/-- Physical stationarity (`ε_h(K) → 0`) implies stationarity on matter tests. -/
theorem RegulatorSequence.matterStationary_of (reg : RegulatorSequence T FC)
    (h : reg.PhysicallyStationary) (K : CylRegion T) : reg.MatterStationary K := by
  intro δ hδ
  have hK := ENNReal.tendsto_nhds_zero.mp (h K) (ENNReal.ofReal δ) (by simpa using hδ)
  filter_upwards [hK] with n hn v _ hv1
  have h1 : ENNReal.ofReal |fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)| ≤
      reg.stationarityDefect n K :=
    le_iSup₂ (f := fun (v : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 v.1 ≤ 1) =>
      ENNReal.ofReal |fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)|) v hv1
  exact (ENNReal.ofReal_le_ofReal_iff hδ.le).mp (h1.trans hn)

/-- **The Standard-Model matter residual vanishes** under consistency and stationarity on matter
tests: `|D𝒮_{SM,θ_h}(z_h)[v]| ≤ |D𝒮_{SM,θ_h}(z_h)[v] - D𝒮_{SM,h}(z_h^d)[𝓘_hv]| + |D𝒮_h(z_h^d)[𝓘_hv]|
+ |D𝒮_{g,h}(z_h^d)[𝓘_hv] - D𝒮_{g,θ_h}(z_h)[v]|`, the last continuum term being zero on matter
tests. -/
theorem RegulatorSequence.matter_residual (reg : RegulatorSequence T FC) {K : CylRegion T}
    (hc : reg.MatterConsistent K) (hs : reg.MatterStationary K) :
    ∀ δ > 0, ∀ᶠ n in atTop, ∀ v : CrTest FC.left reg.r0 K, v.val.e = 0 → ‖v‖ ≤ 1 →
      |firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.val| ≤ δ := by
  intro δ hδ
  filter_upwards [hc (δ / 3) (by positivity), hs (δ / 3) (by positivity)] with n hcn hsn v hv0 hv1
  set w : ↥(testSubmodule FC.left K) := (show ↥(testSubmodule FC.left K) from v)
  have hw0 : w.1.e = 0 := hv0
  have hw1 : testNorm reg.r0 w.1 ≤ 1 := hv1
  have hg := hcn w hw0 hw1 .gravity
  have hsm := hcn w hw0 hw1 .standardModel
  have hst := hsn w hw0 hw1
  rw [firstVariation_gravity_matter FC _ _ _ hw0, sub_zero] at hg
  rw [reg.fderiv_action_eq_sum] at hst
  have e : firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.val =
      -(reg.finiteSectorVariation n .standardModel (reg.lift n K w) -
        firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z w.1) +
      (reg.finiteSectorVariation n .gravity (reg.lift n K w) +
        reg.finiteSectorVariation n .standardModel (reg.lift n K w)) -
      reg.finiteSectorVariation n .gravity (reg.lift n K w) := by
    show _ = -(_ - firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.val) + _ - _
    ring
  rw [e]
  calc _ ≤ |-(reg.finiteSectorVariation n .standardModel (reg.lift n K w) -
        firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z w.1) +
      (reg.finiteSectorVariation n .gravity (reg.lift n K w) +
        reg.finiteSectorVariation n .standardModel (reg.lift n K w))| +
      |reg.finiteSectorVariation n .gravity (reg.lift n K w)| := abs_sub _ _
    _ ≤ (|reg.finiteSectorVariation n .standardModel (reg.lift n K w) -
        firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z w.1| +
      |reg.finiteSectorVariation n .gravity (reg.lift n K w) +
        reg.finiteSectorVariation n .standardModel (reg.lift n K w)|) +
      |reg.finiteSectorVariation n .gravity (reg.lift n K w)| := by
        gcongr
        exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ ≤ δ / 3 + δ / 3 + δ / 3 := by gcongr
    _ = δ := by ring

/-- **`prop:weak-matter-equations`** (slab-box rendering).  Let a finite-interface regulator
sequence (`def:regulator`) have reconstructed fields `z_h` and banks `θ_h` in the weak Yang–Mills /
Higgs class on the slab box `Q ⊇` time support of `K` (`WeakMatterConvergence`: coframes in a
compact subset of the coframe chart converging in `H¹`, `A_h → A` in `L⁴`, `F_{A_h} ⇀ F_A` and
`D_{A_h}H_h ⇀ D_AH` weakly in `L²`, `H_h ⇀ H` and `Ψ_h, Ψ̄_h ⇀ Ψ, Ψ̄` weakly in `H¹`, parameters
converging in the physical region, Yukawa coefficients converging).  If first-variation consistency
and physical stationarity hold for all matter tests, then

* the limiting Yang–Mills, Higgs and Dirac–Yukawa equations hold in distributions:
  `D𝒮_{SM,θ}(z)[v] = 0` for every matter test `v ∈ 𝒱_K` (`k = 0`);
* the complete fermionic first variation (including its metric variation) has its intended limit,
  in the dual norm of `𝒱_K^r` for every `r ≥ 1`, without any stress-convergence assumption. -/
theorem weak_matter_equations (reg : RegulatorSequence T FC) {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁)
    {L : LimitFields FC.C} {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) reg.fields reg.bank L θ₀)
    (hyL : Tendsto (fun n => yukL FC (reg.bank n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (reg.bank n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    (hc : reg.MatterConsistent K) (hs : reg.MatterStationary K) :
    (∀ v : CrTest FC.left reg.r0 K, v.val.e = 0 →
      smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v = 0) ∧
    (∀ r : ℕ, 1 ≤ r → ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : CrTest FC.left r K,
      |actionVariation T (diracSectorDensity FC (reg.bank n)) (reg.fields n).z
          (variationDirection (reg.fields n).z v.val) -
        diracLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖) :=
  ⟨matter_euler_of_residual FC h0 h01 h1 hK (by have := reg.four_le_r0; omega) hW hyL hy0
      (reg.matter_residual hc hs),
    fun _ hr _ hε => diracVariation_weak_tendsto FC h0 h01 h1 hK hr hW hyL hy0 hε⟩

/-- **`prop:weak-matter-equations` from the regulator conditions** `FirstVariationConsistent` and
`PhysicallyStationary` of `def:regulator` (which in particular hold on all matter tests). -/
theorem weak_matter_equations_of_regulator (reg : RegulatorSequence T FC) {t₀ t₁ : ℝ}
    (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {L : LimitFields FC.C} {θ₀ : CoefficientBank Ysec}
    (hW : WeakMatterConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) reg.fields reg.bank L θ₀)
    (hyL : Tendsto (fun n => yukL FC (reg.bank n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (reg.bank n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    (hc : reg.FirstVariationConsistent) (hs : reg.PhysicallyStationary) :
    (∀ v : CrTest FC.left reg.r0 K, v.val.e = 0 →
      smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v = 0) ∧
    (∀ r : ℕ, 1 ≤ r → ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : CrTest FC.left r K,
      |actionVariation T (diracSectorDensity FC (reg.bank n)) (reg.fields n).z
          (variationDirection (reg.fields n).z v.val) -
        diracLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖) :=
  weak_matter_equations reg h0 h01 h1 hK hW hyL hy0 (reg.matterConsistent_of hc K)
    (reg.matterStationary_of hs K)

end Regulator

/-! ### Non-vacuity: the flat regulator -/

section NonVacuity

/-- The flat regulator lies in the weak Yang–Mills / Higgs class on every chart box. -/
theorem flatRegulator_weakMatterConvergence (T : ℝ) (Q : ChartBox T) :
    WeakMatterConvergence Q (flatRegulator T).fields (flatRegulator T).bank flatLimit
      physicalBank := by
  have hRC := flatRegulator_reducedActionConvergence T Q
  have hF : ∀ n, curvatureF ((flatRegulator T).fields n).z.A = 0 := fun n => by
    simp only [flat_A, curvatureF_zero]
  have hK : ∀ n, covDerivHiggs ((flatRegulator T).fields n).z.A
      ((flatRegulator T).fields n).z.H = 0 := fun n => by
    simp only [flat_A, flat_H, covDerivHiggs_zero]
  refine ⟨hRC.coframe_chart, hRC.coframe_mem, hRC.coframe_tendsto, hRC.conn_lie, hRC.conn_mem,
    hRC.conn_tendsto, hRC.curv_mem, hRC.curv_weak, ?_, ?_, ?_, hRC.covgrad_mem, hRC.covgrad_weak,
    ?_, ?_, hRC.spinor_weak, hRC.cospinor_weak, hRC.bank_compact, hRC.bank_tendsto⟩
  · simp only [hF]; exact lpBounded_const MemLp.zero
  · simp only [hF]
    intro ℓ g _
    exact tendsto_const_nhds
  · refine ⟨fun _ _ => 0, ?_⟩
    simp only [flat_H, higgsGrad_zero]
    exact weakH1Tendsto_const Q (0 : Fin 2 → ℂ)
  · simp only [hK]; exact lpBounded_const MemLp.zero
  · simp only [hK]
    intro ℓ g _
    exact tendsto_const_nhds

/-- The Standard-Model first variation of the flat fields vanishes along matter tests. -/
theorem flat_smVariation_matter {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (n : ℕ)
    (v : CrTest (trivialCarrier Unit).left r K) (hv0 : v.val.e = 0) :
    firstVariation T (trivialCarrier Unit) ((flatRegulator T).bank n) .standardModel
      ((flatRegulator T).fields n).z v.val = 0 := by
  have hKGL : ({flatCoframe} : Set CoframeFibre) ⊆ coframeGL :=
    isCompactCoframeSet_flat.2.trans coframeChart_subset_GL
  rw [smVariation_eq_cov (trivialCarrier Unit) _ h0 h01 h1 hK ((flatRegulator T).fields n) v
    isCompact_singleton hKGL (fun x _ => rfl)]
  refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
  have hT0 := testJet_e_eq_zero hv0 x
  simp only [ContinuousLinearMap.add_apply]
  rw [bosonCov_matter _ _ _ hT0, diracCov_redJet]
  simp [redJet, diracStrongField, diracWeakField, potStrongCov, spinorGrad_zero,
    curvatureF_zero, covDerivHiggs_zero]
  rw [Prod.mk_zero_zero, Prod.mk_zero_zero, map_zero, map_zero]
  simp

theorem flat_matterConsistent {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    (K : CylRegion T) (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) :
    (flatRegulator T).MatterConsistent K := by
  intro δ hδ
  refine Eventually.of_forall fun n v hv0 _ b => ?_
  have hlift : (flatRegulator T).lift n K v = 0 := rfl
  cases b
  · rw [firstVariation_gravity_matter _ _ _ _ hv0]
    simp [hlift, RegulatorSequence.finiteSectorVariation, hδ.le]
  · have h' : firstVariation T (trivialCarrier Unit) ((flatRegulator T).bank n) .standardModel
        ((flatRegulator T).fields n).z v.1 = 0 :=
      flat_smVariation_matter h0 h01 h1 hK (r := (flatRegulator T).r0) n v hv0
    rw [h']
    simp [hlift, RegulatorSequence.finiteSectorVariation, hδ.le]

theorem flat_matterStationary (T : ℝ) (K : CylRegion T) :
    (flatRegulator T).MatterStationary K := by
  intro δ hδ
  refine Eventually.of_forall fun n v _ _ => ?_
  have hlift : (flatRegulator T).lift n K v = 0 := rfl
  simp [hlift, hδ.le]

/-- **Non-vacuity of `weak_matter_equations`**: the flat regulator (trivial carrier, physical
bank) satisfies the complete hypothesis packet — the weak class on the slab box, convergent Yukawa
data, consistency and stationarity on matter tests. -/
example {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) :
    ∀ v : CrTest (trivialCarrier Unit).left (flatRegulator T).r0 K, v.val.e = 0 →
      smLimitVariation (trivialCarrier Unit) physicalBank (slabChart t₀ t₁ h0 h01 h1 (T := T))
        flatLimit v = 0 :=
  (weak_matter_equations (flatRegulator T) h0 h01 h1 hK
    (flatRegulator_weakMatterConvergence T _) tendsto_const_nhds tendsto_const_nhds
    (flat_matterConsistent h0 h01 h1 K hK) (flat_matterStationary T K)).1

end NonVacuity

end EinsteinSM
end RenewalGeometry
