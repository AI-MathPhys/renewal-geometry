/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.EinsteinSMWeakMatterLimit
import RenewalGeometry.Continuum.EinsteinSMCompactnessCertificates
open MathPhys

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
open MathPhys.EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

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
