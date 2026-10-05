/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeZeroSource
import RenewalGeometry.Continuum.NativeLowSourceGevrey
import RenewalGeometry.Continuum.NativeSourceBudget

/-!
# The leakage-tolerant physical forcing estimate (`thm:native-source`)

Einstein–Standard-Model action-closure manuscript, `thm:native-source`, all three displays, for
the complete, unfiltered reconstruction `z_h = 𝓘_h^trig u_h` of a record on the odd periodic grid
`(ℤ/n)⁴` (`h = 2π/n`, period-`2π` auxiliary box, `Σ = 𝕋³`), on a slab
`Q = [t₀,t₁] × (0,2π]³` buffered by `Q' = [t₀-δ, t₁+δ) × [0,2π)³` inside one period:

* `eq:native-zero-source`: `‖𝓡_B(z_h)‖_{L²(Q)} + ‖𝓡_D(z_h)‖_{L²(Q)} ≤ C ε_{0,h}`
  (`NativeZeroSource.native_zero_source`);
* `eq:native-strong-source`: `𝒴_k(z_h) = ‖𝓡_B(z_h)‖_{L²_tH^k_x(Q)} + ‖𝓡_D(z_h)‖_{L²_tH^{k+1}_x(Q)}
  ≤ C F_{h,k}` with the literal budget `F_{h,k}` of `eq:native-forcing-budget`;
* `eq:native-full-Cartan`: the literal Cartan plaquette curvature of the record is `C h K³`-close
  to `Riem(g_h)` at every point of every cell (the `L^∞` form; the `L²(Q)` form follows with the
  factor `|Q|^{1/2}`).

The proof is the manuscript's: the zero-order estimate from `prop:native-consistency` and
`lem:nodal-source-transfer`; the zero-order and source-tail clauses of `lem:native-tail-transfer`
(`NativeTail.native_source_tail`); the analytic growth of the low-frequency residual rows
(`NativeLowSource.native_low_gevrey`, the real-variable form of the strip step) feeding
`lem:log-source-upgrade` in the slab norm (`NativeSlab.sobX_log_upgrade`); the bookkeeping
`NativeSourceBudget.native_source_assembly`.  The triangle inequality for the slab norm
(`sobX_add_le`) connects the full and low-frequency rows.

Hypotheses, as in the manuscript: the complete record and its low head lie in the calibrated
field-value chart (coframe values in a compact `K_e ⊂ {det e > 0}`, which gives the uniform
inverse-metric margins; amplitudes `≤ A`), `hK ≤ c_res`, `τ_{h,k+2}(K) ≤ τ_*`, and `σ` bounds the
finite-action covector norm on `Q'`.  The manuscript's `ε_{c,h} ≤ 1` is not needed.  `k ≥ 1`
(the manuscript has `k ≥ 4`).
-/

open MeasureTheory Filter Topology Set Finset
open scoped Real ENNReal Nat ContDiff

namespace RenewalGeometry.NativeSourceThm

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency NativeTail
open TrigInterp (recon reconLow tau)
open NativeRate (eps0 forcingBudget)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### The triangle inequality for the slab norm -/

section Triangle

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- `∫_Q (a+b)² ≤ (√∫a² + √∫b²)²` for continuous nonnegative `a`, `b` on the slab. -/
theorem integral_add_sq_le {a b : R4 → ℝ} (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ z, 0 ≤ a z) (hb0 : ∀ z, 0 ≤ b z) (t₀ t₁ : ℝ) :
    ∫ z in NativeSlab.slab t₀ t₁, (a z + b z) ^ 2 ≤
      (Real.sqrt (∫ z in NativeSlab.slab t₀ t₁, a z ^ 2) +
        Real.sqrt (∫ z in NativeSlab.slab t₀ t₁, b z ^ 2)) ^ 2 := by
  set μ : Measure R4 := volume.restrict (NativeSlab.slab t₀ t₁)
  have hia : Integrable (fun z => a z ^ 2) μ := NativeSlab.integrableOn_slab (ha.pow 2) t₀ t₁
  have hib : Integrable (fun z => b z ^ 2) μ := NativeSlab.integrableOn_slab (hb.pow 2) t₀ t₁
  have hiab : Integrable (fun z => a z * b z) μ := NativeSlab.integrableOn_slab (ha.mul hb) t₀ t₁
  have hma : MemLp a (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mpr hia
  have hmb : MemLp b (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mpr hib
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (Eventually.of_forall ha0) (Eventually.of_forall hb0) hma hmb
  have e2 : ∀ f : R4 → ℝ, (∫ z, f z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
      Real.sqrt (∫ z, f z ^ 2 ∂μ) := by
    intro f
    rw [Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    exact Real.rpow_two (f z)
  rw [e2 a, e2 b] at hH
  have hA0 : 0 ≤ ∫ z, a z ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hB0 : 0 ≤ ∫ z, b z ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hexp : ∫ z, (a z + b z) ^ 2 ∂μ =
      ∫ z, a z ^ 2 ∂μ + 2 * ∫ z, a z * b z ∂μ + ∫ z, b z ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_add hia (hiab.const_mul 2), ← integral_add _ hib]
    · refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only []; ring
    · exact hia.add (hiab.const_mul 2)
  show ∫ z, (a z + b z) ^ 2 ∂μ ≤ _
  rw [hexp, add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  nlinarith

theorem dX_add {F G : R4 → W} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (i : ℕ) (z : R4) :
    NativeTail.dX i (F + G) z = NativeTail.dX i F z + NativeTail.dX i G z := by
  unfold NativeTail.dX
  rw [iteratedFDeriv_add_apply ((hF.of_le (ContEulerBounds.natCast_le_infty i)).contDiffAt)
    ((hG.of_le (ContEulerBounds.natCast_le_infty i)).contDiffAt)]
  ext v
  simp

/-- **The triangle inequality for `‖·‖_{L²_tH^j_x(Q)}`** (smooth fields). -/
theorem sobX_add_le {F G : R4 → W} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (j : ℕ)
    (t₀ t₁ : ℝ) :
    NativeTail.sobX j (NativeSlab.slab t₀ t₁) (F + G) ≤
      NativeTail.sobX j (NativeSlab.slab t₀ t₁) F + NativeTail.sobX j (NativeSlab.slab t₀ t₁) G := by
  set sF : R4 → ℝ := fun z => ∑ i ∈ Finset.range (j + 1), ‖NativeTail.dX i F z‖ ^ 2
  set sG : R4 → ℝ := fun z => ∑ i ∈ Finset.range (j + 1), ‖NativeTail.dX i G z‖ ^ 2
  set sFG : R4 → ℝ := fun z => ∑ i ∈ Finset.range (j + 1), ‖NativeTail.dX i (F + G) z‖ ^ 2
  have hcF : Continuous sF := continuous_finset_sum _ fun i _ =>
    (NativeSlab.continuous_dX hF i).norm.pow 2
  have hcG : Continuous sG := continuous_finset_sum _ fun i _ =>
    (NativeSlab.continuous_dX hG i).norm.pow 2
  have hcFG : Continuous sFG := continuous_finset_sum _ fun i _ =>
    (NativeSlab.continuous_dX (hF.add hG) i).norm.pow 2
  have hsF0 : ∀ z, 0 ≤ sF z := fun z => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsG0 : ∀ z, 0 ≤ sG z := fun z => Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- pointwise Minkowski
  have hpt : ∀ z, sFG z ≤ (Real.sqrt (sF z) + Real.sqrt (sG z)) ^ 2 := by
    intro z
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range (j + 1))
      (fun i => ‖NativeTail.dX i F z‖) (fun i => ‖NativeTail.dX i G z‖)
    have h1 : sFG z ≤ ∑ i ∈ Finset.range (j + 1),
        (‖NativeTail.dX i F z‖ + ‖NativeTail.dX i G z‖) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [dX_add hF hG]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    refine h1.trans ?_
    rw [add_sq, Real.sq_sqrt (hsF0 z), Real.sq_sqrt (hsG0 z)]
    have e : ∑ i ∈ Finset.range (j + 1), (‖NativeTail.dX i F z‖ + ‖NativeTail.dX i G z‖) ^ 2 =
        sF z + 2 * ∑ i ∈ Finset.range (j + 1), ‖NativeTail.dX i F z‖ * ‖NativeTail.dX i G z‖ +
          sG z := by
      simp only [sF, sG, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1; congr 1
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [e]
    nlinarith
  have hsq : ∀ z, Real.sqrt (sF z) ^ 2 = sF z := fun z => Real.sq_sqrt (hsF0 z)
  have hsq' : ∀ z, Real.sqrt (sG z) ^ 2 = sG z := fun z => Real.sq_sqrt (hsG0 z)
  have hint := integral_add_sq_le (Real.continuous_sqrt.comp hcF) (Real.continuous_sqrt.comp hcG)
    (fun z => Real.sqrt_nonneg _) (fun z => Real.sqrt_nonneg _) t₀ t₁
  simp only [Function.comp, hsq, hsq'] at hint
  have hmono : ∫ z in NativeSlab.slab t₀ t₁, sFG z ≤
      ∫ z in NativeSlab.slab t₀ t₁, (Real.sqrt (sF z) + Real.sqrt (sG z)) ^ 2 :=
    setIntegral_mono (NativeSlab.integrableOn_slab hcFG t₀ t₁)
      (NativeSlab.integrableOn_slab (((Real.continuous_sqrt.comp hcF).add
        (Real.continuous_sqrt.comp hcG)).pow 2) t₀ t₁) hpt
  unfold NativeTail.sobX NativeTail.sobXSq
  calc Real.sqrt (∫ z in NativeSlab.slab t₀ t₁, sFG z)
      ≤ Real.sqrt ((Real.sqrt (∫ z in NativeSlab.slab t₀ t₁, sF z) +
          Real.sqrt (∫ z in NativeSlab.slab t₀ t₁, sG z)) ^ 2) :=
        Real.sqrt_le_sqrt (hmono.trans hint)
    _ = Real.sqrt (∫ z in NativeSlab.slab t₀ t₁, sF z) +
          Real.sqrt (∫ z in NativeSlab.slab t₀ t₁, sG z) :=
        Real.sqrt_sq (by positivity)

theorem sobX_neg_eq (F : R4 → W) (j : ℕ) (Q : Set R4) :
    NativeTail.sobX j Q (-F) = NativeTail.sobX j Q F := by
  unfold NativeTail.sobX NativeTail.sobXSq NativeTail.dX
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_neg_apply]
  have e : (-iteratedFDeriv ℝ i F z).compContinuousLinearMap (fun _ => NativeTail.spatialL) =
      -((iteratedFDeriv ℝ i F z).compContinuousLinearMap (fun _ => NativeTail.spatialL)) := by
    ext v; simp
  rw [e, norm_neg]

end Triangle

/-! ### Periodicity of the residual rows -/

section Periodic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem fderiv_add_of_invariant {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {a : E} (hf : ∀ z, f (z + a) = f z)
    (z : E) : fderiv ℝ f (z + a) = fderiv ℝ f z := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext x; exact hf x

/-- The continuum Euler expression of a periodic field is periodic. -/
theorem contEuler_isPeriodic (Lag : V × (Fin 4 → V) → ℝ) {L : ℝ} {Y : R4 → V}
    (hY : IsPeriodic L Y) : IsPeriodic L (contEuler Lag Y) := by
  intro z μ
  set a : R4 := Pi.single μ L
  have hY' : ∀ z, Y (z + a) = Y z := fun z => hY z μ
  have hj : ∀ z, jet1 Y (z + a) = jet1 Y z := by
    intro z
    simp only [jet1, hY' z, fderiv_add_of_invariant hY' z]
  unfold contEuler
  rw [hj z]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hH : ∀ z', (fun z' => (fderiv ℝ Lag (jet1 Y z')).comp
      ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) ν))) (z' + a) =
      (fun z' => (fderiv ℝ Lag (jet1 Y z')).comp
      ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) ν))) z' := fun z' => by
    simp only [hj z']
  rw [fderiv_add_of_invariant hH z]

end Periodic

/-! ### `thm:native-source` -/

section Main

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

local notation "FJ" => ContEulerBounds.JS (Field 𝔄 𝓗 𝓢)
local notation "FF" => Field 𝔄 𝓗 𝓢

theorem isPeriodic_RB {L : ℝ} {Y : R4 → FF} (hY : IsPeriodic L Y) : IsPeriodic L (RB D Y) :=
  fun z μ => by
    unfold RB Rfull
    rw [contEuler_isPeriodic _ hY z μ]

theorem isPeriodic_RD {L : ℝ} {Y : R4 → FF} (hY : IsPeriodic L Y) : IsPeriodic L (RD D Y) :=
  fun z μ => by
    unfold RD Rfull
    rw [contEuler_isPeriodic _ hY z μ]

theorem isPeriodic_reconLow {n : ℕ} [NeZero n] (u : Grid n → FF) (K : ℝ) :
    IsPeriodic (2 * π) (reconLow n K u) := NativeTail.isPeriodic_tp _

theorem isPeriodic_recon' {n : ℕ} [NeZero n] (u : Grid n → FF) :
    IsPeriodic (2 * π) (recon n u) := NativeTail.isPeriodic_tp _

end Main

/-! ### The low-frequency rows: logarithmic upgrade (`lem:log-source-upgrade` applied) -/

section LowUpgrade

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

local notation "FJ" => ContEulerBounds.JS (Field 𝔄 𝓗 𝓢)
local notation "FF" => Field 𝔄 𝓗 𝓢

theorem chartU_of_mem {Ke : Set Mat} (hdet : ∀ e ∈ Ke, 0 < e.det) {K : ℝ} {Y : R4 → FF}
    (hY : ∀ x, (Y x).1 ∈ Ke) (ξ : R4) : ((K⁻¹, jet1 (resc K Y) ξ) : ℝ × FJ) ∈ chartU :=
  (hdet _ (hY (K⁻¹ • ξ))).ne'

/-- **The strip step and `lem:log-source-upgrade` for the low-frequency rows** (inputs `(h2)` of
`native_source_assembly`): there are `C_j, C_A > 0` such that for every record with low head in
the chart, every `K ≥ 1` and every `ε > 0`,
`‖𝓡_B(z^lo)‖_{L²(Q)} ≤ ε ⇒ ‖𝓡_B(z^lo)‖_{L²_tH^k_x} ≤ C_j ε K^k [1 + log(2 + C_j (C_A K²) K^{k+3}/ε)]^k`
and the Dirac analogue with `k+1` and amplitude `C_A K`. -/
theorem native_low_upgrade {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A : ℝ) (k : ℕ) (t₀ t₁ : ℝ) :
    ∃ Cj CA : ℝ, 0 < Cj ∧ 0 < CA ∧ ∀ (n : ℕ) [NeZero n] (u : Grid n → FF) (K : ℝ), 1 ≤ K →
      (∀ x, (reconLow n K u x).1 ∈ Ke) → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      (∀ ε : ℝ, 0 < ε → sobX 0 (NativeSlab.slab t₀ t₁) (RB D (reconLow n K u)) ≤ ε →
        sobX k (NativeSlab.slab t₀ t₁) (RB D (reconLow n K u)) ≤
          Cj * ε * K ^ k * (1 + Real.log (2 + Cj * (CA * K ^ 2) * K ^ (k + 3) / ε)) ^ k) ∧
      (∀ ε : ℝ, 0 < ε → sobX 0 (NativeSlab.slab t₀ t₁) (RD D (reconLow n K u)) ≤ ε →
        sobX (k + 1) (NativeSlab.slab t₀ t₁) (RD D (reconLow n K u)) ≤
          Cj * ε * K ^ (k + 1) *
            (1 + Real.log (2 + Cj * (CA * K) * K ^ (k + 1 + 3) / ε)) ^ (k + 1)) := by
  obtain ⟨CG, RG, hCG, hRG, hgev⟩ := NativeLowSource.native_low_gevrey D hKe hdet A
  obtain ⟨CuB, hCuB, hupB⟩ := NativeSlab.sobX_log_upgrade
    (W := ContEulerBounds.NCLM (Mat × (Fin 4 → 𝔄) × 𝓗) ℝ) (t₀ := t₀) (t₁ := t₁) hRG k
  obtain ⟨CuD, hCuD, hupD⟩ := NativeSlab.sobX_log_upgrade
    (W := ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ) (t₀ := t₀) (t₁ := t₁) hRG (k + 1)
  refine ⟨max CuB CuD, CG + 1, lt_of_lt_of_le hCuB (le_max_left _ _), by positivity, ?_⟩
  intro n _ u K hK hKe' hA
  have hK0 : 0 < K := by linarith
  have hY : ContDiff ℝ ∞ (reconLow n K u) := contDiff_reconLow u K
  have hch := chartU_of_mem (K := K) hdet hKe'
  have hper : IsPeriodic (2 * π) (reconLow n K u) := isPeriodic_reconLow u K
  have hmono : ∀ (C C' a : ℝ) (j : ℕ) (ε : ℝ), 0 < ε → 0 ≤ a → 0 < C → C ≤ C' →
      C * ε * K ^ j * (1 + Real.log (2 + C * a * K ^ (j + 3) / ε)) ^ j ≤
        C' * ε * K ^ j * (1 + Real.log (2 + C' * a * K ^ (j + 3) / ε)) ^ j := by
    intro C C' a j ε hε ha hC hCC
    have h1 : 0 ≤ 1 + Real.log (2 + C * a * K ^ (j + 3) / ε) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + C * a * K ^ (j + 3) / ε by
        have : 0 ≤ C * a * K ^ (j + 3) / ε := by positivity
        linarith)
      linarith
    have h2 : Real.log (2 + C * a * K ^ (j + 3) / ε) ≤ Real.log (2 + C' * a * K ^ (j + 3) / ε) :=
      Real.log_le_log (by positivity) (by gcongr)
    have hε' : 0 ≤ ε * K ^ j := by positivity
    have hC' : 0 ≤ C' * (ε * K ^ j) := mul_nonneg (hC.le.trans hCC) hε'
    calc C * ε * K ^ j * (1 + Real.log (2 + C * a * K ^ (j + 3) / ε)) ^ j
        = C * (ε * K ^ j) * (1 + Real.log (2 + C * a * K ^ (j + 3) / ε)) ^ j := by ring
      _ ≤ C' * (ε * K ^ j) * (1 + Real.log (2 + C' * a * K ^ (j + 3) / ε)) ^ j := by
          gcongr
      _ = C' * ε * K ^ j * (1 + Real.log (2 + C' * a * K ^ (j + 3) / ε)) ^ j := by ring
  constructor
  · intro ε hε hL2
    have hb : ∀ (z v : R4) (p : ℕ), ‖v‖ ≤ 1 →
        ‖iteratedFDeriv ℝ p (RB D (reconLow n K u)) z (fun _ => v)‖ ≤
          (CG + 1) * K ^ 2 * (p ! * (RG * K) ^ p) := by
      intro z v p hv
      refine ((hgev n u K hK hKe' hA z v hv p).1).trans ?_
      have : 0 ≤ K ^ 2 * (p ! * (RG * K) ^ p) := by positivity
      nlinarith
    have h := hupB (RB D (reconLow n K u)) ((CG + 1) * K ^ 2) K ε (contDiff_RB D hK0 hY hch)
      (isPeriodic_RB D hper) (by positivity) hK hε hb hL2
    exact h.trans (hmono CuB (max CuB CuD) ((CG + 1) * K ^ 2) k ε hε (by positivity) hCuB
      (le_max_left _ _))
  · intro ε hε hL2
    have hb : ∀ (z v : R4) (p : ℕ), ‖v‖ ≤ 1 →
        ‖iteratedFDeriv ℝ p (RD D (reconLow n K u)) z (fun _ => v)‖ ≤
          (CG + 1) * K * (p ! * (RG * K) ^ p) := by
      intro z v p hv
      refine ((hgev n u K hK hKe' hA z v hv p).2).trans ?_
      have : 0 ≤ K * (p ! * (RG * K) ^ p) := by positivity
      nlinarith
    have h := hupD (RD D (reconLow n K u)) ((CG + 1) * K) K ε (contDiff_RD D hK0 hY hch)
      (isPeriodic_RD D hper) (by positivity) hK hε hb hL2
    exact h.trans (hmono CuD (max CuB CuD) ((CG + 1) * K) (k + 1) ε hε (by positivity) hCuD
      (le_max_right _ _))

end LowUpgrade

/-! ### The theorem -/

section Theorem

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

local notation "FJ" => ContEulerBounds.JS (Field 𝔄 𝓗 𝓢)
local notation "FF" => Field 𝔄 𝓗 𝓢

theorem sobX_nonneg {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (j : ℕ) (Q : Set R4)
    (F : R4 → W) : 0 ≤ sobX j Q F := Real.sqrt_nonneg _

/-- The triangle inequality in the form used: `‖a‖ ≤ ‖b‖ + ‖a - b‖` and `‖b‖ ≤ ‖a‖ + ‖a - b‖`
for the slab norm of the rows of two smooth fields. -/
theorem sobX_tri {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {F G : R4 → W}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (j : ℕ) (t₀ t₁ : ℝ) :
    sobX j (NativeSlab.slab t₀ t₁) F ≤ sobX j (NativeSlab.slab t₀ t₁) G +
        sobX j (NativeSlab.slab t₀ t₁) (fun x => F x - G x) ∧
      sobX j (NativeSlab.slab t₀ t₁) G ≤ sobX j (NativeSlab.slab t₀ t₁) F +
        sobX j (NativeSlab.slab t₀ t₁) (fun x => F x - G x) := by
  have hFG : ContDiff ℝ ∞ (fun x => F x - G x) := hF.sub hG
  constructor
  · have h := sobX_add_le hG hFG j t₀ t₁
    have e : G + (fun x => F x - G x) = F := by funext x; simp
    rwa [e] at h
  · have hGF : ContDiff ℝ ∞ (fun x => G x - F x) := hG.sub hF
    have h := sobX_add_le hF hGF j t₀ t₁
    have e : F + (fun x => G x - F x) = G := by funext x; simp
    rw [e] at h
    have e2 : (fun x => G x - F x) = -(fun x => F x - G x) := by funext x; simp
    rwa [e2, sobX_neg_eq] at h

open Classical in
-- the final assembly combines the four inputs of `native_source_assembly`
set_option maxHeartbeats 2000000 in
/-- **`thm:native-source`** (leakage-tolerant physical forcing estimate), all three displays.
Fix a compact coframe chart `K_e ⊂ {det e > 0}` (uniform inverse-metric margins), an amplitude
bound `A`, an order `k ≥ 1`, the budget constant `C_k > 0` of `L_{h,k}`, and buffered slabs
`Q = [t₀,t₁] × 𝕋³ ⋐ Q' = [t₀-δ, t₁+δ) × 𝕋³` inside one period of the auxiliary box.  There are
`C`, `c_res > 0`, `τ_* > 0` such that for every odd `n` (`h = 2π/n`), every record `u_h` whose
complete reconstruction `z_h` and low-frequency head `z_h^lo` lie in the chart with amplitudes
`≤ A`, every `K ≥ 1` with `hK ≤ c_res`, `τ_{h,k+2}(K) ≤ τ_*`, and every `σ_h` bounding the
finite-action covector norm `‖E_h^raw(u_h)‖_{0,h;Q'}`:
1. `eq:native-zero-source`: `‖𝓡_B(z_h)‖_{L²(Q)} + ‖𝓡_D(z_h)‖_{L²(Q)} ≤ C ε_{0,h}`;
2. `eq:native-strong-source`:
   `‖𝓡_B(z_h)‖_{L²_tH^k_x(Q)} + ‖𝓡_D(z_h)‖_{L²_tH^{k+1}_x(Q)} ≤ C F_{h,k}`;
3. `eq:native-full-Cartan`: at every point `z` of the cell of every node `x`,
   `‖R_h^{raw}(u_h)_{μν}(x) - e Riem_{μν}(g_h)(z) e⁻¹‖ ≤ C h K³`. -/
theorem native_source {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A : ℝ) (k : ℕ) (hk : 1 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ δ : ℝ} (hδ : 0 < δ)
    (h0 : δ < t₀) (h1 : t₁ + δ ≤ 2 * π) :
    ∃ C c_res τs : ℝ, 0 ≤ C ∧ 0 < c_res ∧ 0 < τs ∧ ∀ (n : ℕ) [NeZero n], Odd n →
      ∀ (u : Grid n → FF) (K σ : ℝ), 1 ≤ K → (2 * π / n) * K ≤ c_res →
      tau n K (k + 2) u ≤ τs →
      (∀ x, (reconLow n K u x).1 ∈ Ke) → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      (∀ x, (recon n u x).1 ∈ Ke) → (∀ x, ‖recon n u x‖ ≤ A) → 0 ≤ σ →
      (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
          (fun x : Grid n => pos (2 * π / n) x ∈ NativeZeroSource.bufSlab (t₀ - δ) (t₁ + δ)),
          ‖eulerRow (localAction D (2 * π / n)) (2 * π / n) u x‖ ^ 2 ≤ σ ^ 2 →
      (sobX 0 (NativeSlab.slab t₀ t₁) (RB D (recon n u)) +
          sobX 0 (NativeSlab.slab t₀ t₁) (RD D (recon n u)) ≤ C * eps0 σ (2 * π / n) K) ∧
      (sobX k (NativeSlab.slab t₀ t₁) (RB D (recon n u)) +
          sobX (k + 1) (NativeSlab.slab t₀ t₁) (RD D (recon n u)) ≤
        C * forcingBudget k Ck σ (2 * π / n) K (tau n K 2 u) (tau n K (k + 2) u)) ∧
      (∀ (x : Grid n) (z : R4), ‖z - pos (2 * π / n) x‖ ≤ 2 * π / n → ∀ μ ν : Fin 4,
        ‖cartanCurvature (2 * π / n) (coframe u) x μ ν -
          matToOp ((recon n u z).1 * riemMat (fun z => (recon n u z).1) z μ ν *
            ((recon n u z).1)⁻¹)‖ ≤ C * (2 * π / n) * K ^ 3) := by
  have ht0 : 0 ≤ t₀ := by linarith
  have ht1 : t₁ ≤ 2 * π := by linarith
  obtain ⟨Cz, cz, τz, hCz, hcz, hτz, hzero⟩ :=
    NativeZeroSource.native_zero_source D hKe hdet A hδ h0 h1
  obtain ⟨Ct, τt, hCt, hτt, htail⟩ := native_source_tail D hKe hdet A k
  obtain ⟨Cj, CA, hCj, hCA, hlow⟩ := native_low_upgrade D hKe hdet A k t₀ t₁
  set Bc : ℝ := 240 ^ 3 * (A + 1) + 1 with hBc
  obtain ⟨Cc, cc, hcc, hcart⟩ := native_cartan_riem (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) hKe hdet A Bc
  set Cas : ℝ := max (2 * Cj * (Cz + Ct + 1) *
      (1 + Real.log (max 1 (Cj * CA / ((Cz + Ct + 1) * Ck)))) ^ (k + 1)) (2 * Ct) with hCas
  have hCas0 : 0 ≤ Cas := le_trans (by positivity) (le_max_right _ _)
  refine ⟨max (max Cz Cas) Cc, min cz cc, min (min τz τt) 1,
    le_trans hCz ((le_max_left _ _).trans (le_max_left _ _)), lt_min hcz hcc,
    lt_min (lt_min hτz hτt) one_pos, ?_⟩
  intro n _ hn u K σ hK hhK hτ hKel hAl hKef hAf hσ hσb
  set h : ℝ := 2 * π / n with hhdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh0 : 0 < h := by rw [hhdef]; positivity
  have hK0 : 0 < K := by linarith
  have hτ3 : tau n K 3 u ≤ tau n K (k + 2) u := TrigInterp.tau_mono n hK0 (by omega) u
  have hτm0 : 0 ≤ tau n K (k + 2) u := TrigInterp.tau_nonneg n hK0 _ u
  have hτ20 : 0 ≤ tau n K 2 u := TrigInterp.tau_nonneg n hK0 _ u
  have hτmin : tau n K (k + 2) u ≤ min (min τz τt) 1 := hτ
  have hτz' : tau n K 3 u ≤ τz := hτ3.trans (hτmin.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hτt' : tau n K (k + 2) u ≤ τt := hτmin.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτ1 : tau n K 3 u ≤ 1 := hτ3.trans (hτmin.trans (min_le_right _ _))
  have hσ' : 0 ≤ σ := hσ
  -- (0) the zero-order source
  have hZ := hzero n hn u K σ hK (hhK.trans (min_le_left _ _)) hτz' hKel hAl hKef hAf hσ hσb
  -- the tail clauses
  obtain ⟨htk, ht2⟩ := htail n u K hK hτt' hKel hAl (NativeSlab.slab t₀ t₁)
    (NativeSlab.slab_subset_box ht0 ht1)
  -- smoothness of the rows
  have hYf : ContDiff ℝ ∞ (recon n u) := contDiff_recon u
  have hYl : ContDiff ℝ ∞ (reconLow n K u) := contDiff_reconLow u K
  have hchf := chartU_of_mem (K := K) hdet hKef
  have hchl := chartU_of_mem (K := K) hdet hKel
  have hRBf := contDiff_RB D hK0 hYf hchf
  have hRBl := contDiff_RB D hK0 hYl hchl
  have hRDf := contDiff_RD D hK0 hYf hchf
  have hRDl := contDiff_RD D hK0 hYl hchl
  have trB0 := sobX_tri hRBf hRBl 0 t₀ t₁
  have trD0 := sobX_tri hRDf hRDl 0 t₀ t₁
  have trBk := sobX_tri hRBf hRBl k t₀ t₁
  have trDk := sobX_tri hRDf hRDl (k + 1) t₀ t₁
  -- the low rows' logarithmic upgrade
  obtain ⟨hlB, hlD⟩ := hlow n u K hK hKel hAl
  -- the assembly
  have hAs := NativeSourceBudget.native_source_assembly k (σ := σ) (h := h) (K := K)
    (τ₂ := tau n K 2 u) (τm := tau n K (k + 2) u) (C₀ := Cz) (C₁ := Ct) (Cj := Cj) (CA := CA)
    (Ct := Ct)
    (eB := sobX 0 (NativeSlab.slab t₀ t₁) (RB D (recon n u)))
    (eD := sobX 0 (NativeSlab.slab t₀ t₁) (RD D (recon n u)))
    (eBlo := sobX 0 (NativeSlab.slab t₀ t₁) (RB D (reconLow n K u)))
    (eDlo := sobX 0 (NativeSlab.slab t₀ t₁) (RD D (reconLow n K u)))
    (YB := sobX k (NativeSlab.slab t₀ t₁) (RB D (recon n u)))
    (YD := sobX (k + 1) (NativeSlab.slab t₀ t₁) (RD D (recon n u)))
    (YBlo := sobX k (NativeSlab.slab t₀ t₁) (RB D (reconLow n K u)))
    (YDlo := sobX (k + 1) (NativeSlab.slab t₀ t₁) (RD D (reconLow n K u)))
    hCk hh0 hK hσ hτ20 hτm0 hCz hCt hCj hCA (sobX_nonneg _ _ _) (sobX_nonneg _ _ _) hZ
    (by
      have := trB0.2
      have hd : sobX 0 (NativeSlab.slab t₀ t₁) (fun x => RB D (recon n u) x - RB D (reconLow n K u) x) ≤
          Ct * K ^ 2 * tau n K 2 u := by
        have := sobX_nonneg 0 (NativeSlab.slab t₀ t₁) (fun x => RD D (recon n u) x - RD D (reconLow n K u) x); linarith
      linarith)
    (by
      have := trD0.2
      have hd : sobX 0 (NativeSlab.slab t₀ t₁) (fun x => RD D (recon n u) x - RD D (reconLow n K u) x) ≤
          Ct * K ^ 2 * tau n K 2 u := by
        have := sobX_nonneg 0 (NativeSlab.slab t₀ t₁) (fun x => RB D (recon n u) x - RB D (reconLow n K u) x); linarith
      linarith)
    hlB hlD
    (by
      have := trBk.1
      have hd : sobX k (NativeSlab.slab t₀ t₁) (fun x => RB D (recon n u) x - RB D (reconLow n K u) x) ≤
          Ct * K ^ (k + 2) * tau n K (k + 2) u := by
        have := sobX_nonneg (k + 1) (NativeSlab.slab t₀ t₁) (fun x => RD D (recon n u) x - RD D (reconLow n K u) x); linarith
      linarith)
    (by
      have := trDk.1
      have hd : sobX (k + 1) (NativeSlab.slab t₀ t₁)
          (fun x => RD D (recon n u) x - RD D (reconLow n K u) x) ≤
          Ct * K ^ (k + 2) * tau n K (k + 2) u := by
        have := sobX_nonneg k (NativeSlab.slab t₀ t₁) (fun x => RB D (recon n u) x - RB D (reconLow n K u) x); linarith
      linarith)
  have hF0 : 0 ≤ forcingBudget k Ck σ h K (tau n K 2 u) (tau n K (k + 2) u) := by
    unfold forcingBudget NativeRate.epsc NativeRate.logFactor eps0
    have : 0 ≤ 1 + Real.log (2 + Ck * K ^ (k + 5) / (σ + h * K ^ 3 + K ^ 2 * tau n K 2 u)) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Ck * K ^ (k + 5) /
          (σ + h * K ^ 3 + K ^ 2 * tau n K 2 u) by
        have : 0 ≤ Ck * K ^ (k + 5) / (σ + h * K ^ 3 + K ^ 2 * tau n K 2 u) := by positivity
        linarith)
      linarith
    positivity
  have he0 : 0 ≤ eps0 σ h K := by unfold eps0; positivity
  refine ⟨?_, ?_, ?_⟩
  · exact hZ.trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) he0)
  · exact hAs.trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_left _ _)) hF0)
  · -- the Cartan clause: `prop:native-consistency` for the complete field
    intro x z hz μ ν
    have hD : ∀ j, j ≤ 3 → 1 ≤ j → ∀ z, ‖iteratedFDeriv ℝ j (recon n u) z‖ ≤ Bc * K ^ j := by
      intro j hj _ z
      refine (NativeZeroSource.norm_iteratedFDeriv_recon_le u hK hAl hj z).trans ?_
      have hA0 : 0 ≤ A := (norm_nonneg _).trans (hAl 0)
      have : 240 ^ 3 * A + tau n K 3 u ≤ Bc := by rw [hBc]; nlinarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hc := hcart K hK h hh0 (hhK.trans (min_le_right _ _)) n (recon n u)
      ((contDiff_recon u).of_le (ContEulerBounds.natCast_le_infty 3))
      (NativeZeroSource.isPeriodic_recon u) hKef hAf
      (fun z => by rw [← pow_one K]; exact hD 1 (by norm_num) le_rfl z)
      (hD 2 (by norm_num) (by norm_num)) (hD 3 le_rfl (by norm_num)) x z hz μ ν
    rw [NativeZeroSource.samp_recon hn u] at hc
    refine hc.trans ?_
    have : 0 ≤ h * K ^ 3 := by positivity
    calc Cc * h * K ^ 3 = Cc * (h * K ^ 3) := by ring
      _ ≤ max (max Cz Cas) Cc * (h * K ^ 3) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) this
      _ = max (max Cz Cas) Cc * h * K ^ 3 := by ring

end Theorem

/-! ### Non-vacuity -/

section NonVacuity

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

open Classical in
/-- **Non-vacuity of `native_source`**: a constant record whose value `w` has coframe in `K_e`
satisfies every record hypothesis with `A = ‖w‖` (zero measured tail, low and complete heads equal
to `w`) for every odd `n` and `K ≥ 0`, and the finite-action hypothesis holds with
`σ = (h⁴ Σ_{x ∈ Q'_h} ‖E_h^raw(u_h)(x)‖²)^{1/2}`; the mesh condition `hK ≤ c_res` holds for `n`
large (`NativeTail` non-vacuity example). -/
theorem native_source_hyps_const (w : Field 𝔄 𝓗 𝓢) {Ke : Set Mat} (hw : w.1 ∈ Ke) {n : ℕ}
    [NeZero n] (hn : Odd n) {K : ℝ} (hK : 0 ≤ K) (k : ℕ) (Q' : Set R4) :
    tau n K (k + 2) (fun _ : Grid n => w) = 0 ∧
      (∀ x, (reconLow n K (fun _ : Grid n => w) x).1 ∈ Ke) ∧
      (∀ x, ‖reconLow n K (fun _ : Grid n => w) x‖ ≤ ‖w‖) ∧
      (∀ x, (recon n (fun _ : Grid n => w) x).1 ∈ Ke) ∧
      (∀ x, ‖recon n (fun _ : Grid n => w) x‖ ≤ ‖w‖) ∧
      (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos (2 * π / n) x ∈ Q'),
          ‖eulerRow (localAction D (2 * π / n)) (2 * π / n) (fun _ : Grid n => w) x‖ ^ 2 ≤
        (Real.sqrt ((2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
          (fun x : Grid n => pos (2 * π / n) x ∈ Q'),
          ‖eulerRow (localAction D (2 * π / n)) (2 * π / n) (fun _ : Grid n => w) x‖ ^ 2)) ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := native_tail_hyps_const w hw hn hK (k + 2)
  refine ⟨h1, h2, h3, h4, fun x => by rw [recon_const hn w x], ?_⟩
  rw [Real.sq_sqrt (by positivity)]

end NonVacuity

end

end RenewalGeometry.NativeSourceThm
