/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallUhlenbeckBall
import RenewalGeometry.Continuum.UhlenbeckCubeRescaling

/-!
# Reduction of Uhlenbeck's theorem on all balls to the unit ball by rescaling
  (stage D4 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure for `prop:critical-uhlenbeck` of the Einstein–Standard-Model
action-closure manuscript.

The four-dimensional Yang–Mills energy and the `L⁴` norm of a connection are scale invariant, the
Coulomb condition is preserved by affine changes of variables and gauge transformations commute
with them (`UhlenbeckCube.affConn`, `UhlenbeckCube.gaugeConn_comp_affInv`,
`UhlenbeckCube.curvEnergy_affConn`).  Hence:

* `uhlenbeckIn_of_ball01` (**reduction**): for `𝔤` closed under real scalars,
  `UhlenbeckBallIn 0 1 m G 𝔤 → UhlenbeckGauge.UhlenbeckSmallEnergyGaugeIn m G 𝔤`, with `C_U`
  unchanged and `C_r = (r + 1) C₀`.  (Same argument as `UhlenbeckCube.cubeIn_of_Q0In`, with the
  affine map `x ↦ c + r x` sending the unit ball onto `B_r(c)`.)
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.UhlenbeckRescale

open SobolevOpen CriticalGauge CriticalQuotient UhlenbeckGauge CubeNeumann UhlenbeckCube
  UhlenbeckBall

set_option linter.unusedSectionVars false

variable {m : ℕ}

theorem affMap_preimage_eBall (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) :
    affMap c r ⁻¹' eBall c r = eBall 0 1 := by
  ext y
  simp only [mem_preimage, eBall, mem_setOf_eq, affMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply, sub_zero, one_pow]
  have e : ∀ i, (c i + r * y i - c i) ^ 2 = r ^ 2 * y i ^ 2 := fun i => by ring
  simp only [e, ← Finset.mul_sum]
  exact mul_lt_iff_lt_one_right (by positivity)

theorem affInv_preimage_eBall (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) :
    affInv c r ⁻¹' eBall 0 1 = eBall c r := by
  rw [preimage_affInv_eq_image hr.ne', ← affMap_preimage_eBall c hr, image_preimage_eq _ ?_]
  intro y; exact ⟨affInv _ _ y, affMap_affInv hr.ne' y⟩

/-- **Reduction of Uhlenbeck's theorem on all balls to the unit ball** by affine rescaling
(scale invariance of the energy and of the `L⁴` norm). -/
theorem uhlenbeckIn_of_ball01 {G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)}
    (h𝔤 : ∀ (s : ℝ), ∀ X ∈ 𝔤, (s : ℂ) • X ∈ 𝔤) (hQ : UhlenbeckBallIn 0 1 m G 𝔤) :
    UhlenbeckSmallEnergyGaugeIn m G 𝔤 := by
  obtain ⟨εU, hεU, CU, C0, hU⟩ := hQ
  refine ⟨εU, hεU, CU, fun c r hr => ?_⟩
  have hL : 0 < r := hr
  refine ⟨C0 * (r + 1).toNNReal, fun A hA h𝔤A hE => ?_⟩
  set Ah := affConn c r A
  have hEeq : curvEnergy Ah (eBall 0 1) = curvEnergy A (eBall c r) := by
    rw [← affMap_preimage_eBall c hr]; exact curvEnergy_affConn hL A _
  obtain ⟨Rh, hRG, hRs, hRC, hRW, hRw, hR4⟩ := hU Ah (isSmoothUnitaryConn_affConn hA c r)
    (fun μ y => h𝔤 r _ (h𝔤A μ _)) (hEeq ▸ hE)
  rw [hEeq] at hRw hR4
  set R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ := fun y => Rh (affInv c r y)
  have hmaps : ∀ y ∈ eBall c r, affInv c r y ∈ (eBall 0 1) := fun y hy => by
    rw [← affInv_preimage_eBall c hr] at hy; exact hy
  have hpre : affInv c r ⁻¹' (eBall 0 1) = eBall c r := affInv_preimage_eBall c hr
  have hLinv : ‖((r⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal r⁻¹ := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hL)]
  refine ⟨R, fun y hy => hRG _ (hmaps y hy), fun c' e' => ?_, fun x hx c' e' => ?_,
    fun ν c' e' => ?_, fun ν c' e' => ?_, fun ν c' e' => ?_⟩
  · exact (hRs c' e').comp (contDiff_affInv c r).contDiffOn hmaps
  · simp only [R, entryGrad_gaugeConn_comp_affInv hL.ne']
    rw [← Finset.mul_sum, ← Finset.mul_sum, hRC _ (hmaps x hx) c' e', mul_zero, mul_zero]
  · have h1 := memW12_comp_affInv (z := c) hL (hRW ν c' e')
    rw [hpre] at h1
    have h2 := memW12_const_mul h1 ((r⁻¹ : ℝ) : ℂ)
    rw [entries_gaugeConn_comp_affInv hL.ne']
    convert h2 using 2
    funext y
    exact entryGrad_gaugeConn_comp_affInv hL.ne' Rh A ν c' e' _ y
  · -- the `W^{1,2}` bound
    rw [entries_gaugeConn_comp_affInv hL.ne']
    have hg : (entryGrad (gaugeConn R A) ν c' e') = fun i y => ((r⁻¹ : ℝ) : ℂ) *
        (((r⁻¹ : ℝ) : ℂ) * entryGrad (gaugeConn Rh Ah) ν c' e' i (affInv c r y)) := by
      funext i y; exact entryGrad_gaugeConn_comp_affInv hL.ne' Rh A ν c' e' i y
    rw [hg, w12Norm_const_mul, hLinv]
    have hW := hRW ν c' e'
    have hu := memLp_comp_affInv (z := c) hL (by norm_num) hW.memLp
    have hgi := fun i => memLp_comp_affInv (z := c) hL (by norm_num) (hW.memLp_grad i)
    rw [hpre] at hu
    simp only [hpre] at hgi
    unfold w12Norm
    have e2 : ∀ i, eLpNorm (fun y => ((r⁻¹ : ℝ) : ℂ) * entryGrad (gaugeConn Rh Ah) ν c' e' i
        (affInv c r y)) 2 (volume.restrict (eBall c r)) =
        ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (r ^ 4) ^ (1 / (2 : ℝ≥0∞)).toReal *
          eLpNorm (entryGrad (gaugeConn Rh Ah) ν c' e' i) 2 (volume.restrict (eBall 0 1))) := by
      intro i
      rw [show (fun y => ((r⁻¹ : ℝ) : ℂ) * entryGrad (gaugeConn Rh Ah) ν c' e' i (affInv c r y)) =
        ((r⁻¹ : ℝ) : ℂ) • fun y => entryGrad (gaugeConn Rh Ah) ν c' e' i (affInv c r y) from rfl,
        eLpNorm_const_smul, hLinv, (hgi i).2]
    rw [hu.2]
    simp only [e2]
    have hsq : ENNReal.ofReal (r ^ 4) ^ (1 / (2 : ℝ≥0∞)).toReal = ENNReal.ofReal (r ^ 2) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [show (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul hL.le]
      norm_num
    rw [hsq]
    set W0 := w12Norm (eBall 0 1) (entries (gaugeConn Rh Ah) ν c' e') (entryGrad (gaugeConn Rh Ah) ν c' e')
    have hW0 := hRw ν c' e'
    -- `r⁻¹ (L² ‖u‖ + Σ r⁻¹ L² ‖g‖) ≤ (r + 1) W0`
    have hcoef1 : ENNReal.ofReal r⁻¹ * ENNReal.ofReal (r ^ 2) = ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
    have hcoef2 : ENNReal.ofReal r⁻¹ * ENNReal.ofReal r⁻¹ * ENNReal.ofReal (r ^ 2) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      rw [show r⁻¹ * r⁻¹ * r ^ 2 = 1 by field_simp]; simp
    calc ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (r ^ 2) *
          eLpNorm (entries (gaugeConn Rh Ah) ν c' e') 2 (volume.restrict (eBall 0 1)) +
          ∑ i, ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (r ^ 2) *
            eLpNorm (entryGrad (gaugeConn Rh Ah) ν c' e' i) 2 (volume.restrict (eBall 0 1))))
        = ENNReal.ofReal r * eLpNorm (entries (gaugeConn Rh Ah) ν c' e') 2 (volume.restrict (eBall 0 1)) +
          ∑ i, eLpNorm (entryGrad (gaugeConn Rh Ah) ν c' e' i) 2 (volume.restrict (eBall 0 1)) := by
          rw [mul_add, ← mul_assoc, hcoef1, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← mul_assoc, ← mul_assoc, hcoef2, one_mul]
      _ ≤ (ENNReal.ofReal r + 1) * W0 := by
          unfold W0 w12Norm
          rw [add_mul, one_mul, mul_add]
          gcongr ?_ + ?_
          · exact le_self_add
          · exact le_add_left le_rfl
      _ ≤ (ENNReal.ofReal r + 1) * (C0 * curvEnergy A (eBall c r) ^ (1 / 2 : ℝ)) := by gcongr
      _ = ((C0 * (r + 1).toNNReal : ℝ≥0) : ℝ≥0∞) * curvEnergy A (eBall c r) ^ (1 / 2 : ℝ) := by
          have hc : ((C0 * (r + 1).toNNReal : ℝ≥0) : ℝ≥0∞) = C0 * (ENNReal.ofReal r + 1) := by
            rw [ENNReal.coe_mul]
            congr 1
            rw [show (((r + 1).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (r + 1) from rfl,
              ENNReal.ofReal_add hL.le zero_le_one, ENNReal.ofReal_one]
          rw [hc]; ring
  · -- the `L⁴` bound (scale invariant)
    rw [entries_gaugeConn_comp_affInv hL.ne']
    have hm4 : MemLp (entries (gaugeConn Rh Ah) ν c' e') 4 (volume.restrict (eBall 0 1)) :=
      ⟨(hRW ν c' e').memLp.1, (hR4 ν c' e').trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          (ne_top_of_le_ne_top ENNReal.coe_ne_top hE)))⟩
    have h4 := memLp_comp_affInv (z := c) hL (by norm_num) hm4
    rw [hpre] at h4
    rw [show (fun y => ((r⁻¹ : ℝ) : ℂ) * entries (gaugeConn Rh Ah) ν c' e' (affInv c r y)) =
      ((r⁻¹ : ℝ) : ℂ) • fun y => entries (gaugeConn Rh Ah) ν c' e' (affInv c r y) from rfl,
      eLpNorm_const_smul, hLinv, h4.2]
    have hq : ENNReal.ofReal (r ^ 4) ^ (1 / (4 : ℝ≥0∞)).toReal = ENNReal.ofReal r := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [show (1 / (4 : ℝ≥0∞)).toReal = 1 / 4 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul hL.le]
      norm_num
    rw [hq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hL.ne',
      ENNReal.ofReal_one, one_mul]
    exact hR4 ν c' e'


end RenewalGeometry.BallAnalysis.UhlenbeckRescale
