/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSlabFourierBridge
import RenewalGeometry.Continuum.CoupledBootstrapSlabModel
import RenewalGeometry.Analysis.PeriodicCubeSobolevInterpolation

/-!
# Spatial Sobolev norms on slabs: Leibniz bounds, dilation and interpolation

Generic infrastructure (no renewal notions) for the source-budget comparison of
`thm:native-closure` (Einstein–Standard-Model action-closure manuscript): the slab residuals of
the actual tuple of a native record are `M(e(ξ))𝓡(ξ)` with algebraic coefficient maps, and their
space-time Sobolev norms are compared with those of the native Euler rows.

Norms: `NativeTail.dX j F z` is the `j`-th spatial derivative (operator norm on `ℝ³` with the sup
norm), `NativeTail.sobXSq k Q F = ∫_Q Σ_{j ≤ k} ‖D^j_x F‖²` (`L²_tH^k_x(Q)`), on the slabs
`NativeSlab.slab t₀ t₁ = [t₀, t₁] × (0, 2π]³`.

## Main results

* `iteratedFDeriv_spatial` — `D^j_y[F(z + ι(y))] = D^j_xF(z + ι(y))`.
* **`norm_dX_clm_apply_le`** — Leibniz: `‖D^j_x(a·b)‖ ≤ Σ_i C(j,i)‖D^i_x a‖‖D^{j-i}_x b‖`.
* **`sum_norm_dX_clm_apply_sq_le`**, **`sobXSq_clm_apply_le`** — if `‖D^i_x a‖ ≤ A_i` on the slab,
  `‖a·b‖²_{L²H^k} ≤ (k+1)²4^k Σ_{i ≤ k} A_i² ‖b‖²_{L²H^{k-i}}`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff

namespace RenewalGeometry.SourceCompare

open DiscreteEulerConsistency (R4)
open NativeTail (dX sobXSq spatialL)

noncomputable section

set_option linter.unusedSectionVars false

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-! ### Spatial derivatives as derivatives of the spatial restriction -/

/-- **`D^j_y[F(z + ι(y))] = D^j_xF(z + ι(y))`** (`ι` the spatial inclusion). -/
theorem iteratedFDeriv_spatial {F : R4 → W} (hF : ContDiff ℝ ∞ F) (z : R4) (j : ℕ)
    (y : Fin 3 → ℝ) :
    iteratedFDeriv ℝ j (fun y => F (z + spatialL y)) y = dX j F (z + spatialL y) := by
  have hfun : (fun y => F (z + spatialL y)) = (fun w => F (z + w)) ∘ spatialL := rfl
  have hg : ContDiff ℝ ∞ (fun w => F (z + w)) := hF.comp (contDiff_const.add contDiff_id)
  rw [hfun, spatialL.iteratedFDeriv_comp_right hg y (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left]
  rfl

theorem contDiff_spatial {F : R4 → W} (hF : ContDiff ℝ ∞ F) (z : R4) :
    ContDiff ℝ ∞ (fun y : Fin 3 → ℝ => F (z + spatialL y)) :=
  hF.comp (contDiff_const.add spatialL.contDiff)

/-- **Leibniz for spatial derivatives**: `‖D^j_x(a·b)(z)‖ ≤ Σ_i C(j,i)‖D^i_x a(z)‖‖D^{j-i}_x b(z)‖`. -/
theorem norm_dX_clm_apply_le {a : R4 → W →L[ℝ] V} {b : R4 → W} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (j : ℕ) (z : R4) :
    ‖dX j (fun ξ => a ξ (b ξ)) z‖ ≤ ∑ i ∈ range (j + 1),
      (j.choose i : ℝ) * ‖dX i a z‖ * ‖dX (j - i) b z‖ := by
  have hz : z = z + spatialL 0 := by simp
  have h := norm_iteratedFDeriv_clm_apply (contDiff_spatial ha z) (contDiff_spatial hb z)
    (0 : Fin 3 → ℝ) (n := j) (by exact_mod_cast le_top)
  have e1 : iteratedFDeriv ℝ j (fun y => a (z + spatialL y) (b (z + spatialL y))) 0 =
      dX j (fun ξ => a ξ (b ξ)) z := by
    rw [iteratedFDeriv_spatial (F := fun ξ => a ξ (b ξ)) (ha.clm_apply hb) z j 0]
    simp
  rw [e1] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [iteratedFDeriv_spatial ha z i 0, iteratedFDeriv_spatial hb z (j - i) 0]
  simp

/-- The partial Sobolev density `Σ_{l ≤ k} ‖D^l_x b‖²`. -/
def hDens (k : ℕ) (b : R4 → W) (z : R4) : ℝ := ∑ l ∈ range (k + 1), ‖dX l b z‖ ^ 2

theorem hDens_nonneg (k : ℕ) (b : R4 → W) (z : R4) : 0 ≤ hDens k b z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_dX_le_sqrt_hDens {k l : ℕ} (hl : l ≤ k) (b : R4 → W) (z : R4) :
    ‖dX l b z‖ ≤ Real.sqrt (hDens k b z) := by
  rw [← Real.sqrt_sq (norm_nonneg (dX l b z))]
  refine Real.sqrt_le_sqrt ?_
  exact Finset.single_le_sum (f := fun l => ‖dX l b z‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hl))

/-- **Pointwise Sobolev bound for `a·b`**: if `‖D^i_x a(z)‖ ≤ A_i` (`i ≤ k`), then
`Σ_{j ≤ k}‖D^j_x(a·b)(z)‖² ≤ (k+1)²4^k Σ_{i ≤ k} A_i² Σ_{l ≤ k-i}‖D^l_x b(z)‖²`. -/
theorem sum_norm_dX_clm_apply_sq_le {a : R4 → W →L[ℝ] V} {b : R4 → W} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (k : ℕ) (z : R4) {A : ℕ → ℝ} (hA0 : ∀ i, 0 ≤ A i)
    (hA : ∀ i ≤ k, ‖dX i a z‖ ≤ A i) :
    hDens k (fun ξ => a ξ (b ξ)) z ≤
      ((k + 1) ^ 2 * 4 ^ k : ℝ) * ∑ i ∈ range (k + 1), A i ^ 2 * hDens (k - i) b z := by
  have hterm : ∀ j ∈ range (k + 1), ‖dX j (fun ξ => a ξ (b ξ)) z‖ ≤
      ∑ i ∈ range (k + 1), 2 ^ k * A i * Real.sqrt (hDens (k - i) b z) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    refine (norm_dX_clm_apply_le ha hb j z).trans ?_
    calc ∑ i ∈ range (j + 1), (j.choose i : ℝ) * ‖dX i a z‖ * ‖dX (j - i) b z‖
        ≤ ∑ i ∈ range (j + 1), 2 ^ k * A i * Real.sqrt (hDens (k - i) b z) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          have h1 : (j.choose i : ℝ) ≤ 2 ^ k := by
            have : (j.choose i : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.choose_le_two_pow j i
            exact this.trans (pow_le_pow_right₀ (by norm_num) hjk)
          have h2 := hA i (hij.trans hjk)
          have h3 : ‖dX (j - i) b z‖ ≤ Real.sqrt (hDens (k - i) b z) :=
            norm_dX_le_sqrt_hDens (by omega) b z
          have := mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3
            (norm_nonneg _) (mul_nonneg (by positivity) (hA0 i))
          exact this
      _ ≤ ∑ i ∈ range (k + 1), 2 ^ k * A i * Real.sqrt (hDens (k - i) b z) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            fun i _ _ => mul_nonneg (mul_nonneg (by positivity) (hA0 i)) (Real.sqrt_nonneg _)
  have hsq : ∀ j ∈ range (k + 1), ‖dX j (fun ξ => a ξ (b ξ)) z‖ ^ 2 ≤
      (k + 1) * ∑ i ∈ range (k + 1), 4 ^ k * A i ^ 2 * hDens (k - i) b z := by
    intro j hj
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hterm j hj) 2
    refine h1.trans ?_
    refine (sq_sum_le_card_mul_sum_sq).trans (le_of_eq ?_)
    rw [Finset.card_range]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (hDens_nonneg _ _ _), ← pow_mul,
      show k * 2 = 2 * k by ring, pow_mul]
    norm_num
  calc hDens k (fun ξ => a ξ (b ξ)) z
      ≤ ∑ j ∈ range (k + 1), ((k : ℝ) + 1) * ∑ i ∈ range (k + 1), 4 ^ k * A i ^ 2 *
          hDens (k - i) b z := Finset.sum_le_sum hsq
    _ = ((k + 1) ^ 2 * 4 ^ k : ℝ) * ∑ i ∈ range (k + 1), A i ^ 2 * hDens (k - i) b z := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring

theorem continuous_hDens {b : R4 → W} (hb : ContDiff ℝ ∞ b) (k : ℕ) : Continuous (hDens k b) :=
  continuous_finset_sum _ fun l _ => (NativeSlab.continuous_dX hb l).norm.pow 2

theorem sobXSq_eq_integral_hDens (k : ℕ) (Q : Set R4) (b : R4 → W) :
    sobXSq k Q b = ∫ z in Q, hDens k b z := rfl

/-- **Integrated Sobolev bound for `a·b` on a slab.** -/
theorem sobXSq_clm_apply_le {a : R4 → W →L[ℝ] V} {b : R4 → W} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (k : ℕ) (t₀ t₁ : ℝ) {A : ℕ → ℝ} (hA0 : ∀ i, 0 ≤ A i)
    (hA : ∀ z ∈ NativeSlab.slab t₀ t₁, ∀ i ≤ k, ‖dX i a z‖ ≤ A i) :
    sobXSq k (NativeSlab.slab t₀ t₁) (fun ξ => a ξ (b ξ)) ≤
      ((k + 1) ^ 2 * 4 ^ k : ℝ) * ∑ i ∈ range (k + 1),
        A i ^ 2 * sobXSq (k - i) (NativeSlab.slab t₀ t₁) b := by
  rw [sobXSq_eq_integral_hDens]
  have hint1 : IntegrableOn (hDens k fun ξ => a ξ (b ξ)) (NativeSlab.slab t₀ t₁) :=
    NativeSlab.integrableOn_slab (continuous_hDens (ha.clm_apply hb) k) t₀ t₁
  have hint2 : ∀ i, IntegrableOn (hDens (k - i) b) (NativeSlab.slab t₀ t₁) := fun i =>
    NativeSlab.integrableOn_slab (continuous_hDens hb (k - i)) t₀ t₁
  have hint3 : IntegrableOn (fun z => ((k + 1) ^ 2 * 4 ^ k : ℝ) *
      ∑ i ∈ range (k + 1), A i ^ 2 * hDens (k - i) b z) (NativeSlab.slab t₀ t₁) :=
    (integrable_finset_sum _ fun i _ => (hint2 i).const_mul _).const_mul _
  calc ∫ z in NativeSlab.slab t₀ t₁, hDens k (fun ξ => a ξ (b ξ)) z
      ≤ ∫ z in NativeSlab.slab t₀ t₁, ((k + 1) ^ 2 * 4 ^ k : ℝ) *
          ∑ i ∈ range (k + 1), A i ^ 2 * hDens (k - i) b z :=
        setIntegral_mono_on hint1 hint3 (NativeSlab.measurableSet_slab t₀ t₁) fun z hz =>
          sum_norm_dX_clm_apply_sq_le ha hb k z hA0 (hA z hz)
    _ = ((k + 1) ^ 2 * 4 ^ k : ℝ) * ∑ i ∈ range (k + 1),
          A i ^ 2 * sobXSq (k - i) (NativeSlab.slab t₀ t₁) b := by
        rw [integral_const_mul, integral_finset_sum _ fun i _ => (hint2 i).const_mul _]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul]
        rfl

/-! ### Fubini on the slab -/

theorem unitCube_ae_eq_Icc :
    (SobolevOpen.unitCube : Set (Fin 3 → ℝ)) =ᵐ[volume] Icc (0 : Fin 3 → ℝ) 1 := by
  have e : (SobolevOpen.unitCube : Set (Fin 3 → ℝ)) =
      Set.pi univ fun _ => Ioc (0 : ℝ) 1 := by
    ext y; simp [SobolevOpen.unitCube]
  rw [e]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

theorem continuous_slice_integral {H : R4 → ℝ} (hH : Continuous H) :
    Continuous fun s : ℝ => ∫ y in Icc (0 : Fin 3 → ℝ) 1, H (NativeSlab.spt s y) := by
  have hc : Continuous (fun p : ℝ × (Fin 3 → ℝ) => H (NativeSlab.spt p.1 p.2)) :=
    hH.comp NativeSlab.continuous_spt
  exact continuous_parametric_integral_of_continuous (f := fun s y => H (NativeSlab.spt s y)) hc
    isCompact_Icc

/-- **Fubini and dilation on the slab** (real form):
`∫_Q H = (2π)³ ∫_{t₀}^{t₁} ∫_{[0,1]³} H(t, 2πy) dy dt` for continuous `H ≥ 0`. -/
theorem integral_slab_slices {H : R4 → ℝ} (hH : Continuous H) (h0 : ∀ z, 0 ≤ H z) {t₀ t₁ : ℝ}
    (h01 : t₀ ≤ t₁) :
    ∫ z in NativeSlab.slab t₀ t₁, H z =
      (2 * π) ^ 3 * ∫ s in t₀..t₁, ∫ y in Icc (0 : Fin 3 → ℝ) 1, H (NativeSlab.spt s y) := by
  have hφ0 : ∀ s, 0 ≤ ∫ y in Icc (0 : Fin 3 → ℝ) 1, H (NativeSlab.spt s y) := fun s =>
    setIntegral_nonneg measurableSet_Icc fun y _ => h0 _
  have hφc := continuous_slice_integral hH
  have hL : 0 ≤ ∫ z in NativeSlab.slab t₀ t₁, H z := setIntegral_nonneg
    (NativeSlab.measurableSet_slab t₀ t₁) fun z _ => h0 z
  have hR : 0 ≤ (2 * π) ^ 3 * ∫ s in t₀..t₁, ∫ y in Icc (0 : Fin 3 → ℝ) 1, H (NativeSlab.spt s y) :=
    mul_nonneg (by positivity) (intervalIntegral.integral_nonneg h01 fun s _ => hφ0 s)
  rw [← ENNReal.ofReal_eq_ofReal_iff hL hR]
  rw [ofReal_integral_eq_lintegral_ofReal (NativeSlab.integrableOn_slab hH t₀ t₁)
    (Eventually.of_forall h0)]
  have hsl := NativeSlab.lintegral_slab t₀ t₁ (G := fun z => ENNReal.ofReal (H z))
    (ENNReal.measurable_ofReal.comp hH.measurable)
  rw [hsl]
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [intervalIntegral.integral_of_le h01, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal (hφc.continuousOn.integrableOn_compact isCompact_Icc)
      (Eventually.of_forall hφ0)]
  refine setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  have hint : IntegrableOn (fun y => H (NativeSlab.spt s y)) (Icc (0 : Fin 3 → ℝ) 1) :=
    (hH.comp (NativeSlab.continuous_spt.comp (Continuous.prodMk_right s))).continuousOn
      |>.integrableOn_compact isCompact_Icc
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => h0 _)]
  exact setLIntegral_congr unitCube_ae_eq_Icc

/-! ### The dilation from the `2π` slab to the unit-period slab -/

open SlabSobAlg (Q wordsLE sd) in
theorem aff_cons (t₀ t : ℝ) (y : Fin 3 → ℝ) :
    (2 * π) • (Fin.cons t y : R4) + Pi.single 0 t₀ = NativeSlab.spt (2 * π * t + t₀) y := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [NativeSlab.spt]
  | succ i => simp [NativeSlab.spt, Pi.single_apply, Fin.succ_ne_zero]

/-- The number of spatial words of length `≤ k`. -/
def nWords (k : ℕ) : ℝ := ((SlabSobAlg.wordsLE 3 k).card : ℝ)

/-- **The slice norm of a dilated field**: for `f(x) = G(2πx + t₀e₀)`,
`Q_k f(t) ≤ N_k (2π)^{2k} ∫_{[0,1]³} Σ_{j ≤ k}‖D^j_xG(2πt + t₀, 2πy)‖² dy`. -/
theorem Q_dil_le {G : R4 → ℝ} (hG : ContDiff ℝ ∞ G) (k : ℕ) (t₀ t : ℝ) :
    SlabSobAlg.Q k (fun x => G ((2 * π) • x + Pi.single 0 t₀)) t ≤
      nWords k * (2 * π) ^ (2 * k) *
        ∫ y in Icc (0 : Fin 3 → ℝ) 1, hDens k G (NativeSlab.spt (2 * π * t + t₀) y) := by
  set f : R4 → ℝ := fun x => G ((2 * π) • x + Pi.single 0 t₀) with hf
  have hfs : ContDiff ℝ ∞ f := hG.comp ((contDiff_const_smul _).add contDiff_const)
  have hslice : (fun y : Fin 3 → ℝ => f (Fin.cons t y)) =
      fun y => G (NativeSlab.spt (2 * π * t + t₀) y) := by
    funext y; simp only [hf, aff_cons]
  have h2π : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  have hterm : ∀ w ∈ SlabSobAlg.wordsLE 3 k, ∀ y,
      SlabSobAlg.sd w f (Fin.cons t y) ^ 2 ≤
        (2 * π) ^ (2 * k) * hDens k G (NativeSlab.spt (2 * π * t + t₀) y) := by
    intro w hw y
    have hlen : w.length ≤ k := SlabSobAlg.mem_wordsLE.1 hw
    have h1 := QLEnergy.abs_sd_le hfs t w y
    have hsl : QLEnergy.slice f t = fun y => G (NativeSlab.spt (2 * π * t + t₀) y) := hslice
    rw [hsl, NativeSlab.iteratedFDeriv_comp_spt hG, norm_smul,
      Real.norm_of_nonneg (by positivity)] at h1
    have h2 : |SlabSobAlg.sd w f (Fin.cons t y)| ≤
        (2 * π) ^ k * ‖dX w.length G (NativeSlab.spt (2 * π * t + t₀) y)‖ :=
      h1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h2π hlen) (norm_nonneg _))
    have h3 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs, mul_pow, ← pow_mul, mul_comm k 2] at h3
    refine h3.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Finset.single_le_sum (f := fun l => ‖dX l G (NativeSlab.spt (2 * π * t + t₀) y)‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hlen))
  have hcH : Continuous fun y => hDens k G (NativeSlab.spt (2 * π * t + t₀) y) :=
    (continuous_hDens hG k).comp (NativeSlab.continuous_spt.comp (Continuous.prodMk_right _))
  unfold SlabSobAlg.Q
  calc ∑ w ∈ SlabSobAlg.wordsLE 3 k, ∫ y in Icc (0 : Fin 3 → ℝ) 1, SlabSobAlg.sd w f (Fin.cons t y) ^ 2
      ≤ ∑ w ∈ SlabSobAlg.wordsLE 3 k, ∫ y in Icc (0 : Fin 3 → ℝ) 1,
          (2 * π) ^ (2 * k) * hDens k G (NativeSlab.spt (2 * π * t + t₀) y) := by
        refine Finset.sum_le_sum fun w hw => ?_
        refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun y _ => hterm w hw y
        · exact (((SlabSobAlg.contDiff_sd w hfs).continuous.comp
            (continuous_const.finCons continuous_id)).pow 2).continuousOn.integrableOn_compact
              isCompact_Icc
        · exact (hcH.const_mul _).continuousOn.integrableOn_compact isCompact_Icc
    _ = nWords k * (2 * π) ^ (2 * k) *
          ∫ y in Icc (0 : Fin 3 → ℝ) 1, hDens k G (NativeSlab.spt (2 * π * t + t₀) y) := by
        rw [Finset.sum_const, nsmul_eq_mul, integral_const_mul, nWords]
        ring

/-- **The unit-period slab norm of a dilated field family is controlled by the `2π`-slab norm**:
for `f_i(x) = G_i(2πx + t₀e₀)` and `T = (t₁ - t₀)/(2π)`,
`‖f‖²_{L²(0,T;H^k)} ≤ N_k(2π)^{2k-4} Σ_i ‖G_i‖²_{L²_tH^k_x([t₀,t₁]×(0,2π]³)}`. -/
theorem l2Sq_dil_le {ι : Type*} [Fintype ι] {G : ι → R4 → ℝ} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (k : ℕ) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) :
    CoupledBootstrap.l2Sq k ((t₁ - t₀) / (2 * π))
        (fun i x => G i ((2 * π) • x + Pi.single 0 t₀)) ≤
      nWords k * (2 * π) ^ (2 * k) / (2 * π) ^ 4 *
        ∑ i, sobXSq k (NativeSlab.slab t₀ t₁) (G i) := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hT : 0 ≤ (t₁ - t₀) / (2 * π) := div_nonneg (by linarith) h2π.le
  set φ : ι → ℝ → ℝ := fun i s =>
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, hDens k (G i) (NativeSlab.spt s y) with hφ
  have hφc : ∀ i, Continuous (φ i) := fun i => continuous_slice_integral (continuous_hDens (hG i) k)
  have hfs : ∀ i, ContDiff ℝ ∞ (fun x : R4 => G i ((2 * π) • x + Pi.single 0 t₀)) := fun i =>
    (hG i).comp ((contDiff_const_smul _).add contDiff_const)
  unfold CoupledBootstrap.l2Sq
  calc ∫ t in (0 : ℝ)..(t₁ - t₀) / (2 * π),
        ∑ i, SlabSobAlg.Q k (fun x => G i ((2 * π) • x + Pi.single 0 t₀)) t
      ≤ ∫ t in (0 : ℝ)..(t₁ - t₀) / (2 * π),
          ∑ i, nWords k * (2 * π) ^ (2 * k) * φ i (2 * π * t + t₀) := by
        refine intervalIntegral.integral_mono_on hT ?_ ?_ fun t _ =>
          Finset.sum_le_sum fun i _ => Q_dil_le (hG i) k t₀ t
        · exact (continuous_finsetSum _ fun i _ => SlabSobAlg.continuous_Q k (hfs i)).intervalIntegrable _ _
        · exact (continuous_finsetSum _ fun i _ => continuous_const.mul ((hφc i).comp
            ((continuous_const.mul continuous_id).add continuous_const))).intervalIntegrable _ _
    _ = nWords k * (2 * π) ^ (2 * k) * ∑ i, ∫ t in (0 : ℝ)..(t₁ - t₀) / (2 * π),
          φ i (2 * π * t + t₀) := by
        have hint : ∀ i ∈ (Finset.univ : Finset ι), IntervalIntegrable
            (fun t : ℝ => φ i (2 * π * t + t₀)) MeasureTheory.volume 0 ((t₁ - t₀) / (2 * π)) :=
          fun i _ => ((hφc i).comp ((continuous_const.mul continuous_id).add
            continuous_const)).intervalIntegrable _ _
        simp_rw [← Finset.mul_sum]
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum hint]
    _ = nWords k * (2 * π) ^ (2 * k) / (2 * π) ^ 4 *
          ∑ i, sobXSq k (NativeSlab.slab t₀ t₁) (G i) := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        congr 1
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_comp_mul_add (fun s => φ i s) h2π.ne' t₀, smul_eq_mul,
          sobXSq_eq_integral_hDens,
          integral_slab_slices (continuous_hDens (hG i) k) (hDens_nonneg k (G i)) h01]
        have e1 : 2 * π * 0 + t₀ = t₀ := by ring
        have e2 : 2 * π * ((t₁ - t₀) / (2 * π)) + t₀ = t₁ := by field_simp; ring
        rw [e1, e2]
        field_simp
        ring

/-! ### Interpolation on the slab -/

/-- Single-step periodicity implies lattice periodicity. -/
theorem zper_of_single {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    {f : (ι → ℝ) → α} {L : ℝ} (hf : ∀ x μ, f (x + Pi.single μ L) = f x) (k : ι → ℤ)
    (x : ι → ℝ) : f (x + L • PeriodicCube.zvec k) = f x := by
  have h1 : ∀ (m : ℤ) (μ : ι) (x : ι → ℝ), f (x + m • (Pi.single μ L : ι → ℝ)) = f x := by
    intro m μ
    induction m using Int.induction_on with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [add_zsmul, one_zsmul, ← add_assoc, hf, ih]
    | pred i ih =>
      intro x
      calc f (x + (-(i : ℤ) - 1) • (Pi.single μ L : ι → ℝ))
          = f (x + (-(i : ℤ) - 1) • (Pi.single μ L : ι → ℝ) + Pi.single μ L) := (hf _ _).symm
        _ = f (x + (-(i : ℤ)) • (Pi.single μ L : ι → ℝ)) := by
          congr 1
          rw [add_assoc, ← add_one_zsmul]
          congr 2
          ring
        _ = f x := ih x
  have hsum : L • PeriodicCube.zvec k = ∑ μ, k μ • (Pi.single μ L : ι → ℝ) := by
    funext i
    simp [PeriodicCube.zvec, Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [hsum]
  have h2 : ∀ s : Finset ι, ∀ x, f (x + ∑ μ ∈ s, k μ • (Pi.single μ L : ι → ℝ)) = f x := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | insert a s ha ih =>
      intro x
      rw [Finset.sum_insert ha]
      have e : x + (k a • (Pi.single a L : ι → ℝ) + ∑ μ ∈ s, k μ • (Pi.single μ L : ι → ℝ)) =
          (x + ∑ μ ∈ s, k μ • (Pi.single μ L : ι → ℝ)) + k a • (Pi.single a L : ι → ℝ) := by abel
      rw [e, h1, ih]
  exact h2 _ x

variable [FiniteDimensional ℝ W]

theorem norm_sq_le_pw {g : (Fin 3 → ℝ) → W} (j : ℕ) (y : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ j g y‖ ^ 2 ≤ 3 ^ j * PeriodicSobInterp.pw g j y := by
  have h1 := QLEnergy.norm_le_sum_basis (iteratedFDeriv ℝ j g y)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine h2.trans ((sq_sum_le_card_mul_sum_sq).trans (le_of_eq ?_))
  simp [PeriodicSobInterp.pw, Fintype.card_fun]

theorem pw_le_norm_sq {g : (Fin 3 → ℝ) → W} (j : ℕ) (y : Fin 3 → ℝ) :
    PeriodicSobInterp.pw g j y ≤ 3 ^ j * ‖iteratedFDeriv ℝ j g y‖ ^ 2 := by
  unfold PeriodicSobInterp.pw
  calc ∑ w : Fin j → Fin 3, ‖iteratedFDeriv ℝ j g y (PeriodicSobInterp.evw w)‖ ^ 2
      ≤ ∑ _w : Fin j → Fin 3, ‖iteratedFDeriv ℝ j g y‖ ^ 2 := by
        refine Finset.sum_le_sum fun w _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine ((iteratedFDeriv ℝ j g y).le_opNorm _).trans (le_of_eq ?_)
        rw [QLEnergy.norm_evw_prod, mul_one]
    _ = 3 ^ j * ‖iteratedFDeriv ℝ j g y‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- Cauchy–Schwarz for interval integrals of continuous nonnegative functions. -/
theorem interval_cs {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ x, 0 ≤ f x)
    (hg0 : ∀ x, 0 ≤ g x) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, Real.sqrt (f x) * Real.sqrt (g x) ≤
      Real.sqrt (∫ x in a..b, f x) * Real.sqrt (∫ x in a..b, g x) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  set μ : Measure ℝ := volume.restrict (Ioc a b)
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hsf : Continuous fun x => Real.sqrt (f x) := hf.sqrt
  have hsg : Continuous fun x => Real.sqrt (g x) := hg.sqrt
  have hint : ∀ {h : ℝ → ℝ}, Continuous h → Integrable h μ := fun {h} hh =>
    (hh.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hma : MemLp (fun x => Real.sqrt (f x)) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq hsf.aestronglyMeasurable).mpr ?_
    exact (hint hf).congr (Eventually.of_forall fun x => by simp [Real.sq_sqrt (hf0 x)])
  have hmb : MemLp (fun x => Real.sqrt (g x)) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq hsg.aestronglyMeasurable).mpr ?_
    exact (hint hg).congr (Eventually.of_forall fun x => by simp [Real.sq_sqrt (hg0 x)])
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => Real.sqrt_nonneg (f x))
    (Eventually.of_forall fun x => Real.sqrt_nonneg (g x)) hma hmb
  have e2 : ∀ (h : ℝ → ℝ), (∀ x, 0 ≤ h x) →
      (∫ x, Real.sqrt (h x) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = Real.sqrt (∫ x, h x ∂μ) := by
    intro h h0
    rw [Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    rw [Real.rpow_two, Real.sq_sqrt (h0 x)]
  rw [e2 f hf0, e2 g hg0] at hH
  exact hH

/-- The slice energy `∫_{[0,1]³} ‖D^j_xF(s, 2πy)‖² dy`. -/
def sliceE (j : ℕ) (F : R4 → W) (s : ℝ) : ℝ :=
  ∫ y in Icc (0 : Fin 3 → ℝ) 1, ‖dX j F (NativeSlab.spt s y)‖ ^ 2

theorem sliceE_nonneg (j : ℕ) (F : R4 → W) (s : ℝ) : 0 ≤ sliceE j F s :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _

theorem continuous_sliceE {F : R4 → W} (hF : ContDiff ℝ ∞ F) (j : ℕ) :
    Continuous (sliceE j F) :=
  continuous_slice_integral ((NativeSlab.continuous_dX hF j).norm.pow 2)

theorem spt_add_zvec (s : ℝ) (y : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    NativeSlab.spt s (y + (1 : ℝ) • PeriodicCube.zvec k) =
      NativeSlab.spt s y + (2 * π) • PeriodicCube.zvec (Fin.cons 0 k : Fin 4 → ℤ) := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [NativeSlab.spt, PeriodicCube.zvec]
  | succ i => simp [NativeSlab.spt, PeriodicCube.zvec]

/-- **Slice interpolation**: `∫‖D_xF‖² ≤ 9√C (∫‖F‖²)^{1/2}(∫‖D²_xF‖²)^{1/2}` on each time slice of
a spatially `2π`-periodic field. -/
theorem sliceE_one_le {F : R4 → W} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ z μ, F (z + Pi.single μ (2 * π)) = F z) (s : ℝ) :
    sliceE 1 F s ≤ 9 * Real.sqrt (PeriodicSobInterp.interpConst W (Fin 3) 1 2) *
      Real.sqrt (sliceE 0 F s) * Real.sqrt (sliceE 2 F s) := by
  set g : (Fin 3 → ℝ) → W := fun y => F (NativeSlab.spt s y) with hgdef
  have hg : ContDiff ℝ ∞ g := NativeSlab.contDiff_comp_spt hF s
  have hgper : PeriodicSobInterp.IsPer 1 g := fun k y => by
    simp only [hgdef]
    rw [spt_add_zvec]
    exact zper_of_single hper _ _
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hD : ∀ j y, ‖iteratedFDeriv ℝ j g y‖ ^ 2 =
      (2 * π) ^ (2 * j) * ‖dX j F (NativeSlab.spt s y)‖ ^ 2 := by
    intro j y
    rw [hgdef, NativeSlab.iteratedFDeriv_comp_spt hF, norm_smul, Real.norm_of_nonneg (by positivity),
      mul_pow, ← pow_mul, mul_comm j 2]
  have hcube : (PeriodicSobInterp.cube 1 : Set (Fin 3 → ℝ)) = Icc (0 : Fin 3 → ℝ) 1 := rfl
  have hcD : ∀ j, Continuous fun y => ‖dX j F (NativeSlab.spt s y)‖ ^ 2 := fun j =>
    ((NativeSlab.continuous_dX hF j).comp (NativeSlab.continuous_spt.comp
      (Continuous.prodMk_right s))).norm.pow 2
  have hint : ∀ {h : (Fin 3 → ℝ) → ℝ}, Continuous h → IntegrableOn h (Icc (0 : Fin 3 → ℝ) 1) :=
    fun hh => hh.continuousOn.integrableOn_compact isCompact_Icc
  -- the three slice energies in terms of `g`
  have hA0 : PeriodicSobInterp.sobA 1 g 0 = sliceE 0 F s := by
    unfold PeriodicSobInterp.sobA sliceE
    rw [hcube]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [PeriodicSobInterp.pw_zero, NativeSlab.norm_dX_zero]
  have hA2 : PeriodicSobInterp.sobA 1 g 2 ≤ 9 * (2 * π) ^ 4 * sliceE 2 F s := by
    unfold PeriodicSobInterp.sobA sliceE
    rw [hcube, ← integral_const_mul]
    refine setIntegral_mono_on (hint (PeriodicSobInterp.continuous_pw hg 2))
      (hint ((hcD 2).const_mul _)) measurableSet_Icc fun y _ => ?_
    refine (pw_le_norm_sq 2 y).trans (le_of_eq ?_)
    rw [hD]; ring
  have hA1 : sliceE 1 F s ≤ 3 / (2 * π) ^ 2 * PeriodicSobInterp.sobA 1 g 1 := by
    unfold PeriodicSobInterp.sobA sliceE
    rw [hcube, ← integral_const_mul]
    refine setIntegral_mono_on (hint (hcD 1))
      (hint ((PeriodicSobInterp.continuous_pw hg 1).const_mul _)) measurableSet_Icc fun y _ => ?_
    have h1 := norm_sq_le_pw (g := g) 1 y
    rw [hD] at h1
    have h1' : (2 * π) ^ 2 * ‖dX 1 F (NativeSlab.spt s y)‖ ^ 2 ≤
        3 * PeriodicSobInterp.pw g 1 y := by simpa using h1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have hI := PeriodicSobInterp.sobA_interp_normed (V := W) (ι := Fin 3) one_pos hg hgper
    (k := 1) (s := 2) (by norm_num)
  simp only [Nat.sub_self, pow_one, show 2 - 1 = 1 from rfl] at hI
  rw [hA0] at hI
  have hS1 : 0 ≤ PeriodicSobInterp.sobA 1 g 1 := PeriodicSobInterp.sobA_nonneg _ _ _
  have hC := PeriodicSobInterp.interpConst_nonneg (V := W) (ι := Fin 3) 1 2
  have hb0 := sliceE_nonneg 0 F s
  have hb2 := sliceE_nonneg 2 F s
  have hA1' : PeriodicSobInterp.sobA 1 g 1 ≤ Real.sqrt (PeriodicSobInterp.interpConst W (Fin 3) 1 2) *
      Real.sqrt (sliceE 0 F s) * Real.sqrt (9 * (2 * π) ^ 4 * sliceE 2 F s) := by
    rw [← Real.sqrt_mul hC, ← Real.sqrt_mul (mul_nonneg hC hb0)]
    refine Real.le_sqrt_of_sq_le ?_
    refine hI.trans ?_
    exact mul_le_mul_of_nonneg_left hA2 (mul_nonneg hC hb0)
  have hsq : Real.sqrt (9 * (2 * π) ^ 4 * sliceE 2 F s) = 3 * (2 * π) ^ 2 * Real.sqrt (sliceE 2 F s) := by
    rw [Real.sqrt_mul (by positivity), show (9 : ℝ) * (2 * π) ^ 4 = (3 * (2 * π) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hsq] at hA1'
  calc sliceE 1 F s ≤ 3 / (2 * π) ^ 2 * PeriodicSobInterp.sobA 1 g 1 := hA1
    _ ≤ 3 / (2 * π) ^ 2 * (Real.sqrt (PeriodicSobInterp.interpConst W (Fin 3) 1 2) *
          Real.sqrt (sliceE 0 F s) * (3 * (2 * π) ^ 2 * Real.sqrt (sliceE 2 F s))) :=
        mul_le_mul_of_nonneg_left hA1' (by positivity)
    _ = _ := by field_simp; ring

theorem integral_slab_dX_sq {F : R4 → W} (hF : ContDiff ℝ ∞ F) (j : ℕ) {t₀ t₁ : ℝ}
    (h01 : t₀ ≤ t₁) :
    ∫ z in NativeSlab.slab t₀ t₁, ‖dX j F z‖ ^ 2 = (2 * π) ^ 3 * ∫ s in t₀..t₁, sliceE j F s :=
  integral_slab_slices ((NativeSlab.continuous_dX hF j).norm.pow 2) (fun _ => sq_nonneg _) h01

/-- **Interpolation on the slab**: for a smooth spatially `2π`-periodic field,
`‖F‖²_{L²H¹} ≤ ‖F‖²_{L²} + 9√C ‖F‖_{L²}‖F‖_{L²H²}`. -/
theorem sobXSq_one_le {F : R4 → W} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ z μ, F (z + Pi.single μ (2 * π)) = F z) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) :
    sobXSq 1 (NativeSlab.slab t₀ t₁) F ≤ sobXSq 0 (NativeSlab.slab t₀ t₁) F +
      9 * Real.sqrt (PeriodicSobInterp.interpConst W (Fin 3) 1 2) *
        Real.sqrt (sobXSq 0 (NativeSlab.slab t₀ t₁) F) *
          Real.sqrt (sobXSq 2 (NativeSlab.slab t₀ t₁) F) := by
  set C := PeriodicSobInterp.interpConst W (Fin 3) 1 2
  have hC := PeriodicSobInterp.interpConst_nonneg (V := W) (ι := Fin 3) 1 2
  have hc : ∀ j, Continuous fun z => ‖dX j F z‖ ^ 2 := fun j =>
    (NativeSlab.continuous_dX hF j).norm.pow 2
  have hi : ∀ j, IntegrableOn (fun z => ‖dX j F z‖ ^ 2) (NativeSlab.slab t₀ t₁) := fun j =>
    NativeSlab.integrableOn_slab (hc j) t₀ t₁
  have h1 : sobXSq 1 (NativeSlab.slab t₀ t₁) F = sobXSq 0 (NativeSlab.slab t₀ t₁) F +
      ∫ z in NativeSlab.slab t₀ t₁, ‖dX 1 F z‖ ^ 2 := by
    unfold sobXSq
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [integral_add (hi 0) (hi 1)]
  have h0 : sobXSq 0 (NativeSlab.slab t₀ t₁) F =
      ∫ z in NativeSlab.slab t₀ t₁, ‖dX 0 F z‖ ^ 2 := by
    unfold sobXSq; simp
  have h2 : ∫ z in NativeSlab.slab t₀ t₁, ‖dX 2 F z‖ ^ 2 ≤ sobXSq 2 (NativeSlab.slab t₀ t₁) F := by
    unfold sobXSq
    refine setIntegral_mono_on (hi 2) (NativeSlab.integrableOn_slab
      (continuous_finset_sum _ fun j _ => hc j) t₀ t₁) (NativeSlab.measurableSet_slab t₀ t₁)
      fun z _ => ?_
    exact Finset.single_le_sum (f := fun j => ‖dX j F z‖ ^ 2) (fun _ _ => sq_nonneg _)
      (by simp)
  rw [h1]
  refine add_le_add_right ?_ (sobXSq 0 (NativeSlab.slab t₀ t₁) F)
  have he := fun j => continuous_sliceE hF j
  have hcs := interval_cs (he 0) (he 2) (sliceE_nonneg 0 F) (sliceE_nonneg 2 F) h01
  have hb : ∫ s in t₀..t₁, sliceE 1 F s ≤
      9 * Real.sqrt C * ∫ s in t₀..t₁, Real.sqrt (sliceE 0 F s) * Real.sqrt (sliceE 2 F s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on h01 ((he 1).intervalIntegrable _ _)
      ((continuous_const.mul (((he 0).sqrt).mul (he 2).sqrt)).intervalIntegrable _ _)
      fun s _ => ?_
    have := sliceE_one_le hF hper s
    linarith
  have hS0 : 0 ≤ ∫ s in t₀..t₁, sliceE 0 F s :=
    intervalIntegral.integral_nonneg h01 fun s _ => sliceE_nonneg 0 F s
  have hS2 : 0 ≤ ∫ s in t₀..t₁, sliceE 2 F s :=
    intervalIntegral.integral_nonneg h01 fun s _ => sliceE_nonneg 2 F s
  rw [integral_slab_dX_sq hF 1 h01]
  have hsq0 : Real.sqrt (sobXSq 0 (NativeSlab.slab t₀ t₁) F) =
      Real.sqrt ((2 * π) ^ 3) * Real.sqrt (∫ s in t₀..t₁, sliceE 0 F s) := by
    rw [h0, integral_slab_dX_sq hF 0 h01, Real.sqrt_mul (by positivity)]
  have hsq2 : Real.sqrt ((2 * π) ^ 3) * Real.sqrt (∫ s in t₀..t₁, sliceE 2 F s) ≤
      Real.sqrt (sobXSq 2 (NativeSlab.slab t₀ t₁) F) := by
    rw [← Real.sqrt_mul (by positivity), ← integral_slab_dX_sq hF 2 h01]
    exact Real.sqrt_le_sqrt h2
  have hpos : 0 ≤ 9 * Real.sqrt C := by positivity
  calc (2 * π) ^ 3 * ∫ s in t₀..t₁, sliceE 1 F s
      ≤ (2 * π) ^ 3 * (9 * Real.sqrt C * (Real.sqrt (∫ s in t₀..t₁, sliceE 0 F s) *
          Real.sqrt (∫ s in t₀..t₁, sliceE 2 F s))) :=
        mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hcs hpos)) (by positivity)
    _ = 9 * Real.sqrt C * (Real.sqrt ((2 * π) ^ 3) * Real.sqrt (∫ s in t₀..t₁, sliceE 0 F s)) *
          (Real.sqrt ((2 * π) ^ 3) * Real.sqrt (∫ s in t₀..t₁, sliceE 2 F s)) := by
        have : Real.sqrt ((2 * π) ^ 3) * Real.sqrt ((2 * π) ^ 3) = (2 * π) ^ 3 :=
          Real.mul_self_sqrt (by positivity)
        linear_combination (-(9 * Real.sqrt C * Real.sqrt (∫ s in t₀..t₁, sliceE 0 F s) *
          Real.sqrt (∫ s in t₀..t₁, sliceE 2 F s))) * this
    _ ≤ 9 * Real.sqrt C * Real.sqrt (sobXSq 0 (NativeSlab.slab t₀ t₁) F) *
          Real.sqrt (sobXSq 2 (NativeSlab.slab t₀ t₁) F) := by
        rw [hsq0]
        exact mul_le_mul_of_nonneg_left hsq2 (mul_nonneg hpos (by positivity))

end

end RenewalGeometry.SourceCompare
