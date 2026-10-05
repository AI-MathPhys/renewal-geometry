/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.GevreyFourierDecay
import RenewalGeometry.Continuum.NativeTailTransfer

/-!
# From the period-`2π` space-time slab to the unit torus: the logarithmic upgrade in `L²_tH^j_x`

Einstein–Standard-Model action-closure manuscript, `thm:native-source` (application of
`lem:log-source-upgrade` to the low-frequency residual rows).  The residual rows live on the
period-`2π` auxiliary box of `ℝ⁴` and take values in finite-dimensional covector spaces; their
space-time Sobolev norms `‖·‖_{L²_tH^j_x(Q)}` (`NativeTail.sobX`: classical spatial derivatives,
operator norms) are compared here with the Fourier norms of the scalar coordinate slices on the
unit torus `𝕋³`, one lemma per norm:

* `integral_unitCube_norm_iteratedFDeriv_sq_le` (generic, `𝕋^d`): for a smooth `ℤ^d`-periodic
  `g`, `∫_{cube} ‖D^i g‖² ≤ d^{2i} ‖g‖²_{H^i(𝕋^d)}` — classical derivatives are controlled by the
  Fourier norm (the converse of `SobolevBoxCr.sobSq_descend_le`).
* `slab t₀ t₁ = [t₀,t₁] × (0,2π]³`, `spt t y = (t, 2π y)`, `lintegral_slab`: Fubini and the
  dilation `x = 2πy`.
* `iteratedFDeriv_comp_spt`: `D^i_y[F(t, 2πy)] = (2π)^i D^i_x F(t, 2πy)`.
* **`sobX_log_upgrade`**: for a smooth spatially `2π`-periodic `F : ℝ⁴ → W` (`W`
  finite-dimensional) whose derivatives along every direction have analytic growth
  `‖DᵖF(z)(v, …, v)‖ ≤ a p! (RK)ᵖ` (`‖v‖ ≤ 1`), `‖F‖_{L²(Q)} ≤ ε` implies
  `‖F‖_{L²_tH^j_x(Q)} ≤ C ε K^j [1 + log(2 + C a K^{j+3}/ε)]^j`
  (`eq:log-source-upgrade` in the norm of `thm:native-source`).
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped Real BigOperators ENNReal Nat ContDiff

namespace RenewalGeometry.NativeSlab

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

open TorusSobolev StripFourier SobolevBoxCr AnalyticSourceUpgrade SobolevOpen
open DiscreteEulerConsistency (R4 evec)

/-! ### Classical derivatives are controlled by the Fourier norm -/

section Generic

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **`∫_{cube} ‖D^i g‖² ≤ d^{2i} ‖g‖²_{H^i}`** for a smooth `ℤ^d`-periodic `g` in `H^i`. -/
theorem integral_unitCube_norm_iteratedFDeriv_sq_le {g : (d → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hp : SobolevBoxCr.IsPeriodic g) (i : ℕ) (hmem : TorusSobolev.MemH (i : ℝ) (descendFun g)) :
    ∫ y in unitCube, ‖iteratedFDeriv ℝ i g y‖ ^ 2 ≤
      (Fintype.card d : ℝ) ^ (2 * i) * TorusSobolev.sobSq i (descendFun g) := by
  set N : ℝ := (Fintype.card (Fin i → d) : ℝ)
  have hN : N = (Fintype.card d : ℝ) ^ i := by simp [N]
  -- pointwise: `‖D^i g‖² ≤ N Σ_w ‖∂^w g‖²`
  have hpt : ∀ y, ‖iteratedFDeriv ℝ i g y‖ ^ 2 ≤ N * ∑ w : Fin i → d, ‖iterPd g w y‖ ^ 2 := by
    intro y
    have h1 := norm_le_sum_single (iteratedFDeriv ℝ i g y)
    simp_rw [iteratedFDeriv_single hg] at h1
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin i → d)))
      (f := fun w => ‖iterPd g w y‖)
    rw [Finset.card_univ] at h2
    calc ‖iteratedFDeriv ℝ i g y‖ ^ 2 ≤ (∑ w : Fin i → d, ‖iterPd g w y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ N * ∑ w : Fin i → d, ‖iterPd g w y‖ ^ 2 := h2
  -- each word: `∫ ‖∂^w g‖² = Σ |symbol|² |ĝ|² ≤ sobSq i`
  have hw : ∀ w : Fin i → d, ∫ y in unitCube, ‖iterPd g w y‖ ^ 2 ≤
      TorusSobolev.sobSq i (descendFun g) := by
    intro w
    have hs := hasSum_sq_descend (contDiff_iterPd hg w).continuous (isPeriodic_iterPd hp w)
    rw [← hs.tsum_eq]
    unfold TorusSobolev.sobSq TorusSobolev.coeffSobSq
    refine Summable.tsum_le_tsum (fun n => ?_) hs.summable hmem
    rw [mFourierCoeff_descend_iterPd hg hp w n, norm_mul, mul_pow, Real.rpow_natCast]
    have := TorusSobolev.norm_symbol_sq_le_pow (idx w) n
    rw [mOrder_idx] at this
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hint : ∀ w : Fin i → d, IntegrableOn (fun y => ‖iterPd g w y‖ ^ 2) unitCube := fun w =>
    integrableOn_unitCube ((contDiff_iterPd hg w).continuous.norm.pow 2)
  have hint2 : IntegrableOn (fun y => ‖iteratedFDeriv ℝ i g y‖ ^ 2) unitCube :=
    integrableOn_unitCube ((hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.pow 2)
  calc ∫ y in unitCube, ‖iteratedFDeriv ℝ i g y‖ ^ 2
      ≤ ∫ y in unitCube, N * ∑ w : Fin i → d, ‖iterPd g w y‖ ^ 2 :=
        setIntegral_mono_on hint2 ((integrable_finsetSum _ fun w _ => hint w).const_mul N)
          measurableSet_unitCube fun y _ => hpt y
    _ = N * ∑ w : Fin i → d, ∫ y in unitCube, ‖iterPd g w y‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun w _ => hint w]
    _ ≤ N * ∑ _w : Fin i → d, TorusSobolev.sobSq i (descendFun g) := by
        gcongr with w
        exact hw w
    _ = (Fintype.card d : ℝ) ^ (2 * i) * TorusSobolev.sobSq i (descendFun g) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
        congr 1
        rw [show (Fintype.card (Fin i → d) : ℝ) = N from rfl, hN, pow_mul]
        ring

end Generic

/-! ### The slab and its dilation to the unit cube -/

/-- The slab `Q = [t₀, t₁] × (0, 2π]³` of the periodic box (`thm:native-source`; the spatial
factor is one full period cell of the auxiliary box). -/
def slab (t₀ t₁ : ℝ) : Set R4 := {z | z 0 ∈ Icc t₀ t₁ ∧ ∀ i : Fin 3, z i.succ ∈ Ioc 0 (2 * π)}

/-- The point `(t, 2π y)` of `ℝ⁴`. -/
def spt (t : ℝ) (y : Fin 3 → ℝ) : R4 := Fin.cons t ((2 * π) • y)

/-- The spatial period cell `(0, 2π]³`. -/
def cell2 : Set (Fin 3 → ℝ) := {x | ∀ i, x i ∈ Ioc 0 (2 * π)}

theorem measurableSet_slab (t₀ t₁ : ℝ) : MeasurableSet (slab t₀ t₁) := by
  have h1 : MeasurableSet {z : R4 | z 0 ∈ Icc t₀ t₁} := (measurable_pi_apply 0) measurableSet_Icc
  have h2 : MeasurableSet {z : R4 | ∀ i : Fin 3, z i.succ ∈ Ioc 0 (2 * π)} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => (measurable_pi_apply _) measurableSet_Ioc
  exact h1.inter h2

theorem slab_subset_box {t₀ t₁ : ℝ} (h0 : 0 ≤ t₀) (h1 : t₁ ≤ 2 * π) :
    slab t₀ t₁ ⊆ NativeTail.box := by
  intro z hz
  refine ⟨fun μ => ?_, fun μ => ?_⟩
  · induction μ using Fin.cases with
    | zero => exact h0.trans hz.1.1
    | succ i => exact (hz.2 i).1.le
  · induction μ using Fin.cases with
    | zero => exact hz.1.2.trans h1
    | succ i => exact (hz.2 i).2

/-- **Fubini on the slab and dilation**: `∫⁻_Q G = (2π)³ ∫⁻_{[t₀,t₁]} ∫⁻_{(0,1]³} G(t, 2πy)`. -/
theorem lintegral_slab (t₀ t₁ : ℝ) {G : R4 → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z in slab t₀ t₁, G z =
      ENNReal.ofReal ((2 * π) ^ 3) * ∫⁻ t in Icc t₀ t₁, ∫⁻ y in unitCube, G (spt t y) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0 with he
  have hmp : MeasurePreserving e (volume : Measure R4) (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have hsymm : ∀ p : ℝ × (Fin 3 → ℝ), e.symm p = Fin.cons p.1 p.2 := by
    intro p
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
    exact Fin.insertNth_zero' p.1 p.2
  have hpre : e.symm ⁻¹' slab t₀ t₁ = Icc t₀ t₁ ×ˢ cell2 := by
    ext p
    simp [hsymm, slab, cell2]
  have h1 : ∫⁻ z in slab t₀ t₁, G z =
      ∫⁻ p in Icc t₀ t₁ ×ˢ cell2, G (Fin.cons p.1 p.2) ∂(volume.prod volume) := by
    rw [← hpre, ← (hmp.symm e).setLIntegral_comp_preimage_emb e.symm.measurableEmbedding G]
    simp only [hsymm]
  have hGc : Measurable fun p : ℝ × (Fin 3 → ℝ) => G (Fin.cons p.1 p.2) := by
    refine hG.comp ?_
    exact measurable_pi_iff.mpr fun μ => by
      induction μ using Fin.cases with
      | zero => simpa using measurable_fst
      | succ i =>
        simp only [Fin.cons_succ]
        exact (measurable_pi_apply i).comp measurable_snd
  rw [h1, ← Measure.prod_restrict, lintegral_prod _ hGc.aemeasurable]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  -- the dilation `x = 2π y`
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hmpA := SobolevOpen.measurePreserving_affine (ι := Fin 3) 0 h2π
  have hemb : MeasurableEmbedding (fun y : Fin 3 → ℝ => (0 : Fin 3 → ℝ) + (2 * π) • y) := by
    simpa using measurableEmbedding_const_smul₀ (α := Fin 3 → ℝ) h2π.ne'
  have hpre2 : (fun y : Fin 3 → ℝ => (0 : Fin 3 → ℝ) + (2 * π) • y) ⁻¹' cell2 = unitCube := by
    ext y
    simp only [mem_preimage, zero_add, cell2, unitCube, mem_setOf_eq, Pi.smul_apply,
      smul_eq_mul, mem_Ioc]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 h2π.le, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos h2π h1, by nlinarith⟩
  have h3 := hmpA.setLIntegral_comp_preimage_emb hemb (fun x => G (Fin.cons t x)) cell2
  rw [hpre2] at h3
  simp only [zero_add] at h3
  rw [Measure.restrict_smul, lintegral_smul_measure] at h3
  have hc : ENNReal.ofReal ((2 * π) ^ 3) * ENNReal.ofReal (((2 * π) ^ Fintype.card (Fin 3))⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), Fintype.card_fin,
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  calc ∫⁻ x in cell2, G (Fin.cons t x)
      = ENNReal.ofReal ((2 * π) ^ 3) * (ENNReal.ofReal (((2 * π) ^ Fintype.card (Fin 3))⁻¹) *
          ∫⁻ x in cell2, G (Fin.cons t x)) := by rw [← mul_assoc, hc, one_mul]
    _ = ENNReal.ofReal ((2 * π) ^ 3) * ∫⁻ y in unitCube, G (spt t y) := by
        rw [smul_eq_mul] at h3
        rw [← h3]; rfl

/-! ### Spatial derivatives of the slices -/

section Slices

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem spt_eq (t : ℝ) (y : Fin 3 → ℝ) :
    spt t y = (Fin.cons t 0 : R4) + ((2 * π) • NativeTail.spatialL) y := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [spt, NativeTail.spatialL]
  | succ i => simp [spt, NativeTail.spatialL]

/-- **`D^i_y[F(t, 2πy)] = (2π)^i D^i_x F(t, 2πy)`.** -/
theorem iteratedFDeriv_comp_spt {F : R4 → W} (hF : ContDiff ℝ ∞ F) (t : ℝ) (i : ℕ)
    (y : Fin 3 → ℝ) :
    iteratedFDeriv ℝ i (fun y => F (spt t y)) y = ((2 * π) ^ i) • NativeTail.dX i F (spt t y) := by
  set L : (Fin 3 → ℝ) →L[ℝ] R4 := (2 * π) • NativeTail.spatialL
  set c : R4 := Fin.cons t 0
  have hfun : (fun y => F (spt t y)) = (fun w => F (c + w)) ∘ L := by
    funext y; simp [spt_eq, c, L]
  have hg : ContDiff ℝ ∞ (fun w => F (c + w)) := hF.comp (contDiff_const.add contDiff_id)
  rw [hfun, L.iteratedFDeriv_comp_right hg y (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left, ← spt_eq]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, L, NativeTail.dX,
    ContinuousMultilinearMap.smul_apply]
  rw [ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ i F (spt t y))
    (fun _ => 2 * π) (fun k => NativeTail.spatialL (v k))]
  simp

theorem norm_dX_spt_le {F : R4 → W} (hF : ContDiff ℝ ∞ F) (t : ℝ) (i : ℕ) (y : Fin 3 → ℝ) :
    ‖NativeTail.dX i F (spt t y)‖ ≤ ‖iteratedFDeriv ℝ i (fun y => F (spt t y)) y‖ := by
  rw [iteratedFDeriv_comp_spt hF, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : (1 : ℝ) ≤ (2 * π) ^ i := one_le_pow₀ (by nlinarith [Real.pi_gt_three])
  exact le_mul_of_one_le_left (norm_nonneg _) h1

theorem norm_dX_zero (F : R4 → W) (z : R4) : ‖NativeTail.dX 0 F z‖ = ‖F z‖ := by
  refine le_antisymm ?_ ?_
  · refine (NativeTail.norm_dX_le 0 F z).trans ?_
    rw [norm_iteratedFDeriv_zero]
  · have h := (NativeTail.dX 0 F z).le_opNorm (fun i => Fin.elim0 i)
    have e : NativeTail.dX 0 F z (fun i => Fin.elim0 i) = F z := by
      simp [NativeTail.dX, iteratedFDeriv_zero_apply]
    rw [e] at h
    simpa using h

/-- **Analytic growth of the slices** along the coordinate directions. -/
theorem norm_iteratedFDeriv_slice_le {F : R4 → W} (hF : ContDiff ℝ ∞ F) (Lc : W →L[ℝ] ℂ)
    {a R K : ℝ} (hb : ∀ (z v : R4) (p : ℕ), ‖v‖ ≤ 1 →
      ‖iteratedFDeriv ℝ p F z (fun _ => v)‖ ≤ a * (p ! * (R * K) ^ p))
    (t : ℝ) (k : Fin 3) (p : ℕ) (y : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ p (fun y => Lc (F (spt t y))) y (fun _ => Pi.single k 1)‖ ≤
      (‖Lc‖ * a) * p ! * (2 * π * (R * K)) ^ p := by
  have hG : ContDiff ℝ ∞ (fun y => F (spt t y)) := by
    have : (fun y => F (spt t y)) = fun y => F ((Fin.cons t 0 : R4) +
        ((2 * π) • NativeTail.spatialL) y) := by funext y; rw [spt_eq]
    rw [this]
    exact hF.comp (contDiff_const.add (ContinuousLinearMap.contDiff _))
  have e1 : (fun y => Lc (F (spt t y))) = ⇑Lc ∘ fun y => F (spt t y) := rfl
  rw [e1, Lc.iteratedFDeriv_comp_left hG.contDiffAt (by exact_mod_cast le_top),
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    iteratedFDeriv_comp_spt hF, ContinuousMultilinearMap.smul_apply]
  have hsp : ‖NativeTail.spatialL (Pi.single k (1 : ℝ))‖ ≤ 1 := by
    refine (NativeTail.spatialL.le_opNorm _).trans ?_
    have : ‖(Pi.single k (1 : ℝ) : Fin 3 → ℝ)‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by
        by_cases h : j = k
        · subst h; simp
        · simp [h]
    calc ‖NativeTail.spatialL‖ * ‖(Pi.single k (1 : ℝ) : Fin 3 → ℝ)‖ ≤ 1 * 1 :=
          mul_le_mul NativeTail.norm_spatialL_le this (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hdX : NativeTail.dX p F (spt t y) (fun _ => Pi.single k 1) =
      iteratedFDeriv ℝ p F (spt t y) (fun _ => NativeTail.spatialL (Pi.single k 1)) := rfl
  rw [hdX]
  have h1 := hb (spt t y) _ p hsp
  have h2 : 0 ≤ a * (p ! * (R * K) ^ p) := (norm_nonneg _).trans h1
  refine (Lc.le_opNorm _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc ‖Lc‖ * ((2 * π) ^ p * ‖iteratedFDeriv ℝ p F (spt t y)
        (fun _ => NativeTail.spatialL (Pi.single k 1))‖)
      ≤ ‖Lc‖ * ((2 * π) ^ p * (a * (p ! * (R * K) ^ p))) := by gcongr
    _ = (‖Lc‖ * a) * p ! * (2 * π * (R * K)) ^ p := by rw [mul_pow]; ring

/-- The slices of a `2π`-periodic field are `ℤ³`-periodic. -/
theorem isPeriodic_slice {F : R4 → W} (hF : DiscreteEulerConsistency.IsPeriodic (2 * π) F)
    (t : ℝ) : SobolevBoxCr.IsPeriodic (fun y : Fin 3 → ℝ => F (spt t y)) := by
  intro n y
  have h := hF.add_intVec (Fin.cons 0 n) (spt t y)
  show F (spt t (y + fun i => (n i : ℝ))) = F (spt t y)
  rw [← h]
  congr 1
  funext μ
  induction μ using Fin.cases with
  | zero => simp [spt, DiscreteEulerConsistency.realVec]
  | succ i => simp [spt, DiscreteEulerConsistency.realVec]

end Slices

/-! ### Measurability of the slice norms in time -/

section Measurability

/-- The Fourier coefficients of a jointly continuous family of periodic slices are measurable in
time. -/
theorem measurable_mFourierCoeff_slice {G : ℝ → (Fin 3 → ℝ) → ℂ}
    (hG : Continuous fun p : ℝ × (Fin 3 → ℝ) => G p.1 p.2)
    (hp : ∀ t, SobolevBoxCr.IsPeriodic (G t)) (n : Fin 3 → ℤ) :
    Measurable fun t => mFourierCoeff (descendFun (G t)) n := by
  have e : (fun t => mFourierCoeff (descendFun (G t)) n) =
      fun t => ∫ y in unitCube, mFourier (-n) (torusMk y) • G t y := by
    funext t
    unfold mFourierCoeff
    rw [integral_torus_eq_unitCube]
    refine setIntegral_congr_fun measurableSet_unitCube fun y _ => ?_
    change mFourier (-n) (torusMk y) • descendFun (G t) (torusMk y) = _
    rw [descendFun_mk (hp t)]
  rw [e]
  have hc : Continuous fun p : ℝ × (Fin 3 → ℝ) => mFourier (-n) (torusMk p.2) • G p.1 p.2 :=
    ((mFourier (-n)).continuous.comp (continuous_torusMk.comp continuous_snd)).smul hG
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume.restrict unitCube)).measurable

/-- `t ↦ ‖G(t)‖²_{H^j(𝕋³)}` is measurable (as an extended real) for a jointly continuous family of
periodic slices in `H^j`. -/
theorem measurable_ofReal_sobSq_slice {G : ℝ → (Fin 3 → ℝ) → ℂ}
    (hG : Continuous fun p : ℝ × (Fin 3 → ℝ) => G p.1 p.2)
    (hp : ∀ t, SobolevBoxCr.IsPeriodic (G t)) (j : ℕ)
    (hmem : ∀ t, TorusSobolev.MemH (j : ℝ) (descendFun (G t))) :
    Measurable fun t => ENNReal.ofReal (TorusSobolev.sobSq (j : ℝ) (descendFun (G t))) := by
  have e : (fun t => ENNReal.ofReal (TorusSobolev.sobSq (j : ℝ) (descendFun (G t)))) =
      fun t => ∑' n : Fin 3 → ℤ, ENNReal.ofReal (TorusSobolev.sobWeight n ^ (j : ℝ) *
        ‖mFourierCoeff (descendFun (G t)) n‖ ^ 2) := by
    funext t
    unfold TorusSobolev.sobSq TorusSobolev.coeffSobSq
    exact ENNReal.ofReal_tsum_of_nonneg (fun n => TorusSobolev.coeffSobSq_term_nonneg _ _ n)
      (hmem t)
  rw [e]
  refine Measurable.ennreal_tsum fun n => ?_
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((measurable_mFourierCoeff_slice hG hp n).norm.pow_const 2))

end Measurability

/-! ### Norm comparisons on the slab -/

section Comparison

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem slab_subset_Icc (t₀ t₁ : ℝ) :
    slab t₀ t₁ ⊆ Icc (Fin.cons t₀ 0 : R4) (Fin.cons t₁ (fun _ => 2 * π)) := by
  intro z hz
  refine ⟨fun μ => ?_, fun μ => ?_⟩
  · induction μ using Fin.cases with
    | zero => simpa using hz.1.1
    | succ i => simpa using (hz.2 i).1.le
  · induction μ using Fin.cases with
    | zero => simpa using hz.1.2
    | succ i => simpa using (hz.2 i).2

theorem integrableOn_slab {f : R4 → ℝ} (hf : Continuous f) (t₀ t₁ : ℝ) :
    IntegrableOn f (slab t₀ t₁) :=
  (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set (slab_subset_Icc t₀ t₁)

theorem continuous_dX {F : R4 → W} (hF : ContDiff ℝ ∞ F) (i : ℕ) :
    Continuous (NativeTail.dX i F) :=
  (ContinuousMultilinearMap.compContinuousLinearMapL (F := W)
    (fun _ : Fin i => NativeTail.spatialL)).continuous.comp
      (hF.continuous_iteratedFDeriv (by exact_mod_cast le_top))

theorem sobXSq_nonneg (j : ℕ) (Q : Set R4) (F : R4 → W) : 0 ≤ NativeTail.sobXSq j Q F := by
  unfold NativeTail.sobXSq
  exact integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem ofReal_sobXSq_eq {F : R4 → W} (hF : ContDiff ℝ ∞ F) (j : ℕ) (t₀ t₁ : ℝ) :
    ENNReal.ofReal (NativeTail.sobXSq j (slab t₀ t₁) F) =
      ∫⁻ z in slab t₀ t₁, ENNReal.ofReal (∑ i ∈ Finset.range (j + 1),
        ‖NativeTail.dX i F z‖ ^ 2) := by
  unfold NativeTail.sobXSq
  have hc : Continuous fun z => ∑ i ∈ Finset.range (j + 1), ‖NativeTail.dX i F z‖ ^ 2 :=
    continuous_finset_sum _ fun i _ => ((continuous_dX hF i).norm.pow 2)
  exact ofReal_integral_eq_lintegral_ofReal (integrableOn_slab hc t₀ t₁)
    (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- **The `L²` norms of the coordinate slices are controlled by `‖F‖_{L²(Q)}`.** -/
theorem lintegral_slice_sq_le {F : R4 → W} (hF : ContDiff ℝ ∞ F)
    (hper : DiscreteEulerConsistency.IsPeriodic (2 * π) F) (Lc : W →L[ℝ] ℂ) (t₀ t₁ : ℝ) :
    ∫⁻ t in Icc t₀ t₁, ENNReal.ofReal (∫ x, ‖descendFun (fun y => Lc (F (spt t y))) x‖ ^ 2) ≤
      ENNReal.ofReal (‖Lc‖ ^ 2 * NativeTail.sobXSq 0 (slab t₀ t₁) F) := by
  have hFc : Continuous F := hF.continuous
  have hspt : ∀ t, Continuous (spt t) := fun t => by
    have : spt t = fun y => (Fin.cons t 0 : R4) + ((2 * π) • NativeTail.spatialL) y := by
      funext y; exact spt_eq t y
    rw [this]; exact continuous_const.add (ContinuousLinearMap.continuous _)
  have hpt : ∀ t, ENNReal.ofReal (∫ x, ‖descendFun (fun y => Lc (F (spt t y))) x‖ ^ 2) ≤
      ENNReal.ofReal (‖Lc‖ ^ 2) * ∫⁻ y in unitCube, ENNReal.ofReal (‖F (spt t y)‖ ^ 2) := by
    intro t
    have hp : SobolevBoxCr.IsPeriodic (fun y => Lc (F (spt t y))) := by
      intro n y
      have := isPeriodic_slice hper t n y
      simp only [] at this ⊢
      rw [this]
    rw [integral_descendFun_sq hp]
    have hint : IntegrableOn (fun y => ‖Lc (F (spt t y))‖ ^ 2) unitCube :=
      integrableOn_unitCube ((Lc.continuous.comp (hFc.comp (hspt t))).norm.pow 2)
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ => sq_nonneg _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (Lc.le_opNorm _) 2
  have hG : Measurable fun z : R4 => ENNReal.ofReal (‖F z‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (hFc.norm.pow 2).measurable
  have hslab := lintegral_slab t₀ t₁ hG
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 * π) ^ 3) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by nlinarith [Real.pi_gt_three]))
  have h0 : ENNReal.ofReal (NativeTail.sobXSq 0 (slab t₀ t₁) F) =
      ∫⁻ z in slab t₀ t₁, ENNReal.ofReal (‖F z‖ ^ 2) := by
    rw [ofReal_sobXSq_eq hF]
    simp [norm_dX_zero]
  calc ∫⁻ t in Icc t₀ t₁, ENNReal.ofReal (∫ x, ‖descendFun (fun y => Lc (F (spt t y))) x‖ ^ 2)
      ≤ ∫⁻ t in Icc t₀ t₁, ENNReal.ofReal (‖Lc‖ ^ 2) *
          ∫⁻ y in unitCube, ENNReal.ofReal (‖F (spt t y)‖ ^ 2) := lintegral_mono hpt
    _ = ENNReal.ofReal (‖Lc‖ ^ 2) * ∫⁻ t in Icc t₀ t₁,
          ∫⁻ y in unitCube, ENNReal.ofReal (‖F (spt t y)‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (‖Lc‖ ^ 2) * (ENNReal.ofReal ((2 * π) ^ 3) * ∫⁻ t in Icc t₀ t₁,
          ∫⁻ y in unitCube, ENNReal.ofReal (‖F (spt t y)‖ ^ 2)) := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hone
    _ = ENNReal.ofReal (‖Lc‖ ^ 2 * NativeTail.sobXSq 0 (slab t₀ t₁) F) := by
        rw [← hslab, ← h0, ENNReal.ofReal_mul (sq_nonneg _)]

end Comparison

/-! ### The classical norm through the Fourier norms of the slices -/

section Upper

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem spt_eq' (p : ℝ × (Fin 3 → ℝ)) :
    spt p.1 p.2 = p.1 • (Pi.single 0 1 : R4) + ((2 * π) • NativeTail.spatialL) p.2 := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [spt, NativeTail.spatialL]
  | succ i => simp [spt, NativeTail.spatialL]

theorem continuous_spt : Continuous fun p : ℝ × (Fin 3 → ℝ) => spt p.1 p.2 := by
  have : (fun p : ℝ × (Fin 3 → ℝ) => spt p.1 p.2) = fun p =>
      p.1 • (Pi.single 0 1 : R4) + ((2 * π) • NativeTail.spatialL) p.2 := funext spt_eq'
  rw [this]
  exact (continuous_fst.smul continuous_const).add
    ((ContinuousLinearMap.continuous _).comp continuous_snd)

theorem contDiff_comp_spt {F : R4 → W} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    ContDiff ℝ ∞ (fun y => F (spt t y)) := by
  have : (fun y => F (spt t y)) = fun y => F ((Fin.cons t 0 : R4) +
      ((2 * π) • NativeTail.spatialL) y) := by funext y; rw [spt_eq]
  rw [this]
  exact hF.comp (contDiff_const.add (ContinuousLinearMap.contDiff _))

variable [FiniteDimensional ℝ W]

/-- The coordinate slices `g_{c,t}(y) = c-th coordinate of F(t, 2πy)`. -/
def sliceC (F : R4 → W) (c : Fin (Module.finrank ℝ W)) (t : ℝ) (y : Fin 3 → ℝ) : ℂ :=
  coordC (Module.finBasis ℝ W) c (F (spt t y))

/-- The constant `Σ_c ‖b_c‖` of the basis. -/
def basisSum (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] : ℝ :=
  ∑ c, ‖Module.finBasis ℝ W c‖

theorem basisSum_nonneg : 0 ≤ basisSum W := Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Pointwise: `Σ_{i≤j} ‖D^i_xF(t,2πy)‖² ≤ N B² Σ_c Σ_{i≤j} ‖D^i g_{c,t}(y)‖²`. -/
theorem sum_norm_dX_sq_le {F : R4 → W} (hF : ContDiff ℝ ∞ F) (j : ℕ) (t : ℝ) (y : Fin 3 → ℝ) :
    ∑ i ∈ Finset.range (j + 1), ‖NativeTail.dX i F (spt t y)‖ ^ 2 ≤
      ((Module.finrank ℝ W : ℝ) * basisSum W ^ 2) *
        ∑ c, ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2 := by
  set b := Module.finBasis ℝ W
  have hG := contDiff_comp_spt hF t
  have hcomp : ∀ i c, iteratedFDeriv ℝ i (sliceC F c t) y =
      (coordC b c).compContinuousMultilinearMap (iteratedFDeriv ℝ i (fun y => F (spt t y)) y) := by
    intro i c
    have e : sliceC F c t = ⇑(coordC b c) ∘ fun y => F (spt t y) := rfl
    rw [e, (coordC b c).iteratedFDeriv_comp_left hG.contDiffAt (by exact_mod_cast le_top)]
  have hbc : ∀ c, ‖b c‖ ≤ basisSum W := fun c =>
    Finset.single_le_sum (f := fun c => ‖b c‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
  have hpt : ∀ i, ‖NativeTail.dX i F (spt t y)‖ ^ 2 ≤
      ((Module.finrank ℝ W : ℝ) * basisSum W ^ 2) * ∑ c, ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2 := by
    intro i
    have h1 := norm_dX_spt_le hF t i y
    have h2 := norm_le_sum_coordC b (iteratedFDeriv ℝ i (fun y => F (spt t y)) y)
    simp_rw [← hcomp] at h2
    have h3 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (Module.finrank ℝ W))))
      (f := fun c => ‖b c‖ * ‖iteratedFDeriv ℝ i (sliceC F c t) y‖)
    rw [Finset.card_univ, Fintype.card_fin] at h3
    have h4 : ∀ c, (‖b c‖ * ‖iteratedFDeriv ℝ i (sliceC F c t) y‖) ^ 2 ≤
        basisSum W ^ 2 * ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2 := by
      intro c
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hbc c) 2) (sq_nonneg _)
    calc ‖NativeTail.dX i F (spt t y)‖ ^ 2
        ≤ (∑ c, ‖b c‖ * ‖iteratedFDeriv ℝ i (sliceC F c t) y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
      _ ≤ (Module.finrank ℝ W : ℝ) * ∑ c, (‖b c‖ * ‖iteratedFDeriv ℝ i (sliceC F c t) y‖) ^ 2 :=
          h3
      _ ≤ (Module.finrank ℝ W : ℝ) * ∑ c, basisSum W ^ 2 *
            ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2 := by
          gcongr with c
          exact h4 c
      _ = ((Module.finrank ℝ W : ℝ) * basisSum W ^ 2) *
            ∑ c, ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2 := by
          rw [← Finset.mul_sum]; ring
  calc ∑ i ∈ Finset.range (j + 1), ‖NativeTail.dX i F (spt t y)‖ ^ 2
      ≤ ∑ i ∈ Finset.range (j + 1), ((Module.finrank ℝ W : ℝ) * basisSum W ^ 2) *
          ∑ c, ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2 := Finset.sum_le_sum fun i _ => hpt i
    _ = ((Module.finrank ℝ W : ℝ) * basisSum W ^ 2) *
          ∑ c, ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]

theorem continuous_sliceC {F : R4 → W} (hF : Continuous F) (c : Fin (Module.finrank ℝ W)) :
    Continuous fun p : ℝ × (Fin 3 → ℝ) => sliceC F c p.1 p.2 :=
  (coordC (Module.finBasis ℝ W) c).continuous.comp (hF.comp continuous_spt)

theorem isPeriodic_sliceC {F : R4 → W} (hper : DiscreteEulerConsistency.IsPeriodic (2 * π) F)
    (c : Fin (Module.finrank ℝ W)) (t : ℝ) : SobolevBoxCr.IsPeriodic (sliceC F c t) := by
  intro n y
  have := isPeriodic_slice hper t n y
  simp only [] at this
  simp only [sliceC, this]

/-- **The classical `L²_tH^j_x(Q)` norm through the Fourier norms of the slices**:
`‖F‖²_{L²_tH^j_x(Q)} ≤ (2π)³ N B² (j+1) 9^j Σ_c ∫_{[t₀,t₁]} ‖g_{c,t}‖²_{H^j(𝕋³)}`. -/
theorem ofReal_sobXSq_le {F : R4 → W} (hF : ContDiff ℝ ∞ F)
    (hper : DiscreteEulerConsistency.IsPeriodic (2 * π) F) (j : ℕ) (t₀ t₁ : ℝ)
    (hmem : ∀ c t, TorusSobolev.MemH (j : ℝ) (descendFun (sliceC F c t))) :
    ENNReal.ofReal (NativeTail.sobXSq j (slab t₀ t₁) F) ≤
      ENNReal.ofReal ((2 * π) ^ 3 * ((Module.finrank ℝ W : ℝ) * basisSum W ^ 2) *
        ((j + 1) * 9 ^ j)) *
        ∑ c, ∫⁻ t in Icc t₀ t₁, ENNReal.ofReal (TorusSobolev.sobSq (j : ℝ)
          (descendFun (sliceC F c t))) := by
  set N : ℝ := (Module.finrank ℝ W : ℝ) * basisSum W ^ 2 with hN
  have hN0 : 0 ≤ N := by have := basisSum_nonneg (W := W); positivity
  have hS : Measurable fun z : R4 => ENNReal.ofReal (∑ i ∈ Finset.range (j + 1),
      ‖NativeTail.dX i F z‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (continuous_finset_sum _ fun i _ =>
      ((continuous_dX hF i).norm.pow 2)).measurable
  rw [ofReal_sobXSq_eq hF, lintegral_slab t₀ t₁ hS]
  -- per time slice
  have hslice : ∀ t, ∫⁻ y in unitCube, ENNReal.ofReal (∑ i ∈ Finset.range (j + 1),
      ‖NativeTail.dX i F (spt t y)‖ ^ 2) ≤
        ENNReal.ofReal (N * ((j + 1) * 9 ^ j)) *
          ∑ c, ENNReal.ofReal (TorusSobolev.sobSq (j : ℝ) (descendFun (sliceC F c t))) := by
    intro t
    have hgc : ∀ c, ContDiff ℝ ∞ (sliceC F c t) := fun c =>
      (coordC (Module.finBasis ℝ W) c).contDiff.comp (contDiff_comp_spt hF t)
    have hint : ∀ c i, IntegrableOn (fun y => ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2)
        unitCube := fun c i =>
      integrableOn_unitCube (((hgc c).continuous_iteratedFDeriv
        (by exact_mod_cast le_top)).norm.pow 2)
    have hword : ∀ c, ∀ i ∈ Finset.range (j + 1),
        ∫ y in unitCube, ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2 ≤
          9 ^ j * TorusSobolev.sobSq (j : ℝ) (descendFun (sliceC F c t)) := by
      intro c i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h1 := integral_unitCube_norm_iteratedFDeriv_sq_le (hgc c) (isPeriodic_sliceC hper c t) i
        ((hmem c t).mono (by exact_mod_cast hij))
      have h2 : TorusSobolev.sobSq (i : ℝ) (descendFun (sliceC F c t)) ≤
          TorusSobolev.sobSq (j : ℝ) (descendFun (sliceC F c t)) :=
        TorusSobolev.coeffSobSq_mono (by exact_mod_cast hij) (hmem c t)
      have h3 : ((Fintype.card (Fin 3) : ℕ) : ℝ) ^ (2 * i) ≤ 9 ^ j := by
        rw [Fintype.card_fin, pow_mul]
        norm_num
        exact pow_le_pow_right₀ (by norm_num) hij
      have h0 := TorusSobolev.sobSq_nonneg (i : ℝ) (descendFun (sliceC F c t))
      calc ∫ y in unitCube, ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2
          ≤ ((Fintype.card (Fin 3) : ℕ) : ℝ) ^ (2 * i) *
              TorusSobolev.sobSq (i : ℝ) (descendFun (sliceC F c t)) := h1
        _ ≤ 9 ^ j * TorusSobolev.sobSq (j : ℝ) (descendFun (sliceC F c t)) :=
            mul_le_mul h3 h2 h0 (by positivity)
    have hpt := sum_norm_dX_sq_le hF j t
    calc ∫⁻ y in unitCube, ENNReal.ofReal (∑ i ∈ Finset.range (j + 1),
          ‖NativeTail.dX i F (spt t y)‖ ^ 2)
        ≤ ∫⁻ y in unitCube, ENNReal.ofReal (N * ∑ c, ∑ i ∈ Finset.range (j + 1),
            ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2) :=
          lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpt y)
      _ = ENNReal.ofReal (N * ∑ c, ∑ i ∈ Finset.range (j + 1),
            ∫ y in unitCube, ‖iteratedFDeriv ℝ i (sliceC F c t) y‖ ^ 2) := by
          rw [← ofReal_integral_eq_lintegral_ofReal]
          · congr 1
            rw [integral_const_mul, integral_finsetSum _ fun c _ =>
              integrable_finsetSum _ fun i _ => hint c i]
            congr 1
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [integral_finsetSum _ fun i _ => hint c i]
          · exact (integrable_finsetSum _ fun c _ =>
              integrable_finsetSum _ fun i _ => hint c i).const_mul N
          · exact Eventually.of_forall fun _ => mul_nonneg hN0
              (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ ≤ ENNReal.ofReal (N * ∑ c, ∑ _i ∈ Finset.range (j + 1),
            9 ^ j * TorusSobolev.sobSq (j : ℝ) (descendFun (sliceC F c t))) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hN0)
          exact Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun i hi => hword c i hi
      _ = ENNReal.ofReal (N * ((j + 1) * 9 ^ j)) *
            ∑ c, ENNReal.ofReal (TorusSobolev.sobSq (j : ℝ) (descendFun (sliceC F c t))) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => TorusSobolev.sobSq_nonneg _ _),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          push_cast; ring
  have hmeas : ∀ c, AEMeasurable (fun t => ENNReal.ofReal (TorusSobolev.sobSq (j : ℝ)
      (descendFun (sliceC F c t)))) (volume.restrict (Icc t₀ t₁)) := fun c =>
    (measurable_ofReal_sobSq_slice (continuous_sliceC hF.continuous c)
      (isPeriodic_sliceC hper c) j (hmem c)).aemeasurable
  calc ENNReal.ofReal ((2 * π) ^ 3) * ∫⁻ t in Icc t₀ t₁, ∫⁻ y in unitCube,
        ENNReal.ofReal (∑ i ∈ Finset.range (j + 1), ‖NativeTail.dX i F (spt t y)‖ ^ 2)
      ≤ ENNReal.ofReal ((2 * π) ^ 3) * ∫⁻ t in Icc t₀ t₁, ENNReal.ofReal (N * ((j + 1) * 9 ^ j)) *
          ∑ c, ENNReal.ofReal (TorusSobolev.sobSq (j : ℝ) (descendFun (sliceC F c t))) := by
        gcongr with t
        exact hslice t
    _ = ENNReal.ofReal ((2 * π) ^ 3 * N * ((j + 1) * 9 ^ j)) *
          ∑ c, ∫⁻ t in Icc t₀ t₁, ENNReal.ofReal (TorusSobolev.sobSq (j : ℝ)
            (descendFun (sliceC F c t))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun c _ => hmeas c, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [hN]; ring

end Upper

/-! ### The logarithmic upgrade in the slab norm -/

section Upgrade

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem sobXSq_le_of_sobX_le {j : ℕ} {Q : Set R4} {F : R4 → W} {ε : ℝ}
    (h : NativeTail.sobX j Q F ≤ ε) : NativeTail.sobXSq j Q F ≤ ε ^ 2 := by
  have h0 := sobXSq_nonneg j Q F
  unfold NativeTail.sobX at h
  have hs := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg (NativeTail.sobXSq j Q F)
  nlinarith

/-- **`lem:log-source-upgrade` in the space-time slab norm of `thm:native-source`.**  Fix a slab
`Q = [t₀,t₁] × (0,2π]³`, a rate `R > 0` and an order `j`.  There is `C > 0` such that every smooth
`2π`-periodic `F : ℝ⁴ → W` (`W` finite-dimensional) whose directional derivatives have analytic
growth `‖DᵖF(z)(v, …, v)‖ ≤ a p! (RK)ᵖ` (`‖v‖ ≤ 1`, every `p`, `K ≥ 1`) and
`‖F‖_{L²(Q)} ≤ ε` satisfies
`‖F‖_{L²_tH^j_x(Q)} ≤ C ε K^j [1 + log(2 + C a K^{j+3}/ε)]^j`. -/
theorem sobX_log_upgrade {t₀ t₁ : ℝ} {R : ℝ} (hR : 0 < R) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : R4 → W) (a K ε : ℝ), ContDiff ℝ ∞ F →
      DiscreteEulerConsistency.IsPeriodic (2 * π) F → 0 ≤ a → 1 ≤ K → 0 < ε →
      (∀ (z v : R4) (p : ℕ), ‖v‖ ≤ 1 →
        ‖iteratedFDeriv ℝ p F z (fun _ => v)‖ ≤ a * (p ! * (R * K) ^ p)) →
      NativeTail.sobX 0 (slab t₀ t₁) F ≤ ε →
      NativeTail.sobX j (slab t₀ t₁) F ≤
        C * ε * K ^ j * (1 + Real.log (2 + C * a * K ^ (j + 3) / ε)) ^ j := by
  set R₁ : ℝ := max R 1 with hR₁
  have hR₁1 : 1 ≤ R₁ := le_max_right _ _
  have hRR₁ : R ≤ R₁ := le_max_left _ _
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  set a₀ : ℝ := 1 / (Real.exp 1 * R₁) with ha₀def
  have ha₀ : 0 < a₀ := by positivity
  have ha₀1 : a₀ ≤ 1 := by
    rw [ha₀def, div_le_one (by positivity)]
    nlinarith
  set μ : Measure ℝ := volume.restrict (Icc t₀ t₁)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by simp)
  obtain ⟨Cu, hCu, hup⟩ := GevreyFourier.log_source_upgrade_of_decay (d := Fin 3) μ ha₀ ha₀1 j
  set b := Module.finBasis ℝ W
  set Mc : ℝ := ∑ c, ‖coordC b c‖ + 1 with hMc
  have hMc0 : 0 < Mc := by
    have : 0 ≤ ∑ c, ‖coordC b c‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hMcc : ∀ c, ‖coordC b c‖ ≤ Mc := fun c => by
    have : ‖coordC b c‖ ≤ ∑ c, ‖coordC b c‖ :=
      Finset.single_le_sum (f := fun c => ‖coordC b c‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ c)
    linarith
  set NN : ℝ := (Module.finrank ℝ W : ℝ)
  set Kc : ℝ := (2 * π) ^ 3 * (NN * basisSum W ^ 2) * ((j + 1) * 9 ^ j) with hKc
  have hKc0 : 0 ≤ Kc := by have := basisSum_nonneg (W := W); positivity
  set C : ℝ := max (Real.sqrt (Kc * NN) * Cu * Mc) (Cu * Real.exp 1) with hCdef
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro F a K ε hF hper ha hK hε hb hL2
  have hK0 : 0 < K := by linarith
  -- the slices
  have hgc : ∀ c t, Continuous (sliceC F c t) := fun c t =>
    (coordC b c).continuous.comp (hF.continuous.comp (by
      have : spt t = fun y => (Fin.cons t 0 : R4) + ((2 * π) • NativeTail.spatialL) y := by
        funext y; exact spt_eq t y
      rw [this]; exact continuous_const.add (ContinuousLinearMap.continuous _)))
  set f : Fin (Module.finrank ℝ W) → ℝ → C(UnitAddTorus (Fin 3), ℂ) := fun c t =>
    SobolevBoxCr.descend (hgc c t) (isPeriodic_sliceC hper c t) with hfdef
  have hfcoe : ∀ c t, ⇑(f c t) = descendFun (sliceC F c t) := fun c t => rfl
  -- Gevrey bounds with `R₁`
  have hb₁ : ∀ (z v : R4) (p : ℕ), ‖v‖ ≤ 1 →
      ‖iteratedFDeriv ℝ p F z (fun _ => v)‖ ≤ a * (p ! * (R₁ * K) ^ p) := by
    intro z v p hv
    refine (hb z v p hv).trans ?_
    gcongr
  -- coefficient decay
  have hdec : ∀ c t n, ‖mFourierCoeff (f c t) n‖ ≤
      (Real.exp 1 * (Mc * a)) * Real.exp (-((a₀ / K) * StripFourier.linfNorm n)) := by
    intro c t n
    rw [hfcoe]
    have hsm : ContDiff ℝ ∞ (sliceC F c t) :=
      (coordC b c).contDiff.comp (contDiff_comp_spt hF t)
    have h := GevreyFourier.norm_mFourierCoeff_le_of_gevrey hsm (isPeriodic_sliceC hper c t)
      (A := ‖coordC b c‖ * a) (R := 2 * π * (R₁ * K)) (by positivity) (by positivity)
      (fun i p y => norm_iteratedFDeriv_slice_le hF (coordC b c) hb₁ t i p y) n
    have harg : 2 * π / (Real.exp 1 * (2 * π * (R₁ * K))) = a₀ / K := by
      rw [ha₀def]; field_simp
    rw [harg] at h
    refine h.trans ?_
    gcongr
    exact hMcc c
  -- `L²` bounds of the slices
  have hsq0 : NativeTail.sobXSq 0 (slab t₀ t₁) F ≤ ε ^ 2 := sobXSq_le_of_sobX_le hL2
  have hL2c : ∀ c, ∫⁻ t, ENNReal.ofReal (∫ x, ‖f c t x‖ ^ 2) ∂μ ≤
      ENNReal.ofReal ((Mc * ε) ^ 2) := by
    intro c
    refine (lintegral_slice_sq_le hF hper (coordC b c) t₀ t₁).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 := sobXSq_nonneg 0 (slab t₀ t₁) F
    calc ‖coordC b c‖ ^ 2 * NativeTail.sobXSq 0 (slab t₀ t₁) F ≤ Mc ^ 2 * ε ^ 2 := by
          gcongr
          exact hMcc c
      _ = (Mc * ε) ^ 2 := by ring
  -- the upgrade, component by component
  set Λ : ℝ := 1 + Real.log (2 + Cu * Real.exp 1 * a * K ^ (j + 3) / ε) with hΛ
  have hup' : ∀ c, (∀ t, TorusSobolev.MemH (j : ℝ) (descendFun (sliceC F c t))) ∧
      ∫⁻ t, ENNReal.ofReal (TorusSobolev.sobSq (j : ℝ) (descendFun (sliceC F c t))) ∂μ ≤
        ENNReal.ofReal ((Cu * (Mc * ε) * K ^ j * Λ ^ j) ^ 2) := by
    intro c
    obtain ⟨hm, hbd⟩ := hup (f c) (Real.exp 1 * (Mc * a)) K (Mc * ε) (by positivity) hK
      (by positivity) (hdec c) (hL2c c)
    refine ⟨fun t => by rw [← hfcoe]; exact hm t, ?_⟩
    have harg : Cu * (Real.exp 1 * (Mc * a)) * K ^ (j + Fintype.card (Fin 3)) / (Mc * ε) =
        Cu * Real.exp 1 * a * K ^ (j + 3) / ε := by
      rw [Fintype.card_fin]; field_simp
    rw [harg] at hbd
    simpa only [hfcoe] using hbd
  -- assemble
  have hupper := ofReal_sobXSq_le hF hper j t₀ t₁ (fun c t => (hup' c).1 t)
  have hsum : ∑ c, ∫⁻ t in Icc t₀ t₁, ENNReal.ofReal (TorusSobolev.sobSq (j : ℝ)
      (descendFun (sliceC F c t))) ≤ ENNReal.ofReal (NN * (Cu * (Mc * ε) * K ^ j * Λ ^ j) ^ 2) := by
    calc ∑ c, ∫⁻ t in Icc t₀ t₁, ENNReal.ofReal (TorusSobolev.sobSq (j : ℝ)
          (descendFun (sliceC F c t)))
        ≤ ∑ _c : Fin (Module.finrank ℝ W), ENNReal.ofReal ((Cu * (Mc * ε) * K ^ j * Λ ^ j) ^ 2) :=
          Finset.sum_le_sum fun c _ => (hup' c).2
      _ = ENNReal.ofReal (NN * (Cu * (Mc * ε) * K ^ j * Λ ^ j) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have htot : NativeTail.sobXSq j (slab t₀ t₁) F ≤
      Kc * (NN * (Cu * (Mc * ε) * K ^ j * Λ ^ j) ^ 2) := by
    have h := hupper.trans (mul_le_mul_right hsum _)
    rw [← ENNReal.ofReal_mul hKc0] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hΛ1 : 1 ≤ Λ := by
    have : 0 ≤ Real.log (2 + Cu * Real.exp 1 * a * K ^ (j + 3) / ε) :=
      Real.log_nonneg (by have : 0 ≤ Cu * Real.exp 1 * a * K ^ (j + 3) / ε := by positivity
                          linarith)
    linarith
  have hΛ' : Λ ≤ 1 + Real.log (2 + C * a * K ^ (j + 3) / ε) := by
    have h1 : 0 < 2 + Cu * Real.exp 1 * a * K ^ (j + 3) / ε := by positivity
    have h2 : Cu * Real.exp 1 * a * K ^ (j + 3) / ε ≤ C * a * K ^ (j + 3) / ε := by
      gcongr
      exact le_max_right _ _
    have := Real.log_le_log h1 (by linarith : 2 + Cu * Real.exp 1 * a * K ^ (j + 3) / ε ≤
      2 + C * a * K ^ (j + 3) / ε)
    linarith
  unfold NativeTail.sobX
  calc Real.sqrt (NativeTail.sobXSq j (slab t₀ t₁) F)
      ≤ Real.sqrt (Kc * (NN * (Cu * (Mc * ε) * K ^ j * Λ ^ j) ^ 2)) := Real.sqrt_le_sqrt htot
    _ = Real.sqrt (Kc * NN) * Cu * Mc * ε * K ^ j * Λ ^ j := by
        rw [← mul_assoc, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        ring
    _ ≤ C * ε * K ^ j * (1 + Real.log (2 + C * a * K ^ (j + 3) / ε)) ^ j := by
        have hC1 : Real.sqrt (Kc * NN) * Cu * Mc ≤ C := le_max_left _ _
        have hp : Λ ^ j ≤ (1 + Real.log (2 + C * a * K ^ (j + 3) / ε)) ^ j :=
          pow_le_pow_left₀ (by linarith) hΛ' j
        calc Real.sqrt (Kc * NN) * Cu * Mc * ε * K ^ j * Λ ^ j
            = (Real.sqrt (Kc * NN) * Cu * Mc) * (ε * K ^ j) * Λ ^ j := by ring
          _ ≤ C * (ε * K ^ j) * (1 + Real.log (2 + C * a * K ^ (j + 3) / ε)) ^ j := by
              gcongr
          _ = C * ε * K ^ j * (1 + Real.log (2 + C * a * K ^ (j + 3) / ε)) ^ j := by ring

end Upgrade

end

end RenewalGeometry.NativeSlab
