/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSourceTheorem
import RenewalGeometry.Continuum.NativePhysRows

/-!
# `thm:native-source` for the physical rows (gauge directions in `𝔤`)

Einstein–Standard-Model action-closure manuscript, `thm:native-source`, all three displays, **with
the gauge rows in the gauge Lie algebra `𝔤` only**: for a continuous linear map `P_𝔤 : 𝔄 → 𝔄`
(for a slab model the projection onto `𝔤`, `SlabData.SlabModel.πg`) the finite-action budget is
`σ ≥ ‖E_h^raw(u_h) ∘ physF P_𝔤‖_{0,h;Q'}` (the raw Euler rows tested on the physical directions
`(δe, P_𝔤δA, δH, δΨ, δΨ̄)`), and the conclusions bound the physical residual maps
`𝓡_B^𝔤 = 𝓡_B ∘ gaugeProjB P_𝔤` (`NativeTail.RBP`) and `𝓡_D`:

* `eq:native-zero-source`: `‖𝓡_B^𝔤(z_h)‖_{L²(Q)} + ‖𝓡_D(z_h)‖_{L²(Q)} ≤ C ε_{0,h}`
  (**`native_zero_source_phys`**);
* `eq:native-strong-source`:
  `‖𝓡_B^𝔤(z_h)‖_{L²_tH^k_x} + ‖𝓡_D(z_h)‖_{L²_tH^{k+1}_x} ≤ C F_{h,k}` (**`native_source_phys`**);
* `eq:native-full-Cartan` (unchanged).

The proof is that of `NativeSourceThm.native_source`, composed with the fixed precomposition
operators `ρ ↦ ρ ∘ physF P_𝔤` and `ρ ↦ ρ ∘ gaugeProjB P_𝔤` (consistency, the `O(K³)` derivative of
the Euler density, the tails and the Gevrey growth of the low rows all pass through a fixed
continuous linear map; `sobX_clm_le`).  With `P_𝔤 = id` the statement is the all-directions form
`NativeSourceThm.native_source`.  Non-vacuity: `native_source_hyps_const_phys`.
-/

open MeasureTheory Filter Topology Set Finset
open scoped Real ENNReal Nat ContDiff

namespace RenewalGeometry.NativeSourceThm

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency NativeTail
open TrigInterp (recon reconLow tau)
open NativeRate (eps0 forcingBudget)
open NativeZeroSource (bufSlab)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Slab norms of fixed linear images -/

section ClmSlab

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

theorem dX_clm_comp (L : W →L[ℝ] V) {F : R4 → W} (hF : ContDiff ℝ ∞ F) (i : ℕ) (z : R4) :
    NativeTail.dX i (fun x => L (F x)) z = L.compContinuousMultilinearMap (NativeTail.dX i F z) := by
  unfold NativeTail.dX
  have e : (fun x => L (F x)) = ⇑L ∘ F := rfl
  rw [e, L.iteratedFDeriv_comp_left (hF.of_le (ContEulerBounds.natCast_le_infty i)).contDiffAt
    le_rfl]
  ext v
  rfl

theorem norm_dX_clm_comp_le (L : W →L[ℝ] V) {F : R4 → W} (hF : ContDiff ℝ ∞ F) (i : ℕ) (z : R4) :
    ‖NativeTail.dX i (fun x => L (F x)) z‖ ≤ ‖L‖ * ‖NativeTail.dX i F z‖ := by
  rw [dX_clm_comp L hF]
  exact L.norm_compContinuousMultilinearMap_le _

/-- **`‖L ∘ F‖_{L²_tH^j_x(Q)} ≤ ‖L‖ ‖F‖_{L²_tH^j_x(Q)}`** for a fixed continuous linear map `L`. -/
theorem sobX_clm_le (L : W →L[ℝ] V) {F : R4 → W} (hF : ContDiff ℝ ∞ F) (j : ℕ) (t₀ t₁ : ℝ) :
    NativeTail.sobX j (NativeSlab.slab t₀ t₁) (fun x => L (F x)) ≤
      ‖L‖ * NativeTail.sobX j (NativeSlab.slab t₀ t₁) F := by
  set sF : R4 → ℝ := fun z => ∑ i ∈ Finset.range (j + 1), ‖NativeTail.dX i F z‖ ^ 2
  set sL : R4 → ℝ := fun z => ∑ i ∈ Finset.range (j + 1),
    ‖NativeTail.dX i (fun x => L (F x)) z‖ ^ 2
  have hcF : Continuous sF := continuous_finsetSum _ fun i _ =>
    (NativeSlab.continuous_dX hF i).norm.pow 2
  have hcL : Continuous sL := continuous_finsetSum _ fun i _ =>
    (NativeSlab.continuous_dX (L.contDiff.comp hF) i).norm.pow 2
  have hpt : ∀ z, sL z ≤ ‖L‖ ^ 2 * sF z := by
    intro z
    simp only [sL, sF, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_dX_clm_comp_le L hF i z) 2
  have hmono : ∫ z in NativeSlab.slab t₀ t₁, sL z ≤
      ∫ z in NativeSlab.slab t₀ t₁, ‖L‖ ^ 2 * sF z :=
    setIntegral_mono (NativeSlab.integrableOn_slab hcL t₀ t₁)
      (NativeSlab.integrableOn_slab (continuous_const.mul hcF) t₀ t₁) hpt
  rw [integral_const_mul] at hmono
  unfold NativeTail.sobX NativeTail.sobXSq
  calc Real.sqrt (∫ z in NativeSlab.slab t₀ t₁, sL z)
      ≤ Real.sqrt (‖L‖ ^ 2 * ∫ z in NativeSlab.slab t₀ t₁, sF z) := Real.sqrt_le_sqrt hmono
    _ = ‖L‖ * Real.sqrt (∫ z in NativeSlab.slab t₀ t₁, sF z) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem norm_iteratedFDeriv_clm_comp_apply_le (L : W →L[ℝ] V) {F : R4 → W} (hF : ContDiff ℝ ∞ F)
    (p : ℕ) (z v : R4) :
    ‖iteratedFDeriv ℝ p (fun x => L (F x)) z (fun _ => v)‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ p F z (fun _ => v)‖ := by
  have e : (fun x => L (F x)) = ⇑L ∘ F := rfl
  rw [e, L.iteratedFDeriv_comp_left (hF.of_le (ContEulerBounds.natCast_le_infty p)).contDiffAt
    le_rfl]
  exact L.le_opNorm _

end ClmSlab

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

local notation "FJ" => ContEulerBounds.JS (Field 𝔄 𝓗 𝓢)
local notation "FF" => Field 𝔄 𝓗 𝓢

/-- The physical Euler covector `𝓔₀(Y) ∘ physF P_𝔤` as a field. -/
def Rphys (Pg : 𝔄 →L[ℝ] 𝔄) (Y : R4 → FF) (x : R4) : ContEulerBounds.CovV FF :=
  ContEulerBounds.preL (physF (𝓗 := 𝓗) (𝓢 := 𝓢) Pg) (Rfull D Y x)

theorem RBP_eq_Rphys (Pg : 𝔄 →L[ℝ] 𝔄) (Y : R4 → FF) :
    RBP D Pg Y = fun x => ContEulerBounds.preL (ιB (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) (Rphys D Pg Y x) :=
  funext fun x => RBP_eq D Pg Y x

theorem RD_eq_Rphys (Pg : 𝔄 →L[ℝ] 𝔄) (Y : R4 → FF) :
    RD D Y = fun x => ContEulerBounds.preL (ιS (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) (Rphys D Pg Y x) :=
  funext fun x => RD_eq_phys D Pg Y x

open Classical in
-- the assembly carries many inequalities between real and extended-real quantities
set_option maxHeartbeats 1000000 in
/-- **`eq:native-zero-source` for the physical rows** (`thm:native-source`, first display, gauge
rows in `𝔤`).  As `NativeZeroSource.native_zero_source`, with the finite-action budget
`σ ≥ ‖E_h^raw(u_h) ∘ physF P_𝔤‖_{0,h;Q'}` and the physical bosonic residual map
`𝓡_B^𝔤 = 𝓡_B ∘ gaugeProjB P_𝔤`:
`‖𝓡_B^𝔤(z_h)‖_{L²(Q)} + ‖𝓡_D(z_h)‖_{L²(Q)} ≤ C (σ + hK³)`. -/
theorem native_zero_source_phys (Pg : 𝔄 →L[ℝ] 𝔄) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {t₀ t₁ δ : ℝ} (hδ : 0 < δ) (h0 : δ < t₀)
    (h1 : t₁ + δ ≤ 2 * π) :
    ∃ C c_res τs : ℝ, 0 ≤ C ∧ 0 < c_res ∧ 0 < τs ∧ ∀ (n : ℕ) [NeZero n], Odd n →
      ∀ (u : Grid n → FF) (K σ : ℝ), 1 ≤ K → (2 * π / n) * K ≤ c_res → tau n K 3 u ≤ τs →
      (∀ x, (reconLow n K u x).1 ∈ Ke) → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      (∀ x, (recon n u x).1 ∈ Ke) → (∀ x, ‖recon n u x‖ ≤ A) → 0 ≤ σ →
      (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
          (fun x : Grid n => pos (2 * π / n) x ∈ bufSlab (t₀ - δ) (t₁ + δ)),
          ‖(eulerRow (localAction D (2 * π / n)) (2 * π / n) u x).comp (physF Pg)‖ ^ 2 ≤ σ ^ 2 →
      sobX 0 (NativeSlab.slab t₀ t₁) (RBP D Pg (recon n u)) +
          sobX 0 (NativeSlab.slab t₀ t₁) (RD D (recon n u)) ≤
        C * NativeRate.eps0 σ (2 * π / n) K := by
  set Bc : ℝ := 240 ^ 3 * (A + 1) + 1 with hBc
  obtain ⟨C₀, c₀, hc₀, hcons⟩ := native_consistency D hKe hdet A Bc
  obtain ⟨CE, hCE, hderiv⟩ := NativeZeroSource.exists_fderiv_Rfull_bound D hKe hdet A 1
  set Lp := ContEulerBounds.preL (physF (𝓗 := 𝓗) (𝓢 := 𝓢) Pg) with hLp
  set cP : ℝ := ‖Lp‖ with hcP
  have hcP0 : 0 ≤ cP := by rw [hcP]; exact ContinuousLinearMap.opNorm_nonneg _
  set V : ℝ := (MeasureTheory.volume (bufSlab (t₀ - δ) (t₁ + δ))).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set C₀' : ℝ := cP * C₀ with hC₀'
  set CE' : ℝ := cP * CE with hCE'
  have hCE'0 : 0 ≤ CE' := mul_nonneg hcP0 hCE
  set C₁ : ℝ := Real.sqrt (4 + 4 * (2 * π) ^ 4 * C₀' ^ 2 + 2 * V * CE' ^ 2) with hC₁
  refine ⟨2 * C₁, min c₀ δ, 1, by positivity, lt_min hc₀ hδ, one_pos, ?_⟩
  intro n _ hn u K σ hK hhK hτ hKel hAl hKef hAf hσ hσb
  set h : ℝ := 2 * π / n with hhdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh0 : 0 < h := by rw [hhdef]; positivity
  have hnh : (n : ℝ) * h = 2 * π := by rw [hhdef]; field_simp
  have hK0 : 0 < K := by linarith
  have hhδ : h ≤ δ := by
    have : h ≤ h * K := le_mul_of_one_le_right hh0.le hK
    linarith [min_le_right c₀ δ]
  have hhc : h * K ≤ c₀ := hhK.trans (min_le_left _ _)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hAl 0)
  set Y := recon n u with hYdef
  -- the derivative reserve of the complete field
  have hD : ∀ j, j ≤ 3 → 1 ≤ j → ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ Bc * K ^ j := by
    intro j hj _ z
    refine (NativeZeroSource.norm_iteratedFDeriv_recon_le u hK hAl hj z).trans ?_
    have : 240 ^ 3 * A + tau n K 3 u ≤ Bc := by rw [hBc]; nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  obtain ⟨-, -, hnode⟩ := hcons K hK h hh0 hhc n Y
    ((contDiff_recon u).of_le (ContEulerBounds.natCast_le_infty 3))
    (NativeZeroSource.isPeriodic_recon u) hKef hAf
    (fun z => by rw [← pow_one K]; exact hD 1 (by norm_num) le_rfl z)
    (hD 2 (by norm_num) (by norm_num)) (hD 3 le_rfl (by norm_num))
  rw [hYdef, NativeZeroSource.samp_recon hn u] at hnode
  obtain ⟨hRsm, hRd⟩ := hderiv n u K hK hτ hAl hKef hAf
  -- the physical covector field
  set RP : R4 → ContEulerBounds.CovV FF := Rphys D Pg Y with hRPdef
  have hRPfun : RP = fun y => Lp (Rfull D Y y) := rfl
  have hRPsm : ContDiff ℝ ∞ RP := by rw [hRPfun]; exact Lp.contDiff.comp hRsm
  have hRPd : ∀ y, ‖fderiv ℝ RP y‖ ≤ CE' * K ^ 3 := by
    intro y
    have hR : HasFDerivAt (Rfull D Y) (fderiv ℝ (Rfull D Y) y) y :=
      ((hRsm.differentiable (by simp)) y).hasFDerivAt
    have hL : HasFDerivAt RP (Lp.comp (fderiv ℝ (Rfull D Y) y)) y := by
      rw [hRPfun]; exact Lp.hasFDerivAt.comp y hR
    rw [hL.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [hCE', mul_assoc]
    exact mul_le_mul_of_nonneg_left (hRd y) hcP0
  -- nodal consistency for the physical rows
  have hnodeP : ∀ x : Grid n, ‖(eulerRow (localAction D h) h u x).comp (physF Pg) -
      RP (pos h x)‖ ≤ C₀' * h * K ^ 3 := by
    intro x
    have e : (eulerRow (localAction D h) h u x).comp (physF Pg) - RP (pos h x) =
        Lp (eulerRow (localAction D h) h u x - Rfull D Y (pos h x)) := by
      rw [map_sub]; rfl
    rw [e]
    refine (Lp.le_opNorm _).trans ?_
    have := hnode x
    calc cP * ‖eulerRow (localAction D h) h u x - Rfull D Y (pos h x)‖
        ≤ cP * (C₀ * h * K ^ 3) := mul_le_mul_of_nonneg_left this hcP0
      _ = C₀' * h * K ^ 3 := by rw [hC₀']; ring
  -- nodal transfer
  set Q' := bufSlab (t₀ - δ) (t₁ + δ)
  have hbuf := fun k hk => NativeZeroSource.cell_subset_bufSlab (t₀ := t₀) (t₁ := t₁) hhdef hhδ k hk
  have hRdiff : ∀ y ∈ Q', HasFDerivWithinAt RP (fderiv ℝ RP y) Q' y :=
    fun y _ => ((hRPsm.differentiable (by simp)) y).hasFDerivAt.hasFDerivWithinAt
  have hnod := NodalSourceTransfer.lintegral_sq_le_nodalMassSq (d := 4) hh0 hbuf hRdiff
    (L := CE' * K ^ 3) (fun y _ => hRPd y)
  have hmass := NativeZeroSource.nodalMassSq_le_grid hhdef (a := t₀ - δ) (b := t₁ + δ)
    (by linarith) h1 RP
  -- the grid sum
  set S := Finset.univ.filter (fun x : Grid n => pos h x ∈ Q')
  have hpt : ∀ x : Grid n, ‖RP (pos h x)‖ ^ 2 ≤
      2 * ‖(eulerRow (localAction D h) h u x).comp (physF Pg)‖ ^ 2 + 2 * (C₀' * h * K ^ 3) ^ 2 := by
    intro x
    have h1x := hnodeP x
    have : ‖RP (pos h x)‖ ≤ ‖(eulerRow (localAction D h) h u x).comp (physF Pg)‖ +
        C₀' * h * K ^ 3 := by
      have e : RP (pos h x) = (eulerRow (localAction D h) h u x).comp (physF Pg) -
          ((eulerRow (localAction D h) h u x).comp (physF Pg) - RP (pos h x)) := by abel
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl h1x)
    have h0' : 0 ≤ ‖RP (pos h x)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖(eulerRow (localAction D h) h u x).comp (physF Pg)‖ - C₀' * h * K ^ 3)]
  have hcard : h ^ 4 * (S.card : ℝ) ≤ (2 * π) ^ 4 := by
    have : (S.card : ℝ) ≤ (n : ℝ) ^ 4 := by
      have h1c : S.card ≤ Fintype.card (Grid n) := Finset.card_le_univ S
      have h2c : Fintype.card (Grid n) = n ^ 4 := by simp [ShiftedJetAction.Grid]
      exact_mod_cast h2c ▸ h1c
    calc h ^ 4 * (S.card : ℝ) ≤ h ^ 4 * (n : ℝ) ^ 4 := by gcongr
      _ = (2 * π) ^ 4 := by rw [← mul_pow, mul_comm, hnh]
  have hgrid : h ^ 4 * ∑ x ∈ S, ‖RP (pos h x)‖ ^ 2 ≤
      2 * σ ^ 2 + 2 * (2 * π) ^ 4 * (C₀' * h * K ^ 3) ^ 2 := by
    calc h ^ 4 * ∑ x ∈ S, ‖RP (pos h x)‖ ^ 2
        ≤ h ^ 4 * ∑ x ∈ S, (2 * ‖(eulerRow (localAction D h) h u x).comp (physF Pg)‖ ^ 2 +
            2 * (C₀' * h * K ^ 3) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpt x) (by positivity)
      _ = 2 * (h ^ 4 * ∑ x ∈ S, ‖(eulerRow (localAction D h) h u x).comp (physF Pg)‖ ^ 2) +
            2 * (h ^ 4 * (S.card : ℝ)) * (C₀' * h * K ^ 3) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]; ring
      _ ≤ 2 * σ ^ 2 + 2 * (2 * π) ^ 4 * (C₀' * h * K ^ 3) ^ 2 := by
          have : 0 ≤ (C₀' * h * K ^ 3) ^ 2 := sq_nonneg _
          gcongr
  -- the `L²(Q)` bound for the physical covector
  have hX : ∫⁻ y in NativeZeroSource.slabIco t₀ t₁, ‖RP y‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * σ ^ 2 + 4 * (2 * π) ^ 4 * (C₀' * h * K ^ 3) ^ 2 +
        2 * V * (h * (CE' * K ^ 3)) ^ 2) := by
    refine hnod.trans ?_
    have hVe : MeasureTheory.volume Q' = ENNReal.ofReal V := by
      rw [hV, ENNReal.ofReal_toReal (NativeZeroSource.volume_bufSlab_ne_top _ _)]
    rw [hVe]
    calc 2 * NodalSourceTransfer.nodalMassSq h Q' RP +
          2 * ENNReal.ofReal V * ENNReal.ofReal (h * (CE' * K ^ 3)) ^ 2
        ≤ 2 * ENNReal.ofReal (h ^ 4 * ∑ x ∈ S, ‖RP (pos h x)‖ ^ 2) +
          2 * ENNReal.ofReal V * ENNReal.ofReal (h * (CE' * K ^ 3)) ^ 2 := by gcongr
      _ ≤ 2 * ENNReal.ofReal (2 * σ ^ 2 + 2 * (2 * π) ^ 4 * (C₀' * h * K ^ 3) ^ 2) +
          2 * ENNReal.ofReal V * ENNReal.ofReal (h * (CE' * K ^ 3)) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal (4 * σ ^ 2 + 4 * (2 * π) ^ 4 * (C₀' * h * K ^ 3) ^ 2 +
            2 * V * (h * (CE' * K ^ 3)) ^ 2) := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          congr 1; ring
  -- each row
  have hbound : 4 * σ ^ 2 + 4 * (2 * π) ^ 4 * (C₀' * h * K ^ 3) ^ 2 +
      2 * V * (h * (CE' * K ^ 3)) ^ 2 ≤ C₁ ^ 2 * NativeRate.eps0 σ h K ^ 2 := by
    rw [hC₁, Real.sq_sqrt (by positivity)]
    have hs : σ ^ 2 ≤ NativeRate.eps0 σ h K ^ 2 := by
      unfold NativeRate.eps0
      have : 0 ≤ h * K ^ 3 := by positivity
      nlinarith
    have hk : (h * K ^ 3) ^ 2 ≤ NativeRate.eps0 σ h K ^ 2 := by
      unfold NativeRate.eps0
      have : 0 ≤ h * K ^ 3 := by positivity
      nlinarith
    have e1 : (C₀' * h * K ^ 3) ^ 2 = C₀' ^ 2 * (h * K ^ 3) ^ 2 := by ring
    have e2 : (h * (CE' * K ^ 3)) ^ 2 = CE' ^ 2 * (h * K ^ 3) ^ 2 := by ring
    rw [e1, e2]
    have : 0 ≤ (2 * π) ^ 4 * C₀' ^ 2 := by positivity
    have : 0 ≤ V * CE' ^ 2 := by positivity
    nlinarith
  have he0 : 0 ≤ NativeRate.eps0 σ h K := by unfold NativeRate.eps0; positivity
  have hC₁0 : 0 ≤ C₁ := Real.sqrt_nonneg _
  have hRBc : Continuous (RBP D Pg Y) := by
    rw [RBP_eq_Rphys]
    exact (ContEulerBounds.preL (ιB (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))).continuous.comp
      hRPsm.continuous
  have hRDc : Continuous (RD D Y) := by
    rw [RD_eq_Rphys D Pg]
    exact (ContEulerBounds.preL (ιS (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))).continuous.comp
      hRPsm.continuous
  have hB := NativeZeroSource.sobX_zero_le_of_lintegral hRBc (f := RP)
    (fun z => by rw [RBP_eq D Pg Y z]; exact norm_comp_ιB_le (RP z)) t₀ t₁ hC₁0 he0 hX
    (by positivity) hbound
  have hDr := NativeZeroSource.sobX_zero_le_of_lintegral hRDc (f := RP)
    (fun z => by rw [RD_eq_phys D Pg Y z]; exact norm_comp_ιS_le (RP z)) t₀ t₁ hC₁0 he0 hX
    (by positivity) hbound
  linarith

/-- **The strip step and `lem:log-source-upgrade` for the low-frequency physical rows** (as
`native_low_upgrade`, for `𝓡_B^𝔤 = 𝓡_B ∘ gaugeProjB P_𝔤` and `𝓡_D`). -/
theorem native_low_upgrade_phys (Pg : 𝔄 →L[ℝ] 𝔄) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) (k : ℕ) (t₀ t₁ : ℝ) :
    ∃ Cj CA : ℝ, 0 < Cj ∧ 0 < CA ∧ ∀ (n : ℕ) [NeZero n] (u : Grid n → FF) (K : ℝ), 1 ≤ K →
      (∀ x, (reconLow n K u x).1 ∈ Ke) → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      (∀ ε : ℝ, 0 < ε → sobX 0 (NativeSlab.slab t₀ t₁) (RBP D Pg (reconLow n K u)) ≤ ε →
        sobX k (NativeSlab.slab t₀ t₁) (RBP D Pg (reconLow n K u)) ≤
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
  set Lb := ContEulerBounds.preL (gaugeProjB (𝓗 := 𝓗) Pg) with hLb
  set cB : ℝ := ‖Lb‖ with hcB
  have hcB0 : 0 ≤ cB := by rw [hcB]; exact ContinuousLinearMap.opNorm_nonneg _
  refine ⟨max CuB CuD, (CG + 1) * (cB + 1), lt_of_lt_of_le hCuB (le_max_left _ _),
    by positivity, ?_⟩
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
  have hRBl := contDiff_RB D hK0 hY hch
  constructor
  · intro ε hε hL2
    have hb : ∀ (z v : R4) (p : ℕ), ‖v‖ ≤ 1 →
        ‖iteratedFDeriv ℝ p (RBP D Pg (reconLow n K u)) z (fun _ => v)‖ ≤
          (CG + 1) * (cB + 1) * K ^ 2 * (p ! * (RG * K) ^ p) := by
      intro z v p hv
      have h1 := norm_iteratedFDeriv_clm_comp_apply_le Lb hRBl p z v
      have h2 := (hgev n u K hK hKe' hA z v hv p).1
      have hfac : 0 ≤ K ^ 2 * (p ! * (RG * K) ^ p) := by positivity
      calc ‖iteratedFDeriv ℝ p (RBP D Pg (reconLow n K u)) z (fun _ => v)‖
          ≤ cB * ‖iteratedFDeriv ℝ p (RB D (reconLow n K u)) z (fun _ => v)‖ := h1
        _ ≤ cB * (CG * K ^ 2 * (p ! * (RG * K) ^ p)) := mul_le_mul_of_nonneg_left h2 hcB0
        _ ≤ (CG + 1) * (cB + 1) * K ^ 2 * (p ! * (RG * K) ^ p) := by nlinarith
    have h := hupB (RBP D Pg (reconLow n K u)) ((CG + 1) * (cB + 1) * K ^ 2) K ε
      (contDiff_RBP D Pg hK0 hY hch) (isPeriodic_RBP D Pg (isPeriodic_RB D hper))
      (by positivity) hK hε hb hL2
    have e : (CG + 1) * (cB + 1) * K ^ 2 = (CG + 1) * (cB + 1) * K ^ 2 := rfl
    exact h.trans (hmono CuB (max CuB CuD) ((CG + 1) * (cB + 1) * K ^ 2) k ε hε (by positivity)
      hCuB (le_max_left _ _))
  · intro ε hε hL2
    have hb : ∀ (z v : R4) (p : ℕ), ‖v‖ ≤ 1 →
        ‖iteratedFDeriv ℝ p (RD D (reconLow n K u)) z (fun _ => v)‖ ≤
          (CG + 1) * (cB + 1) * K * (p ! * (RG * K) ^ p) := by
      intro z v p hv
      refine ((hgev n u K hK hKe' hA z v hv p).2).trans ?_
      have hX : 0 ≤ K * (p ! * (RG * K) ^ p) := by positivity
      have e : (CG + 1) * (cB + 1) * K * (p ! * (RG * K) ^ p) =
          CG * K * (p ! * (RG * K) ^ p) + (CG * cB + cB + 1) * (K * (p ! * (RG * K) ^ p)) := by ring
      rw [e]
      have : 0 ≤ (CG * cB + cB + 1) * (K * (p ! * (RG * K) ^ p)) := by positivity
      linarith
    have h := hupD (RD D (reconLow n K u)) ((CG + 1) * (cB + 1) * K) K ε (contDiff_RD D hK0 hY hch)
      (isPeriodic_RD D hper) (by positivity) hK hε hb hL2
    exact h.trans (hmono CuD (max CuB CuD) ((CG + 1) * (cB + 1) * K) (k + 1) ε hε (by positivity)
      hCuD (le_max_right _ _))


open Classical in
-- the final assembly combines the four inputs of `native_source_assembly`
set_option maxHeartbeats 2000000 in
/-- **`thm:native-source` with the gauge rows in `𝔤`** (leakage-tolerant physical forcing estimate,
all three displays, physical rows).  Fix a continuous linear map `P_𝔤 : 𝔄 → 𝔄` (for a slab model
the projection onto the gauge Lie algebra, `SlabData.SlabModel.πg`), a compact coframe chart
`K_e ⊂ {det e > 0}`, an amplitude bound `A`, an order `k ≥ 1`, the budget constant `C_k > 0` and
buffered slabs `Q = [t₀,t₁] × 𝕋³ ⋐ Q' = [t₀-δ, t₁+δ) × 𝕋³` inside one period.  There are `C`,
`c_res > 0`, `τ_* > 0` such that for every odd `n` (`h = 2π/n`), every record `u_h` whose complete
reconstruction `z_h` and low head `z_h^lo` lie in the chart with amplitudes `≤ A`, every `K ≥ 1` with
`hK ≤ c_res`, `τ_{h,k+2}(K) ≤ τ_*`, and every `σ_h ≥ ‖E_h^raw(u_h) ∘ physF P_𝔤‖_{0,h;Q'}` (the
finite-action covector norm of the **physical** raw rows: coframe, `𝔤`-gauge, Higgs, spinor and
co-spinor directions):
1. `eq:native-zero-source`: `‖𝓡_B^𝔤(z_h)‖_{L²(Q)} + ‖𝓡_D(z_h)‖_{L²(Q)} ≤ C ε_{0,h}`;
2. `eq:native-strong-source`:
   `‖𝓡_B^𝔤(z_h)‖_{L²_tH^k_x(Q)} + ‖𝓡_D(z_h)‖_{L²_tH^{k+1}_x(Q)} ≤ C F_{h,k}`;
3. `eq:native-full-Cartan`: at every point `z` of the cell of every node `x`,
   `‖R_h^{raw}(u_h)_{μν}(x) - e Riem_{μν}(g_h)(z) e⁻¹‖ ≤ C h K³`.
Here `𝓡_B^𝔤 = 𝓡_B ∘ gaugeProjB P_𝔤` (`NativeTail.RBP`). -/
theorem native_source_phys (Pg : 𝔄 →L[ℝ] 𝔄) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) (k : ℕ) (hk : 1 ≤ k) {Ck : ℝ} (hCk : 0 < Ck)
    {t₀ t₁ δ : ℝ} (hδ : 0 < δ) (h0 : δ < t₀) (h1 : t₁ + δ ≤ 2 * π) :
    ∃ C c_res τs : ℝ, 0 ≤ C ∧ 0 < c_res ∧ 0 < τs ∧ ∀ (n : ℕ) [NeZero n], Odd n →
      ∀ (u : Grid n → FF) (K σ : ℝ), 1 ≤ K → (2 * π / n) * K ≤ c_res →
      tau n K (k + 2) u ≤ τs →
      (∀ x, (reconLow n K u x).1 ∈ Ke) → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      (∀ x, (recon n u x).1 ∈ Ke) → (∀ x, ‖recon n u x‖ ≤ A) → 0 ≤ σ →
      (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
          (fun x : Grid n => pos (2 * π / n) x ∈ NativeZeroSource.bufSlab (t₀ - δ) (t₁ + δ)),
          ‖(eulerRow (localAction D (2 * π / n)) (2 * π / n) u x).comp (physF Pg)‖ ^ 2 ≤ σ ^ 2 →
      (sobX 0 (NativeSlab.slab t₀ t₁) (RBP D Pg (recon n u)) +
          sobX 0 (NativeSlab.slab t₀ t₁) (RD D (recon n u)) ≤ C * eps0 σ (2 * π / n) K) ∧
      (sobX k (NativeSlab.slab t₀ t₁) (RBP D Pg (recon n u)) +
          sobX (k + 1) (NativeSlab.slab t₀ t₁) (RD D (recon n u)) ≤
        C * forcingBudget k Ck σ (2 * π / n) K (tau n K 2 u) (tau n K (k + 2) u)) ∧
      (∀ (x : Grid n) (z : R4), ‖z - pos (2 * π / n) x‖ ≤ 2 * π / n → ∀ μ ν : Fin 4,
        ‖cartanCurvature (2 * π / n) (coframe u) x μ ν -
          matToOp ((recon n u z).1 * riemMat (fun z => (recon n u z).1) z μ ν *
            ((recon n u z).1)⁻¹)‖ ≤ C * (2 * π / n) * K ^ 3) := by
  have ht0 : 0 ≤ t₀ := by linarith
  have ht1 : t₁ ≤ 2 * π := by linarith
  obtain ⟨Cz, cz, τz, hCz, hcz, hτz, hzero⟩ := native_zero_source_phys D Pg hKe hdet A hδ h0 h1
  obtain ⟨Ct0, τt, hCt0, hτt, htail⟩ := native_source_tail D hKe hdet A k
  obtain ⟨Cj, CA, hCj, hCA, hlow⟩ := native_low_upgrade_phys D Pg hKe hdet A k t₀ t₁
  set Lb := ContEulerBounds.preL (gaugeProjB (𝓗 := 𝓗) Pg) with hLb
  set cB : ℝ := ‖Lb‖ with hcB
  have hcB0 : 0 ≤ cB := by rw [hcB]; exact ContinuousLinearMap.opNorm_nonneg _
  set Ct : ℝ := (cB + 1) * Ct0 with hCtdef
  have hCt : 0 ≤ Ct := by positivity
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
  have hτz' : tau n K 3 u ≤ τz :=
    hτ3.trans (hτmin.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hτt' : tau n K (k + 2) u ≤ τt := hτmin.trans ((min_le_left _ _).trans (min_le_right _ _))
  -- (0) the zero-order source
  have hZ := hzero n hn u K σ hK (hhK.trans (min_le_left _ _)) hτz' hKel hAl hKef hAf hσ hσb
  -- smoothness of the rows
  have hYf : ContDiff ℝ ∞ (recon n u) := contDiff_recon u
  have hYl : ContDiff ℝ ∞ (reconLow n K u) := contDiff_reconLow u K
  have hchf := chartU_of_mem (K := K) hdet hKef
  have hchl := chartU_of_mem (K := K) hdet hKel
  have hRBf0 := contDiff_RB D hK0 hYf hchf
  have hRBl0 := contDiff_RB D hK0 hYl hchl
  have hRBf := contDiff_RBP D Pg hK0 hYf hchf
  have hRBl := contDiff_RBP D Pg hK0 hYl hchl
  have hRDf := contDiff_RD D hK0 hYf hchf
  have hRDl := contDiff_RD D hK0 hYl hchl
  -- the tail clauses, transported to the physical rows
  obtain ⟨htk0, ht20⟩ := htail n u K hK hτt' hKel hAl (NativeSlab.slab t₀ t₁)
    (NativeSlab.slab_subset_box ht0 ht1)
  have hdiff : ∀ j, sobX j (NativeSlab.slab t₀ t₁)
      (fun x => RBP D Pg (recon n u) x - RBP D Pg (reconLow n K u) x) ≤
      cB * sobX j (NativeSlab.slab t₀ t₁)
        (fun x => RB D (recon n u) x - RB D (reconLow n K u) x) := by
    intro j
    have e : (fun x => RBP D Pg (recon n u) x - RBP D Pg (reconLow n K u) x) =
        fun x => Lb (RB D (recon n u) x - RB D (reconLow n K u) x) := by
      funext x; rw [map_sub]; rfl
    rw [e]
    exact sobX_clm_le Lb (hRBf0.sub hRBl0) j t₀ t₁
  have hcomb : ∀ (j j' : ℕ) (X : ℝ), sobX j (NativeSlab.slab t₀ t₁)
      (fun x => RB D (recon n u) x - RB D (reconLow n K u) x) +
      sobX j' (NativeSlab.slab t₀ t₁)
        (fun x => RD D (recon n u) x - RD D (reconLow n K u) x) ≤ Ct0 * X →
      sobX j (NativeSlab.slab t₀ t₁)
        (fun x => RBP D Pg (recon n u) x - RBP D Pg (reconLow n K u) x) +
      sobX j' (NativeSlab.slab t₀ t₁)
        (fun x => RD D (recon n u) x - RD D (reconLow n K u) x) ≤ Ct * X := by
    intro j j' X hX
    have h1 := hdiff j
    have hb0 := sobX_nonneg j (NativeSlab.slab t₀ t₁)
      (fun x => RB D (recon n u) x - RB D (reconLow n K u) x)
    have hd0 := sobX_nonneg j' (NativeSlab.slab t₀ t₁)
      (fun x => RD D (recon n u) x - RD D (reconLow n K u) x)
    calc _ ≤ cB * sobX j (NativeSlab.slab t₀ t₁)
          (fun x => RB D (recon n u) x - RB D (reconLow n K u) x) +
        sobX j' (NativeSlab.slab t₀ t₁)
          (fun x => RD D (recon n u) x - RD D (reconLow n K u) x) := by linarith
      _ ≤ (cB + 1) * (sobX j (NativeSlab.slab t₀ t₁)
          (fun x => RB D (recon n u) x - RB D (reconLow n K u) x) +
        sobX j' (NativeSlab.slab t₀ t₁)
          (fun x => RD D (recon n u) x - RD D (reconLow n K u) x)) := by nlinarith
      _ ≤ (cB + 1) * (Ct0 * X) := mul_le_mul_of_nonneg_left hX (by positivity)
      _ = Ct * X := by rw [hCtdef]; ring
  have htk := hcomb k (k + 1) (K ^ (k + 2) * tau n K (k + 2) u)
    (by rw [← mul_assoc]; exact htk0)
  have ht2 := hcomb 0 0 (K ^ 2 * tau n K 2 u) (by rw [← mul_assoc]; exact ht20)
  rw [← mul_assoc] at htk ht2
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
    (eB := sobX 0 (NativeSlab.slab t₀ t₁) (RBP D Pg (recon n u)))
    (eD := sobX 0 (NativeSlab.slab t₀ t₁) (RD D (recon n u)))
    (eBlo := sobX 0 (NativeSlab.slab t₀ t₁) (RBP D Pg (reconLow n K u)))
    (eDlo := sobX 0 (NativeSlab.slab t₀ t₁) (RD D (reconLow n K u)))
    (YB := sobX k (NativeSlab.slab t₀ t₁) (RBP D Pg (recon n u)))
    (YD := sobX (k + 1) (NativeSlab.slab t₀ t₁) (RD D (recon n u)))
    (YBlo := sobX k (NativeSlab.slab t₀ t₁) (RBP D Pg (reconLow n K u)))
    (YDlo := sobX (k + 1) (NativeSlab.slab t₀ t₁) (RD D (reconLow n K u)))
    hCk hh0 hK hσ hτ20 hτm0 hCz hCt hCj hCA (sobX_nonneg _ _ _) (sobX_nonneg _ _ _) hZ
    (by
      have := trB0.2
      have hd : sobX 0 (NativeSlab.slab t₀ t₁)
          (fun x => RBP D Pg (recon n u) x - RBP D Pg (reconLow n K u) x) ≤
          Ct * K ^ 2 * tau n K 2 u := by
        have := sobX_nonneg 0 (NativeSlab.slab t₀ t₁)
          (fun x => RD D (recon n u) x - RD D (reconLow n K u) x); linarith
      linarith)
    (by
      have := trD0.2
      have hd : sobX 0 (NativeSlab.slab t₀ t₁)
          (fun x => RD D (recon n u) x - RD D (reconLow n K u) x) ≤
          Ct * K ^ 2 * tau n K 2 u := by
        have := sobX_nonneg 0 (NativeSlab.slab t₀ t₁)
          (fun x => RBP D Pg (recon n u) x - RBP D Pg (reconLow n K u) x); linarith
      linarith)
    hlB hlD
    (by
      have := trBk.1
      have hd : sobX k (NativeSlab.slab t₀ t₁)
          (fun x => RBP D Pg (recon n u) x - RBP D Pg (reconLow n K u) x) ≤
          Ct * K ^ (k + 2) * tau n K (k + 2) u := by
        have := sobX_nonneg (k + 1) (NativeSlab.slab t₀ t₁)
          (fun x => RD D (recon n u) x - RD D (reconLow n K u) x); linarith
      linarith)
    (by
      have := trDk.1
      have hd : sobX (k + 1) (NativeSlab.slab t₀ t₁)
          (fun x => RD D (recon n u) x - RD D (reconLow n K u) x) ≤
          Ct * K ^ (k + 2) * tau n K (k + 2) u := by
        have := sobX_nonneg k (NativeSlab.slab t₀ t₁)
          (fun x => RBP D Pg (recon n u) x - RBP D Pg (reconLow n K u) x); linarith
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
      have : 240 ^ 3 * A + tau n K 3 u ≤ Bc := by
        have hτ1 : tau n K 3 u ≤ 1 := hτ3.trans (hτmin.trans (min_le_right _ _))
        rw [hBc]; nlinarith
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

open Classical in
/-- **Non-vacuity of `native_source_phys`**: a constant record whose value `w` has coframe in
`K_e` satisfies every record hypothesis with `A = ‖w‖`, and the physical finite-action hypothesis
holds with `σ = (h⁴ Σ_{x ∈ Q'_h} ‖E_h^raw(u_h)(x) ∘ physF P_𝔤‖²)^{1/2}`. -/
theorem native_source_hyps_const_phys (Pg : 𝔄 →L[ℝ] 𝔄) (w : Field 𝔄 𝓗 𝓢) {Ke : Set Mat}
    (hw : w.1 ∈ Ke) {n : ℕ} [NeZero n] (hn : Odd n) {K : ℝ} (hK : 0 ≤ K) (k : ℕ)
    (Q' : Set R4) :
    tau n K (k + 2) (fun _ : Grid n => w) = 0 ∧
      (∀ x, (reconLow n K (fun _ : Grid n => w) x).1 ∈ Ke) ∧
      (∀ x, ‖reconLow n K (fun _ : Grid n => w) x‖ ≤ ‖w‖) ∧
      (∀ x, (recon n (fun _ : Grid n => w) x).1 ∈ Ke) ∧
      (∀ x, ‖recon n (fun _ : Grid n => w) x‖ ≤ ‖w‖) ∧
      (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos (2 * π / n) x ∈ Q'),
          ‖(eulerRow (localAction D (2 * π / n)) (2 * π / n) (fun _ : Grid n => w) x).comp
            (physF Pg)‖ ^ 2 ≤
        (Real.sqrt ((2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
          (fun x : Grid n => pos (2 * π / n) x ∈ Q'),
          ‖(eulerRow (localAction D (2 * π / n)) (2 * π / n) (fun _ : Grid n => w) x).comp
            (physF Pg)‖ ^ 2)) ^ 2 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := native_source_hyps_const D w hw hn hK k Q'
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rw [Real.sq_sqrt (by positivity)]

end

end RenewalGeometry.NativeSourceThm
