/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeTailTransfer

/-!
# The source-tail transfer for the record's reconstruction (`eq:native-source-tail`)

Einstein–Standard-Model action-closure manuscript, `lem:native-tail-transfer`: instantiation of
the pointwise residual-difference bounds of `NativeTailTransfer` with the complete reconstruction
`z_h = 𝓘_h^trig u_h` and the low-frequency head `z_h^lo` of a record `u_h` on `(ℤ/n)⁴`.

* `resc_reconLow_bound`, `resc_tail_bound`, `resc_recon_bound`: after the amplitude-preserving
  rescaling `ξ = Kx` the low head has `K`-independent derivative bounds (Bernstein,
  `‖D^p z̃^lo‖ ≤ 240^p A`), the tail has `‖D^p(z̃ - z̃^lo)‖ ≤ τ_{h,m}(K)` for `p ≤ m`.
* **`native_source_tail`** (`eq:native-source-tail` and the zero-order source difference): for a
  compact coframe chart `K_e ⊂ {det e > 0}`, an amplitude bound `A` and `k`, there are `C` and
  `τ_* > 0` such that for every record, every `K ≥ 1` with `τ_{h,k+2}(K) ≤ τ_*` and a low head with
  coframe values in `K_e` and `|z^lo| ≤ A`, on every slab `Q` of the periodic box
  `‖𝓡_B(z) - 𝓡_B(z^lo)‖_{L²_tH^k_x(Q)} + ‖𝓡_D(z) - 𝓡_D(z^lo)‖_{L²_tH^{k+1}_x(Q)} ≤ C K^{k+2} τ_{h,k+2}`
  and `‖𝓡_B(z) - 𝓡_B(z^lo)‖_{L²(Q)} + ‖𝓡_D(z) - 𝓡_D(z^lo)‖_{L²(Q)} ≤ C K² τ_{h,2}`.
  The constants depend on the chart, `A`, `k` and the coefficient bank, not on `h`, `K`, `n` or
  the record.
-/

open Finset Filter Topology Metric Set NormedSpace MeasureTheory
open scoped ContDiff

namespace RenewalGeometry.NativeTail

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency
open ContEulerBounds (JS jetP jetQ eulerOp contEuler_eq_eulerOp inlJ slotJ inrP)
open TrigInterp (recon reconLow tau)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

local notation "FJ" => JS (Field 𝔄 𝓗 𝓢)

/-! ### Rescaled bounds for the reconstruction -/

section Rescaled

variable {n : ℕ} [NeZero n] (u : (Fin 4 → ZMod n) → Field 𝔄 𝓗 𝓢) {K : ℝ}

theorem contDiff_recon : ContDiff ℝ ∞ (recon n u) := VecTrig.contDiff_tp _ _

theorem contDiff_reconLow (K : ℝ) : ContDiff ℝ ∞ (reconLow n K u) := VecTrig.contDiff_tp _ _

theorem resc_reconLow_bound (hK : 1 ≤ K) {A : ℝ} (hA : ∀ y, ‖reconLow n K u y‖ ≤ A) (p : ℕ)
    (ξ : R4) : ‖iteratedFDeriv ℝ p (resc K (reconLow n K u)) ξ‖ ≤ 240 ^ p * A := by
  have hK0 : 0 < K := by linarith
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  refine (norm_iteratedFDeriv_comp_smul_le (contDiff_reconLow u K) K⁻¹ p ξ).trans ?_
  have hb := TrigInterp.norm_iteratedFDeriv_reconLow_le n hK0.le u hA p (K⁻¹ • ξ)
  rw [abs_of_pos (inv_pos.mpr hK0)]
  calc K⁻¹ ^ p * ‖iteratedFDeriv ℝ p (reconLow n K u) (K⁻¹ • ξ)‖
      ≤ K⁻¹ ^ p * ((60 * (4 : ℕ) * K) ^ p * A) := by gcongr
    _ = 240 ^ p * A := by
        rw [← mul_assoc, ← mul_pow]
        congr 1
        push_cast
        field_simp
        ring

theorem resc_tail_bound (hK : 1 ≤ K) {p m : ℕ} (hpm : p ≤ m) (ξ : R4) :
    ‖iteratedFDeriv ℝ p (resc K (recon n u) - resc K (reconLow n K u)) ξ‖ ≤ tau n K m u := by
  have hK0 : 0 < K := by linarith
  have hfun : resc K (recon n u) - resc K (reconLow n K u) =
      fun ξ => (fun x => recon n u x - reconLow n K u x) (K⁻¹ • ξ) := by
    funext ξ; rfl
  rw [hfun]
  refine (norm_iteratedFDeriv_comp_smul_le ((contDiff_recon u).sub (contDiff_reconLow u K))
    K⁻¹ p ξ).trans ?_
  have hb := TrigInterp.norm_iteratedFDeriv_tail_le n hK0 u hpm (K⁻¹ • ξ)
  rw [abs_of_pos (inv_pos.mpr hK0)]
  have hτ := TrigInterp.tau_nonneg n hK0 m u
  calc K⁻¹ ^ p * ‖iteratedFDeriv ℝ p (fun x => recon n u x - reconLow n K u x) (K⁻¹ • ξ)‖
      ≤ K⁻¹ ^ p * (K ^ p * tau n K m u) := by gcongr
    _ = tau n K m u := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hK0.ne', one_pow, one_mul]

theorem resc_recon_bound (hK : 1 ≤ K) {A : ℝ} (hA : ∀ y, ‖reconLow n K u y‖ ≤ A) {p m : ℕ}
    (hpm : p ≤ m) (ξ : R4) :
    ‖iteratedFDeriv ℝ p (resc K (recon n u)) ξ‖ ≤ 240 ^ p * A + tau n K m u := by
  have hlo : ContDiff ℝ ∞ (resc K (reconLow n K u)) :=
    (contDiff_reconLow u K).comp (contDiff_const_smul K⁻¹)
  have hfu : ContDiff ℝ ∞ (resc K (recon n u)) := (contDiff_recon u).comp (contDiff_const_smul K⁻¹)
  have hp := ContEulerBounds.natCast_le_infty p
  have e : resc K (recon n u) = resc K (reconLow n K u) +
      (resc K (recon n u) - resc K (reconLow n K u)) := by abel
  rw [e, iteratedFDeriv_add_apply (f := resc K (reconLow n K u))
    (g := resc K (recon n u) - resc K (reconLow n K u)) (hlo.of_le hp).contDiffAt
    ((hfu.sub hlo).of_le hp).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (resc_reconLow_bound u hK hA p ξ)
    (resc_tail_bound u hK hpm ξ))

end Rescaled


/-! ### Smoothness of the residual maps -/

theorem contDiff_RB {K : ℝ} (hK : 0 < K) {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hch : ∀ ξ, ((K⁻¹, jet1 (resc K Y) ξ) : ℝ × FJ) ∈ chartU) : ContDiff ℝ ∞ (RB D Y) := by
  rw [RB_fun_scale D hK.ne' Y hch]
  have hE := ContEulerBounds.contDiff_eulerOp (contDiffOn_Gd D)
    (hY.comp (contDiff_const_smul K⁻¹)) hch
  exact (contDiff_const (c := (K ^ 2 : ℝ))).smul ((ContEulerBounds.preL ιB).contDiff.comp
    (hE.comp (contDiff_const_smul K)))

theorem contDiff_RD {K : ℝ} (hK : 0 < K) {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hch : ∀ ξ, ((K⁻¹, jet1 (resc K Y) ξ) : ℝ × FJ) ∈ chartU) : ContDiff ℝ ∞ (RD D Y) := by
  rw [RD_fun_scale D hK Y hY hch]
  have hF := ContEulerBounds.contDiff_foOp (contDiffOn_G1D D) (fun μ => contDiffOn_ellD D μ)
    (hY.comp (contDiff_const_smul K⁻¹)) hch (fun ξ => hch ξ)
  exact (contDiff_const (c := K)).smul ((ContinuousLinearMap.id ℝ _).contDiff.comp
    (hF.comp (contDiff_const_smul K)))

/-! ### Uniform constants on the chart -/

/-- The compact set of normalised first jets `[0,1] × {e ∈ K_e, |w| ≤ A} × {|p| ≤ B₁}`. -/
def jetSet (Ke : Set Mat) (A B₁ : ℝ) : Set (ℝ × FJ) :=
  Icc (0 : ℝ) 1 ×ˢ (({w : Field 𝔄 𝓗 𝓢 | w.1 ∈ Ke} ∩ closedBall 0 A) ×ˢ closedBall 0 B₁)

/-- The compact set of normalised values `[0,1] × {e ∈ K_e, |w| ≤ A}`. -/
def valSet (Ke : Set Mat) (A : ℝ) : Set (ℝ × Field 𝔄 𝓗 𝓢) :=
  Icc (0 : ℝ) 1 ×ˢ ({w : Field 𝔄 𝓗 𝓢 | w.1 ∈ Ke} ∩ closedBall 0 A)

variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

theorem isCompact_valPart {Ke : Set Mat} (hKe : IsCompact Ke) (A : ℝ) :
    IsCompact ({w : Field 𝔄 𝓗 𝓢 | w.1 ∈ Ke} ∩ closedBall 0 A) :=
  (isCompact_closedBall _ _).inter_left (hKe.isClosed.preimage continuous_fst)

theorem isCompact_jetSet {Ke : Set Mat} (hKe : IsCompact Ke) (A B₁ : ℝ) :
    IsCompact (jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A B₁) :=
  isCompact_Icc.prod ((isCompact_valPart hKe A).prod (isCompact_closedBall _ _))

theorem isCompact_valSet {Ke : Set Mat} (hKe : IsCompact Ke) (A : ℝ) :
    IsCompact (valSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A) :=
  isCompact_Icc.prod (isCompact_valPart hKe A)

theorem jetSet_subset {Ke : Set Mat} (hdet : ∀ e ∈ Ke, 0 < e.det) (A B₁ : ℝ) :
    jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A B₁ ⊆ chartU := fun q hq =>
  (hdet _ hq.2.1.1).ne'

theorem valSet_subset {Ke : Set Mat} (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) :
    valSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A ⊆ chartW := fun q hq =>
  (hdet _ hq.2.1).ne'

/-- **The uniform constants**: a margin `δ` and a bound `M` for the derivatives (orders `≤ N`) of the
gradient `Gd`, the Dirac coefficient `G₁` and the spinor coefficients `ℓ_μ` on the `δ`-thickenings
of the compact jet sets. -/
theorem exists_native_constants {Ke : Set Mat} (hKe : IsCompact Ke)
    (hdet : ∀ e ∈ Ke, 0 < e.det) (A B₁ : ℝ) (N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 ≤ M ∧
      cthickening δ (jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A B₁) ⊆ chartU ∧
      cthickening δ (valSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A) ⊆ chartW ∧
      (∀ y ∈ cthickening δ (jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A B₁), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (Gd D) y‖ ≤ M ∧ ‖iteratedFDeriv ℝ k (G1D D) y‖ ≤ M) ∧
      (∀ y ∈ cthickening δ (valSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A), ∀ μ, ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (ellD D μ) y‖ ≤ M) := by
  obtain ⟨δ₁, hδ₁, M₁, hM₁, hs₁, hb₁⟩ := exists_deriv_bound_cthickening isOpen_chartU
    (contDiffOn_Gd D) (isCompact_jetSet hKe A B₁) (jetSet_subset hdet A B₁) N
  obtain ⟨δ₂, hδ₂, M₂, hM₂, hs₂, hb₂⟩ := exists_deriv_bound_cthickening isOpen_chartU
    (contDiffOn_G1D D) (isCompact_jetSet hKe A B₁) (jetSet_subset hdet A B₁) N
  have hell : ∀ μ : Fin 4, ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 ≤ M ∧
      cthickening δ (valSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A) ⊆ chartW ∧
      ∀ y ∈ cthickening δ (valSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (ellD D μ) y‖ ≤ M := fun μ =>
    exists_deriv_bound_cthickening isOpen_chartW (contDiffOn_ellD D μ)
      (isCompact_valSet hKe A) (valSet_subset hdet A) N
  choose δf hδf Mf hMf hsf hbf using hell
  set δ₃ := Finset.univ.inf' Finset.univ_nonempty δf with hδ₃
  have hδ₃pos : 0 < δ₃ := by
    rw [hδ₃, Finset.lt_inf'_iff]; exact fun μ _ => hδf μ
  have hδ₃le : ∀ μ, δ₃ ≤ δf μ := fun μ => Finset.inf'_le _ (Finset.mem_univ μ)
  set δ := min δ₁ (min δ₂ δ₃)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ hδ₃pos)
  have hδ1 : δ ≤ δ₁ := min_le_left _ _
  have hδ2 : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : ∀ μ, δ ≤ δf μ := fun μ => ((min_le_right _ _).trans (min_le_right _ _)).trans (hδ₃le μ)
  have hsum0 : 0 ≤ ∑ μ, Mf μ := Finset.sum_nonneg fun μ _ => hMf μ
  have hMtot : 0 ≤ M₁ + M₂ + ∑ μ, Mf μ := by linarith
  refine ⟨δ, hδ, M₁ + M₂ + ∑ μ, Mf μ, hMtot, (cthickening_mono hδ1 _).trans hs₁,
    (cthickening_mono (hδ3 0) _).trans (hsf 0), fun y hy k hk => ⟨?_, ?_⟩, fun y hy μ k hk => ?_⟩
  · have := hb₁ y (cthickening_mono hδ1 _ hy) k hk
    have : 0 ≤ ∑ μ, Mf μ := Finset.sum_nonneg fun μ _ => hMf μ
    linarith
  · have := hb₂ y (cthickening_mono hδ2 _ hy) k hk
    have : 0 ≤ ∑ μ, Mf μ := Finset.sum_nonneg fun μ _ => hMf μ
    linarith
  · have h1 := hbf μ y (cthickening_mono (hδ3 μ) _ hy) k hk
    have h2 : Mf μ ≤ ∑ μ, Mf μ := Finset.single_le_sum (f := Mf) (fun μ _ => hMf μ)
      (Finset.mem_univ μ)
    linarith


/-! ### Jet bounds for the rescaled reconstruction -/

section JetBounds

variable {n : ℕ} [NeZero n] (u : (Fin 4 → ZMod n) → Field 𝔄 𝓗 𝓢) {K : ℝ}

theorem jet1_resc_low_bound (hK : 1 ≤ K) {A : ℝ} (hA : ∀ y, ‖reconLow n K u y‖ ≤ A) (p : ℕ)
    (ξ : R4) : ‖iteratedFDeriv ℝ p (jet1 (resc K (reconLow n K u))) ξ‖ ≤ 5 * 240 ^ (p + 1) * A := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hsm : ContDiff ℝ (p + 1) (resc K (reconLow n K u)) :=
    ((contDiff_reconLow u K).comp (contDiff_const_smul K⁻¹)).of_le
      (ContEulerBounds.natCast_le_infty (p + 1))
  refine (ContEulerBounds.norm_iteratedFDeriv_jet1_le hsm ξ).trans ?_
  have h1 := resc_reconLow_bound u hK hA p ξ
  have h2 := resc_reconLow_bound u hK hA (p + 1) ξ
  have : (240 : ℝ) ^ p ≤ 240 ^ (p + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ p)
  nlinarith

theorem jet1_resc_full_bound (hK : 1 ≤ K) {A : ℝ} (hA : ∀ y, ‖reconLow n K u y‖ ≤ A) {p m : ℕ}
    (hpm : p + 1 ≤ m) (ξ : R4) :
    ‖iteratedFDeriv ℝ p (jet1 (resc K (recon n u))) ξ‖ ≤
      5 * 240 ^ (p + 1) * A + 5 * tau n K m u := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hsm : ContDiff ℝ (p + 1) (resc K (recon n u)) :=
    ((contDiff_recon u).comp (contDiff_const_smul K⁻¹)).of_le
      (ContEulerBounds.natCast_le_infty (p + 1))
  refine (ContEulerBounds.norm_iteratedFDeriv_jet1_le hsm ξ).trans ?_
  have h1 := resc_recon_bound u hK hA (p := p) (m := m) (by omega) ξ
  have h2 := resc_recon_bound u hK hA (p := p + 1) (m := m) hpm ξ
  have : (240 : ℝ) ^ p ≤ 240 ^ (p + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ p)
  nlinarith

theorem jet1_resc_tail_bound (hK : 1 ≤ K) {p m : ℕ} (hpm : p + 1 ≤ m) (ξ : R4) :
    ‖iteratedFDeriv ℝ p (jet1 (resc K (recon n u) - resc K (reconLow n K u))) ξ‖ ≤
      5 * tau n K m u := by
  have hsm : ContDiff ℝ (p + 1) (resc K (recon n u) - resc K (reconLow n K u)) :=
    (((contDiff_recon u).comp (contDiff_const_smul K⁻¹)).sub
      ((contDiff_reconLow u K).comp (contDiff_const_smul K⁻¹))).of_le
        (ContEulerBounds.natCast_le_infty (p + 1))
  refine (ContEulerBounds.norm_iteratedFDeriv_jet1_le hsm ξ).trans ?_
  have h1 := resc_tail_bound u hK (p := p) (m := m) (by omega) ξ
  have h2 := resc_tail_bound u hK (p := p + 1) (m := m) hpm ξ
  linarith

/-- The normalised first jet of the low head lies in the compact jet set. -/
theorem jetP_resc_low_mem (hK : 1 ≤ K) {Ke : Set Mat} {A : ℝ}
    (hKe : ∀ x, (reconLow n K u x).1 ∈ Ke) (hA : ∀ y, ‖reconLow n K u y‖ ≤ A) (ξ : R4) :
    jetP K⁻¹ (resc K (reconLow n K u)) ξ ∈ jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A (240 * A) := by
  have hK0 : 0 < K := by linarith
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  refine ⟨⟨inv_nonneg.mpr hK0.le, inv_le_one_of_one_le₀ hK⟩, ⟨hKe _, ?_⟩, ?_⟩
  · rw [mem_closedBall, dist_zero_right]; exact hA _
  · rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]
    intro μ
    have h1 := resc_reconLow_bound u hK hA 1 ξ
    have h2 := (iteratedFDeriv ℝ 1 (resc K (reconLow n K u)) ξ).le_opNorm (fun _ => evec μ)
    rw [iteratedFDeriv_one_apply] at h2
    simp only [norm_evec, Finset.prod_const_one, mul_one] at h2
    refine le_trans h2 ?_
    have : (240 : ℝ) ^ 1 * A = 240 * A := by ring
    linarith

theorem jetQ_resc_low_mem (hK : 1 ≤ K) {Ke : Set Mat} {A : ℝ}
    (hKe : ∀ x, (reconLow n K u x).1 ∈ Ke) (hA : ∀ y, ‖reconLow n K u y‖ ≤ A) (ξ : R4) :
    jetQ K⁻¹ (resc K (reconLow n K u)) ξ ∈ valSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A := by
  have hK0 : 0 < K := by linarith
  refine ⟨⟨inv_nonneg.mpr hK0.le, inv_le_one_of_one_le₀ hK⟩, hKe _, ?_⟩
  rw [mem_closedBall, dist_zero_right]; exact hA _

theorem dist_jetP_resc_le (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m) (ξ : R4) :
    dist (jetP K⁻¹ (resc K (recon n u)) ξ) (jetP K⁻¹ (resc K (reconLow n K u)) ξ) ≤
      5 * tau n K m u := by
  have hd₁ : Differentiable ℝ (resc K (recon n u)) :=
    ((contDiff_recon u).comp (contDiff_const_smul K⁻¹)).differentiable (by simp)
  have hd₀ : Differentiable ℝ (resc K (reconLow n K u)) :=
    ((contDiff_reconLow u K).comp (contDiff_const_smul K⁻¹)).differentiable (by simp)
  rw [dist_eq_norm]
  have e : jetP K⁻¹ (resc K (recon n u)) ξ - jetP K⁻¹ (resc K (reconLow n K u)) ξ =
      ((0 : ℝ), jet1 (resc K (recon n u) - resc K (reconLow n K u)) ξ) := by
    simp only [jetP, Prod.mk_sub_mk, sub_self, ContEulerBounds.jet1_sub hd₁ hd₀ ξ]
  rw [e, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
  have := jet1_resc_tail_bound u hK (p := 0) (m := m) (by omega) ξ
  rwa [norm_iteratedFDeriv_zero] at this

theorem dist_jetQ_resc_le (hK : 1 ≤ K) (m : ℕ) (ξ : R4) :
    dist (jetQ K⁻¹ (resc K (recon n u)) ξ) (jetQ K⁻¹ (resc K (reconLow n K u)) ξ) ≤
      tau n K m u := by
  rw [dist_eq_norm]
  have e : jetQ K⁻¹ (resc K (recon n u)) ξ - jetQ K⁻¹ (resc K (reconLow n K u)) ξ =
      ((0 : ℝ), (resc K (recon n u) - resc K (reconLow n K u)) ξ) := by
    simp [jetQ]
  rw [e, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
  have := resc_tail_bound u hK (p := 0) (m := m) (Nat.zero_le m) ξ
  rwa [norm_iteratedFDeriv_zero] at this

end JetBounds


/-! ### The source-tail transfer -/

-- the final assembly elaborates many large derivative terms
set_option maxHeartbeats 4000000 in
/-- **`eq:native-source-tail` and the zero-order source difference** (`lem:native-tail-transfer`).
For a compact coframe chart `K_e ⊂ {det e > 0}`, an amplitude bound `A` and `k`, there are
constants `C ≥ 0` and `τ_* > 0` (depending on the chart, `A`, `k` and the coefficient bank only)
such that for every grid size `n`, every record `u_h`, every `K ≥ 1` with `τ_{h,k+2}(K) ≤ τ_*`
and a low-frequency head `z^lo = 𝓘_h^trig P_{≤K} u_h` with coframe values in `K_e` and `|z^lo| ≤ A`,
on every slab `Q` of the periodic box, with `z = 𝓘_h^trig u_h`,
`‖𝓡_B(z) - 𝓡_B(z^lo)‖_{L²_tH^k_x(Q)} + ‖𝓡_D(z) - 𝓡_D(z^lo)‖_{L²_tH^{k+1}_x(Q)} ≤ C K^{k+2} τ_{h,k+2}`
and `‖𝓡_B(z) - 𝓡_B(z^lo)‖_{L²(Q)} + ‖𝓡_D(z) - 𝓡_D(z^lo)‖_{L²(Q)} ≤ C K² τ_{h,2}`. -/
theorem native_source_tail {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A : ℝ) (k : ℕ) :
    ∃ C τs : ℝ, 0 ≤ C ∧ 0 < τs ∧ ∀ (n : ℕ) [NeZero n] (u : (Fin 4 → ZMod n) → Field 𝔄 𝓗 𝓢)
      (K : ℝ), 1 ≤ K → tau n K (k + 2) u ≤ τs →
      (∀ x, (reconLow n K u x).1 ∈ Ke) → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      ∀ Q ⊆ box,
        sobX k Q (fun x => RB D (recon n u) x - RB D (reconLow n K u) x) +
            sobX (k + 1) Q (fun x => RD D (recon n u) x - RD D (reconLow n K u) x) ≤
          C * K ^ (k + 2) * tau n K (k + 2) u ∧
        sobX 0 Q (fun x => RB D (recon n u) x - RB D (reconLow n K u) x) +
            sobX 0 Q (fun x => RD D (recon n u) x - RD D (reconLow n K u) x) ≤
          C * K ^ 2 * tau n K 2 u := by
  set A' := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  obtain ⟨δ, hδ, M, hM0, hsU, hsW, hbU, hbW⟩ :=
    exists_native_constants D hKe hdet A' (240 * A') (k + 3)
  set B : ℝ := 5 * 240 ^ (k + 3) * (A' + 1) with hBdef
  have hB1 : 1 ≤ B := by
    have : (1 : ℝ) ≤ 240 ^ (k + 3) := one_le_pow₀ (by norm_num)
    rw [hBdef]; nlinarith
  set X : ℝ := ∑ j ∈ Finset.range (k + 2),
    ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * 5 with hXdef
  have hterm0 : ∀ j, 0 ≤ ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * 5 := fun j => by
    have := ContEulerBounds.cE_nonneg j; have : 0 ≤ B := by linarith
    positivity
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun j _ => hterm0 j
  have hXj : ∀ j ≤ k + 1, ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * 5 ≤ X :=
    fun j hj => Finset.single_le_sum (f := fun j => ContEulerBounds.cE j * ((j + 2) * M *
      B ^ (j + 1)) * 5) (fun j _ => hterm0 j) (Finset.mem_range.mpr (by omega))
  set S : ℝ := Real.sqrt ((k + 2) * (2 * Real.pi) ^ 4)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  refine ⟨2 * S * X, min 1 (δ / 10), by positivity, lt_min one_pos (by positivity), ?_⟩
  intro n _ u K hK hτ hKe' hA Q hQ
  have hK0 : 0 < K := by linarith
  have hA'' : ∀ y, ‖reconLow n K u y‖ ≤ A' := fun y => (hA y).trans (le_max_left _ _)
  set m := k + 2 with hm
  have hτ1 : tau n K m u ≤ 1 := hτ.trans (min_le_left _ _)
  have hτδ : tau n K m u ≤ δ / 10 := hτ.trans (min_le_right _ _)
  have hτ0 : 0 ≤ tau n K m u := TrigInterp.tau_nonneg n hK0 m u
  have hτ2m : tau n K 2 u ≤ tau n K m u := TrigInterp.tau_mono n hK0 (by omega) u
  have hτ20 : 0 ≤ tau n K 2 u := TrigInterp.tau_nonneg n hK0 2 u
  set zl := reconLow n K u
  set z := recon n u
  have hzl : ContDiff ℝ ∞ zl := contDiff_reconLow u K
  have hz : ContDiff ℝ ∞ z := contDiff_recon u
  -- jets and charts
  have hJ0 : ∀ ξ, jetP K⁻¹ (resc K zl) ξ ∈
      jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A' (240 * A') :=
    jetP_resc_low_mem u hK hKe' hA''
  have hQ0 : ∀ ξ, jetQ K⁻¹ (resc K zl) ξ ∈ valSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A' :=
    jetQ_resc_low_mem u hK hKe' hA''
  have hball1 : ∀ ξ, jetP K⁻¹ (resc K z) ξ ∈ ball (jetP K⁻¹ (resc K zl) ξ) δ := fun ξ => by
    rw [mem_ball]
    have := dist_jetP_resc_le u hK (m := m) (by omega) ξ
    linarith
  have hball0 : ∀ ξ, jetQ K⁻¹ (resc K z) ξ ∈ ball (jetQ K⁻¹ (resc K zl) ξ) δ := fun ξ => by
    rw [mem_ball]
    have := dist_jetQ_resc_le u hK m ξ
    linarith
  have hballU : ∀ ξ, ball (jetP K⁻¹ (resc K zl) ξ) δ ⊆
      cthickening δ (jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A' (240 * A')) := fun ξ =>
    (ball_subset_thickening (hJ0 ξ) δ).trans (thickening_subset_cthickening _ _)
  have hballW : ∀ ξ, ball (jetQ K⁻¹ (resc K zl) ξ) δ ⊆
      cthickening δ (valSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A') := fun ξ =>
    (ball_subset_thickening (hQ0 ξ) δ).trans (thickening_subset_cthickening _ _)
  have hch0 : ∀ ξ, ((K⁻¹, jet1 (resc K zl) ξ) : ℝ × FJ) ∈ chartU := fun ξ =>
    hsU ((hballU ξ) (mem_ball_self hδ))
  have hch1 : ∀ ξ, ((K⁻¹, jet1 (resc K z) ξ) : ℝ × FJ) ∈ chartU := fun ξ =>
    hsU ((hballU ξ) (hball1 ξ))
  -- the uniform derivative bounds of the normalised fields
  have hBJ : ∀ p, p ≤ k + 1 → ‖iteratedFDeriv ℝ p (jet1 (resc K zl)) 0‖ ≤ B →
      True := fun _ _ _ => trivial
  have h240 : (1 : ℝ) ≤ 240 ^ (k + 3) := one_le_pow₀ (by norm_num)
  have hJlo : ∀ p ≤ k + 2, ∀ ξ, ‖iteratedFDeriv ℝ p (jet1 (resc K zl)) ξ‖ ≤ B := by
    intro p hp ξ
    refine (jet1_resc_low_bound u hK hA'' p ξ).trans ?_
    have : (240 : ℝ) ^ (p + 1) ≤ 240 ^ (k + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 := mul_le_mul_of_nonneg_right this hA'0
    rw [hBdef]; nlinarith
  have hJfu : ∀ p ≤ k + 1, ∀ ξ, ‖iteratedFDeriv ℝ p (jet1 (resc K z)) ξ‖ ≤ B := by
    intro p hp ξ
    refine (jet1_resc_full_bound u hK hA'' (m := m) (by omega) ξ).trans ?_
    have : (240 : ℝ) ^ (p + 1) ≤ 240 ^ (k + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 := mul_le_mul_of_nonneg_right this hA'0
    rw [hBdef]; nlinarith
  have hYlo : ∀ p ≤ k + 3, ∀ ξ, ‖iteratedFDeriv ℝ p (resc K zl) ξ‖ ≤ B := by
    intro p hp ξ
    refine (resc_reconLow_bound u hK hA'' p ξ).trans ?_
    have : (240 : ℝ) ^ p ≤ 240 ^ (k + 3) := pow_le_pow_right₀ (by norm_num) hp
    have h1 := mul_le_mul_of_nonneg_right this hA'0
    rw [hBdef]; nlinarith
  have hYfu : ∀ p ≤ k + 2, ∀ ξ, ‖iteratedFDeriv ℝ p (resc K z) ξ‖ ≤ B := by
    intro p hp ξ
    refine (resc_recon_bound u hK hA'' (m := m) hp ξ).trans ?_
    have : (240 : ℝ) ^ p ≤ 240 ^ (k + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 := mul_le_mul_of_nonneg_right this hA'0
    rw [hBdef]; nlinarith
  -- pointwise bounds (high orders)
  have hRB : ∀ x, ∀ j ≤ k, ‖iteratedFDeriv ℝ j
      (fun x => RB D z x - RB D zl x) x‖ ≤ K ^ (k + 2) * X * tau n K m u := by
    intro x j hj
    have hsub : iteratedFDeriv ℝ j (fun x => RB D z x - RB D zl x) x =
        iteratedFDeriv ℝ j (RB D z) x - iteratedFDeriv ℝ j (RB D zl) x :=
      iteratedFDeriv_sub_apply (f := RB D z) (g := RB D zl)
        ((contDiff_RB D hK0 hz hch1).of_le (ContEulerBounds.natCast_le_infty j)).contDiffAt
        ((contDiff_RB D hK0 hzl hch0).of_le (ContEulerBounds.natCast_le_infty j)).contDiffAt
    rw [hsub]
    have h := norm_iteratedFDeriv_RB_sub_le D hK hzl hz hch0 hch1 (j := j)
      (C := ball (jetP K⁻¹ (resc K zl) (K • x)) δ) ((hballU _).trans hsU) (convex_ball _ _)
      (M := M) (fun y hy k' hk' => (hbU y (hballU _ hy) k' (by omega)).1) (x := x)
      (mem_ball_self hδ) (hball1 _) (B := B) (η := 5 * tau n K m u) hB1
      (fun p hp hpj => ⟨hJlo p (by omega) _, hJfu p (by omega) _⟩)
      (fun p hp => jet1_resc_tail_bound u hK (by omega) _)
    refine h.trans ?_
    have hKp : K ^ (j + 2) ≤ K ^ (k + 2) := pow_le_pow_right₀ hK (by omega)
    have hXj' := hXj j (by omega)
    calc K ^ (j + 2) * (ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * (5 * tau n K m u))
        = K ^ (j + 2) * (ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * 5) *
            tau n K m u := by ring
      _ ≤ K ^ (k + 2) * X * tau n K m u := by
          gcongr <;> first | exact hterm0 j | assumption
  have hRD : ∀ x, ∀ j ≤ k + 1, ‖iteratedFDeriv ℝ j
      (fun x => RD D z x - RD D zl x) x‖ ≤ K ^ (k + 2) * X * tau n K m u := by
    intro x j hj
    have hsub : iteratedFDeriv ℝ j (fun x => RD D z x - RD D zl x) x =
        iteratedFDeriv ℝ j (RD D z) x - iteratedFDeriv ℝ j (RD D zl) x :=
      iteratedFDeriv_sub_apply (f := RD D z) (g := RD D zl)
        ((contDiff_RD D hK0 hz hch1).of_le (ContEulerBounds.natCast_le_infty j)).contDiffAt
        ((contDiff_RD D hK0 hzl hch0).of_le (ContEulerBounds.natCast_le_infty j)).contDiffAt
    rw [hsub]
    have h := norm_iteratedFDeriv_RD_sub_le D hK hzl hz hch0 hch1 (j := j)
      (C₁ := ball (jetP K⁻¹ (resc K zl) (K • x)) δ)
      (C₀ := ball (jetQ K⁻¹ (resc K zl) (K • x)) δ) ((hballU _).trans hsU) (convex_ball _ _)
      ((hballW _).trans hsW) (convex_ball _ _) (M := M)
      (fun y hy k' hk' => (hbU y (hballU _ hy) k' (by omega)).2)
      (fun μ y hy k' hk' => hbW y (hballW _ hy) μ k' (by omega)) (x := x)
      (mem_ball_self hδ) (hball1 _) (mem_ball_self hδ) (hball0 _) (B := B)
      (η := 5 * tau n K m u) hB1
      (fun p hp hpj => ⟨hJlo p (by omega) _, hJfu p (by omega) _⟩)
      (fun p hp hpj => ⟨hYlo p (by omega) _, hYfu p (by omega) _⟩)
      (fun p hp => jet1_resc_tail_bound u hK (by omega) _)
      (fun p hp => (resc_tail_bound u hK (m := m) (by omega) _).trans (by linarith))
    refine h.trans ?_
    have hKp : K ^ (j + 1) ≤ K ^ (k + 2) := pow_le_pow_right₀ hK (by omega)
    have hXj' := hXj j hj
    calc K ^ (j + 1) * (ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * (5 * tau n K m u))
        = K ^ (j + 1) * (ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * 5) *
            tau n K m u := by ring
      _ ≤ K ^ (k + 2) * X * tau n K m u := by
          gcongr <;> first | exact hterm0 j | assumption
  -- pointwise bounds (zero order, with `τ_{h,2}`)
  have hRB0 : ∀ x, ‖iteratedFDeriv ℝ 0
      (fun x => RB D z x - RB D zl x) x‖ ≤ K ^ 2 * X * tau n K 2 u := by
    intro x
    have hsub : iteratedFDeriv ℝ 0 (fun x => RB D z x - RB D zl x) x =
        iteratedFDeriv ℝ 0 (RB D z) x - iteratedFDeriv ℝ 0 (RB D zl) x :=
      iteratedFDeriv_sub_apply (f := RB D z) (g := RB D zl)
        ((contDiff_RB D hK0 hz hch1).of_le (ContEulerBounds.natCast_le_infty 0)).contDiffAt
        ((contDiff_RB D hK0 hzl hch0).of_le (ContEulerBounds.natCast_le_infty 0)).contDiffAt
    rw [hsub]
    have h := norm_iteratedFDeriv_RB_sub_le D hK hzl hz hch0 hch1 (j := 0)
      (C := ball (jetP K⁻¹ (resc K zl) (K • x)) δ) ((hballU _).trans hsU) (convex_ball _ _)
      (M := M) (fun y hy k' hk' => (hbU y (hballU _ hy) k' (by omega)).1) (x := x)
      (mem_ball_self hδ) (hball1 _) (B := B) (η := 5 * tau n K 2 u) hB1
      (fun p hp hpj => ⟨hJlo p (by omega) _, hJfu p (by omega) _⟩)
      (fun p hp => jet1_resc_tail_bound u hK (m := 2) (by omega) _)
    refine h.trans ?_
    have hXj' := hXj 0 (by omega)
    calc K ^ (0 + 2) * (ContEulerBounds.cE 0 * ((((0 : ℕ) : ℝ) + 2) * M * B ^ (0 + 1)) *
          (5 * tau n K 2 u))
        = K ^ 2 * (ContEulerBounds.cE 0 * ((((0 : ℕ) : ℝ) + 2) * M * B ^ (0 + 1)) * 5) *
            tau n K 2 u := by ring
      _ ≤ K ^ 2 * X * tau n K 2 u := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hτ20
          simpa using hXj'
  have hRD0 : ∀ x, ‖iteratedFDeriv ℝ 0
      (fun x => RD D z x - RD D zl x) x‖ ≤ K ^ 2 * X * tau n K 2 u := by
    intro x
    have hsub : iteratedFDeriv ℝ 0 (fun x => RD D z x - RD D zl x) x =
        iteratedFDeriv ℝ 0 (RD D z) x - iteratedFDeriv ℝ 0 (RD D zl) x :=
      iteratedFDeriv_sub_apply (f := RD D z) (g := RD D zl)
        ((contDiff_RD D hK0 hz hch1).of_le (ContEulerBounds.natCast_le_infty 0)).contDiffAt
        ((contDiff_RD D hK0 hzl hch0).of_le (ContEulerBounds.natCast_le_infty 0)).contDiffAt
    rw [hsub]
    have h := norm_iteratedFDeriv_RD_sub_le D hK hzl hz hch0 hch1 (j := 0)
      (C₁ := ball (jetP K⁻¹ (resc K zl) (K • x)) δ)
      (C₀ := ball (jetQ K⁻¹ (resc K zl) (K • x)) δ) ((hballU _).trans hsU) (convex_ball _ _)
      ((hballW _).trans hsW) (convex_ball _ _) (M := M)
      (fun y hy k' hk' => (hbU y (hballU _ hy) k' (by omega)).2)
      (fun μ y hy k' hk' => hbW y (hballW _ hy) μ k' (by omega)) (x := x)
      (mem_ball_self hδ) (hball1 _) (mem_ball_self hδ) (hball0 _) (B := B)
      (η := 5 * tau n K 2 u) hB1
      (fun p hp hpj => ⟨hJlo p (by omega) _, hJfu p (by omega) _⟩)
      (fun p hp hpj => ⟨hYlo p (by omega) _, hYfu p (by omega) _⟩)
      (fun p hp => jet1_resc_tail_bound u hK (m := 2) (by omega) _)
      (fun p hp => (resc_tail_bound u hK (m := 2) (by omega) _).trans (by linarith))
    refine h.trans ?_
    have hXj' := hXj 0 (by omega)
    have hK1 : K ^ (0 + 1) ≤ K ^ 2 := pow_le_pow_right₀ hK (by omega)
    calc K ^ (0 + 1) * (ContEulerBounds.cE 0 * ((((0 : ℕ) : ℝ) + 2) * M * B ^ (0 + 1)) *
          (5 * tau n K 2 u))
        = K ^ (0 + 1) * (ContEulerBounds.cE 0 * ((((0 : ℕ) : ℝ) + 2) * M * B ^ (0 + 1)) * 5) *
            tau n K 2 u := by ring
      _ ≤ K ^ 2 * X * tau n K 2 u := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hK1 ?_ (hterm0 0) (by positivity)) hτ20
          simpa using hXj'
  -- the Sobolev norms
  have hSk : Real.sqrt ((k + 1) * (2 * Real.pi) ^ 4) ≤ S :=
    Real.sqrt_le_sqrt (by gcongr; linarith)
  have hSk1 : Real.sqrt (((k + 1 : ℕ) : ℝ) + 1) * 1 ≤ S ∨ True := Or.inr trivial
  have hSk1' : Real.sqrt ((((k + 1 : ℕ) : ℝ) + 1) * (2 * Real.pi) ^ 4) ≤ S :=
    Real.sqrt_le_sqrt (by push_cast; nlinarith [Real.pi_pos])
  have hpi4 : 0 < (2 * Real.pi) ^ 4 := by positivity
  have hS0' : Real.sqrt ((((0 : ℕ) : ℝ) + 1) * (2 * Real.pi) ^ 4) ≤ S :=
    Real.sqrt_le_sqrt (by push_cast; nlinarith)
  have hb : 0 ≤ K ^ (k + 2) * X * tau n K m u := by positivity
  have hb0 : 0 ≤ K ^ 2 * X * tau n K 2 u := by positivity
  have h1 := sobX_le (k := k) hQ hb fun x _ j hj => hRB x j hj
  have h2 := sobX_le (k := k + 1) hQ hb fun x _ j hj => hRD x j hj
  have h3 := sobX_le (k := 0) hQ hb0 fun x _ j hj => by
    rw [Nat.le_zero.mp hj]; exact hRB0 x
  have h4 := sobX_le (k := 0) hQ hb0 fun x _ j hj => by
    rw [Nat.le_zero.mp hj]; exact hRD0 x
  refine ⟨?_, ?_⟩
  · calc _ ≤ Real.sqrt ((k + 1) * (2 * Real.pi) ^ 4) * (K ^ (k + 2) * X * tau n K m u) +
          Real.sqrt ((((k + 1 : ℕ) : ℝ) + 1) * (2 * Real.pi) ^ 4) * (K ^ (k + 2) * X * tau n K m u) :=
          add_le_add h1 h2
      _ ≤ S * (K ^ (k + 2) * X * tau n K m u) + S * (K ^ (k + 2) * X * tau n K m u) := by
          gcongr
      _ = 2 * S * X * K ^ (k + 2) * tau n K (k + 2) u := by ring
  · calc _ ≤ Real.sqrt ((((0 : ℕ) : ℝ) + 1) * (2 * Real.pi) ^ 4) * (K ^ 2 * X * tau n K 2 u) +
          Real.sqrt ((((0 : ℕ) : ℝ) + 1) * (2 * Real.pi) ^ 4) * (K ^ 2 * X * tau n K 2 u) :=
          add_le_add h3 h4
      _ ≤ S * (K ^ 2 * X * tau n K 2 u) + S * (K ^ 2 * X * tau n K 2 u) := by gcongr
      _ = 2 * S * X * K ^ 2 * tau n K 2 u := by ring

end

end RenewalGeometry.NativeTail
