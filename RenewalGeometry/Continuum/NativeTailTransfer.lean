/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeTailStructure
import RenewalGeometry.Analysis.PeriodicTrigInterpolation

/-!
# Finite-order tail transfer for the physical source (`lem:native-tail-transfer`)

Einstein–Standard-Model action-closure manuscript, `lem:native-tail-transfer`
(`eq:native-tail-derivatives`, `eq:native-Euler-tail`, `eq:native-source-tail` and the
zero-order source difference), for the complete record `u_h` on the periodic grid `(ℤ/n)⁴`
(`n` odd, `h = 2π/n`, period `2π`), its trigonometric reconstruction `z_h = 𝓘_h^trig u_h`
(`TrigInterp.recon`) and the low-frequency comparison head `z_h^lo = 𝓘_h^trig P_{≤K} u_h`
(`TrigInterp.reconLow`).

The physical residual maps are the continuum Euler rows of the Einstein–Standard-Model
Lagrangian `L₀ = limDensity (firstJetDensity D)` of the unchanged local action
(`NativeEulerConsistency`): `𝓡(y)(x) = 𝓔₀(y)(x) ∈ (e, A, H, Ψ, Ψ̄)^*` (`Rfull`), its bosonic
rows `𝓡_B = 𝓔₀ ∘ ι_B` (Einstein, Yang–Mills, Higgs) and its Dirac rows `𝓡_D = 𝓔₀ ∘ ι_S`
(Dirac, dual Dirac) (`RB`, `RD`).

The spatial Sobolev norm on a slab `Q` of the periodic box is
`‖f‖²_{L²_t H^k_x(Q)} = ∫_Q Σ_{j ≤ k} ‖D^j_x f‖²` with `D^j_x f` the `j`-th derivative in the three
spatial directions (operator norm) (`sobX`).

## Main results

* `norm_iteratedFDeriv_RB_sub_le`, `norm_iteratedFDeriv_RD_sub_le`: pointwise derivative bounds
  for the differences of the residual maps of two fields under the native scaling
  (`lem:native-scaling`): `‖D^j(𝓡_B(z) - 𝓡_B(z^lo))‖ ≤ C K^{j+2} η`, `‖D^j(𝓡_D(z) - 𝓡_D(z^lo))‖ ≤
  C K^{j+1} η`, with `η` the normalised size of `z - z^lo` through order `j + 2` (bosonic) and
  `j + 1` (Dirac).
* **`native_source_tail`** (`eq:native-source-tail` and the zero-order source difference).
-/

open Finset Filter Topology Metric Set NormedSpace MeasureTheory
open scoped ContDiff

namespace RenewalGeometry.NativeTail

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency
open ContEulerBounds (JS jetP jetQ eulerOp contEuler_eq_eulerOp inlJ slotJ inrP)

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

/-! ### Uniform derivative bounds near a compact set -/

section Packet

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth map on an open set has uniformly bounded derivatives (of orders `≤ N`) on a closed
thickening of a compact subset. -/
theorem exists_deriv_bound_cthickening {f : X → F} {U Kc : Set X} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hKc : IsCompact Kc) (hKU : Kc ⊆ U) (N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 ≤ M ∧ cthickening δ Kc ⊆ U ∧
      ∀ y ∈ cthickening δ Kc, ∀ k ≤ N, ‖iteratedFDeriv ℝ k f y‖ ≤ M := by
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_cthickening_subset_open hU hKU
  have hcomp : IsCompact (cthickening δ Kc) := hKc.cthickening
  have hbd : ∀ k : ℕ, ∃ Mk : ℝ, ∀ y ∈ cthickening δ Kc, ‖iteratedFDeriv ℝ k f y‖ ≤ Mk := by
    intro k
    have hc : ContinuousOn (iteratedFDeriv ℝ k f) U := by
      have h1 := hf.continuousOn_iteratedFDerivWithin (m := k)
        (ContEulerBounds.natCast_le_infty k) hU.uniqueDiffOn
      exact h1.congr fun y hy => (iteratedFDerivWithin_of_isOpen k hU hy).symm
    exact hcomp.exists_bound_of_continuousOn (hc.mono hsub)
  choose Mk hMk using hbd
  refine ⟨δ, hδ, ∑ k ∈ Finset.range (N + 1), max (Mk k) 0, by positivity, hsub, fun y hy k hk => ?_⟩
  refine (hMk k y hy).trans ((le_max_left _ 0).trans ?_)
  exact Finset.single_le_sum (f := fun k => max (Mk k) 0) (fun _ _ => le_max_right _ _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

end Packet

/-! ### Rescaling of derivatives -/

theorem norm_iteratedFDeriv_comp_smul_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : R4 → F} (hf : ContDiff ℝ ∞ f) (c : ℝ) (j : ℕ) (x : R4) :
    ‖iteratedFDeriv ℝ j (fun y => f (c • y)) x‖ ≤ |c| ^ j * ‖iteratedFDeriv ℝ j f (c • x)‖ := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right (c • ContinuousLinearMap.id ℝ R4) hf x
    (i := j) (ContEulerBounds.natCast_le_infty j)
  rw [show (fun y => f (c • y)) = f ∘ ⇑(c • ContinuousLinearMap.id ℝ R4) from rfl, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn : ‖c • ContinuousLinearMap.id ℝ R4‖ ≤ |c| := by
    refine (ContinuousLinearMap.opNorm_smul_le c (ContinuousLinearMap.id ℝ R4)).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le
  have hprod : ∏ _i : Fin j, ‖c • ContinuousLinearMap.id ℝ R4‖ ≤ |c| ^ j := by
    calc ∏ _i : Fin j, ‖c • ContinuousLinearMap.id ℝ R4‖ ≤ ∏ _i : Fin j, |c| :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hn)
      _ = |c| ^ j := by simp
  have hx : (c • ContinuousLinearMap.id ℝ R4) x = c • x := rfl
  rw [hx, mul_comm]
  exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)


/-! ### Scaled differences -/

theorem norm_iteratedFDeriv_scale_sub_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) (c K : ℝ) {g₁ g₀ : R4 → F}
    (h₁ : ContDiff ℝ ∞ g₁) (h₀ : ContDiff ℝ ∞ g₀) (j : ℕ) (x : R4) :
    ‖iteratedFDeriv ℝ j (fun y => c • L (g₁ (K • y))) x -
        iteratedFDeriv ℝ j (fun y => c • L (g₀ (K • y))) x‖ ≤
      |c| * ‖L‖ * (|K| ^ j * ‖iteratedFDeriv ℝ j g₁ (K • x) - iteratedFDeriv ℝ j g₀ (K • x)‖) := by
  have hs₁ : ContDiff ℝ ∞ (fun y => c • L (g₁ (K • y))) :=
    contDiff_const.smul (L.contDiff.comp (h₁.comp (contDiff_const_smul K)))
  have hs₀ : ContDiff ℝ ∞ (fun y => c • L (g₀ (K • y))) :=
    contDiff_const.smul (L.contDiff.comp (h₀.comp (contDiff_const_smul K)))
  have hj := ContEulerBounds.natCast_le_infty j
  rw [← iteratedFDeriv_sub_apply (hs₁.of_le hj).contDiffAt (hs₀.of_le hj).contDiffAt]
  have hfun : ((fun y => c • L (g₁ (K • y))) - fun y => c • L (g₀ (K • y))) =
      fun y => c • L ((g₁ - g₀) (K • y)) := by
    funext y; simp [smul_sub]
  rw [hfun]
  have hW : ContDiff ℝ ∞ (g₁ - g₀) := h₁.sub h₀
  have e1 : iteratedFDeriv ℝ j (fun y => c • L ((g₁ - g₀) (K • y))) x =
      c • iteratedFDeriv ℝ j (fun y => L ((g₁ - g₀) (K • y))) x := by
    have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (f := fun y => L ((g₁ - g₀) (K • y)))
      (a := c) (x := x) (i := j)
      ((L.contDiff.comp (hW.comp (contDiff_const_smul K))).of_le hj).contDiffAt
    exact this
  rw [e1, norm_smul, Real.norm_eq_abs, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
  have e2 : (fun y => L ((g₁ - g₀) (K • y))) = ⇑L ∘ fun y => (g₁ - g₀) (K • y) := rfl
  rw [e2]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left L
    ((hW.comp (contDiff_const_smul K)).of_le hj).contDiffAt le_rfl).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_iteratedFDeriv_comp_smul_le hW K j x).trans ?_
  rw [iteratedFDeriv_sub_apply (h₁.of_le hj).contDiffAt (h₀.of_le hj).contDiffAt]

/-! ### The physical residual maps -/

/-- **The continuum Euler covector** `𝓔₀(y)(x)` of the Einstein–Standard-Model Lagrangian
`L₀ = limDensity (firstJetDensity D)` of the unchanged local action (all physical rows). -/
def Rfull (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) : ContEulerBounds.CovV (Field 𝔄 𝓗 𝓢) :=
  contEuler (limDensity (ι := Shift) (firstJetDensity D)) Y x

/-- **The bosonic residual map** `𝓡_B(y) = 𝓔₀(y) ∘ ι_B` (Einstein, Yang–Mills and Higgs rows). -/
def RB (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) : ContEulerBounds.NCLM (Mat × (Fin 4 → 𝔄) × 𝓗) ℝ :=
  (Rfull D Y x).comp ιB

/-- **The Dirac residual map** `𝓡_D(y) = 𝓔₀(y) ∘ ι_S` (Dirac and dual-Dirac rows). -/
def RD (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) : ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ :=
  (Rfull D Y x).comp ιS

/-- The amplitude-preserving rescaling `ỹ(ξ) = y(ξ/K)`. -/
def resc (K : ℝ) (Y : R4 → Field 𝔄 𝓗 𝓢) : R4 → Field 𝔄 𝓗 𝓢 := fun ξ => Y (K⁻¹ • ξ)

theorem resc_smul {K : ℝ} (hK : K ≠ 0) (Y : R4 → Field 𝔄 𝓗 𝓢) :
    (fun x => resc K Y (K • x)) = Y := by
  funext x; simp [resc, smul_smul, inv_mul_cancel₀ hK]

theorem Rfull_scale {K : ℝ} (hK : K ≠ 0) (Y : R4 → Field 𝔄 𝓗 𝓢)
    (hch : ∀ ξ, ((K⁻¹, jet1 (resc K Y) ξ) : ℝ × FJ) ∈ chartU) (x : R4) :
    Rfull D Y x = K ^ 2 • eulerOp (Gd D) K⁻¹ (resc K Y) (K • x) := by
  have h := contEuler_native_scale D hK (resc K Y) hch x
  rw [resc_smul hK] at h
  exact h

theorem norm_ιB_le : ‖(ιB : ContEulerBounds.NCLM (Mat × (Fin 4 → 𝔄) × 𝓗) (Field 𝔄 𝓗 𝓢))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact norm_ιB_apply_le x

theorem norm_ιS_le : ‖(ιS : ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) (Field 𝔄 𝓗 𝓢))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun s => by
    rw [one_mul]; exact norm_ιS_apply_le s

theorem RB_fun_scale {K : ℝ} (hK : K ≠ 0) (Y : R4 → Field 𝔄 𝓗 𝓢)
    (hch : ∀ ξ, ((K⁻¹, jet1 (resc K Y) ξ) : ℝ × FJ) ∈ chartU) :
    RB D Y = fun x => (K ^ 2) • ContEulerBounds.preL (ιB (𝓢 := 𝓢))
      (eulerOp (Gd D) K⁻¹ (resc K Y) (K • x)) := by
  funext x
  rw [RB, Rfull_scale D hK Y hch x, ContinuousLinearMap.smul_comp]
  rfl

/-- The first-order coefficient `G₁(q) = G_D(q)(ι_S ·, 0)` of the Dirac rows. -/
def G1D (q : ℝ × FJ) : ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ :=
  ContEulerBounds.preL ((inlJ (Field 𝔄 𝓗 𝓢)).comp ιS) (GD D q)

theorem contDiffOn_G1D : ContDiffOn ℝ ∞ (G1D D) chartU :=
  (ContEulerBounds.preL ((inlJ (Field 𝔄 𝓗 𝓢)).comp ιS)).contDiff.comp_contDiffOn (contDiffOn_GD D)

theorem dirOp_eq_foOp (ν : ℝ) (Y : R4 → Field 𝔄 𝓗 𝓢) :
    dirOp D ν Y = ContEulerBounds.foOp (G1D D) (fun μ => ellD D μ) ν Y := rfl

theorem RD_fun_scale {K : ℝ} (hK : 0 < K) (Y : R4 → Field 𝔄 𝓗 𝓢) (hY : ContDiff ℝ ∞ Y)
    (hch : ∀ ξ, ((K⁻¹, jet1 (resc K Y) ξ) : ℝ × FJ) ∈ chartU) :
    RD D Y = fun x => K • ContinuousLinearMap.id ℝ (ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ)
      (ContEulerBounds.foOp (G1D D) (fun μ => ellD D μ) K⁻¹ (resc K Y) (K • x)) := by
  have hYr : ContDiff ℝ ∞ (resc K Y) := hY.comp (contDiff_const_smul K⁻¹)
  funext x
  rw [RD, Rfull_scale D hK.ne' Y hch x, ContinuousLinearMap.smul_comp,
    eulerOp_comp_ιS D hYr hch, smul_smul, ← dirOp_eq_foOp]
  congr 1
  field_simp


/-! ### Pointwise derivative bounds for differences of the residual maps -/

theorem norm_preL_ιB_le :
    ‖ContEulerBounds.preL (ιB (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))‖ ≤ 1 :=
  ContEulerBounds.norm_preL_le _ norm_ιB_le

theorem norm_id_NCLM_le :
    ‖ContinuousLinearMap.id ℝ (ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.norm_id_le

/-- **Bosonic rows: derivative bound for the difference of two fields** under the native scaling:
`‖D^j(𝓡_B(y₁) - 𝓡_B(y₀))(x)‖ ≤ K^{j+2} c_j (j+2) M B^{j+1} η`, where the normalised jets of
`ỹ_i = y_i(·/K)` satisfy the bounds `B` and the normalised difference `η` (orders `≤ j + 1` of the
first jet, i.e. `≤ j + 2` of the field). -/
theorem norm_iteratedFDeriv_RB_sub_le {K : ℝ} (hK : 1 ≤ K) {Y₀ Y₁ : R4 → Field 𝔄 𝓗 𝓢}
    (hY₀ : ContDiff ℝ ∞ Y₀) (hY₁ : ContDiff ℝ ∞ Y₁)
    (hch₀ : ∀ ξ, ((K⁻¹, jet1 (resc K Y₀) ξ) : ℝ × FJ) ∈ chartU)
    (hch₁ : ∀ ξ, ((K⁻¹, jet1 (resc K Y₁) ξ) : ℝ × FJ) ∈ chartU) {j : ℕ} {C : Set (ℝ × FJ)}
    (hCU : C ⊆ chartU) (hC : Convex ℝ C) {M : ℝ}
    (hM : ∀ y ∈ C, ∀ k ≤ j + 1 + 1, ‖iteratedFDeriv ℝ k (Gd D) y‖ ≤ M) {x : R4}
    (hz₀ : jetP K⁻¹ (resc K Y₀) (K • x) ∈ C) (hz₁ : jetP K⁻¹ (resc K Y₁) (K • x) ∈ C) {B η : ℝ}
    (hB1 : 1 ≤ B) (hB : ∀ p, 1 ≤ p → p ≤ j + 1 →
      ‖iteratedFDeriv ℝ p (jet1 (resc K Y₀)) (K • x)‖ ≤ B ∧
        ‖iteratedFDeriv ℝ p (jet1 (resc K Y₁)) (K • x)‖ ≤ B)
    (hη : ∀ p ≤ j + 1, ‖iteratedFDeriv ℝ p (jet1 (resc K Y₁ - resc K Y₀)) (K • x)‖ ≤ η) :
    ‖iteratedFDeriv ℝ j (RB D Y₁) x - iteratedFDeriv ℝ j (RB D Y₀) x‖ ≤
      K ^ (j + 2) * (ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * η) := by
  have hK0 : 0 < K := by linarith
  have hr₀ : ContDiff ℝ ∞ (resc K Y₀) := hY₀.comp (contDiff_const_smul K⁻¹)
  have hr₁ : ContDiff ℝ ∞ (resc K Y₁) := hY₁.comp (contDiff_const_smul K⁻¹)
  have hE₀ : ContDiff ℝ ∞ (eulerOp (Gd D) K⁻¹ (resc K Y₀)) :=
    ContEulerBounds.contDiff_eulerOp (contDiffOn_Gd D) hr₀ hch₀
  have hE₁ : ContDiff ℝ ∞ (eulerOp (Gd D) K⁻¹ (resc K Y₁)) :=
    ContEulerBounds.contDiff_eulerOp (contDiffOn_Gd D) hr₁ hch₁
  rw [RB_fun_scale D hK0.ne' Y₁ hch₁, RB_fun_scale D hK0.ne' Y₀ hch₀]
  refine (norm_iteratedFDeriv_scale_sub_le _ (K ^ 2) K hE₁ hE₀ j x).trans ?_
  have hbound := ContEulerBounds.norm_iteratedFDeriv_eulerOp_sub_le (n := j) isOpen_chartU
    ((contDiffOn_Gd D).of_le (ContEulerBounds.natCast_le_infty (j + 1 + 1))) hCU hC hM
    (hr₀.of_le (ContEulerBounds.natCast_le_infty (j + 1 + 1)))
    (hr₁.of_le (ContEulerBounds.natCast_le_infty (j + 1 + 1))) hch₀ hch₁ hz₀ hz₁ hB1 hB hη
  have hX0 : 0 ≤ ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * η := by
    have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη 0 (Nat.zero_le _))
    have hM0 : 0 ≤ M := by
      have h := hM _ hz₀ 0 (Nat.zero_le _)
      have : 0 ≤ ‖iteratedFDeriv ℝ 0 (Gd D) (jetP K⁻¹ (resc K Y₀) (K • x))‖ := by positivity
      linarith
    have := ContEulerBounds.cE_nonneg j
    have : 0 ≤ B := by linarith
    positivity
  rw [abs_of_pos (by positivity : (0 : ℝ) < K ^ 2), abs_of_pos hK0]
  calc K ^ 2 * ‖ContEulerBounds.preL (ιB (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))‖ *
        (K ^ j * ‖iteratedFDeriv ℝ j (eulerOp (Gd D) K⁻¹ (resc K Y₁)) (K • x) -
          iteratedFDeriv ℝ j (eulerOp (Gd D) K⁻¹ (resc K Y₀)) (K • x)‖)
      ≤ K ^ 2 * 1 * (K ^ j * (ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * η)) := by
        gcongr
        exact norm_preL_ιB_le
    _ = K ^ (j + 2) * (ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * η) := by ring

/-- **Dirac rows: derivative bound for the difference of two fields** under the native scaling:
`‖D^j(𝓡_D(y₁) - 𝓡_D(y₀))(x)‖ ≤ K^{j+1} c_j (j+2) M B^{j+1} η` — one factor `K` less and one
field derivative less than the bosonic rows (`lem:native-scaling`, first-order Dirac rows). -/
theorem norm_iteratedFDeriv_RD_sub_le {K : ℝ} (hK : 1 ≤ K) {Y₀ Y₁ : R4 → Field 𝔄 𝓗 𝓢}
    (hY₀ : ContDiff ℝ ∞ Y₀) (hY₁ : ContDiff ℝ ∞ Y₁)
    (hch₀ : ∀ ξ, ((K⁻¹, jet1 (resc K Y₀) ξ) : ℝ × FJ) ∈ chartU)
    (hch₁ : ∀ ξ, ((K⁻¹, jet1 (resc K Y₁) ξ) : ℝ × FJ) ∈ chartU) {j : ℕ}
    {C₁ : Set (ℝ × FJ)} {C₀ : Set (ℝ × Field 𝔄 𝓗 𝓢)}
    (hCU₁ : C₁ ⊆ chartU) (hC₁ : Convex ℝ C₁) (hCU₀ : C₀ ⊆ chartW) (hC₀ : Convex ℝ C₀) {M : ℝ}
    (hM₁ : ∀ y ∈ C₁, ∀ k ≤ j + 1, ‖iteratedFDeriv ℝ k (G1D D) y‖ ≤ M)
    (hM₀ : ∀ μ, ∀ y ∈ C₀, ∀ k ≤ j + 1 + 1, ‖iteratedFDeriv ℝ k (ellD D μ) y‖ ≤ M) {x : R4}
    (hz₀ : jetP K⁻¹ (resc K Y₀) (K • x) ∈ C₁) (hz₁ : jetP K⁻¹ (resc K Y₁) (K • x) ∈ C₁)
    (hw₀ : jetQ K⁻¹ (resc K Y₀) (K • x) ∈ C₀) (hw₁ : jetQ K⁻¹ (resc K Y₁) (K • x) ∈ C₀)
    {B η : ℝ} (hB1 : 1 ≤ B)
    (hBJ : ∀ p, 1 ≤ p → p ≤ j → ‖iteratedFDeriv ℝ p (jet1 (resc K Y₀)) (K • x)‖ ≤ B ∧
      ‖iteratedFDeriv ℝ p (jet1 (resc K Y₁)) (K • x)‖ ≤ B)
    (hBY : ∀ p, 1 ≤ p → p ≤ j + 1 → ‖iteratedFDeriv ℝ p (resc K Y₀) (K • x)‖ ≤ B ∧
      ‖iteratedFDeriv ℝ p (resc K Y₁) (K • x)‖ ≤ B)
    (hηJ : ∀ p ≤ j, ‖iteratedFDeriv ℝ p (jet1 (resc K Y₁ - resc K Y₀)) (K • x)‖ ≤ η)
    (hηY : ∀ p ≤ j + 1, ‖iteratedFDeriv ℝ p (resc K Y₁ - resc K Y₀) (K • x)‖ ≤ η) :
    ‖iteratedFDeriv ℝ j (RD D Y₁) x - iteratedFDeriv ℝ j (RD D Y₀) x‖ ≤
      K ^ (j + 1) * (ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * η) := by
  have hK0 : 0 < K := by linarith
  have hr₀ : ContDiff ℝ ∞ (resc K Y₀) := hY₀.comp (contDiff_const_smul K⁻¹)
  have hr₁ : ContDiff ℝ ∞ (resc K Y₁) := hY₁.comp (contDiff_const_smul K⁻¹)
  have hV₀ : ∀ ξ, jetQ K⁻¹ (resc K Y₀) ξ ∈ (chartW : Set (ℝ × Field 𝔄 𝓗 𝓢)) := fun ξ => hch₀ ξ
  have hV₁ : ∀ ξ, jetQ K⁻¹ (resc K Y₁) ξ ∈ (chartW : Set (ℝ × Field 𝔄 𝓗 𝓢)) := fun ξ => hch₁ ξ
  have hF₀ : ContDiff ℝ ∞ (ContEulerBounds.foOp (G1D D) (fun μ => ellD D μ) K⁻¹ (resc K Y₀)) :=
    ContEulerBounds.contDiff_foOp (contDiffOn_G1D D) (fun μ => contDiffOn_ellD D μ) hr₀ hch₀ hV₀
  have hF₁ : ContDiff ℝ ∞ (ContEulerBounds.foOp (G1D D) (fun μ => ellD D μ) K⁻¹ (resc K Y₁)) :=
    ContEulerBounds.contDiff_foOp (contDiffOn_G1D D) (fun μ => contDiffOn_ellD D μ) hr₁ hch₁ hV₁
  rw [RD_fun_scale D hK0 Y₁ hY₁ hch₁, RD_fun_scale D hK0 Y₀ hY₀ hch₀]
  refine (norm_iteratedFDeriv_scale_sub_le _ K K hF₁ hF₀ j x).trans ?_
  have hbound := ContEulerBounds.norm_iteratedFDeriv_foOp_sub_le (n := j) isOpen_chartU
    ((contDiffOn_G1D D).of_le (ContEulerBounds.natCast_le_infty (j + 1))) hCU₁ hC₁ isOpen_chartW
    (fun μ => (contDiffOn_ellD D μ).of_le (ContEulerBounds.natCast_le_infty (j + 1 + 1)))
    hCU₀ hC₀ hM₁ hM₀ (hr₀.of_le (ContEulerBounds.natCast_le_infty (j + 1)))
    (hr₁.of_le (ContEulerBounds.natCast_le_infty (j + 1))) hch₀ hch₁ hV₀ hV₁ hz₀ hz₁ hw₀ hw₁
    hB1 hBJ hBY hηJ hηY
  rw [abs_of_pos hK0]
  calc K * ‖ContinuousLinearMap.id ℝ (ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ)‖ *
        (K ^ j * ‖iteratedFDeriv ℝ j (ContEulerBounds.foOp (G1D D) (fun μ => ellD D μ) K⁻¹
          (resc K Y₁)) (K • x) - iteratedFDeriv ℝ j (ContEulerBounds.foOp (G1D D)
            (fun μ => ellD D μ) K⁻¹ (resc K Y₀)) (K • x)‖)
      ≤ K * 1 * (K ^ j * (ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * η)) := by
        gcongr
        exact norm_id_NCLM_le
    _ = K ^ (j + 1) * (ContEulerBounds.cE j * ((j + 2) * M * B ^ (j + 1)) * η) := by ring


/-! ### The spatial Sobolev norm on a slab of the periodic box -/

section Sobolev

/-- The spatial inclusion `ℝ³ → ℝ⁴`, `x ↦ (0, x)`. -/
def spatialL : (Fin 3 → ℝ) →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun μ : Fin 4 =>
    Fin.cases (motive := fun _ => (Fin 3 → ℝ) →L[ℝ] ℝ) 0
      (fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i) μ

theorem norm_spatialL_le : ‖spatialL‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro μ
  induction μ using Fin.cases with
  | zero => simp [spatialL]
  | succ i => simpa [spatialL] using norm_le_pi_norm v i

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The spatial derivative `D^j_x f(z)` (the `j`-th derivative in the three spatial directions). -/
def dX (j : ℕ) (f : R4 → W) (z : R4) : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin 3 → ℝ) W :=
  (iteratedFDeriv ℝ j f z).compContinuousLinearMap fun _ => spatialL

theorem norm_dX_le (j : ℕ) (f : R4 → W) (z : R4) :
    ‖dX j f z‖ ≤ ‖iteratedFDeriv ℝ j f z‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_spatialL_le)

/-- The squared space-time Sobolev norm `∫_Q Σ_{j ≤ k} ‖D^j_x f‖²` (`L²_t H^k_x(Q)`). -/
def sobXSq (k : ℕ) (Q : Set R4) (f : R4 → W) : ℝ :=
  ∫ z in Q, ∑ j ∈ Finset.range (k + 1), ‖dX j f z‖ ^ 2

/-- The space-time Sobolev norm `‖f‖_{L²_t H^k_x(Q)}`. -/
def sobX (k : ℕ) (Q : Set R4) (f : R4 → W) : ℝ := Real.sqrt (sobXSq k Q f)

/-- The periodic box `[0, 2π]⁴`. -/
def box : Set R4 := Set.Icc 0 fun _ => 2 * Real.pi

theorem volume_box_ne_top : volume box ≠ ⊤ := by
  unfold box; rw [Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

theorem measureReal_box : volume.real box = (2 * Real.pi) ^ 4 := by
  unfold box
  rw [Measure.real, Real.volume_Icc_pi_toReal (fun _ => by positivity)]
  simp

/-- **Sup-norm bound for the space-time Sobolev norm** on a slab of the box. -/
theorem sobX_le {k : ℕ} {Q : Set R4} (hQ : Q ⊆ box) {f : R4 → W} {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z ∈ Q, ∀ j ≤ k, ‖iteratedFDeriv ℝ j f z‖ ≤ b) :
    sobX k Q f ≤ Real.sqrt ((k + 1) * (2 * Real.pi) ^ 4) * b := by
  have hQfin : volume Q < ⊤ := (measure_mono hQ).trans_lt (lt_top_iff_ne_top.mpr volume_box_ne_top)
  have hpt : ∀ z ∈ Q, ‖∑ j ∈ Finset.range (k + 1), ‖dX j f z‖ ^ 2‖ ≤ (k + 1) * b ^ 2 := by
    intro z hz
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
    calc ∑ j ∈ Finset.range (k + 1), ‖dX j f z‖ ^ 2 ≤ ∑ _j ∈ Finset.range (k + 1), b ^ 2 :=
          Finset.sum_le_sum fun j hj => pow_le_pow_left₀ (norm_nonneg _)
            ((norm_dX_le j f z).trans (hb z hz j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))) 2
      _ = (k + 1) * b ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hint := norm_setIntegral_le_of_norm_le_const hQfin hpt
  have hreal : volume.real Q ≤ (2 * Real.pi) ^ 4 := by
    rw [← measureReal_box]; exact measureReal_mono hQ volume_box_ne_top
  have hsq : sobXSq k Q f ≤ (k + 1) * (2 * Real.pi) ^ 4 * b ^ 2 := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine hint.trans ?_
    calc (k + 1 : ℝ) * b ^ 2 * volume.real Q ≤ (k + 1) * b ^ 2 * (2 * Real.pi) ^ 4 := by gcongr
      _ = (k + 1) * (2 * Real.pi) ^ 4 * b ^ 2 := by ring
  unfold sobX
  calc Real.sqrt (sobXSq k Q f) ≤ Real.sqrt ((k + 1) * (2 * Real.pi) ^ 4 * b ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt ((k + 1) * (2 * Real.pi) ^ 4) * b := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb0]

end Sobolev

end

end RenewalGeometry.NativeTail
