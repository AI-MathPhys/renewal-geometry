/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSourceTheorem
import RenewalGeometry.Action.NativeSelectedClosure

/-!
# `thm:native-source` with selected upper budgets (`thm:native-selected-closure`, source step)

Einstein–Standard-Model action-closure manuscript, proof of `thm:native-selected-closure`:
"Selection gives `σ_h ≤ s_h` … The reader certificate then gives `τ_{h,j} ≤ T_{h,j}`.  Apply
`thm:native-source` … with these upper budgets."  Its zero-order clause: "Its zero-order physical
residual is at most `C(s_h + hK_h³)` and its literal Cartan discrepancy is at most `ChK_h³`."

`selected_native_source` instantiates the proved `NativeSourceThm.native_source`
(`thm:native-source`,
odd periodic grid, `h = 2π/n`, `Σ = 𝕋³`) with the selected row bound `σ = s_h` and the upper tail
budgets `τ_{h,2} ≤ T_{h,2}`, `τ_{h,k+2} ≤ T_{h,k+2} ≤ τ_*`, and converts the forcing budget with the
actual tails into the composed budget `F̄_{h,k}` of `eq:selected-composed-budget` through
`SelectedClosure.forcingBudget_le_of_le` (uniform factor `e (k+1)!`).  Together with
`SelectedClosure.reader_tail_le` (`eq:selected-reader-general`) this discharges the hypothesis
`hsrc`
of `SelectedClosure.native_selected_closure` for the concrete trigonometric records.
-/

open MeasureTheory Filter Topology Set Finset
open scoped Real ENNReal Nat ContDiff

namespace RenewalGeometry.SelectedNativeSource

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency NativeTail
open TrigInterp (recon reconLow tau)
open NativeRate (eps0 forcingBudget)
open NativeSourceThm

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

local notation "FF" => Field 𝔄 𝓗 𝓢

open Classical in
/-- **`thm:native-source` with the selected upper budgets** (source step of
`thm:native-selected-closure`).  With the constants `C`, `c_res`, `τ_*` of `thm:native-source`: for
every odd grid, every record `u_h` in the calibrated chart, `1 ≤ K`, `hK ≤ c_res`, every selected
row bound `s_h ≥ 0` of the finite-action covector norm and upper tail budgets
`τ_{h,2}(K; u_h) ≤ T₂`, `τ_{h,k+2}(K; u_h) ≤ T_m ≤ τ_*`:
the zero-order residual is `≤ C(s_h + hK³)`, the strong source is
`≤ C e(k+1)! F̄_{h,k}` with `F̄_{h,k} = F_{h,k}(s_h, T₂, T_m)` (`eq:selected-composed-budget`), and
the literal Cartan discrepancy is `≤ C h K³`. -/
theorem selected_native_source {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A : ℝ) (k : ℕ) (hk : 1 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ δ : ℝ} (hδ : 0 < δ)
    (h0 : δ < t₀) (h1 : t₁ + δ ≤ 2 * π) :
    ∃ C c_res τs : ℝ, 0 ≤ C ∧ 0 < c_res ∧ 0 < τs ∧ ∀ (n : ℕ) [NeZero n], Odd n →
      ∀ (u : Grid n → FF) (K sh T₂ Tm : ℝ), 1 ≤ K → (2 * π / n) * K ≤ c_res →
      Tm ≤ τs → tau n K 2 u ≤ T₂ → tau n K (k + 2) u ≤ Tm →
      (∀ x, (reconLow n K u x).1 ∈ Ke) → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      (∀ x, (recon n u x).1 ∈ Ke) → (∀ x, ‖recon n u x‖ ≤ A) → 0 ≤ sh →
      (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
          (fun x : Grid n => pos (2 * π / n) x ∈ NativeZeroSource.bufSlab (t₀ - δ) (t₁ + δ)),
          ‖eulerRow (localAction D (2 * π / n)) (2 * π / n) u x‖ ^ 2 ≤ sh ^ 2 →
      (sobX 0 (NativeSlab.slab t₀ t₁) (RB D (recon n u)) +
          sobX 0 (NativeSlab.slab t₀ t₁) (RD D (recon n u)) ≤ C * eps0 sh (2 * π / n) K) ∧
      (sobX k (NativeSlab.slab t₀ t₁) (RB D (recon n u)) +
          sobX (k + 1) (NativeSlab.slab t₀ t₁) (RD D (recon n u)) ≤
        C * (Real.exp 1 * (k + 1)! * forcingBudget k Ck sh (2 * π / n) K T₂ Tm)) ∧
      (∀ (x : Grid n) (z : R4), ‖z - pos (2 * π / n) x‖ ≤ 2 * π / n → ∀ μ ν : Fin 4,
        ‖cartanCurvature (2 * π / n) (coframe u) x μ ν -
          matToOp ((recon n u z).1 * riemMat (fun z => (recon n u z).1) z μ ν *
            ((recon n u z).1)⁻¹)‖ ≤ C * (2 * π / n) * K ^ 3) := by
  obtain ⟨C, c_res, τs, hC, hc, hτs, hmain⟩ := native_source D hKe hdet A k hk hCk hδ h0 h1
  refine ⟨C, c_res, τs, hC, hc, hτs, ?_⟩
  intro n _ hn u K sh T₂ Tm hK hhK hTm hτ₂ hτm hKel hAl hKef hAf hsh hσ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh : 0 < 2 * π / n := div_pos Real.two_pi_pos hn0
  have hK0 : 0 < K := by linarith
  obtain ⟨hz, hs, hcart⟩ := hmain n hn u K sh hK hhK (hτm.trans hTm) hKel hAl hKef hAf hsh hσ
  refine ⟨hz, hs.trans (mul_le_mul_of_nonneg_left ?_ hC), hcart⟩
  exact SelectedClosure.forcingBudget_le_of_le k hCk.le hsh hh hK0
    (TrigInterp.tau_nonneg n hK0 _ u) hτ₂ (TrigInterp.tau_nonneg n hK0 _ u) hτm

end

end RenewalGeometry.SelectedNativeSource
