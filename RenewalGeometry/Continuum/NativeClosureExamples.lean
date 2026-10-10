/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSelectedClosed

/-!
# Non-vacuity of the native-record hypotheses of `thm:native-closure`

Einstein–Standard-Model action-closure manuscript, `thm:native-closure`: the record hypotheses
`RecordTuple.RecordHyp` (chart and amplitude conditions of `thm:native-source`, finite-action row
bound, tuple hypotheses of the dilated reconstruction) are satisfiable for the concrete slab model
`SlabData.diracSlab` (the native Dirac model `NativeModelExample.diracModel`):

* **`isLorChart_smul_eta`** — `c η` is in the Lorentzian foliated chart for `c > 0`;
* **`exists_margin_flat`** — the dilated flat coframe `2π·1` has a chart margin `δ > 0`;
* **`higgs_record_tupleHyp`** — every *non-constant* Higgs record `u(y) = (1, 0, H(y), 0, 0)`
  (flat coframe, temporal gauge, arbitrary nodal Higgs values `H`) on an odd grid satisfies the
  tuple hypotheses, so its dilated reconstruction is an actual field tuple (`toTuple`);
* **`vacuum_recordHyp`** — the flat vacuum record satisfies all of `RecordHyp` (with the row bound
  `σ = rowNorm`), so `native_source_tuple`, `native_closure`, `native_rate` apply to it.
-/

open Finset Set
open scoped Real

namespace RenewalGeometry.RecordTuple

open NativeScaling (Mat eta metric)
open ShiftedJetAction (Grid)
open NativeDensity NativeModel SlabData NativeFrameBridge ActualJetFrame ActualJetSystem
open NativeModelExample
open TrigInterp (recon reconLow tau)

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- `c η` is in the Lorentzian foliated chart for `c > 0`. -/
theorem isLorChart_smul_eta {c : ℝ} (hc : 0 < c) : IsLorChart (fun a b => c * eta a b) := by
  set gi : IMet := fun a b => c * eta a b with hgi
  have e00 : gi 0 0 = -c := by simp [gi, eta]
  have h0 : hInv gi 0 0 = c := by simp [hInv, gi, eta]
  have h10 : hInv gi 1 0 = 0 := by simp [hInv, gi, eta]
  have h11 : hInv gi 1 1 = c := by simp [hInv, gi, eta]
  have h20 : hInv gi 2 0 = 0 := by simp [hInv, gi, eta]
  have h21 : hInv gi 2 1 = 0 := by simp [hInv, gi, eta]
  have h22 : hInv gi 2 2 = c := by simp [hInv, gi, eta]
  have hL10 : L10 gi = 0 := by simp [L10, h10]
  have hL20 : L20 gi = 0 := by simp [L20, h20]
  have hL21 : L21 gi = 0 := by simp [L21, h21, hL20]
  refine ⟨by rw [e00]; linarith, by rw [h0]; exact hc, ?_, ?_⟩
  · rw [h11, hL10]; simpa using hc
  · rw [h22, hL20, hL21]; simpa using hc

theorem ginvOf_metric_flat :
    ginvOf (fun i j => metric ((2 * π) • (1 : Mat)) i j) =
      fun a b => ((2 * π) ^ 2)⁻¹ * eta a b := by
  funext a b
  show (metric ((2 * π) • (1 : Mat)))⁻¹ a b = _
  rw [FieldScaling.metric_smul, FieldScaling.inv_smul_mat (pow_ne_zero 2 two_pi_ne),
    metric_one_inv]
  rfl

/-- **The dilated flat coframe has a chart margin.** -/
theorem exists_margin_flat : ∃ δ : ℝ, 0 < δ ∧
    Margin δ (ginvOf (fun i j => metric ((2 * π) • (1 : Mat)) i j)) := by
  obtain ⟨δ, hδ, hm⟩ := exists_margin
    (Kg := {ginvOf (fun i j => metric ((2 * π) • (1 : Mat)) i j)}) isCompact_singleton
    (fun gi hgi => by
      rw [Set.mem_singleton_iff] at hgi
      rw [hgi, ginvOf_metric_flat]
      exact isLorChart_smul_eta (by positivity))
  exact ⟨δ, hδ, hm _ rfl⟩

theorem isAdaptedCoframe_one : IsAdaptedCoframe (1 : Mat) :=
  ⟨fun a μ h => by simp [(ne_of_lt h)], fun a => by simp⟩

/-- A Higgs record with flat coframe: `u(y) = (1, 0, H(y), 0, 0)`. -/
def higgsRec {n : ℕ} (H : Grid n → ℝ) : Grid n → Field ℝ ℝ Sp :=
  fun y => ((1 : Mat), 0, H y, 0, 0)

theorem nodalGauge_higgsRec {n : ℕ} (H : Grid n → ℝ) : NodalGauge diracSlab (higgsRec H) where
  adapted _ := isAdaptedCoframe_one
  temporal _ := rfl
  gauge _ _ := Submodule.zero_mem _
  clin _ := fun x => by simp [higgsRec]

theorem recon_higgsRec_fst {n : ℕ} [NeZero n] (hn : Odd n) (H : Grid n → ℝ) (x : Fin 4 → ℝ) :
    (recon n (higgsRec H) x).1 = 1 := by
  have h := recon_clm (fstL (𝔄 := ℝ) (𝓗 := ℝ) (𝓢 := Sp)) (higgsRec H) x
  have e : (fun y => fstL (𝔄 := ℝ) (𝓗 := ℝ) (𝓢 := Sp) (higgsRec H y)) =
      fun _ => (1 : Mat) := by
    funext y; rfl
  rw [e, NativeTail.recon_const hn] at h
  exact h

/-- **Non-flat records satisfy the tuple hypotheses**: for every odd `n`, every nodal Higgs
field `H` and every time shift `t₀` there is a margin `δ > 0` with
`TupleHyp diracSlab δ (dilField t₀ (recon n (higgsRec H)))`. -/
theorem higgs_record_tupleHyp {n : ℕ} [NeZero n] (hn : Odd n) (H : Grid n → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ : ℝ, TupleHyp diracSlab δ (dilField t₀ (recon n (higgsRec H))) := by
  obtain ⟨δ, hδ, hm⟩ := exists_margin_flat
  refine ⟨δ, hδ, fun t₀ => ?_⟩
  refine tupleHyp_dil hn (nodalGauge_higgsRec H) (Ke := {(1 : Mat)})
    (fun e he => by rw [Set.mem_singleton_iff] at he; rw [he]; simp)
    (fun x => by rw [Set.mem_singleton_iff]; exact recon_higgsRec_fst hn H x)
    (fun e he _ => by rw [Set.mem_singleton_iff] at he; rw [he]; exact hm) t₀

/-- The flat vacuum record `u ≡ (1, 0, 0, 0, 0)`. -/
def vacRec (n : ℕ) : Grid n → Field ℝ ℝ Sp := higgsRec (fun _ => 0)

theorem vacRec_eq (n : ℕ) : vacRec n = fun _ => (((1 : Mat), 0, 0, 0, 0) : Field ℝ ℝ Sp) := rfl

/-- **The flat vacuum satisfies all record hypotheses of `thm:native-closure`** (chart `{1}`,
amplitude `‖(1,0,0,0,0)‖`, row bound `σ = rowNorm`, tuple hypotheses with the margin of
`exists_margin_flat`). -/
theorem vacuum_recordHyp {n : ℕ} [NeZero n] (hn : Odd n) {K : ℝ} (hK : 1 ≤ K)
    (t₀ t₁ b : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ RecordHyp diracSlab δ {(1 : Mat)}
      ‖(((1 : Mat), 0, 0, 0, 0) : Field ℝ ℝ Sp)‖ t₀ t₁ b n (vacRec n) K
      (rowNorm diracSlab t₀ t₁ b n (vacRec n)) := by
  obtain ⟨δ, hδ, ht⟩ := higgs_record_tupleHyp hn (fun _ : Grid n => (0 : ℝ))
  have hc : ∀ x, recon n (vacRec n) x = (((1 : Mat), 0, 0, 0, 0) : Field ℝ ℝ Sp) := fun x => by
    rw [vacRec_eq]; exact NativeTail.recon_const hn _ x
  have hcl : ∀ x, reconLow n K (vacRec n) x = (((1 : Mat), 0, 0, 0, 0) : Field ℝ ℝ Sp) :=
    fun x => by rw [vacRec_eq]; exact NativeTail.reconLow_const hn _ (by linarith) x
  refine ⟨δ, hδ, ?_⟩
  exact
    { odd := hn
      one_le := hK
      low_chart := fun x => by rw [hcl]; rfl
      low_amp := fun x => by rw [hcl]
      chart := fun x => by rw [hc]; rfl
      amp := fun x => by rw [hc]
      sigma_nonneg := rowNorm_nonneg _ _ _ _ _ _
      sigma := sq_le_of_rowNorm_le diracSlab le_rfl
      tuple := ht t₀ }

end

end RenewalGeometry.RecordTuple
