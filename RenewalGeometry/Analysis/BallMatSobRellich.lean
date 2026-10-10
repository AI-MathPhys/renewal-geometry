/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallRellich
import RenewalGeometry.Analysis.BallGaugeAlgebra

/-!
# Rellich compactness for the Banach algebras `H^s(B)` and `H^s(B, M_m(ℂ))`
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `rellich_SobAlg` — a bounded sequence in `H^{s+1}(B)` has a subsequence whose restriction
  converges in `H^s(B)` (`rellich_HsB` on the jets, rescaled norms);
* `rellich_Cx` — the same for the complexification;
* `rellich_MatSob` (**main result**) — the same for matrix fields `H^{s+1}(B, M_m(ℂ))`
  (finite diagonal extraction over the entries).
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {s : ℕ} [hs : Fact (3 ≤ s)] {m : ℕ}

/-- **Rellich for the Banach algebra `H^{s+1}(B)`.** -/
theorem rellich_SobAlg (F : ℕ → SobAlg c r (s + 1)) {M : ℝ} (hM : ∀ k, ‖F k‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (G : SobAlg c r s), StrictMono φ ∧
      Tendsto (fun k => restrS (Nat.le_succ s) (F (φ k))) atTop (𝓝 G) := by
  have hb : ∀ k, ‖jet (F k)‖ ≤ (Kal c r (s + 1))⁻¹ * M := fun k =>
    (norm_jet_le (F k)).trans (mul_le_mul_of_nonneg_left (hM k) (inv_nonneg.mpr (Kal_pos c r (s + 1)).le))
  obtain ⟨φ, G, hφ, hG⟩ := rellich_HsB c r (fun k => jet (F k)) hb
  refine ⟨φ, ofJet G, hφ, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero] at hG ⊢
  have := hG.const_mul (Kal c r s)
  rw [mul_zero] at this
  refine this.congr fun k => ?_
  show Kal c r s * ‖restrL c r (Nat.le_succ s) (jet (F (φ k))) - G‖ =
    ‖ofJet (restrL c r (Nat.le_succ s) (jet (F (φ k)))) - ofJet G‖
  rw [← norm_ofJet]
  rfl

theorem tendsto_cx_of {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] {u : ℕ → Cx V} {z : Cx V}
    (h1 : Tendsto (fun k => (u k).re) atTop (𝓝 z.re))
    (h2 : Tendsto (fun k => (u k).im) atTop (𝓝 z.im)) : Tendsto u atTop (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h1 h2 ⊢
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr fun k => ?_
  rw [Cx.norm_def]
  rfl

/-- **Rellich for `H^{s+1}(B, M_m(ℂ))`**: a bounded sequence of matrix fields has a subsequence
whose restriction converges in `H^s(B, M_m(ℂ))`. -/
theorem rellich_MatSob (F : ℕ → MatSob c r (s + 1) m) {M : ℝ} (hM : ∀ k, ‖F k‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (G : MatSob c r s m), StrictMono φ ∧
      Tendsto (fun k => rhoM (F (φ k))) atTop (𝓝 G) := by
  classical
  -- component bounds
  have hre : ∀ i j k, ‖(F k i j).re‖ ≤ M := fun i j k =>
    (Cx.norm_re_le _).trans ((norm_entry_le_linfty (F k) i j).trans (hM k))
  have him : ∀ i j k, ‖(F k i j).im‖ ≤ M := fun i j k =>
    (Cx.norm_im_le _).trans ((norm_entry_le_linfty (F k) i j).trans (hM k))
  -- the index set of components
  set Ι := Fin m × Fin m × Bool
  let e : Fin (Fintype.card Ι) ≃ Ι := (Fintype.equivFin Ι).symm
  let comp : ℕ → Ι → SobAlg c r (s + 1) := fun k p =>
    if p.2.2 then (F k p.1 p.2.1).re else (F k p.1 p.2.1).im
  have hcomp : ∀ p k, ‖comp k p‖ ≤ M := by
    intro p k
    by_cases h : p.2.2
    · simp only [comp, h, ite_true]; exact hre _ _ _
    · simp only [comp, h]; exact him _ _ _
  let P : Fin (Fintype.card Ι) → (ℕ → ℕ) → Prop := fun j φ =>
    ∃ G : SobAlg c r s, Tendsto (fun k => restrS (Nat.le_succ s) (comp (φ k) (e j))) atTop (𝓝 G)
  obtain ⟨φ, hφ, hP⟩ := exists_common_subseq' P (fun j φ hφ => by
      obtain ⟨ψ, G, hψ, hG⟩ := rellich_SobAlg (fun k => comp (φ k) (e j)) fun k => hcomp _ _
      exact ⟨ψ, hψ, G, hG⟩)
    (fun j φ ψ hψ ⟨G, hG⟩ => ⟨G, hG.comp hψ.tendsto_atTop⟩)
  choose G hG using hP
  have hG' : ∀ p, Tendsto (fun k => restrS (Nat.le_succ s) (comp (φ k) p)) atTop
      (𝓝 (G (e.symm p))) := fun p => by
    have := hG (e.symm p)
    simpa using this
  refine ⟨φ, Matrix.of fun i j => ⟨G (e.symm (i, j, true)), G (e.symm (i, j, false))⟩, hφ, ?_⟩
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  refine tendsto_cx_of ?_ ?_
  · have := hG' (i, j, true)
    simpa [comp, rhoM_apply] using this
  · have := hG' (i, j, false)
    simpa [comp, rhoM_apply] using this

end RenewalGeometry.BallAnalysis.BallAlg
