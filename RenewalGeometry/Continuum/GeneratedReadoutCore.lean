/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedJetReadout
import RenewalGeometry.Continuum.ActualJetKatoRealization

/-!
# Readouts of chart-smooth functionals near a compact jet set

Generic infrastructure (no renewal notions) for `eq:generated-bosonic` / `eq:generated-Dirac`
(Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`): a family of
functionals `Ψ_k` smooth on an open chart `O` of jet space, a compact set `K₁ ⊆ O` containing the
jets of the exact solution; then there are a margin `ε₀ > 0` (`cthickening ε₀ K₁ ⊆ O`), smooth
global extensions `Ψ̃_k = Ψ_k` on the margin, and a constant `K` such that on every slice where the
`H^r` energy `E ≤ 1` of the jet difference is small (`C_S E ≤ ε₀²`), the record jets lie in the
margin and `‖Ψ̃_k(u) - Ψ̃_k(v)‖²_{H^r} ≤ K E`.

* **`readout_core`**.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real

noncomputable section

namespace RenewalGeometry.GenHermite

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin

set_option linter.unusedSectionVars false

/-- **Readouts of chart-smooth functionals** on frozen slices of `𝕋³` (`r ≥ 3`). -/
theorem readout_core {ι κ : Type*} [Fintype ι] [Fintype κ] {r : ℕ} (hr : 3 ≤ r)
    {O : Set (ι → ℝ)} (hO : IsOpen O) {K₁ : Set (ι → ℝ)} (hK₁ : IsCompact K₁) (hK₁O : K₁ ⊆ O)
    {Ψ : κ → (ι → ℝ) → ℝ} (hΨ : ∀ k, ContDiffOn ℝ ∞ (Ψ k) O) {M : ℝ} (hM : 0 ≤ M) :
    ∃ ε₀ > 0, Metric.cthickening ε₀ K₁ ⊆ O ∧ ∃ Ψ' : κ → (ι → ℝ) → ℝ,
      (∀ k, ContDiff ℝ ∞ (Ψ' k)) ∧ (∀ k, ∀ w ∈ Metric.cthickening ε₀ K₁, Ψ' k w = Ψ k w) ∧
      ∃ K ≥ 0, ∃ CS ≥ 0, ∀ u v : ι → ST 3 → ℝ, (∀ i, ContDiff ℝ ∞ (u i)) →
        (∀ i, ContDiff ℝ ∞ (v i)) → (∀ i, IsSPeriodic (u i)) → (∀ i, IsSPeriodic (v i)) →
        ∀ t E : ℝ, 0 ≤ E → E ≤ 1 → CS * E ≤ ε₀ ^ 2 →
        (∀ y, (fun i => v i (Fin.cons t y)) ∈ K₁) → ∑ i, Q r (v i) t ≤ M →
        ∑ i, Q r (fun x => u i x - v i x) t ≤ E →
        (∀ y, (fun i => u i (Fin.cons t y)) ∈ Metric.cthickening ε₀ K₁) ∧
        ∀ k, Q r (fun x => Ψ' k (fun i => u i x) - Ψ' k (fun i => v i x)) t ≤ K * E := by
  obtain ⟨ε₀, hε₀, hsub⟩ := hK₁.exists_cthickening_subset_open hO hK₁O
  have hK₂ : IsCompact (Metric.cthickening ε₀ K₁) := hK₁.cthickening
  obtain ⟨Ψ', hΨ's, hΨ'K⟩ := ActualJetKato.exists_contDiff_eqOn_family hO hK₂ hsub hΨ
  refine ⟨ε₀, hε₀, hsub, Ψ', hΨ's, hΨ'K, ?_⟩
  have hm : ((3 : ℕ) : ℝ) / 2 < (2 : ℕ) := by norm_num
  obtain ⟨K, hK0, hK⟩ := Q_compF_sub_le_idx (d := 3) (m := 2) (r := r) hm (by omega) hΨ's
    (R := Real.sqrt (2 * M + 2)) (Real.sqrt_nonneg _)
  obtain ⟨CS, hCS, hsup⟩ := abs_sub_le_of_Q (d := 3) (m := 2) (r := r) hm (by omega)
  refine ⟨K, hK0, CS, hCS, fun u v hu hv hup hvp t E hE0 hE1 hCSE hvK hvM hE => ⟨fun y => ?_,
    fun k => ?_⟩⟩
  · -- the margin
    have hd : ∀ i, |u i (Fin.cons t y) - v i (Fin.cons t y)| ≤ ε₀ := fun i => by
      refine (hsup u v hu hv hup hvp t E hE y i).trans ?_
      rw [← Real.sqrt_sq hε₀.le]
      exact Real.sqrt_le_sqrt hCSE
    refine Metric.mem_cthickening_of_dist_le _ (fun i => v i (Fin.cons t y)) _ _ (hvK y) ?_
    rw [dist_pi_le_iff hε₀.le]
    intro i
    rw [Real.dist_eq]
    exact hd i
  · -- the composition estimate
    have hRsq : Real.sqrt (2 * M + 2) ^ 2 = 2 * M + 2 := Real.sq_sqrt (by linarith)
    have huM : ∑ i, Q r (u i) t ≤ Real.sqrt (2 * M + 2) ^ 2 := by
      rw [hRsq]
      have h1 : ∀ i, Q r (u i) t ≤ 2 * Q r (v i) t + 2 * Q r (fun x => u i x - v i x) t := by
        intro i
        have := Q_add_le r (hv i) ((hu i).sub (hv i)) t
        simp only [add_sub_cancel] at this
        exact this
      calc ∑ i, Q r (u i) t ≤ ∑ i, (2 * Q r (v i) t + 2 * Q r (fun x => u i x - v i x) t) :=
            Finset.sum_le_sum fun i _ => h1 i
        _ = 2 * ∑ i, Q r (v i) t + 2 * ∑ i, Q r (fun x => u i x - v i x) t := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 2 * M + 2 := by linarith
    have hvM' : ∑ i, Q r (v i) t ≤ Real.sqrt (2 * M + 2) ^ 2 := by
      rw [hRsq]; linarith
    exact (hK k u v hu hv hup hvp t huM hvM').trans (mul_le_mul_of_nonneg_left hE hK0)

end RenewalGeometry.GenHermite
