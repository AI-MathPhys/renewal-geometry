/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TorusSobolevDerivatives

/-!
# Compactness of `H^s(𝕋^d) ⊂ C¹(𝕋^d)` for `s > d/2 + 1`

Generic infrastructure (no renewal notions) for `thm:regular-branch` of the Einstein–Standard-Model
action-closure manuscript ("the stronger bounds `eq:regular-bosonic-bound` also give uniform
coefficient convergence": `H^{3+σ}(𝕋⁴)`-bounded fields have `C¹`-convergent subsequences, so that
the Dirac coefficients built from them converge in `W^{1,∞}`).

* `IsLineDeriv.sub`, `IsLineDeriv.unique` — line derivatives of differences, uniqueness;
* **`rellich_C1`** — a sequence of continuous functions bounded in `H^s(𝕋^d)`, `s > d/2 + 1`, has a
  subsequence converging uniformly together with all first partial derivatives (classical line
  derivatives), the limit lying in `H^s` with the same bound.  Proof: Rellich into `H^t`,
  `d/2 + 1 < t < s` (`rellich_coeff`), then `H^t ⊂ C¹` (`memH_isLineDeriv`).
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem IsLineDeriv.sub' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {i : d}
    {F F' G G' : UnitAddTorus d → E} (hF : IsLineDeriv i F F') (hG : IsLineDeriv i G G') :
    IsLineDeriv i (fun x => F x - G x) (fun x => F' x - G' x) := fun x =>
  (hF x).sub (hG x)

theorem IsLineDeriv.unique' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {i : d}
    {F F' F'' : UnitAddTorus d → E} (h1 : IsLineDeriv i F F') (h2 : IsLineDeriv i F F'') :
    F' = F'' := funext fun x => (h1 x).unique (h2 x)

/-- **Compactness of `H^s ⊂ C¹` for `s > d/2 + 1`**: a sequence of continuous functions bounded in
`H^s(𝕋^d)` has a subsequence converging uniformly, together with all first partial derivatives,
to a function of `H^s` with the same bound. -/
theorem rellich_C1 {s : ℝ} (hs : (Fintype.card d : ℝ) / 2 + 1 < s) {B : ℝ}
    (F : ℕ → C(UnitAddTorus d, ℂ)) (hF : ∀ k, MemH s (F k)) (hB : ∀ k, sobSq s (F k) ≤ B) :
    ∃ (φ : ℕ → ℕ) (G : C(UnitAddTorus d, ℂ)), StrictMono φ ∧ MemH s G ∧ sobSq s G ≤ B ∧
      Tendsto (fun k => ‖F (φ k) - G‖) atTop (𝓝 0) ∧
      ∀ i : d, ∃ (G' : C(UnitAddTorus d, ℂ)) (F' : ℕ → C(UnitAddTorus d, ℂ)),
        IsLineDeriv i ⇑G ⇑G' ∧ (∀ k, IsLineDeriv i ⇑(F (φ k)) ⇑(F' k)) ∧
        Tendsto (fun k => ‖F' k - G'‖) atTop (𝓝 0) := by
  set t := ((Fintype.card d : ℝ) / 2 + 1 + s) / 2 with ht_def
  have ht : (Fintype.card d : ℝ) / 2 + 1 < t := by rw [ht_def]; linarith
  have hts : t < s := by rw [ht_def]; linarith
  have ht0 : (Fintype.card d : ℝ) / 2 < t := by linarith
  obtain ⟨φ, cl, hφ, -, h2, h3, h4, h5⟩ :=
    rellich_coeff hts (fun k => mFourierCoeff ⇑(F k)) hF hB
  have hcl := (summable_norm_of_coeffMemH (by linarith) h2).1
  set G := fourierSum cl
  have hG : ∀ n, mFourierCoeff G n = cl n := mFourierCoeff_fourierSum hcl
  have hsub : ∀ k, mFourierCoeff ⇑(F (φ k) - G) = mFourierCoeff ⇑(F (φ k)) - cl := by
    intro k; funext n; rw [mFourierCoeff_continuous_sub, hG]; rfl
  have hGs : MemH s G := by show CoeffMemH s (mFourierCoeff G); rw [funext hG]; exact h2
  have hmt : ∀ k, MemH t ⇑(F (φ k) - G) := fun k => by
    show CoeffMemH t _; rw [hsub]; exact h4 k
  have hnorm : ∀ k, sobNorm t ⇑(F (φ k) - G) =
      Real.sqrt (coeffSobSq t (mFourierCoeff ⇑(F (φ k)) - cl)) := fun k => by
    unfold sobNorm sobSq; rw [hsub]
  have hlim : ∀ C : ℝ, Tendsto (fun k => C * sobNorm t ⇑(F (φ k) - G)) atTop (𝓝 0) := by
    intro C
    have := ((Real.continuous_sqrt.tendsto 0).comp h5).const_mul C
    simp only [Function.comp_def, Real.sqrt_zero, mul_zero] at this
    exact this.congr fun k => by rw [hnorm]
  refine ⟨φ, G, hφ, hGs, ?_, ?_, fun i => ?_⟩
  · unfold sobSq; rw [funext hG]; exact h3
  · exact squeeze_zero (fun k => norm_nonneg _)
      (fun k => norm_le_of_memH ht0 _ (hmt k)) (hlim _)
  · obtain ⟨G', hG', -, -⟩ := memH_isLineDeriv (by linarith) G (hGs.mono hts.le) i
    choose F' hF' _ _ using fun k => memH_isLineDeriv ht (F (φ k)) ((hF (φ k)).mono hts.le) i
    choose D hD _ hDb using fun k => memH_isLineDeriv ht (F (φ k) - G) (hmt k) i
    refine ⟨G', F', hG', hF', ?_⟩
    have heq : ∀ k, F' k - G' = D k := fun k => by
      have h1 : IsLineDeriv i ⇑(F (φ k) - G) ⇑(F' k - G') := by
        have := (hF' k).sub' hG'
        exact this
      have := h1.unique' (hD k)
      ext x
      exact congrFun this x
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => by rw [heq]; exact hDb k) (hlim _)

end

end RenewalGeometry.TorusSobolev
