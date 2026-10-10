/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.UhlenbeckCoulombApriori

/-!
# The continuity method and the Neumann (reflection) rendering of the Coulomb a-priori estimate
  (step (c) of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (K. Uhlenbeck, Comm. Math. Phys. 83 (1982),
Thm 1.3, proof by the continuity method).

* `continuity_method`: a subset `S ⊆ ℝ` containing `0`, closed in `[0,1]` and open to the right
  at each of its points in `[0,1)` contains `[0,1]` (real induction).  In Uhlenbeck's proof `S`
  is the set of dilation parameters for which a Coulomb gauge with `‖∇(g·A_t)‖ < δ` exists;
  openness is the implicit-function step, closedness the a-priori estimate plus compactness.
* `apriori_gap_propagation` (**first exit**): if `f` is continuous on `[0,1]`, `f 0 ≤ δ/2`, and
  the a-priori gap `f t ≤ δ ⇒ f t ≤ δ/2` holds at every `t ∈ [0,1]`, then `f ≤ δ/2` on `[0,1]`.
  With `f t = ‖∇(g_t·A_t)‖` and `coulomb_apriori_gap` this is the closedness half of the
  continuity method.
* `reflect`, `integral_comp_reflect`, `mFourierCoeff_zero_eq_zero_of_odd`: the coordinate
  reflection `x_j ↦ -x_j` of `𝕋⁴` preserves the Haar measure, so a function odd under it has mean
  zero.
* `coulomb_apriori_torus_neumann` (**a-priori estimate in the Neumann/reflection rendering**): a
  one-form on `𝕋⁴` whose component `a_ν` is odd under the reflection of the `ν`-th coordinate is
  the reflection extension of a one-form on the cube `[0, 1/2]⁴` satisfying the Neumann
  condition `*a|_{∂Q} = 0` (normal component vanishing on the faces); for such forms the
  mean-zero hypothesis of `coulomb_apriori_torus` is automatic, so a Coulomb, Neumann one-form
  with `‖∇a‖ ≤ δ` satisfies `‖∇a‖ ≤ 32 m² ‖F_a‖`, with no harmonic part (as on a ball).
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal Real

noncomputable section

namespace RenewalGeometry.UhlenbeckTorus

open SobolevOpen TorusSobolev

set_option linter.unusedSectionVars false

/-! ### The continuity method -/

/-- **The continuity method** (real induction on `[0,1]`): if `0 ∈ S`, `S ∩ [0,1]` is closed and
`S` is a right-neighbourhood of each of its points in `[0,1)`, then `[0,1] ⊆ S`. -/
theorem continuity_method {S : Set ℝ} (h0 : (0 : ℝ) ∈ S) (hclosed : IsClosed (S ∩ Icc 0 1))
    (hopen : ∀ t ∈ S ∩ Ico 0 1, S ∈ 𝓝[>] t) : Icc (0 : ℝ) 1 ⊆ S :=
  hclosed.Icc_subset_of_forall_mem_nhdsWithin h0 hopen

/-- **First exit / a-priori gap propagation.**  Let `f` be continuous on `[0,1]` with
`f 0 ≤ δ/2`, and suppose the a-priori gap: for every `t ∈ [0,1]`, `f t ≤ δ` implies
`f t ≤ δ/2`.  Then `f t ≤ δ/2` for all `t ∈ [0,1]`. -/
theorem apriori_gap_propagation {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : ContinuousOn f (Icc 0 1)) (h0 : f 0 ≤ δ / 2)
    (hgap : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ δ → f t ≤ δ / 2) :
    ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ δ / 2 := by
  set S : Set ℝ := {t | f t ≤ δ / 2}
  have hclosed : IsClosed (S ∩ Icc 0 1) := by
    have : S ∩ Icc 0 1 = Icc 0 1 ∩ f ⁻¹' Iic (δ / 2) := by
      ext t; simp [S, and_comm]
    rw [this]
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hopen : ∀ t ∈ S ∩ Ico 0 1, S ∈ 𝓝[>] t := by
    rintro t ⟨ht, ht0, ht1⟩
    have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1.le⟩
    -- near `t` (inside `[0,1]`), `f < δ`
    have hlt : f t < δ := lt_of_le_of_lt ht (by linarith)
    have hnhds : ∀ᶠ s in 𝓝[Icc 0 1] t, f s < δ :=
      (hf t htc).eventually (gt_mem_nhds hlt)
    have hIcc : Icc (0 : ℝ) 1 ∈ 𝓝[>] t := by
      refine mem_nhdsWithin.2 ⟨Iio 1, isOpen_Iio, ht1, fun s ⟨hs1, hs2⟩ => ?_⟩
      exact ⟨le_trans ht0 (le_of_lt hs2), le_of_lt hs1⟩
    have h1 : ∀ᶠ s in 𝓝[>] t, s ∈ Icc (0 : ℝ) 1 := hIcc
    have h2 : ∀ᶠ s in 𝓝[>] t, f s < δ := by
      have hsub : 𝓝[>] t ≤ 𝓝[Icc 0 1] t := by
        rw [nhdsWithin_le_iff]; exact hIcc
      exact hsub hnhds
    filter_upwards [h1, h2] with s hs1 hs2
    exact hgap s hs1 hs2.le
  intro t ht
  exact continuity_method (S := S) h0 hclosed hopen ht

/-! ### Reflections of `𝕋⁴` and the Neumann rendering -/

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "𝕋⁴" => UnitAddTorus (Fin 4)

/-- The reflection `x_j ↦ -x_j` of the torus `𝕋⁴`. -/
def reflect (j : Fin 4) (x : 𝕋⁴) : 𝕋⁴ := Function.update x j (-x j)

theorem measurePreserving_neg_circle :
    MeasurePreserving (fun z : UnitAddCircle => -z) volume volume :=
  Measure.measurePreserving_neg volume

theorem measurePreserving_reflect (j : Fin 4) :
    MeasurePreserving (reflect j) (volume : Measure 𝕋⁴) volume := by
  have h : reflect j = fun x i => (if i = j then (fun z : UnitAddCircle => -z) else id) (x i) := by
    funext x i
    by_cases hi : i = j
    · subst hi; simp [reflect]
    · simp [reflect, Function.update_of_ne hi, hi]
  rw [h]
  refine measurePreserving_pi (fun _ => volume) (fun _ => volume) fun i => ?_
  by_cases hi : i = j
  · simp only [hi, if_true]; exact measurePreserving_neg_circle
  · simp only [hi, if_false]; exact MeasurePreserving.id _

theorem reflect_reflect (j : Fin 4) (x : 𝕋⁴) : reflect j (reflect j x) = x := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [reflect]
  · simp [reflect, Function.update_of_ne hi]

/-- The reflection as a measurable equivalence. -/
def reflectEquiv (j : Fin 4) : 𝕋⁴ ≃ᵐ 𝕋⁴ where
  toFun := reflect j
  invFun := reflect j
  left_inv := reflect_reflect j
  right_inv := reflect_reflect j
  measurable_toFun := (measurePreserving_reflect j).measurable
  measurable_invFun := (measurePreserving_reflect j).measurable

/-- A function odd under a coordinate reflection has mean zero: `f̂(0) = ∫ f = 0`. -/
theorem mFourierCoeff_zero_eq_zero_of_odd {f : 𝕋⁴ → ℂ} {j : Fin 4}
    (hodd : ∀ᵐ x ∂volume, f (reflect j x) = -f x) : mFourierCoeff f 0 = 0 := by
  have hm : mFourierCoeff f 0 = ∫ x, f x := by
    unfold mFourierCoeff
    simp [mFourier_zero]
  rw [hm]
  have h1 : ∫ x, f (reflect j x) = ∫ x, f x :=
    (measurePreserving_reflect j).integral_comp' (f := reflectEquiv j) f
  have h2 : ∫ x, f (reflect j x) = -∫ x, f x := by
    rw [integral_congr_ae hodd, integral_neg]
  have : ∫ x, f x = -∫ x, f x := h1.symm.trans h2
  have h3 : (2 : ℂ) * ∫ x, f x = 0 := by rw [two_mul]; nth_rewrite 2 [this]; ring
  exact (mul_eq_zero.1 h3).resolve_left two_ne_zero

/-- **Critical Coulomb a-priori estimate, Neumann (reflection) rendering.**  Under the hypotheses
of `coulomb_apriori_torus` with the mean-zero hypothesis replaced by the reflection symmetry
`a_{ν,ce}(R_ν x) = -a_{ν,ce}(x)` (the reflection extension of a Neumann one-form on the cube
`[0,1/2]⁴`, whose normal component vanishes on the faces): `‖∇a‖ ≤ δ` implies
`‖∇a‖ ≤ 32 m² ‖F_a‖`. -/
theorem coulomb_apriori_torus_neumann (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧
    ∀ (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
      IsH1Form a da → (∀ ν c e, ∀ᵐ x ∂volume, a ν c e (reflect ν x) = -a ν c e x) →
      IsCoulomb da → gradNorm da ≤ δ → gradNorm da ≤ 32 * (m : ℝ≥0∞) ^ 2 * curvNorm a da := by
  obtain ⟨δ, hδ, h⟩ := coulomb_apriori_torus m
  exact ⟨δ, hδ, fun a da ha hodd hC hX =>
    h a da ha (fun ν c e => mFourierCoeff_zero_eq_zero_of_odd (hodd ν c e)) hC hX⟩

/-! ### Non-vacuity -/

theorem isTPartial_const (μ : Fin 4) (z : ℂ) : IsTPartial μ (fun _ : 𝕋⁴ => z) (fun _ => 0) := by
  intro n
  rw [mFourierCoeff_const, mFourierCoeff_const]
  by_cases hn : n = 0
  · subst hn; simp [sym_zero]
  · simp [hn]

/-- Non-vacuity of the hypothesis packets: the trivial connection is an `H¹`, mean-zero, Coulomb
one-form (hypotheses of `coulomb_apriori_torus`), and the identity gauge intertwines it with
itself (hypotheses of `coulomb_gauge_unique_torus`). -/
example (m : ℕ) :
    IsH1Form (m := m) (fun _ _ _ _ => 0) (fun _ _ _ _ _ => 0) ∧
      mFourierCoeff (fun _ : 𝕋⁴ => (0 : ℂ)) 0 = 0 ∧
      IsCoulomb (m := m) (fun _ _ _ _ _ => 0) ∧
      (∀ (c e : Fin m) (μ : Fin 4),
        IsTPartial μ (fun _ : 𝕋⁴ => if c = e then (1 : ℂ) else 0) (fun _ => 0)) ∧
      (∀ (c e : Fin m) (μ : Fin 4), ∀ᵐ x ∂(volume : Measure 𝕋⁴),
        (0 : ℂ) = ∑ k, ((if c = k then (1 : ℂ) else 0) * 0 - 0 * (if k = e then 1 else 0))) := by
  refine ⟨⟨fun _ _ _ => memLp_const 0, fun _ _ _ _ => memLp_const 0,
    fun _ _ _ μ => isTPartial_const μ 0⟩, by simp [mFourierCoeff_const],
    fun c e => Eventually.of_forall fun x => by simp, fun c e μ => isTPartial_const μ _,
    fun c e μ => Eventually.of_forall fun x => by simp⟩

end RenewalGeometry.UhlenbeckTorus
