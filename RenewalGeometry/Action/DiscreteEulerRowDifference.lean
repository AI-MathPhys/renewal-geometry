/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.DiscreteEulerConsistency

/-!
# Mean-value bound for the difference of two discrete Euler rows

Generic infrastructure for `eq:native-Euler-tail` of the Einstein–Standard-Model action-closure
manuscript (`lem:native-tail-transfer`: "the finite Euler row is, after the exact
shifted-first-jet reduction, a smooth function of finitely many shifted jets through second
order; the mean-value theorem gives the bound").

For a shifted-first-jet lattice action `h⁴ Σ_x F(h, Ξ_h y(x))` on `(ℤ/n)⁴`
(`ShiftedJetAction.action`) and two smooth periodic fields `Y₀` and `Y₁ = Y₀ + W`:

* **`norm_eulerRow_sub_le`**: under the regularity packet `DensityReg F S δ M₂ M₃` around the
  continuum jets of `Y₀`, field bounds `FieldBound Y₀ B₁ B₂ B₃`, `FieldBound W b₁ b₂ b₃`,
  `|W| ≤ b₀` and the margin `h(1 + c₁) + b₀ + b₁ < δ`,
  `‖E_h(𝖲_h Y₁)(x) - E_h(𝖲_h Y₀)(x)‖ ≤ N M₂ (b₀ + b₁) + 4N (M₃ (b₀ + b₁)(B₁ + B₂ + b₁ + b₂)
  + M₂ (b₁ + b₂))` at every node, `N = card ι`: the difference is controlled by the first two
  derivatives of `W` only (no factor of `h⁻¹` survives, the divided differences of `W` being
  controlled by its derivatives).
-/

open Finset Filter Topology Metric Set
open scoped ContDiff

namespace RenewalGeometry.EulerRowDiff

open ShiftedJetAction (Grid unitVec stencil action)
open DiscreteEulerConsistency

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ℕ} [NeZero n]

theorem discJet_add (σZ : ι → Fin 4 → ℤ) (h : ℝ) (Y W : R4 → V) (b : R4) :
    discJet σZ h (Y + W) b = discJet σZ h Y b + discJet σZ h W b := by
  unfold discJet
  ext i <;> simp [smul_add, smul_sub]; abel

theorem norm_discJet_le {W : R4 → V} {b₀ b₁ b₂ b₃ : ℝ} (hW : FieldBound W b₁ b₂ b₃)
    (hW0 : ∀ z, ‖W z‖ ≤ b₀) (σZ : ι → Fin 4 → ℤ) {h : ℝ} (hh : 0 < h) (b : R4) :
    ‖discJet σZ h W b‖ ≤ b₀ + b₁ := by
  have hb₀ : 0 ≤ b₀ := (norm_nonneg _).trans (hW0 0)
  have hb₁ := hW.B₁_nonneg
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i; exact (hW0 _).trans (by linarith)
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro p
    simp only [discJet]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    have := hW.lip0 (b + h • realVec (σZ p.1)) (b + h • realVec (σZ p.1) + h • evec p.2)
    rw [add_sub_cancel_left, norm_smul, norm_evec, Real.norm_eq_abs, abs_of_pos hh, mul_one] at this
    calc h⁻¹ * ‖W (b + h • realVec (σZ p.1) + h • evec p.2) - W (b + h • realVec (σZ p.1))‖
        ≤ h⁻¹ * (b₁ * h) := by gcongr
      _ = b₁ := by field_simp
      _ ≤ b₀ + b₁ := by linarith

theorem dDisc_add {Y W : R4 → V} (hY : Differentiable ℝ Y) (hW : Differentiable ℝ W)
    (σZ : ι → Fin 4 → ℤ) (h : ℝ) (b : R4) :
    dDisc σZ h (Y + W) b = dDisc σZ h Y b + dDisc σZ h W b := by
  unfold dDisc
  ext v i <;> simp [fderiv_add (hY _) (hW _), smul_add, smul_sub] <;> abel

variable {F : ℝ × Jet ι V → ℝ} {S : Set (Jet ι V)} {δ M₂ M₃ : ℝ} {Y₀ W : R4 → V}
  {B₁ B₂ B₃ b₀ b₁ b₂ b₃ : ℝ} {σZ : ι → Fin 4 → ℤ} {s : ℝ}

-- a long but elementary assembly of mean-value estimates
set_option maxHeartbeats 2000000 in
/-- **The mean-value bound for the difference of two discrete Euler rows.** -/
theorem norm_eulerRow_sub_le (hF : DensityReg F S δ M₂ M₃) (hY : FieldBound Y₀ B₁ B₂ B₃)
    (hW : FieldBound W b₁ b₂ b₃) (hW0 : ∀ z, ‖W z‖ ≤ b₀)
    (hS : ∀ z, cmap (jet1 Y₀ z) ∈ S) (hs0 : 0 ≤ s) (hs : ∀ i μ, |(σZ i μ : ℝ)| ≤ s) {h : ℝ}
    (hh : 0 < h) (hper : IsPeriodic ((n : ℝ) * h) Y₀) (hperW : IsPeriodic ((n : ℝ) * h) W)
    (hδ : h * (1 + cJet B₁ B₂ s) + (b₀ + b₁) < δ) (x : Grid n) :
    ‖eulerRow (action (fun ξ => F (h, ξ)) h (fun i => castVec (σZ i))) h (samp h (Y₀ + W)) x -
        eulerRow (action (fun ξ => F (h, ξ)) h (fun i => castVec (σZ i))) h (samp h Y₀) x‖ ≤
      Fintype.card ι * (M₂ * (b₀ + b₁)) +
        Fintype.card (ι × Fin 4) * (M₃ * (b₀ + b₁) * (B₁ + B₂ + (b₁ + b₂)) + M₂ * (b₁ + b₂)) := by
  have hc1 : 0 ≤ cJet B₁ B₂ s := by
    unfold cJet; have := hY.B₁_nonneg; have := hY.B₂_nonneg; positivity
  have hb₀ : 0 ≤ b₀ := (norm_nonneg _).trans (hW0 0)
  have hb₁ := hW.B₁_nonneg
  have hb₂ := hW.B₂_nonneg
  have hδ0 : 0 < δ := lt_of_le_of_lt (by positivity) hδ
  have hδ' : h * (1 + cJet B₁ B₂ s) < δ := by linarith
  have hperY : IsPeriodic ((n : ℝ) * h) (Y₀ + W) := fun z μ => by
    simp only [Pi.add_apply, hper z μ, hperW z μ]
  set σ : ι → Grid n := fun i => castVec (σZ i) with hσ
  set z₀ := pos h x with hz₀
  set J : Jet ι V := cmap (jet1 Y₀ z₀) with hJ
  set P := pJet F with hP
  -- ball membership of discrete jets of both fields
  have hball₀ : ∀ b z, ‖b - z‖ ≤ h * (s + 1) →
      (h, discJet σZ h Y₀ b) ∈ ball ((0 : ℝ), (cmap (jet1 Y₀ z) : Jet ι V)) δ ∧
        ‖((h, discJet σZ h Y₀ b) : ℝ × Jet ι V) - (0, cmap (jet1 Y₀ z))‖ ≤ h * (1 + cJet B₁ B₂ s) :=
    fun b z hb => discJet_mem_ball hY hh hs0 hs hδ' hb
  have hball₁ : ∀ b z, ‖b - z‖ ≤ h * (s + 1) →
      (h, discJet σZ h (Y₀ + W) b) ∈ ball ((0 : ℝ), (cmap (jet1 Y₀ z) : Jet ι V)) δ := by
    intro b z hb
    rw [mem_ball, dist_eq_norm]
    have h1 := (hball₀ b z hb).2
    have h2 := norm_discJet_le hW hW0 σZ hh b
    have e : ((h, discJet σZ h (Y₀ + W) b) : ℝ × Jet ι V) - (0, cmap (jet1 Y₀ z)) =
        (((h, discJet σZ h Y₀ b) : ℝ × Jet ι V) - (0, cmap (jet1 Y₀ z))) +
          ((0 : ℝ), discJet σZ h W b) := by
      rw [discJet_add]; ext <;> simp <;> abel
    rw [e]
    calc ‖(((h, discJet σZ h Y₀ b) : ℝ × Jet ι V) - (0, cmap (jet1 Y₀ z))) +
          ((0 : ℝ), discJet σZ h W b)‖
        ≤ h * (1 + cJet B₁ B₂ s) + (b₀ + b₁) := by
          refine (norm_add_le _ _).trans (add_le_add h1 ?_)
          rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]; exact h2
      _ < δ := hδ
  -- differentiability at every stencil
  have hdiffY : ∀ (Y : R4 → V), IsPeriodic ((n : ℝ) * h) Y →
      (∀ z : Grid n, (h, discJet σZ h Y (pos h z)) ∈
        ball ((0 : ℝ), (cmap (jet1 Y₀ (pos h z)) : Jet ι V)) δ) →
      ∀ z : Grid n, DifferentiableAt ℝ (fun ξ => F (h, ξ)) (stencil h σ z (samp h Y)) := by
    intro Y hpY hm z
    rw [hσ, stencil_samp' hpY]
    have hin := ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).hasFDerivAt
      (x := discJet σZ h Y (pos h z))).const_add ((h, 0) : ℝ × Jet ι V)
    have hin' : DifferentiableAt ℝ (fun ξ : Jet ι V => ((h, ξ) : ℝ × Jet ι V))
        (discJet σZ h Y (pos h z)) :=
      (hin.congr_of_eventuallyEq (Eventually.of_forall fun ξ' => by simp)).differentiableAt
    exact (hF.diff _ (hS _) _ (hm z)).comp _ hin'
  have hdiff₀ := hdiffY Y₀ hper fun z => (hball₀ (pos h z) (pos h z) (by simp; positivity)).1
  have hdiff₁ := hdiffY (Y₀ + W) hperY fun z => hball₁ (pos h z) (pos h z) (by simp; positivity)
  -- the shifted base points
  set a : ι → R4 := fun i => z₀ + h • realVec (-σZ i) with ha
  set a' : ι × Fin 4 → R4 := fun p => z₀ + h • realVec (-σZ p.1 - Pi.single p.2 1) with ha'
  have hnode : ∀ i, x - σ i = x + castVec (-σZ i) := fun i => by
    rw [castVec_neg, sub_eq_add_neg]
  have hnode' : ∀ p : ι × Fin 4, x - σ p.1 - unitVec n p.2 =
      x + castVec (-σZ p.1 - Pi.single p.2 1) := fun p => by
    rw [sub_eq_add_neg (-σZ p.1), castVec_add, castVec_neg, castVec_neg, castVec_single]; abel
  have hst : ∀ (Y : R4 → V), IsPeriodic ((n : ℝ) * h) Y → ∀ i,
      stencil h σ (x - σ i) (samp h Y) = discJet σZ h Y (a i) := fun Y hpY i => by
    rw [hnode, hσ, stencil_samp hpY]
  have hst' : ∀ (Y : R4 → V), IsPeriodic ((n : ℝ) * h) Y → ∀ p : ι × Fin 4,
      stencil h σ (x - σ p.1 - unitVec n p.2) (samp h Y) = discJet σZ h Y (a' p) := fun Y hpY p => by
    rw [hnode', hσ, stencil_samp hpY]
  have hsi : ∀ i μ, |((-σZ i) μ : ℝ)| ≤ s := fun i μ => by simpa using hs i μ
  have ha_le : ∀ i, ‖a i - z₀‖ ≤ h * (s + 1) := fun i => by
    rw [ha]; simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left ((norm_realVec_le (hsi i) hs0).trans (by linarith)) hh.le
  have hsa : ∀ (p : ι × Fin 4) (μ : Fin 4),
      |(((-σZ p.1 - Pi.single p.2 1 : Fin 4 → ℤ) μ : ℤ) : ℝ)| ≤ s + 1 := by
    intro p μ
    have h1 := hs p.1 μ
    simp only [Pi.sub_apply, Pi.neg_apply, Int.cast_sub, Int.cast_neg]
    by_cases hμ : μ = p.2
    · subst hμ
      simp only [Pi.single_eq_same, Int.cast_one]
      calc |-(σZ p.1 p.2 : ℝ) - 1| ≤ |-(σZ p.1 p.2 : ℝ)| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ s + 1 := by rw [abs_neg, abs_one]; linarith
    · simp only [Pi.single_eq_of_ne hμ, Int.cast_zero, sub_zero, abs_neg]; linarith
  have ha'_le : ∀ p : ι × Fin 4, ‖a' p - z₀‖ ≤ h * (s + 1) := fun p => by
    rw [ha']; simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left (norm_realVec_le (hsa p) (by linarith)) hh.le
  have hseg : ∀ p : ι × Fin 4, a p.1 - a' p = h • evec p.2 := fun p => by
    rw [ha, ha']
    simp only [add_sub_add_left_eq_sub, ← smul_sub]
    congr 1
    rw [sub_eq_add_neg (-σZ p.1), realVec_add, realVec_neg (Pi.single p.2 1), realVec_single]
    abel
  -- the two rows in slot form
  rw [eulerRow_action_eq hh.ne' hdiff₁ x, eulerRow_action_eq hh.ne' hdiff₀ x]
  have hP1 : ∀ (Y : R4 → V) (hpY : IsPeriodic ((n : ℝ) * h) Y),
      (∀ b, ‖b - z₀‖ ≤ h * (s + 1) → (h, discJet σZ h Y b) ∈ ball ((0 : ℝ), J) δ) →
      ∀ i, fderiv ℝ (fun ξ => F (h, ξ)) (stencil h σ (x - σ i) (samp h Y)) =
        P (h, discJet σZ h Y (a i)) := fun Y hpY hm i => by
    rw [hst Y hpY]
    exact fderiv_slice (hF.diff _ (hS z₀) _ (hm _ (ha_le i)))
  have hP2 : ∀ (Y : R4 → V) (hpY : IsPeriodic ((n : ℝ) * h) Y),
      (∀ b, ‖b - z₀‖ ≤ h * (s + 1) → (h, discJet σZ h Y b) ∈ ball ((0 : ℝ), J) δ) →
      ∀ p : ι × Fin 4,
      fderiv ℝ (fun ξ => F (h, ξ)) (stencil h σ (x - σ p.1 - unitVec n p.2) (samp h Y)) =
        P (h, discJet σZ h Y (a' p)) := fun Y hpY hm p => by
    rw [hst' Y hpY]
    exact fderiv_slice (hF.diff _ (hS z₀) _ (hm _ (ha'_le p)))
  have hm₀ : ∀ b, ‖b - z₀‖ ≤ h * (s + 1) → (h, discJet σZ h Y₀ b) ∈ ball ((0 : ℝ), J) δ :=
    fun b hb => (hball₀ b z₀ hb).1
  have hm₁ : ∀ b, ‖b - z₀‖ ≤ h * (s + 1) → (h, discJet σZ h (Y₀ + W) b) ∈ ball ((0 : ℝ), J) δ :=
    fun b hb => hball₁ b z₀ hb
  simp only [hP1 Y₀ hper hm₀, hP2 Y₀ hper hm₀, hP1 (Y₀ + W) hperY hm₁, hP2 (Y₀ + W) hperY hm₁]
  -- algebraic rearrangement
  set g₁ : R4 → (Jet ι V →L[ℝ] ℝ) := fun b => P (h, discJet σZ h (Y₀ + W) b) with hg₁
  set g₀ : R4 → (Jet ι V →L[ℝ] ℝ) := fun b => P (h, discJet σZ h Y₀ b) with hg₀
  have hEq : (∑ i, (g₁ (a i)).comp (ιv i) +
      h⁻¹ • ∑ p : ι × Fin 4, ((g₁ (a' p)).comp (ιd p) - (g₁ (a p.1)).comp (ιd p))) -
      (∑ i, (g₀ (a i)).comp (ιv i) +
      h⁻¹ • ∑ p : ι × Fin 4, ((g₀ (a' p)).comp (ιd p) - (g₀ (a p.1)).comp (ιd p))) =
      ∑ i, (g₁ (a i) - g₀ (a i)).comp (ιv i) +
        ∑ p : ι × Fin 4, (h⁻¹ • ((g₁ (a' p) - g₀ (a' p)) - (g₁ (a p.1) - g₀ (a p.1)))).comp (ιd p) := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.smul_comp, Finset.smul_sum,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, smul_sub]
    abel
  rw [hEq]
  have hJmem : ((0 : ℝ), J) ∈ ball ((0 : ℝ), J) δ := mem_ball_self hδ0
  -- value terms
  have hval : ∀ i, ‖(g₁ (a i) - g₀ (a i)).comp (ιv i)‖ ≤ M₂ * (b₀ + b₁) := by
    intro i
    refine (norm_comp_slot_le (norm_ιv_le i)).trans ?_
    have := (convex_ball ((0 : ℝ), J) δ).norm_image_sub_le_of_norm_fderiv_le
      (fun q hq => hF.diffP _ (hS z₀) q hq) (fun q hq => hF.boundDP _ (hS z₀) q hq)
      (hm₀ _ (ha_le i)) (hm₁ _ (ha_le i))
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hF.M₂_nonneg)
    have e : ((h, discJet σZ h (Y₀ + W) (a i)) : ℝ × Jet ι V) - (h, discJet σZ h Y₀ (a i)) =
        ((0 : ℝ), discJet σZ h W (a i)) := by
      rw [discJet_add]; ext <;> simp
    rw [e, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
    exact norm_discJet_le hW hW0 σZ hh _
  -- difference terms
  have hdif : ∀ p : ι × Fin 4,
      ‖(h⁻¹ • ((g₁ (a' p) - g₀ (a' p)) - (g₁ (a p.1) - g₀ (a p.1)))).comp (ιd p)‖ ≤
        M₃ * (b₀ + b₁) * (B₁ + B₂ + (b₁ + b₂)) + M₂ * (b₁ + b₂) := by
    intro p
    refine (norm_comp_slot_le (norm_ιd_le p)).trans ?_
    set G : R4 → (Jet ι V →L[ℝ] ℝ) := fun b => g₁ b - g₀ b with hG
    have hsegball : segment ℝ (a' p) (a p.1) ⊆ closedBall z₀ (h * (s + 1)) :=
      (convex_closedBall z₀ _).segment_subset (by rw [mem_closedBall, dist_eq_norm]; exact ha'_le p)
        (by rw [mem_closedBall, dist_eq_norm]; exact ha_le p.1)
    have hY1 : FieldBound (Y₀ + W) (B₁ + b₁) (B₂ + b₂) (B₃ + b₃) := by
      refine ⟨hY.smooth.add hW.smooth, fun z => ?_, fun a b => ?_, fun a b => ?_,
        add_nonneg hY.B₁_nonneg hb₁, add_nonneg hY.B₂_nonneg hb₂,
        add_nonneg hY.B₃_nonneg hW.B₃_nonneg⟩
      · rw [fderiv_add (hY.diff0 z) (hW.diff0 z)]
        exact (norm_add_le _ _).trans (add_le_add (hY.b1 z) (hW.b1 z))
      · have e : fderiv ℝ (Y₀ + W) b - fderiv ℝ (Y₀ + W) a =
            (fderiv ℝ Y₀ b - fderiv ℝ Y₀ a) + (fderiv ℝ W b - fderiv ℝ W a) := by
          rw [fderiv_add (hY.diff0 b) (hW.diff0 b), fderiv_add (hY.diff0 a) (hW.diff0 a)]; abel
        rw [e]
        refine (norm_add_le _ _).trans ?_
        have := hY.lip1 a b; have := hW.lip1 a b
        nlinarith [norm_nonneg ((b - a : R4))]
      · have hfd : fderiv ℝ (Y₀ + W) = fderiv ℝ Y₀ + fderiv ℝ W := by
          funext z; rw [Pi.add_apply, fderiv_add (hY.diff0 z) (hW.diff0 z)]
        have e : fderiv ℝ (fderiv ℝ (Y₀ + W)) b - fderiv ℝ (fderiv ℝ (Y₀ + W)) a =
            (fderiv ℝ (fderiv ℝ Y₀) b - fderiv ℝ (fderiv ℝ Y₀) a) +
              (fderiv ℝ (fderiv ℝ W) b - fderiv ℝ (fderiv ℝ W) a) := by
          rw [hfd, fderiv_add (hY.diff1 b) (hW.diff1 b), fderiv_add (hY.diff1 a) (hW.diff1 a)]
          abel
        rw [e]
        refine (norm_add_le (E := R4 →L[ℝ] (R4 →L[ℝ] V)) _ _).trans ?_
        have := hY.lip2 a b; have := hW.lip2 a b
        nlinarith [norm_nonneg ((b - a : R4))]
    have hgd : ∀ b ∈ segment ℝ (a' p) (a p.1), HasFDerivAt G
        ((fderiv ℝ P (h, discJet σZ h (Y₀ + W) b)).comp
            ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dDisc σZ h (Y₀ + W) b)) -
          (fderiv ℝ P (h, discJet σZ h Y₀ b)).comp
            ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dDisc σZ h Y₀ b))) b := by
      intro b hb
      have hb' : ‖b - z₀‖ ≤ h * (s + 1) := by
        have := hsegball hb; rwa [mem_closedBall, dist_eq_norm] at this
      have hin : ∀ (Y : R4 → V) {C₁ C₂ C₃ : ℝ}, FieldBound Y C₁ C₂ C₃ →
          HasFDerivAt (fun b => ((h, discJet σZ h Y b) : ℝ × Jet ι V))
            ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dDisc σZ h Y b)) b := by
        intro Y C₁ C₂ C₃ hYb
        have := (((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).hasFDerivAt
          (x := discJet σZ h Y b)).comp b (hasFDerivAt_discJet (σZ := σZ) hYb h b)).const_add
          ((h, 0) : ℝ × Jet ι V)
        refine this.congr_of_eventuallyEq (Eventually.of_forall fun b' => ?_)
        simp
      exact ((hF.diffP _ (hS z₀) _ (hm₁ b hb')).hasFDerivAt.comp b (hin _ hY1)).sub
        ((hF.diffP _ (hS z₀) _ (hm₀ b hb')).hasFDerivAt.comp b (hin _ hY))
    have hgb : ∀ b ∈ segment ℝ (a' p) (a p.1), ‖fderiv ℝ G b‖ ≤
        M₃ * (b₀ + b₁) * (B₁ + B₂ + (b₁ + b₂)) + M₂ * (b₁ + b₂) := by
      intro b hb
      have hb' : ‖b - z₀‖ ≤ h * (s + 1) := by
        have := hsegball hb; rwa [mem_closedBall, dist_eq_norm] at this
      rw [(hgd b hb).fderiv]
      set A₁ := fderiv ℝ P (h, discJet σZ h (Y₀ + W) b)
      set A₀ := fderiv ℝ P (h, discJet σZ h Y₀ b)
      set D₁ := dDisc σZ h (Y₀ + W) b
      set D₀ := dDisc σZ h Y₀ b
      set ιr := ContinuousLinearMap.inr ℝ ℝ (Jet ι V)
      have hιr : ‖ιr‖ ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
        simp [ιr, Prod.norm_def]
      have e : A₁.comp (ιr.comp D₁) - A₀.comp (ιr.comp D₀) =
          (A₁ - A₀).comp (ιr.comp D₁) + A₀.comp (ιr.comp (D₁ - D₀)) := by
        simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]; abel
      rw [e]
      have hAA : ‖A₁ - A₀‖ ≤ M₃ * (b₀ + b₁) := by
        refine (hF.lipDP _ (hS z₀) _ (hm₁ b hb') _ (hm₀ b hb')).trans
          (mul_le_mul_of_nonneg_left ?_ hF.M₃_nonneg)
        have e2 : ((h, discJet σZ h (Y₀ + W) b) : ℝ × Jet ι V) - (h, discJet σZ h Y₀ b) =
            ((0 : ℝ), discJet σZ h W b) := by
          rw [discJet_add]; ext <;> simp
        rw [e2, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
        exact norm_discJet_le hW hW0 σZ hh _
      have hDD : ‖D₁ - D₀‖ ≤ b₁ + b₂ := by
        have e3 : D₁ - D₀ = dDisc σZ h W b := by
          simp only [D₁, D₀]; rw [dDisc_add hY.diff0 hW.diff0]; abel
        rw [e3]; exact norm_dDisc_le hW hh b
      have hD : ‖D₁‖ ≤ B₁ + b₁ + (B₂ + b₂) := norm_dDisc_le hY1 hh b
      have hA₀ : ‖A₀‖ ≤ M₂ := hF.boundDP _ (hS z₀) _ (hm₀ b hb')
      calc ‖(A₁ - A₀).comp (ιr.comp D₁) + A₀.comp (ιr.comp (D₁ - D₀))‖
          ≤ ‖A₁ - A₀‖ * (‖ιr‖ * ‖D₁‖) + ‖A₀‖ * (‖ιr‖ * ‖D₁ - D₀‖) := by
            refine (norm_add_le ((A₁ - A₀).comp (ιr.comp D₁)) (A₀.comp (ιr.comp (D₁ - D₀)))).trans
              (add_le_add ?_ ?_)
            · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
                (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
                  (norm_nonneg (A₁ - A₀)))
            · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
                (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
                  (norm_nonneg A₀))
        _ ≤ (M₃ * (b₀ + b₁)) * (1 * (B₁ + b₁ + (B₂ + b₂))) + M₂ * (1 * (b₁ + b₂)) := by
            have hDn := norm_nonneg D₁
            have hDDn := norm_nonneg (D₁ - D₀)
            have hm3 : 0 ≤ M₃ * (b₀ + b₁) := by have := hF.M₃_nonneg; positivity
            exact add_le_add
              (mul_le_mul hAA (mul_le_mul hιr hD hDn zero_le_one) (by positivity) hm3)
              (mul_le_mul hA₀ (mul_le_mul hιr hDD hDDn zero_le_one) (by positivity) hF.M₂_nonneg)
        _ = M₃ * (b₀ + b₁) * (B₁ + B₂ + (b₁ + b₂)) + M₂ * (b₁ + b₂) := by ring
    have hmv := (convex_segment (a' p) (a p.1)).norm_image_sub_le_of_norm_fderiv_le
      (f := G) (fun b hb => (hgd b hb).differentiableAt) hgb
      (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    rw [hseg p, norm_smul, norm_evec, Real.norm_eq_abs, abs_of_pos hh, mul_one] at hmv
    have e : h⁻¹ • ((g₁ (a' p) - g₀ (a' p)) - (g₁ (a p.1) - g₀ (a p.1))) =
        -(h⁻¹ • (G (a p.1) - G (a' p))) := by
      simp only [hG]; module
    rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    calc h⁻¹ * ‖G (a p.1) - G (a' p)‖
        ≤ h⁻¹ * ((M₃ * (b₀ + b₁) * (B₁ + B₂ + (b₁ + b₂)) + M₂ * (b₁ + b₂)) * h) := by gcongr
      _ = M₃ * (b₀ + b₁) * (B₁ + B₂ + (b₁ + b₂)) + M₂ * (b₁ + b₂) := by
          rw [mul_comm _ h, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
  -- summation
  calc ‖∑ i, (g₁ (a i) - g₀ (a i)).comp (ιv i) +
        ∑ p : ι × Fin 4, (h⁻¹ • ((g₁ (a' p) - g₀ (a' p)) - (g₁ (a p.1) - g₀ (a p.1)))).comp (ιd p)‖
      ≤ ∑ _i : ι, M₂ * (b₀ + b₁) +
          ∑ _p : ι × Fin 4, (M₃ * (b₀ + b₁) * (B₁ + B₂ + (b₁ + b₂)) + M₂ * (b₁ + b₂)) :=
        (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum
          fun i _ => hval i)) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => hdif p)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end

end RenewalGeometry.EulerRowDiff
