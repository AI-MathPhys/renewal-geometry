/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniform `C^{1,1}` bounds and their calculus

Bookkeeping for the smooth-family estimates of `prop:mesh-consistency` (Einstein–Standard-Model
action-closure manuscript): every field entering the comparison stencils is controlled in
`W^{2,∞}` (`eq:smooth-reconstruction-estimate`), i.e. it is bounded, differentiable with bounded
derivative, and its derivative is Lipschitz.  `IsC11 f B` records these three bounds with one
constant `B`; the closure lemmas produce explicit constants depending only on the constants of
the inputs, so that the final estimates are uniform over bounded smooth families.

* `IsC11.lipschitz` (mean value), `IsC11.clm` (continuous linear images), `IsC11.add`,
  `IsC11.neg`, `IsC11.sub`, `IsC11.bilin` (continuous bilinear products), `IsC11.mono`,
  `IsC11.congr`;
* `exists_C1_on_compact`: a `C¹` map on an open set is bounded and Lipschitz on every compact
  subset;
* `exists_IsC11_comp`: composition with a `C²` map on an open set containing a compact set that
  contains the values (uniform constants);
* `exists_taylor2_on_compact`: the second-order Taylor remainder of a `C²` map is uniformly
  quadratic on a compact subset of an open set.
-/

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.C11Calculus

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
  [NormedSpace ℝ H]

/-- **`f` is `C^{1,1}` with constant `B`**: `‖f‖ ≤ B`, `‖Df‖ ≤ B`, `Df` is `B`-Lipschitz. -/
structure IsC11 (f : E → F) (B : ℝ) : Prop where
  hasFDerivAt : ∀ y, HasFDerivAt f (fderiv ℝ f y) y
  norm_le : ∀ y, ‖f y‖ ≤ B
  norm_fderiv_le : ∀ y, ‖fderiv ℝ f y‖ ≤ B
  lip : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ B * ‖y - z‖

namespace IsC11

variable {f g : E → F} {B B' : ℝ}

theorem nonneg [Nonempty E] (hf : IsC11 f B) : 0 ≤ B :=
  (norm_nonneg _).trans (hf.norm_le (Classical.arbitrary E))

theorem differentiable (hf : IsC11 f B) : Differentiable ℝ f := fun y =>
  (hf.hasFDerivAt y).differentiableAt

theorem continuous (hf : IsC11 f B) : Continuous f := hf.differentiable.continuous

theorem mono [Nonempty E] (hf : IsC11 f B) (h : B ≤ B') : IsC11 f B' :=
  ⟨hf.hasFDerivAt, fun y => (hf.norm_le y).trans h, fun y => (hf.norm_fderiv_le y).trans h,
    fun y z => (hf.lip y z).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))⟩

theorem congr (hf : IsC11 f B) (h : ∀ y, f y = g y) : IsC11 g B := by
  have e : f = g := funext h
  exact e ▸ hf

/-- **Mean value**: `‖f y - f z‖ ≤ B ‖y - z‖`. -/
theorem lipschitz (hf : IsC11 f B) (y z : E) : ‖f y - f z‖ ≤ B * ‖y - z‖ :=
  convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hf.hasFDerivAt x).hasFDerivWithinAt) (fun x _ => hf.norm_fderiv_le x)
    (mem_univ z) (mem_univ y)

/-- Continuous linear images. -/
theorem clm (hf : IsC11 f B) (Λ : F →L[ℝ] G) : IsC11 (fun y => Λ (f y)) (‖Λ‖ * B) := by
  have hd : ∀ y, HasFDerivAt (fun y => Λ (f y)) (Λ.comp (fderiv ℝ f y)) y := fun y =>
    Λ.hasFDerivAt.comp y (hf.hasFDerivAt y)
  have hfd : ∀ y, fderiv ℝ (fun y => Λ (f y)) y = Λ.comp (fderiv ℝ f y) := fun y => (hd y).fderiv
  refine ⟨fun y => by rw [hfd]; exact hd y, fun y => ?_, fun y => ?_, fun y z => ?_⟩
  · exact (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hf.norm_le y) (norm_nonneg _))
  · rw [hfd]; exact (Λ.opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (hf.norm_fderiv_le y) (norm_nonneg _))
  · rw [hfd, hfd, ← ContinuousLinearMap.comp_sub, mul_assoc]
    exact (Λ.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (hf.lip y z) (norm_nonneg _))

theorem add (hf : IsC11 f B) (hg : IsC11 g B') : IsC11 (fun y => f y + g y) (B + B') := by
  have hd : ∀ y, HasFDerivAt (fun y => f y + g y) (fderiv ℝ f y + fderiv ℝ g y) y := fun y =>
    (hf.hasFDerivAt y).add (hg.hasFDerivAt y)
  have hfd : ∀ y, fderiv ℝ (fun y => f y + g y) y = fderiv ℝ f y + fderiv ℝ g y :=
    fun y => (hd y).fderiv
  refine ⟨fun y => by rw [hfd]; exact hd y, fun y => (norm_add_le _ _).trans
    (add_le_add (hf.norm_le y) (hg.norm_le y)), fun y => by
      rw [hfd]; exact (norm_add_le _ _).trans (add_le_add (hf.norm_fderiv_le y)
        (hg.norm_fderiv_le y)), fun y z => ?_⟩
  rw [hfd, hfd, add_sub_add_comm, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf.lip y z) (hg.lip y z))

theorem neg [Nonempty E] (hf : IsC11 f B) : IsC11 (fun y => -f y) B := by
  have h1 := hf.clm (-ContinuousLinearMap.id ℝ F)
  have hn : ‖-ContinuousLinearMap.id ℝ F‖ ≤ 1 := by
    rw [norm_neg]; exact ContinuousLinearMap.norm_id_le
  have hB := hf.nonneg
  refine (h1.mono ?_).congr fun y => by simp
  nlinarith [norm_nonneg (-ContinuousLinearMap.id ℝ F)]

theorem sub [Nonempty E] (hf : IsC11 f B) (hg : IsC11 g B') :
    IsC11 (fun y => f y - g y) (B + B') :=
  (hf.add hg.neg).congr fun y => (sub_eq_add_neg _ _).symm

theorem const (c : F) : IsC11 (fun _ : E => c) ‖c‖ := by
  have hfd : ∀ y : E, fderiv ℝ (fun _ : E => c) y = 0 := fun y => fderiv_const_apply c
  refine ⟨fun y => by rw [hfd]; exact hasFDerivAt_const c y, fun y => le_rfl, fun y => ?_,
    fun y z => ?_⟩
  · rw [hfd, norm_zero]; exact norm_nonneg _
  · rw [hfd, hfd, sub_zero, norm_zero]; exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **Continuous bilinear products** `y ↦ β(f y, g y)`. -/
theorem bilin [Nonempty E] {g : E → G} (β : F →L[ℝ] G →L[ℝ] H) (hf : IsC11 f B)
    (hg : IsC11 g B') : IsC11 (fun y => β (f y) (g y)) (4 * ‖β‖ * B * B') := by
  have hB := hf.nonneg
  have hB' := hg.nonneg
  set D : E → E →L[ℝ] H := fun y => (β (f y)).comp (fderiv ℝ g y) +
    (β.comp (fderiv ℝ f y)).flip (g y)
  have hd : ∀ y, HasFDerivAt (fun y => β (f y) (g y)) (D y) y := by
    intro y
    have hc : HasFDerivAt (fun y => β (f y)) (β.comp (fderiv ℝ f y)) y :=
      β.hasFDerivAt.comp y (hf.hasFDerivAt y)
    exact hc.clm_apply (hg.hasFDerivAt y)
  have hfd : ∀ y, fderiv ℝ (fun y => β (f y) (g y)) y = D y := fun y => (hd y).fderiv
  have hβ := norm_nonneg β
  have nf : ∀ y, ‖β (f y)‖ ≤ ‖β‖ * B := fun y =>
    (β.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hf.norm_le y) hβ)
  have nfl : ∀ y, ‖(β.comp (fderiv ℝ f y)).flip‖ ≤ ‖β‖ * B := fun y => by
    rw [ContinuousLinearMap.opNorm_flip]
    exact (β.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (hf.norm_fderiv_le y) hβ)
  refine ⟨fun y => by rw [hfd]; exact hd y, fun y => ?_, fun y => ?_, fun y z => ?_⟩
  · calc ‖β (f y) (g y)‖ ≤ ‖β (f y)‖ * ‖g y‖ := (β (f y)).le_opNorm _
      _ ≤ (‖β‖ * B) * B' := mul_le_mul (nf y) (hg.norm_le y) (norm_nonneg _) (by positivity)
      _ ≤ 4 * ‖β‖ * B * B' := by nlinarith [mul_nonneg (mul_nonneg hβ hB) hB']
  · rw [hfd]
    calc ‖D y‖ ≤ ‖β (f y)‖ * ‖fderiv ℝ g y‖ + ‖(β.comp (fderiv ℝ f y)).flip‖ * ‖g y‖ :=
          (norm_add_le _ _).trans (add_le_add ((β (f y)).opNorm_comp_le _)
            (ContinuousLinearMap.le_opNorm _ _))
      _ ≤ (‖β‖ * B) * B' + (‖β‖ * B) * B' :=
          add_le_add (mul_le_mul (nf y) (hg.norm_fderiv_le y) (norm_nonneg _) (by positivity))
            (mul_le_mul (nfl y) (hg.norm_le y) (norm_nonneg _) (by positivity))
      _ ≤ 4 * ‖β‖ * B * B' := by nlinarith [mul_nonneg (mul_nonneg hβ hB) hB']
  · rw [hfd, hfd]
    have e : D y - D z = ((β (f y - f z)).comp (fderiv ℝ g y) +
        (β (f z)).comp (fderiv ℝ g y - fderiv ℝ g z)) +
        ((β.comp (fderiv ℝ f y - fderiv ℝ f z)).flip (g y) +
          (β.comp (fderiv ℝ f z)).flip (g y - g z)) := by
      ext u
      simp [D, map_sub]
      abel
    rw [e]
    have t1 : ‖(β (f y - f z)).comp (fderiv ℝ g y)‖ ≤ ‖β‖ * (B * ‖y - z‖) * B' :=
      ((β (f y - f z)).opNorm_comp_le _).trans (mul_le_mul ((β.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hf.lipschitz y z) hβ)) (hg.norm_fderiv_le y)
        (norm_nonneg _) (by positivity))
    have t2 : ‖(β (f z)).comp (fderiv ℝ g y - fderiv ℝ g z)‖ ≤ (‖β‖ * B) * (B' * ‖y - z‖) :=
      ((β (f z)).opNorm_comp_le _).trans (mul_le_mul (nf z) (hg.lip y z) (norm_nonneg _)
        (by positivity))
    have t3 : ‖(β.comp (fderiv ℝ f y - fderiv ℝ f z)).flip (g y)‖ ≤
        (‖β‖ * (B * ‖y - z‖)) * B' := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul ?_ (hg.norm_le y)
        (norm_nonneg _) (by positivity))
      rw [ContinuousLinearMap.opNorm_flip]
      exact (β.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (hf.lip y z) hβ)
    have t4 : ‖(β.comp (fderiv ℝ f z)).flip (g y - g z)‖ ≤ (‖β‖ * B) * (B' * ‖y - z‖) :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (nfl z) (hg.lipschitz y z)
        (norm_nonneg _) (by positivity))
    calc _ ≤ ‖(β (f y - f z)).comp (fderiv ℝ g y)‖ +
          ‖(β (f z)).comp (fderiv ℝ g y - fderiv ℝ g z)‖ +
          (‖(β.comp (fderiv ℝ f y - fderiv ℝ f z)).flip (g y)‖ +
            ‖(β.comp (fderiv ℝ f z)).flip (g y - g z)‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ 4 * ‖β‖ * B * B' * ‖y - z‖ := by nlinarith
end IsC11

/-! ### Maps on compact subsets of open sets -/

/-- A `C¹` map on an open set is bounded and Lipschitz on every compact subset. -/
theorem exists_C1_on_compact {Φ : F → G} {U : Set F} (hU : IsOpen U)
    (hΦ : ContDiffOn ℝ 1 Φ U) {Kc : Set F} (hKc : IsCompact Kc) (hsub : Kc ⊆ U) :
    ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧ (∀ p ∈ Kc, ‖Φ p‖ ≤ M) ∧
      ∀ p ∈ Kc, ∀ p' ∈ Kc, ‖Φ p - Φ p'‖ ≤ L * ‖p - p'‖ := by
  have hloc : LocallyLipschitzOn Kc Φ := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ := (hΦ.contDiffAt (hU.mem_nhds (hsub hx))).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact hKc
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hΦ.continuousOn.mono hsub)
  refine ⟨K, max M 0, K.2, le_max_right _ _, fun e he => (hM e he).trans (le_max_left _ _),
    fun e he e' he' => ?_⟩
  rw [← dist_eq_norm, ← dist_eq_norm]
  exact hK.dist_le_mul e he e' he'

/-- **Composition with a `C²` map, uniform constants**: for `Φ` of class `C²` on an open set
containing a compact `K_c` and a bound `B`, there is `C` such that `Φ ∘ f` is `C^{1,1}` with
constant `C` for every `f` that is `C^{1,1}` with constant `B` and takes values in `K_c`. -/
theorem exists_IsC11_comp [Nonempty E] {Φ : F → G} {U : Set F} (hU : IsOpen U)
    (hΦ : ContDiffOn ℝ 2 Φ U) {Kc : Set F} (hKc : IsCompact Kc) (hsub : Kc ⊆ U) (B : ℝ) :
    ∃ C : ℝ, ∀ f : E → F, IsC11 f B → (∀ y, f y ∈ Kc) → IsC11 (fun y => Φ (f y)) C := by
  have hΦ1 : ContDiffOn ℝ 1 (fderiv ℝ Φ) U :=
    hΦ.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨L₀, M₀, -, -, hM₀, -⟩ := exists_C1_on_compact hU (hΦ.of_le (by norm_num)) hKc hsub
  obtain ⟨L₁, M₁, hL₁, hM₁0, hM₁, hL₁'⟩ := exists_C1_on_compact hU hΦ1 hKc hsub
  refine ⟨max M₀ (max (M₁ * |B|) (L₁ * |B| * |B| + M₁ * |B|)), fun f hf hfK => ?_⟩
  have hB := hf.nonneg
  have hdiff : ∀ y, DifferentiableAt ℝ Φ (f y) := fun y =>
    (hΦ.contDiffAt (hU.mem_nhds (hsub (hfK y)))).differentiableAt (by norm_num)
  have hd : ∀ y, HasFDerivAt (fun y => Φ (f y)) ((fderiv ℝ Φ (f y)).comp (fderiv ℝ f y)) y :=
    fun y => (hdiff y).hasFDerivAt.comp y (hf.hasFDerivAt y)
  have hfd : ∀ y, fderiv ℝ (fun y => Φ (f y)) y = (fderiv ℝ Φ (f y)).comp (fderiv ℝ f y) :=
    fun y => (hd y).fderiv
  rw [abs_of_nonneg hB]
  refine ⟨fun y => by rw [hfd]; exact hd y, fun y => (hM₀ _ (hfK y)).trans (le_max_left _ _),
    fun y => ?_, fun y z => ?_⟩
  · rw [hfd]
    refine ((fderiv ℝ Φ (f y)).opNorm_comp_le _).trans ?_
    refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
    exact mul_le_mul (hM₁ _ (hfK y)) (hf.norm_fderiv_le y) (norm_nonneg _) hM₁0
  · rw [hfd, hfd]
    have e : (fderiv ℝ Φ (f y)).comp (fderiv ℝ f y) - (fderiv ℝ Φ (f z)).comp (fderiv ℝ f z) =
        (fderiv ℝ Φ (f y) - fderiv ℝ Φ (f z)).comp (fderiv ℝ f y) +
          (fderiv ℝ Φ (f z)).comp (fderiv ℝ f y - fderiv ℝ f z) := by
      ext u; simp
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have t1 : ‖(fderiv ℝ Φ (f y) - fderiv ℝ Φ (f z)).comp (fderiv ℝ f y)‖ ≤
        (L₁ * (B * ‖y - z‖)) * B :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ((hL₁' _ (hfK y) _ (hfK z)).trans
        (mul_le_mul_of_nonneg_left (hf.lipschitz y z) hL₁)) (hf.norm_fderiv_le y) (norm_nonneg _)
        (by positivity))
    have t2 : ‖(fderiv ℝ Φ (f z)).comp (fderiv ℝ f y - fderiv ℝ f z)‖ ≤ M₁ * (B * ‖y - z‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hM₁ _ (hfK z)) (hf.lip y z)
        (norm_nonneg _) hM₁0)
    have hm : L₁ * B * B + M₁ * B ≤ max M₀ (max (M₁ * B) (L₁ * B * B + M₁ * B)) :=
      (le_max_right _ _).trans (le_max_right _ _)
    calc _ ≤ (L₁ * (B * ‖y - z‖)) * B + M₁ * (B * ‖y - z‖) := add_le_add t1 t2
      _ = (L₁ * B * B + M₁ * B) * ‖y - z‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (norm_nonneg _)

/-- **Second-order Taylor remainder, uniform on a compact set**: for `Φ` of class `C²` on an open
set `U ⊇ K_c` (compact), there are `δ > 0` and `C` with `p + u ∈ U` and
`‖Φ(p + u) - Φ(p) - DΦ(p)u‖ ≤ C ‖u‖²` for all `p ∈ K_c`, `‖u‖ ≤ δ`. -/
theorem exists_taylor2_on_compact [ProperSpace F] {Φ : F → G} {U : Set F} (hU : IsOpen U)
    (hΦ : ContDiffOn ℝ 2 Φ U) {Kc : Set F} (hKc : IsCompact Kc) (hsub : Kc ⊆ U) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ p ∈ Kc, ∀ u : F, ‖u‖ ≤ δ →
      p + u ∈ cthickening δ Kc ∧ cthickening δ Kc ⊆ U ∧
      ‖Φ (p + u) - Φ p - fderiv ℝ Φ p u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨δ, hδ, hδU⟩ := hKc.exists_cthickening_subset_open hU hsub
  have hKδ : IsCompact (cthickening δ Kc) := hKc.cthickening
  have hΦ1 : ContDiffOn ℝ 1 (fderiv ℝ Φ) U := hΦ.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨L, M, hL, -, -, hL'⟩ := exists_C1_on_compact hU hΦ1 hKδ hδU
  refine ⟨δ, L, hδ, hL, fun p hp u hu => ?_⟩
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, p + s • u ∈ cthickening δ Kc := by
    intro s hs
    refine mem_cthickening_of_dist_le _ p δ Kc hp ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [hs.2, norm_nonneg u]
  have hpK : p ∈ cthickening δ Kc := self_subset_cthickening Kc hp
  refine ⟨by simpa using hseg 1 ⟨zero_le_one, le_rfl⟩, hδU, ?_⟩
  set φ : ℝ → G := fun s => Φ (p + s • u) - s • fderiv ℝ Φ p u
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (fderiv ℝ Φ (p + s • u) u - fderiv ℝ Φ p u) s := by
    intro s hs
    have hl : HasDerivAt (fun s : ℝ => p + s • u) u s := by
      simpa using ((hasDerivAt_id s).smul_const u).const_add p
    have hdiff : DifferentiableAt ℝ Φ (p + s • u) :=
      (hΦ.contDiffAt (hU.mem_nhds (hδU (hseg s hs)))).differentiableAt (by norm_num)
    have h2 := hdiff.hasFDerivAt.comp_hasDerivAt s hl
    have h3 : HasDerivAt (fun s : ℝ => s • fderiv ℝ Φ p u) (fderiv ℝ Φ p u) s := by
      simpa using (hasDerivAt_id s).smul_const (fderiv ℝ Φ p u)
    exact h2.sub h3
  have hb := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) (a := 0) (b := 1)
    (C := L * ‖u‖ ^ 2) (fun s hs => (hd s hs).hasDerivWithinAt) (fun s hs => ?_) 1
    ⟨zero_le_one, le_rfl⟩
  · have e : φ 1 - φ 0 = Φ (p + u) - Φ p - fderiv ℝ Φ p u := by
      simp only [φ, one_smul, zero_smul, add_zero, sub_zero]
      abel
    rw [e] at hb
    simpa using hb
  · rw [← ContinuousLinearMap.sub_apply]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have h1 := hL' _ (hseg s (Ico_subset_Icc_self hs)) _ hpK
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] at h1
    have hs1 : s ≤ 1 := hs.2.le
    calc ‖fderiv ℝ Φ (p + s • u) - fderiv ℝ Φ p‖ * ‖u‖ ≤ L * (s * ‖u‖) * ‖u‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ L * (1 * ‖u‖) * ‖u‖ := by gcongr
      _ = L * ‖u‖ ^ 2 := by ring


/-! ### Families `Φ(p + t q)` of a `C²` map along `C^{0,1}` data -/

section Family

/-- **Uniform data of a `C²` map near a compact subset of an open set**: a margin `δ` (inside the
open set), bounds of `Φ` on the `δ`-thickening, of `DΦ` on the compact set, Lipschitz constants of
`Φ` and `DΦ` on the compact set, and a uniform second-order Taylor constant. -/
structure ChartData (Φ : F → G) (Kc : Set F) (δ M₀ M₁ L₀ L₁ Cq : ℝ) : Prop where
  δ_pos : 0 < δ
  M₀_nonneg : 0 ≤ M₀
  M₁_nonneg : 0 ≤ M₁
  L₀_nonneg : 0 ≤ L₀
  L₁_nonneg : 0 ≤ L₁
  Cq_nonneg : 0 ≤ Cq
  bound : ∀ p ∈ Kc, ∀ u : F, ‖u‖ ≤ δ → ‖Φ (p + u)‖ ≤ M₀
  dbound : ∀ p ∈ Kc, ‖fderiv ℝ Φ p‖ ≤ M₁
  lip : ∀ p ∈ Kc, ∀ p' ∈ Kc, ‖Φ p - Φ p'‖ ≤ L₀ * ‖p - p'‖
  dlip : ∀ p ∈ Kc, ∀ p' ∈ Kc, ‖fderiv ℝ Φ p - fderiv ℝ Φ p'‖ ≤ L₁ * ‖p - p'‖
  taylor : ∀ p ∈ Kc, ∀ u : F, ‖u‖ ≤ δ → ‖Φ (p + u) - Φ p - fderiv ℝ Φ p u‖ ≤ Cq * ‖u‖ ^ 2
  diffAt : ∀ p ∈ Kc, ∀ u : F, ‖u‖ ≤ δ → DifferentiableAt ℝ Φ (p + u)
  contAt : ∀ p ∈ Kc, ∀ u : F, ‖u‖ < δ → ContinuousAt Φ (p + u)

theorem exists_chartData [ProperSpace F] {Φ : F → G} {U : Set F} (hU : IsOpen U)
    (hΦ : ContDiffOn ℝ 2 Φ U) {Kc : Set F} (hKc : IsCompact Kc) (hsub : Kc ⊆ U) :
    ∃ δ M₀ M₁ L₀ L₁ Cq : ℝ, ChartData Φ Kc δ M₀ M₁ L₀ L₁ Cq := by
  obtain ⟨δ, Cq, hδ, hCq, hT⟩ := exists_taylor2_on_compact hU hΦ hKc hsub
  obtain ⟨δ', hδ', hδ'U⟩ := hKc.exists_cthickening_subset_open hU hsub
  set δ₀ := min δ δ'
  have hδ₀ : 0 < δ₀ := lt_min hδ hδ'
  have hsubU : cthickening δ₀ Kc ⊆ U := (cthickening_mono (min_le_right _ _) Kc).trans hδ'U
  have hKδ₀ : IsCompact (cthickening δ₀ Kc) := hKc.cthickening
  obtain ⟨-, M₀, -, hM₀, hM₀', -⟩ := exists_C1_on_compact hU (hΦ.of_le (by norm_num)) hKδ₀ hsubU
  have hΦ1 : ContDiffOn ℝ 1 (fderiv ℝ Φ) U := hΦ.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨L₁, M₁, hL₁, hM₁, hM₁', hL₁'⟩ := exists_C1_on_compact hU hΦ1 hKc hsub
  obtain ⟨L₀, -, hL₀, -, -, hL₀'⟩ := exists_C1_on_compact hU (hΦ.of_le (by norm_num)) hKc hsub
  have hmem : ∀ p ∈ Kc, ∀ u : F, ‖u‖ ≤ δ₀ → p + u ∈ cthickening δ₀ Kc := by
    intro p hp u hu
    refine mem_cthickening_of_dist_le _ p δ₀ Kc hp ?_
    rw [dist_eq_norm, add_sub_cancel_left]; exact hu
  refine ⟨δ₀, M₀, M₁, L₀, L₁, Cq, ⟨hδ₀, hM₀, hM₁, hL₀, hL₁, hCq, fun p hp u hu =>
    hM₀' _ (hmem p hp u hu), hM₁', hL₀', hL₁', fun p hp u hu =>
    (hT p hp u (hu.trans (min_le_left _ _))).2.2, fun p hp u hu => ?_, fun p hp u hu => ?_⟩⟩
  · exact (hΦ.contDiffAt (hU.mem_nhds (hsubU (hmem p hp u hu)))).differentiableAt (by norm_num)
  · exact (hΦ.contDiffAt (hU.mem_nhds (hsubU (hmem p hp u hu.le)))).continuousAt

end Family

end RenewalGeometry.C11Calculus
