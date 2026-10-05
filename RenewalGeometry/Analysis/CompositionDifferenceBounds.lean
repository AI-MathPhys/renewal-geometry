/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Faà di Bruno bounds for compositions and for differences of compositions

Generic infrastructure (no renewal notions) for the source-tail transfer of the
Einstein–Standard-Model action-closure manuscript (`lem:native-tail-transfer`,
`eq:native-source-tail`: "differentiate the difference `k` times; every product contains at least
one tail factor and at most `k + 2` total field derivatives").

Let `G : X → F` be `C^{N+1}` on an open set `U`, with `‖D^kG‖ ≤ M` (`k ≤ N + 1`) on a convex
`C ⊆ U`, and let `J₀, J₁ : E → X` be `C^N` at `z`, with values in `C` at `z`.  Through Mathlib's
Faà di Bruno formula (`iteratedFDeriv_comp`, `FormalMultilinearSeries.taylorComp`) and the
difference estimate for compositions along ordered finpartitions:

* **`norm_iteratedFDeriv_comp_le_local`**: if `‖D^pJ(z)‖ ≤ B` (`1 ≤ p ≤ N`, `B ≥ 1`) then
  `‖D^N(G ∘ J)(z)‖ ≤ #OFP(N) · M · B^N`;
* **`norm_iteratedFDeriv_comp_sub_le`**: if moreover `‖J₁(z) - J₀(z)‖ ≤ η` and
  `‖D^pJ₁(z) - D^pJ₀(z)‖ ≤ η` (`1 ≤ p ≤ N`), then
  `‖D^N(G ∘ J₁)(z) - D^N(G ∘ J₀)(z)‖ ≤ #OFP(N) · (N + 1) · M · B^N · η`.

Only derivatives of `J₁ - J₀` up to the order `N` enter (no derivative is lost to a
mean-value argument), which is the derivative count of the manuscript.  `#OFP(N)` is the number of
ordered finpartitions of `Fin N`.
-/

open Set

namespace RenewalGeometry.CompDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `N`-th derivative of a composition as the Faà di Bruno sum over ordered finpartitions. -/
theorem iteratedFDeriv_comp_eq_sum {G : X → F} {J : E → X} {z : E} {N : ℕ}
    (hG : ContDiffAt ℝ N G (J z)) (hJ : ContDiffAt ℝ N J z) :
    iteratedFDeriv ℝ N (G ∘ J) z =
      ∑ c : OrderedFinpartition N, c.compAlongOrderedFinpartition
        (iteratedFDeriv ℝ c.length G (J z)) (fun m => iteratedFDeriv ℝ (c.partSize m) J z) := by
  rw [iteratedFDeriv_comp hG hJ le_rfl]
  rfl

theorem norm_pi_iteratedFDeriv_le {J : E → X} {z : E} {N : ℕ} (c : OrderedFinpartition N)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ p, 1 ≤ p → p ≤ N → ‖iteratedFDeriv ℝ p J z‖ ≤ B) :
    ‖(fun m => iteratedFDeriv ℝ (c.partSize m) J z)‖ ≤ B :=
  (pi_norm_le_iff_of_nonneg hB0).mpr fun m =>
    hB _ (c.partSize_pos m) (c.partSize_le m)

/-- **Local Faà di Bruno bound**: `‖D^N(G ∘ J)(z)‖ ≤ #OFP(N) · M · B^N`. -/
theorem norm_iteratedFDeriv_comp_le_local {G : X → F} {J : E → X} {z : E} {N : ℕ}
    (hG : ContDiffAt ℝ N G (J z)) (hJ : ContDiffAt ℝ N J z) {M B : ℝ} (hB1 : 1 ≤ B)
    (hM : ∀ k ≤ N, ‖iteratedFDeriv ℝ k G (J z)‖ ≤ M)
    (hB : ∀ p, 1 ≤ p → p ≤ N → ‖iteratedFDeriv ℝ p J z‖ ≤ B) :
    ‖iteratedFDeriv ℝ N (G ∘ J) z‖ ≤ Fintype.card (OrderedFinpartition N) * M * B ^ N := by
  have hB0 : 0 ≤ B := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _))
  rw [iteratedFDeriv_comp_eq_sum hG hJ]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ c : OrderedFinpartition N, ‖c.compAlongOrderedFinpartition
      (iteratedFDeriv ℝ c.length G (J z)) (fun m => iteratedFDeriv ℝ (c.partSize m) J z)‖ ≤
        M * B ^ N := by
    intro c
    refine (c.norm_compAlongOrderedFinpartition_le _ _).trans ?_
    gcongr
    · exact hM _ c.length_le
    · calc ∏ m, ‖iteratedFDeriv ℝ (c.partSize m) J z‖ ≤ ∏ _m : Fin c.length, B :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              (fun m _ => hB _ (c.partSize_pos m) (c.partSize_le m))
        _ = B ^ c.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ B ^ N := pow_le_pow_right₀ hB1 c.length_le
  calc ∑ c : OrderedFinpartition N, ‖c.compAlongOrderedFinpartition
        (iteratedFDeriv ℝ c.length G (J z)) (fun m => iteratedFDeriv ℝ (c.partSize m) J z)‖
      ≤ ∑ _c : OrderedFinpartition N, M * B ^ N := Finset.sum_le_sum fun c _ => hterm c
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Mean-value bound for the iterated derivatives of `G` on a convex set. -/
theorem norm_iteratedFDeriv_sub_le_of_convex {G : X → F} {U C : Set X} (hU : IsOpen U) {N : ℕ}
    (hG : ContDiffOn ℝ (N + 1) G U) (hCU : C ⊆ U) (hC : Convex ℝ C) {M : ℝ}
    (hM : ∀ y ∈ C, ‖iteratedFDeriv ℝ (N + 1) G y‖ ≤ M) {a b : X} (ha : a ∈ C) (hb : b ∈ C) :
    ‖iteratedFDeriv ℝ N G b - iteratedFDeriv ℝ N G a‖ ≤ M * ‖b - a‖ := by
  refine hC.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun y hy => ?_) (fun y hy => ?_) ha hb
  · exact ((hG.contDiffAt (hU.mem_nhds (hCU hy))).differentiableAt_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self N))
  · rw [norm_fderiv_iteratedFDeriv]; exact hM y hy

/-- **Faà di Bruno difference bound**:
`‖D^N(G ∘ J₁)(z) - D^N(G ∘ J₀)(z)‖ ≤ #OFP(N) · (N + 1) · M · B^N · η`. -/
theorem norm_iteratedFDeriv_comp_sub_le {G : X → F} {U C : Set X} (hU : IsOpen U) {N : ℕ}
    (hG : ContDiffOn ℝ (N + 1) G U) (hCU : C ⊆ U) (hC : Convex ℝ C) {M : ℝ}
    (hM : ∀ y ∈ C, ∀ k ≤ N + 1, ‖iteratedFDeriv ℝ k G y‖ ≤ M)
    {J₀ J₁ : E → X} {z : E} (h0 : ContDiffAt ℝ N J₀ z) (h1 : ContDiffAt ℝ N J₁ z)
    (hz0 : J₀ z ∈ C) (hz1 : J₁ z ∈ C) {B η : ℝ} (hB1 : 1 ≤ B)
    (hB : ∀ p, 1 ≤ p → p ≤ N → ‖iteratedFDeriv ℝ p J₀ z‖ ≤ B ∧ ‖iteratedFDeriv ℝ p J₁ z‖ ≤ B)
    (hη0 : ‖J₁ z - J₀ z‖ ≤ η)
    (hη : ∀ p, 1 ≤ p → p ≤ N → ‖iteratedFDeriv ℝ p J₁ z - iteratedFDeriv ℝ p J₀ z‖ ≤ η) :
    ‖iteratedFDeriv ℝ N (G ∘ J₁) z - iteratedFDeriv ℝ N (G ∘ J₀) z‖ ≤
      Fintype.card (OrderedFinpartition N) * ((N + 1) * M * B ^ N) * η := by
  have hB0 : 0 ≤ B := by linarith
  have hη00 : 0 ≤ η := (norm_nonneg _).trans hη0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ hz0 0 (Nat.zero_le _))
  have hGa : ∀ y ∈ C, ContDiffAt ℝ N G y := fun y hy =>
    ((hG.contDiffAt (hU.mem_nhds (hCU hy))).of_le (by exact_mod_cast Nat.le_succ N))
  rw [iteratedFDeriv_comp_eq_sum (hGa _ hz1) h1, iteratedFDeriv_comp_eq_sum (hGa _ hz0) h0,
    ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ c : OrderedFinpartition N,
      ‖c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length G (J₁ z))
          (fun m => iteratedFDeriv ℝ (c.partSize m) J₁ z) -
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length G (J₀ z))
          (fun m => iteratedFDeriv ℝ (c.partSize m) J₀ z)‖ ≤ (N + 1) * M * B ^ N * η := by
    intro c
    refine (c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le _ _ _ _).trans ?_
    have hf1 : ‖iteratedFDeriv ℝ c.length G (J₁ z)‖ ≤ M :=
      hM _ hz1 _ (c.length_le.trans (Nat.le_succ N))
    have hg1 := norm_pi_iteratedFDeriv_le (J := J₁) c hB0 fun p hp hpN => (hB p hp hpN).2
    have hg0 := norm_pi_iteratedFDeriv_le (J := J₀) c hB0 fun p hp hpN => (hB p hp hpN).1
    have hmax : max ‖(fun m => iteratedFDeriv ℝ (c.partSize m) J₁ z)‖
        ‖(fun m => iteratedFDeriv ℝ (c.partSize m) J₀ z)‖ ≤ B := max_le hg1 hg0
    have hgd : ‖(fun m => iteratedFDeriv ℝ (c.partSize m) J₁ z) -
        (fun m => iteratedFDeriv ℝ (c.partSize m) J₀ z)‖ ≤ η :=
      (pi_norm_le_iff_of_nonneg hη00).mpr fun m => by
        simpa using hη _ (c.partSize_pos m) (c.partSize_le m)
    have hfd : ‖iteratedFDeriv ℝ c.length G (J₁ z) - iteratedFDeriv ℝ c.length G (J₀ z)‖ ≤
        M * η := by
      have hle : c.length + 1 ≤ N + 1 := Nat.succ_le_succ c.length_le
      have := norm_iteratedFDeriv_sub_le_of_convex hU
        (hG.of_le (by exact_mod_cast hle)) hCU hC
        (fun y hy => hM y hy _ hle) hz0 hz1
      exact this.trans (mul_le_mul_of_nonneg_left hη0 hM0)
    have hprod : ∏ m, ‖iteratedFDeriv ℝ (c.partSize m) J₀ z‖ ≤ B ^ N := by
      calc ∏ m, ‖iteratedFDeriv ℝ (c.partSize m) J₀ z‖ ≤ ∏ _m : Fin c.length, B :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              (fun m _ => (hB _ (c.partSize_pos m) (c.partSize_le m)).1)
        _ = B ^ c.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ B ^ N := pow_le_pow_right₀ hB1 c.length_le
    have hpow : max ‖(fun m => iteratedFDeriv ℝ (c.partSize m) J₁ z)‖
        ‖(fun m => iteratedFDeriv ℝ (c.partSize m) J₀ z)‖ ^ (c.length - 1) ≤ B ^ N :=
      (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _)) hmax _).trans
        (pow_le_pow_right₀ hB1 (by have := c.length_le; omega))
    have hlen : (c.length : ℝ) ≤ N := by exact_mod_cast c.length_le
    calc ‖iteratedFDeriv ℝ c.length G (J₁ z)‖ * c.length *
          max ‖(fun m => iteratedFDeriv ℝ (c.partSize m) J₁ z)‖
            ‖(fun m => iteratedFDeriv ℝ (c.partSize m) J₀ z)‖ ^ (c.length - 1) *
          ‖(fun m => iteratedFDeriv ℝ (c.partSize m) J₁ z) -
            (fun m => iteratedFDeriv ℝ (c.partSize m) J₀ z)‖ +
        ‖iteratedFDeriv ℝ c.length G (J₁ z) - iteratedFDeriv ℝ c.length G (J₀ z)‖ *
          ∏ m, ‖iteratedFDeriv ℝ (c.partSize m) J₀ z‖
        ≤ M * N * B ^ N * η + M * η * B ^ N := by
          gcongr
      _ = (N + 1) * M * B ^ N * η := by ring
  calc ∑ c : OrderedFinpartition N, ‖c.compAlongOrderedFinpartition
        (iteratedFDeriv ℝ c.length G (J₁ z)) (fun m => iteratedFDeriv ℝ (c.partSize m) J₁ z) -
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length G (J₀ z))
          (fun m => iteratedFDeriv ℝ (c.partSize m) J₀ z)‖
      ≤ ∑ _c : OrderedFinpartition N, (N + 1) * M * B ^ N * η :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end

end RenewalGeometry.CompDiff
