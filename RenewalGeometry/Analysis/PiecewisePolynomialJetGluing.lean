/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TwoPointHermiteInterpolation

/-!
# Gluing polynomial segments with shared endpoint jets

Infrastructure for the chronological words of `lem:supp-law-cost-control` (emergent-spacetime
manuscript): a word is a finite sequence of polynomial segments `Q_j` (letters) on consecutive
cells `[t_j, t_{j+1}]` with *shared endpoint value, velocity, acceleration and jerk*.  We show that
the glued path is `C^m` (two-sided derivatives everywhere) when the endpoint jets agree through
order `m`.

Let `E` be a real normed space, `t : ℕ → ℝ` strictly increasing nodes, `J ≥ 1` cells and letters
`c j : Fin (d + 1) → E` (letter `j` is `σ ↦ ∑ᵢ (σ - t_j)ⁱ • c j i`, extended polynomially
before `t_1` and after `t_{J-1}`).

* `cellIdx`: the cell containing a time (`Nat.findGreatest`);
* `splinePath t J c k`: the `k`-th derivative of the letter of the current cell, at local time;
* `JetsMatch t J c m`: shared endpoint jets through order `m` at the interior nodes;
* `hasDerivAt_splinePath`: for `k + 1 ≤ m`, `splinePath k` has derivative `splinePath (k + 1)`
  at every time (two-sided, including the nodes);
* `continuous_splinePath`: for `k ≤ m`, `splinePath k` is continuous.
-/

open Set Filter Topology

namespace RenewalGeometry.SplineGluing

open TwoPointHermite

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

/-- The cell of a time: the largest `j ≤ J - 1` with `t_j ≤ τ` (and `0` if there is none). -/
def cellIdx (t : ℕ → ℝ) (J : ℕ) (τ : ℝ) : ℕ := Nat.findGreatest (fun j => t j ≤ τ) (J - 1)

/-- The `k`-th derivative of the glued word: the `k`-th derivative of the letter of the current
cell at the local time `τ - t_j`. -/
def splinePath {d : ℕ} (t : ℕ → ℝ) (J : ℕ) (c : ℕ → Fin (d + 1) → E) (k : ℕ) (τ : ℝ) : E :=
  polyCurveDeriv k (c (cellIdx t J τ)) (τ - t (cellIdx t J τ))

/-- **Shared endpoint jets through order `m`** at every interior node `t_{j+1}`, `j + 1 < J`:
`Q_j^{(k)}(t_{j+1}) = Q_{j+1}^{(k)}(t_{j+1})` for `k ≤ m`. -/
def JetsMatch {d : ℕ} (t : ℕ → ℝ) (J : ℕ) (c : ℕ → Fin (d + 1) → E) (m : ℕ) : Prop :=
  ∀ j, j + 1 < J → ∀ k ≤ m, polyCurveDeriv k (c j) (t (j + 1) - t j) = polyCurveDeriv k (c (j + 1)) 0

theorem cellIdx_le (t : ℕ → ℝ) (J : ℕ) (τ : ℝ) : cellIdx t J τ ≤ J - 1 :=
  Nat.findGreatest_le _

theorem cellIdx_spec {t : ℕ → ℝ} {J : ℕ} {τ : ℝ} (h : cellIdx t J τ ≠ 0) :
    t (cellIdx t J τ) ≤ τ :=
  Nat.findGreatest_of_ne_zero rfl h

/-- Characterization of the cell index. -/
theorem cellIdx_eq {t : ℕ → ℝ} (ht : StrictMono t) {J j : ℕ} {τ : ℝ} (hj : j ≤ J - 1)
    (h1 : j ≠ 0 → t j ≤ τ) (h2 : j + 1 ≤ J - 1 → τ < t (j + 1)) : cellIdx t J τ = j := by
  unfold cellIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨hj, h1, fun n hn hnJ => ?_⟩
  have h3 : τ < t (j + 1) := h2 (by omega)
  have h4 : t (j + 1) ≤ t n := ht.monotone (by omega)
  simp only [not_le]
  linarith

theorem lt_of_cellIdx {t : ℕ → ℝ} {J : ℕ} {τ : ℝ}
    (h : cellIdx t J τ + 1 ≤ J - 1) : τ < t (cellIdx t J τ + 1) := by
  by_contra hcon
  push Not at hcon
  have h' : cellIdx t J τ + 1 ≤ cellIdx t J τ := Nat.le_findGreatest (P := fun j => t j ≤ τ) h hcon
  omega

/-- The letter `j` and its derivatives in global time. -/
theorem hasDerivAt_letter {d : ℕ} (c : Fin (d + 1) → E) (a : ℝ) (k : ℕ) (σ : ℝ) :
    HasDerivAt (fun τ => polyCurveDeriv k c (τ - a)) (polyCurveDeriv (k + 1) c (σ - a)) σ := by
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 σ := (hasDerivAt_id' σ).sub_const a
  have h := (hasDerivAt_polyCurveDeriv k c (σ - a)).scomp σ h1
  simpa [Function.comp_def] using h

/-- On the right of every time, the path coincides with the letter of the current cell. -/
theorem eventually_right {d : ℕ} {t : ℕ → ℝ} (ht : StrictMono t) {J : ℕ}
    (c : ℕ → Fin (d + 1) → E) (k : ℕ) (τ : ℝ) :
    ∀ᶠ σ in 𝓝[≥] τ, splinePath t J c k σ =
      polyCurveDeriv k (c (cellIdx t J τ)) (σ - t (cellIdx t J τ)) := by
  set j := cellIdx t J τ
  have hcell : ∀ σ, τ ≤ σ → (j + 1 ≤ J - 1 → σ < t (j + 1)) → cellIdx t J σ = j := by
    intro σ hσ h2
    refine cellIdx_eq ht (cellIdx_le t J τ) (fun hj => (cellIdx_spec hj).trans hσ) h2
  by_cases hJ : j + 1 ≤ J - 1
  · have hlt := lt_of_cellIdx hJ
    filter_upwards [Ico_mem_nhdsGE hlt] with σ hσ
    simp only [splinePath, hcell σ hσ.1 fun _ => hσ.2]
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [splinePath, hcell σ hσ fun h => absurd h hJ]

/-- On the left of a time which is not an interior node, the path coincides with the letter of
the current cell. -/
theorem eventually_left_of_ne {d : ℕ} {t : ℕ → ℝ} (ht : StrictMono t) {J : ℕ}
    (c : ℕ → Fin (d + 1) → E) (k : ℕ) {τ : ℝ}
    (hτ : cellIdx t J τ = 0 ∨ t (cellIdx t J τ) < τ) :
    ∀ᶠ σ in 𝓝[≤] τ, splinePath t J c k σ =
      polyCurveDeriv k (c (cellIdx t J τ)) (σ - t (cellIdx t J τ)) := by
  set j := cellIdx t J τ
  have hcell : ∀ σ, σ ≤ τ → (j ≠ 0 → t j ≤ σ) → cellIdx t J σ = j := by
    intro σ hσ h1
    refine cellIdx_eq ht (cellIdx_le t J τ) h1 fun h2 => lt_of_le_of_lt hσ ?_
    exact lt_of_cellIdx h2
  rcases hτ with h0 | hlt
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [splinePath, hcell σ hσ fun h => absurd h0 h]
  · filter_upwards [Ioc_mem_nhdsLE hlt] with σ hσ
    simp only [splinePath, hcell σ hσ.2 fun _ => hσ.1.le]

/-- At an interior node `τ = t_j`, `1 ≤ j`, the path coincides on the left with the previous
letter (the value at the node by the shared jets). -/
theorem eventually_left_of_node {d : ℕ} {t : ℕ → ℝ} (ht : StrictMono t) {J m : ℕ}
    {c : ℕ → Fin (d + 1) → E} (hm : JetsMatch t J c m) {k : ℕ} (hk : k ≤ m) {τ : ℝ}
    (hj0 : cellIdx t J τ ≠ 0) (hτ : t (cellIdx t J τ) = τ) :
    ∀ᶠ σ in 𝓝[≤] τ, splinePath t J c k σ =
      polyCurveDeriv k (c (cellIdx t J τ - 1)) (σ - t (cellIdx t J τ - 1)) := by
  set j := cellIdx t J τ
  have hjJ : j ≤ J - 1 := cellIdx_le t J τ
  have hlt : t (j - 1) < τ := by rw [← hτ]; exact ht (by omega)
  filter_upwards [Ioc_mem_nhdsLE hlt] with σ hσ
  rcases hσ.2.lt_or_eq with h | h
  · have hc : cellIdx t J σ = j - 1 := by
      refine cellIdx_eq ht (by omega) (fun _ => hσ.1.le) fun _ => ?_
      rw [show j - 1 + 1 = j by omega, hτ]; exact h
    simp only [splinePath, hc]
  · rw [h]
    show polyCurveDeriv k (c j) (τ - t j) = _
    have hmatch := hm (j - 1) (by omega) k hk
    rw [show j - 1 + 1 = j by omega] at hmatch
    have e1 : τ - t j = 0 := by rw [hτ, sub_self]
    have e2 : τ - t (j - 1) = t j - t (j - 1) := by rw [hτ]
    rw [e1, e2, hmatch]

/-- **The glued word is `C^m`**: if the endpoint jets agree through order `m` and `k + 1 ≤ m`,
then `splinePath k` has (two-sided) derivative `splinePath (k + 1)` at every time. -/
theorem hasDerivAt_splinePath {d : ℕ} {t : ℕ → ℝ} (ht : StrictMono t) {J m : ℕ}
    {c : ℕ → Fin (d + 1) → E} (hm : JetsMatch t J c m) {k : ℕ} (hk : k + 1 ≤ m) (τ : ℝ) :
    HasDerivAt (splinePath t J c k) (splinePath t J c (k + 1) τ) τ := by
  set j := cellIdx t J τ
  have hval : ∀ k', splinePath t J c k' τ = polyCurveDeriv k' (c j) (τ - t j) := fun _ => rfl
  -- the right derivative
  have hR : HasDerivWithinAt (splinePath t J c k) (splinePath t J c (k + 1) τ) (Ici τ) τ := by
    rw [hval]
    exact (hasDerivAt_letter (c j) (t j) k τ).hasDerivWithinAt.congr_of_eventuallyEq
      (eventually_right ht c k τ) (hval k)
  -- the left derivative
  have hL : HasDerivWithinAt (splinePath t J c k) (splinePath t J c (k + 1) τ) (Iic τ) τ := by
    by_cases hnode : j ≠ 0 ∧ t j = τ
    · have hev := eventually_left_of_node (k := k) ht hm (by omega) hnode.1 hnode.2
      have hv : splinePath t J c k τ =
          polyCurveDeriv k (c (j - 1)) (τ - t (j - 1)) := hev.self_of_nhdsWithin (le_refl τ : τ ∈ Iic τ)
      have hjJ : j ≤ J - 1 := cellIdx_le t J τ
      have hmatch := hm (j - 1) (by omega) (k + 1) hk
      rw [show j - 1 + 1 = j by omega, hnode.2] at hmatch
      have hd : splinePath t J c (k + 1) τ =
          polyCurveDeriv (k + 1) (c (j - 1)) (τ - t (j - 1)) := by
        rw [hval, hmatch, ← hnode.2, sub_self]
      rw [hd]
      exact (hasDerivAt_letter (c (j - 1)) (t (j - 1)) k τ).hasDerivWithinAt.congr_of_eventuallyEq
        hev hv
    · have hτ : j = 0 ∨ t j < τ := by
        by_cases h0 : j = 0
        · exact Or.inl h0
        · right
          have h1 : t j ≤ τ := cellIdx_spec h0
          rcases h1.lt_or_eq with h | h
          · exact h
          · exact absurd ⟨h0, h⟩ hnode
      rw [hval]
      exact (hasDerivAt_letter (c j) (t j) k τ).hasDerivWithinAt.congr_of_eventuallyEq
        (eventually_left_of_ne ht c k hτ) (hval k)
  have h := hL.union hR
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h

/-- **The top derivative of the glued word is continuous**: for `k ≤ m`, `splinePath k` is
continuous. -/
theorem continuous_splinePath {d : ℕ} {t : ℕ → ℝ} (ht : StrictMono t) {J m : ℕ}
    {c : ℕ → Fin (d + 1) → E} (hm : JetsMatch t J c m) {k : ℕ} (hk : k ≤ m) :
    Continuous (splinePath t J c k) := by
  refine continuous_iff_continuousAt.2 fun τ => ?_
  set j := cellIdx t J τ
  have hval : splinePath t J c k τ = polyCurveDeriv k (c j) (τ - t j) := rfl
  have hcont : ∀ (c' : Fin (d + 1) → E) (a : ℝ),
      Continuous fun σ => polyCurveDeriv k c' (σ - a) := fun c' a => by
    unfold polyCurveDeriv; fun_prop
  have hR : ContinuousWithinAt (splinePath t J c k) (Ici τ) τ := by
    refine ((hcont (c j) (t j)).continuousAt.continuousWithinAt).congr_of_eventuallyEq
      (eventually_right ht c k τ) hval
  have hL : ContinuousWithinAt (splinePath t J c k) (Iic τ) τ := by
    by_cases hnode : j ≠ 0 ∧ t j = τ
    · have hev := eventually_left_of_node ht hm hk hnode.1 hnode.2
      exact ((hcont (c (j - 1)) (t (j - 1))).continuousAt.continuousWithinAt).congr_of_eventuallyEq
        hev (hev.self_of_nhdsWithin (le_refl τ : τ ∈ Iic τ))
    · have hτ : j = 0 ∨ t j < τ := by
        by_cases h0 : j = 0
        · exact Or.inl h0
        · right
          have h1 : t j ≤ τ := cellIdx_spec h0
          rcases h1.lt_or_eq with h | h
          · exact h
          · exact absurd ⟨h0, h⟩ hnode
      exact ((hcont (c j) (t j)).continuousAt.continuousWithinAt).congr_of_eventuallyEq
        (eventually_left_of_ne ht c k hτ) hval
  exact continuousAt_iff_continuous_left_right.2 ⟨hL, hR⟩

end

end RenewalGeometry.SplineGluing
