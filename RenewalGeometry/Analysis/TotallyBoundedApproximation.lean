/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Total boundedness by approximation and by finitely many components

Two elementary criteria used by the compactness files `Analysis/BochnerTimeCompactness.lean`
and `Analysis/KolmogorovRieszTorus.lean` (the `ε`-net arguments of `prop:time-compactness`,
`lem:native-discrete-KR` and `thm:native-Wilson-compactness` of the Einstein–SM action-closure
manuscript).

* `totallyBounded_of_forall_approx`: a set that lies, for every `ε > 0`, within `ε` of a
  totally bounded set is totally bounded.
* `totallyBounded_of_components`: in a normed space `X`, if `x = Σ_j L_j (P_j x)` for finitely
  many bounded linear maps `P_j : X → Z_j`, `L_j : Z_j → X`, and every component set `P_j '' s`
  is totally bounded, then `s` is totally bounded (used for vector-valued fibres, component by
  component in a basis).
* `totallyBounded_inter_closedBall_of_finiteDimensional`: a bounded subset of a
  finite-dimensional subspace of a normed space over `ℝ` or `ℂ` is totally bounded.
-/

open Set Metric Filter Topology

namespace RenewalGeometry

/-- **Approximation criterion.**  If for every `ε > 0` every point of `s` lies within `ε` of a
totally bounded set `t ε`, then `s` is totally bounded. -/
theorem totallyBounded_of_forall_approx {X : Type*} [PseudoMetricSpace X] {s : Set X}
    (h : ∀ ε > 0, ∃ t : Set X, TotallyBounded t ∧ ∀ x ∈ s, ∃ y ∈ t, dist x y < ε) :
    TotallyBounded s := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨t, ht, hst⟩ := h (ε / 2) (by positivity)
  obtain ⟨u, hu, htu⟩ := Metric.totallyBounded_iff.mp ht (ε / 2) (by positivity)
  refine ⟨u, hu, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hst x hx
  have := htu hy
  simp only [mem_iUnion, Metric.mem_ball] at this ⊢
  obtain ⟨z, hz, hyz⟩ := this
  exact ⟨z, hz, by linarith [dist_triangle x y z]⟩

/-- **Component criterion.**  Let `X` be a seminormed group, `P_j : X → Z_j` and
`L_j : Z_j → X` (`j` in a finite type) additive maps with `L_j` Lipschitz (`‖L_j z‖ ≤ K ‖z‖`
on differences) and `x = Σ_j L_j (P_j x)` on `s`.  If every component set `P_j '' s` is totally
bounded, so is `s`. -/
theorem totallyBounded_of_components {X : Type*} [SeminormedAddCommGroup X] {J : Type*}
    [Fintype J] {Z : J → Type*} [∀ j, SeminormedAddCommGroup (Z j)]
    (P : ∀ j, X → Z j) (L : ∀ j, Z j →+ X) {K : ℝ} (hK : 0 ≤ K)
    (hL : ∀ j z, ‖L j z‖ ≤ K * ‖z‖) {s : Set X}
    (hrec : ∀ x ∈ s, x = ∑ j, L j (P j x)) (hs : ∀ j, TotallyBounded (P j '' s)) :
    TotallyBounded s := by
  classical
  apply totallyBounded_of_forall_approx
  intro ε hε
  set η : ℝ := ε / ((Fintype.card J + 1) * (K + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hnet : ∀ j, ∃ u : Set (Z j), u.Finite ∧ P j '' s ⊆ ⋃ y ∈ u, ball y η := fun j =>
    Metric.totallyBounded_iff.mp (hs j) η hη0
  choose u hu hcov using hnet
  refine ⟨(fun z : ∀ j, Z j => ∑ j, L j (z j)) '' (Set.pi univ u),
    ((Set.Finite.pi hu).image _).totallyBounded, fun x hx => ?_⟩
  have hpick : ∀ j, ∃ z ∈ u j, dist (P j x) z < η := by
    intro j
    have := hcov j ⟨x, hx, rfl⟩
    simp only [mem_iUnion, Metric.mem_ball] at this
    obtain ⟨z, hz, hd⟩ := this
    exact ⟨z, hz, hd⟩
  choose z hzu hzd using hpick
  refine ⟨∑ j, L j (z j), ⟨z, fun j _ => hzu j, rfl⟩, ?_⟩
  rw [dist_eq_norm, hrec x hx, ← Finset.sum_sub_distrib]
  calc ‖∑ j, (L j (P j x) - L j (z j))‖ ≤ ∑ j, ‖L j (P j x) - L j (z j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : J, K * η := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← map_sub]
        refine (hL j _).trans ?_
        have := hzd j
        rw [dist_eq_norm] at this
        exact mul_le_mul_of_nonneg_left this.le hK
    _ = Fintype.card J * K * η := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ < ε := by
        rw [hη]
        have hc : (0 : ℝ) ≤ Fintype.card J := by positivity
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg hc hK]

/-- A ball of a finite-dimensional subspace of a normed space over `𝕜 = ℝ, ℂ` is totally
bounded. -/
theorem totallyBounded_inter_closedBall_of_finiteDimensional {𝕜 : Type*} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] (W : Submodule 𝕜 X)
    [FiniteDimensional 𝕜 W] (r : ℝ) : TotallyBounded ((W : Set X) ∩ closedBall 0 r) := by
  have : ProperSpace W := FiniteDimensional.proper_rclike 𝕜 W
  have hc : IsCompact ((Subtype.val : W → X) '' closedBall (0 : W) r) :=
    (isCompact_closedBall (0 : W) r).image continuous_subtype_val
  refine hc.totallyBounded.subset ?_
  rintro x ⟨hxW, hxr⟩
  refine ⟨⟨x, hxW⟩, ?_, rfl⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hxr

end RenewalGeometry
