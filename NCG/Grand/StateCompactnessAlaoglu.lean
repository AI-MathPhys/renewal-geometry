/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# State compactness and spectral tightness
  (`thm:state-compactness-tightness`,
  Gran-Tensor manuscript)

* `state_compactness_tightness`:
  (i) **sequential Banach–Alaoglu for states** — on a
      separable normed space, the state set (functionals
      of norm at most one, normalized at the unit, and
      nonnegative on the positive cone) is weak-*
      sequentially compact: every sequence of states has
      a weak-* convergent subsequence with a state limit;
  (ii) **dense determination** — a uniformly bounded
      sequence of functionals converging pointwise on a
      dense subspace converges pointwise everywhere to
      the unique continuous extension (the ε/3 argument),
      and two continuous functionals agreeing on a dense
      subspace are equal;
  (iii) the boxed **Markov/Chebyshev spectral tightness**
      `ω(1_{|F|>R}) ≤ C_p R^{-p}` for finite spectral
      weights with a uniform `p`-moment bound.

The passage from the abstract separable normed carrier to
the quasilocal C*-algebra `𝒜_ql` (its unit, its positive
cone `{a*a}`, and the norm-one property of states) is the
manuscript's C*-layer: the clauses are stated for an
arbitrary unit vector `one` and positivity cone `P`, which
the C*-structure instantiates.
-/

open Filter Metric TopologicalSpace

namespace NCG

/-- `thm:state-compactness-tightness` (sequential
Banach–Alaoglu for the state set, dense determination,
and the boxed Markov tightness bound). -/
theorem state_compactness_tightness
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [SeparableSpace X] (one : X) (P : Set X) :
    -- (i) the state set is weak-* sequentially compact
    IsSeqCompact
      ((WeakDual.toStrongDual ⁻¹' closedBall 0 1)
        ∩ {φ : WeakDual ℂ X | φ one = 1}
        ∩ {φ : WeakDual ℂ X | ∀ a ∈ P, 0 ≤ (φ a).re})
    -- (ii) dense determination and unique extension
    ∧ (∀ (D : Submodule ℂ X), Dense (D : Set X) →
        (∀ (φn : ℕ → X →L[ℂ] ℂ) (ψ : X →L[ℂ] ℂ),
          (∀ n, ‖φn n‖ ≤ 1) → ‖ψ‖ ≤ 1 →
          (∀ x ∈ D, Tendsto (fun n => φn n x) atTop
            (nhds (ψ x))) →
          ∀ x : X, Tendsto (fun n => φn n x) atTop
            (nhds (ψ x)))
        ∧ (∀ ψ ψ' : X →L[ℂ] ℂ,
            (∀ x ∈ D, ψ x = ψ' x) → ψ = ψ'))
    -- (iii) the boxed spectral tightness bound
    ∧ (∀ {ι : Type} [Fintype ι] (w f : ι → ℝ)
        (p R Cp : ℝ), (∀ i, 0 ≤ w i) → 0 < R → 0 < p →
        (∑ i, w i * |f i| ^ p ≤ Cp) →
        (∑ i ∈ Finset.univ.filter fun i => R < |f i|,
          w i) ≤ Cp / R ^ p) := by
  refine ⟨?_, fun D hD => ⟨?_, ?_⟩, ?_⟩
  · -- (i) bounded ∩ closed ⟹ sequentially compact
    apply WeakDual.isSeqCompact_of_isBounded_of_isClosed
    · apply Bornology.IsBounded.subset
        (WeakDual.isBounded_closedBall (𝕜 := ℂ)
          (E := X) 0 1)
      intro φ hφ
      exact hφ.1.1
    · apply IsClosed.inter
      · apply IsClosed.inter
        · exact WeakDual.isClosed_closedBall 0 1
        · have : {φ : WeakDual ℂ X | φ one = 1}
              = (fun φ : WeakDual ℂ X => φ one) ⁻¹'
                {1} := rfl
          rw [this]
          exact IsClosed.preimage
            (WeakDual.eval_continuous one)
            isClosed_singleton
      · have : {φ : WeakDual ℂ X | ∀ a ∈ P,
            0 ≤ (φ a).re}
            = ⋂ a ∈ P, {φ : WeakDual ℂ X |
              0 ≤ (φ a).re} := by
          ext φ
          simp only [Set.mem_setOf_eq, Set.mem_iInter]
        rw [this]
        apply isClosed_iInter
        intro a
        apply isClosed_iInter
        intro _
        apply isClosed_le continuous_const
        exact (Complex.continuous_re).comp
          (WeakDual.eval_continuous a)
  · -- (ii) dense determination, ε/3
    intro φn ψ hφn hψ hconv x
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨d, hdD, hdx⟩ :
        ∃ d ∈ (D : Set X), dist x d < ε / 3 := by
      have := Metric.dense_iff.mp hD x (ε / 3)
        (by positivity)
      obtain ⟨d, hd1, hd2⟩ := this
      rw [Metric.mem_ball] at hd1
      rw [dist_comm] at hd1
      exact ⟨d, hd2, hd1⟩
    have hd := hconv d hdD
    rw [Metric.tendsto_atTop] at hd
    obtain ⟨N, hN⟩ := hd (ε / 3) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : dist (φn n x) (φn n d) ≤ ε / 3 := by
      rw [dist_eq_norm, ← map_sub]
      calc ‖φn n (x - d)‖
          ≤ ‖φn n‖ * ‖x - d‖ :=
            (φn n).le_opNorm _
        _ ≤ 1 * ‖x - d‖ :=
            mul_le_mul_of_nonneg_right (hφn n)
              (norm_nonneg _)
        _ = dist x d := by rw [one_mul, dist_eq_norm]
        _ ≤ ε / 3 := le_of_lt hdx
    have h2 : dist (φn n d) (ψ d) < ε / 3 := hN n hn
    have h3 : dist (ψ d) (ψ x) ≤ ε / 3 := by
      rw [dist_eq_norm, ← map_sub]
      calc ‖ψ (d - x)‖
          ≤ ‖ψ‖ * ‖d - x‖ := ψ.le_opNorm _
        _ ≤ 1 * ‖d - x‖ :=
            mul_le_mul_of_nonneg_right hψ
              (norm_nonneg _)
        _ = dist x d := by
            rw [one_mul, norm_sub_rev, dist_eq_norm]
        _ ≤ ε / 3 := le_of_lt hdx
    calc dist (φn n x) (ψ x)
        ≤ dist (φn n x) (φn n d)
          + dist (φn n d) (ψ x) := dist_triangle _ _ _
      _ ≤ dist (φn n x) (φn n d)
          + (dist (φn n d) (ψ d)
            + dist (ψ d) (ψ x)) := by
          have := dist_triangle (φn n d) (ψ d) (ψ x)
          linarith
      _ < ε / 3 + (ε / 3 + ε / 3) := by linarith
      _ = ε := by ring
  · -- (ii) unique extension by density
    intro ψ ψ' hagree
    ext x
    have hclosed : IsClosed {y : X | ψ y = ψ' y} :=
      isClosed_eq ψ.continuous ψ'.continuous
    have hsub : (D : Set X) ⊆ {y : X | ψ y = ψ' y} :=
      fun y hy => hagree y hy
    exact hclosed.closure_subset_iff.mpr hsub (hD x)
  · -- (iii) the boxed Markov bound
    intro ι _ w f p R Cp hw hR hp hmom
    have hstep : (∑ i ∈ Finset.univ.filter
        fun i => R < |f i|, w i) * R ^ p
        ≤ ∑ i, w i * |f i| ^ p := by
      rw [Finset.sum_mul]
      calc (∑ i ∈ Finset.univ.filter
            fun i => R < |f i|, w i * R ^ p)
          ≤ ∑ i ∈ Finset.univ.filter
              fun i => R < |f i|, w i * |f i| ^ p := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.mem_filter] at hi
            apply mul_le_mul_of_nonneg_left _ (hw i)
            exact Real.rpow_le_rpow (le_of_lt hR)
              (le_of_lt hi.2) (le_of_lt hp)
        _ ≤ ∑ i, w i * |f i| ^ p := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _)
            intro i _ _
            apply mul_nonneg (hw i)
            exact Real.rpow_nonneg (abs_nonneg _) p
    have hRp : (0 : ℝ) < R ^ p :=
      Real.rpow_pos_of_pos hR p
    rw [le_div_iff₀ hRp]
    exact le_trans hstep hmom

end NCG
