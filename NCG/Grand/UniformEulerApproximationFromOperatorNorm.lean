/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniformEulerResolventSemigroupConvergence
import NCG.Grand.VaryingHilbertStrongBoundedness

/-!
# Uniform Euler approximation from operator-norm error bounds

The varying-Hilbert Euler compiler asks for a vectorwise error estimate along every strongly
convergent dependent source family.  In applications, the available analytic estimate is usually
stronger and simpler: a cutoff- and time-uniform operator-norm error bounded by a scalar sequence
that tends to zero.  Strong convergence automatically bounds the source norms, so such an
operator estimate supplies the vectorwise premise.

This file packages that reduction and a direct uniform Euler-resolvent semigroup compiler.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- A scalar operator-norm error tending to zero yields the vectorwise uniform approximation
premise for every strongly convergent varying-Hilbert source sequence. -/
theorem eventually_uniform_apply_dist_of_operatorNorm_error
    {τ : Type z} (An : ∀ n, τ → Hn n →L[K] Hn n)
    (Bn : ℕ → ∀ n, τ → Hn n →L[K] Hn n)
    (error : ℕ → ℝ) (s : Set τ)
    (herror : Tendsto error atTop (𝓝 0))
    (herrorNonneg : ∀ m, 0 ≤ error m)
    (hop : ∀ m, ∀ᶠ n in atTop, ∀ t ∈ s, ‖An n t - Bn m n t‖ ≤ error m)
    (x : ∀ n, Hn n) (xlim : H) (hx : J.StronglyConverges x xlim) :
    ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, ∀ t ∈ s,
      dist (J.embedding n (An n t (x n)))
        (J.embedding n (Bn m n t (x n))) < ε := by
  obtain ⟨C, hC, hxC⟩ := hx.exists_pos_uniform_norm_bound J
  intro ε hε
  have hevent : ∀ᶠ m in atTop, dist (error m) 0 < ε / C :=
    (Metric.tendsto_atTop.mp herror) (ε / C) (div_pos hε hC) |>
      fun ⟨N, hN⟩ ↦ eventually_atTop.mpr ⟨N, hN⟩
  filter_upwards [hevent] with m hm
  filter_upwards [hop m] with n hn
  intro t ht
  have herrlt : error m < ε / C := by
    simpa [Real.dist_eq, abs_of_nonneg (herrorNonneg m)] using hm
  rw [dist_eq_norm, ← map_sub, (J.embedding n).norm_map]
  calc
    ‖An n t (x n) - Bn m n t (x n)‖ =
        ‖(An n t - Bn m n t) (x n)‖ := by rw [sub_apply]
    _ ≤ ‖An n t - Bn m n t‖ * ‖x n‖ :=
      (An n t - Bn m n t).le_opNorm (x n)
    _ ≤ error m * C :=
      mul_le_mul (hn t ht) (hxC n) (norm_nonneg _) (herrorNonneg m)
    _ < (ε / C) * C := mul_lt_mul_of_pos_right herrlt hC
    _ = ε := by field_simp

/-- Uniform strong semigroup convergence from fixed-order resolvent convergence, convergence of
the limit Euler scheme, and a cutoff/time-uniform operator-norm Euler error tending to zero. -/
theorem StrongOperatorConvergesUniformlyOn.of_eulerResolventOperatorNormError
    {τ : Type z} [TopologicalSpace τ]
    (Sn : ∀ n, τ → Hn n →L[K] Hn n) (S : τ → H →L[K] H)
    (Rn : ℕ → ∀ n, τ → Hn n →L[K] Hn n)
    (R : ℕ → τ → H →L[K] H) (a : ℕ → τ → K) (s : Set τ)
    (error : ℕ → ℝ)
    (hs : IsCompact s)
    (hR : ∀ m, ∀ t ∈ s,
      J.StrongOperatorConverges J (fun n ↦ Rn m n t) (R m t))
    (hfixedEq : ∀ m, ∀ (x : ∀ n, Hn n) (xlim : H),
      J.StronglyConverges x xlim →
        EquicontinuousOn
          (fun n t ↦ J.embedding n (((a m t • Rn m n t) ^ m) (x n))) s)
    (hEulerLimit : ∀ x : H,
      TendstoUniformlyOn
        (fun m t ↦ ((a m t • R m t) ^ m) x)
        (fun t ↦ S t x) atTop s)
    (herror : Tendsto error atTop (𝓝 0))
    (herrorNonneg : ∀ m, 0 ≤ error m)
    (hop : ∀ m, ∀ᶠ n in atTop, ∀ t ∈ s,
      ‖Sn n t - (a m t • Rn m n t) ^ m‖ ≤ error m) :
    J.StrongOperatorConvergesUniformlyOn Sn S s := by
  apply StrongOperatorConvergesUniformlyOn.of_eulerResolventApproximants
    J Sn S Rn R a s hs hR hfixedEq hEulerLimit
  intro x xlim hx
  exact eventually_uniform_apply_dist_of_operatorNorm_error J Sn
    (fun m n t ↦ (a m t • Rn m n t) ^ m) error s
    herror herrorNonneg hop x xlim hx

/-- Pointwise strong semigroup convergence from the same eventual cutoff-uniform operator-norm
Euler error estimate. -/
theorem StrongOperatorConverges.of_eulerResolventOperatorNormError
    (Sn : ∀ n, Hn n →L[K] Hn n) (S : H →L[K] H)
    (Rn : ℕ → ∀ n, Hn n →L[K] Hn n) (R : ℕ → H →L[K] H)
    (a : ℕ → K) (error : ℕ → ℝ)
    (hR : ∀ m, J.StrongOperatorConverges J (Rn m) (R m))
    (hEulerLimit : ∀ x : H,
      Tendsto (fun m ↦ ((a m • R m) ^ m) x) atTop (𝓝 (S x)))
    (herror : Tendsto error atTop (𝓝 0))
    (herrorNonneg : ∀ m, 0 ≤ error m)
    (hop : ∀ m, ∀ᶠ n in atTop,
      ‖Sn n - (a m • Rn m n) ^ m‖ ≤ error m) :
    J.StrongOperatorConverges J Sn S := by
  apply StrongOperatorConverges.of_eulerResolventApproximants
    J Sn S Rn R a hR hEulerLimit
  intro x xlim hx ε hε
  have h := eventually_uniform_apply_dist_of_operatorNorm_error J
    (τ := Unit) (fun n _ ↦ Sn n)
    (fun m n _ ↦ (a m • Rn m n) ^ m) error (Set.univ : Set Unit)
    herror herrorNonneg
    (fun m ↦ (hop m).mono fun n hn _ _ ↦ hn) x xlim hx ε hε
  simpa using h

end NCG.VaryingHilbert.System
