/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.LapseShiftFirstJetShadowing

/-!
# The active/weak amplitude grading and the necessary lapse--shift clock test
  (`prop:supp-exact-clock-test`, `eq:supp-exact-rate-norm`,
  `eq:supp-exact-rate-necessary`; emergent-spacetime manuscript)

This file closes the two interface hypotheses left open in
`RenewalGeometry.Gravity.LapseShiftFirstJetShadowing` (`hlam`, `hnorm`).

## The grading `S_a = diag(a I_A, a² I_W)`

`AmplitudeGrading Λ` is an orthogonal active/weak decomposition of the (real,
inner-product) multiplier space `Λ`: a weak subspace `W` (with orthogonal
projection) and its orthogonal complement `A = Wᗮ`.  `activePart`, `weakPart`
are the two orthogonal projections, `scale a` is the grading
`S_a v = a v_A + a² v_W`, and the normalized source coefficient entering the
multiplier solve is `normalizedSource a λ_t = S_a λ_t` — i.e. the multiplier
solve returns the multiplier rate `λ_t = S_a⁻¹ u_a`, which is the only
property of `u_a` the manuscript uses.  Then `eq:supp-exact-rate-norm`

`‖λ_t‖² = a⁻² ‖(u_a)_A‖² + a⁻⁴ ‖(u_a)_W‖²`

is the theorem `AmplitudeGrading.rate_norm` (Pythagoras for the orthogonal
decomposition plus `(u_a)_A = a λ_A`, `(u_a)_W = a² λ_W`).

## The multiplier rate is the lapse--shift first jet

The ADM multipliers are the lapse and shift, so the multiplier rate at the
initial cut is the lapse--shift first jet `(∂ₜN, ∂ₜβ)`; on `V` sites this is
the vector `lapseShiftJet N₁ β₁` of the `4V`-dimensional Euclidean multiplier
space `EuclideanSpace ℝ (V × Fin 4)` (`lapseShiftJet_norm_sq`).

## The proposition

`exact_clock_test` (`prop:supp-exact-clock-test`): along a regulator family
`i ↦ a i ≠ 0`, if at every site the exact-action ADM metric shadows a small
harmonic ADM metric in the initial first time derivative of `g₀₀`, `g₀ᵢ`
(same lapse `N = 1`, shift `β = 0`, spatial metric at the initial cut, uniformly
coercive spatial metrics, small harmonic first jet), then for every amplitude
grading `G` of the multiplier space, with `u_a = S_a λ_t` and
`λ_t = lapseShiftJet (∂ₜN) (∂ₜβ)`,

`a⁻¹ ‖(u_a)_A‖ → 0` and `a⁻² ‖(u_a)_W‖ → 0` (`eq:supp-exact-rate-necessary`).

The instantaneous electric coefficient does not enter.  Disclosed modelling
choices (inherited from the earlier files): "small harmonic metric" means
smallness of its lapse--shift first jet with a uniformly coercive shared
spatial metric; the shadowing topology is the initial first time derivative
of the ADM components `g₀₀`, `g₀ᵢ` at each site; the grading is any orthogonal
active/weak decomposition of the site multiplier space, as the paper leaves it.
-/

open scoped BigOperators Topology
open Filter

namespace RenewalGeometry

/-! ### The active/weak amplitude grading -/

/-- An active/weak amplitude grading of a real inner-product multiplier space `Λ`:
the weak subspace `W` (with orthogonal projection); the active subspace is `Wᗮ`. -/
structure AmplitudeGrading (Λ : Type*) [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ] where
  /-- The weak multiplier subspace `W`. -/
  weak : Submodule ℝ Λ
  /-- `W` admits an orthogonal projection (automatic in finite dimension). -/
  [hasProj : weak.HasOrthogonalProjection]

namespace AmplitudeGrading

variable {Λ : Type*} [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ] (G : AmplitudeGrading Λ)

attribute [instance] AmplitudeGrading.hasProj

/-- The weak component `v_W` (orthogonal projection onto `W`). -/
noncomputable def weakPart (v : Λ) : Λ := G.weak.starProjection v

/-- The active component `v_A` (orthogonal projection onto `A = Wᗮ`). -/
noncomputable def activePart (v : Λ) : Λ := G.weakᗮ.starProjection v

theorem weakPart_mem (v : Λ) : G.weakPart v ∈ G.weak :=
  Submodule.starProjection_apply_mem _ v

theorem activePart_mem (v : Λ) : G.activePart v ∈ G.weakᗮ :=
  Submodule.starProjection_apply_mem _ v

theorem activePart_add_weakPart (v : Λ) : G.activePart v + G.weakPart v = v := by
  unfold activePart weakPart
  rw [add_comm]
  exact Submodule.starProjection_add_starProjection_orthogonal v

theorem weakPart_of_mem_weak {v : Λ} (hv : v ∈ G.weak) : G.weakPart v = v :=
  Submodule.starProjection_eq_self_iff.mpr hv

theorem activePart_of_mem_active {v : Λ} (hv : v ∈ G.weakᗮ) : G.activePart v = v :=
  Submodule.starProjection_eq_self_iff.mpr hv

theorem weakPart_of_mem_active {v : Λ} (hv : v ∈ G.weakᗮ) : G.weakPart v = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).mpr hv

theorem activePart_of_mem_weak {v : Λ} (hv : v ∈ G.weak) : G.activePart v = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).mpr (Submodule.le_orthogonal_orthogonal _ hv)

/-- Pythagoras for the grading: `‖v‖² = ‖v_A‖² + ‖v_W‖²`. -/
theorem norm_sq_eq (v : Λ) : ‖v‖ ^ 2 = ‖G.activePart v‖ ^ 2 + ‖G.weakPart v‖ ^ 2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_projection v G.weak
  rw [add_comm] at h
  exact h

/-- The grading `S_a v = a v_A + a² v_W` (`S_a = diag(a I_A, a² I_W)`). -/
noncomputable def scale (a : ℝ) (v : Λ) : Λ := a • G.activePart v + a ^ 2 • G.weakPart v

theorem activePart_scale (a : ℝ) (v : Λ) : G.activePart (G.scale a v) = a • G.activePart v := by
  unfold scale
  have h1 : G.activePart (a • G.activePart v) = a • G.activePart v :=
    G.activePart_of_mem_active (Submodule.smul_mem _ a (G.activePart_mem v))
  have h2 : G.activePart (a ^ 2 • G.weakPart v) = 0 :=
    G.activePart_of_mem_weak (Submodule.smul_mem _ _ (G.weakPart_mem v))
  unfold activePart at h1 h2 ⊢
  rw [map_add, h1, h2, add_zero]

theorem weakPart_scale (a : ℝ) (v : Λ) : G.weakPart (G.scale a v) = a ^ 2 • G.weakPart v := by
  unfold scale
  have h1 : G.weakPart (a • G.activePart v) = 0 :=
    G.weakPart_of_mem_active (Submodule.smul_mem _ a (G.activePart_mem v))
  have h2 : G.weakPart (a ^ 2 • G.weakPart v) = a ^ 2 • G.weakPart v :=
    G.weakPart_of_mem_weak (Submodule.smul_mem _ _ (G.weakPart_mem v))
  unfold weakPart at h1 h2 ⊢
  rw [map_add, h1, h2, zero_add]

/-- The normalized source coefficient entering the multiplier solve, `u_a = S_a λ_t`
(the multiplier solve returns `λ_t = S_a⁻¹ u_a`). -/
noncomputable def normalizedSource (a : ℝ) (lt : Λ) : Λ := G.scale a lt

/-- **`eq:supp-exact-rate-norm`**: `‖λ_t‖² = a⁻² ‖(u_a)_A‖² + a⁻⁴ ‖(u_a)_W‖²` for
`u_a = S_a λ_t`, `a ≠ 0`. -/
theorem rate_norm (a : ℝ) (ha : a ≠ 0) (lt : Λ) :
    ‖lt‖ ^ 2 = a⁻¹ ^ 2 * ‖G.activePart (G.normalizedSource a lt)‖ ^ 2 +
      a⁻¹ ^ 4 * ‖G.weakPart (G.normalizedSource a lt)‖ ^ 2 := by
  unfold normalizedSource
  rw [activePart_scale, weakPart_scale, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, G.norm_sq_eq lt]
  have h2 : |a| ^ 2 = a ^ 2 := sq_abs a
  have h4 : |a ^ 2| ^ 2 = a ^ 4 := by rw [abs_of_nonneg (sq_nonneg a)]; ring
  rw [h2, h4]
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  field_simp

end AmplitudeGrading

/-! ### The lapse--shift first jet as the multiplier rate -/

/-- The lapse--shift first jet `(∂ₜN, ∂ₜβ)` at the sites `V`, as a vector of the
`4V`-dimensional multiplier space (index `0` = lapse, `1..3` = shift). -/
noncomputable def lapseShiftJet {V : Type*} [Fintype V] (N₁ : V → ℝ) (β₁ : V → Fin 3 → ℝ) :
    EuclideanSpace ℝ (V × Fin 4) :=
  WithLp.toLp 2 fun p => (Fin.cons (N₁ p.1) (β₁ p.1) : Fin 4 → ℝ) p.2

theorem lapseShiftJet_apply {V : Type*} [Fintype V] (N₁ : V → ℝ) (β₁ : V → Fin 3 → ℝ)
    (p : V × Fin 4) :
    WithLp.ofLp (lapseShiftJet N₁ β₁) p = (Fin.cons (N₁ p.1) (β₁ p.1) : Fin 4 → ℝ) p.2 := rfl

/-- `‖(∂ₜN, ∂ₜβ)‖² = ∑_x ((∂ₜN_x)² + ∑_j (∂ₜβ_x^j)²)`. -/
theorem lapseShiftJet_norm_sq {V : Type*} [Fintype V] (N₁ : V → ℝ) (β₁ : V → Fin 3 → ℝ) :
    ‖lapseShiftJet N₁ β₁‖ ^ 2 = ∑ x, (N₁ x ^ 2 + sumSq (β₁ x)) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fin.sum_univ_succ]
  simp only [lapseShiftJet_apply, Fin.cons_zero, Fin.cons_succ, sumSq]

/-! ### The necessary clock condition -/

/-- **`prop:supp-exact-clock-test`** (`eq:supp-exact-rate-necessary`).  Along a regulator
family `i ↦ a i ≠ 0`, suppose at every site `x` the exact-action ADM metric
`(N i x, β i x, γ i x)` shadows a small harmonic ADM metric `(N' i x, β' i x, γ i x)` in the
initial first time derivative of `g₀₀`, `g₀ᵢ`, with the same lapse `N = 1`, shift `β = 0`
and spatial metric at the initial cut `t₀`, uniformly coercive spatial metrics and a small
harmonic first jet.  Then for every active/weak amplitude grading `G` of the multiplier
space, with the multiplier rate `λ_t = (∂ₜN, ∂ₜβ)` and the normalized source coefficient
`u_a = S_a λ_t`, necessarily `a⁻¹ ‖(u_a)_A‖ → 0` and `a⁻² ‖(u_a)_W‖ → 0`.  The
instantaneous electric coefficient does not enter. -/
theorem exact_clock_test {ι V : Type*} [Fintype V] (l : Filter ι) (t₀ : ℝ)
    (N N' : ι → V → ℝ → ℝ) (β β' : ι → V → ℝ → Fin 3 → ℝ)
    (γ : ι → V → ℝ → Fin 3 → Fin 3 → ℝ)
    (N₁ N₁' : ι → V → ℝ) (β₁ β₁' : ι → V → Fin 3 → ℝ) (γ₁ : ι → V → Fin 3 → Fin 3 → ℝ)
    (hN : ∀ i x, HasDerivAt (N i x) (N₁ i x) t₀)
    (hN' : ∀ i x, HasDerivAt (N' i x) (N₁' i x) t₀)
    (hβ : ∀ i x j, HasDerivAt (fun t => β i x t j) (β₁ i x j) t₀)
    (hβ' : ∀ i x j, HasDerivAt (fun t => β' i x t j) (β₁' i x j) t₀)
    (hγ : ∀ i x j k, HasDerivAt (fun t => γ i x t j k) (γ₁ i x j k) t₀)
    (hN0 : ∀ i x, N i x t₀ = 1) (hN0' : ∀ i x, N' i x t₀ = 1)
    (hβ0 : ∀ i x j, β i x t₀ j = 0) (hβ0' : ∀ i x j, β' i x t₀ j = 0)
    (c : ℝ) (hc : 0 < c)
    (hcoer : ∀ i x (y : Fin 3 → ℝ), c * sumSq y ≤ ∑ j, y j * (∑ k, γ i x t₀ j k * y k))
    (hshadow00 : ∀ x, Tendsto (fun i => deriv (admMetric00 (N i x) (γ i x) (β i x)) t₀
      - deriv (admMetric00 (N' i x) (γ i x) (β' i x)) t₀) l (𝓝 0))
    (hshadow0i : ∀ x j, Tendsto (fun i => deriv (admMetric0i (γ i x) (β i x) j) t₀
      - deriv (admMetric0i (γ i x) (β' i x) j) t₀) l (𝓝 0))
    (hsmallN : ∀ x, Tendsto (fun i => N₁' i x) l (𝓝 0))
    (hsmallβ : ∀ x j, Tendsto (fun i => β₁' i x j) l (𝓝 0))
    (G : AmplitudeGrading (EuclideanSpace ℝ (V × Fin 4)))
    (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    Tendsto (fun i => (a i)⁻¹ *
      ‖G.activePart (G.normalizedSource (a i) (lapseShiftJet (N₁ i) (β₁ i)))‖) l (𝓝 0) ∧
    Tendsto (fun i => (a i)⁻¹ ^ 2 *
      ‖G.weakPart (G.normalizedSource (a i) (lapseShiftJet (N₁ i) (β₁ i)))‖) l (𝓝 0) := by
  -- the lapse--shift first jet vanishes at every site
  have hsite : ∀ x, Tendsto (fun i => N₁ i x) l (𝓝 0) ∧
      ∀ j, Tendsto (fun i => β₁ i x j) l (𝓝 0) := fun x =>
    first_jet_shadowing_lapse_shift_rate l t₀ (fun i => N i x) (fun i => N' i x)
      (fun i => β i x) (fun i => β' i x) (fun i => γ i x) (fun i => N₁ i x) (fun i => N₁' i x)
      (fun i => β₁ i x) (fun i => β₁' i x) (fun i => γ₁ i x) (fun i => hN i x) (fun i => hN' i x)
      (fun i => hβ i x) (fun i => hβ' i x) (fun i => hγ i x) (fun i => hN0 i x)
      (fun i => hN0' i x) (fun i => hβ0 i x) (fun i => hβ0' i x) c hc (fun i => hcoer i x)
      (hshadow00 x) (hshadow0i x) (hsmallN x) (hsmallβ x)
  -- hence `‖λ_t‖² → 0`
  have hsq : Tendsto (fun i => ‖lapseShiftJet (N₁ i) (β₁ i)‖ ^ 2) l (𝓝 0) := by
    have hx : ∀ x, Tendsto (fun i => N₁ i x ^ 2 + sumSq (β₁ i x)) l (𝓝 0) := by
      intro x
      have hβsq : Tendsto (fun i => sumSq (β₁ i x)) l (𝓝 0) := by
        have := tendsto_finsetSum Finset.univ fun j _ => ((hsite x).2 j).pow 2
        simpa [sumSq] using this
      have := ((hsite x).1.pow 2).add hβsq
      simpa using this
    have := tendsto_finsetSum Finset.univ fun x _ => hx x
    simp only [Finset.sum_const_zero] at this
    exact this.congr fun i => (lapseShiftJet_norm_sq (N₁ i) (β₁ i)).symm
  have hl : Tendsto (fun i => ‖lapseShiftJet (N₁ i) (β₁ i)‖) l (𝓝 0) := by
    have hsqrt : Tendsto (fun i => Real.sqrt (‖lapseShiftJet (N₁ i) (β₁ i)‖ ^ 2)) l (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hsq
      rw [Real.sqrt_zero] at this
      exact this
    refine squeeze_zero_norm (fun i => ?_) hsqrt
    rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
  -- the graded rate norm `eq:supp-exact-rate-norm` and the squeeze
  exact lapse_shift_clock_condition l a
    (fun i => ‖G.activePart (G.normalizedSource (a i) (lapseShiftJet (N₁ i) (β₁ i)))‖)
    (fun i => ‖G.weakPart (G.normalizedSource (a i) (lapseShiftJet (N₁ i) (β₁ i)))‖)
    (fun i => ‖lapseShiftJet (N₁ i) (β₁ i)‖)
    (fun i => G.rate_norm (a i) (ha i) _) hl

end RenewalGeometry
