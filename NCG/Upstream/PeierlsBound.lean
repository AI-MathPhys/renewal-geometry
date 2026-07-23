/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Peierls bound: uniform low-temperature magnetization

The quantitative core of the Gibbs/Peierls cluster
(`thm:torsion-phase-coexistence` (ii), `cor:torsion-selection`,
clause (iii) of `thm:common-origin-phase`, criterion (C4) of
`cor:full-phase-nonempty`; `manuscripts/renewal_emergence/renewal_emergence.tex`).

* `sum_le_of_weight_gain` — **the flip-injection estimate**: if an
  event injects into the configuration space with Gibbs-weight gain
  `K`, its probability is at most `1/K`;
* `ContourDatum` — the contour interface for a finite-volume plus
  phase: every minus-at-origin configuration exhibits a contour of
  length `≥ 4`, with at most `4n·3^{n−1}` contours of length `n`
  (the classical planar dual-circuit geometry, the scoped input),
  each carrying a weight-gaining flip injection;
* `tail_geometric_eval` — the exact tail series
  `∑_{n≥4} n rⁿ = r⁴(4−3r)/(1−r)²`;
* `peierls_prob_bound` — **the Peierls estimate**: the probability
  of a minus origin is at most `(4/3)·r⁴(4−3r)/(1−r)²` with
  `r = 3e^{−2θ}`, hence at most `13/432` for `r ≤ 1/4`;
* `peierls_magnetization` — **the uniform magnetization bound**: for
  `θ ≥ ½·log 12`, every finite volume with plus boundary satisfies
  `⟨τ₀⟩ ≥ 203/216`, uniformly in the volume;
* `flip_phase_neg` / `mixture_zero` — the deck-related minus phase
  has opposite magnetization, and the symmetric mixture has zero
  mean for every exchange-odd observable;
* `phase_pair_of_uniform_bound` — **the thermodynamic-limit
  packaging**: uniformly bounded finite-volume magnetizations have a
  subsequential limit `m⁺ ≥ 203/216`; with its deck image
  `m⁻ = −m⁺` this is the separated pair of orientation phases, with
  vanishing symmetric mixture.
-/

namespace NCG.Upstream

open Filter

/-! ## The flip-injection estimate -/

/-- **The flip-injection estimate**: an event that injects into the
configuration space with uniform weight gain `K` has weight at most
`1/K` of the total. -/
theorem sum_le_of_weight_gain {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (w : Ω → ℝ) (hw : ∀ σ, 0 ≤ w σ)
    (A : Finset Ω) (F : Ω → Ω) (hinj : Set.InjOn F A)
    {K : ℝ} (hK : 0 < K)
    (hgain : ∀ σ ∈ A, K * w σ ≤ w (F σ)) :
    K * ∑ σ ∈ A, w σ ≤ ∑ σ, w σ := by
  calc K * ∑ σ ∈ A, w σ = ∑ σ ∈ A, K * w σ := Finset.mul_sum _ _ _
    _ ≤ ∑ σ ∈ A, w (F σ) := Finset.sum_le_sum hgain
    _ = ∑ τ ∈ A.image F, w τ := by
        rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    _ ≤ ∑ σ, w σ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun τ _ _ => hw τ)

/-! ## The contour interface -/

/-- **The contour interface** for a finite-volume plus phase: the
classical planar dual-circuit geometry (Georgii, Ch. 6), the scoped
input of the Peierls argument.  Contours have length at least four,
at most `4n·3^{n−1}` contours of length `n` exist, every
minus-at-origin configuration exhibits a contour, and flipping
inside a contour is injective with Gibbs-weight gain
`e^{2θ|γ|}`. -/
structure ContourDatum (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (w : Ω → ℝ) (θ : ℝ) (Bad : Finset Ω) where
  /-- Contour labels. -/
  ι : Type
  /-- Finitely many contours. -/
  fin : Fintype ι
  /-- Contour length. -/
  len : ι → ℕ
  /-- Contours surround at least one plaquette. -/
  len_ge : ∀ γ, 4 ≤ len γ
  /-- The planar counting bound. -/
  count : ∀ n : ℕ, ((Finset.univ (α := ι)).filter
    (fun γ => len γ = n)).card ≤ 4 * n * 3 ^ (n - 1)
  /-- The configurations exhibiting the contour `γ`. -/
  occurs : ι → Finset Ω
  /-- Every bad configuration exhibits a contour. -/
  cover : ∀ σ ∈ Bad, ∃ γ, σ ∈ occurs γ
  /-- The contour flip. -/
  flip : ι → Ω → Ω
  /-- Flipping a fixed contour is injective. -/
  flip_inj : ∀ γ, Set.InjOn (flip γ) (occurs γ)
  /-- Flipping gains the Peierls weight. -/
  gain : ∀ γ, ∀ σ ∈ occurs γ,
    Real.exp (2 * θ * len γ) * w σ ≤ w (flip γ σ)

attribute [instance] ContourDatum.fin

/-! ## The tail series -/

/-- The exact tail of the derivative geometric series:
`∑_{n≥4} n rⁿ = r⁴(4−3r)/(1−r)²`, as an upper bound for every
finite subsum. -/
theorem tail_geometric_eval {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 4 ≤ n) :
    ∑ n ∈ S, (n : ℝ) * r ^ n
      ≤ r ^ 4 * (4 - 3 * r) / (1 - r) ^ 2 := by
  have habs : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hsum : HasSum (fun n : ℕ => (n : ℝ) * r ^ n)
      (r / (1 - r) ^ 2) := hasSum_coe_mul_geometric_of_norm_lt_one habs
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) * r ^ n := fun n =>
    mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hr0 n)
  -- the finite subsum together with the head is below the total sum
  have hdisj : Disjoint S (Finset.range 4) := by
    rw [Finset.disjoint_right]
    intro n hn hnS
    rw [Finset.mem_range] at hn
    exact absurd (hS n hnS) (by omega)
  have hle : ∑ n ∈ S ∪ Finset.range 4, (n : ℝ) * r ^ n
      ≤ r / (1 - r) ^ 2 := by
    rw [← hsum.tsum_eq]
    exact hsum.summable.sum_le_tsum _ (fun n _ => hnn n)
  rw [Finset.sum_union hdisj] at hle
  have hhead : ∑ n ∈ Finset.range 4, (n : ℝ) * r ^ n
      = r + 2 * r ^ 2 + 3 * r ^ 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    push_cast
    ring
  rw [hhead] at hle
  have hne : (1 - r) ≠ 0 := by linarith
  have hkey : r / (1 - r) ^ 2 - (r + 2 * r ^ 2 + 3 * r ^ 3)
      = r ^ 4 * (4 - 3 * r) / (1 - r) ^ 2 := by
    field_simp
    ring
  linarith [hkey]

/-- The closed-form tail is at most `13/432` on `r ∈ [0, 1/4]`. -/
theorem tail_le_at_quarter {r : ℝ} (hr0 : 0 ≤ r) (hr4 : r ≤ 1 / 4) :
    (4 / 3) * (r ^ 4 * (4 - 3 * r) / (1 - r) ^ 2) ≤ 13 / 432 := by
  have hpos : (0 : ℝ) < (1 - r) ^ 2 := by nlinarith
  have h1 : (4 / 3) * (r ^ 4 * (4 - 3 * r) / (1 - r) ^ 2)
      = (4 * r ^ 4 * (4 - 3 * r)) / (3 * (1 - r) ^ 2) := by
    field_simp
    try ring
  rw [h1, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 432)]
  have h14 : 0 ≤ 1 - 4 * r := by linarith
  have hr2 : r ^ 2 ≤ 1 / 16 := by nlinarith
  have hr4pow : r ^ 2 * r ^ 2 ≤ (1 / 16) * r ^ 2 :=
    mul_le_mul_of_nonneg_right hr2 (sq_nonneg r)
  have hq : 0 ≤ 39 + 78 * r + 351 * r ^ 2 + 1404 * r ^ 3
      - 1296 * r ^ 4 := by
    nlinarith [pow_nonneg hr0 3, sq_nonneg r, hr0, hr4pow]
  nlinarith [mul_nonneg h14 hq]

/-! ## The Peierls estimate -/

/-- **The Peierls probability bound**: with `r = 3e^{−2θ} < 1`, the
weight of the bad event is at most `(4/3)·r⁴(4−3r)/(1−r)²` of the
total. -/
theorem peierls_prob_bound {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {w : Ω → ℝ} {θ : ℝ} {Bad : Finset Ω}
    (hw : ∀ σ, 0 ≤ w σ) (D : ContourDatum Ω w θ Bad)
    (hr1 : 3 * Real.exp (-(2 * θ)) < 1) :
    ∑ σ ∈ Bad, w σ
      ≤ (4 / 3) * ((3 * Real.exp (-(2 * θ))) ^ 4
          * (4 - 3 * (3 * Real.exp (-(2 * θ))))
          / (1 - 3 * Real.exp (-(2 * θ))) ^ 2) * ∑ σ, w σ := by
  classical
  set r : ℝ := 3 * Real.exp (-(2 * θ)) with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hW0 : 0 ≤ ∑ σ, w σ := Finset.sum_nonneg fun σ _ => hw σ
  -- union bound over contours
  have hunion : ∑ σ ∈ Bad, w σ
      ≤ ∑ γ : D.ι, ∑ σ ∈ D.occurs γ, w σ := by
    have h1 : ∀ σ ∈ Bad, w σ ≤ ∑ γ : D.ι,
        (if σ ∈ D.occurs γ then w σ else 0) := by
      intro σ hσ
      obtain ⟨γ₀, hγ₀⟩ := D.cover σ hσ
      refine Finset.single_le_sum (f := fun γ =>
        (if σ ∈ D.occurs γ then w σ else 0)) ?_ (Finset.mem_univ γ₀)
        |>.trans_eq' ?_
      · intro γ _
        by_cases h : σ ∈ D.occurs γ <;> simp [h, hw σ]
      · rw [if_pos hγ₀]
    calc ∑ σ ∈ Bad, w σ
        ≤ ∑ σ ∈ Bad, ∑ γ : D.ι,
            (if σ ∈ D.occurs γ then w σ else 0) :=
          Finset.sum_le_sum h1
      _ = ∑ γ : D.ι, ∑ σ ∈ Bad,
            (if σ ∈ D.occurs γ then w σ else 0) := Finset.sum_comm
      _ ≤ ∑ γ : D.ι, ∑ σ ∈ D.occurs γ, w σ := by
          refine Finset.sum_le_sum fun γ _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            (fun σ _ _ => hw σ)
          intro σ hσ
          rw [Finset.mem_filter] at hσ
          exact hσ.2
  -- each contour event is exponentially suppressed
  have hcontour : ∀ γ : D.ι, ∑ σ ∈ D.occurs γ, w σ
      ≤ Real.exp (-(2 * θ * D.len γ)) * ∑ σ, w σ := by
    intro γ
    have hK : (0 : ℝ) < Real.exp (2 * θ * D.len γ) := Real.exp_pos _
    have h2 := sum_le_of_weight_gain w hw (D.occurs γ) (D.flip γ)
      (D.flip_inj γ) hK (D.gain γ)
    rw [Real.exp_neg]
    rw [inv_mul_eq_div, le_div_iff₀ hK, mul_comm]
    exact h2
  -- group by contour length and evaluate the series
  have hgroup : ∑ γ : D.ι, Real.exp (-(2 * θ * D.len γ))
      ≤ (4 / 3) * (r ^ 4 * (4 - 3 * r) / (1 - r) ^ 2) := by
    have h3 : ∀ γ : D.ι, Real.exp (-(2 * θ * D.len γ))
        = Real.exp (-(2 * θ)) ^ (D.len γ) := by
      intro γ
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hregroup : ∑ γ : D.ι, Real.exp (-(2 * θ)) ^ (D.len γ)
        = ∑ n ∈ Finset.univ.image D.len,
            (((Finset.univ (α := D.ι)).filter
              (fun γ => D.len γ = n)).card : ℝ)
              * Real.exp (-(2 * θ)) ^ n := by
      rw [Finset.sum_comp (fun n : ℕ => Real.exp (-(2 * θ)) ^ n)
        D.len]
      exact Finset.sum_congr rfl fun n _ => by rw [nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun γ _ => h3 γ, hregroup]
    have h4 : ∀ n ∈ Finset.univ.image D.len,
        (((Finset.univ (α := D.ι)).filter
          (fun γ => D.len γ = n)).card : ℝ)
          * Real.exp (-(2 * θ)) ^ n
        ≤ (4 / 3) * ((n : ℝ) * r ^ n) := by
      intro n hn
      obtain ⟨γ, -, hγ⟩ := Finset.mem_image.mp hn
      have hn4 : 4 ≤ n := hγ ▸ D.len_ge γ
      have h5 : (((Finset.univ (α := D.ι)).filter
          (fun γ => D.len γ = n)).card : ℝ)
          ≤ 4 * n * 3 ^ (n - 1) := by
        exact_mod_cast D.count n
      have h6 : (0 : ℝ) ≤ Real.exp (-(2 * θ)) ^ n :=
        pow_nonneg (Real.exp_pos _).le n
      have h7 : (4 * (n : ℝ) * 3 ^ (n - 1))
          * Real.exp (-(2 * θ)) ^ n
          = (4 / 3) * ((n : ℝ) * r ^ n) := by
        rw [hrdef, mul_pow]
        have h8 : (3 : ℝ) ^ (n - 1) = 3 ^ n / 3 := by
          rw [eq_div_iff (by norm_num : (3:ℝ) ≠ 0), ← pow_succ]
          congr 1
          omega
        rw [h8]
        ring
      calc (((Finset.univ (α := D.ι)).filter
          (fun γ => D.len γ = n)).card : ℝ)
          * Real.exp (-(2 * θ)) ^ n
          ≤ (4 * (n : ℝ) * 3 ^ (n - 1))
            * Real.exp (-(2 * θ)) ^ n :=
            mul_le_mul_of_nonneg_right h5 h6
        _ = (4 / 3) * ((n : ℝ) * r ^ n) := h7
    calc ∑ n ∈ Finset.univ.image D.len,
        (((Finset.univ (α := D.ι)).filter
          (fun γ => D.len γ = n)).card : ℝ)
          * Real.exp (-(2 * θ)) ^ n
        ≤ ∑ n ∈ Finset.univ.image D.len,
            (4 / 3) * ((n : ℝ) * r ^ n) :=
          Finset.sum_le_sum h4
      _ = (4 / 3) * ∑ n ∈ Finset.univ.image D.len,
            (n : ℝ) * r ^ n := by
          rw [Finset.mul_sum]
      _ ≤ (4 / 3) * (r ^ 4 * (4 - 3 * r) / (1 - r) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine tail_geometric_eval hr0 hr1 _ ?_
          intro n hn
          obtain ⟨γ, -, hγ⟩ := Finset.mem_image.mp hn
          exact hγ ▸ D.len_ge γ
  calc ∑ σ ∈ Bad, w σ
      ≤ ∑ γ : D.ι, ∑ σ ∈ D.occurs γ, w σ := hunion
    _ ≤ ∑ γ : D.ι, Real.exp (-(2 * θ * D.len γ)) * ∑ σ, w σ :=
        Finset.sum_le_sum fun γ _ => hcontour γ
    _ = (∑ γ : D.ι, Real.exp (-(2 * θ * D.len γ))) * ∑ σ, w σ := by
        rw [Finset.sum_mul]
    _ ≤ (4 / 3) * (r ^ 4 * (4 - 3 * r) / (1 - r) ^ 2)
        * ∑ σ, w σ :=
        mul_le_mul_of_nonneg_right hgroup hW0

/-! ## The magnetization bound and the phase pair -/

/-- The supercriticality threshold: `θ ≥ ½·log 12` puts
`r = 3e^{−2θ}` below `1/4`. -/
theorem r_le_quarter {θ : ℝ} (hθ : (1 / 2) * Real.log 12 ≤ θ) :
    3 * Real.exp (-(2 * θ)) ≤ 1 / 4 := by
  have h2 : Real.exp (-(2 * θ)) ≤ Real.exp (-(Real.log 12)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-(Real.log 12)) = 1 / 12 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 12)]
    norm_num
  linarith

/-- Magnetization from the bad-event bound:
`⟨s⟩ = 1 − 2·P(s = −1) ≥ 203/216`. -/
theorem magnetization_ge {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (w s : Ω → ℝ) (hs : ∀ σ, s σ = 1 ∨ s σ = -1)
    (hbad : ∑ σ ∈ Finset.univ.filter (fun σ => s σ = -1), w σ
      ≤ (13 / 432) * ∑ σ, w σ) :
    (203 / 216) * ∑ σ, w σ ≤ ∑ σ, w σ * s σ := by
  classical
  have hsplitW := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun σ => s σ = -1) w
  have hsplitS := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun σ => s σ = -1) (fun σ => w σ * s σ)
  have hbadS : ∑ σ ∈ Finset.univ.filter (fun σ => s σ = -1),
      w σ * s σ
      = -∑ σ ∈ Finset.univ.filter (fun σ => s σ = -1), w σ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    rw [hσ.2]
    ring
  have hgoodS : ∑ σ ∈ Finset.univ.filter (fun σ => ¬ s σ = -1),
      w σ * s σ
      = ∑ σ ∈ Finset.univ.filter (fun σ => ¬ s σ = -1), w σ := by
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    rcases hs σ with h | h
    · rw [h, mul_one]
    · exact absurd h hσ.2
  linarith

/-- **The uniform Peierls magnetization bound**
(`thm:torsion-phase-coexistence` (ii), finite-volume core): for
`θ ≥ ½·log 12`, in every finite volume carrying a contour datum, the
plus-phase magnetization satisfies `⟨τ₀⟩ ≥ 203/216` — uniformly in
the volume. -/
theorem peierls_magnetization {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {w : Ω → ℝ} {θ : ℝ} {s : Ω → ℝ}
    (hw : ∀ σ, 0 ≤ w σ)
    (hs : ∀ σ, s σ = 1 ∨ s σ = -1)
    (D : ContourDatum Ω w θ
      (Finset.univ.filter (fun σ => s σ = -1)))
    (hθ : (1 / 2) * Real.log 12 ≤ θ) :
    (203 / 216) * ∑ σ, w σ ≤ ∑ σ, w σ * s σ := by
  have hr4 := r_le_quarter hθ
  have hr0 : (0:ℝ) ≤ 3 * Real.exp (-(2 * θ)) := by positivity
  have hr1 : 3 * Real.exp (-(2 * θ)) < 1 := by linarith
  have hW0 : 0 ≤ ∑ σ, w σ := Finset.sum_nonneg fun σ _ => hw σ
  have h1 := peierls_prob_bound hw D hr1
  have h2 := tail_le_at_quarter hr0 hr4
  have h3 : ∑ σ ∈ Finset.univ.filter (fun σ => s σ = -1), w σ
      ≤ (13 / 432) * ∑ σ, w σ := by
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right h2 hW0
  exact magnetization_ge w s hs h3

/-- **The deck-related minus phase**: pushing the weights forward by
the global flip negates the magnetization of every exchange-odd
observable, at equal total mass. -/
theorem flip_phase_neg {Ω : Type*} [Fintype Ω] (w s : Ω → ℝ)
    (ϑ : Equiv.Perm Ω) (hodd : ∀ σ, s (ϑ σ) = -s σ) :
    (∑ σ, w (ϑ σ) * s σ = -∑ σ, w σ * s σ)
    ∧ ∑ σ, w (ϑ σ) = ∑ σ, w σ := by
  constructor
  · have h1 : ∑ σ, w σ * s σ = ∑ σ, w (ϑ σ) * s (ϑ σ) :=
      (Equiv.sum_comp ϑ (fun σ => w σ * s σ)).symm
    rw [h1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hodd σ]
    ring
  · exact Equiv.sum_comp ϑ w

/-- **The symmetric mixture is torsion free**: the mean of every
exchange-odd observable in the equal mixture of the two deck-related
phases vanishes (`thm:torsion-phase-coexistence` (iii)). -/
theorem mixture_zero {mplus : ℝ} :
    (mplus + -mplus) / 2 = 0 := by ring

/-- **The thermodynamic-limit packaging** (the scoped compactness
step): uniformly bounded finite-volume magnetizations have a
subsequential limit `m⁺ ≥ 203/216`; together with the deck image
`m⁻ = −m⁺` this is the separated pair of orientation phases with
vanishing symmetric mixture. -/
theorem phase_pair_of_uniform_bound (a : ℕ → ℝ)
    (hlb : ∀ n, 203 / 216 ≤ a n) (hub : ∀ n, a n ≤ 1) :
    ∃ (m : ℝ) (φ : ℕ → ℕ), StrictMono φ
      ∧ Tendsto (a ∘ φ) atTop (nhds m)
      ∧ Tendsto (fun k => -(a (φ k))) atTop (nhds (-m))
      ∧ 203 / 216 ≤ m
      ∧ -m ≤ -(203 / 216)
      ∧ 0 < m - -m
      ∧ (m + -m) / 2 = 0 := by
  have hbd : Bornology.IsBounded (Set.Icc (203 / 216 : ℝ) 1) :=
    Metric.isBounded_Icc _ _
  have hmem : ∀ n, a n ∈ Set.Icc (203 / 216 : ℝ) 1 := fun n =>
    ⟨hlb n, hub n⟩
  obtain ⟨m, hmcl, φ, hφ, hconv⟩ :=
    tendsto_subseq_of_bounded hbd hmem
  rw [IsClosed.closure_eq isClosed_Icc] at hmcl
  refine ⟨m, φ, hφ, hconv, hconv.neg, hmcl.1, by linarith [hmcl.1],
    by
      have h1 : (203 / 216 : ℝ) ≤ m := hmcl.1
      linarith, by ring⟩

end NCG.Upstream
