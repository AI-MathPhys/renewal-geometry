/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.FiniteLaplaceSandwich
import RenewalGeometry.Action.ConservativeBlockingHyperbolicCost
import RenewalGeometry.Action.FiniteTwistRetention

/-!
# Finite-grid, finite-temperature conservative blocking and its controlled limit
(`thm:main-no-blocking-attractor`, closing sentence, second half;
`eq:supp-finite-block-error`; emergent-spacetime manuscript)

Intermediate positive amplitudes are integrated over a finite grid `G ⊂ (0, R]` with the
uniform (probability-normalized) average.  One finite blocking step at temperature `ε > 0` is
`(E₁ ⋆^ε_G E₂)(x,y) = -ε log (m⁻¹ ∑_{z ∈ G} exp (-(E₁(x,z) + E₂(z,y))/ε))`, `m = #G`
(`softBlock`), the finite analogue of the conservative blocking `⋆₀`; the `n`-fold finite
blocked cost `E^ε_{G,n}` is `finiteBlockedCost`.

* `exp_neg_finiteBlockedCost_div`: `exp(-E^ε_{G,n}/ε) = m · Lⁿ` on the grid, for the
  subprobability kernel `L(x,y) = m⁻¹ exp(-E(x,y)/ε)`; i.e. `E^ε_{G,n} = -ε log Lⁿ - ε log m`.
* `hyperbolicKernel_eq_diag_conj`, `finiteBlockedCost_twist`: the grid kernel of
  `E_{μ,θ,C}` is `D_C L₀ D_C⁻¹` with a symmetric positive untwisted `L₀`, so the finite blocked
  cost carries exactly the endpoint twist `C` (`eq:supp-finite-twist-read`).
* `hyperbolicCost_le_finiteBlockedCost`, `finiteBlockedCost_le_sharp`,
  `finite_block_error`: **`eq:supp-finite-block-error`**
  `0 ≤ E^ε_{G,n}(x,y) − E_{μ,nθ,C}(x,y) ≤ 4u(n−1)d² + ε(n−1) log m`
  (`u = μ coth θ`, `d` the covering error of the grid on `(0,R]`, `x, y ∈ (0,R]`),
  with the sharper constant `2u` proved.
* `finite_block_error_schedule`: at fixed total angle `Θ` (`θ = Θ/n`), with
  `d_n ≤ n⁻²`, `m_n ≤ K n²` and `ε_n = n⁻³/(1 + log n)`, the error is `≤ M n⁻²`.
* `probeRelativeDefect`, `probeRelativeDefect_measuredQuadraticCost`,
  `tendsto_probeRelativeDefect`: the three-probe reconstruction of `Δ_rel` from the costs
  `E(u,u)`, `E(u,v)`, `E(v,u)` (`prop:supp-three-costs`) is exact on measured quadratic costs
  and continuous on the calibrated range `AB ≠ 0`.
* `finite_blocking_relativeDefect_limit`: **the controlled low-temperature/grid limit**: for
  `A, B, S > 0`, `BS² < 4A`, the three-probe relative defect of the finite blocked costs of the
  total interval tends to `Δ_rel = (AB − C²)/(AB)`; if `Δ_rel > 0` it stays above `Δ_rel/2`
  for all sufficiently fine finite blockings.
* `exists_grid_schedule`: non-vacuity: uniform grids `{k/n²} ∩ (0,R]` satisfy the schedule.

Normalization (disclosed).  The manuscript does not define `E^ε_{F,n}` explicitly.  The bound
`eq:supp-finite-block-error`, with lower bound `0` and entropy term `ε(n−1) log m`, holds for
the probability-normalized average over the `n−1` intermediate grid amplitudes (equivalently,
`E^ε_{F,n} = −ε log (m Lⁿ)` for the subprobability kernel `L = m⁻¹ e^{−E/ε}`).  For
`−ε log Lⁿ` itself the error interval is `[ε log m, 4u(n−1)d² + εn log m]`, and for the
unnormalized counting sum the lower bound `0` fails.
-/

namespace RenewalGeometry.FiniteBlockingGrid

open Real Filter Topology Matrix
open RenewalGeometry.FiniteLaplace RenewalGeometry.ConservativeBlocking
  RenewalGeometry.HyperbolicCostOptimizer

/-! ### Finite blocking -/

/-- One finite conservative blocking step at temperature `ε` on the grid `G`:
`-ε log (m⁻¹ ∑_{z∈G} exp(-(E₁(x,z) + E₂(z,y))/ε))`. -/
noncomputable def softBlock (ε : ℝ) (G : Finset ℝ) (E₁ E₂ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  softMin ε G (fun z => E₁ x z + E₂ z y)

/-- The `n`-fold finite blocked cost `E^ε_{G,n}` of an interval cost `E` (meaningful for
`n ≥ 1`; the value at `n = 0` is set to `E`). -/
noncomputable def finiteBlockedCost (ε : ℝ) (G : Finset ℝ) (E : ℝ → ℝ → ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0 => E
  | 1 => E
  | (n + 2) => softBlock ε G (finiteBlockedCost ε G E (n + 1)) E

theorem finiteBlockedCost_one (ε : ℝ) (G : Finset ℝ) (E : ℝ → ℝ → ℝ) :
    finiteBlockedCost ε G E 1 = E := rfl

theorem finiteBlockedCost_succ (ε : ℝ) (G : Finset ℝ) (E : ℝ → ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    finiteBlockedCost ε G E (n + 1) = softBlock ε G (finiteBlockedCost ε G E n) E := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

/-- The subprobability grid kernel `L(x,y) = m⁻¹ exp(-E(x,y)/ε)`, `m = #G`. -/
noncomputable def gridKernel (ε : ℝ) (G : Finset ℝ) (E : ℝ → ℝ → ℝ) : Matrix G G ℝ :=
  fun x y => ((G.card : ℝ))⁻¹ * Real.exp (-E x y / ε)

/-- The finite blocked cost is the free energy of the kernel power:
`exp(-E^ε_{G,n}(x,y)/ε) = m · Lⁿ(x,y)` for grid points `x, y` and `n ≥ 1`. -/
theorem exp_neg_finiteBlockedCost_div {ε : ℝ} (hε : ε ≠ 0) (G : Finset ℝ) (E : ℝ → ℝ → ℝ)
    {n : ℕ} (hn : 1 ≤ n) (x y : G) :
    Real.exp (-finiteBlockedCost ε G E n x y / ε) = (G.card : ℝ) * (gridKernel ε G E ^ n) x y := by
  have hG : G.Nonempty := ⟨x, x.2⟩
  have hc : (G.card : ℝ) ≠ 0 := by exact_mod_cast hG.card_pos.ne'
  induction n, hn using Nat.le_induction generalizing y with
  | base =>
      rw [finiteBlockedCost_one, pow_one, gridKernel]
      field_simp
  | succ n hn ih =>
      rw [finiteBlockedCost_succ ε G E hn, softBlock, exp_neg_softMin_div hε hG, pow_succ,
        Matrix.mul_apply, ← Finset.sum_coe_sort G, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      have h1 : Real.exp (-(finiteBlockedCost ε G E n x z + E z y) / ε)
          = Real.exp (-finiteBlockedCost ε G E n x z / ε) * Real.exp (-E z y / ε) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h1, ih z, gridKernel]
      field_simp

/-! ### Elementary facts on the hyperbolic coefficients -/

theorem uCoef_pos {μ θ : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) : 0 < uCoef μ θ := by
  unfold uCoef; exact mul_pos hμ (div_pos (cosh_pos _) (sinh_pos_iff.mpr hθ))

theorem vCoef_pos {μ θ : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) : 0 < vCoef μ θ := by
  unfold vCoef; exact mul_pos hμ (div_pos one_pos (sinh_pos_iff.mpr hθ))

theorem vCoef_le_uCoef {μ θ : ℝ} (hμ : 0 ≤ μ) (hθ : 0 < θ) : vCoef μ θ ≤ uCoef μ θ := by
  unfold uCoef vCoef
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (one_le_cosh θ) (sinh_pos_iff.mpr hθ).le) hμ

/-- `θ ↦ μ coth θ` is antitone on `(0, ∞)`. -/
theorem uCoef_anti {μ a b : ℝ} (hμ : 0 ≤ μ) (ha : 0 < a) (hab : a ≤ b) :
    uCoef μ b ≤ uCoef μ a := by
  unfold uCoef
  refine mul_le_mul_of_nonneg_left ?_ hμ
  have hsa := sinh_pos_iff.mpr ha
  have hsb := sinh_pos_iff.mpr (lt_of_lt_of_le ha hab)
  rw [div_le_div_iff₀ hsb hsa]
  have : 0 ≤ sinh (b - a) := Real.sinh_nonneg_iff.mpr (by linarith)
  rw [Real.sinh_sub] at this
  linarith

/-- `μ coth t ≤ μ cosh T / t` for `0 < t ≤ T`. -/
theorem uCoef_le_div {μ t T : ℝ} (hμ : 0 ≤ μ) (ht : 0 < t) (htT : t ≤ T) :
    uCoef μ t ≤ μ * cosh T / t := by
  unfold uCoef
  have hs : t ≤ sinh t := Real.self_le_sinh_iff.mpr ht.le
  have hc : cosh t ≤ cosh T := Real.cosh_le_cosh.mpr (by
    rw [abs_of_pos ht, abs_of_pos (lt_of_lt_of_le ht htT)]; exact htT)
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hμ
  calc cosh t / sinh t ≤ cosh t / t := div_le_div_of_nonneg_left (cosh_pos t).le ht hs
    _ ≤ cosh T / t := div_le_div_of_nonneg_right hc ht.le

/-- The blocked minimizer lies below `max x y` when `0 < vᵢ ≤ uᵢ`. -/
theorem blockMinimizer_le_max {u₁ u₂ v₁ v₂ x y : ℝ} (hu₁ : 0 < u₁) (hu₂ : 0 < u₂)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (h₁ : v₁ ≤ u₁) (h₂ : v₂ ≤ u₂) (hx : 0 ≤ x) (_hy : 0 ≤ y) :
    blockMinimizer u₁ u₂ v₁ v₂ x y ≤ max x y := by
  unfold blockMinimizer
  rw [div_le_iff₀ (by linarith)]
  have hxm : x ≤ max x y := le_max_left _ _
  have hym : y ≤ max x y := le_max_right _ _
  have hm : 0 ≤ max x y := le_trans hx hxm
  nlinarith [mul_le_mul_of_nonneg_left hxm hv₁, mul_le_mul_of_nonneg_left hym hv₂,
    mul_le_mul_of_nonneg_right h₁ hm, mul_le_mul_of_nonneg_right h₂ hm]

/-! ### `eq:supp-finite-block-error` -/

/-- **Lower half of `eq:supp-finite-block-error`**: the finite blocked cost never undercuts the
exact blocked cost, `E_{μ,nθ,C} ≤ E^ε_{G,n}` (all real endpoints, `n ≥ 1`). -/
theorem hyperbolicCost_le_finiteBlockedCost {μ θ C ε : ℝ} (hμ : 0 < μ) (hθ : 0 < θ)
    (hε : 0 < ε) {G : Finset ℝ} (hG : G.Nonempty) {n : ℕ} (hn : 1 ≤ n) (x y : ℝ) :
    hyperbolicCost μ (n * θ) C x y ≤ finiteBlockedCost ε G (hyperbolicCost μ θ C) n x y := by
  induction n, hn using Nat.le_induction generalizing y with
  | base => simp [finiteBlockedCost_one]
  | succ n hn ih =>
      rw [finiteBlockedCost_succ ε G _ hn, softBlock]
      refine le_softMin hε hG _ fun z _ => ?_
      have hnθ : 0 < (n : ℝ) * θ := mul_pos (by exact_mod_cast hn) hθ
      have key := hyperbolicCost_add_eq μ (n * θ) θ C x y z hnθ hθ hμ
      have hsq : 0 ≤ (uCoef μ (n * θ) + uCoef μ θ) * (z - blockMinimizer (uCoef μ (n * θ))
          (uCoef μ θ) (vCoef μ (n * θ)) (vCoef μ θ) x y) ^ 2 :=
        mul_nonneg (add_pos (uCoef_pos hμ hnθ) (uCoef_pos hμ hθ)).le (sq_nonneg _)
      have hcast : ((n + 1 : ℕ) : ℝ) * θ = n * θ + θ := by push_cast; ring
      rw [hcast]
      have := ih z
      linarith

/-- **Upper half of `eq:supp-finite-block-error`, sharp form**: if `G ⊂ (0,R]` covers `(0,R]`
with error `d`, then for endpoints `x, y ∈ (0,R]` and `n ≥ 1`,
`E^ε_{G,n}(x,y) ≤ E_{μ,nθ,C}(x,y) + 2u(n−1)d² + ε(n−1) log m`, `u = μ coth θ`. -/
theorem finiteBlockedCost_le_sharp {μ θ C ε R d : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hε : 0 < ε)
    {G : Finset ℝ} (hGsub : ∀ g ∈ G, 0 < g ∧ g ≤ R)
    (hcover : ∀ z, 0 < z → z ≤ R → ∃ g ∈ G, |z - g| ≤ d) {n : ℕ} (hn : 1 ≤ n)
    {x y : ℝ} (hx : 0 < x) (hxR : x ≤ R) (hy : 0 < y) (hyR : y ≤ R) :
    finiteBlockedCost ε G (hyperbolicCost μ θ C) n x y
      ≤ hyperbolicCost μ (n * θ) C x y + 2 * uCoef μ θ * ((n : ℝ) - 1) * d ^ 2
        + ε * ((n : ℝ) - 1) * Real.log G.card := by
  induction n, hn using Nat.le_induction generalizing y with
  | base => simp [finiteBlockedCost_one]
  | succ n hn ih =>
      rw [finiteBlockedCost_succ ε G _ hn, softBlock]
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hnθ : 0 < (n : ℝ) * θ := mul_pos (by linarith) hθ
      set zs := blockMinimizer (uCoef μ (n * θ)) (uCoef μ θ) (vCoef μ (n * θ)) (vCoef μ θ) x y
        with hzs
      have hzpos : 0 < zs := hyperbolic_blockMinimizer_pos μ (n * θ) θ x y hnθ hθ hμ hx hy
      have hzR : zs ≤ R := by
        refine le_trans (blockMinimizer_le_max (uCoef_pos hμ hnθ) (uCoef_pos hμ hθ)
          (vCoef_pos hμ hnθ).le (vCoef_pos hμ hθ).le (vCoef_le_uCoef hμ.le hnθ)
          (vCoef_le_uCoef hμ.le hθ) hx.le hy.le) (max_le hxR hyR)
      obtain ⟨g, hgG, hgd⟩ := hcover zs hzpos hzR
      obtain ⟨hg, hgR⟩ := hGsub g hgG
      have hstep := softMin_le hε (fun z => finiteBlockedCost ε G (hyperbolicCost μ θ C) n x z
        + hyperbolicCost μ θ C z y) hgG
      have hih := ih hg hgR
      have key := hyperbolicCost_add_eq μ (n * θ) θ C x y g hnθ hθ hμ
      rw [← hzs] at key
      have hanti : uCoef μ (n * θ) ≤ uCoef μ θ :=
        uCoef_anti hμ.le hθ (by nlinarith)
      have hsq : (g - zs) ^ 2 ≤ d ^ 2 := by
        have : |g - zs| ≤ d := by rw [abs_sub_comm]; exact hgd
        have hd : 0 ≤ d := le_trans (abs_nonneg _) this
        have h2 := abs_le.mp this
        nlinarith [h2.1, h2.2]
      have hu := uCoef_pos hμ hθ
      have hun := uCoef_pos hμ hnθ
      have hbound : (uCoef μ (n * θ) + uCoef μ θ) * (g - zs) ^ 2 ≤ 2 * uCoef μ θ * d ^ 2 := by
        calc (uCoef μ (n * θ) + uCoef μ θ) * (g - zs) ^ 2 ≤ (2 * uCoef μ θ) * (g - zs) ^ 2 :=
              mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
          _ ≤ 2 * uCoef μ θ * d ^ 2 := mul_le_mul_of_nonneg_left hsq (by linarith)
      have hcast : ((n + 1 : ℕ) : ℝ) * θ = n * θ + θ := by push_cast; ring
      have hcast' : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
      rw [hcast, hcast']
      nlinarith

/-- **`eq:supp-finite-block-error`** (`thm:main-no-blocking-attractor`): for a grid
`G ⊂ (0,R]` of cardinality `m` covering `(0,R]` with error `d`, temperature `ε > 0`,
`μ, θ > 0`, endpoints `x, y ∈ (0,R]` and `n ≥ 1` blocked intervals,
`0 ≤ E^ε_{G,n}(x,y) − E_{μ,nθ,C}(x,y) ≤ 4u(n−1)d² + ε(n−1) log m`, `u = μ coth θ`. -/
theorem finite_block_error {μ θ C ε R d : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hε : 0 < ε)
    {G : Finset ℝ} (hGsub : ∀ g ∈ G, 0 < g ∧ g ≤ R)
    (hcover : ∀ z, 0 < z → z ≤ R → ∃ g ∈ G, |z - g| ≤ d) {n : ℕ} (hn : 1 ≤ n)
    {x y : ℝ} (hx : 0 < x) (hxR : x ≤ R) (hy : 0 < y) (hyR : y ≤ R) :
    0 ≤ finiteBlockedCost ε G (hyperbolicCost μ θ C) n x y - hyperbolicCost μ (n * θ) C x y ∧
      finiteBlockedCost ε G (hyperbolicCost μ θ C) n x y - hyperbolicCost μ (n * θ) C x y
        ≤ 4 * uCoef μ θ * ((n : ℝ) - 1) * d ^ 2 + ε * ((n : ℝ) - 1) * Real.log G.card := by
  obtain ⟨g, hg, -⟩ := hcover x hx hxR
  have hG : G.Nonempty := ⟨g, hg⟩
  refine ⟨sub_nonneg.2 (hyperbolicCost_le_finiteBlockedCost hμ hθ hε hG hn x y), ?_⟩
  have h := finiteBlockedCost_le_sharp (C := C) hμ hθ hε hGsub hcover hn hx hxR hy hyR
  have hn' : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have : 2 * uCoef μ θ * ((n : ℝ) - 1) * d ^ 2 ≤ 4 * uCoef μ θ * ((n : ℝ) - 1) * d ^ 2 := by
    have := uCoef_pos hμ hθ
    have : 0 ≤ uCoef μ θ * ((n : ℝ) - 1) * d ^ 2 := by positivity
    nlinarith
  linarith

/-! ### Exact twist retention for the finite blocked cost -/

/-- The grid kernel of `E_{μ,θ,C}` is `D_C L₀ D_C⁻¹` with `D_C = diag(e^{C x²/ε})` and the
untwisted kernel `L₀` of `E_{μ,θ,0}` (`eq:supp-finite-twist-similarity`). -/
theorem hyperbolicKernel_eq_diag_conj (ε μ θ C : ℝ) (G : Finset ℝ) :
    gridKernel ε G (hyperbolicCost μ θ C)
      = diagonal (fun x : G => Real.exp (C * (x : ℝ) ^ 2 / ε)) *
          gridKernel ε G (hyperbolicCost μ θ 0) *
          diagonal (fun x : G => (Real.exp (C * (x : ℝ) ^ 2 / ε))⁻¹) := by
  ext x y
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, gridKernel]
  rw [← Real.exp_neg]
  have : -hyperbolicCost μ θ C x y / ε
      = C * (x : ℝ) ^ 2 / ε + -hyperbolicCost μ θ 0 x y / ε + -(C * (y : ℝ) ^ 2 / ε) := by
    unfold hyperbolicCost; ring
  rw [this, Real.exp_add, Real.exp_add]
  ring

/-- The untwisted grid kernel is symmetric. -/
theorem untwistedKernel_symm (ε μ θ : ℝ) (G : Finset ℝ) :
    (gridKernel ε G (hyperbolicCost μ θ 0))ᵀ = gridKernel ε G (hyperbolicCost μ θ 0) := by
  ext x y
  simp only [Matrix.transpose_apply, gridKernel]
  congr 3
  unfold hyperbolicCost; ring

/-- **Exact twist retention for the finite blocked cost** (`thm:main-no-blocking-attractor`,
"the endpoint twist `C` is retained exactly under finite blocking"): on a finite positive grid,
for every `n ≥ 1` and distinct grid amplitudes `x ≠ y`, the measured endpoint twist
`ε/(2(x²−y²)) log(Lⁿ(x,y)/Lⁿ(y,x))` of the blocked kernel is exactly `C`, equivalently
`E^ε_{G,n}(y,x) − E^ε_{G,n}(x,y) = 2C(x² − y²)`. -/
theorem finiteBlockedCost_twist {ε : ℝ} (hε : ε ≠ 0) (μ θ C : ℝ) {G : Finset ℝ}
    (hGpos : ∀ g ∈ G, 0 < g) {n : ℕ} (hn : 1 ≤ n) (x y : G) (hxy : x ≠ y) :
    ε / (2 * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2)) *
        Real.log ((gridKernel ε G (hyperbolicCost μ θ C) ^ n) x y /
          (gridKernel ε G (hyperbolicCost μ θ C) ^ n) y x) = C ∧
      finiteBlockedCost ε G (hyperbolicCost μ θ C) n y x
        - finiteBlockedCost ε G (hyperbolicCost μ θ C) n x y
        = 2 * C * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2) := by
  have hG : G.Nonempty := ⟨x, x.2⟩
  have hc : (0 : ℝ) < G.card := by exact_mod_cast hG.card_pos
  have hpos : ∀ a b, 0 < gridKernel ε G (hyperbolicCost μ θ 0) a b := fun a b =>
    mul_pos (inv_pos.2 hc) (Real.exp_pos _)
  have ht := (FiniteTwistRetention.finite_twist_retention G hGpos ε C hε
    (gridKernel ε G (hyperbolicCost μ θ 0)) (untwistedKernel_symm ε μ θ G) hpos n hn).2 x y hxy
  rw [← hyperbolicKernel_eq_diag_conj] at ht
  refine ⟨ht, ?_⟩
  set F := finiteBlockedCost ε G (hyperbolicCost μ θ C) n
  have h1 : (gridKernel ε G (hyperbolicCost μ θ C) ^ n) x y = Real.exp (-F x y / ε) / G.card := by
    rw [exp_neg_finiteBlockedCost_div hε G _ hn x y]; field_simp
  have h2 : (gridKernel ε G (hyperbolicCost μ θ C) ^ n) y x = Real.exp (-F y x / ε) / G.card := by
    rw [exp_neg_finiteBlockedCost_div hε G _ hn y x]; field_simp
  have hratio : (gridKernel ε G (hyperbolicCost μ θ C) ^ n) x y /
      (gridKernel ε G (hyperbolicCost μ θ C) ^ n) y x = Real.exp ((F y x - F x y) / ε) := by
    rw [h1, h2, div_div_div_cancel_right₀ hc.ne', ← Real.exp_sub]
    congr 1; ring
  rw [hratio, Real.log_exp] at ht
  have hx2 : (x : ℝ) ^ 2 - (y : ℝ) ^ 2 ≠ 0 := by
    intro h
    apply hxy
    apply Subtype.ext
    have hx := hGpos x x.2
    have hy := hGpos y y.2
    nlinarith [sq_nonneg ((x : ℝ) - y), sq_nonneg ((x : ℝ) + y)]
  field_simp at ht
  linear_combination ht

/-! ### The fine-blocking schedule -/

/-- The temperature schedule `ε_n = n⁻³/(1 + log n)`. -/
noncomputable def scheduleTemp (n : ℕ) : ℝ := 1 / ((n : ℝ) ^ 3 * (1 + Real.log n))

theorem scheduleTemp_pos {n : ℕ} (hn : 1 ≤ n) : 0 < scheduleTemp n := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hN
  unfold scheduleTemp; positivity

/-- The interior-energy term of the schedule: `4 u_n (n−1) (n⁻²)² ≤ 4 μ cosh Θ / Θ · n⁻²`
for `u_n = μ coth(Θ/n)`. -/
theorem schedule_energy_term {μ Θ : ℝ} (hμ : 0 < μ) (hΘ : 0 < Θ) {n : ℕ} (hn : 1 ≤ n) :
    4 * uCoef μ (Θ / n) * ((n : ℝ) - 1) * (1 / (n : ℝ) ^ 2) ^ 2
      ≤ 4 * μ * cosh Θ / Θ / (n : ℝ) ^ 2 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have ht : 0 < Θ / n := div_pos hΘ hN0
  have htT : Θ / n ≤ Θ := div_le_self hΘ.le hN
  have hu := uCoef_le_div hμ.le ht htT
  have hu0 := uCoef_pos hμ ht
  have hc : 0 ≤ μ * cosh Θ := mul_nonneg hμ.le (cosh_pos _).le
  have heq : μ * cosh Θ / (Θ / n) = μ * cosh Θ / Θ * n := by field_simp
  rw [heq] at hu
  calc 4 * uCoef μ (Θ / n) * ((n : ℝ) - 1) * (1 / (n : ℝ) ^ 2) ^ 2
      ≤ 4 * (μ * cosh Θ / Θ * n) * (n : ℝ) * (1 / (n : ℝ) ^ 2) ^ 2 := by
        have h4 : 0 ≤ (1 / (n : ℝ) ^ 2) ^ 2 := by positivity
        refine mul_le_mul_of_nonneg_right ?_ h4
        exact mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
    _ = 4 * μ * cosh Θ / Θ / (n : ℝ) ^ 2 := by field_simp

/-- The entropy term of the schedule: `ε_n (n−1) log m ≤ (log K + 2) n⁻²` for
`1 ≤ m ≤ K n²`, `K ≥ 1`. -/
theorem schedule_entropy_term {K : ℝ} (hK : 1 ≤ K) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmK : (m : ℝ) ≤ K * (n : ℝ) ^ 2) :
    scheduleTemp n * ((n : ℝ) - 1) * Real.log m ≤ (Real.log K + 2) / (n : ℝ) ^ 2 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hL : 0 ≤ Real.log n := Real.log_nonneg hN
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hlm' : Real.log m ≤ Real.log K + 2 * Real.log n := by
    have := Real.log_le_log (by linarith) hmK
    rwa [Real.log_mul (by linarith) (by positivity), Real.log_pow, Nat.cast_ofNat] at this
  have hε := scheduleTemp_pos hn
  calc scheduleTemp n * ((n : ℝ) - 1) * Real.log m
      ≤ scheduleTemp n * (n : ℝ) * (Real.log K + 2 * Real.log n) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hε.le) hlm' hlm (by positivity)
    _ = (Real.log K + 2 * Real.log n) / ((n : ℝ) ^ 2 * (1 + Real.log n)) := by
        unfold scheduleTemp; field_simp
    _ ≤ (Real.log K + 2) / (n : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 ≤ Real.log K * Real.log n := mul_nonneg hlK hL
        have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
        nlinarith [mul_nonneg this hn2.le]

/-- **The fine-blocking schedule** (`thm:main-no-blocking-attractor`, proof): at fixed total
angle `Θ = nθ`, with covering error `d_n = n⁻²`, cardinality `m_n ≤ K n²` and temperature
`ε_n = n⁻³/(1 + log n)`, the finite blocked cost of the total interval is within
`(4μ cosh Θ/Θ + log K + 2) n⁻²` of the exact cost `E_{μ,Θ,C}` on `(0,R]²`. -/
theorem finite_block_error_schedule {μ Θ C R K : ℝ} (hμ : 0 < μ) (hΘ : 0 < Θ) (hK : 1 ≤ K)
    {G : Finset ℝ} {n : ℕ} (hn : 1 ≤ n) (hGsub : ∀ g ∈ G, 0 < g ∧ g ≤ R)
    (hcover : ∀ z, 0 < z → z ≤ R → ∃ g ∈ G, |z - g| ≤ 1 / (n : ℝ) ^ 2)
    (hcard : (G.card : ℝ) ≤ K * (n : ℝ) ^ 2) {x y : ℝ} (hx : 0 < x) (hxR : x ≤ R)
    (hy : 0 < y) (hyR : y ≤ R) :
    |finiteBlockedCost (scheduleTemp n) G (hyperbolicCost μ (Θ / n) C) n x y
        - hyperbolicCost μ Θ C x y|
      ≤ (4 * μ * cosh Θ / Θ + Real.log K + 2) / (n : ℝ) ^ 2 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hθ : 0 < Θ / n := div_pos hΘ hN0
  have hnθ : (n : ℝ) * (Θ / n) = Θ := by field_simp
  obtain ⟨h0, h1⟩ := finite_block_error (C := C) hμ hθ (scheduleTemp_pos hn) hGsub hcover hn
    hx hxR hy hyR
  rw [hnθ] at h0 h1
  obtain ⟨g, hg, -⟩ := hcover x hx hxR
  have hm : 1 ≤ G.card := Finset.card_pos.2 ⟨g, hg⟩
  have e1 := schedule_energy_term hμ hΘ hn
  have e2 := schedule_entropy_term hK hn hm hcard
  rw [abs_of_nonneg h0]
  have : (4 * μ * cosh Θ / Θ + Real.log K + 2) / (n : ℝ) ^ 2
      = 4 * μ * cosh Θ / Θ / (n : ℝ) ^ 2 + (Real.log K + 2) / (n : ℝ) ^ 2 := by ring
  rw [this]
  linarith

/-- A sequence within `M n⁻²` of `L` for all `n ≥ 1` converges to `L`. -/
theorem tendsto_of_abs_sub_le_div_sq {a : ℕ → ℝ} {L M : ℝ}
    (h : ∀ n, 1 ≤ n → |a n - L| ≤ M / (n : ℝ) ^ 2) : Tendsto a atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
    (eventually_atTop.2 ⟨1, fun n hn => by simpa [Real.norm_eq_abs] using h n hn⟩) ?_
  exact tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)

/-! ### Three-probe reconstruction of the relative defect -/

/-- Three-probe reconstruction of `B` from `E(u,u)` (`eq:supp-three-cost-identification`). -/
noncomputable def probeB (S u : ℝ) (E : ℝ → ℝ → ℝ) : ℝ := E u u / (S * u ^ 2)

/-- Three-probe reconstruction of `C` from `E(u,v)`, `E(v,u)`. -/
noncomputable def probeC (u v : ℝ) (E : ℝ → ℝ → ℝ) : ℝ := (E u v - E v u) / (2 * (v ^ 2 - u ^ 2))

/-- Three-probe reconstruction of `A`. -/
noncomputable def probeA (S u v : ℝ) (E : ℝ → ℝ → ℝ) : ℝ :=
  S / (2 * (v - u) ^ 2) * (E u v + E v u - 2 * probeB S u E * S * ((u + v) / 2) ^ 2)

/-- The reconstructed scale-free mismatch `Δ̂_rel = (ÂB̂ − Ĉ²)/(ÂB̂)`. -/
noncomputable def probeRelativeDefect (S u v : ℝ) (E : ℝ → ℝ → ℝ) : ℝ :=
  rankDefect (probeA S u v E) (probeB S u E) (probeC u v E) / (probeA S u v E * probeB S u E)

/-- The three-probe reconstruction is exact on measured quadratic costs. -/
theorem probe_measuredQuadraticCost {A B C S u v : ℝ} (hS : 0 < S) (hu : 0 < u) (hv : 0 < v)
    (huv : u ≠ v) :
    probeA S u v (measuredQuadraticCost A B C S) = A ∧
      probeB S u (measuredQuadraticCost A B C S) = B ∧
      probeC u v (measuredQuadraticCost A B C S) = C ∧
      probeRelativeDefect S u v (measuredQuadraticCost A B C S) = rankDefect A B C / (A * B) := by
  obtain ⟨h1, h2, h3⟩ := measuredQuadraticCost_three_cost_identification A B C S u v hS hu hv huv
  have hB : probeB S u (measuredQuadraticCost A B C S) = B := h1.symm
  have hC : probeC u v (measuredQuadraticCost A B C S) = C := h2.symm
  have hA : probeA S u v (measuredQuadraticCost A B C S) = A := by
    unfold probeA; rw [hB]; exact h3.symm
  refine ⟨hA, hB, hC, ?_⟩
  unfold probeRelativeDefect; rw [hA, hB, hC]

/-- **Continuity of the three-probe reconstruction** on the calibrated range `ÂB̂ ≠ 0`: if the
three probe values converge, so does the reconstructed relative defect. -/
theorem tendsto_probeRelativeDefect {S u v : ℝ} {Es : ℕ → ℝ → ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (huu : Tendsto (fun n => Es n u u) atTop (𝓝 (E u u)))
    (huv : Tendsto (fun n => Es n u v) atTop (𝓝 (E u v)))
    (hvu : Tendsto (fun n => Es n v u) atTop (𝓝 (E v u)))
    (hAB : probeA S u v E * probeB S u E ≠ 0) :
    Tendsto (fun n => probeRelativeDefect S u v (Es n)) atTop
      (𝓝 (probeRelativeDefect S u v E)) := by
  have hB : Tendsto (fun n => probeB S u (Es n)) atTop (𝓝 (probeB S u E)) :=
    huu.div_const _
  have hC : Tendsto (fun n => probeC u v (Es n)) atTop (𝓝 (probeC u v E)) :=
    (huv.sub hvu).div_const _
  have hA : Tendsto (fun n => probeA S u v (Es n)) atTop (𝓝 (probeA S u v E)) :=
    (((huv.add hvu).sub (((hB.const_mul 2).mul_const S).mul_const (((u + v) / 2) ^ 2)))).const_mul _
  unfold probeRelativeDefect rankDefect
  exact ((hA.mul hB).sub (hC.pow 2)).div (hA.mul hB) hAB

/-! ### The controlled low-temperature/grid limit -/

/-- The total hyperbolic angle `Θ = 2 artanh((S/2)√(B/A))` of a measured interval of duration
`S` (`eq:main-relative-rank-defect`). -/
noncomputable def totalAngle (A B S : ℝ) : ℝ := 2 * artanh (S / 2 * Real.sqrt (B / A))

theorem totalAngle_pos {A B S : ℝ} (hA : 0 < A) (hB : 0 < B) (hS : 0 < S)
    (hsmall : B * S ^ 2 < 4 * A) : 0 < totalAngle A B S := by
  unfold totalAngle
  have hBA : 0 < B / A := div_pos hB hA
  set x₀ := S / 2 * Real.sqrt (B / A) with hx₀
  have hx₀pos : 0 < x₀ := by rw [hx₀]; positivity
  have hx₀sq : x₀ ^ 2 = S ^ 2 * B / (4 * A) := by
    rw [hx₀, mul_pow, Real.sq_sqrt hBA.le]; field_simp; ring
  have hx₀lt : x₀ < 1 := by
    have : x₀ ^ 2 < 1 := by
      rw [hx₀sq, div_lt_one (by positivity)]; nlinarith
    nlinarith
  have := Real.artanh_pos ⟨hx₀pos, hx₀lt⟩
  linarith

/-- **The controlled low-temperature/grid limit of `thm:main-no-blocking-attractor`.**
Let `A, B, S > 0` with `0 < S√(B/A) < 2` (`BS² < 4A`), any twist `C`, `μ = √(AB)` and total
angle `Θ = 2 artanh((S/2)√(B/A))`, so that the exact cost of the total interval is the measured
cost `E_S = E_{μ,Θ,C}`.  Block the total interval into `n` elementary intervals of angle
`Θ/n`, integrating the intermediate positive amplitudes over grids `G_n ⊂ (0,R]` of covering
error `n⁻²` and cardinality `≤ K n²` at temperature `ε_n = n⁻³/(1 + log n)`.  Then for probes
`0 < u ≠ v ≤ R` the three-probe reconstructed relative defect of the finite blocked costs
converges to `Δ_rel = (AB − C²)/(AB)`; in particular a positive initial `Δ_rel` stays above
`Δ_rel/2 > 0` for every sufficiently fine finite blocking. -/
theorem finite_blocking_relativeDefect_limit {A B C S R K u v : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hS : 0 < S) (hsmall : B * S ^ 2 < 4 * A) (hK : 1 ≤ K) (hu : 0 < u) (huR : u ≤ R)
    (hv : 0 < v) (hvR : v ≤ R) (huv : u ≠ v) (G : ℕ → Finset ℝ)
    (hGsub : ∀ n, 1 ≤ n → ∀ g ∈ G n, 0 < g ∧ g ≤ R)
    (hcover : ∀ n, 1 ≤ n → ∀ z, 0 < z → z ≤ R → ∃ g ∈ G n, |z - g| ≤ 1 / (n : ℝ) ^ 2)
    (hcard : ∀ n, 1 ≤ n → ((G n).card : ℝ) ≤ K * (n : ℝ) ^ 2) :
    Tendsto (fun n : ℕ => probeRelativeDefect S u v
        (finiteBlockedCost (scheduleTemp n) (G n)
          (hyperbolicCost (Real.sqrt (A * B)) (totalAngle A B S / n) C) n))
      atTop (𝓝 (rankDefect A B C / (A * B))) ∧
    (0 < rankDefect A B C / (A * B) →
      ∀ᶠ n : ℕ in atTop, rankDefect A B C / (A * B) / 2 < probeRelativeDefect S u v
        (finiteBlockedCost (scheduleTemp n) (G n)
          (hyperbolicCost (Real.sqrt (A * B)) (totalAngle A B S / n) C) n)) := by
  have hμ : 0 < Real.sqrt (A * B) := Real.sqrt_pos.2 (mul_pos hA hB)
  have hΘ := totalAngle_pos hA hB hS hsmall
  have hprobe : ∀ p q : ℝ, 0 < p → p ≤ R → 0 < q → q ≤ R →
      Tendsto (fun n : ℕ => finiteBlockedCost (scheduleTemp n) (G n)
          (hyperbolicCost (Real.sqrt (A * B)) (totalAngle A B S / n) C) n p q) atTop
        (𝓝 (measuredQuadraticCost A B C S p q)) := by
    intro p q hp hpR hq hqR
    rw [measuredQuadraticCost_eq_hyperbolicCost A B C S p q hA hB hS hsmall]
    exact tendsto_of_abs_sub_le_div_sq fun n hn =>
      finite_block_error_schedule hμ hΘ hK hn (hGsub n hn) (hcover n hn) (hcard n hn)
        hp hpR hq hqR
  obtain ⟨hA', hB', -, hD⟩ := probe_measuredQuadraticCost (A := A) (B := B) (C := C) hS hu hv huv
  have hT := tendsto_probeRelativeDefect (S := S) (hprobe u u hu huR hu huR)
    (hprobe u v hu huR hv hvR) (hprobe v u hv hvR hu huR)
    (by rw [hA', hB']; exact (mul_pos hA hB).ne')
  rw [hD] at hT
  refine ⟨hT, fun hpos => hT.eventually (lt_mem_nhds (by linarith))⟩

/-! ### Non-vacuity: uniform grids satisfy the schedule -/

/-- Uniform grids `G_n = {min(k/n², R) : 1 ≤ k ≤ ⌈R n²⌉}` lie in `(0,R]`, cover `(0,R]` with
error `n⁻²` and have cardinality `≤ (R+1) n²`. -/
theorem exists_grid_schedule {R : ℝ} (hR : 0 < R) :
    ∃ G : ℕ → Finset ℝ, ∀ n, 1 ≤ n →
      (∀ g ∈ G n, 0 < g ∧ g ≤ R) ∧
      (∀ z, 0 < z → z ≤ R → ∃ g ∈ G n, |z - g| ≤ 1 / (n : ℝ) ^ 2) ∧
      ((G n).card : ℝ) ≤ (R + 1) * (n : ℝ) ^ 2 := by
  refine ⟨fun n => (Finset.Icc 1 ⌈R * (n : ℝ) ^ 2⌉₊).image
    (fun k : ℕ => min ((k : ℝ) / (n : ℝ) ^ 2) R), fun n hn => ?_⟩
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hn21 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hg
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    exact ⟨lt_min (by positivity) hR, min_le_right _ _⟩
  · intro z hz hzR
    have hzn : 0 < z * (n : ℝ) ^ 2 := by positivity
    refine ⟨min ((⌈z * (n : ℝ) ^ 2⌉₊ : ℝ) / (n : ℝ) ^ 2) R,
      Finset.mem_image.2 ⟨⌈z * (n : ℝ) ^ 2⌉₊, Finset.mem_Icc.2 ⟨Nat.one_le_ceil_iff.2 hzn,
        Nat.ceil_mono (by nlinarith)⟩, rfl⟩, ?_⟩
    have h1 : z * (n : ℝ) ^ 2 ≤ (⌈z * (n : ℝ) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈z * (n : ℝ) ^ 2⌉₊ : ℝ) < z * (n : ℝ) ^ 2 + 1 := Nat.ceil_lt_add_one hzn.le
    have h3 : z ≤ (⌈z * (n : ℝ) ^ 2⌉₊ : ℝ) / (n : ℝ) ^ 2 := by rw [le_div_iff₀ hn2]; exact h1
    have h4 : (⌈z * (n : ℝ) ^ 2⌉₊ : ℝ) / (n : ℝ) ^ 2 ≤ z + 1 / (n : ℝ) ^ 2 := by
      rw [div_le_iff₀ hn2, add_mul, one_div, inv_mul_cancel₀ hn2.ne']; linarith
    have h5 : z ≤ min ((⌈z * (n : ℝ) ^ 2⌉₊ : ℝ) / (n : ℝ) ^ 2) R := le_min h3 hzR
    have h6 : min ((⌈z * (n : ℝ) ^ 2⌉₊ : ℝ) / (n : ℝ) ^ 2) R ≤ z + 1 / (n : ℝ) ^ 2 :=
      le_trans (min_le_left _ _) h4
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have hcard := Finset.card_image_le (s := Finset.Icc 1 ⌈R * (n : ℝ) ^ 2⌉₊)
      (f := fun k : ℕ => min ((k : ℝ) / (n : ℝ) ^ 2) R)
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    have hc : ((Finset.image (fun k : ℕ => min ((k : ℝ) / (n : ℝ) ^ 2) R)
        (Finset.Icc 1 ⌈R * (n : ℝ) ^ 2⌉₊)).card : ℝ) ≤ (⌈R * (n : ℝ) ^ 2⌉₊ : ℝ) := by
      exact_mod_cast hcard
    have h2 : (⌈R * (n : ℝ) ^ 2⌉₊ : ℝ) < R * (n : ℝ) ^ 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    nlinarith

/-- Non-vacuity of `finite_blocking_relativeDefect_limit`: `A = B = 1`, `C = 1/2`, `S = 1`
(so `Δ_rel = 3/4 > 0`), probes `1/2, 1`, uniform grids on `(0,1]` with `K = 2`. -/
example : ∃ G : ℕ → Finset ℝ,
    Tendsto (fun n : ℕ => probeRelativeDefect 1 (1 / 2) 1
        (finiteBlockedCost (scheduleTemp n) (G n)
          (hyperbolicCost (Real.sqrt (1 * 1)) (totalAngle 1 1 1 / n) (1 / 2)) n))
      atTop (𝓝 (rankDefect 1 1 (1 / 2) / (1 * 1))) ∧
    ∀ᶠ n : ℕ in atTop, rankDefect 1 1 (1 / 2) / (1 * 1) / 2 < probeRelativeDefect 1 (1 / 2) 1
        (finiteBlockedCost (scheduleTemp n) (G n)
          (hyperbolicCost (Real.sqrt (1 * 1)) (totalAngle 1 1 1 / n) (1 / 2)) n) := by
  obtain ⟨G, hG⟩ := exists_grid_schedule (R := 1) one_pos
  have h := finite_blocking_relativeDefect_limit (A := 1) (B := 1) (C := 1 / 2) (S := 1) (R := 1)
    (K := 1 + 1) (u := 1 / 2) (v := 1) one_pos one_pos one_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) one_pos le_rfl (by norm_num) G (fun n hn => (hG n hn).1)
    (fun n hn => (hG n hn).2.1) (fun n hn => (hG n hn).2.2)
  exact ⟨G, h.1, h.2 (by unfold rankDefect; norm_num)⟩

end RenewalGeometry.FiniteBlockingGrid
