/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.HyperbolicCostOptimizerComposition
import RenewalGeometry.Gravity.ThreeCostIdentification

/-!
# No transverse matching attraction under conservative blocking
(`thm:main-no-blocking-attractor`, `lem:supp-two-edge-schur`,
`eq:main-hyperbolic-cost`, `eq:main-conservative-blocking`,
`eq:main-hyperbolic-blocking`, `eq:main-homogeneous-block-map`;
emergent-spacetime manuscript)

Conservative blocking of two successive interval costs is
`(E₁ ⋆₀ E₂)(x,y) = inf_{z>0} {E₁(x,z) + E₂(z,y)}` (`conservativeBlock`).

* `twoEdgeCost_add_eq`: the two-edge Schur identity (`lem:supp-two-edge-schur`)
  in `(u,v)` form: for `E_i(x,y) = u_i (x²+y²) − 2 v_i x y + C (y² − x²)`,
  `E₁(x,z) + E₂(z,y) = E'(x,y) + (u₁+u₂)(z − z_*)²` with
  `z_* = (v₁ x + v₂ y)/(u₁+u₂)`, `u' = (u₁u₂ + (u₁² − v₁²))/(u₁+u₂)` and
  `v' = v₁v₂/(u₁+u₂)` (the `μ² = u_i² − v_i²` relation is a hypothesis);
* `conservativeBlock_eq_of_sq`: the infimum over `z > 0` of a quadratic
  `V + L (z − z_*)²` with `L ≥ 0`, `z_* > 0` is `V`;
* `hyperbolicCost_conservativeBlock`: **`eq:main-hyperbolic-blocking`**
  `E_{μ,θ₁,C} ⋆₀ E_{μ,θ₂,C} = E_{μ,θ₁+θ₂,C}` on `x, y > 0` for `μ > 0`,
  `θ₁, θ₂ > 0` and every twist `C`;
* `hyperbolicCost_foldl_conservativeBlock`: every finite sequence of
  homogeneous blockings gives `E_{μ, θ₀ + Σθ, C}`, so `μ² (= AB)`, `C`,
  `𝔇 = μ² − C²` and `Δ_rel = 1 − C²/μ²` are invariant
  (`hyperbolic_blocking_invariants`);
* `measuredQuadraticCost_eq_uv`, `measuredQuadraticCost_conservativeBlock_self`:
  **`eq:main-homogeneous-block-map`**: two identical midpoint intervals of
  duration `s` block to one midpoint interval of duration `2s` with
  `A' = A + Bs²/4`, `B' = AB/(A + Bs²/4)`, `C' = C`, under the standing
  assumption `0 < s√(B/A) < 2` (encoded as `B s² < 4A`);
* `blockMap_invariants`: `A'B' = AB`, `𝔇' = 𝔇`, `Δ_rel' = Δ_rel`, hence
  `Δ_rel > 0` stays strictly positive (`blockMap_relativeDefect_pos`);
* `relative_defect_unit_invariant`: invariance of `C²/(AB)` under changes of
  time/amplitude units and common positive action rescaling;
* `measuredQuadraticCost_eq_hyperbolicCost`: the dictionary
  `A/s ± Bs/4 = μ coth θ, μ csch θ` with `μ = √(AB)`,
  `θ = 2 artanh((s/2)√(B/A))` (`eq:main-relative-rank-defect`).

Scope note.  The blocking identities are stated on positive amplitudes
`x, y > 0` (the amplitude domain of the manuscript); the closing sentence of
`thm:main-no-blocking-attractor` about finite positive amplitude alphabets and
the low-temperature/grid limit is an analytic Laplace-method statement and is
**not** formalised here.
-/

namespace RenewalGeometry.ConservativeBlocking

open Real RenewalGeometry.HyperbolicCostOptimizer

/-- Conservative blocking `(E₁ ⋆₀ E₂)(x,y) = inf_{z>0} {E₁(x,z) + E₂(z,y)}`
(`eq:main-conservative-blocking`). -/
noncomputable def conservativeBlock (E₁ E₂ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  sInf ((fun z => E₁ x z + E₂ z y) '' Set.Ioi 0)

/-- A general symmetric two-edge cost `u (x² + y²) − 2 v x y + C (y² − x²)`
(the `(u,v)` form of `eq:main-hyperbolic-cost`, `u = μ coth θ`, `v = μ csch θ`). -/
def twoEdgeCost (u v C x y : ℝ) : ℝ := u * (x ^ 2 + y ^ 2) - 2 * v * x * y + C * (y ^ 2 - x ^ 2)

/-- The `(u,v)`-coefficients of the hyperbolic cost: `μ coth θ`. -/
noncomputable def uCoef (μ θ : ℝ) : ℝ := μ * (cosh θ / sinh θ)

/-- The `(u,v)`-coefficients of the hyperbolic cost: `μ csch θ`. -/
noncomputable def vCoef (μ θ : ℝ) : ℝ := μ * (1 / sinh θ)

/-- The hyperbolic cost is a two-edge cost with `u = μ coth θ`, `v = μ csch θ`. -/
theorem hyperbolicCost_eq_twoEdgeCost (μ θ C x y : ℝ) :
    hyperbolicCost μ θ C x y = twoEdgeCost (uCoef μ θ) (vCoef μ θ) C x y := by
  unfold hyperbolicCost twoEdgeCost uCoef vCoef; ring

/-- `u² − v² = μ²` for the hyperbolic coefficients (`θ ≠ 0`). -/
theorem uCoef_sq_sub_vCoef_sq (μ : ℝ) {θ : ℝ} (hθ : θ ≠ 0) :
    uCoef μ θ ^ 2 - vCoef μ θ ^ 2 = μ ^ 2 := by
  have hs : sinh θ ≠ 0 := sinh_ne_zero.mpr hθ
  unfold uCoef vCoef
  have hc : cosh θ ^ 2 = sinh θ ^ 2 + 1 := cosh_sq θ
  field_simp
  linear_combination μ ^ 2 * hc

/-- The blocked minimizer `z_* = (v₁ x + v₂ y)/(u₁ + u₂)` (`lem:supp-two-edge-schur`). -/
noncomputable def blockMinimizer (u₁ u₂ v₁ v₂ x y : ℝ) : ℝ := (v₁ * x + v₂ * y) / (u₁ + u₂)

/-- `lem:supp-two-edge-schur` (two-edge Schur identity, `(u,v)` form): with
`μ² = u₁² − v₁² = u₂² − v₂²`,
`E₁(x,z) + E₂(z,y) = E'(x,y) + (u₁+u₂)(z − z_*)²` where `E'` has
`u' = (u₁u₂ + μ²)/(u₁+u₂)`, `v' = v₁v₂/(u₁+u₂)` and the same twist `C`
(the two intermediate `C z²` terms cancel). -/
theorem twoEdgeCost_add_eq (u₁ u₂ v₁ v₂ C μsq x y z : ℝ) (hsum : u₁ + u₂ ≠ 0)
    (h₁ : u₁ ^ 2 - v₁ ^ 2 = μsq) (h₂ : u₂ ^ 2 - v₂ ^ 2 = μsq) :
    twoEdgeCost u₁ v₁ C x z + twoEdgeCost u₂ v₂ C z y
      = twoEdgeCost ((u₁ * u₂ + μsq) / (u₁ + u₂)) (v₁ * v₂ / (u₁ + u₂)) C x y
        + (u₁ + u₂) * (z - blockMinimizer u₁ u₂ v₁ v₂ x y) ^ 2 := by
  unfold twoEdgeCost blockMinimizer
  field_simp
  linear_combination (x ^ 2) * h₁ + (y ^ 2) * h₂

/-- The infimum over `z > 0` of `V + L (z − z_*)²` with `L ≥ 0` and `z_* > 0`
is `V`, attained at `z_*`. -/
theorem conservativeBlock_eq_of_sq (E₁ E₂ : ℝ → ℝ → ℝ) (x y V L zs : ℝ) (hL : 0 ≤ L)
    (hzs : 0 < zs) (h : ∀ z, E₁ x z + E₂ z y = V + L * (z - zs) ^ 2) :
    conservativeBlock E₁ E₂ x y = V := by
  unfold conservativeBlock
  apply IsLeast.csInf_eq
  refine ⟨⟨zs, hzs, ?_⟩, ?_⟩
  · show E₁ x zs + E₂ zs y = V
    rw [h]; simp
  rintro _ ⟨z, _, rfl⟩
  show V ≤ E₁ x z + E₂ z y
  rw [h]
  have : 0 ≤ L * (z - zs) ^ 2 := mul_nonneg hL (sq_nonneg _)
  linarith

/-- `u' = μ coth(θ₁+θ₂)`: the hyperbolic addition formula for the blocked
coefficient (`eq:main-hyperbolic-blocking`). -/
theorem uCoef_add (μ : ℝ) {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) :
    (uCoef μ θ₁ * uCoef μ θ₂ + μ ^ 2) / (uCoef μ θ₁ + uCoef μ θ₂)
      = uCoef μ (θ₁ + θ₂) := by
  have hs₁ : 0 < sinh θ₁ := sinh_pos_iff.mpr h₁
  have hs₂ : 0 < sinh θ₂ := sinh_pos_iff.mpr h₂
  have hs : 0 < sinh (θ₁ + θ₂) := sinh_pos_iff.mpr (by linarith)
  have hc₁ := cosh_pos θ₁
  have hc₂ := cosh_pos θ₂
  have hden : cosh θ₁ * sinh θ₂ + cosh θ₂ * sinh θ₁ ≠ 0 := by positivity
  unfold uCoef
  rw [sinh_add, cosh_add]
  field_simp
  ring

/-- `v' = μ csch(θ₁+θ₂)` (`eq:main-hyperbolic-blocking`). -/
theorem vCoef_add (μ : ℝ) {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) :
    vCoef μ θ₁ * vCoef μ θ₂ / (uCoef μ θ₁ + uCoef μ θ₂) = vCoef μ (θ₁ + θ₂) := by
  have hs₁ : 0 < sinh θ₁ := sinh_pos_iff.mpr h₁
  have hs₂ : 0 < sinh θ₂ := sinh_pos_iff.mpr h₂
  have hs : 0 < sinh (θ₁ + θ₂) := sinh_pos_iff.mpr (by linarith)
  have hc₁ := cosh_pos θ₁
  have hc₂ := cosh_pos θ₂
  have hden : cosh θ₁ * sinh θ₂ + cosh θ₂ * sinh θ₁ ≠ 0 := by positivity
  unfold uCoef vCoef
  rw [sinh_add]
  field_simp
  ring

/-- The two-edge hyperbolic sum completes the square around the positive
intermediate minimizer: for `μ > 0`, `θ₁, θ₂ > 0`,
`E_{μ,θ₁,C}(x,z) + E_{μ,θ₂,C}(z,y) = E_{μ,θ₁+θ₂,C}(x,y) + (u₁+u₂)(z − z_*)²`. -/
theorem hyperbolicCost_add_eq (μ θ₁ θ₂ C x y z : ℝ) (h₁ : 0 < θ₁) (h₂ : 0 < θ₂)
    (hμ : 0 < μ) :
    hyperbolicCost μ θ₁ C x z + hyperbolicCost μ θ₂ C z y
      = hyperbolicCost μ (θ₁ + θ₂) C x y
        + (uCoef μ θ₁ + uCoef μ θ₂)
          * (z - blockMinimizer (uCoef μ θ₁) (uCoef μ θ₂) (vCoef μ θ₁) (vCoef μ θ₂) x y) ^ 2 := by
  have hu₁ : 0 < uCoef μ θ₁ := by
    unfold uCoef; exact mul_pos hμ (div_pos (cosh_pos _) (sinh_pos_iff.mpr h₁))
  have hu₂ : 0 < uCoef μ θ₂ := by
    unfold uCoef; exact mul_pos hμ (div_pos (cosh_pos _) (sinh_pos_iff.mpr h₂))
  rw [hyperbolicCost_eq_twoEdgeCost, hyperbolicCost_eq_twoEdgeCost, hyperbolicCost_eq_twoEdgeCost,
    twoEdgeCost_add_eq (uCoef μ θ₁) (uCoef μ θ₂) (vCoef μ θ₁) (vCoef μ θ₂) C (μ ^ 2) x y z
      (by positivity) (uCoef_sq_sub_vCoef_sq μ h₁.ne') (uCoef_sq_sub_vCoef_sq μ h₂.ne'),
    uCoef_add μ h₁ h₂, vCoef_add μ h₁ h₂]

/-- The blocked minimizer is positive on positive endpoints
(`lem:supp-two-edge-schur`). -/
theorem hyperbolic_blockMinimizer_pos (μ θ₁ θ₂ x y : ℝ) (h₁ : 0 < θ₁) (h₂ : 0 < θ₂)
    (hμ : 0 < μ) (hx : 0 < x) (hy : 0 < y) :
    0 < blockMinimizer (uCoef μ θ₁) (uCoef μ θ₂) (vCoef μ θ₁) (vCoef μ θ₂) x y := by
  have hs₁ : 0 < sinh θ₁ := sinh_pos_iff.mpr h₁
  have hs₂ : 0 < sinh θ₂ := sinh_pos_iff.mpr h₂
  have hc₁ := cosh_pos θ₁
  have hc₂ := cosh_pos θ₂
  unfold blockMinimizer uCoef vCoef
  positivity

/-- **`eq:main-hyperbolic-blocking`** (`thm:main-no-blocking-attractor`): for
`μ > 0`, `θ₁, θ₂ > 0`, any twist `C`, and positive amplitudes `x, y > 0`,
`(E_{μ,θ₁,C} ⋆₀ E_{μ,θ₂,C})(x,y) = E_{μ,θ₁+θ₂,C}(x,y)`. -/
theorem hyperbolicCost_conservativeBlock (μ θ₁ θ₂ C : ℝ) (h₁ : 0 < θ₁) (h₂ : 0 < θ₂)
    (hμ : 0 < μ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    conservativeBlock (hyperbolicCost μ θ₁ C) (hyperbolicCost μ θ₂ C) x y
      = hyperbolicCost μ (θ₁ + θ₂) C x y := by
  have hu₁ : 0 < uCoef μ θ₁ := by
    unfold uCoef; exact mul_pos hμ (div_pos (cosh_pos _) (sinh_pos_iff.mpr h₁))
  have hu₂ : 0 < uCoef μ θ₂ := by
    unfold uCoef; exact mul_pos hμ (div_pos (cosh_pos _) (sinh_pos_iff.mpr h₂))
  exact conservativeBlock_eq_of_sq _ _ x y _ _ _ (by positivity)
    (hyperbolic_blockMinimizer_pos μ θ₁ θ₂ x y h₁ h₂ hμ hx hy)
    (fun z => hyperbolicCost_add_eq μ θ₁ θ₂ C x y z h₁ h₂ hμ)

/-- Blocking depends only on the values of the two costs on positive
amplitudes. -/
theorem conservativeBlock_congr {E₁ E₁' E₂ E₂' : ℝ → ℝ → ℝ} {x y : ℝ}
    (h₁ : ∀ z, 0 < z → E₁ x z = E₁' x z) (h₂ : ∀ z, 0 < z → E₂ z y = E₂' z y) :
    conservativeBlock E₁ E₂ x y = conservativeBlock E₁' E₂' x y := by
  unfold conservativeBlock
  congr 1
  apply Set.EqOn.image_eq
  intro z hz
  simp only [h₁ z hz, h₂ z hz]


/-- Every finite sequence of homogeneous blockings (`List.foldl`) of hyperbolic
costs with common `μ > 0` and twist `C` and positive angles `θ₀, θ ∈ L`, started
from any cost `E₀` agreeing with `E_{μ,θ₀,C}` on positive amplitudes, yields
`E_{μ, θ₀ + Σ L, C}` on positive amplitudes (`thm:main-no-blocking-attractor`,
"invariant under every finite sequence of homogeneous blockings"). -/
theorem hyperbolicCost_foldl_conservativeBlock (μ C : ℝ) (hμ : 0 < μ) (L : List ℝ)
    (hL : ∀ θ ∈ L, 0 < θ) :
    ∀ (θ₀ : ℝ), 0 < θ₀ → ∀ E₀ : ℝ → ℝ → ℝ,
      (∀ x y : ℝ, 0 < x → 0 < y → E₀ x y = hyperbolicCost μ θ₀ C x y) →
      ∀ x y : ℝ, 0 < x → 0 < y →
        (L.foldl (fun E θ => conservativeBlock E (hyperbolicCost μ θ C)) E₀) x y
          = hyperbolicCost μ (θ₀ + L.sum) C x y := by
  induction L with
  | nil => intro θ₀ _ E₀ hE x y hx hy; simpa using hE x y hx hy
  | cons θ L ih =>
      intro θ₀ h₀ E₀ hE x y hx hy
      have hθ : 0 < θ := hL θ (List.mem_cons_self ..)
      have hL' : ∀ θ' ∈ L, 0 < θ' := fun θ' h => hL θ' (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons, List.sum_cons]
      rw [show θ₀ + (θ + L.sum) = θ₀ + θ + L.sum by ring]
      refine ih hL' (θ₀ + θ) (by linarith) _ ?_ x y hx hy
      intro x y hx hy
      rw [conservativeBlock_congr (E₁' := hyperbolicCost μ θ₀ C) (E₂' := hyperbolicCost μ θ C)
        (fun z hz => hE x z hx hz) (fun _ _ => rfl)]
      exact hyperbolicCost_conservativeBlock μ θ₀ θ C h₀ hθ hμ hx hy

/-- The invariants of `thm:main-no-blocking-attractor`: after any finite sequence of
homogeneous blockings the cost is again `E_{μ,θ',C}` with the *same* `μ` and `C`,
so `AB = μ²`, `C`, `𝔇 = μ² − C²` (`rankDefect` of the `(u+v, u−v, C)` parameters,
which is `u² − v² − C²`) are unchanged; this is the identity content of the
statement (`hyperbolicCost_foldl_conservativeBlock` fixes `θ' = θ₀ + Σ L`). -/
theorem hyperbolic_blocking_invariants (μ C : ℝ) (hμ : 0 < μ) (L : List ℝ)
    (hL : ∀ θ ∈ L, 0 < θ) (θ₀ : ℝ) (h₀ : 0 < θ₀) :
    ∃ θ' : ℝ, 0 < θ' ∧
      (∀ x y : ℝ, 0 < x → 0 < y →
        (L.foldl (fun E θ => conservativeBlock E (hyperbolicCost μ θ C))
          (hyperbolicCost μ θ₀ C)) x y = hyperbolicCost μ θ' C x y) ∧
      rankDefect (uCoef μ θ' + vCoef μ θ') (uCoef μ θ' - vCoef μ θ') C
        = rankDefect (uCoef μ θ₀ + vCoef μ θ₀) (uCoef μ θ₀ - vCoef μ θ₀) C ∧
      rankDefect (uCoef μ θ' + vCoef μ θ') (uCoef μ θ' - vCoef μ θ') C = μ ^ 2 - C ^ 2 := by
  have hsum : 0 ≤ L.sum := List.sum_nonneg (fun θ h => (hL θ h).le)
  have hθ' : (0:ℝ) < θ₀ + L.sum := by linarith
  refine ⟨θ₀ + L.sum, hθ', fun x y hx hy =>
    hyperbolicCost_foldl_conservativeBlock μ C hμ L hL θ₀ h₀ _ (fun _ _ _ _ => rfl) x y hx hy,
    ?_, ?_⟩
  · unfold rankDefect
    have e1 := uCoef_sq_sub_vCoef_sq μ hθ'.ne'
    have e2 := uCoef_sq_sub_vCoef_sq μ h₀.ne'
    linear_combination e1 - e2
  · unfold rankDefect
    have e1 := uCoef_sq_sub_vCoef_sq μ hθ'.ne'
    linear_combination e1

/-! ### The midpoint block map `eq:main-homogeneous-block-map` -/

/-- The midpoint cost `E_s` of `eq:main-measured-quadratic-cost` is the two-edge
cost with `u = A/s + Bs/4`, `v = A/s − Bs/4` (`subsec:supp-homogeneous-blocking`). -/
theorem measuredQuadraticCost_eq_twoEdgeCost (A B C s x y : ℝ) (hs : s ≠ 0) :
    measuredQuadraticCost A B C s x y
      = twoEdgeCost (A / s + B * s / 4) (A / s - B * s / 4) C x y := by
  unfold measuredQuadraticCost twoEdgeCost
  field_simp
  ring

/-- `u² − v² = AB` for the midpoint coefficients. -/
theorem midpoint_u_sq_sub_v_sq (A B s : ℝ) (hs : s ≠ 0) :
    (A / s + B * s / 4) ^ 2 - (A / s - B * s / 4) ^ 2 = A * B := by
  field_simp; ring

/-- The blocked midpoint parameter `A' = A + Bs²/4` (`eq:main-homogeneous-block-map`). -/
noncomputable def blockA (A B s : ℝ) : ℝ := A + B * s ^ 2 / 4

/-- The blocked midpoint parameter `B' = AB/(A + Bs²/4)` (`eq:main-homogeneous-block-map`). -/
noncomputable def blockB (A B s : ℝ) : ℝ := A * B / (A + B * s ^ 2 / 4)

/-- Two identical midpoint intervals of duration `s` sum to the midpoint interval of
duration `2s` with parameters `(A', B', C)` plus a nonnegative square in the
intermediate amplitude: the exact two-edge identity behind
`eq:main-homogeneous-block-map` (`A > 0`, `B > 0`, `s > 0`). -/
theorem measuredQuadraticCost_add_self_eq (A B C s x y z : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hs : 0 < s) :
    measuredQuadraticCost A B C s x z + measuredQuadraticCost A B C s z y
      = measuredQuadraticCost (blockA A B s) (blockB A B s) C (2 * s) x y
        + (A / s + B * s / 4 + (A / s + B * s / 4))
          * (z - blockMinimizer (A / s + B * s / 4) (A / s + B * s / 4)
              (A / s - B * s / 4) (A / s - B * s / 4) x y) ^ 2 := by
  have hu : 0 < A / s + B * s / 4 := by positivity
  have hblock : 0 < A + B * s ^ 2 / 4 := by positivity
  rw [measuredQuadraticCost_eq_twoEdgeCost _ _ _ _ _ _ hs.ne',
    measuredQuadraticCost_eq_twoEdgeCost _ _ _ _ _ _ hs.ne',
    measuredQuadraticCost_eq_twoEdgeCost _ _ _ _ _ _ (by positivity),
    twoEdgeCost_add_eq _ _ _ _ C (A * B) x y z (by positivity)
      (midpoint_u_sq_sub_v_sq A B s hs.ne') (midpoint_u_sq_sub_v_sq A B s hs.ne')]
  have e1 : ((A / s + B * s / 4) * (A / s + B * s / 4) + A * B)
      / (A / s + B * s / 4 + (A / s + B * s / 4))
      = blockA A B s / (2 * s) + blockB A B s * (2 * s) / 4 := by
    unfold blockA blockB; field_simp; ring
  have e2 : (A / s - B * s / 4) * (A / s - B * s / 4)
      / (A / s + B * s / 4 + (A / s + B * s / 4))
      = blockA A B s / (2 * s) - blockB A B s * (2 * s) / 4 := by
    unfold blockA blockB; field_simp; ring
  rw [e1, e2]

/-- **`eq:main-homogeneous-block-map`** (`thm:main-no-blocking-attractor`): under the
standing assumption `0 < s√(B/A) < 2` (encoded as `B s² < 4A` with `A, B, s > 0`),
conservative blocking of two identical midpoint intervals of duration `s` is the
midpoint interval of duration `2s` with `A' = A + Bs²/4`, `B' = AB/(A + Bs²/4)`,
`C' = C`, on positive amplitudes. -/
theorem measuredQuadraticCost_conservativeBlock_self (A B C s : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hs : 0 < s) (hsmall : B * s ^ 2 < 4 * A) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    conservativeBlock (measuredQuadraticCost A B C s) (measuredQuadraticCost A B C s) x y
      = measuredQuadraticCost (blockA A B s) (blockB A B s) C (2 * s) x y := by
  have hu : 0 < A / s + B * s / 4 := by positivity
  have hv : 0 < A / s - B * s / 4 := by
    rw [sub_pos, div_lt_div_iff₀ (by norm_num) hs]; nlinarith
  refine conservativeBlock_eq_of_sq _ _ x y _ _ _ (by positivity) ?_
    (fun z => measuredQuadraticCost_add_self_eq A B C s x y z hA hB hs)
  unfold blockMinimizer
  positivity

/-- The block map preserves `AB`, `C`, `𝔇 = AB − C²` and `Δ_rel = 𝔇/(AB)`
(`thm:main-no-blocking-attractor`). -/
theorem blockMap_invariants (A B C s : ℝ) (hA : 0 < A) (hB : 0 < B) :
    blockA A B s * blockB A B s = A * B ∧
      rankDefect (blockA A B s) (blockB A B s) C = rankDefect A B C ∧
      rankDefect (blockA A B s) (blockB A B s) C / (blockA A B s * blockB A B s)
        = rankDefect A B C / (A * B) := by
  have hblock : A + B * s ^ 2 / 4 ≠ 0 := by positivity
  have h1 : blockA A B s * blockB A B s = A * B := by
    unfold blockA blockB; field_simp
  refine ⟨h1, ?_, ?_⟩
  · unfold rankDefect; rw [h1]
  · unfold rankDefect; rw [h1]

/-- The block map keeps the parameters positive, and a strictly positive relative
defect `Δ_rel > 0` stays strictly positive after blocking: the matched surface
`Δ_rel = 0` has no basin of attraction (`thm:main-no-blocking-attractor`). -/
theorem blockMap_relativeDefect_pos (A B C s : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hpos : 0 < rankDefect A B C / (A * B)) :
    0 < blockA A B s ∧ 0 < blockB A B s ∧
      0 < rankDefect (blockA A B s) (blockB A B s) C / (blockA A B s * blockB A B s) := by
  refine ⟨by unfold blockA; positivity, by unfold blockB; positivity, ?_⟩
  rw [(blockMap_invariants A B C s hA hB).2.2]; exact hpos

/-- Invariance of the scale-free mismatch `C²/(AB)` under a change of amplitude and
time units `x = r x̃`, `s = ℓ s̃` and a common positive action rescaling by `d`:
`Ã = r²A/(dℓ)`, `B̃ = r²ℓB/d`, `C̃ = r²C/d` (`thm:main-no-blocking-attractor`,
"even after changes of time/amplitude units or common positive rescaling"). -/
theorem relative_defect_unit_invariant (A B C r ℓ d : ℝ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hr : r ≠ 0) (hℓ : ℓ ≠ 0) (hd : d ≠ 0) :
    (r ^ 2 * C / d) ^ 2 / ((r ^ 2 * A / (d * ℓ)) * (r ^ 2 * ℓ * B / d)) = C ^ 2 / (A * B) := by
  field_simp

/-! ### The hyperbolic dictionary `eq:main-relative-rank-defect` -/

/-- `exp (2 artanh x) = (1 + x)/(1 − x)` for `|x| < 1`. -/
theorem exp_two_mul_artanh {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    Real.exp (2 * artanh x) = (1 + x) / (1 - x) := by
  rw [two_mul, Real.exp_add, exp_artanh hx, Real.mul_self_sqrt]
  exact div_nonneg (by linarith [hx.1]) (by linarith [hx.2])

/-- The dictionary `μ coth θ = A/s + Bs/4` and `μ csch θ = A/s − Bs/4` for
`μ = √(AB)`, `θ = 2 artanh((s/2)√(B/A))`, under `0 < s√(B/A) < 2`
(encoded as `B s² < 4A`). -/
theorem midpoint_dictionary (A B s : ℝ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s)
    (hsmall : B * s ^ 2 < 4 * A) :
    uCoef (Real.sqrt (A * B)) (2 * artanh (s / 2 * Real.sqrt (B / A))) = A / s + B * s / 4 ∧
      vCoef (Real.sqrt (A * B)) (2 * artanh (s / 2 * Real.sqrt (B / A))) = A / s - B * s / 4 := by
  set x₀ := s / 2 * Real.sqrt (B / A) with hx₀
  have hBA : 0 < B / A := div_pos hB hA
  have hx₀pos : 0 < x₀ := by rw [hx₀]; positivity
  have hx₀sq : x₀ ^ 2 = s ^ 2 * B / (4 * A) := by
    rw [hx₀, mul_pow, Real.sq_sqrt hBA.le]; field_simp; ring
  have hx₀lt : x₀ < 1 := by
    have : x₀ ^ 2 < 1 := by
      rw [hx₀sq, div_lt_one (by positivity)]; nlinarith
    nlinarith
  have hmem : x₀ ∈ Set.Ioo (-1) 1 := ⟨by linarith, hx₀lt⟩
  have hE : Real.exp (2 * artanh x₀) = (1 + x₀) / (1 - x₀) := exp_two_mul_artanh hmem
  have h1x : 1 - x₀ ≠ 0 := by linarith
  have h1x' : 1 + x₀ ≠ 0 := by linarith
  have hμ : Real.sqrt (A * B) = A / s * (2 * x₀) := by
    have h1 : A / s * (2 * x₀) = A * Real.sqrt (B / A) := by
      rw [hx₀]; field_simp
    rw [h1, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have h2 : A * Real.sqrt (B / A) * (A * Real.sqrt (B / A))
        = A * A * (Real.sqrt (B / A) * Real.sqrt (B / A)) := by ring
    rw [h2, Real.mul_self_sqrt hBA.le]
    field_simp
  have hBs : B * s / 4 = A / s * (x₀ ^ 2) := by
    rw [hx₀sq]; field_simp
  have hEpos : 0 < Real.exp (2 * artanh x₀) := Real.exp_pos _
  have hsinh' : sinh (2 * artanh x₀) = 2 * x₀ / (1 - x₀ ^ 2) := by
    rw [Real.sinh_eq, Real.exp_neg, hE]
    have : (1:ℝ) - x₀ ^ 2 = (1 - x₀) * (1 + x₀) := by ring
    rw [this]
    field_simp
    ring
  have hcosh' : cosh (2 * artanh x₀) = (1 + x₀ ^ 2) / (1 - x₀ ^ 2) := by
    rw [Real.cosh_eq, Real.exp_neg, hE]
    have : (1:ℝ) - x₀ ^ 2 = (1 - x₀) * (1 + x₀) := by ring
    rw [this]
    field_simp
    ring
  have h1x2 : 1 - x₀ ^ 2 ≠ 0 := by nlinarith
  constructor
  · unfold uCoef; rw [hsinh', hcosh', hμ, hBs]; field_simp
  · unfold vCoef; rw [hsinh', hμ, hBs]; field_simp

/-- `eq:main-hyperbolic-cost`: on the standing domain the midpoint cost equals the
hyperbolic cost `E_{μ,θ,C}` with `μ = √(AB)`, `θ = 2 artanh((s/2)√(B/A))`. -/
theorem measuredQuadraticCost_eq_hyperbolicCost (A B C s x y : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hs : 0 < s) (hsmall : B * s ^ 2 < 4 * A) :
    measuredQuadraticCost A B C s x y
      = hyperbolicCost (Real.sqrt (A * B)) (2 * artanh (s / 2 * Real.sqrt (B / A))) C x y := by
  obtain ⟨hu, hv⟩ := midpoint_dictionary A B s hA hB hs hsmall
  rw [hyperbolicCost_eq_twoEdgeCost, hu, hv, measuredQuadraticCost_eq_twoEdgeCost _ _ _ _ _ _ hs.ne']

end RenewalGeometry.ConservativeBlocking
