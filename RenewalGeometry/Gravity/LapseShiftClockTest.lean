/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Necessary lapse--shift clock condition for harmonic shadowing
  (`prop:supp-exact-clock-test`, `eq:supp-exact-rate-norm`,
  `eq:supp-exact-rate-necessary`; emergent-spacetime manuscript)

Two ingredients of the paper's proof are formalized.

* ADM first-jet identities at `N = 1`, `β = 0`
  (`admMetric00_hasDerivAt`, `admMetric0i_hasDerivAt`): with
  `g₀₀ = -N² + γ_{ij} βⁱ βʲ` and `g₀ᵢ = γ_{ij} βʲ`, at an instant where
  `N = 1` and `β = 0` one has `∂ₜ g₀₀ = -2 ∂ₜ N` and
  `∂ₜ g₀ᵢ = γ_{ij} ∂ₜ βʲ`.  Hence a topology controlling the initial
  first time derivative of the metric controls the lapse--shift clock rate.
* The rate-norm squeeze (`rate_norm_components_tendsto_zero`,
  `lapse_shift_clock_condition`): if
  `‖λ_t‖² = a⁻² ‖u_A‖² + a⁻⁴ ‖u_W‖²` (`eq:supp-exact-rate-norm`) and
  `‖λ_t‖ → 0` along the regulator family, then necessarily
  `a⁻¹ ‖u_A‖ → 0` and `a⁻² ‖u_W‖ → 0` (`eq:supp-exact-rate-necessary`).
  No sign, smallness or limit assumption on `a(h)` is needed for this step,
  and the conclusion is independent of the instantaneous electric
  coefficient, which does not enter the identity.

The physical premise "first-jet shadowing forces `‖λ_t‖ → 0`" is taken as
the hypothesis `hl` of `lapse_shift_clock_condition`; it is the paper's
identification of the multiplier rate `λ_t` with the lapse--shift first
jet, which the ADM identities express.
-/

open scoped BigOperators Topology

namespace RenewalGeometry

/-! ### ADM first-jet identities -/

/-- The ADM time-time metric component `g₀₀ = -N² + γ_{ij} βⁱ βʲ`. -/
def admMetric00 (N : ℝ → ℝ) (γ : ℝ → Fin 3 → Fin 3 → ℝ)
    (β : ℝ → Fin 3 → ℝ) (t : ℝ) : ℝ :=
  -(N t) ^ 2 + ∑ i, ∑ j, γ t i j * β t i * β t j

/-- The ADM time-space metric component `g₀ᵢ = γ_{ij} βʲ`. -/
def admMetric0i (γ : ℝ → Fin 3 → Fin 3 → ℝ) (β : ℝ → Fin 3 → ℝ)
    (i : Fin 3) (t : ℝ) : ℝ :=
  ∑ j, γ t i j * β t j

/-- At an instant with `N = 1` and `β = 0`, `∂ₜ g₀₀ = -2 ∂ₜ N`. -/
theorem admMetric00_hasDerivAt (N : ℝ → ℝ) (γ : ℝ → Fin 3 → Fin 3 → ℝ)
    (β : ℝ → Fin 3 → ℝ) (N' : ℝ) (γ' : Fin 3 → Fin 3 → ℝ) (β' : Fin 3 → ℝ)
    (t₀ : ℝ) (hN : HasDerivAt N N' t₀)
    (hγ : ∀ i j, HasDerivAt (fun t => γ t i j) (γ' i j) t₀)
    (hβ : ∀ j, HasDerivAt (fun t => β t j) (β' j) t₀)
    (hN0 : N t₀ = 1) (hβ0 : ∀ j, β t₀ j = 0) :
    HasDerivAt (admMetric00 N γ β) (-2 * N') t₀ := by
  have hsq : HasDerivAt (fun t => -(N t) ^ 2) (-(2 * N t₀ * N')) t₀ := by
    have := (hN.pow 2).neg
    refine this.congr_deriv ?_
    push_cast
    ring
  have hsum : HasDerivAt (fun t => ∑ i, ∑ j, γ t i j * β t i * β t j)
      (∑ i, ∑ j, ((γ' i j * β t₀ i + γ t₀ i j * β' i) * β t₀ j +
        γ t₀ i j * β t₀ i * β' j)) t₀ := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact ((hγ i j).mul (hβ i)).mul (hβ j)
  have h := hsq.add hsum
  refine h.congr_deriv ?_
  simp only [hβ0, hN0, mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  ring

/-- At an instant with `β = 0`, `∂ₜ g₀ᵢ = γ_{ij} ∂ₜ βʲ`. -/
theorem admMetric0i_hasDerivAt (γ : ℝ → Fin 3 → Fin 3 → ℝ)
    (β : ℝ → Fin 3 → ℝ) (γ' : Fin 3 → Fin 3 → ℝ) (β' : Fin 3 → ℝ)
    (t₀ : ℝ)
    (hγ : ∀ i j, HasDerivAt (fun t => γ t i j) (γ' i j) t₀)
    (hβ : ∀ j, HasDerivAt (fun t => β t j) (β' j) t₀)
    (hβ0 : ∀ j, β t₀ j = 0) (i : Fin 3) :
    HasDerivAt (admMetric0i γ β i) (∑ j, γ t₀ i j * β' j) t₀ := by
  have hsum : HasDerivAt (fun t => ∑ j, γ t i j * β t j)
      (∑ j, (γ' i j * β t₀ j + γ t₀ i j * β' j)) t₀ := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact (hγ i j).mul (hβ j)
  refine hsum.congr_deriv ?_
  simp only [hβ0, mul_zero, zero_add]

/-! ### The rate-norm squeeze -/

/-- If `‖λ‖² = (‖u_A‖/a)² + (‖u_W‖/a²)²` and `‖λ‖ → 0`, then both graded
components tend to zero (`eq:supp-exact-rate-necessary`). -/
theorem rate_norm_components_tendsto_zero {ι : Type*} (l : Filter ι)
    (a nA nW nl : ι → ℝ)
    (hnorm : ∀ n, nl n ^ 2 = (nA n / a n) ^ 2 + (nW n / a n ^ 2) ^ 2)
    (hl : Filter.Tendsto nl l (𝓝 0)) :
    Filter.Tendsto (fun n => nA n / a n) l (𝓝 0) ∧
    Filter.Tendsto (fun n => nW n / a n ^ 2) l (𝓝 0) := by
  have habs : Filter.Tendsto (fun n => |nl n|) l (𝓝 0) := by
    simpa using hl.abs
  constructor
  · refine squeeze_zero_norm (fun n => ?_) habs
    rw [Real.norm_eq_abs, ← sq_le_sq]
    rw [hnorm n]
    nlinarith [sq_nonneg (nW n / a n ^ 2)]
  · refine squeeze_zero_norm (fun n => ?_) habs
    rw [Real.norm_eq_abs, ← sq_le_sq]
    rw [hnorm n]
    nlinarith [sq_nonneg (nA n / a n)]

/-- `prop:supp-exact-clock-test`, analytic content: along a regulator family
`h ↦ a(h)` with the graded rate norm `eq:supp-exact-rate-norm`, first-jet
shadowing (`‖λ_t‖ → 0`) forces `a(h)⁻¹ ‖(u_{a(h)})_A‖ → 0` and
`a(h)⁻² ‖(u_{a(h)})_W‖ → 0`.  The instantaneous electric coefficient does
not appear. -/
theorem lapse_shift_clock_condition {ι : Type*} (l : Filter ι)
    (a nA nW nl : ι → ℝ)
    (hnorm : ∀ n, nl n ^ 2 = (a n)⁻¹ ^ 2 * nA n ^ 2 + (a n)⁻¹ ^ 4 * nW n ^ 2)
    (hl : Filter.Tendsto nl l (𝓝 0)) :
    Filter.Tendsto (fun n => (a n)⁻¹ * nA n) l (𝓝 0) ∧
    Filter.Tendsto (fun n => (a n)⁻¹ ^ 2 * nW n) l (𝓝 0) := by
  have h := rate_norm_components_tendsto_zero l a nA nW nl
    (fun n => by rw [hnorm n]; ring) hl
  refine ⟨?_, ?_⟩
  · refine h.1.congr fun n => ?_
    ring
  · refine h.2.congr fun n => ?_
    ring

end RenewalGeometry
