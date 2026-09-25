/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact staggered momentum under symmetric splitting
  (`thm:supp-gowdy-momentum`, emergent-spacetime supplement)

The Gowdy local splitting scheme on a periodic grid `ZMod N` of spacing `ℓ`:

* `J` — the quadratic momentum density `𝒥(U) = u₁u₂ + u₃u₄`;
* `sourceField`, `localField` — the local source flow
  `eq:supp-gowdy-source-flow` (frame part, and the full `(U,P,Q,t)`
  system with `dt/ds = 1`, `dλ/ds = 0`);
* `IsMidpointStep` — the implicit-midpoint relation
  `Y = X + σ F((X+Y)/2)` over source duration `σ`;
* `gradJ_dot_sourceField`, `J_sub_eq_gradJ_midpoint`,
  `J_of_midpointStep` — `∇𝒥·U̇ = 0`, the quadratic endpoint identity, and
  exact preservation of `𝒥` by every implicit-midpoint source step;
* `transport` — the characteristic transport map `eq:supp-gowdy-transport`
  (`w⁺ ↦ S₊w⁺`, `w⁻ ↦ S₋w⁻`, `λ ↦ λ + (ℓ/2)[(I+S₊)g⁺ + (I+S₋)g⁻]`, `P,Q`
  fixed);
* `J_transport`, `transport_identity` — the transport identity
  `Δ𝒥 = ½[(S₊-I)g⁺ - (S₋-I)g⁻]`, `D₊Δλ = 2𝖠₊Δ𝒥`
  (`eq:supp-gowdy-transport-identity`);
* `staggeredMomentum` — the boxed `𝒦_ℓ = D₊λ - 2𝖠₊𝒥(U)`;
* `staggeredMomentum_transport`, `staggeredMomentum_sourceStep`,
  `staggeredMomentum_symmetric_splitting` — exact preservation of `𝒦_ℓ`
  by transport, by source steps and by the source-half / transport /
  source-half composition;
* `transport_lam_increment_nonneg` — the background increment is a
  nonnegative sum of squared characteristic amplitudes;
* `transport_nearest_neighbour` — the update at site `j` depends only on
  the state at `j-1, j, j+1`.

The second-order consistency clause (Taylor remainders of the trapezoid
rule and of the implicit midpoint on smooth charts) is not formalised.
-/

open scoped BigOperators

namespace RenewalGeometry.GowdyStaggered

noncomputable section

/-! ### The local source flow -/

/-- The quadratic momentum density `𝒥(U) = u₁u₂ + u₃u₄`
(`eq:supp-gowdy-rescaled-frame`). -/
def J (u : Fin 4 → ℝ) : ℝ := u 0 * u 1 + u 2 * u 3

/-- `∇𝒥(U) = (u₂, u₁, u₄, u₃)`. -/
def gradJ (u : Fin 4 → ℝ) : Fin 4 → ℝ := ![u 1, u 0, u 3, u 2]

/-- Frame part of the source flow `eq:supp-gowdy-source-flow` at physical
time `t`. -/
def sourceField (t : ℝ) (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-(u 0) / (2 * t) + (u 2 ^ 2 - u 3 ^ 2) / Real.sqrt t,
    u 1 / (2 * t),
    -(u 2) / (2 * t) + (-(u 0) * u 2 + u 1 * u 3) / Real.sqrt t,
    u 3 / (2 * t) + (u 0 * u 3 - u 1 * u 2) / Real.sqrt t]

/-- `∇𝒥(U) · U̇ = 0` along the source flow. -/
theorem gradJ_dot_sourceField (t : ℝ) (u : Fin 4 → ℝ) :
    ∑ i, gradJ u i * sourceField t u i = 0 := by
  simp [gradJ, sourceField, Fin.sum_univ_four]
  ring

/-- The difference of the quadratic `𝒥` at two endpoints equals its
gradient at the arithmetic midpoint paired with the increment. -/
theorem J_sub_eq_gradJ_midpoint (u v : Fin 4 → ℝ) :
    J v - J u = ∑ i, gradJ ((1 / 2 : ℝ) • (u + v)) i * (v i - u i) := by
  simp [J, gradJ, Fin.sum_univ_four]
  ring

/-- Local state `(U, P, Q, t)` of the source system. -/
structure LocalState where
  u : Fin 4 → ℝ
  P : ℝ
  Q : ℝ
  t : ℝ

/-- The full local source vector field: `eq:supp-gowdy-source-flow`
together with `dP/ds = u₁/√t`, `dQ/ds = e^{-P} u₃/√t`, `dt/ds = 1`. -/
def localField (X : LocalState) : LocalState where
  u := sourceField X.t X.u
  P := X.u 0 / Real.sqrt X.t
  Q := Real.exp (-X.P) * X.u 2 / Real.sqrt X.t
  t := 1

/-- Arithmetic midpoint of two local states. -/
def midpoint (X Y : LocalState) : LocalState where
  u := (1 / 2 : ℝ) • (X.u + Y.u)
  P := (X.P + Y.P) / 2
  Q := (X.Q + Y.Q) / 2
  t := (X.t + Y.t) / 2

/-- The implicit-midpoint relation `Y = X + σ F((X+Y)/2)` over source
duration `σ` (the map `𝖲_σ` of the manuscript). -/
def IsMidpointStep (σ : ℝ) (X Y : LocalState) : Prop :=
  Y.u = X.u + σ • (localField (midpoint X Y)).u ∧
    Y.P = X.P + σ * (localField (midpoint X Y)).P ∧
    Y.Q = X.Q + σ * (localField (midpoint X Y)).Q ∧
    Y.t = X.t + σ * (localField (midpoint X Y)).t

/-- Implicit midpoint preserves `𝒥` exactly. -/
theorem J_of_midpointStep {σ : ℝ} {X Y : LocalState}
    (h : IsMidpointStep σ X Y) : J Y.u = J X.u := by
  have hu := h.1
  have hdiff : J Y.u - J X.u =
      ∑ i, gradJ (midpoint X Y).u i * (Y.u i - X.u i) :=
    J_sub_eq_gradJ_midpoint X.u Y.u
  have hinc : ∀ i, Y.u i - X.u i =
      σ * sourceField (midpoint X Y).t (midpoint X Y).u i := by
    intro i
    rw [hu]
    simp only [localField, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hinc] at hdiff
  have hdot := gradJ_dot_sourceField (midpoint X Y).t (midpoint X Y).u
  have : ∑ i, gradJ (midpoint X Y).u i *
      (σ * sourceField (midpoint X Y).t (midpoint X Y).u i) =
      σ * ∑ i, gradJ (midpoint X Y).u i *
        sourceField (midpoint X Y).t (midpoint X Y).u i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this, hdot, mul_zero] at hdiff
  linarith

/-! ### The characteristic transport -/

/-- `1/√2`. -/
def invSqrt2 : ℝ := (Real.sqrt 2)⁻¹

theorem invSqrt2_sq : invSqrt2 * invSqrt2 = 1 / 2 := by
  unfold invSqrt2
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- Characteristic amplitude `w⁺ = (u₁+u₂, u₃+u₄)/√2`. -/
def wPlus (u : Fin 4 → ℝ) : Fin 2 → ℝ :=
  ![(u 0 + u 1) * invSqrt2, (u 2 + u 3) * invSqrt2]

/-- Characteristic amplitude `w⁻ = (u₁-u₂, u₃-u₄)/√2`. -/
def wMinus (u : Fin 4 → ℝ) : Fin 2 → ℝ :=
  ![(u 0 - u 1) * invSqrt2, (u 2 - u 3) * invSqrt2]

/-- `g⁺ = |w⁺|²`. -/
def gPlus (u : Fin 4 → ℝ) : ℝ := wPlus u 0 ^ 2 + wPlus u 1 ^ 2

/-- `g⁻ = |w⁻|²`. -/
def gMinus (u : Fin 4 → ℝ) : ℝ := wMinus u 0 ^ 2 + wMinus u 1 ^ 2

/-- Recover the frame from its characteristic amplitudes. -/
def recombine (wp wm : Fin 2 → ℝ) : Fin 4 → ℝ :=
  ![(wp 0 + wm 0) * invSqrt2, (wp 0 - wm 0) * invSqrt2,
    (wp 1 + wm 1) * invSqrt2, (wp 1 - wm 1) * invSqrt2]

theorem recombine_wPlus_wMinus (u : Fin 4 → ℝ) :
    recombine (wPlus u) (wMinus u) = u := by
  have h2 := invSqrt2_sq
  funext i
  fin_cases i
  · simp [recombine, wPlus, wMinus]; linear_combination (2 * u 0) * h2
  · simp [recombine, wPlus, wMinus]; linear_combination (2 * u 1) * h2
  · simp [recombine, wPlus, wMinus]; linear_combination (2 * u 2) * h2
  · simp [recombine, wPlus, wMinus]; linear_combination (2 * u 3) * h2

/-- `𝒥(U) = (g⁺ - g⁻)/2`. -/
theorem J_eq_gPlus_sub_gMinus (u : Fin 4 → ℝ) :
    J u = (gPlus u - gMinus u) / 2 := by
  have h2 := invSqrt2_sq
  simp only [J, gPlus, gMinus, wPlus, wMinus, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination (-(2 * (u 0 * u 1 + u 2 * u 3))) * h2

/-- `𝒥(recombine wp wm) = (|wp|² - |wm|²)/2`. -/
theorem J_recombine (wp wm : Fin 2 → ℝ) :
    J (recombine wp wm) =
      ((wp 0 ^ 2 + wp 1 ^ 2) - (wm 0 ^ 2 + wm 1 ^ 2)) / 2 := by
  have h2 := invSqrt2_sq
  simp [J, recombine]
  linear_combination ((wp 0 ^ 2 + wp 1 ^ 2) - (wm 0 ^ 2 + wm 1 ^ 2)) * h2

/-- Grid state on the periodic grid `ZMod N`: local `(U,P,Q,t)` at every
site and the background `λ`. -/
structure GridState (N : ℕ) where
  site : ZMod N → LocalState
  lam : ZMod N → ℝ

variable {N : ℕ}

/-- The transport map `eq:supp-gowdy-transport` at frozen physical time:
`(w⁺)⁺ = S₊w⁺`, `(w⁻)⁺ = S₋w⁻`,
`λ⁺ = λ + (ℓ/2)[(I+S₊)g⁺ + (I+S₋)g⁻]`, with `P, Q, t` fixed. -/
def transport (ℓ : ℝ) (X : GridState N) : GridState N where
  site := fun j =>
    { X.site j with
      u := recombine (wPlus (X.site (j + 1)).u) (wMinus (X.site (j - 1)).u) }
  lam := fun j => X.lam j + ℓ / 2 *
    ((gPlus (X.site j).u + gPlus (X.site (j + 1)).u) +
      (gMinus (X.site j).u + gMinus (X.site (j - 1)).u))

/-- The transported momentum density: `𝒥⁺(j) = (g⁺(j+1) - g⁻(j-1))/2`. -/
theorem J_transport (ℓ : ℝ) (X : GridState N) (j : ZMod N) :
    J ((transport ℓ X).site j).u =
      (gPlus (X.site (j + 1)).u - gMinus (X.site (j - 1)).u) / 2 := by
  simp only [transport]
  rw [J_recombine]
  rfl

/-- `eq:supp-gowdy-transport-identity`:
`Δ𝒥 = ½[(S₊-I)g⁺ - (S₋-I)g⁻]` and `D₊Δλ = 2𝖠₊Δ𝒥`. -/
theorem transport_identity (ℓ : ℝ) (hℓ : ℓ ≠ 0) (X : GridState N)
    (j : ZMod N) :
    (J ((transport ℓ X).site j).u - J (X.site j).u =
      1 / 2 * ((gPlus (X.site (j + 1)).u - gPlus (X.site j).u) -
        (gMinus (X.site (j - 1)).u - gMinus (X.site j).u))) ∧
    (((transport ℓ X).lam (j + 1) - X.lam (j + 1)) -
        ((transport ℓ X).lam j - X.lam j)) / ℓ =
      2 * ((J ((transport ℓ X).site j).u - J (X.site j).u) +
        (J ((transport ℓ X).site (j + 1)).u - J (X.site (j + 1)).u)) / 2 := by
  constructor
  · rw [J_transport, J_eq_gPlus_sub_gMinus]
    ring
  · rw [J_transport, J_transport, J_eq_gPlus_sub_gMinus,
      J_eq_gPlus_sub_gMinus]
    simp only [transport, add_sub_cancel_right]
    field_simp
    ring

/-- The boxed staggered momentum `𝒦_ℓ = D₊λ - 2𝖠₊𝒥(U)` at site `j`,
with `D₊ = (S₊ - I)/ℓ` and `𝖠₊ = (I + S₊)/2`. -/
def staggeredMomentum (ℓ : ℝ) (X : GridState N) (j : ZMod N) : ℝ :=
  (X.lam (j + 1) - X.lam j) / ℓ -
    2 * ((J (X.site j).u + J (X.site (j + 1)).u) / 2)

/-- Transport preserves `𝒦_ℓ` exactly. -/
theorem staggeredMomentum_transport (ℓ : ℝ) (hℓ : ℓ ≠ 0) (X : GridState N)
    (j : ZMod N) :
    staggeredMomentum ℓ (transport ℓ X) j = staggeredMomentum ℓ X j := by
  unfold staggeredMomentum
  rw [J_transport, J_transport, J_eq_gPlus_sub_gMinus (X.site j).u,
    J_eq_gPlus_sub_gMinus (X.site (j + 1)).u]
  simp only [transport, add_sub_cancel_right]
  field_simp
  ring

/-- A source step: an implicit-midpoint step at every site, `λ` fixed. -/
def IsSourceStep (σ : ℝ) (X Y : GridState N) : Prop :=
  (∀ j, IsMidpointStep σ (X.site j) (Y.site j)) ∧ Y.lam = X.lam

/-- Source steps preserve `𝒦_ℓ` exactly (they preserve `𝒥` and fix `λ`). -/
theorem staggeredMomentum_sourceStep (ℓ σ : ℝ) {X Y : GridState N}
    (h : IsSourceStep σ X Y) (j : ZMod N) :
    staggeredMomentum ℓ Y j = staggeredMomentum ℓ X j := by
  unfold staggeredMomentum
  rw [h.2, J_of_midpointStep (h.1 j), J_of_midpointStep (h.1 (j + 1))]

/-- `thm:supp-gowdy-momentum`, exact clause: the source-half / transport /
source-half composition preserves `𝒦_ℓ` exactly (for the synchronized
full step `h = ℓ` take `σ = ℓ / 2`). -/
theorem staggeredMomentum_symmetric_splitting (ℓ σ : ℝ) (hℓ : ℓ ≠ 0)
    {X₀ X₁ X₃ : GridState N}
    (h₁ : IsSourceStep σ X₀ X₁) (h₃ : IsSourceStep σ (transport ℓ X₁) X₃)
    (j : ZMod N) :
    staggeredMomentum ℓ X₃ j = staggeredMomentum ℓ X₀ j := by
  rw [staggeredMomentum_sourceStep ℓ σ h₃, staggeredMomentum_transport ℓ hℓ,
    staggeredMomentum_sourceStep ℓ σ h₁]

/-- The background increment is `ℓ/2` times a sum of squared characteristic
amplitudes, hence nonnegative for `ℓ ≥ 0`. -/
theorem transport_lam_increment_nonneg (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (X : GridState N) (j : ZMod N) :
    0 ≤ (transport ℓ X).lam j - X.lam j := by
  simp only [transport, add_sub_cancel_left]
  unfold gPlus gMinus
  positivity

/-- The update is nearest neighbour: if two grid states agree at
`j-1, j, j+1`, their transported states agree at `j`. -/
theorem transport_nearest_neighbour (ℓ : ℝ) (X X' : GridState N)
    (j : ZMod N)
    (hm : X.site (j - 1) = X'.site (j - 1)) (h0 : X.site j = X'.site j)
    (hp : X.site (j + 1) = X'.site (j + 1)) (hl : X.lam j = X'.lam j) :
    (transport ℓ X).site j = (transport ℓ X').site j ∧
      (transport ℓ X).lam j = (transport ℓ X').lam j := by
  simp only [transport]
  rw [hm, h0, hp, hl]
  exact ⟨rfl, rfl⟩

end

end RenewalGeometry.GowdyStaggered
