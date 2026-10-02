/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdyHermiteReadoutCurvature

/-!
# The unreduced Gowdy ADM density, its discretization and their first variations
  (`eq:supp-gowdy-adm-density`, `eq:main-gowdy-adm-density`, `eq:supp-gowdy-action-test`,
  `thm:main-gowdy-regulator` (G4); emergent-spacetime supplement)

The six fields `u = (R, λ, P, Q, N, β)` (indices `0, …, 5`) are independent; with
`v_u = u̇ - β u'` the boundary-marked ADM density of the manuscript is
`𝓛_G = -v_R (v_λ - 4β')/(2N) + R/(2N) (v_P² + e^{2P} v_Q²) + N[-2R'' + R'λ'/2 - R/2 {P'² + e^{2P}Q'²}]`,
and its discretization replaces `-2NR''` by `2N'R'` (periodic boundary convention).

* `FieldJet`: first jets `(u, u_t, u_θ)` of the six fields; `admDensity`: the density with
  `-2NR''` replaced by `2N'R'` as a function of the first jet (defined for `N ≠ 0`).
* `admVariation x y` and `hasDerivAt_admDensity_line`: the first variation of the density, i.e.
  `d/ds 𝓛(x + s y)|_{s=0}` at every jet with `N ≠ 0`, in closed form.
* `liftJet`, `liftVariation`, `admVariation_liftJet`: at an areal-gauge jet (`R = t`, `R_t = 1`,
  `R' = 0`, `N = 1`, `N_t = N' = 0`, `β = β_t = β' = 0`) the first variation is the explicit
  expression `liftVariation` (lapse and shift directions still varied).
* `gridJet`, `discreteAction`, `discreteFirstVariation`: the **independent midpoint/centered
  discretization** — midpoint time sampling `(uⁿ + uⁿ⁺¹)/2`, forward time quotient
  `(uⁿ⁺¹ - uⁿ)/h`, centered spatial differences of the time-averaged field — of the action
  `S_h(u) = ∑_{n<n₀} ∑_j h ℓ 𝓛(gridJet u n j)` on the periodic grid `ZMod N`, with all six
  fields (including `N` and `β`) independent, and its first variation
  `δS_h[u; φ] = d/ds S_h(u + s φ)|_{s=0}`.
* `arealRecord`: the recorded areal-gauge fields of a numerical history `X` of the Gowdy scheme
  (`R = t_n`, `λ, P, Q` from the records, `N = 1`, `β = 0`);
  `discreteFirstVariation_arealRecord`: there `δS_h` is the sum of `h ℓ liftVariation` over the
  cells.
* `contJet`, `continuumFirstVariation`: the continuum first variation
  `δS_*[U; φ] = ∫ t in α..β, ∫ θ in 0..2π, d/ds 𝓛(j¹(U + s φ))|_{s=0}` and
  `continuumFirstVariation_eq`: its integrand is `admVariation (j¹U) (j¹φ)`.
-/

open Set Finset
open scoped BigOperators

namespace RenewalGeometry.GowdyStaggered.ActionTest

noncomputable section

/-! ### The density -/

/-- A first jet of the six independent fields `(R, λ, P, Q, N, β)` (indices `0, …, 5`):
values, `t`-derivatives and `θ`-derivatives. -/
abbrev FieldJet := (Fin 6 → ℝ) × (Fin 6 → ℝ) × (Fin 6 → ℝ)

/-- The shift-corrected velocity `v_u = u_t - β u_θ` of the field with index `i`. -/
def shiftVel (x : FieldJet) (i : Fin 6) : ℝ := x.2.1 i - x.1 5 * x.2.2 i

/-- **The boundary-marked ADM density `eq:supp-gowdy-adm-density`** with `-2NR''` replaced by
`2N'R'` (the manuscript's periodic boundary convention for the discretization), as a function of
the first jet of `(R, λ, P, Q, N, β)`:
`-v_R (v_λ - 4β')/(2N) + R/(2N) (v_P² + e^{2P} v_Q²) + 2N'R' + N R'λ'/2
  - N R/2 (P'² + e^{2P} Q'²)`. -/
def admDensity (x : FieldJet) : ℝ :=
  -(shiftVel x 0 * (shiftVel x 1 - 4 * x.2.2 5)) / (2 * x.1 4) +
    x.1 0 / (2 * x.1 4) * (shiftVel x 2 ^ 2 + Real.exp (2 * x.1 2) * shiftVel x 3 ^ 2) +
    2 * x.2.2 4 * x.2.2 0 + x.1 4 * x.2.2 0 * x.2.2 1 / 2 -
    x.1 4 * x.1 0 / 2 * (x.2.2 2 ^ 2 + Real.exp (2 * x.1 2) * x.2.2 3 ^ 2)

/-- The variation of the shift-corrected velocity in the direction `y`. -/
def shiftVelVar (x y : FieldJet) (i : Fin 6) : ℝ :=
  y.2.1 i - y.1 5 * x.2.2 i - x.1 5 * y.2.2 i

/-- The first variation `d/ds 𝓛(x + s y)|_{s=0}` of the density in closed form. -/
def admVariation (x y : FieldJet) : ℝ :=
  -(shiftVelVar x y 0 * (shiftVel x 1 - 4 * x.2.2 5) +
      shiftVel x 0 * (shiftVelVar x y 1 - 4 * y.2.2 5)) / (2 * x.1 4) +
    shiftVel x 0 * (shiftVel x 1 - 4 * x.2.2 5) * y.1 4 / (2 * x.1 4 ^ 2) +
    y.1 0 * (shiftVel x 2 ^ 2 + Real.exp (2 * x.1 2) * shiftVel x 3 ^ 2) / (2 * x.1 4) +
    x.1 0 * (2 * shiftVel x 2 * shiftVelVar x y 2 +
        2 * y.1 2 * Real.exp (2 * x.1 2) * shiftVel x 3 ^ 2 +
        2 * Real.exp (2 * x.1 2) * shiftVel x 3 * shiftVelVar x y 3) / (2 * x.1 4) -
    x.1 0 * (shiftVel x 2 ^ 2 + Real.exp (2 * x.1 2) * shiftVel x 3 ^ 2) * y.1 4 /
      (2 * x.1 4 ^ 2) +
    2 * y.2.2 4 * x.2.2 0 + 2 * x.2.2 4 * y.2.2 0 +
    (y.1 4 * x.2.2 0 * x.2.2 1 + x.1 4 * y.2.2 0 * x.2.2 1 + x.1 4 * x.2.2 0 * y.2.2 1) / 2 -
    (y.1 4 * x.1 0 + x.1 4 * y.1 0) * (x.2.2 2 ^ 2 + Real.exp (2 * x.1 2) * x.2.2 3 ^ 2) / 2 -
    x.1 4 * x.1 0 * (2 * x.2.2 2 * y.2.2 2 + 2 * y.1 2 * Real.exp (2 * x.1 2) * x.2.2 3 ^ 2 +
      2 * Real.exp (2 * x.1 2) * x.2.2 3 * y.2.2 3) / 2

theorem hasDerivAt_line (a b : ℝ) : HasDerivAt (fun s : ℝ => a + s * b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

/-- **The first variation of the density**: at every jet with `N ≠ 0`,
`d/ds 𝓛(x + s y)|_{s=0} = admVariation x y`. -/
theorem hasDerivAt_admDensity_line (x y : FieldJet) (hN : x.1 4 ≠ 0) :
    HasDerivAt (fun s : ℝ => admDensity (x + s • y)) (admVariation x y) 0 := by
  have hu : ∀ i, HasDerivAt (fun s : ℝ => x.1 i + s * y.1 i) (y.1 i) 0 :=
    fun i => hasDerivAt_line _ _
  have hut : ∀ i, HasDerivAt (fun s : ℝ => x.2.1 i + s * y.2.1 i) (y.2.1 i) 0 :=
    fun i => hasDerivAt_line _ _
  have huθ : ∀ i, HasDerivAt (fun s : ℝ => x.2.2 i + s * y.2.2 i) (y.2.2 i) 0 :=
    fun i => hasDerivAt_line _ _
  have hv : ∀ i, HasDerivAt (fun s : ℝ => (x.2.1 i + s * y.2.1 i) -
      (x.1 5 + s * y.1 5) * (x.2.2 i + s * y.2.2 i))
      (y.2.1 i - (y.1 5 * (x.2.2 i + 0 * y.2.2 i) + (x.1 5 + 0 * y.1 5) * y.2.2 i)) 0 :=
    fun i => (hut i).sub ((hu 5).mul (huθ i))
  have hE : HasDerivAt (fun s : ℝ => Real.exp (2 * (x.1 2 + s * y.1 2)))
      (Real.exp (2 * (x.1 2 + 0 * y.1 2)) * (2 * y.1 2)) 0 := ((hu 2).const_mul 2).exp
  have hd : (fun s : ℝ => 2 * (x.1 4 + s * y.1 4)) 0 ≠ 0 := by simpa using hN
  have T1 := (((hv 0).mul ((hv 1).sub ((huθ 5).const_mul 4))).neg).div ((hu 4).const_mul 2) hd
  have T2 := ((hu 0).div ((hu 4).const_mul 2) hd).mul (((hv 2).pow 2).add (hE.mul ((hv 3).pow 2)))
  have T3 := ((huθ 4).const_mul 2).mul (huθ 0)
  have T4 := (((hu 4).mul (huθ 0)).mul (huθ 1)).div_const 2
  have T5 := (((hu 4).mul (hu 0)).div_const 2).mul (((huθ 2).pow 2).add (hE.mul ((huθ 3).pow 2)))
  have key := (((T1.add T2).add T3).add T4).sub T5
  refine (key.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  · simp only [admVariation, shiftVel, shiftVelVar, zero_mul, add_zero, Nat.cast_ofNat,
      Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply]
    field_simp
    ring
  · simp only [admDensity, shiftVel, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply,
      Pi.div_apply, Pi.pow_apply]

/-! ### Areal-gauge jets -/

/-- The areal-gauge jet `R = t, R_t = 1, R' = 0, N = 1, N_t = N' = 0, β = β_t = β' = 0` with
the given `λ, P, Q` jets. -/
def liftJet (t lam P Q lt lθ Pt Pθ Qt Qθ : ℝ) : FieldJet :=
  (![t, lam, P, Q, 1, 0], ![1, lt, Pt, Qt, 0, 0], ![0, lθ, Pθ, Qθ, 0, 0])

/-- **The first variation at an areal-gauge jet**, with all six directions (in particular the
lapse `δN = y.1 4` and the shift `δβ = y.1 5`) still varied:
`δN [λ_t/2 - t/2 (P_t² + e^{2P}Q_t² + P_θ² + e^{2P}Q_θ²)] + δβ [λ_θ/2 - t (P_tP_θ + e^{2P}Q_tQ_θ)]
 + 2 δβ_θ - δλ_t/2 + δR [(P_t² + e^{2P}Q_t²) - (P_θ² + e^{2P}Q_θ²)]/2 - δR_t λ_t/2
 + δR_θ λ_θ/2 + δP t e^{2P}(Q_t² - Q_θ²) + δP_t t P_t - δP_θ t P_θ + δQ_t t e^{2P} Q_t
 - δQ_θ t e^{2P} Q_θ`. -/
def liftVariation (t lt lθ P Pt Pθ Qt Qθ : ℝ) (y : FieldJet) : ℝ :=
  y.1 4 * (lt / 2 - t / 2 * (Pt ^ 2 + Real.exp (2 * P) * Qt ^ 2 + Pθ ^ 2 +
      Real.exp (2 * P) * Qθ ^ 2)) +
    y.1 5 * (lθ / 2 - t * (Pt * Pθ + Real.exp (2 * P) * Qt * Qθ)) + 2 * y.2.2 5 - y.2.1 1 / 2 +
    y.1 0 * ((Pt ^ 2 + Real.exp (2 * P) * Qt ^ 2) - (Pθ ^ 2 + Real.exp (2 * P) * Qθ ^ 2)) / 2 -
    y.2.1 0 * lt / 2 + y.2.2 0 * lθ / 2 + y.1 2 * t * Real.exp (2 * P) * (Qt ^ 2 - Qθ ^ 2) +
    y.2.1 2 * t * Pt - y.2.2 2 * t * Pθ + y.2.1 3 * t * Real.exp (2 * P) * Qt -
    y.2.2 3 * t * Real.exp (2 * P) * Qθ

theorem admVariation_liftJet (t lam P Q lt lθ Pt Pθ Qt Qθ : ℝ) (y : FieldJet) :
    admVariation (liftJet t lam P Q lt lθ Pt Pθ Qt Qθ) y = liftVariation t lt lθ P Pt Pθ Qt Qθ y := by
  simp only [admVariation, liftJet, liftVariation, shiftVel, shiftVelVar, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp
  ring

/-! ### The independent midpoint/centered discretization -/

variable {N : ℕ}

/-- Midpoint time sampling `(vⁿ_j + vⁿ⁺¹_j)/2` of a scalar grid field. -/
def gridAvg (v : ℕ → ZMod N → ℝ) (n : ℕ) (j : ZMod N) : ℝ := (v n j + v (n + 1) j) / 2

/-- Forward time quotient `(vⁿ⁺¹_j - vⁿ_j)/h`. -/
def gridDt (h : ℝ) (v : ℕ → ZMod N → ℝ) (n : ℕ) (j : ZMod N) : ℝ := (v (n + 1) j - v n j) / h

/-- Centered spatial difference of the time-averaged field,
`(v̄_{j+1} - v̄_{j-1})/(2ℓ)` with `v̄ = (vⁿ + vⁿ⁺¹)/2`. -/
def gridDθ (ℓ : ℝ) (v : ℕ → ZMod N → ℝ) (n : ℕ) (j : ZMod N) : ℝ :=
  (gridAvg v n (j + 1) - gridAvg v n (j - 1)) / (2 * ℓ)

/-- The discrete first jet of a grid field of the six fields on the cell `(n, j)`. -/
def gridJet (h ℓ : ℝ) (u : ℕ → ZMod N → Fin 6 → ℝ) (n : ℕ) (j : ZMod N) : FieldJet :=
  (fun k => gridAvg (fun m i => u m i k) n j, fun k => gridDt h (fun m i => u m i k) n j,
    fun k => gridDθ ℓ (fun m i => u m i k) n j)

theorem gridJet_add_smul (h ℓ : ℝ) (u φ : ℕ → ZMod N → Fin 6 → ℝ) (s : ℝ) (n : ℕ)
    (j : ZMod N) :
    gridJet h ℓ (u + s • φ) n j = gridJet h ℓ u n j + s • gridJet h ℓ φ n j := by
  ext k <;> simp only [gridJet, gridAvg, gridDt, gridDθ, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] <;> ring

/-- **The discrete action** `S_h(u) = ∑_{n<n₀} ∑_j h ℓ 𝓛(gridJet u n j)` (midpoint time sampling,
centered spatial differences, `N` and `β` independent). -/
def discreteAction [NeZero N] (h ℓ : ℝ) (n₀ : ℕ) (u : ℕ → ZMod N → Fin 6 → ℝ) : ℝ :=
  ∑ n ∈ range n₀, ∑ j : ZMod N, h * ℓ * admDensity (gridJet h ℓ u n j)

/-- **The first variation of the discrete action** in the direction of the grid field `φ`:
`δS_h[u; φ] = d/ds S_h(u + s φ)|_{s=0}`. -/
def discreteFirstVariation [NeZero N] (h ℓ : ℝ) (n₀ : ℕ) (u φ : ℕ → ZMod N → Fin 6 → ℝ) : ℝ :=
  deriv (fun s : ℝ => discreteAction h ℓ n₀ (u + s • φ)) 0

theorem hasDerivAt_discreteAction [NeZero N] (h ℓ : ℝ) (n₀ : ℕ)
    (u φ : ℕ → ZMod N → Fin 6 → ℝ) (hN : ∀ n < n₀, ∀ j, (gridJet h ℓ u n j).1 4 ≠ 0) :
    HasDerivAt (fun s : ℝ => discreteAction h ℓ n₀ (u + s • φ))
      (∑ n ∈ range n₀, ∑ j : ZMod N, h * ℓ *
        admVariation (gridJet h ℓ u n j) (gridJet h ℓ φ n j)) 0 := by
  unfold discreteAction
  refine HasDerivAt.fun_sum fun n hn => HasDerivAt.fun_sum fun j _ => ?_
  have := (hasDerivAt_admDensity_line (gridJet h ℓ u n j) (gridJet h ℓ φ n j)
    (hN n (mem_range.1 hn) j)).const_mul (h * ℓ)
  simpa only [gridJet_add_smul] using this

theorem discreteFirstVariation_eq [NeZero N] (h ℓ : ℝ) (n₀ : ℕ)
    (u φ : ℕ → ZMod N → Fin 6 → ℝ) (hN : ∀ n < n₀, ∀ j, (gridJet h ℓ u n j).1 4 ≠ 0) :
    discreteFirstVariation h ℓ n₀ u φ = ∑ n ∈ range n₀, ∑ j : ZMod N, h * ℓ *
        admVariation (gridJet h ℓ u n j) (gridJet h ℓ φ n j) :=
  (hasDerivAt_discreteAction h ℓ n₀ u φ hN).deriv

/-! ### The recorded areal-gauge fields of a numerical history -/

/-- **The recorded areal-gauge fields** of a numerical history `X` of the Gowdy scheme started at
`τ₀` with time step `h`: `R = t_n = τ₀ + n h`, `λ`, `P`, `Q` read from the records of `X_n`,
lapse `N = 1` and shift `β = 0`. -/
def arealRecord (τ₀ h : ℝ) (X : ℕ → GridState N) : ℕ → ZMod N → Fin 6 → ℝ :=
  fun n j => ![τ₀ + n * h, (X n).lam j, ((X n).site j).P, ((X n).site j).Q, 1, 0]

/-- The recorded `λ` field. -/
def recLam (X : ℕ → GridState N) : ℕ → ZMod N → ℝ := fun n j => (X n).lam j

/-- The recorded `P` field. -/
def recP (X : ℕ → GridState N) : ℕ → ZMod N → ℝ := fun n j => ((X n).site j).P

/-- The recorded `Q` field. -/
def recQ (X : ℕ → GridState N) : ℕ → ZMod N → ℝ := fun n j => ((X n).site j).Q

theorem gridJet_arealRecord {h : ℝ} (hh : h ≠ 0) (ℓ τ₀ : ℝ) (X : ℕ → GridState N) (n : ℕ)
    (j : ZMod N) :
    gridJet h ℓ (arealRecord τ₀ h X) n j =
      liftJet (τ₀ + n * h + h / 2) (gridAvg (recLam X) n j) (gridAvg (recP X) n j)
        (gridAvg (recQ X) n j) (gridDt h (recLam X) n j) (gridDθ ℓ (recLam X) n j)
        (gridDt h (recP X) n j) (gridDθ ℓ (recP X) n j) (gridDt h (recQ X) n j)
        (gridDθ ℓ (recQ X) n j) := by
  ext k <;> fin_cases k <;>
    simp [gridJet, liftJet, arealRecord, gridAvg, gridDt, gridDθ, recLam, recP, recQ] <;>
    field_simp <;> ring

/-- **The discrete first variation at the recorded areal-gauge fields** is the cell sum of
`h ℓ liftVariation` of the discrete jets (lapse and shift directions included). -/
theorem discreteFirstVariation_arealRecord [NeZero N] {h : ℝ} (hh : h ≠ 0) (ℓ τ₀ : ℝ)
    (n₀ : ℕ) (X : ℕ → GridState N) (φ : ℕ → ZMod N → Fin 6 → ℝ) :
    discreteFirstVariation h ℓ n₀ (arealRecord τ₀ h X) φ =
      ∑ n ∈ range n₀, ∑ j : ZMod N, h * ℓ *
        liftVariation (τ₀ + n * h + h / 2) (gridDt h (recLam X) n j) (gridDθ ℓ (recLam X) n j)
          (gridAvg (recP X) n j) (gridDt h (recP X) n j) (gridDθ ℓ (recP X) n j)
          (gridDt h (recQ X) n j) (gridDθ ℓ (recQ X) n j) (gridJet h ℓ φ n j) := by
  rw [discreteFirstVariation_eq]
  · simp only [gridJet_arealRecord hh, admVariation_liftJet]
  · intro n _ j
    rw [gridJet_arealRecord hh]
    simp [liftJet]

/-! ### The continuum first variation -/

/-- The first jet `(U(p), ∂_t U(p), ∂_θ U(p))` of six fields on `ℝ × ℝ` at `p = (t, θ)`. -/
def contJet (U : Fin 6 → ℝ × ℝ → ℝ) (p : ℝ × ℝ) : FieldJet :=
  (fun k => U k p, fun k => dT (U k) p, fun k => dΘ (U k) p)

theorem contJet_add_smul {U φ : Fin 6 → ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hU : ∀ k, DifferentiableAt ℝ (U k) p) (hφ : ∀ k, DifferentiableAt ℝ (φ k) p) (s : ℝ) :
    contJet (fun k => U k + s • φ k) p = contJet U p + s • contJet φ p := by
  have hd : ∀ k (w : ℝ × ℝ), fderiv ℝ (U k + s • φ k) p w =
      fderiv ℝ (U k) p w + s * fderiv ℝ (φ k) p w := by
    intro k w
    rw [fderiv_add (hU k) ((hφ k).const_smul s), fderiv_const_smul (hφ k)]
    simp
  ext k <;> simp only [contJet, dT, dΘ, hd, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **The continuum first variation** of the action `∫∫ 𝓛_G` at the six fields `U` in the
direction `φ`, over the slab `[α, β] × [0, 2π]`:
`δS_*[U; φ] = ∫ t in α..β, ∫ θ in 0..2π, d/ds 𝓛(j¹(U + s φ))(t, θ)|_{s=0}`. -/
def continuumFirstVariation (U φ : Fin 6 → ℝ × ℝ → ℝ) (α β : ℝ) : ℝ :=
  ∫ t in α..β, ∫ θ in (0 : ℝ)..2 * Real.pi,
    deriv (fun s : ℝ => admDensity (contJet (fun k => U k + s • φ k) (t, θ))) 0

theorem deriv_admDensity_contJet {U φ : Fin 6 → ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hU : ∀ k, DifferentiableAt ℝ (U k) p) (hφ : ∀ k, DifferentiableAt ℝ (φ k) p)
    (hN : U 4 p ≠ 0) :
    deriv (fun s : ℝ => admDensity (contJet (fun k => U k + s • φ k) p)) 0 =
      admVariation (contJet U p) (contJet φ p) := by
  have e : (fun s : ℝ => admDensity (contJet (fun k => U k + s • φ k) p)) =
      fun s => admDensity (contJet U p + s • contJet φ p) := by
    funext s; rw [contJet_add_smul hU hφ]
  rw [e]
  exact (hasDerivAt_admDensity_line _ _ hN).deriv

/-- The integrand of the continuum first variation is `admVariation (j¹U) (j¹φ)` wherever the
fields are differentiable and the lapse is nonzero. -/
theorem continuumFirstVariation_eq {U φ : Fin 6 → ℝ × ℝ → ℝ} (α β : ℝ)
    (hU : ∀ k, Differentiable ℝ (U k)) (hφ : ∀ k, Differentiable ℝ (φ k))
    (hN : ∀ p, U 4 p ≠ 0) :
    continuumFirstVariation U φ α β =
      ∫ t in α..β, ∫ θ in (0 : ℝ)..2 * Real.pi, admVariation (contJet U (t, θ)) (contJet φ (t, θ)) := by
  unfold continuumFirstVariation
  congr 1; funext t; congr 1; funext θ
  exact deriv_admDensity_contJet (fun k => hU k _) (fun k => hφ k _) (hN _)

end

end RenewalGeometry.GowdyStaggered.ActionTest
