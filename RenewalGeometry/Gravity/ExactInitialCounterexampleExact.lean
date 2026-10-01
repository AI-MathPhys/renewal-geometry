/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Analytic preparation does not imply the two-row cancellation
  (`prop:supp-exact-initial-counterexample`, `eq:supp-exact-counterexample-L`,
  `eq:supp-exact-counterexample-solution`; emergent-spacetime manuscript)

The autonomous polynomial Lagrangian (`eq:supp-exact-counterexample-L`)
`L(α, z, λ; α', z', λ') = ½ α² (z')² - ½ (z - α)² + λ α'`
is encoded as `lagrangian`, together with its six partial derivatives
(`lagrangian_hasDerivAt_*`).  Its Euler–Lagrange equations are
`α' = 0`, `(α² z')' = α - z`, `λ' = α (z')² + (z - α)`.

For an amplitude `a > 0` and a jet parameter `d` (`d = 0` is the solution of
the proposition's proof, general `d` is the family of the example following
`prop:supp-finite-acc-invariance`) the exact solution is
`α ≡ a`, `z(τ) = a (1 - cos(τ/a)) + a³ d sin(τ/a)`, and
`λ(τ) = ∫₀^τ (a z'(s)² + z(s) - a) ds` (the multiplier equation solved by
integration).  `counterexample_euler_lagrange` verifies all three
Euler–Lagrange equations at every time, in the form
`d/dτ ∂_{q'} L(q(τ), q'(τ)) = ∂_q L(q(τ), q'(τ))`.

`prop_supp_exact_initial_counterexample` collects the proposition:
the initial records `α(0) = a`, `z(0) = 0`, `λ(0) = 0` and the initial
velocities `α'(0) = 0`, `z'(0) = 0`, `λ'(0) = -a` are polynomial (hence
analytic and bounded) in `a`; the first derivatives are bounded uniformly in
time (`|α'| = 0`, `|z'| ≤ 1`, `|λ'| ≤ 2a`); but `a z''(0) = 1` for every `a`,
so the scaled acceleration defect (the one-row analogue of the upper
homological row, the right-hand side of
`eq:supp-exact-initial-acceleration-defect` with no source term) tends to
`1 ≠ 0` as `a ↓ 0`.  `counterexample_jet_family_defect` records the
`d`-family: initial weak rate `z'(0) = a² d`, yet `a z''(0) = 1` for every `d`.
-/

namespace RenewalGeometry
namespace ExactInitialCounterexample

noncomputable section

/-- The polynomial Lagrangian `L = ½ α² (z')² - ½ (z - α)² + λ α'`
(`eq:supp-exact-counterexample-L`). -/
def lagrangian (α z l α' z' l' : ℝ) : ℝ :=
  (1 / 2) * α ^ 2 * z' ^ 2 - (1 / 2) * (z - α) ^ 2 + l * α' + 0 * l'

/-- `∂L/∂α = α (z')² + (z - α)`. -/
theorem lagrangian_hasDerivAt_α (α z l α' z' l' : ℝ) :
    HasDerivAt (fun s => lagrangian s z l α' z' l') (α * z' ^ 2 + (z - α)) α := by
  have e : (fun s => lagrangian s z l α' z' l')
      = fun s => (1 / 2 * z' ^ 2) * s ^ 2 - (1 / 2) * (z - s) ^ 2 + l * α' := by
    funext s; simp only [lagrangian]; ring
  rw [e]
  have h := (((hasDerivAt_pow 2 α).const_mul (1 / 2 * z' ^ 2)).sub
    ((((hasDerivAt_id α).const_sub z).pow 2).const_mul (1 / 2 : ℝ))).add_const (l * α')
  exact h.congr_deriv (by simp; ring)

/-- `∂L/∂z = -(z - α)`. -/
theorem lagrangian_hasDerivAt_z (α z l α' z' l' : ℝ) :
    HasDerivAt (fun s => lagrangian α s l α' z' l') (-(z - α)) z := by
  have e : (fun s => lagrangian α s l α' z' l')
      = fun s => (1 / 2 * α ^ 2 * z' ^ 2 + l * α') - (1 / 2) * (s - α) ^ 2 := by
    funext s; simp only [lagrangian]; ring
  rw [e]
  have h := ((((hasDerivAt_id z).sub_const α).pow 2).const_mul (1 / 2 : ℝ)).const_sub
    (1 / 2 * α ^ 2 * z' ^ 2 + l * α')
  exact h.congr_deriv (by simp)

/-- `∂L/∂λ = α'`. -/
theorem lagrangian_hasDerivAt_l (α z l α' z' l' : ℝ) :
    HasDerivAt (fun s => lagrangian α z s α' z' l') α' l := by
  have e : (fun s => lagrangian α z s α' z' l')
      = fun s => (1 / 2 * α ^ 2 * z' ^ 2 - 1 / 2 * (z - α) ^ 2) + s * α' := by
    funext s; simp only [lagrangian]; ring
  rw [e]
  have h := ((hasDerivAt_id l).mul_const α').const_add (1 / 2 * α ^ 2 * z' ^ 2 - 1 / 2 * (z - α) ^ 2)
  exact h.congr_deriv (by simp)

/-- `∂L/∂α' = λ`. -/
theorem lagrangian_hasDerivAt_α' (α z l α' z' l' : ℝ) :
    HasDerivAt (fun s => lagrangian α z l s z' l') l α' := by
  have e : (fun s => lagrangian α z l s z' l')
      = fun s => (1 / 2 * α ^ 2 * z' ^ 2 - 1 / 2 * (z - α) ^ 2) + l * s := by
    funext s; simp only [lagrangian]; ring
  rw [e]
  have h := ((hasDerivAt_id α').const_mul l).const_add (1 / 2 * α ^ 2 * z' ^ 2 - 1 / 2 * (z - α) ^ 2)
  exact h.congr_deriv (by simp)

/-- `∂L/∂z' = α² z'`. -/
theorem lagrangian_hasDerivAt_z' (α z l α' z' l' : ℝ) :
    HasDerivAt (fun s => lagrangian α z l α' s l') (α ^ 2 * z') z' := by
  have e : (fun s => lagrangian α z l α' s l')
      = fun s => (1 / 2 * α ^ 2) * s ^ 2 + (l * α' - 1 / 2 * (z - α) ^ 2) := by
    funext s; simp only [lagrangian]; ring
  rw [e]
  have h := ((hasDerivAt_pow 2 z').const_mul (1 / 2 * α ^ 2)).add_const
    (l * α' - 1 / 2 * (z - α) ^ 2)
  exact h.congr_deriv (by simp; ring)

/-- `∂L/∂λ' = 0`. -/
theorem lagrangian_hasDerivAt_l' (α z l α' z' l' : ℝ) :
    HasDerivAt (fun s => lagrangian α z l α' z' s) 0 l' := by
  have : (fun s => lagrangian α z l α' z' s)
      = fun _ => (1 / 2) * α ^ 2 * z' ^ 2 - (1 / 2) * (z - α) ^ 2 + l * α' := by
    funext s; simp [lagrangian]
  rw [this]; exact hasDerivAt_const _ _

/-- The `z` component `z(τ) = a (1 - cos(τ/a)) + a³ d sin(τ/a)`
(`eq:supp-exact-counterexample-solution` for `d = 0`). -/
def zSol (a d τ : ℝ) : ℝ := a * (1 - Real.cos (τ / a)) + a ^ 3 * d * Real.sin (τ / a)

/-- Its velocity `z'(τ) = sin(τ/a) + a² d cos(τ/a)`. -/
def zVel (a d τ : ℝ) : ℝ := Real.sin (τ / a) + a ^ 2 * d * Real.cos (τ / a)

/-- Its acceleration `z''(τ) = cos(τ/a)/a - a d sin(τ/a)`. -/
def zAcc (a d τ : ℝ) : ℝ := Real.cos (τ / a) / a - a * d * Real.sin (τ / a)

/-- The multiplier rate `λ'(τ) = a z'(τ)² + (z(τ) - a)` (right-hand side of the
`α` Euler–Lagrange equation). -/
def lRate (a d τ : ℝ) : ℝ := a * zVel a d τ ^ 2 + (zSol a d τ - a)

/-- The multiplier `λ(τ) = ∫₀^τ λ'(s) ds`, solving the multiplier equation by
integration with `λ(0) = 0`. -/
def lSol (a d τ : ℝ) : ℝ := ∫ s in (0 : ℝ)..τ, lRate a d s

theorem hasDerivAt_cos_div (a τ : ℝ) :
    HasDerivAt (fun t => Real.cos (t / a)) (-Real.sin (τ / a) * (1 / a)) τ := by
  have := ((hasDerivAt_id τ).div_const a).cos
  simpa using this

theorem hasDerivAt_sin_div (a τ : ℝ) :
    HasDerivAt (fun t => Real.sin (t / a)) (Real.cos (τ / a) * (1 / a)) τ := by
  have := ((hasDerivAt_id τ).div_const a).sin
  simpa using this

theorem zSol_hasDerivAt {a : ℝ} (ha : a ≠ 0) (d τ : ℝ) :
    HasDerivAt (zSol a d) (zVel a d τ) τ := by
  have h := ((hasDerivAt_cos_div a τ).const_sub 1).const_mul a
    |>.add ((hasDerivAt_sin_div a τ).const_mul (a ^ 3 * d))
  refine h.congr_deriv ?_
  unfold zVel; field_simp

theorem zVel_hasDerivAt {a : ℝ} (ha : a ≠ 0) (d τ : ℝ) :
    HasDerivAt (zVel a d) (zAcc a d τ) τ := by
  have h := (hasDerivAt_sin_div a τ).add ((hasDerivAt_cos_div a τ).const_mul (a ^ 2 * d))
  refine h.congr_deriv ?_
  unfold zAcc; field_simp; ring

theorem zSol_continuous (a d : ℝ) : Continuous (zSol a d) := by
  unfold zSol; fun_prop

theorem zVel_continuous (a d : ℝ) : Continuous (zVel a d) := by
  unfold zVel; fun_prop

theorem lRate_continuous (a d : ℝ) : Continuous (lRate a d) := by
  unfold lRate; have := zSol_continuous a d; have := zVel_continuous a d; fun_prop

theorem lSol_hasDerivAt (a d τ : ℝ) : HasDerivAt (lSol a d) (lRate a d τ) τ :=
  ((lRate_continuous a d).integral_hasStrictDerivAt 0 τ).hasDerivAt

/-- The three Euler–Lagrange equations of `eq:supp-exact-counterexample-L` hold
along `q(τ) = (a, z(τ), λ(τ))`, `q'(τ) = (0, z'(τ), λ'(τ))`, in the form
`d/dτ ∂_{q'} L = ∂_q L` (for `α`: `λ' = α z'² + (z - α)`; for `z`:
`(α² z')' = -(z - α)`; for `λ`: `0 = α'`), for every amplitude `a ≠ 0`, jet
parameter `d` and time `τ`. -/
theorem counterexample_euler_lagrange {a : ℝ} (ha : a ≠ 0) (d τ : ℝ) :
    -- α-equation
    HasDerivAt (fun t => (lSol a d t : ℝ)) (a * zVel a d τ ^ 2 + (zSol a d τ - a)) τ ∧
    -- z-equation
    HasDerivAt (fun t => a ^ 2 * zVel a d t) (-(zSol a d τ - a)) τ ∧
    -- λ-equation (∂L/∂λ' ≡ 0 and ∂L/∂λ = α' = 0)
    HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 τ ∧
    -- the velocities are the time derivatives of the coordinates
    HasDerivAt (fun _ : ℝ => a) 0 τ ∧ HasDerivAt (zSol a d) (zVel a d τ) τ ∧
    HasDerivAt (lSol a d) (lRate a d τ) τ := by
  refine ⟨lSol_hasDerivAt a d τ, ?_, hasDerivAt_const _ _, hasDerivAt_const _ _,
    zSol_hasDerivAt ha d τ, lSol_hasDerivAt a d τ⟩
  have := (zVel_hasDerivAt ha d τ).const_mul (a ^ 2)
  refine this.congr_deriv ?_
  unfold zAcc zSol; field_simp; ring

/-- The Euler–Lagrange equations, stated with the partial derivatives of the
encoded Lagrangian: along the curve the momenta `∂_{q'} L` are differentiable
with derivative `∂_q L`.  Here `pα, pz, pl` are the partials in the velocity
slots and `fα, fz, fl` those in the position slots (each identified by
`lagrangian_hasDerivAt_*`). -/
theorem counterexample_euler_lagrange_partials {a : ℝ} (ha : a ≠ 0) (d τ : ℝ) :
    let q := fun t => (a, zSol a d t, lSol a d t)
    let v := fun t => ((0 : ℝ), zVel a d t, lRate a d t)
    -- velocity-slot partials along the curve
    (∀ t, HasDerivAt (fun s => lagrangian (q t).1 (q t).2.1 (q t).2.2 s (v t).2.1 (v t).2.2)
        (lSol a d t) 0) ∧
    (∀ t, HasDerivAt (fun s => lagrangian (q t).1 (q t).2.1 (q t).2.2 (v t).1 s (v t).2.2)
        (a ^ 2 * zVel a d t) (zVel a d t)) ∧
    (∀ t, HasDerivAt (fun s => lagrangian (q t).1 (q t).2.1 (q t).2.2 (v t).1 (v t).2.1 s)
        0 (lRate a d t)) ∧
    -- position-slot partials along the curve
    HasDerivAt (fun s => lagrangian s (q τ).2.1 (q τ).2.2 (v τ).1 (v τ).2.1 (v τ).2.2)
        (a * zVel a d τ ^ 2 + (zSol a d τ - a)) a ∧
    HasDerivAt (fun s => lagrangian (q τ).1 s (q τ).2.2 (v τ).1 (v τ).2.1 (v τ).2.2)
        (-(zSol a d τ - a)) (zSol a d τ) ∧
    HasDerivAt (fun s => lagrangian (q τ).1 (q τ).2.1 s (v τ).1 (v τ).2.1 (v τ).2.2)
        0 (lSol a d τ) ∧
    -- Euler–Lagrange: d/dτ (velocity partial) = position partial
    HasDerivAt (fun t => lSol a d t) (a * zVel a d τ ^ 2 + (zSol a d τ - a)) τ ∧
    HasDerivAt (fun t => a ^ 2 * zVel a d t) (-(zSol a d τ - a)) τ ∧
    HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 τ := by
  intro q v
  obtain ⟨h1, h2, h3, -, -, -⟩ := counterexample_euler_lagrange ha d τ
  exact ⟨fun t => lagrangian_hasDerivAt_α' _ _ _ _ _ _,
    fun t => lagrangian_hasDerivAt_z' _ _ _ _ _ _,
    fun t => lagrangian_hasDerivAt_l' _ _ _ _ _ _,
    lagrangian_hasDerivAt_α _ _ _ _ _ _,
    lagrangian_hasDerivAt_z _ _ _ _ _ _,
    lagrangian_hasDerivAt_l _ _ _ _ _ _, h1, h2, h3⟩

/-- Initial records and the scaled initial acceleration of the `d`-family:
`z(0) = 0`, `z'(0) = a² d`, `λ(0) = 0`, `λ'(0) = a⁵ d² - a`, and
`a z''(0) = 1` for every `d` (the example following
`prop:supp-finite-acc-invariance`: changing the initial weak rate by `a² d`
does not remove the defect). -/
theorem counterexample_jet_family_defect {a : ℝ} (ha : a ≠ 0) (d : ℝ) :
    zSol a d 0 = 0 ∧ zVel a d 0 = a ^ 2 * d ∧ lSol a d 0 = 0 ∧
    lRate a d 0 = a ^ 5 * d ^ 2 - a ∧ a * zAcc a d 0 = 1 := by
  refine ⟨by simp [zSol], by simp [zVel], by simp [lSol], ?_, ?_⟩
  · simp [lRate, zVel, zSol]; ring
  · simp [zAcc]; field_simp

/-- Uniform first-derivative bounds for the `d = 0` solution:
`|z'(τ)| ≤ 1` and `|λ'(τ)| ≤ 2a` for all `τ` (and `α' = 0`). -/
theorem counterexample_first_derivative_bounds {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    |zVel a 0 τ| ≤ 1 ∧ |lRate a 0 τ| ≤ 2 * a := by
  have hs := Real.abs_sin_le_one (τ / a)
  have hc := Real.abs_cos_le_one (τ / a)
  refine ⟨by simpa [zVel] using hs, ?_⟩
  have hl : lRate a 0 τ = a * Real.sin (τ / a) ^ 2 - a * Real.cos (τ / a) := by
    simp [lRate, zVel, zSol]; ring
  rw [hl]
  have hs2 : Real.sin (τ / a) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact hs
  have hs0 : 0 ≤ Real.sin (τ / a) ^ 2 := sq_nonneg _
  rw [abs_le] at hc ⊢
  constructor <;> nlinarith

/-- `prop:supp-exact-initial-counterexample`.  For the unchanged polynomial
Lagrangian `eq:supp-exact-counterexample-L` and every amplitude `a > 0`, the
exact solution `α ≡ a`, `z = a (1 - cos(τ/a))`, `λ = ∫₀^τ (a z'² + z - a)`
(`eq:supp-exact-counterexample-solution`):
1. solves all three Euler–Lagrange equations at every time;
2. has initial records `α(0) = a`, `z(0) = 0`, `λ(0) = 0` and initial velocities
   `α'(0) = 0`, `z'(0) = 0`, `λ'(0) = -a`, all polynomial (analytic, bounded) in `a`;
3. has uniformly bounded first derivatives: `|z'| ≤ 1`, `|λ'| ≤ 2a`, `α' = 0`;
4. but `a z''(0) = 1` for every `a`, so the scaled acceleration defect tends to
   `1 ≠ 0` as `a ↓ 0`. -/
theorem prop_supp_exact_initial_counterexample :
    (∀ a : ℝ, 0 < a → ∀ τ : ℝ,
      HasDerivAt (lSol a 0) (a * zVel a 0 τ ^ 2 + (zSol a 0 τ - a)) τ ∧
      HasDerivAt (fun t => a ^ 2 * zVel a 0 t) (-(zSol a 0 τ - a)) τ ∧
      HasDerivAt (zSol a 0) (zVel a 0 τ) τ ∧
      HasDerivAt (zVel a 0) (zAcc a 0 τ) τ) ∧
    (∀ a : ℝ, 0 < a →
      zSol a 0 0 = 0 ∧ lSol a 0 0 = 0 ∧ zVel a 0 0 = 0 ∧ lRate a 0 0 = -a) ∧
    (∀ a : ℝ, 0 < a → ∀ τ : ℝ, |zVel a 0 τ| ≤ 1 ∧ |lRate a 0 τ| ≤ 2 * a) ∧
    (∀ a : ℝ, 0 < a → a * zAcc a 0 0 = 1) ∧
    Filter.Tendsto (fun a => a * zAcc a 0 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hdef : ∀ a : ℝ, 0 < a → a * zAcc a 0 0 = 1 := fun a ha =>
    (counterexample_jet_family_defect ha.ne' 0).2.2.2.2
  refine ⟨fun a ha τ => ?_, fun a ha => ?_, fun a ha τ =>
    counterexample_first_derivative_bounds ha τ, hdef, ?_⟩
  · obtain ⟨h1, h2, -, -, h5, -⟩ := counterexample_euler_lagrange ha.ne' 0 τ
    exact ⟨h1, h2, h5, zVel_hasDerivAt ha.ne' 0 τ⟩
  · obtain ⟨e1, e2, e3, e4, -⟩ := counterexample_jet_family_defect ha.ne' 0
    exact ⟨e1, e3, by simpa using e2, by simpa using e4⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (hdef a ha).symm

end

end ExactInitialCounterexample
end RenewalGeometry
