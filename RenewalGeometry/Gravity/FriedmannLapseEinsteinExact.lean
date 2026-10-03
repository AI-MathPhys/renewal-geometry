/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.CoordinateCurvatureJetLipschitz
import RenewalGeometry.Gravity.RenewalFriedmannExact

/-!
# The full lapse-varied vacuum Einstein equation of the homogeneous renewal sector
  (`thm:main-homogeneous-friedmann`, last sentence: "the complete vacuum Einstein equation
  within the spatially flat homogeneous isotropic ansatz, including the lapse constraint";
  emergent-spacetime manuscript)

This file computes, from the metric itself, the Einstein tensor of
`g = -N(t)² dt² + a(t)² δᵢⱼ dxⁱ dxʲ` with an arbitrary positive lapse `N`, and identifies the
vacuum equation `G + Λ g = 0` with the two Euler equations of the renewal-rate action.

* `partialDeriv` — the coordinate partial derivative `∂_c f(x)` of a scalar field on `ℝ⁴`
  (a Mathlib `deriv` along the `c`-th coordinate line);
* `metricJetOf g x` — the metric 2-jet `((g x)⁻¹, ∂g, ∂∂g)` of a metric *field* `g`, with the
  inverse taken at type `Matrix` and all derivatives genuine coordinate partial derivatives;
  `einsteinOf g x = Ric - ½ R g` with the Ricci tensor `CoordinateCurvatureJet.ricciJet` of
  that jet (Christoffel symbols `Γ = ½ g⁻¹(∂g + ∂g - ∂g)` and their derivatives by the product
  rule, `Riem = ∂Γ - ∂Γ + ΓΓ - ΓΓ`);
* `lapseMetric N a` — the metric field `diag(-N(x⁰)², a(x⁰)², a(x⁰)², a(x⁰)²)`;
  `metricJetOf_lapseMetric` evaluates its jet (only `a` twice differentiable at the point and
  differentiable nearby, `N` differentiable at the point; `∂₀²g₀₀` is never needed — it cancels
  identically);
* `lapse_einstein_00`, `lapse_einstein_spatial`, `lapse_einstein_offdiag` — the components
  `G₀₀ = 3 ȧ²/a² = N²·3𝓗²`, `Gₖₖ = -(2aä/N² - 2aȧṄ/N³ + ȧ²/N²) = -a²(2 D_τ𝓗 + 3𝓗²)`,
  `G_{μν} = 0` (`μ ≠ ν`), with `𝓗 = ȧ/(Na)` and `D_τ = N⁻¹ d/dt` (`hubbleRate`,
  `properTimeDeriv` of `RenewalFriedmannExact`);
* `lapse_vacuum_einstein_iff` — `G + Λ g = 0` (all sixteen components) iff
  `3𝓗² = Λ` (the `00` lapse constraint) and `D_τ𝓗 = 0` (the spatial equations given the
  constraint);
* `renewal_euler_einstein_components` — for the metric reconstructed from the renewal variables
  `u = log κ`, `v = log ϱ` by `eq:main-isotropic-renewal-map`, the exact identities
  `G₀₀ + Λg₀₀ = (N/a³) E_u` and `Gₖₖ + Λgₖₖ = -(E_v/2 - E_u/3)/(N a)` with the Euler expressions
  `E_u, E_v` of the renewal-rate action;
* `renewal_stationary_iff_vacuum_einstein` — **`thm:main-homogeneous-friedmann`, last clause**:
  `E_u = E_v = 0` iff the reconstructed metric solves the complete vacuum Einstein equation
  `G + Λ g = 0`, iff `3𝓗² = Λ ∧ D_τ𝓗 = 0`.

Non-vacuity: `desitter_lapseMetric_vacuum` — the de Sitter profile `a = e^{Ht}`, `N = 1` solves
`G + 3H² g = 0` (computed by this machinery), and `lapse_einstein_00_ne_zero_example` — for the
non-static profile `a = e^t`, `N = 2` the `00` component is `3 ≠ 0`.
-/

open Filter Topology
open scoped BigOperators

namespace RenewalGeometry.FriedmannLapseEinstein

open CoordinateCurvatureJet

noncomputable section

/-! ### Coordinate partial derivatives and the curvature of a metric field -/

/-- The coordinate partial derivative `∂_c f (x)` of a scalar field on `ℝ⁴`. -/
def partialDeriv (f : (Fin 4 → ℝ) → ℝ) (c : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  deriv (fun s => f (Function.update x c s)) (x c)

/-- A field depending only on the time coordinate `x⁰` has only a time derivative. -/
theorem partialDeriv_time (f : ℝ → ℝ) (c : Fin 4) (x : Fin 4 → ℝ) :
    partialDeriv (fun y => f (y 0)) c x = if c = 0 then deriv f (x 0) else 0 := by
  unfold partialDeriv
  split_ifs with hc
  · subst hc
    simp only [Function.update_self]
  · have : (fun s => f (Function.update x c s 0)) = fun _ => f (x 0) := by
      funext s
      rw [Function.update_of_ne (Ne.symm hc)]
    rw [this, deriv_const]

/-- The metric 2-jet `(g⁻¹, ∂g, ∂∂g)` of a metric field `g` at `x`: inverse at type `Matrix`,
`∂_c g_{ij}` and `∂_d ∂_c g_{ij}` genuine coordinate partial derivatives (index conventions of
`CoordinateCurvatureJet.dChristoffel`). -/
def metricJetOf (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : Jet :=
  (fun i j => (g x)⁻¹ i j,
    fun c i j => partialDeriv (fun y => g y i j) c x,
    fun d c i j => partialDeriv (fun y => partialDeriv (fun z => g z i j) c y) d x)

/-- Scalar curvature `R = g^{μν} R_{μν}` of a metric field. -/
def scalarOf (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ μ, ∑ ν, (metricJetOf g x).1 μ ν * ricciJet (metricJetOf g x) μ ν

/-- Einstein tensor `G_{μν} = R_{μν} - ½ R g_{μν}` of a metric field. -/
def einsteinOf (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => ricciJet (metricJetOf g x) μ ν - (1 / 2) * scalarOf g x * g x μ ν

/-! ### The lapse-FLRW metric field -/

/-- Entries of `diag(-N², a², a², a²)` as functions of time. -/
def lapseEntry (N a : ℝ → ℝ) (i j : Fin 4) (s : ℝ) : ℝ :=
  if i = j then (if i = 0 then -(N s ^ 2) else a s ^ 2) else 0

/-- The homogeneous isotropic metric field `g = -N(x⁰)² dt² + a(x⁰)² δᵢⱼ dxⁱ dxʲ`. -/
def lapseMetric (N a : ℝ → ℝ) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun i => if i = 0 then -(N (x 0) ^ 2) else a (x 0) ^ 2

theorem lapseMetric_apply (N a : ℝ → ℝ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    lapseMetric N a x i j = lapseEntry N a i j (x 0) := by
  unfold lapseMetric lapseEntry
  rw [Matrix.diagonal_apply]

/-- Closed form of the inverse metric `diag(-N⁻², a⁻², a⁻², a⁻²)`. -/
def ginvVal (Nv av : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => if i = j then (if i = 0 then -(Nv ^ 2)⁻¹ else (av ^ 2)⁻¹) else 0

theorem lapseMetric_inv (N a : ℝ → ℝ) (x : Fin 4 → ℝ) (hN : N (x 0) ≠ 0) (ha : a (x 0) ≠ 0)
    (i j : Fin 4) : (lapseMetric N a x)⁻¹ i j = ginvVal (N (x 0)) (a (x 0)) i j := by
  have h : (lapseMetric N a x)⁻¹ =
      Matrix.diagonal fun i => if i = 0 then -(N (x 0) ^ 2)⁻¹ else (a (x 0) ^ 2)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    unfold lapseMetric
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    split_ifs
    · field_simp
    · field_simp
  rw [h, Matrix.diagonal_apply]
  unfold ginvVal
  rfl

/-- Closed form of `∂_c g_{ij}`: only `∂₀g₀₀ = -2NṄ` and `∂₀gₖₖ = 2aȧ`. -/
def dgVal (Nv N'v av a'v : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun c i j => if c = 0 ∧ i = j then (if i = 0 then -(2 * Nv * N'v) else 2 * av * a'v) else 0

/-- Closed form of `∂_d ∂_c g_{ij}`: `∂₀²gₖₖ = 2(ȧ² + aä)`; the value `X = ∂₀²g₀₀` is left
free (it cancels from the curvature). -/
def ddgVal (av a'v a''v X : ℝ) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun d c i j => if d = 0 ∧ c = 0 ∧ i = j then
    (if i = 0 then X else 2 * (a'v ^ 2 + av * a''v)) else 0

theorem deriv_lapseEntry {N a N' a' : ℝ → ℝ} {t : ℝ} (hN : HasDerivAt N (N' t) t)
    (ha : HasDerivAt a (a' t) t) (i j : Fin 4) :
    deriv (lapseEntry N a i j) t =
      if i = j then (if i = 0 then -(2 * N t * N' t) else 2 * a t * a' t) else 0 := by
  unfold lapseEntry
  split_ifs with hij hi
  · have h : HasDerivAt (fun s => -(N s ^ 2)) (-(2 * N t * N' t)) t := by
      have e : (fun s => -(N s ^ 2)) = -(N * N) := by
        funext s; simp [sq]
      rw [e]
      exact (hN.mul hN).neg.congr_deriv (by ring)
    exact h.deriv
  · have h : HasDerivAt (fun s => a s ^ 2) (2 * a t * a' t) t := by
      have e : (fun s => a s ^ 2) = a * a := by
        funext s; simp [sq]
      rw [e]
      exact (ha.mul ha).congr_deriv (by ring)
    exact h.deriv
  · exact deriv_const _ _

theorem deriv_deriv_lapseEntry_spatial {N a a' : ℝ → ℝ} {t a'' : ℝ}
    (ha : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) (ha' : HasDerivAt a' a'' t) (i j : Fin 4)
    (hij : i = j) (hi : i ≠ 0) :
    deriv (deriv (lapseEntry N a i j)) t = 2 * (a' t ^ 2 + a t * a'') := by
  subst hij
  have heq : deriv (lapseEntry N a i i) =ᶠ[𝓝 t] fun s => 2 * a s * a' s := by
    filter_upwards [ha] with s hs
    have h : HasDerivAt (lapseEntry N a i i) (2 * a s * a' s) s := by
      have he : lapseEntry N a i i = fun s => a s ^ 2 := by
        funext r; unfold lapseEntry; simp [hi]
      have e : (fun s => a s ^ 2) = a * a := by
        funext s; simp [sq]
      rw [he, e]
      exact (hs.mul hs).congr_deriv (by ring)
    exact h.deriv
  rw [heq.deriv_eq]
  have ha0 : HasDerivAt a (a' t) t := ha.self_of_nhds
  have h : HasDerivAt (fun s => 2 * a s * a' s) (2 * (a' t ^ 2 + a t * a'')) t := by
    exact ((ha0.const_mul 2).mul ha').congr_deriv (by ring)
  exact h.deriv

/-- **The metric 2-jet of the lapse-FLRW field**, computed from its coordinate derivatives. -/
theorem metricJetOf_lapseMetric {N a N' a' : ℝ → ℝ} {a'' : ℝ} {x : Fin 4 → ℝ}
    (hN : HasDerivAt N (N' (x 0)) (x 0)) (ha : ∀ᶠ s in 𝓝 (x 0), HasDerivAt a (a' s) s)
    (ha' : HasDerivAt a' a'' (x 0)) (hNpos : N (x 0) ≠ 0) (hapos : a (x 0) ≠ 0) :
    metricJetOf (lapseMetric N a) x =
      (ginvVal (N (x 0)) (a (x 0)), dgVal (N (x 0)) (N' (x 0)) (a (x 0)) (a' (x 0)),
        ddgVal (a (x 0)) (a' (x 0)) a'' (deriv (deriv (lapseEntry N a 0 0)) (x 0))) := by
  have ha0 : HasDerivAt a (a' (x 0)) (x 0) := ha.self_of_nhds
  unfold metricJetOf
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i j
    exact lapseMetric_inv N a x hNpos hapos i j
  · funext c i j
    simp only [lapseMetric_apply]
    rw [partialDeriv_time, deriv_lapseEntry hN ha0]
    unfold dgVal
    by_cases hc : c = 0 <;> by_cases hij : i = j <;> simp [hc, hij]
  · funext d c i j
    simp only [lapseMetric_apply]
    have hinner : (fun y : Fin 4 → ℝ => partialDeriv (fun z => lapseEntry N a i j (z 0)) c y) =
        fun y => (fun s => if c = 0 then deriv (lapseEntry N a i j) s else 0) (y 0) := by
      funext y
      rw [partialDeriv_time]
    rw [hinner, partialDeriv_time (fun s => if c = 0 then deriv (lapseEntry N a i j) s else 0)]
    unfold ddgVal
    by_cases hd : d = 0
    · by_cases hc : c = 0
      · simp only [hd, hc, if_true, true_and]
        by_cases hij : i = j
        · by_cases hi : i = 0
          · subst hij; subst hi; simp
          · rw [if_pos hij, if_neg hi]
            exact deriv_deriv_lapseEntry_spatial ha ha' i j hij hi
        · rw [if_neg hij]
          have : lapseEntry N a i j = fun _ => 0 := by
            funext s; unfold lapseEntry; rw [if_neg hij]
          rw [this]
          simp
      · simp [hd, hc]
    · simp [hd]

/-! ### Christoffel symbols and their derivatives -/

/-- Closed form of the Christoffel symbols of the lapse-FLRW jet:
`Γ⁰₀₀ = Ṅ/N`, `Γ⁰ₖₖ = aȧ/N²`, `Γᵏ₀ₖ = Γᵏₖ₀ = ȧ/a`, all others zero. -/
def lapseGamma (Nv N'v av a'v : ℝ) : Arr3 := fun c i j =>
  if c = 0 then (if i = 0 ∧ j = 0 then N'v / Nv else if i = j then av * a'v / Nv ^ 2 else 0)
  else (if (i = 0 ∧ j = c) ∨ (j = 0 ∧ i = c) then a'v / av else 0)

/-- Closed form of `∂_d Γ^c_{ij}` of the lapse-FLRW jet (only `d = 0`). -/
def lapseDGamma (Nv N'v av a'v a''v X : ℝ) : Arr4 := fun d c i j =>
  if d = 0 then
    (if c = 0 then
      (if i = 0 ∧ j = 0 then -(2 * N'v ^ 2 / Nv ^ 2) - X / (2 * Nv ^ 2)
       else if i = j then (a'v ^ 2 + av * a''v) / Nv ^ 2 - 2 * av * a'v * N'v / Nv ^ 3 else 0)
     else (if (i = 0 ∧ j = c) ∨ (j = 0 ∧ i = c) then a''v / av - a'v ^ 2 / av ^ 2 else 0))
  else 0

theorem christoffel_lapse {Nv av : ℝ} (hN : Nv ≠ 0) (ha : av ≠ 0) (N'v a'v : ℝ) :
    christoffel (ginvVal Nv av) (dgVal Nv N'v av a'v) = lapseGamma Nv N'v av a'v := by
  funext c i j
  unfold christoffel ginvVal dgVal lapseGamma
  fin_cases c <;> fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four] <;> field_simp <;> ring

theorem dChristoffel_lapse {Nv av : ℝ} (hN : Nv ≠ 0) (ha : av ≠ 0) (N'v a'v a''v X : ℝ) :
    dChristoffel (ginvVal Nv av) (dgVal Nv N'v av a'v) (ddgVal av a'v a''v X) =
      lapseDGamma Nv N'v av a'v a''v X := by
  funext d c i j
  unfold dChristoffel dInvMetric ginvVal dgVal ddgVal lapseDGamma
  fin_cases d
  · fin_cases c <;> fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_four] <;> field_simp <;> ring
  all_goals simp

/-! ### Ricci tensor and Einstein tensor -/

/-- The Ricci tensor of the lapse-FLRW connection jet:
`R₀₀ = -3ä/a + 3ȧṄ/(aN)`, `Rₖₖ = (aä + 2ȧ²)/N² - aȧṄ/N³`, off-diagonal zero. -/
theorem ricci_lapse {Nv av : ℝ} (hN : Nv ≠ 0) (ha : av ≠ 0) (N'v a'v a''v X : ℝ) :
    ricci (lapseGamma Nv N'v av a'v) (lapseDGamma Nv N'v av a'v a''v X) 0 0 =
        -(3 * a''v / av) + 3 * a'v * N'v / (av * Nv) ∧
      (∀ k : Fin 4, k ≠ 0 →
        ricci (lapseGamma Nv N'v av a'v) (lapseDGamma Nv N'v av a'v a''v X) k k =
          (av * a''v + 2 * a'v ^ 2) / Nv ^ 2 - av * a'v * N'v / Nv ^ 3) ∧
      (∀ i j : Fin 4, i ≠ j →
        ricci (lapseGamma Nv N'v av a'v) (lapseDGamma Nv N'v av a'v a''v X) i j = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ricci riemann lapseGamma lapseDGamma
    simp [Fin.sum_univ_four]
    field_simp
    ring
  · intro k hk
    unfold ricci riemann lapseGamma lapseDGamma
    fin_cases k
    · exact absurd rfl hk
    all_goals simp [Fin.sum_univ_four]; field_simp; ring
  · intro i j hij
    unfold ricci riemann lapseGamma lapseDGamma
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simp [Fin.sum_univ_four]

/-- Regularity packet at the evaluation time `t = x⁰`: `a` differentiable near `t` with
derivative `a'`, `a'` differentiable at `t`, `N` differentiable at `t`, `N, a > 0`. -/
structure LapseRegular (N a N' a' : ℝ → ℝ) (a'' t : ℝ) : Prop where
  hasDerivAt_N : HasDerivAt N (N' t) t
  hasDerivAt_a : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s
  hasDerivAt_a' : HasDerivAt a' a'' t
  N_pos : 0 < N t
  a_pos : 0 < a t

theorem ricciJet_lapse {N a N' a' : ℝ → ℝ} {a'' : ℝ} {x : Fin 4 → ℝ}
    (hr : LapseRegular N a N' a' a'' (x 0)) :
    ricciJet (metricJetOf (lapseMetric N a) x) =
      ricci (lapseGamma (N (x 0)) (N' (x 0)) (a (x 0)) (a' (x 0)))
        (lapseDGamma (N (x 0)) (N' (x 0)) (a (x 0)) (a' (x 0)) a''
          (deriv (deriv (lapseEntry N a 0 0)) (x 0))) := by
  rw [metricJetOf_lapseMetric hr.hasDerivAt_N hr.hasDerivAt_a hr.hasDerivAt_a'
    hr.N_pos.ne' hr.a_pos.ne']
  unfold ricciJet
  simp only
  rw [christoffel_lapse hr.N_pos.ne' hr.a_pos.ne', dChristoffel_lapse hr.N_pos.ne' hr.a_pos.ne']

/-- Scalar curvature of the lapse-FLRW metric:
`R = 6ä/(aN²) + 6ȧ²/(a²N²) - 6ȧṄ/(aN³)`. -/
theorem scalarOf_lapse {N a N' a' : ℝ → ℝ} {a'' : ℝ} {x : Fin 4 → ℝ}
    (hr : LapseRegular N a N' a' a'' (x 0)) :
    scalarOf (lapseMetric N a) x =
      6 * a'' / (a (x 0) * N (x 0) ^ 2) + 6 * a' (x 0) ^ 2 / (a (x 0) ^ 2 * N (x 0) ^ 2) -
        6 * a' (x 0) * N' (x 0) / (a (x 0) * N (x 0) ^ 3) := by
  have hN := hr.N_pos.ne'
  have ha := hr.a_pos.ne'
  obtain ⟨h00, hkk, hoff⟩ := ricci_lapse hN ha (N' (x 0)) (a' (x 0)) a''
    (deriv (deriv (lapseEntry N a 0 0)) (x 0))
  unfold scalarOf
  rw [ricciJet_lapse hr, metricJetOf_lapseMetric hr.hasDerivAt_N hr.hasDerivAt_a
    hr.hasDerivAt_a' hN ha]
  simp only [Fin.sum_univ_four]
  rw [h00, hkk 1 (by decide), hkk 2 (by decide), hkk 3 (by decide)]
  unfold ginvVal
  simp
  field_simp
  ring

/-- `G₀₀ = 3ȧ²/a²` for the lapse-FLRW metric (independent of `N`). -/
theorem lapse_einstein_00 {N a N' a' : ℝ → ℝ} {a'' : ℝ} {x : Fin 4 → ℝ}
    (hr : LapseRegular N a N' a' a'' (x 0)) :
    einsteinOf (lapseMetric N a) x 0 0 = 3 * (a' (x 0) / a (x 0)) ^ 2 := by
  have hN := hr.N_pos.ne'
  have ha := hr.a_pos.ne'
  obtain ⟨h00, -, -⟩ := ricci_lapse hN ha (N' (x 0)) (a' (x 0)) a''
    (deriv (deriv (lapseEntry N a 0 0)) (x 0))
  unfold einsteinOf
  rw [Matrix.of_apply, ricciJet_lapse hr, h00, scalarOf_lapse hr, lapseMetric_apply]
  unfold lapseEntry
  simp
  field_simp
  ring

/-- `Gₖₖ = -(2aä/N² - 2aȧṄ/N³ + ȧ²/N²)` for the lapse-FLRW metric. -/
theorem lapse_einstein_spatial {N a N' a' : ℝ → ℝ} {a'' : ℝ} {x : Fin 4 → ℝ}
    (hr : LapseRegular N a N' a' a'' (x 0)) (k : Fin 4) (hk : k ≠ 0) :
    einsteinOf (lapseMetric N a) x k k =
      -(2 * a (x 0) * a'' / N (x 0) ^ 2 - 2 * a (x 0) * a' (x 0) * N' (x 0) / N (x 0) ^ 3 +
        a' (x 0) ^ 2 / N (x 0) ^ 2) := by
  have hN := hr.N_pos.ne'
  have ha := hr.a_pos.ne'
  obtain ⟨-, hkk, -⟩ := ricci_lapse hN ha (N' (x 0)) (a' (x 0)) a''
    (deriv (deriv (lapseEntry N a 0 0)) (x 0))
  unfold einsteinOf
  rw [Matrix.of_apply, ricciJet_lapse hr, hkk k hk, scalarOf_lapse hr, lapseMetric_apply]
  unfold lapseEntry
  simp only [if_true, hk, if_false]
  field_simp
  ring

/-- `G_{μν} = 0` for `μ ≠ ν`. -/
theorem lapse_einstein_offdiag {N a N' a' : ℝ → ℝ} {a'' : ℝ} {x : Fin 4 → ℝ}
    (hr : LapseRegular N a N' a' a'' (x 0)) (i j : Fin 4) (hij : i ≠ j) :
    einsteinOf (lapseMetric N a) x i j = 0 := by
  have hN := hr.N_pos.ne'
  have ha := hr.a_pos.ne'
  obtain ⟨-, -, hoff⟩ := ricci_lapse hN ha (N' (x 0)) (a' (x 0)) a''
    (deriv (deriv (lapseEntry N a 0 0)) (x 0))
  unfold einsteinOf
  rw [Matrix.of_apply, ricciJet_lapse hr, hoff i j hij, lapseMetric_apply]
  unfold lapseEntry
  simp [hij]

/-! ### Hubble-rate form and the vacuum equation -/

theorem hasDerivAt_hubbleRate {N a N' a' : ℝ → ℝ} {a'' t : ℝ}
    (hr : LapseRegular N a N' a' a'' t) :
    HasDerivAt (hubbleRate a a' N)
      ((a'' * (N t * a t) - a' t * (N' t * a t + N t * a' t)) / (N t * a t) ^ 2) t := by
  have hd := hr.hasDerivAt_a'.div (hr.hasDerivAt_N.mul hr.hasDerivAt_a.self_of_nhds)
    (mul_pos hr.N_pos hr.a_pos).ne'
  exact hd

theorem properTimeDeriv_hubbleRate {N a N' a' : ℝ → ℝ} {a'' t : ℝ}
    (hr : LapseRegular N a N' a' a'' t) :
    properTimeDeriv N (hubbleRate a a' N) t =
      a'' / (N t ^ 2 * a t) - a' t * N' t / (N t ^ 3 * a t) - a' t ^ 2 / (N t ^ 2 * a t ^ 2) := by
  unfold properTimeDeriv
  rw [(hasDerivAt_hubbleRate hr).deriv]
  have := hr.N_pos.ne'
  have := hr.a_pos.ne'
  field_simp
  ring

/-- The `00` component (lapse constraint): `G₀₀ + Λ g₀₀ = N² (3𝓗² - Λ)`. -/
theorem lapse_einstein_constraint {N a N' a' : ℝ → ℝ} {a'' : ℝ} {x : Fin 4 → ℝ}
    (hr : LapseRegular N a N' a' a'' (x 0)) (Λ : ℝ) :
    einsteinOf (lapseMetric N a) x 0 0 + Λ * lapseMetric N a x 0 0 =
      N (x 0) ^ 2 * (3 * hubbleRate a a' N (x 0) ^ 2 - Λ) := by
  rw [lapse_einstein_00 hr, lapseMetric_apply]
  unfold lapseEntry hubbleRate
  have := hr.N_pos.ne'
  have := hr.a_pos.ne'
  simp
  field_simp
  ring

/-- The spatial components: `Gₖₖ + Λ gₖₖ = -a² (2 D_τ𝓗 + 3𝓗² - Λ)`. -/
theorem lapse_einstein_dynamical {N a N' a' : ℝ → ℝ} {a'' : ℝ} {x : Fin 4 → ℝ}
    (hr : LapseRegular N a N' a' a'' (x 0)) (Λ : ℝ) (k : Fin 4) (hk : k ≠ 0) :
    einsteinOf (lapseMetric N a) x k k + Λ * lapseMetric N a x k k =
      -(a (x 0) ^ 2) * (2 * properTimeDeriv N (hubbleRate a a' N) (x 0) +
        3 * hubbleRate a a' N (x 0) ^ 2 - Λ) := by
  rw [lapse_einstein_spatial hr k hk, lapseMetric_apply, properTimeDeriv_hubbleRate hr]
  unfold lapseEntry hubbleRate
  have := hr.N_pos.ne'
  have := hr.a_pos.ne'
  simp only [if_true, hk, if_false]
  field_simp
  ring

/-- **The complete vacuum Einstein equation of the homogeneous isotropic ansatz, with the lapse
retained**: `G + Λ g = 0` (all sixteen components) iff `3𝓗² = Λ` and `D_τ𝓗 = 0`. -/
theorem lapse_vacuum_einstein_iff {N a N' a' : ℝ → ℝ} {a'' : ℝ} {x : Fin 4 → ℝ}
    (hr : LapseRegular N a N' a' a'' (x 0)) (Λ : ℝ) :
    (∀ μ ν : Fin 4, einsteinOf (lapseMetric N a) x μ ν + Λ * lapseMetric N a x μ ν = 0) ↔
      (3 * hubbleRate a a' N (x 0) ^ 2 = Λ ∧
        properTimeDeriv N (hubbleRate a a' N) (x 0) = 0) := by
  have hN2 : 0 < N (x 0) ^ 2 := pow_pos hr.N_pos 2
  have ha2 : 0 < a (x 0) ^ 2 := pow_pos hr.a_pos 2
  constructor
  · intro h
    have h0 := h 0 0
    rw [lapse_einstein_constraint hr Λ] at h0
    have hc : 3 * hubbleRate a a' N (x 0) ^ 2 - Λ = 0 := by
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' hN2.ne'
      · exact h'
    have h1 := h 1 1
    rw [lapse_einstein_dynamical hr Λ 1 (by decide)] at h1
    have hd : 2 * properTimeDeriv N (hubbleRate a a' N) (x 0) +
        3 * hubbleRate a a' N (x 0) ^ 2 - Λ = 0 := by
      rcases mul_eq_zero.mp h1 with h' | h'
      · exact absurd h' (neg_ne_zero.mpr ha2.ne')
      · exact h'
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hc, hd⟩ μ ν
    by_cases hμν : μ = ν
    · subst hμν
      by_cases hμ : μ = 0
      · subst hμ
        rw [lapse_einstein_constraint hr Λ, hc, sub_self, mul_zero]
      · rw [lapse_einstein_dynamical hr Λ μ hμ, hd, hc]
        ring
    · rw [lapse_einstein_offdiag hr μ ν hμν, lapseMetric_apply]
      unfold lapseEntry
      simp [hμν]

/-! ### The metric reconstructed from the renewal variables -/

/-- Regularity of the renewal paths at `t`: `u` differentiable at `t`, `v` differentiable near
`t` with derivative `v'`, and `v'` differentiable at `t` (the hypotheses of
`renewal_stationary_iff_friedmann`, with `v` differentiable on a neighbourhood). -/
theorem lapseRegular_renewal {u u' v v' v'' : ℝ → ℝ} {t : ℝ}
    (hu : HasDerivAt u (u' t) t) (hv : ∀ᶠ s in 𝓝 t, HasDerivAt v (v' s) s)
    (hv' : HasDerivAt v' (v'' t) t) :
    LapseRegular (renewalLapse u v) (renewalScaleFactor v)
      (fun s => Real.exp (u s / 2 + v s / 3) * (u' s / 2 + v' s / 3))
      (renewalScaleFactorDeriv v v')
      (Real.exp (v t / 3) * (v' t / 3) * v' t / 3 + Real.exp (v t / 3) * v'' t / 3) t where
  hasDerivAt_N := by
    have := ((hu.div_const 2).add (hv.self_of_nhds.div_const 3)).exp
    exact this
  hasDerivAt_a := by
    filter_upwards [hv] with s hs
    exact hasDerivAt_renewalScaleFactor hs
  hasDerivAt_a' := by
    have h := ((hv.self_of_nhds.div_const 3).exp.mul hv').div_const 3
    unfold renewalScaleFactorDeriv
    exact h.congr_deriv (by ring)
  N_pos := Real.exp_pos _
  a_pos := Real.exp_pos _

/-- **Euler expressions = Einstein components.**  For the metric
`g = -N² dt² + a² δ` reconstructed from the renewal variables by
`eq:main-isotropic-renewal-map` (`a = e^{v/3}`, `N = e^{u/2 + v/3}`), the Euler expressions of
the renewal-rate action are, exactly, the `00` and spatial Einstein components:
`G₀₀ + Λ g₀₀ = (N/a³) E_u`, `Gₖₖ + Λ gₖₖ = -(E_v/2 - E_u/3)/(N a)`, and the off-diagonal
components vanish. -/
theorem renewal_euler_einstein_components (Λ : ℝ) {u u' v v' v'' : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hu : HasDerivAt u (u' (x 0)) (x 0)) (hv : ∀ᶠ s in 𝓝 (x 0), HasDerivAt v (v' s) s)
    (hv' : HasDerivAt v' (v'' (x 0)) (x 0)) :
    einsteinOf (lapseMetric (renewalLapse u v) (renewalScaleFactor v)) x 0 0 +
        Λ * lapseMetric (renewalLapse u v) (renewalScaleFactor v) x 0 0 =
      renewalLapse u v (x 0) / renewalScaleFactor v (x 0) ^ 3 * eulerU Λ u u' v v' (x 0) ∧
    (∀ k : Fin 4, k ≠ 0 →
      einsteinOf (lapseMetric (renewalLapse u v) (renewalScaleFactor v)) x k k +
          Λ * lapseMetric (renewalLapse u v) (renewalScaleFactor v) x k k =
        -((eulerV Λ u u' v v' (x 0) / 2 - eulerU Λ u u' v v' (x 0) / 3) /
          (renewalLapse u v (x 0) * renewalScaleFactor v (x 0)))) ∧
    (∀ μ ν : Fin 4, μ ≠ ν →
      einsteinOf (lapseMetric (renewalLapse u v) (renewalScaleFactor v)) x μ ν +
          Λ * lapseMetric (renewalLapse u v) (renewalScaleFactor v) x μ ν = 0) := by
  have hr := lapseRegular_renewal hu hv hv'
  have hN : 0 < renewalLapse u v (x 0) := Real.exp_pos _
  have ha : 0 < renewalScaleFactor v (x 0) := Real.exp_pos _
  refine ⟨?_, fun k hk => ?_, fun μ ν hμν => ?_⟩
  · rw [lapse_einstein_constraint hr Λ, eulerU_eq]
    field_simp
  · rw [lapse_einstein_dynamical hr Λ k hk, eulerU_eq, eulerV_eq Λ hu hv.self_of_nhds hv']
    field_simp
    ring
  · rw [lapse_einstein_offdiag hr μ ν hμν, lapseMetric_apply]
    unfold lapseEntry
    simp [hμν]

/-- **`thm:main-homogeneous-friedmann`, last clause.**  Stationarity of the renewal-rate action
in the two independent positive renewal variables (`E_u = E_v = 0`) is equivalent to the
complete vacuum Einstein equation `G + Λ g = 0` of the reconstructed metric
`-N² dt² + a² δ` (all components, the lapse constraint `00` included), and both are equivalent
to the vacuum Friedmann system `3𝓗² = Λ`, `D_τ𝓗 = 0`. -/
theorem renewal_stationary_iff_vacuum_einstein (Λ : ℝ) {u u' v v' v'' : ℝ → ℝ}
    {x : Fin 4 → ℝ}
    (hu : HasDerivAt u (u' (x 0)) (x 0)) (hv : ∀ᶠ s in 𝓝 (x 0), HasDerivAt v (v' s) s)
    (hv' : HasDerivAt v' (v'' (x 0)) (x 0)) :
    ((eulerU Λ u u' v v' (x 0) = 0 ∧ eulerV Λ u u' v v' (x 0) = 0) ↔
      ∀ μ ν : Fin 4,
        einsteinOf (lapseMetric (renewalLapse u v) (renewalScaleFactor v)) x μ ν +
          Λ * lapseMetric (renewalLapse u v) (renewalScaleFactor v) x μ ν = 0) ∧
    ((∀ μ ν : Fin 4,
        einsteinOf (lapseMetric (renewalLapse u v) (renewalScaleFactor v)) x μ ν +
          Λ * lapseMetric (renewalLapse u v) (renewalScaleFactor v) x μ ν = 0) ↔
      (3 * hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
          (renewalLapse u v) (x 0) ^ 2 = Λ ∧
        properTimeDeriv (renewalLapse u v)
          (hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
            (renewalLapse u v)) (x 0) = 0)) := by
  have hr := lapseRegular_renewal hu hv hv'
  have hE := lapse_vacuum_einstein_iff hr Λ
  exact ⟨(renewal_stationary_iff_friedmann Λ hu hv.self_of_nhds hv').trans hE.symm, hE⟩

/-- **`thm:main-homogeneous-friedmann`** assembled: the renewal-rate Lagrangian is the reduced
homogeneous Lagrangian under `ϱ = a³`, `κ = N²/a²`; its Euler expressions are
`E_u = N a³(3𝓗² - Λ)`, `E_v = N a³[4 D_τ𝓗 + (8/3)(3𝓗² - Λ)]`; and stationarity is equivalent
to the vacuum Friedmann system and to the complete vacuum Einstein equation of the
reconstructed metric (lapse constraint included). -/
theorem homogeneous_friedmann_complete (Λ : ℝ) {u u' v v' v'' : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hu : HasDerivAt u (u' (x 0)) (x 0)) (hv : ∀ᶠ s in 𝓝 (x 0), HasDerivAt v (v' s) s)
    (hv' : HasDerivAt v' (v'' (x 0)) (x 0)) :
    (∀ a a' N : ℝ, 0 < a → 0 < N →
      renewalRateLagrangian Λ (N ^ 2 / a ^ 2) (a ^ 3) (3 * a ^ 2 * a') =
        homogeneousLagrangian Λ a a' N) ∧
    eulerU Λ u u' v v' (x 0) =
      renewalLapse u v (x 0) * renewalScaleFactor v (x 0) ^ 3 *
        (3 * hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
          (renewalLapse u v) (x 0) ^ 2 - Λ) ∧
    eulerV Λ u u' v v' (x 0) =
      renewalLapse u v (x 0) * renewalScaleFactor v (x 0) ^ 3 *
        (4 * properTimeDeriv (renewalLapse u v)
            (hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
              (renewalLapse u v)) (x 0) +
          8 / 3 * (3 * hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
            (renewalLapse u v) (x 0) ^ 2 - Λ)) ∧
    ((eulerU Λ u u' v v' (x 0) = 0 ∧ eulerV Λ u u' v v' (x 0) = 0) ↔
      (3 * hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
          (renewalLapse u v) (x 0) ^ 2 = Λ ∧
        properTimeDeriv (renewalLapse u v)
          (hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
            (renewalLapse u v)) (x 0) = 0)) ∧
    ((eulerU Λ u u' v v' (x 0) = 0 ∧ eulerV Λ u u' v v' (x 0) = 0) ↔
      ∀ μ ν : Fin 4,
        einsteinOf (lapseMetric (renewalLapse u v) (renewalScaleFactor v)) x μ ν +
          Λ * lapseMetric (renewalLapse u v) (renewalScaleFactor v) x μ ν = 0) :=
  ⟨fun a a' N ha hN => renewalRateLagrangian_eq_homogeneous Λ a a' N ha hN,
    eulerU_eq Λ u u' v v' (x 0), eulerV_eq Λ hu hv.self_of_nhds hv',
    renewal_stationary_iff_friedmann Λ hu hv.self_of_nhds hv',
    (renewal_stationary_iff_vacuum_einstein Λ hu hv hv').1⟩

/-! ### Non-vacuity -/

/-- The de Sitter profile `a = e^{Ht}`, `N = 1` solves `G + 3H² g = 0`, computed by the
metric-field machinery above. -/
theorem desitter_lapseMetric_vacuum (H : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    einsteinOf (lapseMetric (fun _ => 1) (fun s => Real.exp (H * s))) x μ ν +
      3 * H ^ 2 * lapseMetric (fun _ => 1) (fun s => Real.exp (H * s)) x μ ν = 0 := by
  have hr : LapseRegular (fun _ => 1) (fun s => Real.exp (H * s)) (fun _ => 0)
      (fun s => H * Real.exp (H * s)) (H ^ 2 * Real.exp (H * x 0)) (x 0) := by
    refine ⟨hasDerivAt_const _ _, Eventually.of_forall fun s => ?_, ?_, one_pos,
      Real.exp_pos _⟩
    · have := ((hasDerivAt_id s).const_mul H).exp
      simpa [mul_comm] using this
    · have := (((hasDerivAt_id (x 0)).const_mul H).exp).const_mul H
      refine this.congr_deriv ?_
      simp; ring
  have hH : hubbleRate (fun s => Real.exp (H * s)) (fun s => H * Real.exp (H * s))
      (fun _ => 1) = fun _ => H := by
    funext s
    unfold hubbleRate
    have := Real.exp_pos (H * s)
    field_simp
  refine (lapse_vacuum_einstein_iff hr (3 * H ^ 2)).2 ⟨?_, ?_⟩ μ ν
  · rw [hH]
  · unfold properTimeDeriv
    rw [hH, deriv_const, mul_zero]

/-- The machinery is not degenerate: for the non-static profile `a = e^t`, `N = 2`, the
`00` Einstein component is `3 ≠ 0`. -/
theorem lapse_einstein_00_ne_zero_example (x : Fin 4 → ℝ) :
    einsteinOf (lapseMetric (fun _ => 2) Real.exp) x 0 0 = 3 := by
  have hr : LapseRegular (fun _ => 2) Real.exp (fun _ => 0) Real.exp (Real.exp (x 0)) (x 0) :=
    ⟨hasDerivAt_const _ _, Eventually.of_forall fun s => Real.hasDerivAt_exp s,
      Real.hasDerivAt_exp _, two_pos, Real.exp_pos _⟩
  rw [lapse_einstein_00 hr, div_self (Real.exp_pos _).ne']
  norm_num

end

end RenewalGeometry.FriedmannLapseEinstein
