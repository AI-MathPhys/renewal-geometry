/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallDivergence

/-!
# Gaffney, Friedrichs and Poincaré inequalities for tangential one-forms on Euclidean balls
  (stage C1 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.  One-forms `u = (u_ν)` on `Fin n → ℝ`
(`n ≥ 1`) with the **vanishing normal component** `(x - c)·u = 0` on `∂B_r(c)` (the boundary
condition of Uhlenbeck's Neumann–Coulomb gauge), all classical (`C²`).

* `sum_mul_pd_eq_zero_of_tangent`: tangential derivatives of a function vanishing on a sphere
  vanish (the curve `c + r(x - c + tv)/|x - c + tv|`).
* `gradSq_eq` (**pointwise Bochner–Gaffney identity**):
  `|∇u|² = ½|du|² + (div u)² + div V`, `V_μ = Σ_ν (u_ν ∂_ν u_μ - u_μ ∂_ν u_ν)` (`gaffV`),
  using the symmetry of second derivatives (`pd_pd_symm`);
* `gaffV_boundary`: on `∂B_r(c)`, `⟨V, x - c⟩ = -|u|²` (the second fundamental form of the
  sphere, `II = g/r > 0`: convexity);
* `gaffney_ball` (**Gaffney's identity**):
  `∫_B |∇u|² + r^{n-1}(1/r) ∫_{S^{n-1}} |u(c+rω)|² dσ = ∫_B (½|du|² + (div u)²)`, and
  `gaffney_ball_le`: `∫_B |∇u|² ≤ ∫_B (½|du|² + (div u)²)`;
* `friedrichs_ball` (**Friedrichs' trace–Poincaré inequality**, every `C¹` `f`, no boundary
  condition): `(n-1) ∫_B f² ≤ r^n ∫_{S^{n-1}} f(c+rω)² dσ + r² ∫_B |∇f|²`;
* `poincare_ball_tangential` (**Poincaré inequality for tangential forms**, quantitative, no
  compactness): `(n-1) ∫_B |u|² ≤ r² ∫_B (½|du|² + (div u)²)` — in particular there are no
  harmonic fields (`du = 0`, `div u = 0`) with vanishing normal component on a ball;
* complex-valued versions `gaffney_ball_complex`, `poincare_ball_complex` (real and imaginary
  parts).

Conventions: `curlSq u = Σ_{μν} (∂_μ u_ν - ∂_ν u_μ)²` (full double sum, i.e. `2|du|²` in form
norms), `divF u = Σ_μ ∂_μ u_μ = -d^*u`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ### Calculus helpers -/

theorem contDiff_pd_of_two {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin n) :
    ContDiff ℝ 1 (pd f i) := by
  unfold pd
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- **Schwarz**: mixed partials of a `C²` function commute. -/
theorem pd_pd_symm {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (μ ν : Fin n) (x : Fin n → ℝ) :
    pd (pd f ν) μ x = pd (pd f μ) ν x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.contDiffAt.fderiv_right (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) x := h1.differentiableAt one_ne_zero
  have hsymm := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have key : ∀ v w : Fin n → ℝ,
      fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
    intro v w
    rw [fderiv_clm_apply h2 (differentiableAt_const v)]
    simp
  show fderiv ℝ (fun y => fderiv ℝ f y (Pi.single ν 1)) x (Pi.single μ 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single μ 1)) x (Pi.single ν 1)
  rw [key, key]
  exact hsymm _ _

theorem pd_add_real {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    pd (fun y => f y + g y) i x = pd f i x + pd g i x := by
  unfold pd
  rw [show (fun y => f y + g y) = f + g from rfl, (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  rfl

theorem pd_sub_real {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    pd (fun y => f y - g y) i x = pd f i x - pd g i x := by
  unfold pd
  rw [show (fun y => f y - g y) = f - g from rfl, (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]
  rfl

theorem pd_sum_real {κ : Type*} {s : Finset κ} {F : κ → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : ∀ k ∈ s, DifferentiableAt ℝ (F k) x) (i : Fin n) :
    pd (fun y => ∑ k ∈ s, F k y) i x = ∑ k ∈ s, pd (F k) i x := by
  unfold pd
  have hs := HasFDerivAt.sum (u := s) fun k hk => (h k hk).hasFDerivAt
  rw [show (fun y => ∑ k ∈ s, F k y) = ∑ k ∈ s, F k from by funext y; simp [Finset.sum_apply],
    hs.fderiv]
  simp

theorem pd_mul_real {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    pd (fun y => f y * g y) i x = pd f i x * g x + f x * pd g i x := by
  unfold pd
  rw [show (fun y => f y * g y) = f * g from rfl, (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem pd_coord_sub (c : Fin n → ℝ) (μ ν : Fin n) (x : Fin n → ℝ) :
    pd (fun y : Fin n → ℝ => y μ - c μ) ν x = if μ = ν then 1 else 0 := by
  have h0 : HasFDerivAt (fun y : Fin n → ℝ => y μ)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) μ) x := hasFDerivAt_apply μ x
  unfold pd
  rw [(h0.sub_const (c μ)).fderiv]
  simp [Pi.single_apply, eq_comm]

/-- The directional derivative is the sum of partials. -/
theorem fderiv_apply_eq_sum_pd {f : (Fin n → ℝ) → ℝ} (x v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ i, v i * pd f i x :=
  clm_apply_eq_sum (fderiv ℝ f x) v

/-! ### Tangential derivatives on spheres -/

/-- **Tangential derivatives of a function vanishing on a sphere vanish**: if `f` vanishes on
`∂B_r(c)`, is differentiable at `x ∈ ∂B_r(c)` and `v ⊥ x - c`, then `∂_v f(x) = 0`.  (Proof: the
curve `γ(t) = c + r (x - c + tv)/|x - c + tv|` stays on the sphere, `γ(0) = x`, `γ'(0) = v`.) -/
theorem sum_mul_pd_eq_zero_of_tangent {c x : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    {f : (Fin n → ℝ) → ℝ} (hf : DifferentiableAt ℝ f x)
    (hS : ∀ y, sqDist c y = r ^ 2 → f y = 0) (hx : sqDist c x = r ^ 2) {v : Fin n → ℝ}
    (hv : ∑ i, (x i - c i) * v i = 0) : ∑ i, v i * pd f i x = 0 := by
  set V := ∑ i, v i ^ 2 with hVdef
  have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set q : ℝ → ℝ := fun t => r ^ 2 + t ^ 2 * V
  have hq : ∀ t, 0 < q t := fun t => by simp only [q]; positivity
  set g : ℝ → ℝ := fun t => r / Real.sqrt (q t)
  set γ : ℝ → Fin n → ℝ := fun t => c + g t • (x - c + t • v)
  have hsq : ∀ t, ∑ i, (x i - c i + t * v i) ^ 2 = q t := fun t => by
    simp only [q]
    have e : ∀ i, (x i - c i + t * v i) ^ 2 = (x i - c i) ^ 2 + 2 * t * ((x i - c i) * v i) +
        t ^ 2 * v i ^ 2 := fun i => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    unfold sqDist at hx
    rw [hx, hv]; ring
  have hγS : ∀ t, sqDist c (γ t) = r ^ 2 := fun t => by
    unfold sqDist
    simp only [γ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left,
      mul_pow]
    rw [← Finset.mul_sum, hsq t]
    simp only [g, div_pow, Real.sq_sqrt (hq t).le]
    field_simp [(hq t).ne']
  have hg0 : g 0 = 1 := by
    simp only [g, q]; simp [Real.sqrt_sq hr.le, hr.ne']
  have hγ0 : γ 0 = x := by simp [γ, hg0]
  -- derivative of the curve at 0
  have hq' : HasDerivAt q 0 0 := by
    have := ((hasDerivAt_pow 2 (0 : ℝ)).mul_const V).const_add (r ^ 2)
    exact this.congr_deriv (by simp)
  have hs' : HasDerivAt (fun t => Real.sqrt (q t)) 0 0 := by
    have := hq'.sqrt (hq 0).ne'
    exact this.congr_deriv (by simp)
  have hg' : HasDerivAt g 0 0 := by
    have := (hasDerivAt_const (0 : ℝ) r).div hs' (Real.sqrt_pos.mpr (hq 0)).ne'
    exact this.congr_deriv (by simp)
  have hy' : HasDerivAt (fun t : ℝ => x - c + t • v) v 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (x - c)
    exact this.congr_deriv (by simp)
  have hγ' : HasDerivAt γ v 0 := by
    have := (hg'.smul hy').const_add c
    exact this.congr_deriv (by simp [hg0])
  have h1 : HasDerivAt (f ∘ γ) (fderiv ℝ f x v) 0 := by
    rw [← hγ0] at hf
    have := hf.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ'
    rwa [hγ0] at this
  have h2 : HasDerivAt (f ∘ γ) 0 0 := by
    have : f ∘ γ = fun _ => 0 := funext fun t => hS _ (hγS t)
    rw [this]; exact hasDerivAt_const _ _
  rw [← fderiv_apply_eq_sum_pd]
  exact h1.unique h2


/-! ### One-forms: the Gaffney identity -/

/-- `|∇u|² = Σ_{μν} (∂_μ u_ν)²` for a real one-form `u = (u_ν)`. -/
def gradSq (u : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ μ, ∑ ν, pd (u ν) μ x ^ 2

/-- `|du|²` in the full-sum convention `Σ_{μν} (∂_μ u_ν - ∂_ν u_μ)²` (twice the form norm). -/
def curlSq (u : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ μ, ∑ ν, (pd (u ν) μ x - pd (u μ) ν x) ^ 2

/-- `-d^*u = div u = Σ_μ ∂_μ u_μ`. -/
def divF (u : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ μ, pd (u μ) μ x

/-- `|u|² = Σ_ν u_ν²`. -/
def normSq (u : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ ν, u ν x ^ 2

/-- The Gaffney vector field `V_μ = Σ_ν (u_ν ∂_ν u_μ - u_μ ∂_ν u_ν)`, with
`|∇u|² = ½|du|² + (div u)² + div V`. -/
def gaffV (u : Fin n → (Fin n → ℝ) → ℝ) (μ : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ ν, (u ν x * pd (u μ) ν x - u μ x * pd (u ν) ν x)

theorem contDiff_gaffV {u : Fin n → (Fin n → ℝ) → ℝ} (hu : ∀ ν, ContDiff ℝ 2 (u ν)) (μ : Fin n) :
    ContDiff ℝ 1 (gaffV u μ) := by
  have h1 : ∀ ν, ContDiff ℝ 1 (u ν) := fun ν => (hu ν).of_le (by norm_num)
  unfold gaffV
  exact ContDiff.sum fun ν _ => ((h1 ν).mul (contDiff_pd_of_two (hu μ) ν)).sub
    ((h1 μ).mul (contDiff_pd_of_two (hu ν) ν))

theorem pd_gaffV {u : Fin n → (Fin n → ℝ) → ℝ} (hu : ∀ ν, ContDiff ℝ 2 (u ν)) (μ : Fin n)
    (x : Fin n → ℝ) :
    pd (gaffV u μ) μ x = ∑ ν, ((pd (u ν) μ x * pd (u μ) ν x + u ν x * pd (pd (u μ) ν) μ x) -
      (pd (u μ) μ x * pd (u ν) ν x + u μ x * pd (pd (u ν) ν) μ x)) := by
  have d1 : ∀ ν, DifferentiableAt ℝ (u ν) x := fun ν =>
    ((hu ν).differentiable (by norm_num)) x
  have d2 : ∀ ν μ, DifferentiableAt ℝ (pd (u μ) ν) x := fun ν μ =>
    ((contDiff_pd_of_two (hu μ) ν).differentiable (by norm_num)) x
  unfold gaffV
  rw [pd_sum_real (F := fun ν y => u ν y * pd (u μ) ν y - u μ y * pd (u ν) ν y)
    (fun ν _ => ((d1 ν).mul (d2 ν μ)).sub ((d1 μ).mul (d2 ν ν)))]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [pd_sub_real (f := fun y => u ν y * pd (u μ) ν y) (g := fun y => u μ y * pd (u ν) ν y)
    ((d1 ν).mul (d2 ν μ)) ((d1 μ).mul (d2 ν ν)), pd_mul_real (d1 ν) (d2 ν μ),
    pd_mul_real (d1 μ) (d2 ν ν)]

/-- **Pointwise Gaffney (Bochner) identity** for real `C²` one-forms:
`|∇u|² = ½|du|² + (div u)² + div V`. -/
theorem gradSq_eq {u : Fin n → (Fin n → ℝ) → ℝ} (hu : ∀ ν, ContDiff ℝ 2 (u ν))
    (x : Fin n → ℝ) :
    gradSq u x = curlSq u x / 2 + divF u x ^ 2 + ∑ μ, pd (gaffV u μ) μ x := by
  simp only [pd_gaffV hu]
  -- symmetric second-derivative terms cancel
  have hT : ∑ μ, ∑ ν, u ν x * pd (pd (u μ) ν) μ x = ∑ μ, ∑ ν, u μ x * pd (pd (u ν) ν) μ x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [pd_pd_symm (hu μ) ν μ x]
  have hD : divF u x ^ 2 = ∑ μ, ∑ ν, pd (u μ) μ x * pd (u ν) ν x := by
    rw [divF, sq, Finset.sum_mul_sum]
  have hG : ∑ μ, ∑ ν, pd (u μ) ν x ^ 2 = gradSq u x := by
    rw [gradSq, Finset.sum_comm]
  have hC : curlSq u x = 2 * gradSq u x - 2 * ∑ μ, ∑ ν, pd (u ν) μ x * pd (u μ) ν x := by
    have e : ∀ μ ν, (pd (u ν) μ x - pd (u μ) ν x) ^ 2 =
        pd (u ν) μ x ^ 2 + pd (u μ) ν x ^ 2 - 2 * (pd (u ν) μ x * pd (u μ) ν x) :=
      fun μ ν => by ring
    simp only [curlSq, e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hG, gradSq]; ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hT, hD, hC]
  ring

variable [NeZero n]

/-- **The boundary term of Gaffney's identity on a sphere**: if `x·u` (`= Σ (x_μ - c_μ) u_μ`)
vanishes on `∂B_r(c)`, then at every `x ∈ ∂B_r(c)`, `⟨V(x), x - c⟩ = -|u(x)|²` (the second
fundamental form of the sphere of radius `r` is `1/r` times the metric). -/
theorem gaffV_boundary {c : Fin n → ℝ} {r : ℝ} (hr : 0 < r) {u : Fin n → (Fin n → ℝ) → ℝ}
    (hu : ∀ ν, ContDiff ℝ 2 (u ν))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, (y μ - c μ) * u μ y = 0) {x : Fin n → ℝ}
    (hx : sqDist c x = r ^ 2) :
    ∑ μ, gaffV u μ x * (x μ - c μ) = -normSq u x := by
  have d1 : ∀ ν, DifferentiableAt ℝ (u ν) x := fun ν =>
    ((hu ν).differentiable (by norm_num)) x
  set f : (Fin n → ℝ) → ℝ := fun y => ∑ μ, (y μ - c μ) * u μ y
  have dcoord : ∀ μ, DifferentiableAt ℝ (fun y : Fin n → ℝ => y μ - c μ) x := fun μ =>
    ((differentiableAt_apply μ x).sub_const (c μ))
  have hfd : DifferentiableAt ℝ f x :=
    DifferentiableAt.fun_sum fun μ _ => (dcoord μ).mul (d1 μ)
  have hpf : ∀ ν, pd f ν x = u ν x + ∑ μ, (x μ - c μ) * pd (u μ) ν x := fun ν => by
    simp only [f]
    rw [pd_sum_real (F := fun μ y => (y μ - c μ) * u μ y) (fun μ _ => (dcoord μ).mul (d1 μ))]
    have e : ∀ μ, pd (fun y => (y μ - c μ) * u μ y) ν x =
        (if μ = ν then 1 else 0) * u μ x + (x μ - c μ) * pd (u μ) ν x := fun μ => by
      rw [pd_mul_real (dcoord μ) (d1 μ), pd_coord_sub]
    simp only [e, Finset.sum_add_distrib]
    congr 1
    simp [ite_mul]
  have htan := sum_mul_pd_eq_zero_of_tangent hr hfd hS hx (v := fun ν => u ν x) (hS x hx)
  have hfx : ∑ μ, (x μ - c μ) * u μ x = 0 := hS x hx
  have e1 : ∑ μ, gaffV u μ x * (x μ - c μ) =
      ∑ ν, u ν x * (∑ μ, (x μ - c μ) * pd (u μ) ν x) -
        (∑ μ, (x μ - c μ) * u μ x) * divF u x := by
    have hL : ∑ μ, gaffV u μ x * (x μ - c μ) =
        ∑ μ, ∑ ν, (u ν x * pd (u μ) ν x * (x μ - c μ)) -
          ∑ μ, ∑ ν, ((x μ - c μ) * u μ x * pd (u ν) ν x) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [gaffV, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ν _ => by ring
    have hR1 : ∑ ν, u ν x * (∑ μ, (x μ - c μ) * pd (u μ) ν x) =
        ∑ μ, ∑ ν, (u ν x * pd (u μ) ν x * (x μ - c μ)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
    have hR2 : (∑ μ, (x μ - c μ) * u μ x) * divF u x =
        ∑ μ, ∑ ν, ((x μ - c μ) * u μ x * pd (u ν) ν x) := by
      rw [divF, Finset.sum_mul_sum]
    rw [hL, hR1, hR2]
  rw [e1, hfx, zero_mul, sub_zero]
  have e2 : ∀ ν, ∑ μ, (x μ - c μ) * pd (u μ) ν x = pd f ν x - u ν x := fun ν => by
    rw [hpf ν]; ring
  simp only [e2, mul_sub, Finset.sum_sub_distrib, htan, normSq, sq]
  ring


/-! ### Continuity of the quadratic densities -/

theorem continuous_gradSq {u : Fin n → (Fin n → ℝ) → ℝ} (hu : ∀ ν, ContDiff ℝ 1 (u ν)) :
    Continuous (gradSq u) := by
  unfold gradSq
  exact continuous_finset_sum _ fun μ _ => continuous_finset_sum _ fun ν _ =>
    (continuous_pd (hu ν) μ).pow 2

theorem continuous_curlSq {u : Fin n → (Fin n → ℝ) → ℝ} (hu : ∀ ν, ContDiff ℝ 1 (u ν)) :
    Continuous (curlSq u) := by
  unfold curlSq
  exact continuous_finset_sum _ fun μ _ => continuous_finset_sum _ fun ν _ =>
    ((continuous_pd (hu ν) μ).sub (continuous_pd (hu μ) ν)).pow 2

theorem continuous_divF {u : Fin n → (Fin n → ℝ) → ℝ} (hu : ∀ ν, ContDiff ℝ 1 (u ν)) :
    Continuous (divF u) := by
  unfold divF
  exact continuous_finset_sum _ fun μ _ => continuous_pd (hu μ) μ

theorem continuous_normSq {u : Fin n → (Fin n → ℝ) → ℝ} (hu : ∀ ν, Continuous (u ν)) :
    Continuous (normSq u) := by
  unfold normSq
  exact continuous_finset_sum _ fun ν _ => (hu ν).pow 2

theorem normSq_nonneg (u : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : 0 ≤ normSq u x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ### Gaffney, Friedrichs and Poincaré on balls -/

/-- **Gaffney's identity on a ball** for real `C²` one-forms `u` with vanishing normal component
`(x - c)·u = 0` on `∂B_r(c)`:
`∫_B |∇u|² + r^{n-1}·(1/r) ∫_{S^{n-1}} |u(c + rω)|² dσ = ∫_B (½|du|² + (div u)²)`.
The boundary term is the second fundamental form `II = (1/r) g` of the sphere evaluated on the
tangential field `u`; it is nonnegative (convexity of the ball). -/
theorem gaffney_ball (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : Fin n → (Fin n → ℝ) → ℝ}
    (hu : ∀ ν, ContDiff ℝ 2 (u ν))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, (y μ - c μ) * u μ y = 0) :
    (∫ x in euclBall c r, gradSq u x) +
        r ^ (n - 1) / r * ∫ w, normSq u (c + r • w) ∂(sphereMeasure n) =
      ∫ x in euclBall c r, (curlSq u x / 2 + divF u x ^ 2) := by
  have hu1 : ∀ ν, ContDiff ℝ 1 (u ν) := fun ν => (hu ν).of_le (by norm_num)
  have hdiv := divergence_ball c hr (gaffV u) (contDiff_gaffV hu)
  have hbd : ∫ w, ∑ μ, gaffV u μ (c + r • w) * w μ ∂(sphereMeasure n) =
      -(r⁻¹ * ∫ w, normSq u (c + r • w) ∂(sphereMeasure n)) := by
    rw [← integral_const_mul, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_sphereMeasure n] with w hw
    have hx := sqDist_add_smul c w r hw
    have hb := gaffV_boundary hr hu hS hx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left] at hb
    have e : ∑ μ, gaffV u μ (c + r • w) * w μ =
        r⁻¹ * ∑ μ, gaffV u μ (c + r • w) * (r * w μ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => by field_simp
    rw [e, hb]; ring
  have hcont1 : Continuous fun x => curlSq u x / 2 + divF u x ^ 2 :=
    ((continuous_curlSq hu1).div_const 2).add ((continuous_divF hu1).pow 2)
  have hcont2 : Continuous fun x => ∑ μ, pd (gaffV u μ) μ x :=
    continuous_finset_sum _ fun μ _ => continuous_pd (contDiff_gaffV hu μ) μ
  have hpt : ∫ x in euclBall c r, gradSq u x =
      (∫ x in euclBall c r, (curlSq u x / 2 + divF u x ^ 2)) +
        ∫ x in euclBall c r, ∑ μ, pd (gaffV u μ) μ x := by
    rw [← integral_add (integrableOn_euclBall hr.le hcont1) (integrableOn_euclBall hr.le hcont2)]
    exact setIntegral_congr_fun (measurableSet_euclBall c r) fun x _ => by rw [gradSq_eq hu x]
  rw [hpt, hdiv, hbd]
  ring

/-- **Gaffney's inequality on a ball**: `∫_B |∇u|² ≤ ∫_B (½|du|² + (div u)²)` for real `C²`
one-forms with vanishing normal component on `∂B_r(c)`. -/
theorem gaffney_ball_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : Fin n → (Fin n → ℝ) → ℝ}
    (hu : ∀ ν, ContDiff ℝ 2 (u ν))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, (y μ - c μ) * u μ y = 0) :
    ∫ x in euclBall c r, gradSq u x ≤ ∫ x in euclBall c r, (curlSq u x / 2 + divF u x ^ 2) := by
  rw [← gaffney_ball c hr hu hS]
  have : 0 ≤ r ^ (n - 1) / r * ∫ w, normSq u (c + r • w) ∂(sphereMeasure n) :=
    mul_nonneg (by positivity) (integral_nonneg fun w => normSq_nonneg u _)
  linarith

/-- **Friedrichs' inequality on a ball** (a trace–Poincaré inequality, from the divergence
theorem applied to `f² (x - c)`): for real `C¹` functions `f`,
`(n - 1) ∫_B f² ≤ r^n ∫_{S^{n-1}} f(c + rω)² dσ + r² ∫_B |∇f|²`. -/
theorem friedrichs_ball (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) :
    ((n : ℝ) - 1) * ∫ x in euclBall c r, f x ^ 2 ≤
      r ^ n * ∫ w, f (c + r • w) ^ 2 ∂(sphereMeasure n) +
        r ^ 2 * ∫ x in euclBall c r, ∑ i, pd f i x ^ 2 := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  set X : Fin n → (Fin n → ℝ) → ℝ := fun i x => f x ^ 2 * (x i - c i)
  have hcoord : ∀ i, ContDiff ℝ 1 (fun x : Fin n → ℝ => x i - c i) := fun i =>
    (contDiff_apply ℝ ℝ i).sub contDiff_const
  have hX : ∀ i, ContDiff ℝ 1 (X i) := fun i => (hf.pow 2).mul (hcoord i)
  have hdf : ∀ x, DifferentiableAt ℝ f x := fun x => (hf.differentiable (by norm_num)) x
  have hpX : ∀ x, ∑ i, pd (X i) i x =
      (n : ℝ) * f x ^ 2 + 2 * f x * ∑ i, (x i - c i) * pd f i x := by
    intro x
    have e : ∀ i, pd (X i) i x = 2 * f x * ((x i - c i) * pd f i x) + f x ^ 2 := fun i => by
      have h1 : pd (fun y => f y ^ 2 * (y i - c i)) i x =
          pd (fun y => f y ^ 2) i x * (x i - c i) + f x ^ 2 * pd (fun y => y i - c i) i x :=
        pd_mul_real ((hdf x).pow 2) (((differentiableAt_apply i x).sub_const (c i))) i
      have h2 : pd (fun y => f y ^ 2) i x = 2 * f x * pd f i x := by
        have := pd_mul_real (hdf x) (hdf x) i
        simp only [← sq] at this; rw [this]; ring
      simp only [X]
      rw [h1, h2, pd_coord_sub]; simp; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hdiv := divergence_ball c hr X hX
  have hbd : ∫ w, ∑ i, X i (c + r • w) * w i ∂(sphereMeasure n) =
      r * ∫ w, f (c + r • w) ^ 2 ∂(sphereMeasure n) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_sphereMeasure n] with w hw
    simp only [X, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
    have : ∑ i, f (c + r • w) ^ 2 * (r * w i) * w i = f (c + r • w) ^ 2 * r * ∑ i, w i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hw]; ring
  simp only [hpX] at hdiv
  rw [hbd] at hdiv
  -- pointwise lower bound on the ball
  have hcf : Continuous fun x => f x ^ 2 := hf.continuous.pow 2
  have hcG : Continuous fun x => ∑ i, pd f i x ^ 2 :=
    continuous_finset_sum _ fun i _ => (continuous_pd hf i).pow 2
  have hcS : Continuous fun x => (n : ℝ) * f x ^ 2 + 2 * f x * ∑ i, (x i - c i) * pd f i x :=
    (continuous_const.mul hcf).add ((continuous_const.mul hf.continuous).mul
      (continuous_finset_sum _ fun i _ => ((continuous_apply i).sub continuous_const).mul
        (continuous_pd hf i)))
  have hmono : ∫ x in euclBall c r, (((n : ℝ) - 1) * f x ^ 2 - r ^ 2 * ∑ i, pd f i x ^ 2) ≤
      ∫ x in euclBall c r, ((n : ℝ) * f x ^ 2 + 2 * f x * ∑ i, (x i - c i) * pd f i x) := by
    refine setIntegral_mono_on (integrableOn_euclBall hr.le
      ((continuous_const.mul hcf).sub (continuous_const.mul hcG)))
      (integrableOn_euclBall hr.le hcS) (measurableSet_euclBall c r) fun x hx => ?_
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => x i - c i) (fun i => pd f i x)
    have hxr : sqDist c x ≤ r ^ 2 := le_of_lt hx
    have hS2 : (∑ i, (x i - c i) * pd f i x) ^ 2 ≤ r ^ 2 * ∑ i, pd f i x ^ 2 :=
      hCS.trans (mul_le_mul_of_nonneg_right hxr (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    nlinarith [sq_nonneg (f x + ∑ i, (x i - c i) * pd f i x)]
  have hsub : ∫ x in euclBall c r, (((n : ℝ) - 1) * f x ^ 2 - r ^ 2 * ∑ i, pd f i x ^ 2) =
      ((n : ℝ) - 1) * (∫ x in euclBall c r, f x ^ 2) -
        r ^ 2 * ∫ x in euclBall c r, ∑ i, pd f i x ^ 2 := by
    rw [integral_sub (f := fun x => ((n : ℝ) - 1) * f x ^ 2)
      (g := fun x => r ^ 2 * ∑ i, pd f i x ^ 2)
      (integrableOn_euclBall hr.le (continuous_const.mul hcf))
      (integrableOn_euclBall hr.le (continuous_const.mul hcG)), integral_const_mul,
      integral_const_mul]
  rw [hsub, hdiv] at hmono
  have hpow : r ^ (n - 1) * (r * ∫ w, f (c + r • w) ^ 2 ∂(sphereMeasure n)) =
      r ^ n * ∫ w, f (c + r • w) ^ 2 ∂(sphereMeasure n) := by
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
  linarith

/-- **Poincaré inequality for tangential one-forms on a ball** (no harmonic fields with
vanishing normal component), quantitative and without compactness:
`(n - 1) ∫_B |u|² ≤ r² ∫_B (½|du|² + (div u)²)` for real `C²` one-forms `u` with `(x - c)·u = 0`
on `∂B_r(c)`.  (Friedrichs for each component + Gaffney's identity, whose boundary term exactly
pays for the trace term of Friedrichs.) -/
theorem poincare_ball_tangential (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {u : Fin n → (Fin n → ℝ) → ℝ} (hu : ∀ ν, ContDiff ℝ 2 (u ν))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, (y μ - c μ) * u μ y = 0) :
    ((n : ℝ) - 1) * ∫ x in euclBall c r, normSq u x ≤
      r ^ 2 * ∫ x in euclBall c r, (curlSq u x / 2 + divF u x ^ 2) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hu1 : ∀ ν, ContDiff ℝ 1 (u ν) := fun ν => (hu ν).of_le (by norm_num)
  have hF := fun ν => friedrichs_ball c hr (hu1 ν)
  have hG := gaffney_ball c hr hu hS
  have e1 : ∫ x in euclBall c r, normSq u x = ∑ ν, ∫ x in euclBall c r, u ν x ^ 2 :=
    integral_finset_sum _ fun ν _ => integrableOn_euclBall hr.le ((hu1 ν).continuous.pow 2)
  have e2 : ∫ w, normSq u (c + r • w) ∂(sphereMeasure n) =
      ∑ ν, ∫ w, u ν (c + r • w) ^ 2 ∂(sphereMeasure n) :=
    integral_finset_sum _ fun ν _ => by
      have h := (hu1 ν).continuous
      exact integrable_sphereMeasure (by fun_prop)
  have e3 : ∫ x in euclBall c r, gradSq u x =
      ∑ ν, ∫ x in euclBall c r, ∑ i, pd (u ν) i x ^ 2 := by
    rw [← integral_finset_sum (f := fun ν x => ∑ i, pd (u ν) i x ^ 2) _
      fun ν _ => integrableOn_euclBall hr.le
      (continuous_finset_sum _ fun i _ => (continuous_pd (hu1 ν) i).pow 2)]
    exact setIntegral_congr_fun (measurableSet_euclBall c r) fun x _ => by
      rw [gradSq, Finset.sum_comm]
  have hsum := Finset.sum_le_sum fun ν (_ : ν ∈ Finset.univ) => hF ν
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [e1]
  rw [e2, e3] at hG
  have hpow : r ^ n = r ^ 2 * (r ^ (n - 1) / r) := by
    have : r ^ n = r ^ (n - 1) * r := by rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [this]; field_simp
  rw [hpow] at hsum
  rw [← hG]
  linarith


/-! ### Complex-valued one-forms -/

/-- `Σ_{μν} ‖∂_μ w_ν‖²` for a complex one-form. -/
def gradSqC (w : Fin n → (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℝ :=
  ∑ μ, ∑ ν, ‖pd (w ν) μ x‖ ^ 2

/-- `Σ_{μν} ‖∂_μ w_ν - ∂_ν w_μ‖²` for a complex one-form. -/
def curlSqC (w : Fin n → (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℝ :=
  ∑ μ, ∑ ν, ‖pd (w ν) μ x - pd (w μ) ν x‖ ^ 2

/-- `div w = Σ_μ ∂_μ w_μ` for a complex one-form. -/
def divC (w : Fin n → (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ := ∑ μ, pd (w μ) μ x

/-- `Σ_ν ‖w_ν‖²`. -/
def normSqC (w : Fin n → (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℝ := ∑ ν, ‖w ν x‖ ^ 2

/-- Real part of a complex one-form. -/
def reF (w : Fin n → (Fin n → ℝ) → ℂ) : Fin n → (Fin n → ℝ) → ℝ := fun ν x => (w ν x).re

/-- Imaginary part of a complex one-form. -/
def imF (w : Fin n → (Fin n → ℝ) → ℂ) : Fin n → (Fin n → ℝ) → ℝ := fun ν x => (w ν x).im

theorem contDiff_reF {w : Fin n → (Fin n → ℝ) → ℂ} {k : WithTop ℕ∞}
    (hw : ∀ ν, ContDiff ℝ k (w ν)) (ν : Fin n) : ContDiff ℝ k (reF w ν) :=
  Complex.reCLM.contDiff.comp (hw ν)

theorem contDiff_imF {w : Fin n → (Fin n → ℝ) → ℂ} {k : WithTop ℕ∞}
    (hw : ∀ ν, ContDiff ℝ k (w ν)) (ν : Fin n) : ContDiff ℝ k (imF w ν) :=
  Complex.imCLM.contDiff.comp (hw ν)

theorem pd_reF {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 1 (w ν)) (ν μ : Fin n)
    (x : Fin n → ℝ) : pd (reF w ν) μ x = (pd (w ν) μ x).re := pd_re (hw ν) μ x

theorem pd_imF {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 1 (w ν)) (ν μ : Fin n)
    (x : Fin n → ℝ) : pd (imF w ν) μ x = (pd (w ν) μ x).im := pd_im (hw ν) μ x

theorem norm_sq_eq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem gradSqC_eq {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 1 (w ν))
    (x : Fin n → ℝ) : gradSqC w x = gradSq (reF w) x + gradSq (imF w) x := by
  simp only [gradSqC, gradSq, pd_reF hw, pd_imF hw, norm_sq_eq_re_im,
    Finset.sum_add_distrib]

theorem curlSqC_eq {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 1 (w ν))
    (x : Fin n → ℝ) : curlSqC w x = curlSq (reF w) x + curlSq (imF w) x := by
  simp only [curlSqC, curlSq, pd_reF hw, pd_imF hw, norm_sq_eq_re_im,
    Complex.sub_re, Complex.sub_im, Finset.sum_add_distrib]

theorem norm_divC_sq {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 1 (w ν))
    (x : Fin n → ℝ) : ‖divC w x‖ ^ 2 = divF (reF w) x ^ 2 + divF (imF w) x ^ 2 := by
  simp only [divC, divF, pd_reF hw, pd_imF hw, norm_sq_eq_re_im, Complex.re_sum,
    Complex.im_sum]

theorem normSqC_eq (w : Fin n → (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    normSqC w x = normSq (reF w) x + normSq (imF w) x := by
  simp only [normSqC, normSq, reF, imF, norm_sq_eq_re_im, Finset.sum_add_distrib]

theorem tangent_re {c : Fin n → ℝ} {r : ℝ} {w : Fin n → (Fin n → ℝ) → ℂ}
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, ((y μ - c μ : ℝ) : ℂ) * w μ y = 0) :
    ∀ y, sqDist c y = r ^ 2 → ∑ μ, (y μ - c μ) * reF w μ y = 0 := fun y hy => by
  have := congrArg Complex.re (hS y hy)
  simpa [Complex.re_sum, reF] using this

theorem tangent_im {c : Fin n → ℝ} {r : ℝ} {w : Fin n → (Fin n → ℝ) → ℂ}
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, ((y μ - c μ : ℝ) : ℂ) * w μ y = 0) :
    ∀ y, sqDist c y = r ^ 2 → ∑ μ, (y μ - c μ) * imF w μ y = 0 := fun y hy => by
  have := congrArg Complex.im (hS y hy)
  simpa [Complex.im_sum, imF] using this

theorem continuous_curlDiv {u : Fin n → (Fin n → ℝ) → ℝ} (hu : ∀ ν, ContDiff ℝ 1 (u ν)) :
    Continuous fun x => curlSq u x / 2 + divF u x ^ 2 :=
  ((continuous_curlSq hu).div_const 2).add ((continuous_divF hu).pow 2)

/-- **Gaffney's inequality on a ball for complex one-forms** with vanishing normal component:
`∫_B Σ‖∂_μ w_ν‖² ≤ ∫_B (½ Σ‖∂_μ w_ν - ∂_ν w_μ‖² + ‖div w‖²)`. -/
theorem gaffney_ball_complex (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 2 (w ν))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, ((y μ - c μ : ℝ) : ℂ) * w μ y = 0) :
    ∫ x in euclBall c r, gradSqC w x ≤
      ∫ x in euclBall c r, (curlSqC w x / 2 + ‖divC w x‖ ^ 2) := by
  have hw1 : ∀ ν, ContDiff ℝ 1 (w ν) := fun ν => (hw ν).of_le (by norm_num)
  have h1 := gaffney_ball_le c hr (contDiff_reF hw) (tangent_re hS)
  have h2 := gaffney_ball_le c hr (contDiff_imF hw) (tangent_im hS)
  have hr1 := contDiff_reF hw1
  have hi1 := contDiff_imF hw1
  have eL : ∫ x in euclBall c r, gradSqC w x =
      (∫ x in euclBall c r, gradSq (reF w) x) + ∫ x in euclBall c r, gradSq (imF w) x := by
    rw [← integral_add (integrableOn_euclBall hr.le (continuous_gradSq hr1))
      (integrableOn_euclBall hr.le (continuous_gradSq hi1))]
    exact setIntegral_congr_fun (measurableSet_euclBall c r) fun x _ => gradSqC_eq hw1 x
  have eR : ∫ x in euclBall c r, (curlSqC w x / 2 + ‖divC w x‖ ^ 2) =
      (∫ x in euclBall c r, (curlSq (reF w) x / 2 + divF (reF w) x ^ 2)) +
        ∫ x in euclBall c r, (curlSq (imF w) x / 2 + divF (imF w) x ^ 2) := by
    rw [← integral_add (integrableOn_euclBall hr.le (continuous_curlDiv hr1))
      (integrableOn_euclBall hr.le (continuous_curlDiv hi1))]
    refine setIntegral_congr_fun (measurableSet_euclBall c r) fun x _ => ?_
    rw [curlSqC_eq hw1, norm_divC_sq hw1]; ring
  rw [eL, eR]; linarith

/-- **Poincaré inequality on a ball for complex tangential one-forms**:
`(n - 1) ∫_B Σ‖w_ν‖² ≤ r² ∫_B (½ Σ‖∂_μ w_ν - ∂_ν w_μ‖² + ‖div w‖²)`. -/
theorem poincare_ball_complex (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 2 (w ν))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, ((y μ - c μ : ℝ) : ℂ) * w μ y = 0) :
    ((n : ℝ) - 1) * ∫ x in euclBall c r, normSqC w x ≤
      r ^ 2 * ∫ x in euclBall c r, (curlSqC w x / 2 + ‖divC w x‖ ^ 2) := by
  have hw1 : ∀ ν, ContDiff ℝ 1 (w ν) := fun ν => (hw ν).of_le (by norm_num)
  have h1 := poincare_ball_tangential c hr (contDiff_reF hw) (tangent_re hS)
  have h2 := poincare_ball_tangential c hr (contDiff_imF hw) (tangent_im hS)
  have hr1 := contDiff_reF hw1
  have hi1 := contDiff_imF hw1
  have eL : ∫ x in euclBall c r, normSqC w x =
      (∫ x in euclBall c r, normSq (reF w) x) + ∫ x in euclBall c r, normSq (imF w) x := by
    rw [← integral_add (integrableOn_euclBall hr.le
      (continuous_normSq fun ν => (hr1 ν).continuous))
      (integrableOn_euclBall hr.le (continuous_normSq fun ν => (hi1 ν).continuous))]
    exact setIntegral_congr_fun (measurableSet_euclBall c r) fun x _ => normSqC_eq w x
  have eR : ∫ x in euclBall c r, (curlSqC w x / 2 + ‖divC w x‖ ^ 2) =
      (∫ x in euclBall c r, (curlSq (reF w) x / 2 + divF (reF w) x ^ 2)) +
        ∫ x in euclBall c r, (curlSq (imF w) x / 2 + divF (imF w) x ^ 2) := by
    rw [← integral_add (integrableOn_euclBall hr.le (continuous_curlDiv hr1))
      (integrableOn_euclBall hr.le (continuous_curlDiv hi1))]
    refine setIntegral_congr_fun (measurableSet_euclBall c r) fun x _ => ?_
    rw [curlSqC_eq hw1, norm_divC_sq hw1]; ring
  rw [eL, eR, mul_add, mul_add]; linarith


/-! ### Non-vacuity -/

/-- The rotation field `(-x₁, x₀, 0, 0)`: a nonzero smooth one-form on `ℝ⁴` tangent to every
sphere centred at `0`, so the hypotheses of `gaffney_ball` / `poincare_ball_tangential` are
satisfiable by nonzero forms. -/
def rotField : Fin 4 → (Fin 4 → ℝ) → ℝ := ![fun y => -y 1, fun y => y 0, fun _ => 0, fun _ => 0]

example : (∀ ν, ContDiff ℝ 2 (rotField ν)) ∧
    ∀ y, sqDist (0 : Fin 4 → ℝ) y = 1 ^ 2 → ∑ μ, (y μ - (0 : Fin 4 → ℝ) μ) * rotField μ y = 0 := by
  refine ⟨fun ν => ?_, fun y _ => ?_⟩
  · fin_cases ν <;> simp [rotField]
    · exact (contDiff_apply ℝ ℝ (1 : Fin 4)).neg
    · exact contDiff_apply ℝ ℝ (0 : Fin 4)
    · exact contDiff_const
    · exact contDiff_const
  · simp [rotField, Fin.sum_univ_four]; ring

end RenewalGeometry.BallAnalysis
