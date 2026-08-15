/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Accepted Bregman gap forces common-action stationarity
  (`thm:accepted-Bregman-stationarity`)

On one determining-field chart carrying the operational Fisher
potential `Ψ` (with `mI ⪯ ∇²Ψ ⪯ MI`, rendered through its
gradient: strong monotonicity, upper monotonicity, and
`M`-Lipschitz bounds) and the reconstructed common action `𝒜`
(with `-λG ⪯ D²𝒜 ⪯ LG`, rendered as relative upper
monotonicity and `ℓM`-Lipschitz bounds, `ℓ = max λ L`), the
proximal objective is `Φ_θ(y) = 𝒜(y) + η⁻¹ D_Ψ(y,θ)` and the
accepted Fisher–Bregman action gap is
`Δ_Ψ(θ,y) = Φ_θ(y) - Φ_θ(y*_θ)`.

This file derives the pointwise convex-analysis layer from the
gradient hypotheses by segment-integral Taylor arguments —
nothing is hypothesized at the level of the conclusions:

* `bregman_lower`: the metric floor
  `D_Ψ(y,θ) ≥ (m/2)‖y-θ‖²`;
* `descent_upper` / `grad_sq_le_gap`: the descent lemma and
  `‖∇Φ_θ(y)‖² ≤ 2Λ_Φ Δ_Ψ(θ,y)` with `Λ_Φ = (η⁻¹+L)M`;
* `resid_sq_le` / `grad_action_le`: the KKT-residual bound and
  the reconstruction of `η∇𝒜(θ)` from the residual;

and then the record's boxed kernel-integrated conclusions for
a stationary law `ν` of the accepted kernel (`K ∘ₘ ν = ν`):

* `integral_bregman_le`: `∫ D_Ψ dνK ≤ η·Δ̄_Ψ`
  (stationarity cancels the action difference);
* `integral_sq_le`: `∫ ‖y-θ‖² dνK ≤ (2η/m)·Δ̄_Ψ`;
* `integral_stationarity_form_le`:
  `∫ 𝔖 dν ≤ C_{Ψ,𝒜,η}·Δ̄_Ψ` with the boxed constant
  `C = 4Λ_Φ/m + 4M²(1+ηℓ)²/(m²η)` for any stationarity form
  `0 ≤ 𝔖 ≤ m⁻¹‖∇𝒜‖²` (the `G⁻¹ ⪯ m⁻¹I` rendering of
  `∇𝒜*G⁻¹∇𝒜`);
* `vanishing_gap_forces_stationarity`: `Δ̄_Ψ = 0` forces the
  complete represented common-action first variation to vanish
  `ν`-almost surely.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace

namespace NCG
namespace BregmanStationarity

variable {E : Type} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Segment-integral Taylor layer -/

/-- Chain rule along an affine segment. -/
theorem hasDerivAt_line (f : E → ℝ) (g : E → E)
    (hg : ∀ x, HasGradientAt f (g x) x) (a v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (a + s • v))
      ⟪g (a + t • v), v⟫ t := by
  have hpath : HasDerivAt (fun s : ℝ => a + s • v) v t := by
    have h1 : HasDerivAt (fun s : ℝ => s • v)
        ((1 : ℝ) • v) t := (hasDerivAt_id t).smul_const v
    rw [one_smul] at h1
    exact h1.const_add a
  have hf := (hg (a + t • v)).hasFDerivAt
  have h := hf.comp_hasDerivAt t hpath
  have hval : (InnerProductSpace.toDual ℝ E
      (g (a + t • v))) v = ⟪g (a + t • v), v⟫ :=
    InnerProductSpace.toDual_apply_apply
  rw [hval] at h
  exact h

/-- Fundamental theorem of calculus for the first-order
Taylor gap. -/
theorem taylor_gap (f : E → ℝ) (g : E → E)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hgc : Continuous g) (a v : E) :
    f (a + v) - f a - ⟪g a, v⟫
      = ∫ t in (0:ℝ)..1,
          (⟪g (a + t • v), v⟫ - ⟪g a, v⟫) := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ =>
        f (a + s • v) - s * ⟪g a, v⟫)
        (⟪g (a + t • v), v⟫ - ⟪g a, v⟫) t := by
    intro t _
    have h1 := hasDerivAt_line f g hg a v t
    have h2 : HasDerivAt
        (fun s : ℝ => s * ⟪g a, v⟫) ⟪g a, v⟫ t := by
      have h3 := (hasDerivAt_id t).mul_const ⟪g a, v⟫
      rwa [one_mul] at h3
    exact h1.sub h2
  have hcont : Continuous (fun t : ℝ =>
      ⟪g (a + t • v), v⟫ - ⟪g a, v⟫) := by
    refine Continuous.sub ?_ continuous_const
    refine Continuous.inner ?_ continuous_const
    exact hgc.comp (by fun_prop)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv (hcont.intervalIntegrable 0 1)
  rw [h]
  simp only [one_smul, zero_smul, add_zero, zero_mul,
    one_mul, sub_zero]
  ring

/-- **The Bregman metric floor**: strong monotonicity of the
gradient gives `f(a+v) - f(a) - ⟪∇f(a),v⟫ ≥ (m/2)‖v‖²`. -/
theorem bregman_floor (f : E → ℝ) (g : E → E)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hgc : Continuous g) (m : ℝ)
    (hmono : ∀ x y : E,
      m * ‖x - y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫)
    (a v : E) :
    m / 2 * ‖v‖ ^ 2 ≤ f (a + v) - f a - ⟪g a, v⟫ := by
  rw [taylor_gap f g hg hgc a v]
  have hlow : ∀ t ∈ Set.Icc (0:ℝ) 1,
      m * t * ‖v‖ ^ 2
        ≤ ⟪g (a + t • v), v⟫ - ⟪g a, v⟫ := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]
      simp
    · have hm := hmono (a + t • v) a
      rw [add_sub_cancel_left] at hm
      have hinner : ⟪g (a + t • v) - g a, t • v⟫
          = t * ⟪g (a + t • v) - g a, v⟫ :=
        real_inner_smul_right _ _ _
      have hnorm : ‖t • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos h0, mul_pow]
      rw [hinner, hnorm] at hm
      have h2 : m * t * ‖v‖ ^ 2
          ≤ ⟪g (a + t • v) - g a, v⟫ := by
        by_contra hcon
        push Not at hcon
        have h4 := mul_lt_mul_of_pos_left hcon h0
        nlinarith
      rwa [inner_sub_left] at h2
  have hint1 : Continuous (fun t : ℝ =>
      m * t * ‖v‖ ^ 2) := by fun_prop
  have hint2 : Continuous (fun t : ℝ =>
      ⟪g (a + t • v), v⟫ - ⟪g a, v⟫) := by
    refine Continuous.sub ?_ continuous_const
    refine Continuous.inner ?_ continuous_const
    exact hgc.comp (by fun_prop)
  have hmono2 := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) zero_le_one
    (hint1.intervalIntegrable 0 1)
    (hint2.intervalIntegrable 0 1) hlow
  have hval : (∫ t in (0:ℝ)..1, m * t * ‖v‖ ^ 2)
      = m / 2 * ‖v‖ ^ 2 := by
    have h1 : (fun t : ℝ => m * t * ‖v‖ ^ 2)
        = fun t : ℝ => (m * ‖v‖ ^ 2) * t := by
      funext t
      ring
    rw [h1, intervalIntegral.integral_const_mul,
      integral_id]
    ring_nf
  rw [hval] at hmono2
  exact hmono2

/-- **The descent inequality**: upper monotonicity of the
gradient gives
`f(a+v) ≤ f(a) + ⟪∇f(a),v⟫ + (Λ/2)‖v‖²`. -/
theorem descent_upper (f : E → ℝ) (g : E → E)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hgc : Continuous g) (Λ : ℝ)
    (hup : ∀ x y : E,
      ⟪g x - g y, x - y⟫ ≤ Λ * ‖x - y‖ ^ 2)
    (a v : E) :
    f (a + v) ≤ f a + ⟪g a, v⟫ + Λ / 2 * ‖v‖ ^ 2 := by
  have hgap := taylor_gap f g hg hgc a v
  have hhigh : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ⟪g (a + t • v), v⟫ - ⟪g a, v⟫
        ≤ Λ * t * ‖v‖ ^ 2 := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]
      simp
    · have hm := hup (a + t • v) a
      rw [add_sub_cancel_left] at hm
      have hinner : ⟪g (a + t • v) - g a, t • v⟫
          = t * ⟪g (a + t • v) - g a, v⟫ :=
        real_inner_smul_right _ _ _
      have hnorm : ‖t • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos h0, mul_pow]
      rw [hinner, hnorm] at hm
      have h2 : ⟪g (a + t • v) - g a, v⟫
          ≤ Λ * t * ‖v‖ ^ 2 := by
        by_contra hcon
        push Not at hcon
        have h4 := mul_lt_mul_of_pos_left hcon h0
        nlinarith
      rw [inner_sub_left] at h2
      exact h2
  have hint1 : Continuous (fun t : ℝ =>
      ⟪g (a + t • v), v⟫ - ⟪g a, v⟫) := by
    refine Continuous.sub ?_ continuous_const
    refine Continuous.inner ?_ continuous_const
    exact hgc.comp (by fun_prop)
  have hint2 : Continuous (fun t : ℝ =>
      Λ * t * ‖v‖ ^ 2) := by fun_prop
  have hmono2 := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) zero_le_one
    (hint1.intervalIntegrable 0 1)
    (hint2.intervalIntegrable 0 1) hhigh
  have hval : (∫ t in (0:ℝ)..1, Λ * t * ‖v‖ ^ 2)
      = Λ / 2 * ‖v‖ ^ 2 := by
    have h1 : (fun t : ℝ => Λ * t * ‖v‖ ^ 2)
        = fun t : ℝ => (Λ * ‖v‖ ^ 2) * t := by
      funext t
      ring
    rw [h1, intervalIntegral.integral_const_mul,
      integral_id]
    ring_nf
  rw [hval] at hmono2
  rw [← hgap] at hmono2
  linarith

/-- **The gradient-squared descent bound**: a `Λ`-smooth
function dominates its minimum by `‖∇f‖²/(2Λ)`. -/
theorem grad_sq_le (f : E → ℝ) (g : E → E)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hgc : Continuous g) (Λ : ℝ) (hΛ : 0 < Λ)
    (hup : ∀ x y : E,
      ⟪g x - g y, x - y⟫ ≤ Λ * ‖x - y‖ ^ 2)
    (z y : E) (hminz : ∀ w, f z ≤ f w) :
    ‖g y‖ ^ 2 ≤ 2 * Λ * (f y - f z) := by
  have h := descent_upper f g hg hgc Λ hup y
    (-(Λ⁻¹ • g y))
  have hinner : ⟪g y, -(Λ⁻¹ • g y)⟫
      = -(Λ⁻¹ * ‖g y‖ ^ 2) := by
    rw [inner_neg_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  have hnorm : ‖-(Λ⁻¹ • g y)‖ ^ 2
      = Λ⁻¹ ^ 2 * ‖g y‖ ^ 2 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), mul_pow]
  rw [hinner, hnorm] at h
  have hz := hminz (y + -(Λ⁻¹ • g y))
  have hΛne : Λ ≠ 0 := ne_of_gt hΛ
  have hkey : f z ≤ f y - Λ⁻¹ / 2 * ‖g y‖ ^ 2 := by
    have h2 : f y + -(Λ⁻¹ * ‖g y‖ ^ 2)
        + Λ / 2 * (Λ⁻¹ ^ 2 * ‖g y‖ ^ 2)
        = f y - Λ⁻¹ / 2 * ‖g y‖ ^ 2 := by
      field_simp
      ring
    linarith [h2 ▸ le_trans hz h]
  have h3 : Λ⁻¹ / 2 * ‖g y‖ ^ 2 ≤ f y - f z := by
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3
    (by positivity : (0:ℝ) ≤ 2 * Λ)
  calc ‖g y‖ ^ 2 = 2 * Λ * (Λ⁻¹ / 2 * ‖g y‖ ^ 2) := by
        field_simp
    _ ≤ 2 * Λ * (f y - f z) := h4

/-! ### The proximal record objects -/

section Record

variable (Ψ 𝒜 : E → ℝ) (gΨ g𝒜 : E → E) (η : ℝ)

/-- The Fisher–Bregman divergence
`D_Ψ(y,θ) = Ψ(y) - Ψ(θ) - ⟪∇Ψ(θ), y-θ⟫`. -/
def bregmanD (y θ : E) : ℝ :=
  Ψ y - Ψ θ - ⟪gΨ θ, y - θ⟫

/-- The proximal objective `Φ_θ(y) = 𝒜(y) + η⁻¹ D_Ψ(y,θ)`. -/
noncomputable def prox (θ y : E) : ℝ :=
  𝒜 y + η⁻¹ * bregmanD Ψ gΨ y θ

/-- The accepted Fisher–Bregman action gap
`Δ_Ψ(θ,y) = Φ_θ(y) - Φ_θ(y*_θ)`. -/
noncomputable def gap (ystar : E → E) (θ y : E) : ℝ :=
  prox Ψ 𝒜 gΨ η θ y - prox Ψ 𝒜 gΨ η θ (ystar θ)

/-- The KKT residual
`r_Ψ(θ,y) = ∇Ψ(y) - ∇Ψ(θ) + η∇𝒜(y)`. -/
def resid (θ y : E) : E := gΨ y - gΨ θ + η • g𝒜 y

omit [CompleteSpace E] in
theorem bregmanD_self (θ : E) :
    bregmanD Ψ gΨ θ θ = 0 := by
  simp [bregmanD]

variable {Ψ 𝒜 gΨ g𝒜 η}
variable {ystar : E → E}

omit [CompleteSpace E] in
theorem gap_nonneg
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z) (θ y : E) :
    0 ≤ gap Ψ 𝒜 gΨ η ystar θ y :=
  sub_nonneg.mpr (hmin θ y)

omit [CompleteSpace E] in
/-- The proximal-minimality inequality: the action increment
plus the scaled divergence is dominated by the gap. -/
theorem action_bregman_le_gap
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z) (θ y : E) :
    𝒜 y - 𝒜 θ + η⁻¹ * bregmanD Ψ gΨ y θ
      ≤ gap Ψ 𝒜 gΨ η ystar θ y := by
  have h1 := hmin θ θ
  have h2 : prox Ψ 𝒜 gΨ η θ θ = 𝒜 θ := by
    rw [prox, bregmanD_self, mul_zero, add_zero]
  rw [h2] at h1
  unfold gap prox
  unfold prox at h1
  linarith

/-- The gradient of the proximal objective. -/
theorem hasGradientAt_prox
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (h𝒜g : ∀ x, HasGradientAt 𝒜 (g𝒜 x) x) (θ y : E) :
    HasGradientAt (prox Ψ 𝒜 gΨ η θ)
      (g𝒜 y + η⁻¹ • (gΨ y - gΨ θ)) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h𝒜 := (h𝒜g y).hasFDerivAt
  have hΨ := (hΨg y).hasFDerivAt
  have hlin : HasFDerivAt (fun z : E => ⟪gΨ θ, z - θ⟫)
      (InnerProductSpace.toDual ℝ E (gΨ θ)) y := by
    have hfun : (fun z : E => ⟪gΨ θ, z - θ⟫)
        = fun z : E =>
          (InnerProductSpace.toDual ℝ E (gΨ θ)) z
            - ⟪gΨ θ, θ⟫ := by
      funext z
      rw [InnerProductSpace.toDual_apply_apply,
        inner_sub_right]
    rw [hfun]
    exact ((InnerProductSpace.toDual ℝ E
      (gΨ θ)).hasFDerivAt).sub_const _
  have hD : HasFDerivAt
      (fun z => bregmanD Ψ gΨ z θ)
      ((InnerProductSpace.toDual ℝ E (gΨ y))
        - InnerProductSpace.toDual ℝ E (gΨ θ)) y := by
    have h1 := (hΨ.sub_const (Ψ θ)).sub hlin
    exact h1
  have hsum := h𝒜.add (hD.const_mul η⁻¹)
  have hclm : (InnerProductSpace.toDual ℝ E (g𝒜 y))
      + η⁻¹ • ((InnerProductSpace.toDual ℝ E (gΨ y))
        - InnerProductSpace.toDual ℝ E (gΨ θ))
      = InnerProductSpace.toDual ℝ E
          (g𝒜 y + η⁻¹ • (gΨ y - gΨ θ)) := by
    ext w
    simp only [add_apply, smul_apply, sub_apply,
      InnerProductSpace.toDual_apply_apply,
      inner_add_left, smul_eq_mul]
    rw [real_inner_smul_left, inner_sub_left]
  rw [← hclm]
  exact hsum

omit [CompleteSpace E] in
/-- Upper monotonicity of the proximal gradient with the boxed
constant `Λ_Φ = (η⁻¹+L)M`. -/
theorem prox_grad_upper (L M : ℝ) (hL : 0 ≤ L)
    (hη : 0 < η)
    (hΨup : ∀ a b : E,
      ⟪gΨ a - gΨ b, a - b⟫ ≤ M * ‖a - b‖ ^ 2)
    (hΨlo0 : ∀ a b : E, 0 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜up : ∀ a b : E, ⟪g𝒜 a - g𝒜 b, a - b⟫
      ≤ L * ⟪gΨ a - gΨ b, a - b⟫) (θ a b : E) :
    ⟪(g𝒜 a + η⁻¹ • (gΨ a - gΨ θ))
        - (g𝒜 b + η⁻¹ • (gΨ b - gΨ θ)), a - b⟫
      ≤ ((η⁻¹ + L) * M) * ‖a - b‖ ^ 2 := by
  have hdiff : (g𝒜 a + η⁻¹ • (gΨ a - gΨ θ))
      - (g𝒜 b + η⁻¹ • (gΨ b - gΨ θ))
      = (g𝒜 a - g𝒜 b) + η⁻¹ • (gΨ a - gΨ b) := by
    rw [smul_sub, smul_sub, smul_sub]
    abel
  rw [hdiff, inner_add_left, real_inner_smul_left]
  have h1 := h𝒜up a b
  have h2 := hΨup a b
  have h3 := hΨlo0 a b
  have hηinv : (0:ℝ) ≤ η⁻¹ := by positivity
  nlinarith

end Record

/-! ### Derived residual bounds -/

section Residual

variable {Ψ 𝒜 : E → ℝ} {gΨ g𝒜 : E → E}
  {η m M L lam : ℝ} {ystar : E → E}

omit [CompleteSpace E] in
/-- The KKT residual is the `η`-scaled proximal gradient. -/
theorem resid_eq_smul_grad (hη : η ≠ 0) (θ y : E) :
    resid gΨ g𝒜 η θ y
      = η • (g𝒜 y + η⁻¹ • (gΨ y - gΨ θ)) := by
  rw [resid, smul_add, smul_smul, mul_inv_cancel₀ hη,
    one_smul]
  abel

/-- **The KKT-residual descent bound**
`‖r_Ψ(θ,y)‖² ≤ 2η²Λ_Φ Δ_Ψ(θ,y)` with `Λ_Φ = (η⁻¹+L)M`. -/
theorem resid_sq_le
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ)
    (h𝒜g : ∀ x, HasGradientAt 𝒜 (g𝒜 x) x)
    (h𝒜gc : Continuous g𝒜)
    (hη : 0 < η) (hM : 0 < M) (hL : 0 ≤ L)
    (hΨup : ∀ a b : E,
      ⟪gΨ a - gΨ b, a - b⟫ ≤ M * ‖a - b‖ ^ 2)
    (hΨlo0 : ∀ a b : E, 0 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜up : ∀ a b : E, ⟪g𝒜 a - g𝒜 b, a - b⟫
      ≤ L * ⟪gΨ a - gΨ b, a - b⟫)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z)
    (θ y : E) :
    ‖resid gΨ g𝒜 η θ y‖ ^ 2
      ≤ 2 * η ^ 2 * ((η⁻¹ + L) * M)
        * gap Ψ 𝒜 gΨ η ystar θ y := by
  have hgrad : ∀ z, HasGradientAt (prox Ψ 𝒜 gΨ η θ)
      (g𝒜 z + η⁻¹ • (gΨ z - gΨ θ)) z :=
    fun z => hasGradientAt_prox hΨg h𝒜g θ z
  have hgc : Continuous
      (fun z => g𝒜 z + η⁻¹ • (gΨ z - gΨ θ)) :=
    h𝒜gc.add ((hΨgc.sub continuous_const).const_smul η⁻¹)
  have hΛ : (0:ℝ) < (η⁻¹ + L) * M := by positivity
  have h := grad_sq_le (prox Ψ 𝒜 gΨ η θ) _ hgrad hgc
    ((η⁻¹ + L) * M) hΛ
    (fun a b => prox_grad_upper L M hL hη hΨup hΨlo0
      h𝒜up θ a b)
    (ystar θ) y (fun w => hmin θ w)
  rw [resid_eq_smul_grad (ne_of_gt hη), norm_smul,
    Real.norm_eq_abs, abs_of_pos hη, mul_pow]
  calc η ^ 2 * ‖g𝒜 y + η⁻¹ • (gΨ y - gΨ θ)‖ ^ 2
      ≤ η ^ 2 * (2 * ((η⁻¹ + L) * M)
          * (prox Ψ 𝒜 gΨ η θ y
            - prox Ψ 𝒜 gΨ η θ (ystar θ))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * η ^ 2 * ((η⁻¹ + L) * M)
        * gap Ψ 𝒜 gΨ η ystar θ y := by
        rw [gap]
        ring

omit [CompleteSpace E] in
/-- **Reconstruction of the action gradient**: squared bound
`‖∇𝒜(θ)‖² ≤ 2η⁻²(‖r‖² + (1+ηℓ)²M²‖y-θ‖²)`, `ℓ = max λ L`. -/
theorem grad_action_sq_le (hη : 0 < η) (_hM : 0 ≤ M)
    (hΨlip : ∀ a b : E, ‖gΨ a - gΨ b‖ ≤ M * ‖a - b‖)
    (h𝒜lip : ∀ a b : E,
      ‖g𝒜 a - g𝒜 b‖ ≤ max lam L * M * ‖a - b‖)
    (_hml : 0 ≤ max lam L) (θ y : E) :
    ‖g𝒜 θ‖ ^ 2 ≤ 2 * η⁻¹ ^ 2
      * (‖resid gΨ g𝒜 η θ y‖ ^ 2
        + (1 + η * max lam L) ^ 2 * M ^ 2
          * ‖y - θ‖ ^ 2) := by
  have hid : η • g𝒜 θ = resid gΨ g𝒜 η θ y
      - (gΨ y - gΨ θ) - η • (g𝒜 y - g𝒜 θ) := by
    rw [resid, smul_sub]
    abel
  have hnorm : η * ‖g𝒜 θ‖
      ≤ ‖resid gΨ g𝒜 η θ y‖
        + (1 + η * max lam L) * M * ‖y - θ‖ := by
    have h1 : η * ‖g𝒜 θ‖ = ‖η • g𝒜 θ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    rw [h1, hid]
    have h2 : ‖resid gΨ g𝒜 η θ y - (gΨ y - gΨ θ)
        - η • (g𝒜 y - g𝒜 θ)‖
        ≤ ‖resid gΨ g𝒜 η θ y‖ + ‖gΨ y - gΨ θ‖
          + ‖η • (g𝒜 y - g𝒜 θ)‖ := by
      calc ‖resid gΨ g𝒜 η θ y - (gΨ y - gΨ θ)
          - η • (g𝒜 y - g𝒜 θ)‖
          ≤ ‖resid gΨ g𝒜 η θ y - (gΨ y - gΨ θ)‖
            + ‖η • (g𝒜 y - g𝒜 θ)‖ := norm_sub_le _ _
        _ ≤ ‖resid gΨ g𝒜 η θ y‖ + ‖gΨ y - gΨ θ‖
            + ‖η • (g𝒜 y - g𝒜 θ)‖ := by
            have := norm_sub_le (resid gΨ g𝒜 η θ y)
              (gΨ y - gΨ θ)
            linarith
    have h3 := hΨlip y θ
    have h4 : ‖η • (g𝒜 y - g𝒜 θ)‖
        ≤ η * (max lam L * M * ‖y - θ‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      exact mul_le_mul_of_nonneg_left (h𝒜lip y θ) hη.le
    calc ‖resid gΨ g𝒜 η θ y - (gΨ y - gΨ θ)
        - η • (g𝒜 y - g𝒜 θ)‖
        ≤ ‖resid gΨ g𝒜 η θ y‖ + ‖gΨ y - gΨ θ‖
          + ‖η • (g𝒜 y - g𝒜 θ)‖ := h2
      _ ≤ ‖resid gΨ g𝒜 η θ y‖
          + (1 + η * max lam L) * M * ‖y - θ‖ := by
          nlinarith [norm_nonneg (y - θ)]
  have hgle : ‖g𝒜 θ‖ ≤ η⁻¹
      * (‖resid gΨ g𝒜 η θ y‖
        + (1 + η * max lam L) * M * ‖y - θ‖) := by
    have h5 : ‖g𝒜 θ‖ = η⁻¹ * (η * ‖g𝒜 θ‖) := by
      field_simp
    rw [h5]
    exact mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hgle 2
  calc ‖g𝒜 θ‖ ^ 2
      ≤ (η⁻¹ * (‖resid gΨ g𝒜 η θ y‖
          + (1 + η * max lam L) * M * ‖y - θ‖)) ^ 2 := hsq
    _ ≤ 2 * η⁻¹ ^ 2 * (‖resid gΨ g𝒜 η θ y‖ ^ 2
        + (1 + η * max lam L) ^ 2 * M ^ 2
          * ‖y - θ‖ ^ 2) := by
        nlinarith [sq_nonneg (‖resid gΨ g𝒜 η θ y‖
          - (1 + η * max lam L) * M * ‖y - θ‖),
          sq_nonneg η⁻¹]

end Residual

/-! ### The kernel-integrated record -/

section Integration

variable [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
variable {Ψ 𝒜 : E → ℝ} {gΨ g𝒜 : E → E}
  {η m M L lam : ℝ} {ystar : E → E}
variable {ν : Measure E} [IsProbabilityMeasure ν]
variable {K : Kernel E E} [IsMarkovKernel K]

omit [InnerProductSpace ℝ E] [CompleteSpace E]
  [BorelSpace E] in
/-- First-marginal integral over the accepted pair law. -/
theorem integral_fst_pair (h : E → ℝ)
    (hint : Integrable (fun p : E × E => h p.1)
      (ν ⊗ₘ K)) :
    ∫ p, h p.1 ∂(ν ⊗ₘ K) = ∫ θ, h θ ∂ν := by
  rw [Measure.integral_compProd hint]
  refine integral_congr_ae (Filter.Eventually.of_forall
    fun θ => ?_)
  simp

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- The second marginal of the pair law is `ν` under
stationarity. -/
theorem snd_pair_eq (hstat : K ∘ₘ ν = ν) :
    Measure.map Prod.snd (ν ⊗ₘ K) = ν := by
  have h0 : Measure.map Prod.snd (ν ⊗ₘ K)
      = (ν ⊗ₘ K).snd := rfl
  rw [h0, Measure.snd_compProd, hstat]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- The first marginal of the pair law is `ν`. -/
theorem fst_pair_eq :
    Measure.map Prod.fst (ν ⊗ₘ K) = ν := by
  have h0 : Measure.map Prod.fst (ν ⊗ₘ K)
      = (ν ⊗ₘ K).fst := rfl
  rw [h0, Measure.fst_compProd]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- Second-marginal integral under stationarity. -/
theorem integral_snd_pair (h : E → ℝ)
    (hstat : K ∘ₘ ν = ν)
    (haesm : AEStronglyMeasurable h ν) :
    ∫ p, h p.2 ∂(ν ⊗ₘ K) = ∫ θ, h θ ∂ν := by
  have hmap := snd_pair_eq (ν := ν) (K := K) hstat
  have h1 := integral_map (φ := Prod.snd)
    (μ := ν ⊗ₘ K) measurable_snd.aemeasurable
    (f := h) (by rw [hmap]; exact haesm)
  rw [hmap] at h1
  exact h1.symm

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- Integrability transport to the first coordinate. -/
theorem integrable_fst_pair (h : E → ℝ)
    (hint : Integrable h ν) :
    Integrable (fun p : E × E => h p.1) (ν ⊗ₘ K) := by
  have hmap := fst_pair_eq (ν := ν) (K := K)
  exact (integrable_map_measure
    (by rw [hmap]; exact hint.aestronglyMeasurable)
    measurable_fst.aemeasurable).mp
    (by rw [hmap]; exact hint)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- Integrability transport to the second coordinate under
stationarity. -/
theorem integrable_snd_pair (h : E → ℝ)
    (hstat : K ∘ₘ ν = ν) (hint : Integrable h ν) :
    Integrable (fun p : E × E => h p.2) (ν ⊗ₘ K) := by
  have hmap := snd_pair_eq (ν := ν) (K := K) hstat
  exact (integrable_map_measure
    (by rw [hmap]; exact hint.aestronglyMeasurable)
    measurable_snd.aemeasurable).mp
    (by rw [hmap]; exact hint)

end Integration

/-! ### The boxed kernel-integrated conclusions -/

variable [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
variable {Ψ 𝒜 : E → ℝ} {gΨ g𝒜 : E → E}
  {η m M L lam : ℝ} {ystar : E → E}
variable {ν : Measure E} [IsProbabilityMeasure ν]
variable {K : Kernel E E} [IsMarkovKernel K]

omit [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- The Bregman divergence is nonnegative under the metric
floor, pointwise. -/
theorem bregmanD_nonneg
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ) (hm : 0 < m)
    (hΨlo : ∀ a b : E,
      m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (θ y : E) : 0 ≤ bregmanD Ψ gΨ y θ := by
  have h := bregman_floor Ψ gΨ hΨg hΨgc m hΨlo θ (y - θ)
  rw [show θ + (y - θ) = y from by abel] at h
  have h2 : (0:ℝ) ≤ m / 2 * ‖y - θ‖ ^ 2 := by positivity
  unfold bregmanD
  linarith

/-- Integrability of the Bregman integrand over the accepted
pair law. -/
theorem integrable_bregmanD
    (hη : 0 < η)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z)
    (hstat : K ∘ₘ ν = ν)
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ) (hm : 0 < m)
    (hΨlo : ∀ a b : E,
      m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hi𝒜 : Integrable 𝒜 ν)
    (higap : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2) (ν ⊗ₘ K)) :
    Integrable (fun p : E × E =>
      bregmanD Ψ gΨ p.2 p.1) (ν ⊗ₘ K) := by
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr
    fun x => (hΨg x).differentiableAt.continuousAt
  have hDc : Continuous (fun p : E × E =>
      bregmanD Ψ gΨ p.2 p.1) := by
    unfold bregmanD
    refine Continuous.sub (Continuous.sub ?_ ?_) ?_
    · exact hΨc.comp continuous_snd
    · exact hΨc.comp continuous_fst
    · exact Continuous.inner (hΨgc.comp continuous_fst)
        (continuous_snd.sub continuous_fst)
  have hfg : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2 + 𝒜 p.1) (ν ⊗ₘ K) :=
    higap.add (integrable_fst_pair (K := K) 𝒜 hi𝒜)
  have hb : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2 + 𝒜 p.1 - 𝒜 p.2)
      (ν ⊗ₘ K) :=
    hfg.sub (integrable_snd_pair 𝒜 hstat hi𝒜)
  have hibound := hb.const_mul η
  refine Integrable.mono' hibound
    hDc.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun p => ?_
  have hpt := action_bregman_le_gap hmin p.1 p.2
  have hnn := bregmanD_nonneg hΨg hΨgc hm hΨlo p.1 p.2
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have h2 : η⁻¹ * bregmanD Ψ gΨ p.2 p.1
      ≤ gap Ψ 𝒜 gΨ η ystar p.1 p.2 + 𝒜 p.1 - 𝒜 p.2 := by
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hη.le
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hη),
    one_mul] at h3
  linarith

/-- **Boxed inequality 1**: stationarity cancels the action
difference and `∫ D_Ψ dνK ≤ η·Δ̄_Ψ`. -/
theorem integral_bregman_le
    (hη : 0 < η)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z)
    (hstat : K ∘ₘ ν = ν)
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ) (hm : 0 < m)
    (hΨlo : ∀ a b : E,
      m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hi𝒜 : Integrable 𝒜 ν)
    (higap : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2) (ν ⊗ₘ K)) :
    ∫ p, bregmanD Ψ gΨ p.2 p.1 ∂(ν ⊗ₘ K)
      ≤ η * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2
          ∂(ν ⊗ₘ K) := by
  have hi𝒜f := integrable_fst_pair (K := K) 𝒜 hi𝒜
  have hi𝒜s := integrable_snd_pair 𝒜 hstat hi𝒜
  have hiD := integrable_bregmanD hη hmin hstat hΨg hΨgc
    hm hΨlo hi𝒜 higap
  have hpt : ∀ p : E × E,
      η⁻¹ * bregmanD Ψ gΨ p.2 p.1
      ≤ gap Ψ 𝒜 gΨ η ystar p.1 p.2 + 𝒜 p.1 - 𝒜 p.2 := by
    intro p
    have := action_bregman_le_gap hmin p.1 p.2
    linarith
  have hfg : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2 + 𝒜 p.1) (ν ⊗ₘ K) :=
    higap.add hi𝒜f
  have hb : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2 + 𝒜 p.1 - 𝒜 p.2)
      (ν ⊗ₘ K) := hfg.sub hi𝒜s
  have hint := integral_mono (hiD.const_mul η⁻¹) hb hpt
  rw [integral_sub hfg hi𝒜s, integral_add higap hi𝒜f,
    integral_fst_pair 𝒜 hi𝒜f,
    integral_snd_pair 𝒜 hstat hi𝒜.aestronglyMeasurable,
    integral_const_mul] at hint
  have h2 : η⁻¹ * ∫ p, bregmanD Ψ gΨ p.2 p.1 ∂(ν ⊗ₘ K)
      ≤ ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂(ν ⊗ₘ K) := by
    linarith
  calc ∫ p, bregmanD Ψ gΨ p.2 p.1 ∂(ν ⊗ₘ K)
      = η * (η⁻¹ * ∫ p, bregmanD Ψ gΨ p.2 p.1
          ∂(ν ⊗ₘ K)) := by
        field_simp
    _ ≤ η * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2
          ∂(ν ⊗ₘ K) :=
        mul_le_mul_of_nonneg_left h2 hη.le

/-- Integrability of the squared displacement. -/
theorem integrable_sq_pair
    (hη : 0 < η)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z)
    (hstat : K ∘ₘ ν = ν)
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ) (hm : 0 < m)
    (hΨlo : ∀ a b : E,
      m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hi𝒜 : Integrable 𝒜 ν)
    (higap : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2) (ν ⊗ₘ K)) :
    Integrable (fun p : E × E => ‖p.2 - p.1‖ ^ 2)
      (ν ⊗ₘ K) := by
  have hiD := integrable_bregmanD hη hmin hstat hΨg hΨgc
    hm hΨlo hi𝒜 higap
  refine Integrable.mono' (hiD.const_mul (2 / m))
    ?_ ?_
  · exact (Continuous.pow ((continuous_snd.sub
      continuous_fst).norm) 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := bregman_floor Ψ gΨ hΨg hΨgc m hΨlo p.1
      (p.2 - p.1)
    rw [show p.1 + (p.2 - p.1) = p.2 from by abel] at h
    have h2 : m / 2 * ‖p.2 - p.1‖ ^ 2
        ≤ bregmanD Ψ gΨ p.2 p.1 := h
    have hm2 : (0:ℝ) < m / 2 := by positivity
    calc ‖p.2 - p.1‖ ^ 2
        = 2 / m * (m / 2 * ‖p.2 - p.1‖ ^ 2) := by
          field_simp
      _ ≤ 2 / m * bregmanD Ψ gΨ p.2 p.1 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Boxed inequality 2**:
`∫ ‖y-θ‖² dνK ≤ (2η/m)·Δ̄_Ψ`. -/
theorem integral_sq_le
    (hη : 0 < η)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z)
    (hstat : K ∘ₘ ν = ν)
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ) (hm : 0 < m)
    (hΨlo : ∀ a b : E,
      m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hi𝒜 : Integrable 𝒜 ν)
    (higap : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2) (ν ⊗ₘ K)) :
    ∫ p, ‖p.2 - p.1‖ ^ 2 ∂(ν ⊗ₘ K)
      ≤ 2 * η / m * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2
          ∂(ν ⊗ₘ K) := by
  have hiD := integrable_bregmanD hη hmin hstat hΨg hΨgc
    hm hΨlo hi𝒜 higap
  have hisq := integrable_sq_pair hη hmin hstat hΨg hΨgc
    hm hΨlo hi𝒜 higap
  have hpt : ∀ p : E × E, ‖p.2 - p.1‖ ^ 2
      ≤ 2 / m * bregmanD Ψ gΨ p.2 p.1 := by
    intro p
    have h := bregman_floor Ψ gΨ hΨg hΨgc m hΨlo p.1
      (p.2 - p.1)
    rw [show p.1 + (p.2 - p.1) = p.2 from by abel] at h
    calc ‖p.2 - p.1‖ ^ 2
        = 2 / m * (m / 2 * ‖p.2 - p.1‖ ^ 2) := by
          field_simp
      _ ≤ 2 / m * bregmanD Ψ gΨ p.2 p.1 :=
          mul_le_mul_of_nonneg_left h (by positivity)
  have hint := integral_mono hisq (hiD.const_mul (2 / m))
    hpt
  rw [integral_const_mul] at hint
  have hD := integral_bregman_le hη hmin hstat hΨg hΨgc
    hm hΨlo hi𝒜 higap
  calc ∫ p, ‖p.2 - p.1‖ ^ 2 ∂(ν ⊗ₘ K)
      ≤ 2 / m * ∫ p, bregmanD Ψ gΨ p.2 p.1
          ∂(ν ⊗ₘ K) := hint
    _ ≤ 2 / m * (η * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2
          ∂(ν ⊗ₘ K)) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = 2 * η / m * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2
          ∂(ν ⊗ₘ K) := by ring

omit [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- Pointwise reconstruction bound for the action gradient
against the gap and the displacement. -/
theorem grad_action_sq_le_gap
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ)
    (h𝒜g : ∀ x, HasGradientAt 𝒜 (g𝒜 x) x)
    (h𝒜gc : Continuous g𝒜)
    (hη : 0 < η) (hM : 0 < M) (hL : 0 ≤ L) (hlam : 0 ≤ lam)
    (hΨup : ∀ a b : E,
      ⟪gΨ a - gΨ b, a - b⟫ ≤ M * ‖a - b‖ ^ 2)
    (hΨlo0 : ∀ a b : E, 0 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hΨlip : ∀ a b : E, ‖gΨ a - gΨ b‖ ≤ M * ‖a - b‖)
    (h𝒜up : ∀ a b : E, ⟪g𝒜 a - g𝒜 b, a - b⟫
      ≤ L * ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜lip : ∀ a b : E,
      ‖g𝒜 a - g𝒜 b‖ ≤ max lam L * M * ‖a - b‖)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z) (p : E × E) :
    ‖g𝒜 p.1‖ ^ 2 ≤ 2 * η⁻¹ ^ 2
      * (2 * η ^ 2 * ((η⁻¹ + L) * M)
          * gap Ψ 𝒜 gΨ η ystar p.1 p.2
        + (1 + η * max lam L) ^ 2 * M ^ 2
          * ‖p.2 - p.1‖ ^ 2) := by
  have h1 := grad_action_sq_le (lam := lam) hη hM.le
    hΨlip h𝒜lip (le_trans hlam (le_max_left lam L))
    p.1 p.2
  have h2 := resid_sq_le hΨg hΨgc h𝒜g h𝒜gc hη hM hL
    hΨup hΨlo0 h𝒜up hmin p.1 p.2
  have h3 : (0:ℝ) ≤ 2 * η⁻¹ ^ 2 := by positivity
  nlinarith [sq_nonneg (1 + η * max lam L),
    sq_nonneg ‖p.2 - p.1‖]

/-- Integrability of the squared action gradient over the
stationary law. -/
theorem integrable_grad_action_sq
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ)
    (h𝒜g : ∀ x, HasGradientAt 𝒜 (g𝒜 x) x)
    (h𝒜gc : Continuous g𝒜)
    (hη : 0 < η) (hm : 0 < m) (hM : 0 < M) (hL : 0 ≤ L)
    (hlam : 0 ≤ lam)
    (hΨlo : ∀ a b : E,
      m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hΨup : ∀ a b : E,
      ⟪gΨ a - gΨ b, a - b⟫ ≤ M * ‖a - b‖ ^ 2)
    (hΨlip : ∀ a b : E, ‖gΨ a - gΨ b‖ ≤ M * ‖a - b‖)
    (h𝒜up : ∀ a b : E, ⟪g𝒜 a - g𝒜 b, a - b⟫
      ≤ L * ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜lip : ∀ a b : E,
      ‖g𝒜 a - g𝒜 b‖ ≤ max lam L * M * ‖a - b‖)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z)
    (hstat : K ∘ₘ ν = ν)
    (hi𝒜 : Integrable 𝒜 ν)
    (higap : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2) (ν ⊗ₘ K)) :
    Integrable (fun p : E × E => ‖g𝒜 p.1‖ ^ 2)
      (ν ⊗ₘ K) := by
  have hΨlo0 : ∀ a b : E,
      0 ≤ ⟪gΨ a - gΨ b, a - b⟫ := fun a b =>
    le_trans (by positivity) (hΨlo a b)
  have hisq := integrable_sq_pair hη hmin hstat hΨg hΨgc
    hm hΨlo hi𝒜 higap
  have h1 : Integrable (fun p : E × E =>
      2 * η ^ 2 * ((η⁻¹ + L) * M)
        * gap Ψ 𝒜 gΨ η ystar p.1 p.2) (ν ⊗ₘ K) :=
    higap.const_mul _
  have h2 : Integrable (fun p : E × E =>
      (1 + η * max lam L) ^ 2 * M ^ 2
        * ‖p.2 - p.1‖ ^ 2) (ν ⊗ₘ K) :=
    hisq.const_mul _
  have hsum : Integrable (fun p : E × E =>
      2 * η ^ 2 * ((η⁻¹ + L) * M)
        * gap Ψ 𝒜 gΨ η ystar p.1 p.2
      + (1 + η * max lam L) ^ 2 * M ^ 2
        * ‖p.2 - p.1‖ ^ 2) (ν ⊗ₘ K) := h1.add h2
  refine Integrable.mono' (hsum.const_mul (2 * η⁻¹ ^ 2))
    ?_ ?_
  · exact (((h𝒜gc.comp continuous_fst).norm).pow
      2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact grad_action_sq_le_gap hΨg hΨgc h𝒜g h𝒜gc hη hM
      hL hlam hΨup hΨlo0 hΨlip h𝒜up h𝒜lip hmin p

/-- **Boxed inequality 3**: any stationarity form dominated
by the inverse-Fisher envelope integrates against the boxed
constant `C_{Ψ,𝒜,η} = 4Λ_Φ/m + 4M²(1+ηℓ)²/(m²η)`. -/
theorem integral_stationarity_form_le
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ)
    (h𝒜g : ∀ x, HasGradientAt 𝒜 (g𝒜 x) x)
    (h𝒜gc : Continuous g𝒜)
    (hη : 0 < η) (hm : 0 < m) (hM : 0 < M) (hL : 0 ≤ L)
    (hlam : 0 ≤ lam)
    (hΨlo : ∀ a b : E,
      m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hΨup : ∀ a b : E,
      ⟪gΨ a - gΨ b, a - b⟫ ≤ M * ‖a - b‖ ^ 2)
    (hΨlip : ∀ a b : E, ‖gΨ a - gΨ b‖ ≤ M * ‖a - b‖)
    (h𝒜up : ∀ a b : E, ⟪g𝒜 a - g𝒜 b, a - b⟫
      ≤ L * ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜lip : ∀ a b : E,
      ‖g𝒜 a - g𝒜 b‖ ≤ max lam L * M * ‖a - b‖)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z)
    (hstat : K ∘ₘ ν = ν)
    (hi𝒜 : Integrable 𝒜 ν)
    (higap : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2) (ν ⊗ₘ K))
    (S : E → ℝ) (hS0 : ∀ θ, 0 ≤ S θ)
    (hSle : ∀ θ, S θ ≤ m⁻¹ * ‖g𝒜 θ‖ ^ 2)
    (hSm : AEStronglyMeasurable S ν) :
    ∫ θ, S θ ∂ν
      ≤ (4 * ((η⁻¹ + L) * M) / m
          + 4 * M ^ 2 * (1 + η * max lam L) ^ 2
            / (m ^ 2 * η))
        * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2
            ∂(ν ⊗ₘ K) := by
  have hΨlo0 : ∀ a b : E,
      0 ≤ ⟪gΨ a - gΨ b, a - b⟫ := fun a b =>
    le_trans (by positivity) (hΨlo a b)
  have hig𝒜π := integrable_grad_action_sq hΨg hΨgc h𝒜g
    h𝒜gc hη hm hM hL hlam hΨlo hΨup hΨlip h𝒜up h𝒜lip
    hmin hstat hi𝒜 higap
  have hig𝒜ν : Integrable (fun θ => ‖g𝒜 θ‖ ^ 2) ν := by
    have h := (integrable_map_measure
      (by rw [fst_pair_eq (ν := ν) (K := K)]
          exact (((h𝒜gc.norm).pow
            2).aestronglyMeasurable)
        : AEStronglyMeasurable (fun θ => ‖g𝒜 θ‖ ^ 2)
            (Measure.map Prod.fst (ν ⊗ₘ K)))
      measurable_fst.aemeasurable).mpr hig𝒜π
    rwa [fst_pair_eq (ν := ν) (K := K)] at h
  have hiS : Integrable S ν := by
    refine Integrable.mono' (hig𝒜ν.const_mul m⁻¹)
      hSm ?_
    refine Filter.Eventually.of_forall fun θ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hS0 θ)]
    exact hSle θ
  have hstep1 := integral_mono hiS
    (hig𝒜ν.const_mul m⁻¹) hSle
  rw [integral_const_mul] at hstep1
  have hstep2 : ∫ θ, ‖g𝒜 θ‖ ^ 2 ∂ν
      = ∫ p, ‖g𝒜 p.1‖ ^ 2 ∂(ν ⊗ₘ K) :=
    (integral_fst_pair _ hig𝒜π).symm
  have h1 : Integrable (fun p : E × E =>
      2 * η ^ 2 * ((η⁻¹ + L) * M)
        * gap Ψ 𝒜 gΨ η ystar p.1 p.2) (ν ⊗ₘ K) :=
    higap.const_mul _
  have hisq := integrable_sq_pair hη hmin hstat hΨg hΨgc
    hm hΨlo hi𝒜 higap
  have h2 : Integrable (fun p : E × E =>
      (1 + η * max lam L) ^ 2 * M ^ 2
        * ‖p.2 - p.1‖ ^ 2) (ν ⊗ₘ K) :=
    hisq.const_mul _
  have hsum : Integrable (fun p : E × E =>
      2 * η ^ 2 * ((η⁻¹ + L) * M)
        * gap Ψ 𝒜 gΨ η ystar p.1 p.2
      + (1 + η * max lam L) ^ 2 * M ^ 2
        * ‖p.2 - p.1‖ ^ 2) (ν ⊗ₘ K) := h1.add h2
  have hstep3 := integral_mono hig𝒜π
    (hsum.const_mul (2 * η⁻¹ ^ 2))
    (fun p => grad_action_sq_le_gap hΨg hΨgc h𝒜g h𝒜gc
      hη hM hL hlam hΨup hΨlo0 hΨlip h𝒜up h𝒜lip hmin p)
  rw [integral_const_mul, integral_add h1 h2,
    integral_const_mul, integral_const_mul] at hstep3
  have hstep4 := integral_sq_le hη hmin hstat hΨg hΨgc
    hm hΨlo hi𝒜 higap
  have hgapnn : (0:ℝ) ≤ ∫ p,
      gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂(ν ⊗ₘ K) :=
    integral_nonneg fun p => gap_nonneg hmin p.1 p.2
  have hchain : ∫ θ, S θ ∂ν
      ≤ m⁻¹ * (2 * η⁻¹ ^ 2
        * (2 * η ^ 2 * ((η⁻¹ + L) * M)
            * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂(ν ⊗ₘ K)
          + (1 + η * max lam L) ^ 2 * M ^ 2
            * (2 * η / m * ∫ p,
                gap Ψ 𝒜 gΨ η ystar p.1 p.2
                  ∂(ν ⊗ₘ K)))) := by
    have hmono := mul_le_mul_of_nonneg_left hstep4
      (by positivity :
        (0:ℝ) ≤ (1 + η * max lam L) ^ 2 * M ^ 2)
    have hins : ∫ p, ‖g𝒜 p.1‖ ^ 2 ∂(ν ⊗ₘ K)
        ≤ 2 * η⁻¹ ^ 2
          * (2 * η ^ 2 * ((η⁻¹ + L) * M)
              * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2
                  ∂(ν ⊗ₘ K)
            + (1 + η * max lam L) ^ 2 * M ^ 2
              * (2 * η / m * ∫ p,
                  gap Ψ 𝒜 gΨ η ystar p.1 p.2
                    ∂(ν ⊗ₘ K))) := by
      have h5 : (0:ℝ) ≤ 2 * η⁻¹ ^ 2 := by positivity
      nlinarith [hstep3, hmono]
    calc ∫ θ, S θ ∂ν
        ≤ m⁻¹ * ∫ θ, ‖g𝒜 θ‖ ^ 2 ∂ν := hstep1
      _ = m⁻¹ * ∫ p, ‖g𝒜 p.1‖ ^ 2 ∂(ν ⊗ₘ K) := by
          rw [hstep2]
      _ ≤ _ := mul_le_mul_of_nonneg_left hins
          (by positivity)
  have hconst : ∀ Δ : ℝ,
      m⁻¹ * (2 * η⁻¹ ^ 2
        * (2 * η ^ 2 * ((η⁻¹ + L) * M) * Δ
          + (1 + η * max lam L) ^ 2 * M ^ 2
            * (2 * η / m * Δ)))
      = (4 * ((η⁻¹ + L) * M) / m
          + 4 * M ^ 2 * (1 + η * max lam L) ^ 2
            / (m ^ 2 * η)) * Δ := by
    intro Δ
    field_simp
    ring
  rw [hconst] at hchain
  exact hchain

/-- **The vanishing clause**: `Δ̄_Ψ = 0` forces the complete
represented common-action first variation to vanish
`ν`-almost surely. -/
theorem vanishing_gap_forces_stationarity
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ)
    (h𝒜g : ∀ x, HasGradientAt 𝒜 (g𝒜 x) x)
    (h𝒜gc : Continuous g𝒜)
    (hη : 0 < η) (hm : 0 < m) (hM : 0 < M) (hL : 0 ≤ L)
    (hlam : 0 ≤ lam)
    (hΨlo : ∀ a b : E,
      m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hΨup : ∀ a b : E,
      ⟪gΨ a - gΨ b, a - b⟫ ≤ M * ‖a - b‖ ^ 2)
    (hΨlip : ∀ a b : E, ‖gΨ a - gΨ b‖ ≤ M * ‖a - b‖)
    (h𝒜up : ∀ a b : E, ⟪g𝒜 a - g𝒜 b, a - b⟫
      ≤ L * ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜lip : ∀ a b : E,
      ‖g𝒜 a - g𝒜 b‖ ≤ max lam L * M * ‖a - b‖)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z)
    (hstat : K ∘ₘ ν = ν)
    (hi𝒜 : Integrable 𝒜 ν)
    (higap : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2) (ν ⊗ₘ K))
    (hzero : ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2
      ∂(ν ⊗ₘ K) = 0) :
    ∀ᵐ θ ∂ν, g𝒜 θ = 0 := by
  have hT3 := integral_stationarity_form_le hΨg hΨgc h𝒜g
    h𝒜gc hη hm hM hL hlam hΨlo hΨup hΨlip h𝒜up h𝒜lip
    hmin hstat hi𝒜 higap
    (fun θ => m⁻¹ * ‖g𝒜 θ‖ ^ 2)
    (fun θ => by positivity) (fun θ => le_refl _)
    ((continuous_const.mul
      ((h𝒜gc.norm).pow 2)).aestronglyMeasurable)
  rw [hzero, mul_zero] at hT3
  have hig𝒜π := integrable_grad_action_sq hΨg hΨgc h𝒜g
    h𝒜gc hη hm hM hL hlam hΨlo hΨup hΨlip h𝒜up h𝒜lip
    hmin hstat hi𝒜 higap
  have hig𝒜ν : Integrable (fun θ => ‖g𝒜 θ‖ ^ 2) ν := by
    have h := (integrable_map_measure
      (by rw [fst_pair_eq (ν := ν) (K := K)]
          exact (((h𝒜gc.norm).pow
            2).aestronglyMeasurable)
        : AEStronglyMeasurable (fun θ => ‖g𝒜 θ‖ ^ 2)
            (Measure.map Prod.fst (ν ⊗ₘ K)))
      measurable_fst.aemeasurable).mpr hig𝒜π
    rwa [fst_pair_eq (ν := ν) (K := K)] at h
  have h0 : ∫ θ, m⁻¹ * ‖g𝒜 θ‖ ^ 2 ∂ν = 0 := by
    refine le_antisymm hT3 ?_
    exact integral_nonneg fun θ => by positivity
  rw [integral_eq_zero_iff_of_nonneg
    (fun θ => by positivity) (hig𝒜ν.const_mul m⁻¹)] at h0
  filter_upwards [h0] with θ hθ
  have hθ' : m⁻¹ * ‖g𝒜 θ‖ ^ 2 = 0 := hθ
  have h2 : ‖g𝒜 θ‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hθ' with h | h
    · exact absurd h (by positivity)
    · exact h
  have h3 : ‖g𝒜 θ‖ = 0 :=
    pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h2
  exact norm_eq_zero.mp h3

end BregmanStationarity
end NCG
