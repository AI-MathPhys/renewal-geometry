/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Initial-energy curvature propagation certificate
  (`thm:main-curvature-propagation`, `eq:main-curvature-energy`,
  `eq:main-curvature-propagation-writer`, `eq:main-curvature-growth`,
  `eq:main-curvature-energy-propagation`, `eq:main-derived-l2-curvature`;
  emergent-spacetime manuscript)

On a finite-dimensional real inner-product space `V` (the retained
electric/magnetic curvature coefficients `y_X = (E_X, B_X)`), with a
time-dependent symmetric positive Gram `M(t)` (`gramEnergy M y t = z_X(t) =
√⟪y, M y⟫`, `eq:main-curvature-energy`), the propagation writer
`eq:main-curvature-propagation-writer` `ẏ = (K + L) y + f` with `M`-skew
principal block `K` (`⟪M x, K x⟫ = 0`) and a growth function `a ≥ 0` with
`⟪x, (Ṁ + M L + Lᵀ M) x⟫ ≤ 2 a ⟪x, M x⟫` (`eq:main-curvature-growth`: the
manuscript's `a_X = ½ max{0, λ_max[M^{-1/2}(Ṁ + ML + LᵀM)M^{-1/2}]}` is the
least such function) gives:

* the energy differential inequality `½ (z²)' ≤ a z² + z ‖f‖_M`
  (`gramEnergySq_deriv_le`, `eq:supp-curvature-energy-differential`), using
  the exact skew cancellation and the Cauchy–Schwarz inequality of the
  positive form (`gram_inner_le`);
* the boxed propagation bound `eq:main-curvature-energy-propagation`
  `z(t) ≤ e^{∫₀ᵗ a} [z(0) + ∫₀ᵗ e^{-∫₀ˢ a} ‖f(s)‖_{M(s)} ds]`
  (`curvature_energy_propagation`), by the integrating-factor argument on the
  regularisation `√(z² + ε²)` and `ε ↓ 0`;
* the uniform bound `z(t) ≤ e^{A_*}(Z_* + F_*)` on `[0, T_*]` under the
  budgets `eq:main-curvature-budgets` (`curvature_energy_uniform_bound`);
* the derived `L²` curvature bound `eq:main-derived-l2-curvature`
  `‖R_X‖_{L²(K)} ≤ C_I √(N_* T_*) e^{A_*}(Z_* + F_*) + C_ζ`
  (`derived_l2_curvature_bound`).

Scoped hypotheses disclosed: the writer is stated for all real times (the
manuscript's cylinder `[0, T_*]`; only `[0, t]` is used), `y` and `M` are
differentiable, `f` and `a` continuous.  For the `L²` box the slice structure
of `L²(K)` is abstracted: the interpolated field has slice norms
`ρ(t) = ‖𝓘_X y_X(t)‖_{L²(Σ_t)} ≤ C_I z(t)`, the lapse satisfies
`0 ≤ N ≤ N_*`, and the `L²(K)` norm of `R_X = 𝓘_X y_X + ζ_X` is bounded by
`√(∫₀^{T_*} N ρ²) + C_ζ` (the foliated slice decomposition of `L²(K)`, the
triangle inequality, and `‖ζ_X‖_{L²(K)} ≤ C_ζ`).
-/

open scoped InnerProductSpace
open MeasureTheory intervalIntegral

namespace RenewalGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Gram energy `z = √⟪y, M y⟫` (`eq:main-curvature-energy`; also the source
norm `‖f‖_M`). -/
noncomputable def gramEnergy (M : ℝ → V →L[ℝ] V) (y : ℝ → V) (t : ℝ) : ℝ :=
  Real.sqrt ⟪y t, M t (y t)⟫_ℝ

/-- Cauchy–Schwarz for a symmetric positive semidefinite form:
`⟪M x, z⟫ ≤ √⟪x, M x⟫ √⟪z, M z⟫`. -/
theorem gram_inner_le (M : V →L[ℝ] V) (hsymm : ∀ x z, ⟪M x, z⟫_ℝ = ⟪x, M z⟫_ℝ)
    (hpos : ∀ x, 0 ≤ ⟪x, M x⟫_ℝ) (x z : V) :
    ⟪M x, z⟫_ℝ ≤ Real.sqrt ⟪x, M x⟫_ℝ * Real.sqrt ⟪z, M z⟫_ℝ := by
  have hzx : ⟪z, M x⟫_ℝ = ⟪x, M z⟫_ℝ := by rw [real_inner_comm (M x) z, hsymm x z]
  have hquad : ∀ l : ℝ, 0 ≤ ⟪z, M z⟫_ℝ * (l * l) + (2 * ⟪M x, z⟫_ℝ) * l + ⟪x, M x⟫_ℝ := by
    intro l
    have h := hpos (l • z + x)
    have hexp : ⟪l • z + x, M (l • z + x)⟫_ℝ =
        ⟪z, M z⟫_ℝ * (l * l) + (2 * ⟪M x, z⟫_ℝ) * l + ⟪x, M x⟫_ℝ := by
      rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
        real_inner_smul_right, hzx, hsymm x z]
      ring
    rw [hexp] at h
    exact h
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have hB2 : ⟪M x, z⟫_ℝ ^ 2 ≤ ⟪x, M x⟫_ℝ * ⟪z, M z⟫_ℝ := by nlinarith
  have hQx := hpos x
  calc ⟪M x, z⟫_ℝ ≤ |⟪M x, z⟫_ℝ| := le_abs_self _
    _ = Real.sqrt (⟪M x, z⟫_ℝ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (⟪x, M x⟫_ℝ * ⟪z, M z⟫_ℝ) := Real.sqrt_le_sqrt hB2
    _ = Real.sqrt ⟪x, M x⟫_ℝ * Real.sqrt ⟪z, M z⟫_ℝ := Real.sqrt_mul hQx _

/-- The energy `q = ⟪y, M y⟫` is differentiable with derivative
`⟪y, Ṁ y⟫ + 2 ⟪M y, ẏ⟫`. -/
theorem hasDerivAt_gramEnergySq {M M' : ℝ → V →L[ℝ] V} {y y' : ℝ → V} {t : ℝ}
    (hM : HasDerivAt M (M' t) t) (hy : HasDerivAt y (y' t) t)
    (hsymm : ∀ x z, ⟪M t x, z⟫_ℝ = ⟪x, M t z⟫_ℝ) :
    HasDerivAt (fun s => ⟪y s, M s (y s)⟫_ℝ)
      (⟪y t, M' t (y t)⟫_ℝ + 2 * ⟪M t (y t), y' t⟫_ℝ) t := by
  have h := hy.inner ℝ (hM.clm_apply hy)
  refine h.congr_deriv ?_
  rw [inner_add_right, hsymm, real_inner_comm (M t (y' t)) (y t), hsymm]
  ring

/-- `eq:supp-curvature-energy-differential`: `½ (z²)' ≤ a z² + z ‖f‖_M`,
i.e. `(z²)' ≤ 2 a z² + 2 z ‖f‖_M`. -/
theorem gramEnergySq_deriv_le {M M' K L : ℝ → V →L[ℝ] V} {y y' f : ℝ → V} {a : ℝ → ℝ}
    {t : ℝ}
    (hsymm : ∀ x z, ⟪M t x, z⟫_ℝ = ⟪x, M t z⟫_ℝ) (hpos : ∀ x, 0 ≤ ⟪x, M t x⟫_ℝ)
    (hwriter : y' t = (K t + L t) (y t) + f t)
    (hskew : ∀ x, ⟪M t x, K t x⟫_ℝ = 0)
    (hgrowth : ∀ x, ⟪x, M' t x⟫_ℝ + 2 * ⟪M t x, L t x⟫_ℝ ≤ 2 * a t * ⟪x, M t x⟫_ℝ) :
    ⟪y t, M' t (y t)⟫_ℝ + 2 * ⟪M t (y t), y' t⟫_ℝ ≤
      2 * a t * ⟪y t, M t (y t)⟫_ℝ +
        2 * Real.sqrt ⟪y t, M t (y t)⟫_ℝ * Real.sqrt ⟪f t, M t (f t)⟫_ℝ := by
  rw [hwriter, ContinuousLinearMap.add_apply, inner_add_right, inner_add_right, hskew]
  have hcs := gram_inner_le (M t) hsymm hpos (y t) (f t)
  have hg := hgrowth (y t)
  linarith

/-- The regularised energy `√(q + ε²)` satisfies `z_ε' ≤ a z_ε + ‖f‖_M`. -/
theorem regularised_energy_deriv_le {q q' a F ε : ℝ} (hq0 : 0 ≤ q) (hε : 0 < ε)
    (ha : 0 ≤ a) (hF : 0 ≤ F)
    (hq' : q' ≤ 2 * a * q + 2 * Real.sqrt q * F) :
    q' / (2 * Real.sqrt (q + ε ^ 2)) ≤ a * Real.sqrt (q + ε ^ 2) + F := by
  have hz : 0 < Real.sqrt (q + ε ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hzsq : Real.sqrt (q + ε ^ 2) ^ 2 = q + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hsq : Real.sqrt q ≤ Real.sqrt (q + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have hsq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  rw [div_le_iff₀ (by positivity)]
  have h1 : q ≤ Real.sqrt (q + ε ^ 2) ^ 2 := by rw [hzsq]; nlinarith
  have h2 : 2 * a * q ≤ 2 * a * Real.sqrt (q + ε ^ 2) ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 2 * Real.sqrt q * F ≤ 2 * Real.sqrt (q + ε ^ 2) * F :=
    mul_le_mul_of_nonneg_right (by linarith) hF
  nlinarith

/-- `thm:main-curvature-propagation`, first box
(`eq:main-curvature-energy-propagation`): for the writer
`ẏ = (K + L) y + f` with `M`-skew `K` and growth function `a ≥ 0`,
`z(t) ≤ e^{∫₀ᵗ a} [z(0) + ∫₀ᵗ e^{-∫₀ˢ a} ‖f(s)‖_{M(s)} ds]` for `t ≥ 0`. -/
theorem curvature_energy_propagation (M M' K L : ℝ → V →L[ℝ] V) (y y' f : ℝ → V)
    (a : ℝ → ℝ)
    (hM : ∀ t, HasDerivAt M (M' t) t) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hf : Continuous f) (ha : Continuous a) (ha0 : ∀ t, 0 ≤ a t)
    (hsymm : ∀ t x z, ⟪M t x, z⟫_ℝ = ⟪x, M t z⟫_ℝ) (hpos : ∀ t x, 0 ≤ ⟪x, M t x⟫_ℝ)
    (hwriter : ∀ t, y' t = (K t + L t) (y t) + f t)
    (hskew : ∀ t x, ⟪M t x, K t x⟫_ℝ = 0)
    (hgrowth : ∀ t x, ⟪x, M' t x⟫_ℝ + 2 * ⟪M t x, L t x⟫_ℝ ≤ 2 * a t * ⟪x, M t x⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    gramEnergy M y t ≤ Real.exp (∫ s in (0:ℝ)..t, a s) *
      (gramEnergy M y 0 + ∫ s in (0:ℝ)..t,
        Real.exp (-∫ u in (0:ℝ)..s, a u) * gramEnergy M f s) := by
  -- notation
  set q : ℝ → ℝ := fun s => ⟪y s, M s (y s)⟫_ℝ with hq
  set q' : ℝ → ℝ := fun s => ⟪y s, M' s (y s)⟫_ℝ + 2 * ⟪M s (y s), y' s⟫_ℝ with hq'
  set F : ℝ → ℝ := fun s => Real.sqrt ⟪f s, M s (f s)⟫_ℝ with hF
  set A : ℝ → ℝ := fun s => ∫ u in (0:ℝ)..s, a u with hA
  set Φ : ℝ → ℝ := fun s => ∫ u in (0:ℝ)..s, Real.exp (-A u) * F u with hΦ
  have hq0 : ∀ s, 0 ≤ q s := fun s => hpos s (y s)
  have hF0 : ∀ s, 0 ≤ F s := fun s => Real.sqrt_nonneg _
  have hqderiv : ∀ s, HasDerivAt q (q' s) s := fun s =>
    hasDerivAt_gramEnergySq (hM s) (hy s) (hsymm s)
  have hqbound : ∀ s, q' s ≤ 2 * a s * q s + 2 * Real.sqrt (q s) * F s := fun s =>
    gramEnergySq_deriv_le (hsymm s) (hpos s) (hwriter s) (hskew s) (hgrowth s)
  -- continuity of `M`, `F`, `A`
  have hMc : Continuous M := continuous_iff_continuousAt.mpr fun s => (hM s).continuousAt
  have hFc : Continuous F := Real.continuous_sqrt.comp (hf.inner (hMc.clm_apply hf))
  have hAderiv : ∀ s, HasDerivAt A (a s) s := fun s =>
    (ha.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun s => (hAderiv s).continuousAt
  have hΦderiv : ∀ s, HasDerivAt Φ (Real.exp (-A s) * F s) s := fun s =>
    (((hAc.neg.rexp).mul hFc).integral_hasStrictDerivAt 0 s).hasDerivAt
  have hA0 : A 0 = 0 := by simp [hA]
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  -- the regularised integrating-factor argument
  have hmain : ∀ ε : ℝ, 0 < ε →
      Real.sqrt (q t + ε ^ 2) ≤ Real.exp (A t) * (Real.sqrt (q 0 + ε ^ 2) + Φ t) := by
    intro ε hε
    set zε : ℝ → ℝ := fun s => Real.sqrt (q s + ε ^ 2) with hzε
    have hzεderiv : ∀ s, HasDerivAt zε (q' s / (2 * Real.sqrt (q s + ε ^ 2))) s := by
      intro s
      have hne : q s + ε ^ 2 ≠ 0 := by have := hq0 s; positivity
      exact ((hqderiv s).add_const (ε ^ 2)).sqrt hne
    have hzεbound : ∀ s, q' s / (2 * Real.sqrt (q s + ε ^ 2)) ≤ a s * zε s + F s := fun s =>
      regularised_energy_deriv_le (hq0 s) hε (ha0 s) (hF0 s) (hqbound s)
    set ψ : ℝ → ℝ := fun s => Real.exp (-A s) * zε s - Φ s with hψ
    have hψderiv : ∀ s, HasDerivAt ψ
        (Real.exp (-A s) * (-a s) * zε s + Real.exp (-A s) *
          (q' s / (2 * Real.sqrt (q s + ε ^ 2))) - Real.exp (-A s) * F s) s := by
      intro s
      have h1 := ((hAderiv s).neg.exp.mul (hzεderiv s)).sub (hΦderiv s)
      refine h1.congr_deriv ?_
      simp only [Pi.neg_apply]
    have hψnonpos : ∀ s, Real.exp (-A s) * (-a s) * zε s + Real.exp (-A s) *
        (q' s / (2 * Real.sqrt (q s + ε ^ 2))) - Real.exp (-A s) * F s ≤ 0 := by
      intro s
      have hb := hzεbound s
      have he : 0 < Real.exp (-A s) := Real.exp_pos _
      have := mul_le_mul_of_nonneg_left hb he.le
      nlinarith
    have hanti : AntitoneOn ψ (Set.Icc 0 t) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) ?_ ?_ ?_
      · exact fun s _ => (hψderiv s).continuousAt.continuousWithinAt
      · exact fun s _ => (hψderiv s).differentiableAt.differentiableWithinAt
      · intro s _
        rw [(hψderiv s).deriv]
        exact hψnonpos s
    have hψt : ψ t ≤ ψ 0 := hanti ⟨le_refl 0, ht⟩ ⟨ht, le_refl t⟩ ht
    simp only [hψ, hzε, hA0, hΦ0, neg_zero, Real.exp_zero, one_mul, sub_zero] at hψt
    have he : 0 < Real.exp (A t) := Real.exp_pos _
    have hexp : Real.exp (-A t) * Real.exp (A t) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.sqrt (q t + ε ^ 2)
        = Real.exp (A t) * (Real.exp (-A t) * Real.sqrt (q t + ε ^ 2)) := by
          rw [← mul_assoc, mul_comm (Real.exp (A t)), hexp, one_mul]
      _ ≤ Real.exp (A t) * (Real.sqrt (q 0 + ε ^ 2) + Φ t) := by
          gcongr
          linarith
  -- pass to `ε ↓ 0`
  have hzt : gramEnergy M y t = Real.sqrt (q t) := rfl
  have hz0 : gramEnergy M y 0 = Real.sqrt (q 0) := rfl
  rw [hzt, hz0]
  change Real.sqrt (q t) ≤ Real.exp (A t) * (Real.sqrt (q 0) + Φ t)
  have he : 0 < Real.exp (A t) := Real.exp_pos _
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := δ / Real.exp (A t) with hεdef
  have hε : 0 < ε := by positivity
  have h1 : Real.sqrt (q t) ≤ Real.sqrt (q t + ε ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h2 : Real.sqrt (q 0 + ε ^ 2) ≤ Real.sqrt (q 0) + ε := by
    rw [show Real.sqrt (q 0) + ε = Real.sqrt ((Real.sqrt (q 0) + ε) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have := Real.sq_sqrt (hq0 0)
    nlinarith [Real.sqrt_nonneg (q 0)]
  have h3 := hmain ε hε
  have h4 : Real.exp (A t) * ε = δ := by
    rw [hεdef, mul_div_cancel₀ _ he.ne']
  calc Real.sqrt (q t) ≤ Real.sqrt (q t + ε ^ 2) := h1
    _ ≤ Real.exp (A t) * (Real.sqrt (q 0 + ε ^ 2) + Φ t) := h3
    _ ≤ Real.exp (A t) * (Real.sqrt (q 0) + ε + Φ t) := by gcongr
    _ = Real.exp (A t) * (Real.sqrt (q 0) + Φ t) + δ := by rw [← h4]; ring

/-- Uniform bound under the budgets `eq:main-curvature-budgets`:
if `z(0) ≤ Z_*`, `∫₀^{T_*} a ≤ A_*` and `∫₀^{T_*} ‖f‖_M ≤ F_*`, then
`z(t) ≤ e^{A_*}(Z_* + F_*)` for all `t ∈ [0, T_*]`. -/
theorem curvature_energy_uniform_bound (M M' K L : ℝ → V →L[ℝ] V) (y y' f : ℝ → V)
    (a : ℝ → ℝ)
    (hM : ∀ t, HasDerivAt M (M' t) t) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hf : Continuous f) (ha : Continuous a) (ha0 : ∀ t, 0 ≤ a t)
    (hsymm : ∀ t x z, ⟪M t x, z⟫_ℝ = ⟪x, M t z⟫_ℝ) (hpos : ∀ t x, 0 ≤ ⟪x, M t x⟫_ℝ)
    (hwriter : ∀ t, y' t = (K t + L t) (y t) + f t)
    (hskew : ∀ t x, ⟪M t x, K t x⟫_ℝ = 0)
    (hgrowth : ∀ t x, ⟪x, M' t x⟫_ℝ + 2 * ⟪M t x, L t x⟫_ℝ ≤ 2 * a t * ⟪x, M t x⟫_ℝ)
    {T Z A F : ℝ} (hT : 0 ≤ T)
    (hZ : gramEnergy M y 0 ≤ Z) (hA : ∫ s in (0:ℝ)..T, a s ≤ A)
    (hF : ∫ s in (0:ℝ)..T, gramEnergy M f s ≤ F) :
    ∀ t ∈ Set.Icc 0 T, gramEnergy M y t ≤ Real.exp A * (Z + F) := by
  intro t ht
  have hprop := curvature_energy_propagation M M' K L y y' f a hM hy hf ha ha0 hsymm hpos
    hwriter hskew hgrowth ht.1
  have hMc : Continuous M := continuous_iff_continuousAt.mpr fun s => (hM s).continuousAt
  have hFc : Continuous (gramEnergy M f) :=
    Real.continuous_sqrt.comp (hf.inner (hMc.clm_apply hf))
  have hF0 : ∀ s, 0 ≤ gramEnergy M f s := fun s => Real.sqrt_nonneg _
  -- `∫₀ᵗ a ≤ ∫₀ᵀ a ≤ A`
  have hAt : ∫ s in (0:ℝ)..t, a s ≤ A := by
    refine le_trans ?_ hA
    exact intervalIntegral.integral_mono_interval (le_refl 0) ht.1 ht.2
      (Filter.Eventually.of_forall ha0) (ha.intervalIntegrable _ _)
  -- the weighted source integral is at most `∫₀ᵀ ‖f‖_M ≤ F`
  have hexp_le : ∀ s ∈ Set.uIcc 0 t, Real.exp (-∫ u in (0:ℝ)..s, a u) * gramEnergy M f s ≤
      gramEnergy M f s := by
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    have hA0 : 0 ≤ ∫ u in (0:ℝ)..s, a u :=
      intervalIntegral.integral_nonneg hs.1 fun u _ => ha0 u
    have : Real.exp (-∫ u in (0:ℝ)..s, a u) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    exact mul_le_of_le_one_left (hF0 s) this
  have hAc : Continuous fun s => ∫ u in (0:ℝ)..s, a u :=
    continuous_iff_continuousAt.mpr fun s =>
      (ha.integral_hasStrictDerivAt 0 s).hasDerivAt.continuousAt
  have hint1 : IntervalIntegrable
      (fun s => Real.exp (-∫ u in (0:ℝ)..s, a u) * gramEnergy M f s) volume 0 t :=
    ((hAc.neg.rexp).mul hFc).intervalIntegrable _ _
  have hFt : ∫ s in (0:ℝ)..t, Real.exp (-∫ u in (0:ℝ)..s, a u) * gramEnergy M f s ≤ F := by
    calc ∫ s in (0:ℝ)..t, Real.exp (-∫ u in (0:ℝ)..s, a u) * gramEnergy M f s
        ≤ ∫ s in (0:ℝ)..t, gramEnergy M f s :=
          intervalIntegral.integral_mono_on ht.1 hint1 (hFc.intervalIntegrable _ _)
            (fun s hs => hexp_le s (by rw [Set.uIcc_of_le ht.1]; exact hs))
      _ ≤ ∫ s in (0:ℝ)..T, gramEnergy M f s :=
          intervalIntegral.integral_mono_interval (le_refl 0) ht.1 ht.2
            (Filter.Eventually.of_forall hF0) (hFc.intervalIntegrable _ _)
      _ ≤ F := hF
  have hZ0 : 0 ≤ gramEnergy M y 0 := Real.sqrt_nonneg _
  have hΦ0 : 0 ≤ ∫ s in (0:ℝ)..t, Real.exp (-∫ u in (0:ℝ)..s, a u) * gramEnergy M f s :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => by
      have := hF0 s; positivity
  calc gramEnergy M y t ≤ _ := hprop
    _ ≤ Real.exp A * (Z + F) := by
        gcongr

/-- `thm:main-curvature-propagation`, second box
(`eq:main-derived-l2-curvature`): with a uniformly stable interpolation
`‖𝓘_X y_X(t)‖_{L²(Σ_t)} = ρ(t) ≤ C_I z(t)`, lapse `0 ≤ N ≤ N_*`, and
`‖R_X‖_{L²(K)} ≤ √(∫₀^{T_*} N ρ²) + C_ζ` (slice decomposition of `L²(K)`
plus `‖ζ_X‖_{L²(K)} ≤ C_ζ`), the uniform energy bound
`z ≤ e^{A_*}(Z_* + F_*)` on `[0, T_*]` gives
`‖R_X‖_{L²(K)} ≤ C_I √(N_* T_*) e^{A_*}(Z_* + F_*) + C_ζ`. -/
theorem derived_l2_curvature_bound (z ρ N : ℝ → ℝ) {T Nstar CI Cζ B RL2 : ℝ}
    (hT : 0 ≤ T) (hCI : 0 ≤ CI) (hB : 0 ≤ B)
    (hz : ∀ t ∈ Set.Icc 0 T, z t ≤ B)
    (hz0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ z t)
    (hρ : ∀ t ∈ Set.Icc 0 T, 0 ≤ ρ t ∧ ρ t ≤ CI * z t)
    (hN : ∀ t ∈ Set.Icc 0 T, 0 ≤ N t ∧ N t ≤ Nstar)
    (hint : IntervalIntegrable (fun t => N t * ρ t ^ 2) volume 0 T)
    (hR : RL2 ≤ Real.sqrt (∫ t in (0:ℝ)..T, N t * ρ t ^ 2) + Cζ) :
    RL2 ≤ CI * Real.sqrt (Nstar * T) * B + Cζ := by
  have hNstar : 0 ≤ Nstar := by
    rcases hN 0 ⟨le_refl 0, hT⟩ with ⟨h0, h1⟩
    linarith
  have hpt : ∀ t ∈ Set.Icc 0 T, N t * ρ t ^ 2 ≤ Nstar * (CI * B) ^ 2 := by
    intro t ht
    obtain ⟨hρ0, hρ1⟩ := hρ t ht
    obtain ⟨hN0, hN1⟩ := hN t ht
    have hzt := hz t ht
    have hz0t := hz0 t ht
    have h1 : ρ t ≤ CI * B := hρ1.trans (mul_le_mul_of_nonneg_left hzt hCI)
    have h2 : ρ t ^ 2 ≤ (CI * B) ^ 2 := pow_le_pow_left₀ hρ0 h1 2
    calc N t * ρ t ^ 2 ≤ Nstar * ρ t ^ 2 := mul_le_mul_of_nonneg_right hN1 (sq_nonneg _)
      _ ≤ Nstar * (CI * B) ^ 2 := mul_le_mul_of_nonneg_left h2 hNstar
  have hI : ∫ t in (0:ℝ)..T, N t * ρ t ^ 2 ≤ Nstar * T * (CI * B) ^ 2 := by
    calc ∫ t in (0:ℝ)..T, N t * ρ t ^ 2 ≤ ∫ t in (0:ℝ)..T, Nstar * (CI * B) ^ 2 :=
          intervalIntegral.integral_mono_on hT hint intervalIntegrable_const
            (fun t ht => hpt t ht)
      _ = Nstar * T * (CI * B) ^ 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hsqrt : Real.sqrt (∫ t in (0:ℝ)..T, N t * ρ t ^ 2) ≤ CI * Real.sqrt (Nstar * T) * B := by
    calc Real.sqrt (∫ t in (0:ℝ)..T, N t * ρ t ^ 2)
        ≤ Real.sqrt (Nstar * T * (CI * B) ^ 2) := Real.sqrt_le_sqrt hI
      _ = Real.sqrt (Nstar * T) * (CI * B) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ = CI * Real.sqrt (Nstar * T) * B := by ring
  linarith

end RenewalGeometry
