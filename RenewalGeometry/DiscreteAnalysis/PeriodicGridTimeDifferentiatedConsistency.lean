/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridCompositionConsistency
import RenewalGeometry.DiscreteAnalysis.PeriodicGridMoserComposition

/-!
# Time-differentiated sampling, difference, product and composition consistency
  (`lem:supp-open-interpolation`, last assertion; emergent-spacetime manuscript, supplement)

The five estimates of `lem:supp-open-interpolation` (`sampling_error`, `sampling_stable`,
`difference_consistency_Dp/_Dm/_D0`, `product_consistency`, `composition_consistency`) admit
time-differentiated versions "by the ordinary chain rule".  Here physical time is a real
parameter `t`, grid histories are maps `ℝ → (Grid N → ℂ)` and continuum histories are maps
`ℝ → C(𝕋³, ℂ)`; every constant is independent of the mesh `h = 1/N` and of the history.

* `interpL`: `𝓘_h` as a continuous linear map; `hasDerivAt_interp`, `hasDerivAt_proj`,
  `hasDerivAt_linear` (a grid linear map `T` commutes with `∂_t`).
* `sampling_error_deriv`, `sampling_stable_deriv`: `∂_t(𝒫_h u - u) = 𝒫_h u_t - u_t` in `C(𝕋³)`,
  with `‖∂_t(𝒫_h u - u)‖²_{H^r} ≤ C h^{2j} ‖u_t‖²_{H^{r+j}}` and `‖∂_t 𝒫_h u‖²_{H^r} ≤ C ‖u_t‖²_{H^r}`.
* `difference_consistency_deriv` (`D = D_i^±, D_i⁰`):
  `∂_t(𝓘_h D u_h - ∂_i 𝓘_h u_h) = 𝓘_h D u_{h,t} - ∂_i 𝓘_h u_{h,t}`, bounded by
  `(π²/4)^{r+2} h² ‖u_{h,t}‖²_{r+2,h}`.
* `product_consistency_deriv`: the derivative of `𝓘_h(u_h w_h) - (𝓘_h u_h)(𝓘_h w_h)` is the sum of the
  two product errors of `(u_{h,t}, w_h)` and `(u_h, w_{h,t})` (Leibniz rule), with
  `‖·‖²_{H^r} ≤ C h² (‖u_{h,t}‖²_{r+1,h} ‖w_h‖²_{r+1,h} + ‖u_h‖²_{r+1,h} ‖w_{h,t}‖²_{r+1,h})`.
* `composition_consistency_deriv`: for `A` analytic at the constant base point `c`, on the small
  chart, `t ↦ 𝓘_h A(u_h)(y) - A(𝓘_h u_h)(y)` is differentiable at every point `y` of the torus, with
  derivative `𝓘_h[DA(u_h) u_{h,t}](y) - DA(𝓘_h u_h)(𝓘_h u_{h,t})(y)` (chain rule, `DA = fderiv ℂ A`),
  and `‖·‖²_{H^r} ≤ C h² (Σ_j ‖u_{j,t}‖_{r+1,h})²`.  Proof: the map `(z, w) ↦ DA(z) w` is analytic at
  `(c, 0)`, so `composition_consistency` applies to it; homogeneity in `w` removes the smallness
  requirement on the velocity `u_{h,t}`.

In every case the derivative of the error is again an error of the same type (with `u_t` in place
of `u`, or a sum of such errors), so the estimates iterate: one spatial order is spent on each
controlled time derivative exactly through the norms of `u_t` appearing on the right.
-/

open Finset ComplexConjugate UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.PeriodicGridSobolev

namespace TimeConsistency

open LatticeTorusPlancherel Sampling RenewalGeometry.PeriodicGridSobolev.Composition

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable section

/-! ### `𝓘_h` and grid linear maps commute with the time derivative -/

/-- The trigonometric interpolant `𝓘_h` as a continuous linear map. -/
def interpL (N : ℕ) [NeZero N] : (Grid N → ℂ) →L[ℂ] C(UnitAddTorus (Fin 3), ℂ) :=
  LinearMap.toContinuousLinearMap
    ({ toFun := interp, map_add' := interp_add, map_smul' := interp_smul } :
      (Grid N → ℂ) →ₗ[ℂ] C(UnitAddTorus (Fin 3), ℂ))

theorem interpL_apply (N : ℕ) [NeZero N] (u : Grid N → ℂ) : interpL N u = interp u := rfl

variable {N : ℕ} [NeZero N]

/-- `∂_t 𝓘_h u_h = 𝓘_h ∂_t u_h` in `C(𝕋³, ℂ)`. -/
theorem hasDerivAt_interp {u : ℝ → Grid N → ℂ} {u' : Grid N → ℂ} {t : ℝ}
    (hu : HasDerivAt u u' t) : HasDerivAt (fun s => interp (u s)) (interp u') t := by
  have := ((interpL N).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu
  exact this

/-- `∂_t 𝒫_h f = 𝒫_h ∂_t f` in `C(𝕋³, ℂ)`. -/
theorem hasDerivAt_proj {f : ℝ → C(UnitAddTorus (Fin 3), ℂ)} {f' : C(UnitAddTorus (Fin 3), ℂ)}
    {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => projL N (f s)) (projL N f') t :=
  ((projL N).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hf

/-- A grid linear map commutes with the time derivative. -/
theorem hasDerivAt_linear (T : Module.End ℂ (Grid N → ℂ)) {u : ℝ → Grid N → ℂ}
    {u' : Grid N → ℂ} {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => T (u s)) (T u') t := by
  have := ((LinearMap.toContinuousLinearMap T).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu
  exact this

/-- The spectral derivative `specD i` is linear. -/
def specDL (i : Fin 3) : Module.End ℂ (Grid N → ℂ) where
  toFun := specD i
  map_add' u w := by
    funext x
    simp only [specD, Pi.add_apply, dft_add, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  map_smul' a u := by
    funext x
    simp only [specD, Pi.smul_apply, dft_smul, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun k _ => by ring

theorem specDL_apply (i : Fin 3) (u : Grid N → ℂ) : specDL i u = specD i u := rfl

/-! ### Sampling -/

/-- **Time-differentiated sampling estimate** (`eq:supp-open-sampling-estimate`, with the `h^j`,
`H^{r+j}` refinement).  For a `C(𝕋³)`-valued history `f` differentiable at `t`,
`∂_t(𝒫_h f - f) = 𝒫_h f_t - f_t`, and `‖∂_t(𝒫_h f - f)‖²_{H^r} ≤ C h^{2j} ‖f_t‖²_{H^{r+j}}`. -/
theorem sampling_error_deriv (r j : ℕ) (hrj : 2 ≤ r + j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (f : ℝ → C(UnitAddTorus (Fin 3), ℂ))
      (f' : C(UnitAddTorus (Fin 3), ℂ)) (t : ℝ), HasDerivAt f f' t →
      Summable (fun n => trigWeight (r + j) n * ‖mFourierCoeff ⇑f' n‖ ^ 2) →
      HasDerivAt (fun s => projL N (f s) - f s) (projL N f' - f') t ∧
      trigSobSq r ⇑(projL N f' - f') ≤ C * (((N : ℝ) ^ 2) ^ j)⁻¹ * trigSobSq (r + j) ⇑f' := by
  obtain ⟨C, hC, hE⟩ := sampling_error r j hrj
  exact ⟨C, hC, fun N _ f f' t hf hs => ⟨(hasDerivAt_proj hf).sub hf, (hE N f' hs).2⟩⟩

/-- **Time-differentiated sampling stability**: `‖∂_t 𝒫_h f‖²_{H^r} ≤ C ‖f_t‖²_{H^r}` (`r ≥ 2`). -/
theorem sampling_stable_deriv (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (f : ℝ → C(UnitAddTorus (Fin 3), ℂ))
      (f' : C(UnitAddTorus (Fin 3), ℂ)) (t : ℝ), HasDerivAt f f' t →
      Summable (fun n => trigWeight r n * ‖mFourierCoeff ⇑f' n‖ ^ 2) →
      HasDerivAt (fun s => projL N (f s)) (projL N f') t ∧
      trigSobSq r ⇑(projL N f') ≤ C * trigSobSq r ⇑f' := by
  obtain ⟨C, hC, hE⟩ := sampling_stable r hr
  exact ⟨C, hC, fun N _ f f' t hf hs => ⟨hasDerivAt_proj hf, (hE N f' hs).2⟩⟩

/-! ### Difference consistency -/

/-- **Time-differentiated difference consistency** for `D_i⁺`. -/
theorem difference_consistency_Dp_deriv (r : ℕ) (i : Fin 3) {u : ℝ → Grid N → ℂ}
    {u' : Grid N → ℂ} {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => interp (Dp i (u s)) - interp (specD i (u s)))
      (interp (Dp i u') - interp (specD i u')) t ∧
    trigSobSq r ⇑(interp (Dp i u') - interp (specD i u')) ≤
      ((π ^ 2 / 4) ^ (r + 2) * (((N : ℝ) ^ 2)⁻¹)) * sobSq (r + 2) u' :=
  ⟨(hasDerivAt_interp (hasDerivAt_linear (Dp i) hu)).sub
      (hasDerivAt_interp (hasDerivAt_linear (specDL i) hu)),
    difference_consistency_Dp r i u'⟩

/-- **Time-differentiated difference consistency** for `D_i⁻`. -/
theorem difference_consistency_Dm_deriv (r : ℕ) (i : Fin 3) {u : ℝ → Grid N → ℂ}
    {u' : Grid N → ℂ} {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => interp (Dm i (u s)) - interp (specD i (u s)))
      (interp (Dm i u') - interp (specD i u')) t ∧
    trigSobSq r ⇑(interp (Dm i u') - interp (specD i u')) ≤
      ((π ^ 2 / 4) ^ (r + 2) * (((N : ℝ) ^ 2)⁻¹)) * sobSq (r + 2) u' :=
  ⟨(hasDerivAt_interp (hasDerivAt_linear (Dm i) hu)).sub
      (hasDerivAt_interp (hasDerivAt_linear (specDL i) hu)),
    difference_consistency_Dm r i u'⟩

/-- **Time-differentiated difference consistency** for `D_i⁰`. -/
theorem difference_consistency_D0_deriv (r : ℕ) (i : Fin 3) {u : ℝ → Grid N → ℂ}
    {u' : Grid N → ℂ} {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => interp (D0 i (u s)) - interp (specD i (u s)))
      (interp (D0 i u') - interp (specD i u')) t ∧
    trigSobSq r ⇑(interp (D0 i u') - interp (specD i u')) ≤
      ((π ^ 2 / 4) ^ (r + 2) * (((N : ℝ) ^ 2)⁻¹)) * sobSq (r + 2) u' :=
  ⟨(hasDerivAt_interp (hasDerivAt_linear (D0 i) hu)).sub
      (hasDerivAt_interp (hasDerivAt_linear (specDL i) hu)),
    difference_consistency_D0 r i u'⟩

/-! ### Product consistency -/

/-- The product error `𝓘_h(u w) - (𝓘_h u)(𝓘_h w)` is a trigonometric polynomial. -/
theorem isTP_productError (u w : Grid N → ℂ) : IsTP (interp (u * w) - interp u * interp w) :=
  (isTP_interp _).sub ((isTP_interp _).mul (isTP_interp _))

/-- **Time-differentiated product consistency** (`eq:supp-open-product-consistency`).  For grid
histories `u, w` differentiable at `t`, the time derivative of `𝓘_h(u w) - (𝓘_h u)(𝓘_h w)` in
`C(𝕋³)` is the sum of the product errors of `(u_t, w)` and `(u, w_t)` (Leibniz rule), and for
`r ≥ 1`, with a mesh-independent `C`,
`‖∂_t[𝓘_h(u w) - (𝓘_h u)(𝓘_h w)]‖²_{H^r} ≤ C h² (‖u_t‖²_{r+1,h} ‖w‖²_{r+1,h} + ‖u‖²_{r+1,h} ‖w_t‖²_{r+1,h})`. -/
theorem product_consistency_deriv (r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (u w : ℝ → Grid N → ℂ) (u' w' : Grid N → ℂ) (t : ℝ),
      HasDerivAt u u' t → HasDerivAt w w' t →
      HasDerivAt (fun s => interp (u s * w s) - interp (u s) * interp (w s))
        ((interp (u' * w t) - interp u' * interp (w t)) +
          (interp (u t * w') - interp (u t) * interp w')) t ∧
      trigSobSq r ⇑((interp (u' * w t) - interp u' * interp (w t)) +
          (interp (u t * w') - interp (u t) * interp w')) ≤
        C * ((N : ℝ) ^ 2)⁻¹ * (sobSq (r + 1) u' * sobSq (r + 1) (w t) +
          sobSq (r + 1) (u t) * sobSq (r + 1) w') := by
  obtain ⟨C, hC, hP⟩ := product_consistency r hr
  refine ⟨2 * C, by positivity, fun N _ u w u' w' t hu hw => ⟨?_, ?_⟩⟩
  · have h1 : HasDerivAt (fun s => interp (u s * w s)) (interp (u' * w t + u t * w')) t :=
      hasDerivAt_interp (hu.mul hw)
    have h2 := (hasDerivAt_interp hu).mul (hasDerivAt_interp hw)
    have h3 := h1.sub h2
    rw [interp_add] at h3
    exact h3.congr_deriv (by abel)
  · obtain ⟨-, hb⟩ := trigSobSq_add_le r _ _ ((isTP_productError u' (w t)).summable r)
      ((isTP_productError (u t) w').summable r)
    have e1 := hP N u' (w t)
    have e2 := hP N (u t) w'
    refine hb.trans ?_
    nlinarith

/-! ### Composition consistency -/

theorem mFourierCoeff_const_mul (a : ℂ) (f : UnitAddTorus (Fin 3) → ℂ) (n : Fin 3 → ℤ) :
    mFourierCoeff (fun y => a * f y) n = a * mFourierCoeff f n := by
  simp only [mFourierCoeff, smul_eq_mul]
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext y
  ring

theorem trigSobSq_const_mul (r : ℕ) (a : ℂ) (f : UnitAddTorus (Fin 3) → ℂ) :
    trigSobSq r (fun y => a * f y) = ‖a‖ ^ 2 * trigSobSq r f := by
  unfold trigSobSq
  rw [← tsum_mul_left]
  congr 1
  funext n
  rw [mFourierCoeff_const_mul, norm_mul, mul_pow]
  ring

/-- Uniform sup bound of an interpolant by the grid `H^{r+1}` norm (`r ≥ 1`). -/
theorem norm_interp_apply_le (r : ℕ) (hr : 1 ≤ r) (v : Grid N → ℂ) (y : UnitAddTorus (Fin 3)) :
    ‖interp v y‖ ≤ Real.sqrt cEmb * (π / 2) ^ (r + 1) * sobNorm (r + 1) v := by
  calc ‖interp v y‖ ≤ ‖interp v‖ := (interp v).norm_coe_le_norm y
    _ ≤ Real.sqrt cEmb * sn 2 ⇑(interp v) := norm_le_sn_two (isTP_interp v)
    _ ≤ Real.sqrt cEmb * sn (r + 1) ⇑(interp v) := by
        gcongr; exact sn_mono (by omega) (isTP_interp v)
    _ ≤ Real.sqrt cEmb * ((π / 2) ^ (r + 1) * sobNorm (r + 1) v) := by
        gcongr; exact sn_interp_le _ _
    _ = _ := by ring

section CompositionDeriv

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The directional-derivative map `(z, w) ↦ DA(z) w` on `ℂ^{ι ⊕ ι}` (`DA = fderiv ℂ A`). -/
def dirDerivMap (A : (ι → ℂ) → ℂ) (z : ι ⊕ ι → ℂ) : ℂ :=
  fderiv ℂ A (fun j => z (Sum.inl j)) (fun j => z (Sum.inr j))

/-- If `A` is analytic at `c`, the map `(z, w) ↦ DA(z) w` is analytic at `(c, 0)`. -/
theorem analyticAt_dirDerivMap {A : (ι → ℂ) → ℂ} {c : ι → ℂ} (hA : AnalyticAt ℂ A c) :
    AnalyticAt ℂ (dirDerivMap A) (Sum.elim c 0) := by
  set L : (ι ⊕ ι → ℂ) →L[ℂ] (ι → ℂ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Sum.inl j)
  have hL : ∀ z, L z = fun j => z (Sum.inl j) := fun z => rfl
  have h1 : AnalyticAt ℂ (fderiv ℂ A) (L (Sum.elim c 0)) := by
    have : L (Sum.elim c 0) = c := by funext j; simp [hL]
    rw [this]; exact hA.fderiv
  have h2 : AnalyticAt ℂ (fun z => fderiv ℂ A (L z)) (Sum.elim c 0) :=
    h1.comp (L.analyticAt _)
  have e : dirDerivMap A = fun z => ∑ j, z (Sum.inr j) * fderiv ℂ A (L z) (Pi.single j 1) := by
    funext z
    have hw : (fun j => z (Sum.inr j)) = ∑ j, z (Sum.inr j) • (Pi.single j 1 : ι → ℂ) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [dirDerivMap, hw, map_sum]
    simp [hL]
  rw [e]
  refine Finset.analyticAt_fun_sum _ fun j _ => ?_
  have h3 : AnalyticAt ℂ (fun z => fderiv ℂ A (L z) (Pi.single j 1)) (Sum.elim c 0) :=
    (ContinuousLinearMap.apply ℂ ℂ (Pi.single j (1 : ℂ) : ι → ℂ)).analyticAt _ |>.comp h2
  have h4 : AnalyticAt ℂ (fun z : ι ⊕ ι → ℂ => z (Sum.inr j)) (Sum.elim c 0) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ⊕ ι => ℂ) (Sum.inr j)).analyticAt _
  exact h4.mul h3

theorem mem_eball_of_norm_le {z c : ι → ℂ} {ρ : NNReal} {R : ENNReal} (hρR : (ρ : ENNReal) < R)
    (h : ‖z - c‖ ≤ ρ / 2) : z ∈ Metric.eball c R := by
  rw [Metric.mem_eball]
  refine lt_of_le_of_lt ?_ hρR
  rw [edist_eq_enorm_sub, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
  have := ρ.2
  linarith

/-- The sup-norm of a family of interpolant deviations is controlled by the chart quantity. -/
theorem norm_sub_le_of_chart (r : ℕ) (hr : 1 ≤ r) {N : ℕ} [NeZero N] (v : ι → Grid N → ℂ)
    (z c : ι → ℂ) (hz : ∀ j, ∃ y, z j - c j = interp (v j) y) :
    ‖z - c‖ ≤ Real.sqrt cEmb * (π / 2) ^ (r + 1) * ∑ j, sobNorm (r + 1) (v j) := by
  have hK : 0 ≤ Real.sqrt cEmb * (π / 2) ^ (r + 1) := by positivity
  refine (pi_norm_le_iff_of_nonneg (by
    exact mul_nonneg hK (sum_nonneg fun j _ => Real.sqrt_nonneg _))).mpr fun j => ?_
  obtain ⟨y, hy⟩ := hz j
  rw [Pi.sub_apply, hy]
  refine (norm_interp_apply_le r hr _ y).trans ?_
  exact mul_le_mul_of_nonneg_left
    (single_le_sum (f := fun j => sobNorm (r + 1) (v j)) (fun _ _ => Real.sqrt_nonneg _)
      (mem_univ j)) hK

theorem interp_sub_const_apply {N : ℕ} [NeZero N] (u : Grid N → ℂ) (a : ℂ)
    (y : UnitAddTorus (Fin 3)) : interp (u - fun _ => a) y = interp u y - a := by
  rw [interp_sub, interp_const]
  rfl

/-- **Time-differentiated analytic composition consistency** (`eq:supp-open-composition-consistency`,
differentiated once in time).  Let `A : ℂ^ι → ℂ` be analytic at the constant base point `c` and
`r ≥ 1`.  There are mesh-independent `δ > 0, C` such that for every grid history
`u : ℝ → (ι → Grid N → ℂ)` differentiable at `t` (velocity `u_t = u'`) whose position lies in the
small chart `Σ_j ‖u_j(t) - c_j‖_{r+1,h} ≤ δ`:
* at every point `y` of the torus, `s ↦ 𝓘_h A(u(s))(y) - A(𝓘_h u(s))(y)` is differentiable at `t`
  with derivative `D(y) = 𝓘_h[DA(u) u_t](y) - DA(𝓘_h u(y))(𝓘_h u_t(y))` (chain rule), and
* `‖D‖²_{H^r} ≤ C h² (Σ_j ‖u_{j,t}‖_{r+1,h})²`, with no smallness assumption on the velocity. -/
theorem composition_consistency_deriv (r : ℕ) (hr : 1 ≤ r) {A : (ι → ℂ) → ℂ}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) ℂ} {c : ι → ℂ} {R : ENNReal}
    (hA : HasFPowerSeriesOnBall A p c R) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (u : ℝ → ι → Grid N → ℂ) (u' : ι → Grid N → ℂ)
      (t : ℝ), HasDerivAt u u' t →
      ∑ j, sobNorm (r + 1) (u t j - fun _ => c j) ≤ δ →
      (∀ y, HasDerivAt
        (fun s => interp (fun x => A (fun j => u s j x)) y - A (fun j => interp (u s j) y))
        (interp (fun x => fderiv ℂ A (fun j => u t j x) (fun j => u' j x)) y -
          fderiv ℂ A (fun j => interp (u t j) y) (fun j => interp (u' j) y)) t) ∧
      trigSobSq r (fun y => interp (fun x => fderiv ℂ A (fun j => u t j x) (fun j => u' j x)) y -
          fderiv ℂ A (fun j => interp (u t j) y) (fun j => interp (u' j) y)) ≤
        C * ((N : ℝ) ^ 2)⁻¹ * (∑ j, sobNorm (r + 1) (u' j)) ^ 2 := by
  obtain ⟨p', R', hA'⟩ := analyticAt_dirDerivMap hA.analyticAt
  obtain ⟨δ', hδ', C', hC', hcomp⟩ := composition_consistency (ι := ι ⊕ ι) r hr hA'
  obtain ⟨ρ, hρ0, hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hA.r_pos
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hρ0)
  set K : ℝ := Real.sqrt cEmb * (π / 2) ^ (r + 1) with hKdef
  have hK0 : 0 ≤ K := by positivity
  set δ : ℝ := min (δ' / 2) (ρ / (2 * (K + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ, 4 * C', by positivity, fun N _ u u' t hu hchart => ⟨fun y => ?_, ?_⟩⟩
  · -- the chart keeps every relevant point inside the ball of convergence
    have hKσ : K * ∑ j, sobNorm (r + 1) (u t j - fun _ => c j) ≤ ρ / 2 := by
      have h1 : ∑ j, sobNorm (r + 1) (u t j - fun _ => c j) ≤ ρ / (2 * (K + 1)) :=
        hchart.trans (min_le_right _ _)
      have h2 : K * ∑ j, sobNorm (r + 1) (u t j - fun _ => c j) ≤
          (K + 1) * (ρ / (2 * (K + 1))) :=
        mul_le_mul (by linarith) h1 (sum_nonneg fun j _ => Real.sqrt_nonneg _) (by linarith)
      have h3 : (K + 1) * (ρ / (2 * (K + 1))) = ρ / 2 := by field_simp
      linarith
    have hball : ∀ z : ι → ℂ, (∀ j, ∃ y, z j - c j = interp (u t j - fun _ => c j) y) →
        HasFDerivAt A (fderiv ℂ A z) z := by
      intro z hz
      have := norm_sub_le_of_chart r hr (fun j => u t j - fun _ => c j) z c hz
      exact ((hA.analyticAt_of_mem (mem_eball_of_norm_le hρR (this.trans hKσ))).differentiableAt
        ).hasFDerivAt
    have hcomp1 : ∀ j, HasDerivAt (fun s => u s j) (u' j) t := fun j => hasDerivAt_pi.mp hu j
    -- first term: interpolant of the grid composition
    have hg : HasDerivAt (fun s => fun x => A (fun j => u s j x))
        (fun x => fderiv ℂ A (fun j => u t j x) (fun j => u' j x)) t := by
      refine hasDerivAt_pi.mpr fun x => ?_
      have hz : HasDerivAt (fun s => fun j => u s j x) (fun j => u' j x) t :=
        hasDerivAt_pi.mpr fun j => hasDerivAt_pi.mp (hcomp1 j) x
      have hAz := hball (fun j => u t j x) fun j =>
        ⟨samplePt x, by rw [interp_sub_const_apply, interp_sample]⟩
      exact (hAz.restrictScalars ℝ).comp_hasDerivAt t hz
    have hF1 := ((ContinuousMap.evalCLM ℝ y).hasFDerivAt).comp_hasDerivAt t
      (hasDerivAt_interp hg)
    -- second term: composition of the interpolants
    have hz2 : HasDerivAt (fun s => fun j => interp (u s j) y) (fun j => interp (u' j) y) t :=
      hasDerivAt_pi.mpr fun j => by
        have := ((ContinuousMap.evalCLM ℝ y : C(UnitAddTorus (Fin 3), ℂ) →L[ℝ] ℂ).hasFDerivAt
          ).comp_hasDerivAt t (hasDerivAt_interp (hcomp1 j))
        exact this
    have hAz2 := hball (fun j => interp (u t j) y) fun j =>
      ⟨y, by rw [interp_sub_const_apply]⟩
    have hF2 := (hAz2.restrictScalars ℝ).comp_hasDerivAt t hz2
    exact hF1.sub hF2
  · set D : UnitAddTorus (Fin 3) → ℂ := fun y =>
      interp (fun x => fderiv ℂ A (fun j => u t j x) (fun j => u' j x)) y -
        fderiv ℂ A (fun j => interp (u t j) y) (fun j => interp (u' j) y) with hDdef
    set a := ∑ j, sobNorm (r + 1) (u t j - fun _ => c j)
    set σ := ∑ j, sobNorm (r + 1) (u' j)
    have ha0 : 0 ≤ a := sum_nonneg fun j _ => Real.sqrt_nonneg _
    have hσ0 : 0 ≤ σ := sum_nonneg fun j _ => Real.sqrt_nonneg _
    have ha : a ≤ δ' / 2 := hchart.trans (min_le_left _ _)
    set X := trigSobSq r D
    have hX0 : 0 ≤ X := trigSobSq_nonneg' r D
    set M : ℝ := C' * ((N : ℝ) ^ 2)⁻¹ * δ' ^ 2
    have hM0 : 0 ≤ M := by positivity
    -- scaled comparison: `D` is linear in the velocity, the chart constraint is not
    have hscale : ∀ lam : ℝ, 0 < lam → lam * σ ≤ δ' / 2 → lam ^ 2 * X ≤ M := by
      intro lam hlam hlamσ
      set U : ι ⊕ ι → Grid N → ℂ := Sum.elim (u t) (fun j => (lam : ℂ) • u' j)
      have hdev : ∑ k, sobNorm (r + 1) (U k - fun _ => Sum.elim c 0 k) = a + lam * σ := by
        rw [Fintype.sum_sum_type]
        congr 1
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        simp only [U, Sum.elim_inr, Pi.zero_apply]
        rw [show ((lam : ℂ) • u' j - fun _ => (0 : ℂ)) = (lam : ℂ) • u' j by
          funext x; simp, Moser.sobNorm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hlam]
      have hdevle : a + lam * σ ≤ δ' := by linarith
      have hb := hcomp N U (by rw [hdev]; exact hdevle)
      rw [hdev] at hb
      have hfun : (fun y => interp (fun x => dirDerivMap A (fun k => U k x)) y -
          dirDerivMap A (fun k => interp (U k) y)) = fun y => (lam : ℂ) * D y := by
        funext y
        have e1 : (fun x => dirDerivMap A (fun k => U k x)) =
            (lam : ℂ) • fun x => fderiv ℂ A (fun j => u t j x) (fun j => u' j x) := by
          funext x
          simp only [dirDerivMap, U, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply]
          rw [show (fun j => (lam : ℂ) • u' j x) = (lam : ℂ) • fun j => u' j x from rfl,
            map_smul]
        have e2 : dirDerivMap A (fun k => interp (U k) y) =
            (lam : ℂ) * fderiv ℂ A (fun j => interp (u t j) y) (fun j => interp (u' j) y) := by
          simp only [dirDerivMap, U, Sum.elim_inl, Sum.elim_inr, interp_smul]
          rw [show (fun j => ((lam : ℂ) • interp (u' j)) y) =
            (lam : ℂ) • fun j => interp (u' j) y from rfl, map_smul, smul_eq_mul]
        rw [e1, e2, interp_smul, hDdef]
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      rw [hfun, trigSobSq_const_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hb
      refine hb.trans ?_
      have : (a + lam * σ) ^ 2 ≤ δ' ^ 2 := pow_le_pow_left₀ (by positivity) hdevle 2
      calc C' * ((N : ℝ) ^ 2)⁻¹ * (a + lam * σ) ^ 2 ≤ C' * ((N : ℝ) ^ 2)⁻¹ * δ' ^ 2 := by
            gcongr
        _ = M := rfl
    rcases hσ0.lt_or_eq with hσ | hσ
    · -- positive velocity norm: optimal scaling `lam = δ' / (2σ)`
      have h := hscale (δ' / (2 * σ)) (by positivity) (by
        rw [div_mul_eq_mul_div, mul_comm, ← div_mul_eq_mul_div]
        field_simp
        rfl)
      have e : X = (δ' / (2 * σ)) ^ 2 * X * (4 * σ ^ 2 / δ' ^ 2) := by
        field_simp
        ring
      rw [e]
      calc (δ' / (2 * σ)) ^ 2 * X * (4 * σ ^ 2 / δ' ^ 2) ≤ M * (4 * σ ^ 2 / δ' ^ 2) := by
            gcongr
        _ = 4 * C' * ((N : ℝ) ^ 2)⁻¹ * σ ^ 2 := by
            simp only [M]; field_simp
    · -- vanishing velocity norm: every scaling is admissible, so `X = 0`
      rw [← hσ]
      have hX : X ≤ 0 := by
        by_contra hneg
        replace hneg := not_le.mp hneg
        have h := hscale (M / X + 1) (by positivity) (by rw [← hσ]; simp; positivity)
        have h1 : 1 ≤ M / X + 1 := by have : 0 ≤ M / X := by positivity
                                      linarith
        have h2 : (M / X + 1) * X ≤ (M / X + 1) ^ 2 * X := by
          rw [sq]; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) h1)
            hX0
        have h3 : (M / X + 1) * X = M + X := by field_simp
        linarith
      have : (0 : ℝ) ≤ 4 * C' * ((N : ℝ) ^ 2)⁻¹ * 0 ^ 2 := by simp
      linarith

/-- Non-vacuity: the constant history at the base point lies in every chart, and every analytic
`A` (e.g. a constant) has a power series on a ball. -/
example (r : ℕ) (N : ℕ) [NeZero N] (c : ι → ℂ) :
    ∑ j, sobNorm (N := N) (r + 1) ((fun _ => c j) - fun _ => c j) = 0 := by
  simp [Moser.sobNorm_zero]

example (c : ι → ℂ) (a : ℂ) :
    HasFPowerSeriesOnBall (fun _ : ι → ℂ => a) (constFormalMultilinearSeries ℂ (ι → ℂ) a) c ⊤ :=
  hasFPowerSeriesOnBall_const

end CompositionDeriv

end

end TimeConsistency

end RenewalGeometry.PeriodicGridSobolev
