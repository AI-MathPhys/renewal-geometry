/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Interface lifting of face measures on a cubical mesh
  (`lem:supp-interface-lifting`, `eq:supp-interface-lifting`, `eq:supp-interface-lifting-bounds`,
  `eq:main-interface-budget`; emergent-spacetime manuscript, supplement)

Geometric measure theory of a uniform cubical mesh of side `h > 0` in `ℝ^{n+1}` (the manuscript
uses `n + 1 = 4`).

* A **face** `f = (i, k)` (`Face n`) has normal direction `i : Fin (n+1)` and integer label
  `k : Fin (n+1) → ℤ`; as a set it is `{x : x_i = k_i h, k_j h ≤ x_j < (k_j + 1) h, j ≠ i}`.  It is
  parametrized by its tangential coordinates `y ∈ ℝ^n` through `x = insertNth i (k_i h) y`
  (`facePoint`), over the box `faceBox h f = Π_j [k_{s(j)} h, (k_{s(j)} + 1) h)`
  (`s = i.succAbove`).  The **face measure** `δ_f` is the push-forward of Lebesgue measure on the
  box (the product measure on the coordinate face, i.e. the `n`-dimensional surface measure of
  the face); `faceMeasurePairing` is the pairing `⟨Σ_f J_f δ_f, Φ⟩ = Σ_f ∫_f Φ J_f`.
* The **normal prism** of `f` is `{y + r e_i : y ∈ f, |r| ≤ h/4}` and the **lifting**
  (`eq:supp-interface-lifting`) is `(𝓛_f J_f)(y + r e_i) = h⁻¹ η(r/h) J_f(y)`, extended by zero,
  `𝓛_h J = Σ_f 𝓛_f J_f` (`faceLift`, `interfaceLift`), for a profile `η ≥ 0` supported in
  `[-1/4, 1/4]` with `∫ η = 1` (`IsLiftingProfile`).
* `interfaceBudgetSq` is `𝒥_h² = Σ_f h⁻¹ ‖J_f‖²_{L²(f)}` (`eq:main-interface-budget`).

Main results:
* `lintegral_normalLift_sq`, `norm_integral_normalLift_sub_le`: integration in the normal
  coordinate on `ℝ × Y` (`‖𝓛 J‖₂² = h⁻¹ ‖η‖₂² ‖J‖₂²` and the `h/4`-displacement error);
* `faceLift_injOn_direction`: bounded overlap — at every point at most one face of each normal
  direction has a nonzero lift (so at most `n + 1` prisms overlap);
* `lintegral_interfaceLift_sq_le`, `eLpNorm_interfaceLift_le`: `‖𝓛_h J‖₂ ≤ C 𝒥_h` with
  `C² = (n+1) ‖η‖₂²` depending only on the dimension and `η`;
* `norm_integral_interfaceLift_sub_faceMeasure_le`: the distributional error
  `|⟨𝓛_h J - Σ J_f δ_f, Φ⟩| ≤ (h/4) Lip(Φ) Σ_f ‖J_f‖_{L¹(f)}`;
* `sum_integral_norm_le_sqrt_mul_sqrt`: `Σ_f ‖J_f‖_{L¹(f)} ≤ (#F h^{n+1})^{1/2} 𝒥_h`;
* `card_mul_pow_le_volume`: face counting — if the cells of the faces lie in `U`, then
  `#F h^{n+1} ≤ (n+1) vol(U)` (there are `O_U(h^{-(n+1)})` faces of area `h^n`);
* `interface_lifting_bounds`: **`lem:supp-interface-lifting`**, both bounds of
  `eq:supp-interface-lifting-bounds` with `C_K = ¼ ((n+1) vol U)^{1/2}`.

`‖∇Φ‖_∞` is rendered as the Lipschitz constant of the test (sup norm on `ℝ^{n+1}`); every smooth
compactly supported test is Lipschitz (`ContDiff.lipschitzWith_of_hasCompactSupport`).
-/

open MeasureTheory Filter Topology ENNReal Set
open scoped NNReal

noncomputable section

namespace RenewalGeometry.InterfaceLifting

set_option linter.unusedSectionVars false

/-! ### The lifting profile -/

/-- A lifting profile `η`: continuous, nonnegative, supported in `[-1/4, 1/4]`, with integral one
(the manuscript takes `η` smooth and supported in `(-1/4, 1/4)`). -/
structure IsLiftingProfile (η : ℝ → ℝ) : Prop where
  continuous : Continuous η
  nonneg : ∀ s, 0 ≤ η s
  support : ∀ s, η s ≠ 0 → |s| ≤ 1 / 4
  integral_eq_one : ∫ s, η s = 1

namespace IsLiftingProfile

variable {η : ℝ → ℝ}

theorem hasCompactSupport (hη : IsLiftingProfile η) : HasCompactSupport η := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Icc (-(1 / 4)) (1 / 4))
    isCompact_Icc fun s hs => ?_
  have := hη.support s hs
  exact abs_le.1 this

theorem integrable (hη : IsLiftingProfile η) : Integrable η :=
  hη.continuous.integrable_of_hasCompactSupport hη.hasCompactSupport

theorem integrable_sq (hη : IsLiftingProfile η) : Integrable fun s => η s ^ 2 :=
  (hη.continuous.pow 2).integrable_of_hasCompactSupport <|
    HasCompactSupport.of_support_subset_isCompact (K := Icc (-(1 / 4)) (1 / 4)) isCompact_Icc
      fun s hs => abs_le.1 (hη.support s fun h0 => hs (by simp [h0]))

/-- The rescaled profile `t ↦ h⁻¹ η((t - c)/h)`. -/
theorem integrable_rescaled (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h) (c : ℝ) :
    Integrable fun t => h⁻¹ * η ((t - c) / h) := by
  have h1 : Integrable fun t => η (t / h) := hη.integrable.comp_div hh.ne'
  exact (h1.comp_sub_right c).const_mul _

theorem integral_rescaled (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h) (c : ℝ) :
    ∫ t, h⁻¹ * η ((t - c) / h) = 1 := by
  rw [integral_const_mul, integral_sub_right_eq_self (fun t => η (t / h)) c,
    Measure.integral_comp_div, hη.integral_eq_one, abs_of_pos hh, smul_eq_mul, mul_one,
    inv_mul_cancel₀ hh.ne']

theorem integral_rescaled_sq (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h) (c : ℝ) :
    ∫ t, (h⁻¹ * η ((t - c) / h)) ^ 2 = h⁻¹ * ∫ s, η s ^ 2 := by
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_sub_right_eq_self (fun t => η (t / h) ^ 2) c,
    Measure.integral_comp_div (fun s => η s ^ 2), abs_of_pos hh, smul_eq_mul]
  field_simp

theorem integrable_rescaled_sq (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h) (c : ℝ) :
    Integrable fun t => (h⁻¹ * η ((t - c) / h)) ^ 2 := by
  have h1 : Integrable fun t => η (t / h) ^ 2 :=
    hη.integrable_sq.comp_div (g := fun s => η s ^ 2) hh.ne'
  simp_rw [mul_pow]
  exact (h1.comp_sub_right c).const_mul _

theorem rescaled_nonneg (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h) (c t : ℝ) :
    0 ≤ h⁻¹ * η ((t - c) / h) :=
  mul_nonneg (inv_nonneg.2 hh.le) (hη.nonneg _)

/-- On the support of the rescaled profile, `|t - c| ≤ h/4`. -/
theorem abs_sub_le_of_ne_zero (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h) {c t : ℝ}
    (ht : η ((t - c) / h) ≠ 0) : |t - c| ≤ h / 4 := by
  have := hη.support _ ht
  rw [abs_div, abs_of_pos hh, div_le_iff₀ hh] at this
  linarith

end IsLiftingProfile

/-! ### Integration in the normal coordinate on `ℝ × Y` -/

section NormalCoordinates

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SFinite ν]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The lift of a face density `J : Y → E` to the normal slab of the hyperplane `{t = c}` in
`ℝ × Y`: `(t, y) ↦ h⁻¹ η((t - c)/h) J(y)` (`eq:supp-interface-lifting` in normal coordinates). -/
def normalLift (h c : ℝ) (η : ℝ → ℝ) (J : Y → E) (p : ℝ × Y) : E :=
  (h⁻¹ * η ((p.1 - c) / h)) • J p.2

theorem enorm_sq_real (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

/-- **Integration in the normal coordinate**: `‖𝓛 J‖²_{L²(ℝ × Y)} = h⁻¹ ‖η‖²_{L²} ‖J‖²_{L²(Y)}`. -/
theorem lintegral_normalLift_sq {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h)
    (c : ℝ) {J : Y → E} (hJ : AEStronglyMeasurable J ν) :
    ∫⁻ p, ‖normalLift h c η J p‖ₑ ^ 2 ∂(volume.prod ν) =
      ENNReal.ofReal (h⁻¹ * ∫ s, η s ^ 2) * ∫⁻ y, ‖J y‖ₑ ^ 2 ∂ν := by
  have hsplit : ∀ p : ℝ × Y, ‖normalLift h c η J p‖ₑ ^ 2 =
      ‖h⁻¹ * η ((p.1 - c) / h)‖ₑ ^ 2 * ‖J p.2‖ₑ ^ 2 := fun p => by
    rw [normalLift, enorm_smul, mul_pow]
  simp_rw [hsplit]
  have hw : Measurable fun t : ℝ => h⁻¹ * η ((t - c) / h) :=
    measurable_const.mul (hη.continuous.measurable.comp
      ((measurable_id.sub_const c).div_const h))
  rw [lintegral_prod_mul (hw.enorm.pow_const 2).aemeasurable
    (hJ.enorm.pow_const 2)]
  congr 1
  simp_rw [enorm_sq_real]
  rw [← ofReal_integral_eq_lintegral_ofReal (hη.integrable_rescaled_sq hh c)
    (Eventually.of_forall fun t => sq_nonneg _), hη.integral_rescaled_sq hh c]

/-- **Distributional error of the normal lift**: for a test `φ` on `ℝ × Y` with
`|φ(t, y) - φ(c, y)| ≤ L |t - c|`,
`‖∫ φ 𝓛 J - ∫ φ(c, ·) J‖ ≤ (h/4) L ‖J‖_{L¹(Y)}`. -/
theorem norm_integral_normalLift_sub_le {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ}
    (hh : 0 < h) (c : ℝ) [CompleteSpace E] {J : Y → E} (hJ : Integrable J ν)
    {φ : ℝ × Y → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ p, |φ p| ≤ M) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t y, |φ (t, y) - φ (c, y)| ≤ L * |t - c|) :
    ‖(∫ p, φ p • normalLift h c η J p ∂(volume.prod ν)) - ∫ y, φ (c, y) • J y ∂ν‖ ≤
      h / 4 * L * ∫ y, ‖J y‖ ∂ν := by
  set w : ℝ → ℝ := fun t => h⁻¹ * η ((t - c) / h) with hw_def
  have hwi : Integrable w := hη.integrable_rescaled hh c
  have hw1 : ∫ t, w t = 1 := hη.integral_rescaled hh c
  have hw0 : ∀ t, 0 ≤ w t := hη.rescaled_nonneg hh c
  have hφc : Measurable fun y => φ (c, y) := hφ.comp measurable_prodMk_left
  -- the two integrands are integrable on the product
  have hJφ : Integrable (fun y => φ (c, y) • J y) ν := by
    refine hJ.smul_of_top_right (φ := fun y => φ (c, y)) ?_
    exact memLp_top_of_bound hφc.aestronglyMeasurable M (Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hM (c, y))
  have hI2 : Integrable (fun p : ℝ × Y => w p.1 • (φ (c, p.2) • J p.2)) (volume.prod ν) :=
    hwi.smul_prod hJφ
  have hwJ : Integrable (fun p : ℝ × Y => w p.1 • J p.2) (volume.prod ν) := hwi.smul_prod hJ
  have hI1 : Integrable (fun p => φ p • normalLift h c η J p) (volume.prod ν) := by
    refine hwJ.smul_of_top_right (φ := φ) ?_
    exact memLp_top_of_bound hφ.aestronglyMeasurable M (Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using hM p)
  have h2 : ∫ y, φ (c, y) • J y ∂ν = ∫ p, w p.1 • (φ (c, p.2) • J p.2) ∂(volume.prod ν) := by
    have := integral_prod_smul (μ := (volume : Measure ℝ)) (ν := ν) w (fun y => φ (c, y) • J y)
    rw [this, hw1, one_smul]
  rw [h2, ← integral_sub hI1 hI2]
  -- pointwise bound
  have hbound : ∀ p : ℝ × Y, ‖φ p • normalLift h c η J p - w p.1 • (φ (c, p.2) • J p.2)‖ ≤
      w p.1 * (h / 4 * L * ‖J p.2‖) := by
    rintro ⟨t, y⟩
    have heq : φ (t, y) • normalLift h c η J (t, y) - w t • (φ (c, y) • J y) =
        (w t * (φ (t, y) - φ (c, y))) • J y := by
      simp only [normalLift, hw_def, smul_smul, ← sub_smul]
      congr 1; ring
    rw [heq, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 t)]
    by_cases ht : η ((t - c) / h) = 0
    · simp [hw_def, ht]
    · have h1 := hLip t y
      have h2 := hη.abs_sub_le_of_ne_zero hh ht
      have h3 : |φ (t, y) - φ (c, y)| ≤ h / 4 * L := by nlinarith
      calc w t * |φ (t, y) - φ (c, y)| * ‖J y‖ ≤ w t * (h / 4 * L) * ‖J y‖ := by
            gcongr; exact hw0 t
        _ = w t * (h / 4 * L * ‖J y‖) := by ring
  have hbi : Integrable (fun p : ℝ × Y => w p.1 * (h / 4 * L * ‖J p.2‖)) (volume.prod ν) :=
    hwi.mul_prod (hJ.norm.const_mul _)
  calc ‖∫ p, (φ p • normalLift h c η J p - w p.1 • (φ (c, p.2) • J p.2)) ∂(volume.prod ν)‖
      ≤ ∫ p, w p.1 * (h / 4 * L * ‖J p.2‖) ∂(volume.prod ν) :=
        norm_integral_le_of_norm_le hbi (Eventually.of_forall hbound)
    _ = h / 4 * L * ∫ y, ‖J y‖ ∂ν := by
        rw [integral_prod_mul (f := w) (g := fun y => h / 4 * L * ‖J y‖), hw1, one_mul,
          integral_const_mul]

theorem aestronglyMeasurable_normalLift {η : ℝ → ℝ} (hη : IsLiftingProfile η) (h c : ℝ)
    {J : Y → E} (hJ : AEStronglyMeasurable J ν) :
    AEStronglyMeasurable (normalLift h c η J) (volume.prod ν) := by
  have hw : Measurable fun t : ℝ => h⁻¹ * η ((t - c) / h) :=
    measurable_const.mul (hη.continuous.measurable.comp
      ((measurable_id.sub_const c).div_const h))
  exact (hw.comp measurable_fst).aestronglyMeasurable.smul hJ.comp_snd

/-- A bounded measurable test times a lifted integrable face density is integrable. -/
theorem integrable_smul_normalLift {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h)
    (c : ℝ) {J : Y → E} (hJ : Integrable J ν) {φ : ℝ × Y → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ p, |φ p| ≤ M) :
    Integrable (fun p => φ p • normalLift h c η J p) (volume.prod ν) := by
  have hwJ : Integrable (fun p : ℝ × Y => (h⁻¹ * η ((p.1 - c) / h)) • J p.2) (volume.prod ν) :=
    (hη.integrable_rescaled hh c).smul_prod hJ
  refine hwJ.smul_of_top_right (φ := φ) ?_
  exact memLp_top_of_bound hφ.aestronglyMeasurable M (Eventually.of_forall fun p => by
    simpa [Real.norm_eq_abs] using hM p)

end NormalCoordinates

/-! ### The cubical mesh, its faces and face measures -/

section Mesh

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A face of the uniform cubical mesh `hℤ^{n+1}`: normal direction `i` and integer label `k`;
as a set, `{x : x_i = k_i h, k_j h ≤ x_j < (k_j + 1) h for j ≠ i}`. -/
abbrev Face (n : ℕ) := Fin (n + 1) × (Fin (n + 1) → ℤ)

/-- The tangential box `Π_j [k_{s j} h, (k_{s j} + 1) h)` (`s = i.succAbove`) parametrizing the
face `f = (i, k)`. -/
def faceBox (h : ℝ) (f : Face n) : Set (Fin n → ℝ) :=
  univ.pi fun j => Ico ((f.2 (f.1.succAbove j) : ℝ) * h) (((f.2 (f.1.succAbove j) : ℝ) + 1) * h)

/-- The normal level `k_i h` of the face `f = (i, k)`. -/
def faceLevel (h : ℝ) (f : Face n) : ℝ := (f.2 f.1 : ℝ) * h

/-- The point `insertNth i (k_i h) y` of the face with tangential coordinates `y`. -/
def facePoint (h : ℝ) (f : Face n) (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  f.1.insertNth (faceLevel h f) y

/-- The closed-open cell `Π_m [k_m h, (k_m + 1) h)` with label `k`. -/
def cell (h : ℝ) (k : Fin (n + 1) → ℤ) : Set (Fin (n + 1) → ℝ) :=
  univ.pi fun m => Ico ((k m : ℝ) * h) (((k m : ℝ) + 1) * h)

/-- Normal coordinates `(x_i, x without its i-th coordinate)`. -/
def normalCoord (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : ℝ × (Fin n → ℝ) :=
  (x i, i.removeNth x)

/-- The lift `𝓛_f J_f` of one face (`eq:supp-interface-lifting`):
`(𝓛_f J_f)(y + r e_i) = h⁻¹ η(r/h) J_f(y)` on the normal prism, zero elsewhere. -/
def faceLift (h : ℝ) (η : ℝ → ℝ) (f : Face n) (J : (Fin n → ℝ) → E) (x : Fin (n + 1) → ℝ) :
    E :=
  normalLift h (faceLevel h f) η ((faceBox h f).indicator J) (normalCoord f.1 x)

/-- The volume lifting `𝓛_h J = Σ_f 𝓛_f J_f` of a finite family of face densities. -/
def interfaceLift (h : ℝ) (η : ℝ → ℝ) (F : Finset (Face n)) (J : Face n → (Fin n → ℝ) → E)
    (x : Fin (n + 1) → ℝ) : E :=
  ∑ f ∈ F, faceLift h η f (J f) x

/-- The face-measure pairing `⟨Σ_f J_f δ_f, Φ⟩ = Σ_f ∫_f Φ J_f dσ`. -/
def faceMeasurePairing (h : ℝ) (F : Finset (Face n)) (J : Face n → (Fin n → ℝ) → E)
    (φ : (Fin (n + 1) → ℝ) → ℝ) : E :=
  ∑ f ∈ F, ∫ y in faceBox h f, φ (facePoint h f y) • J f y

/-- The squared interface budget `𝒥_h² = Σ_f h⁻¹ ‖J_f‖²_{L²(f)}` (`eq:main-interface-budget`). -/
def interfaceBudgetSq (h : ℝ) (F : Finset (Face n)) (J : Face n → (Fin n → ℝ) → E) : ℝ :=
  ∑ f ∈ F, h⁻¹ * ∫ y in faceBox h f, ‖J f y‖ ^ 2

theorem measurableSet_faceBox (h : ℝ) (f : Face n) : MeasurableSet (faceBox h f) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem measurableSet_cell (h : ℝ) (k : Fin (n + 1) → ℤ) : MeasurableSet (cell h k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem volume_faceBox {h : ℝ} (hh : 0 ≤ h) (f : Face n) :
    volume (faceBox h f) = ENNReal.ofReal (h ^ n) := by
  rw [faceBox, Real.volume_pi_Ico]
  simp only [add_mul, one_mul, add_sub_cancel_left, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [ENNReal.ofReal_pow hh]

theorem volume_cell {h : ℝ} (hh : 0 ≤ h) (k : Fin (n + 1) → ℤ) :
    volume (cell h k) = ENNReal.ofReal (h ^ (n + 1)) := by
  rw [cell, Real.volume_pi_Ico]
  simp only [add_mul, one_mul, add_sub_cancel_left, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [ENNReal.ofReal_pow hh]

theorem normalCoord_eq (i : Fin (n + 1)) :
    normalCoord i = ⇑(MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) := by
  funext x
  simp [normalCoord, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]

theorem measurePreserving_normalCoord (i : Fin (n + 1)) :
    MeasurePreserving (normalCoord i) (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
  rw [normalCoord_eq]
  exact volume_preserving_piFinSuccAbove (fun _ => ℝ) i

theorem insertNth_normalCoord (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    i.insertNth (normalCoord i x).1 (normalCoord i x).2 = x :=
  Fin.insertNth_self_removeNth i x

theorem measurable_insertNth (i : Fin (n + 1)) :
    Measurable fun p : ℝ × (Fin n → ℝ) => Fin.insertNth (α := fun _ => ℝ) i p.1 p.2 := by
  have := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm.measurable
  convert this using 1
  funext p
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

/-! #### Integer bookkeeping and bounded overlap -/

theorem int_eq_of_mem_Ico {h x : ℝ} (hh : 0 < h) {a b : ℤ}
    (ha : (a : ℝ) * h ≤ x ∧ x < ((a : ℝ) + 1) * h)
    (hb : (b : ℝ) * h ≤ x ∧ x < ((b : ℝ) + 1) * h) : a = b := by
  have h1 : (a : ℝ) < b + 1 := lt_of_mul_lt_mul_right (ha.1.trans_lt hb.2) hh.le
  have h2 : (b : ℝ) < a + 1 := lt_of_mul_lt_mul_right (hb.1.trans_lt ha.2) hh.le
  have h1' : a < b + 1 := by exact_mod_cast h1
  have h2' : b < a + 1 := by exact_mod_cast h2
  omega

theorem int_eq_of_abs_sub_le {h x : ℝ} (hh : 0 < h) {a b : ℤ} (ha : |x - a * h| ≤ h / 4)
    (hb : |x - b * h| ≤ h / 4) : a = b := by
  rw [abs_le] at ha hb
  have h1 : ((a : ℝ) - b) * h < 1 * h := by nlinarith
  have h2 : ((b : ℝ) - a) * h < 1 * h := by nlinarith
  have h1' : (a : ℝ) - b < 1 := lt_of_mul_lt_mul_right h1 hh.le
  have h2' : (b : ℝ) - a < 1 := lt_of_mul_lt_mul_right h2 hh.le
  have h1'' : a - b < 1 := by exact_mod_cast h1'
  have h2'' : b - a < 1 := by exact_mod_cast h2'
  omega

/-- Where a face lift is nonzero, the point lies in the normal prism of the face. -/
theorem mem_prism_of_faceLift_ne_zero {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ}
    (hh : 0 < h) {f : Face n} {J : (Fin n → ℝ) → E} {x : Fin (n + 1) → ℝ}
    (hx : faceLift h η f J x ≠ 0) :
    |x f.1 - faceLevel h f| ≤ h / 4 ∧ f.1.removeNth x ∈ faceBox h f := by
  simp only [faceLift, normalLift, normalCoord] at hx
  have h1 : η ((x f.1 - faceLevel h f) / h) ≠ 0 := by
    intro h0; apply hx; simp [h0]
  have h2 : f.1.removeNth x ∈ faceBox h f := by
    by_contra h0; apply hx; simp [h0]
  exact ⟨hη.abs_sub_le_of_ne_zero hh h1, h2⟩

/-- **Bounded overlap**: two faces of the same normal direction whose lifts are both nonzero at
the same point coincide.  Hence at most `n + 1` prisms overlap at any point. -/
theorem eq_of_faceLift_ne_zero {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h)
    {f f' : Face n} (hdir : f.1 = f'.1) {J J' : (Fin n → ℝ) → E} {x : Fin (n + 1) → ℝ}
    (h1 : faceLift h η f J x ≠ 0) (h2 : faceLift h η f' J' x ≠ 0) : f = f' := by
  obtain ⟨a1, b1⟩ := mem_prism_of_faceLift_ne_zero hη hh h1
  obtain ⟨a2, b2⟩ := mem_prism_of_faceLift_ne_zero hη hh h2
  obtain ⟨i, k⟩ := f
  obtain ⟨i', k'⟩ := f'
  simp only at hdir
  subst hdir
  refine Prod.ext rfl (funext fun m => ?_)
  rcases Fin.eq_self_or_eq_succAbove i m with rfl | ⟨j, rfl⟩
  · exact int_eq_of_abs_sub_le hh a1 a2
  · have hb1 := b1 j (mem_univ _)
    have hb2 := b2 j (mem_univ _)
    simp only [Fin.removeNth] at hb1 hb2
    exact int_eq_of_mem_Ico hh ⟨hb1.1, hb1.2⟩ ⟨hb2.1, hb2.2⟩

/-- Pointwise Cauchy–Schwarz over the overlapping prisms:
`‖𝓛_h J(x)‖² ≤ (n+1) Σ_f ‖𝓛_f J_f(x)‖²`. -/
theorem norm_interfaceLift_sq_le {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h)
    (F : Finset (Face n)) (J : Face n → (Fin n → ℝ) → E) (x : Fin (n + 1) → ℝ) :
    ‖interfaceLift h η F J x‖ ^ 2 ≤ (n + 1 : ℝ) * ∑ f ∈ F, ‖faceLift h η f (J f) x‖ ^ 2 := by
  classical
  set a : Face n → E := fun f => faceLift h η f (J f) x with ha
  set S := F.filter fun f => a f ≠ 0
  have hS : S.card ≤ n + 1 := by
    have : S.card ≤ (Finset.univ : Finset (Fin (n + 1))).card := by
      refine Finset.card_le_card_of_injOn Prod.fst (fun _ _ => Finset.mem_coe.2
        (Finset.mem_univ _)) ?_
      intro f hf f' hf' heq
      have hf1 := (Finset.mem_filter.1 hf).2
      have hf2 := (Finset.mem_filter.1 hf').2
      exact eq_of_faceLift_ne_zero hη hh heq hf1 hf2
    simpa using this
  have hsum : interfaceLift h η F J x = ∑ f ∈ S, a f := by
    rw [interfaceLift, Finset.sum_filter_ne_zero]
  have h1 : ‖∑ f ∈ S, a f‖ ≤ ∑ f ∈ S, ‖a f‖ := norm_sum_le _ _
  have h2 : (∑ f ∈ S, ‖a f‖) ^ 2 ≤ S.card * ∑ f ∈ S, ‖a f‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ f ∈ S, ‖a f‖ ^ 2 ≤ ∑ f ∈ F, ‖a f‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => sq_nonneg _
  have hS' : (S.card : ℝ) ≤ n + 1 := by exact_mod_cast hS
  rw [hsum]
  calc ‖∑ f ∈ S, a f‖ ^ 2 ≤ (∑ f ∈ S, ‖a f‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ S.card * ∑ f ∈ S, ‖a f‖ ^ 2 := h2
    _ ≤ (n + 1) * ∑ f ∈ F, ‖a f‖ ^ 2 :=
        mul_le_mul hS' h3 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

end Mesh

/-! ### The two bounds of `lem:supp-interface-lifting` -/

section Bounds

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem aestronglyMeasurable_faceLift {η : ℝ → ℝ} (hη : IsLiftingProfile η) (h : ℝ)
    (f : Face n) {J : (Fin n → ℝ) → E}
    (hJ : AEStronglyMeasurable J (volume.restrict (faceBox h f))) :
    AEStronglyMeasurable (faceLift h η f J) volume := by
  have hind : AEStronglyMeasurable ((faceBox h f).indicator J) volume :=
    (aestronglyMeasurable_indicator_iff (measurableSet_faceBox h f)).2 hJ
  exact (aestronglyMeasurable_normalLift (ν := volume) hη h (faceLevel h f) hind).comp_measurePreserving
    (measurePreserving_normalCoord f.1)

theorem indicator_enorm_sq {s : Set (Fin n → ℝ)} (J : (Fin n → ℝ) → E) :
    (fun y => ‖s.indicator J y‖ₑ ^ 2) = s.indicator fun y => ‖J y‖ₑ ^ 2 := by
  funext y
  by_cases hy : y ∈ s <;> simp [hy]

/-- Integration in the normal coordinate of one face:
`‖𝓛_f J_f‖²_{L²} = h⁻¹ ‖η‖²_{L²} ‖J_f‖²_{L²(f)}`. -/
theorem lintegral_faceLift_sq {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h)
    (f : Face n) {J : (Fin n → ℝ) → E}
    (hJ : AEStronglyMeasurable J (volume.restrict (faceBox h f))) :
    ∫⁻ x, ‖faceLift h η f J x‖ₑ ^ 2 =
      ENNReal.ofReal (h⁻¹ * ∫ s, η s ^ 2) * ∫⁻ y in faceBox h f, ‖J y‖ₑ ^ 2 := by
  have hind : AEStronglyMeasurable ((faceBox h f).indicator J) volume :=
    (aestronglyMeasurable_indicator_iff (measurableSet_faceBox h f)).2 hJ
  have hmp := measurePreserving_normalCoord (n := n) f.1
  rw [normalCoord_eq] at hmp
  have := hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
    (fun p => ‖normalLift h (faceLevel h f) η ((faceBox h f).indicator J) p‖ₑ ^ 2)
  simp only [faceLift, normalCoord_eq]
  rw [this, lintegral_normalLift_sq hη hh _ hind, indicator_enorm_sq,
    lintegral_indicator (measurableSet_faceBox h f)]

/-- **First bound of `eq:supp-interface-lifting-bounds`** (ENNReal form, no integrability
hypotheses): `‖𝓛_h J‖₂² ≤ (n+1) ‖η‖₂² Σ_f h⁻¹ ‖J_f‖²_{L²(f)}`. -/
theorem lintegral_interfaceLift_sq_le {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ}
    (hh : 0 < h) (F : Finset (Face n)) (J : Face n → (Fin n → ℝ) → E)
    (hJ : ∀ f ∈ F, AEStronglyMeasurable (J f) (volume.restrict (faceBox h f))) :
    ∫⁻ x, ‖interfaceLift h η F J x‖ₑ ^ 2 ≤
      ENNReal.ofReal ((n + 1) * ∫ s, η s ^ 2) *
        ∑ f ∈ F, ENNReal.ofReal h⁻¹ * ∫⁻ y in faceBox h f, ‖J f y‖ₑ ^ 2 := by
  have hpt : ∀ x, ‖interfaceLift h η F J x‖ₑ ^ 2 ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * ∑ f ∈ F, ‖faceLift h η f (J f) x‖ₑ ^ 2 := by
    intro x
    have h1 := norm_interfaceLift_sq_le hη hh F J x
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    have h2 : ∀ f ∈ F, ‖faceLift h η f (J f) x‖ₑ ^ 2 =
        ENNReal.ofReal (‖faceLift h η f (J f) x‖ ^ 2) := fun f _ => by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [Finset.sum_congr rfl h2, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by push_cast; exact h1)
  have hmeas : ∀ f ∈ F, AEMeasurable (fun x => ‖faceLift h η f (J f) x‖ₑ ^ 2) volume :=
    fun f hf => ((aestronglyMeasurable_faceLift hη h f (hJ f hf)).enorm.pow_const 2)
  calc ∫⁻ x, ‖interfaceLift h η F J x‖ₑ ^ 2
      ≤ ∫⁻ x, ((n + 1 : ℕ) : ℝ≥0∞) * ∑ f ∈ F, ‖faceLift h η f (J f) x‖ₑ ^ 2 :=
        lintegral_mono hpt
    _ = ((n + 1 : ℕ) : ℝ≥0∞) * ∑ f ∈ F, ∫⁻ x, ‖faceLift h η f (J f) x‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum' _ hmeas]
    _ = ((n + 1 : ℕ) : ℝ≥0∞) * ∑ f ∈ F, ENNReal.ofReal (h⁻¹ * ∫ s, η s ^ 2) *
          ∫⁻ y in faceBox h f, ‖J f y‖ₑ ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl fun f hf => lintegral_faceLift_sq hη hh f (hJ f hf)
    _ = ENNReal.ofReal ((n + 1) * ∫ s, η s ^ 2) *
          ∑ f ∈ F, ENNReal.ofReal h⁻¹ * ∫⁻ y in faceBox h f, ‖J f y‖ₑ ^ 2 := by
        have hn : ENNReal.ofReal ((n + 1) * ∫ s, η s ^ 2) =
            ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (∫ s, η s ^ 2) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl
        rw [hn, mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [ENNReal.ofReal_mul (inv_nonneg.2 hh.le)]
        ring

theorem lintegral_faceBox_eq_ofReal {h : ℝ} {f : Face n} {J : (Fin n → ℝ) → E}
    (hJ : MemLp J 2 (volume.restrict (faceBox h f))) :
    ∫⁻ y in faceBox h f, ‖J y‖ₑ ^ 2 = ENNReal.ofReal (∫ y in faceBox h f, ‖J y‖ ^ 2) := by
  have hi : Integrable (fun y => ‖J y‖ ^ 2) (volume.restrict (faceBox h f)) :=
    (hJ : MemLp J ((2 : ℕ) : ℝ≥0∞) _).integrable_norm_pow (by norm_num)
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)]
  congr 1
  funext y
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

theorem interfaceBudgetSq_nonneg {h : ℝ} (hh : 0 ≤ h) (F : Finset (Face n))
    (J : Face n → (Fin n → ℝ) → E) : 0 ≤ interfaceBudgetSq h F J :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (inv_nonneg.2 hh)
    (integral_nonneg fun _ => sq_nonneg _)

/-- **First bound of `eq:supp-interface-lifting-bounds`**: `‖𝓛_h J‖_{L²} ≤ C 𝒥_h` with
`C = ((n+1) ‖η‖²_{L²})^{1/2}` depending only on the dimension and the profile. -/
theorem eLpNorm_interfaceLift_le {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h)
    (F : Finset (Face n)) (J : Face n → (Fin n → ℝ) → E)
    (hJ : ∀ f ∈ F, MemLp (J f) 2 (volume.restrict (faceBox h f))) :
    eLpNorm (interfaceLift h η F J) 2 volume ≤
      ENNReal.ofReal (Real.sqrt ((n + 1) * ∫ s, η s ^ 2) *
        Real.sqrt (interfaceBudgetSq h F J)) := by
  have hle := lintegral_interfaceLift_sq_le hη hh F J fun f hf => (hJ f hf).1
  have hsum : ∑ f ∈ F, ENNReal.ofReal h⁻¹ * ∫⁻ y in faceBox h f, ‖J f y‖ₑ ^ 2 =
      ENNReal.ofReal (interfaceBudgetSq h F J) := by
    rw [interfaceBudgetSq, ENNReal.ofReal_sum_of_nonneg fun f _ => mul_nonneg
      (inv_nonneg.2 hh.le) (integral_nonneg fun _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [lintegral_faceBox_eq_ofReal (hJ f hf), ENNReal.ofReal_mul (inv_nonneg.2 hh.le)]
  rw [hsum, ← ENNReal.ofReal_mul (by positivity)] at hle
  have hB := interfaceBudgetSq_nonneg hh.le F J
  have hη2 : 0 ≤ ∫ s, η s ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc (∫⁻ x, ‖interfaceLift h η F J x‖ₑ ^ 2) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal ((n + 1) * (∫ s, η s ^ 2) * interfaceBudgetSq h F J)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt ((n + 1) * ∫ s, η s ^ 2) *
          Real.sqrt (interfaceBudgetSq h F J)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_mul
          (by positivity), Real.sqrt_eq_rpow]

/-- The integral of a test against one face lift, in normal coordinates. -/
theorem integral_smul_faceLift {η : ℝ → ℝ} (h : ℝ) (f : Face n) (J : (Fin n → ℝ) → E)
    (φ : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ x, φ x • faceLift h η f J x =
      ∫ p, φ (Fin.insertNth (α := fun _ => ℝ) f.1 p.1 p.2) •
        normalLift h (faceLevel h f) η ((faceBox h f).indicator J) p
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
  have hmp := measurePreserving_normalCoord (n := n) f.1
  rw [normalCoord_eq] at hmp
  rw [← hmp.integral_comp' (g := fun p => φ (Fin.insertNth (α := fun _ => ℝ) f.1 p.1 p.2) •
        normalLift h (faceLevel h f) η ((faceBox h f).indicator J) p)]
  congr 1
  funext x
  simp only [faceLift, normalCoord_eq]
  congr 2
  have := insertNth_normalCoord f.1 x
  rw [normalCoord_eq] at this
  exact this.symm

theorem integrable_smul_faceLift {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h)
    (f : Face n) {J : (Fin n → ℝ) → E} (hJ : IntegrableOn J (faceBox h f))
    {φ : (Fin (n + 1) → ℝ) → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ x, |φ x| ≤ M) :
    Integrable (fun x => φ x • faceLift h η f J x) := by
  have hmp := measurePreserving_normalCoord (n := n) f.1
  have hint := integrable_smul_normalLift (ν := volume) hη hh (faceLevel h f)
    (hJ.integrable_indicator (measurableSet_faceBox h f))
    (hφ.comp (measurable_insertNth f.1)) (fun p => hM _)
  have := (hmp.integrable_comp hint.aestronglyMeasurable).2 hint
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, faceLift]
  congr 2
  exact insertNth_normalCoord f.1 x

/-- Moving along the normal of a face changes a Lipschitz test by at most `L |t - c|`. -/
theorem abs_sub_insertNth_le {φ : (Fin (n + 1) → ℝ) → ℝ} {L : ℝ≥0} (hL : LipschitzWith L φ)
    (i : Fin (n + 1)) (t c : ℝ) (y : Fin n → ℝ) :
    |φ (Fin.insertNth (α := fun _ => ℝ) i t y) - φ (Fin.insertNth (α := fun _ => ℝ) i c y)| ≤
      L * |t - c| := by
  have h1 := hL.dist_le_mul (Fin.insertNth (α := fun _ => ℝ) i t y)
    (Fin.insertNth (α := fun _ => ℝ) i c y)
  have h2 : dist (Fin.insertNth (α := fun _ => ℝ) i t y)
      (Fin.insertNth (α := fun _ => ℝ) i c y) ≤ |t - c| := by
    refine (dist_pi_le_iff (abs_nonneg _)).2 fun m => ?_
    rcases Fin.eq_self_or_eq_succAbove i m with rfl | ⟨j, rfl⟩
    · simp [Real.dist_eq]
    · simp
  rw [Real.dist_eq] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h2 L.2)

/-- **Distributional error of one face lift**:
`‖⟨𝓛_f J_f - J_f δ_f, Φ⟩‖ ≤ (h/4) Lip(Φ) ‖J_f‖_{L¹(f)}`. -/
theorem norm_integral_faceLift_sub_le {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ}
    (hh : 0 < h) [CompleteSpace E] (f : Face n) {J : (Fin n → ℝ) → E}
    (hJ : IntegrableOn J (faceBox h f)) {φ : (Fin (n + 1) → ℝ) → ℝ} {M : ℝ}
    (hM : ∀ x, |φ x| ≤ M) {L : ℝ≥0} (hL : LipschitzWith L φ) :
    ‖(∫ x, φ x • faceLift h η f J x) - ∫ y in faceBox h f, φ (facePoint h f y) • J y‖ ≤
      h / 4 * L * ∫ y in faceBox h f, ‖J y‖ := by
  have hφ : Measurable φ := hL.continuous.measurable
  rw [integral_smul_faceLift]
  have key := norm_integral_normalLift_sub_le (ν := volume) hη hh (faceLevel h f)
    (hJ.integrable_indicator (measurableSet_faceBox h f))
    (hφ.comp (measurable_insertNth f.1)) (fun p => hM _) L.2
    (fun t y => abs_sub_insertNth_le hL f.1 t (faceLevel h f) y)
  have e1 : ∫ y, φ (Fin.insertNth (α := fun _ => ℝ) f.1 (faceLevel h f) y) •
      (faceBox h f).indicator J y = ∫ y in faceBox h f, φ (facePoint h f y) • J y := by
    rw [← integral_indicator (measurableSet_faceBox h f)]
    congr 1
    funext y
    by_cases hy : y ∈ faceBox h f <;> simp [hy, facePoint]
  have e2 : ∫ y, ‖(faceBox h f).indicator J y‖ = ∫ y in faceBox h f, ‖J y‖ := by
    rw [← integral_indicator (measurableSet_faceBox h f)]
    congr 1
    funext y
    by_cases hy : y ∈ faceBox h f <;> simp [hy]
  simp only [Function.comp_apply] at key
  rw [e1, e2] at key
  exact key

/-- **Distributional error of the interface lifting**:
`‖⟨𝓛_h J - Σ_f J_f δ_f, Φ⟩‖ ≤ (h/4) Lip(Φ) Σ_f ‖J_f‖_{L¹(f)}`. -/
theorem norm_integral_interfaceLift_sub_faceMeasure_le {η : ℝ → ℝ} (hη : IsLiftingProfile η)
    {h : ℝ} (hh : 0 < h) [CompleteSpace E] (F : Finset (Face n))
    (J : Face n → (Fin n → ℝ) → E) (hJ : ∀ f ∈ F, IntegrableOn (J f) (faceBox h f))
    {φ : (Fin (n + 1) → ℝ) → ℝ} {M : ℝ} (hM : ∀ x, |φ x| ≤ M) {L : ℝ≥0}
    (hL : LipschitzWith L φ) :
    ‖(∫ x, φ x • interfaceLift h η F J x) - faceMeasurePairing h F J φ‖ ≤
      h / 4 * L * ∑ f ∈ F, ∫ y in faceBox h f, ‖J f y‖ := by
  have hφ : Measurable φ := hL.continuous.measurable
  have hsplit : ∫ x, φ x • interfaceLift h η F J x = ∑ f ∈ F, ∫ x, φ x • faceLift h η f (J f) x := by
    simp only [interfaceLift, Finset.smul_sum]
    exact integral_finsetSum _ fun f hf => integrable_smul_faceLift hη hh f (hJ f hf) hφ hM
  rw [hsplit, faceMeasurePairing, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f hf => ?_)
  exact norm_integral_faceLift_sub_le hη hh f (hJ f hf) hM hL

/-- Cauchy–Schwarz on each face and over the faces:
`Σ_f ‖J_f‖_{L¹(f)} ≤ (#F h^{n+1})^{1/2} 𝒥_h`. -/
theorem sum_integral_norm_le_sqrt_mul_sqrt {h : ℝ} (hh : 0 < h) (F : Finset (Face n))
    (J : Face n → (Fin n → ℝ) → E)
    (hJ : ∀ f ∈ F, MemLp (J f) 2 (volume.restrict (faceBox h f))) :
    ∑ f ∈ F, ∫ y in faceBox h f, ‖J f y‖ ≤
      Real.sqrt (F.card * h ^ (n + 1)) * Real.sqrt (interfaceBudgetSq h F J) := by
  set I : Face n → ℝ := fun f => ∫ y in faceBox h f, ‖J f y‖ ^ 2 with hI
  have hI0 : ∀ f, 0 ≤ I f := fun f => integral_nonneg fun _ => sq_nonneg _
  -- Hölder on one face
  have hface : ∀ f ∈ F, ∫ y in faceBox h f, ‖J f y‖ ≤
      Real.sqrt (h ^ (n + 1)) * Real.sqrt (h⁻¹ * I f) := by
    intro f hf
    have : IsFiniteMeasure (volume.restrict (faceBox h f)) :=
      ⟨by rw [Measure.restrict_apply_univ, volume_faceBox hh.le]; exact ENNReal.ofReal_lt_top⟩
    have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
    have hmem1 : MemLp (fun _ => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict (faceBox h f)) :=
      memLp_const _
    have hmem2 : MemLp (fun y => ‖J f y‖) (ENNReal.ofReal 2) (volume.restrict (faceBox h f)) := by
      rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact (hJ f hf).norm
    have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
      (Eventually.of_forall fun _ => zero_le_one) (Eventually.of_forall fun _ => norm_nonneg _)
      hmem1 hmem2
    simp only [one_mul, integral_const, smul_eq_mul] at hH
    rw [Measure.real, Measure.restrict_apply_univ, volume_faceBox hh.le,
      ENNReal.toReal_ofReal (by positivity)] at hH
    have hrw : ∀ x : ℝ, 0 ≤ x → x ^ (1 / (2 : ℝ)) = Real.sqrt x := fun x _ =>
      (Real.sqrt_eq_rpow x).symm
    have hJ2 : ∫ y in faceBox h f, ‖J f y‖ ^ (2 : ℝ) = I f := by
      simp only [hI, Real.rpow_two]
    rw [hJ2, hrw _ (by positivity), hrw _ (hI0 f)] at hH
    refine hH.trans (le_of_eq ?_)
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
    ring
  -- Cauchy–Schwarz over the faces
  have hcs : ∑ f ∈ F, Real.sqrt (h⁻¹ * I f) ≤ Real.sqrt (F.card * ∑ f ∈ F, h⁻¹ * I f) := by
    apply Real.le_sqrt_of_sq_le
    have := sq_sum_le_card_mul_sum_sq (s := F) (f := fun f => Real.sqrt (h⁻¹ * I f))
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    exact Real.sq_sqrt (mul_nonneg (inv_nonneg.2 hh.le) (hI0 f))
  calc ∑ f ∈ F, ∫ y in faceBox h f, ‖J f y‖
      ≤ ∑ f ∈ F, Real.sqrt (h ^ (n + 1)) * Real.sqrt (h⁻¹ * I f) := Finset.sum_le_sum hface
    _ = Real.sqrt (h ^ (n + 1)) * ∑ f ∈ F, Real.sqrt (h⁻¹ * I f) := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt (h ^ (n + 1)) * Real.sqrt (F.card * ∑ f ∈ F, h⁻¹ * I f) :=
        mul_le_mul_of_nonneg_left hcs (Real.sqrt_nonneg _)
    _ = Real.sqrt (F.card * h ^ (n + 1)) * Real.sqrt (interfaceBudgetSq h F J) := by
        rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
        congr 1
        simp only [interfaceBudgetSq, hI]
        ring

/-- Distinct cells are disjoint. -/
theorem disjoint_cell {h : ℝ} (hh : 0 < h) {k k' : Fin (n + 1) → ℤ} (hk : k ≠ k') :
    Disjoint (cell h k) (cell h k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  apply hk
  funext m
  have h1 := hx m (mem_univ _)
  have h2 := hx' m (mem_univ _)
  exact int_eq_of_mem_Ico hh ⟨h1.1, h1.2⟩ ⟨h2.1, h2.2⟩

/-- **Face counting**: if the cells carrying the faces of `F` lie in `U`, then
`#F h^{n+1} ≤ (n+1) vol(U)`; i.e. there are `O_U(h^{-(n+1)})` faces, each of area `h^n`. -/
theorem card_mul_pow_le_volume {h : ℝ} (hh : 0 < h) (F : Finset (Face n))
    {U : Set (Fin (n + 1) → ℝ)} (hU : ∀ f ∈ F, cell h f.2 ⊆ U) :
    (F.card : ℝ≥0∞) * ENNReal.ofReal (h ^ (n + 1)) ≤ (n + 1 : ℕ) * volume U := by
  classical
  set G := F.image Prod.snd
  have hcard : F.card ≤ (n + 1) * G.card := by
    refine Finset.card_le_mul_card_image F (n + 1) fun k _ => ?_
    have : (F.filter fun f => f.2 = k).card ≤ (Finset.univ : Finset (Fin (n + 1))).card := by
      refine Finset.card_le_card_of_injOn Prod.fst (fun _ _ => Finset.mem_coe.2
        (Finset.mem_univ _)) ?_
      intro f hf f' hf' heq
      exact Prod.ext heq (((Finset.mem_filter.1 hf).2).trans ((Finset.mem_filter.1 hf').2).symm)
    simpa using this
  have hvol : (G.card : ℝ≥0∞) * ENNReal.ofReal (h ^ (n + 1)) ≤ volume U := by
    have hU' : (⋃ k ∈ G, cell h k) ⊆ U := by
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨k, hk, hxk⟩ := hx
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hk
      exact hU f hf hxk
    calc (G.card : ℝ≥0∞) * ENNReal.ofReal (h ^ (n + 1))
        = ∑ k ∈ G, volume (cell h k) := by
          rw [Finset.sum_congr rfl fun k _ => volume_cell hh.le k]; simp
      _ = volume (⋃ k ∈ G, cell h k) := by
          rw [measure_biUnion_finset (fun k _ k' _ hkk' => disjoint_cell hh hkk')
            fun k _ => measurableSet_cell h k]
      _ ≤ volume U := measure_mono hU'
  calc (F.card : ℝ≥0∞) * ENNReal.ofReal (h ^ (n + 1))
      ≤ ((n + 1) * G.card : ℕ) * ENNReal.ofReal (h ^ (n + 1)) := by
        gcongr
    _ = (n + 1 : ℕ) * ((G.card : ℝ≥0∞) * ENNReal.ofReal (h ^ (n + 1))) := by
        push_cast; ring
    _ ≤ (n + 1 : ℕ) * volume U := by gcongr

theorem card_mul_pow_le_volume_toReal {h : ℝ} (hh : 0 < h) (F : Finset (Face n))
    {U : Set (Fin (n + 1) → ℝ)} (hU : ∀ f ∈ F, cell h f.2 ⊆ U) (hUf : volume U ≠ ∞) :
    (F.card : ℝ) * h ^ (n + 1) ≤ (n + 1) * (volume U).toReal := by
  have := card_mul_pow_le_volume hh F hU
  have h2 := (ENNReal.toReal_le_toReal (by
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (by simp) hUf)).2 this
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_natCast, ENNReal.toReal_natCast] at h2
  push_cast at h2
  exact h2

/-- **`lem:supp-interface-lifting`** (`eq:supp-interface-lifting-bounds`).  On the uniform cubical
mesh of side `h > 0` in `ℝ^{n+1}`, let `F` be a finite family of faces whose cells lie in a set
`U` of finite volume (the compact subdomain together with its neighbouring cells), `J_f ∈ L²(f)`
face densities with values in a Banach space `E`, and `η` a lifting profile.  Then
1. `‖𝓛_h J‖_{L²} ≤ C 𝒥_h` with `C = ((n+1) ‖η‖²_{L²})^{1/2}` (dimension and `η` only);
2. for every bounded `L`-Lipschitz test `Φ` (e.g. smooth compactly supported, `L = ‖∇Φ‖_∞`),
   `‖⟨𝓛_h J - Σ_f J_f δ_f, Φ⟩‖ ≤ C_U h 𝒥_h L` with `C_U = ¼ ((n+1) vol U)^{1/2}`. -/
theorem interface_lifting_bounds [CompleteSpace E] {η : ℝ → ℝ} (hη : IsLiftingProfile η)
    {h : ℝ} (hh : 0 < h) (F : Finset (Face n)) (J : Face n → (Fin n → ℝ) → E)
    (hJ : ∀ f ∈ F, MemLp (J f) 2 (volume.restrict (faceBox h f)))
    {U : Set (Fin (n + 1) → ℝ)} (hU : ∀ f ∈ F, cell h f.2 ⊆ U) (hUf : volume U ≠ ∞) :
    eLpNorm (interfaceLift h η F J) 2 volume ≤
        ENNReal.ofReal (Real.sqrt ((n + 1) * ∫ s, η s ^ 2) *
          Real.sqrt (interfaceBudgetSq h F J)) ∧
      ∀ (φ : (Fin (n + 1) → ℝ) → ℝ) (M : ℝ), (∀ x, |φ x| ≤ M) → ∀ L : ℝ≥0,
        LipschitzWith L φ →
        ‖(∫ x, φ x • interfaceLift h η F J x) - faceMeasurePairing h F J φ‖ ≤
          (1 / 4 * Real.sqrt ((n + 1) * (volume U).toReal)) * h *
            Real.sqrt (interfaceBudgetSq h F J) * L := by
  refine ⟨eLpNorm_interfaceLift_le hη hh F J hJ, fun φ M hM L hL => ?_⟩
  have hJ1 : ∀ f ∈ F, IntegrableOn (J f) (faceBox h f) := fun f hf => by
    have : IsFiniteMeasure (volume.restrict (faceBox h f)) :=
      ⟨by rw [Measure.restrict_apply_univ, volume_faceBox hh.le]; exact ENNReal.ofReal_lt_top⟩
    exact (hJ f hf).integrable (by norm_num)
  have h1 := norm_integral_interfaceLift_sub_faceMeasure_le hη hh F J hJ1 hM hL
  have h2 := sum_integral_norm_le_sqrt_mul_sqrt hh F J hJ
  have h3 : Real.sqrt (F.card * h ^ (n + 1)) ≤ Real.sqrt ((n + 1) * (volume U).toReal) :=
    Real.sqrt_le_sqrt (card_mul_pow_le_volume_toReal hh F hU hUf)
  have hB := Real.sqrt_nonneg (interfaceBudgetSq h F J)
  calc ‖(∫ x, φ x • interfaceLift h η F J x) - faceMeasurePairing h F J φ‖
      ≤ h / 4 * L * ∑ f ∈ F, ∫ y in faceBox h f, ‖J f y‖ := h1
    _ ≤ h / 4 * L * (Real.sqrt ((n + 1) * (volume U).toReal) *
          Real.sqrt (interfaceBudgetSq h F J)) := by
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_right h3 hB)
    _ = (1 / 4 * Real.sqrt ((n + 1) * (volume U).toReal)) * h *
          Real.sqrt (interfaceBudgetSq h F J) * L := by ring

end Bounds

/-! ### Existence of smooth profiles and non-vacuity -/

/-- The manuscript's profile exists: a smooth `η ≥ 0` supported in `(-1/4, 1/4)` with integral
one (a normalized bump function). -/
theorem exists_smooth_liftingProfile :
    ∃ η : ℝ → ℝ, IsLiftingProfile η ∧ ContDiff ℝ (⊤ : ℕ∞) η ∧
      ∀ s, η s ≠ 0 → |s| < 1 / 4 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  have hsupp : ∀ s, b.normed volume s ≠ 0 → |s| < 1 / 4 := fun s hs => by
    have : s ∈ Function.support (b.normed volume) := hs
    rw [b.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at this
    exact this
  refine ⟨b.normed volume, ⟨b.continuous_normed, b.nonneg_normed, fun s hs => (hsupp s hs).le,
    b.integral_normed⟩, b.contDiff_normed, hsupp⟩

/-- Non-vacuity of `interface_lifting_bounds`: one face of the unit mesh of `ℝ⁴` carrying the
constant density `1`, with `U` its cell. -/
example : ∃ η : ℝ → ℝ, IsLiftingProfile η ∧
    eLpNorm (interfaceLift 1 η {((0 : Fin 4), (0 : Fin 4 → ℤ))} fun _ _ => (1 : ℝ)) 2 volume ≤
      ENNReal.ofReal (Real.sqrt ((3 + 1) * ∫ s, η s ^ 2) *
        Real.sqrt (interfaceBudgetSq 1 {((0 : Fin 4), (0 : Fin 4 → ℤ))} fun _ _ => (1 : ℝ))) := by
  obtain ⟨η, hη, -, -⟩ := exists_smooth_liftingProfile
  refine ⟨η, hη, ?_⟩
  have hfin : ∀ f : Face 3, IsFiniteMeasure (volume.restrict (faceBox 1 f)) := fun f =>
    ⟨by rw [Measure.restrict_apply_univ, volume_faceBox zero_le_one]; exact ENNReal.ofReal_lt_top⟩
  have := (interface_lifting_bounds hη one_pos {((0 : Fin 4), (0 : Fin 4 → ℤ))}
    (fun _ _ => (1 : ℝ)) (fun f _ => by have := hfin f; exact memLp_const _)
    (U := cell 1 0) (fun f hf => by rw [Finset.mem_singleton.1 hf])
    (by rw [volume_cell zero_le_one]; exact ENNReal.ofReal_ne_top)).1
  simpa using this

end RenewalGeometry.InterfaceLifting
