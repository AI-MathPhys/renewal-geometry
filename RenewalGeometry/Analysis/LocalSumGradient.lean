/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Site-wise gradients of lattice sums of local functions

Let `S` be a finite additive group (a periodic lattice), `W` a real normed space (the value of
a field at one site), and equip fields `A : S → W` with the sup (Pi) norm.  Fix finitely many
offsets `o : Fin k → S` and local functions `φ x : (Fin k → W) → ℝ`, one per site.  The
*local sum*
`localSum o φ A = ∑ x, φ x (A (x + o 0), …, A (x + o (k-1)))`
is the shape of the connection remainder of a finite lattice action.  This file computes its
derivative, its partial derivative at a single site, and proves **cutoff-uniform** Lipschitz
bounds for the site-wise derivative in the sup norm: the constant `k * L` depends only on the
number of offsets and on the Lipschitz constant of the local derivatives, never on `card S`.

* `loc o x : (S → W) →L[ℝ] (Fin k → W)`, `loc o x A ℓ = A (x + o ℓ)`, with `‖loc o x‖ ≤ 1`.
* `hasFDerivAt_localSum`: the derivative is `∑ x, (fderiv ℝ (φ x) (loc o x A)).comp (loc o x)`.
* `fderiv_localSum_single`, `fderiv_localSum_comp_single`: the partial derivative at site `y`
  is `∑ ℓ, ∂_ℓ φ (y - o ℓ)` (valid also when offsets coincide).
* `norm_fderiv_localSum_single_sub_le`: Lipschitz bound `k * L * ‖A - Ã‖` for the site-wise
  derivative; `norm_fderiv_localSum_single_le`: the bound `k * M`.
* `siteGrad`, `grad`: the gradient field `y ↦ w⁻¹ • rieszInv (∂_y f A)` for a fixed linear
  identification `rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W` and a weight `w`; `grad_lipschitz`
  (sup-norm Lipschitz bound `w⁻¹ * ‖rieszInv‖ * k * L`), `fderiv_eq_sum_siteGrad` /
  `fderiv_localSum_eq_sum_grad` (the gradient represents the derivative in the weighted
  pairing `w * ∑ y, pair (grad A y) (δ y)`).
* Several term types: `localSum_add`, `siteGrad_add`, `siteGrad_sum`, and
  `norm_siteGrad_sum_localSum_sub_le` for a finite family of local sums with different
  `k`, `o`, `φ` (constant `w⁻¹ * ‖rieszInv‖ * ∑ i, k i * L i`).
-/

namespace RenewalGeometry.LocalSumGradient

open Finset

noncomputable section

variable {S : Type*} [Fintype S] [AddCommGroup S] [DecidableEq S]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {k : ℕ}

/-! ### The localisation map -/

/-- The localisation map at site `x`: `loc o x A = (A (x + o ℓ))_ℓ`. -/
def loc (o : Fin k → S) (x : S) : (S → W) →L[ℝ] (Fin k → W) :=
  ContinuousLinearMap.pi fun ℓ => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => W) (x + o ℓ)

omit [Fintype S] [DecidableEq S] in
/-- Evaluation of the localisation map. -/
@[simp] theorem loc_apply (o : Fin k → S) (x : S) (A : S → W) (ℓ : Fin k) :
    loc o x A ℓ = A (x + o ℓ) := rfl

omit [DecidableEq S] in
/-- The localisation map does not increase the sup norm. -/
theorem norm_loc_apply_le (o : Fin k → S) (x : S) (A : S → W) : ‖loc o x A‖ ≤ ‖A‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg A)).2 fun ℓ => norm_le_pi_norm A (x + o ℓ)

omit [DecidableEq S] in
/-- The localisation map has operator norm at most one. -/
theorem norm_loc_le (o : Fin k → S) (x : S) :
    ‖(loc o x : (S → W) →L[ℝ] (Fin k → W))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => by
    simpa using norm_loc_apply_le o x A

omit [Fintype S] in
/-- Localisation of a single-site field: only the offsets hitting `y` contribute. -/
theorem loc_single (o : Fin k → S) (x y : S) (v : W) :
    loc o x (Pi.single y v : S → W) =
      ∑ ℓ, if x = y - o ℓ then (Pi.single ℓ v : Fin k → W) else 0 := by
  funext m
  rw [Finset.sum_apply, Finset.sum_eq_single m]
  · by_cases h : x = y - o m
    · simp [h]
    · have h' : x + o m ≠ y := fun h' => h (eq_sub_of_add_eq h')
      simp [h, h']
  · intro ℓ _ hℓ
    split_ifs <;> simp [Ne.symm hℓ]
  · simp

/-! ### Local sums and their derivatives -/

/-- The lattice sum of local functions `∑ x, φ x (loc o x A)`. -/
def localSum (o : Fin k → S) (φ : S → (Fin k → W) → ℝ) (A : S → W) : ℝ :=
  ∑ x, φ x (loc o x A)

omit [DecidableEq S] in
/-- Local sums are additive in the local functions. -/
theorem localSum_add (o : Fin k → S) (φ ψ : S → (Fin k → W) → ℝ) :
    localSum o (φ + ψ) = localSum o φ + localSum o ψ := by
  funext A
  simp [localSum, Finset.sum_add_distrib]

omit [DecidableEq S] in
/-- The derivative of a local sum. -/
theorem hasFDerivAt_localSum (o : Fin k → S) (φ : S → (Fin k → W) → ℝ) (A : S → W)
    (hφ : ∀ x, DifferentiableAt ℝ (φ x) (loc o x A)) :
    HasFDerivAt (localSum o φ) (∑ x, (fderiv ℝ (φ x) (loc o x A)).comp (loc o x)) A := by
  have h : ∀ x ∈ (Finset.univ : Finset S), HasFDerivAt (fun B => φ x (loc o x B))
      ((fderiv ℝ (φ x) (loc o x A)).comp (loc o x)) A :=
    fun x _ => (hφ x).hasFDerivAt.comp A (loc (W := W) o x).hasFDerivAt
  exact HasFDerivAt.fun_sum h

omit [DecidableEq S] in
/-- A local sum is differentiable where its local functions are. -/
theorem differentiableAt_localSum (o : Fin k → S) (φ : S → (Fin k → W) → ℝ) (A : S → W)
    (hφ : ∀ x, DifferentiableAt ℝ (φ x) (loc o x A)) :
    DifferentiableAt ℝ (localSum o φ) A :=
  (hasFDerivAt_localSum o φ A hφ).differentiableAt

/-- The derivative of a local sum applied to a single-site variation `Pi.single y v`. -/
theorem fderiv_localSum_single (o : Fin k → S) (φ : S → (Fin k → W) → ℝ) (A : S → W)
    (hφ : ∀ x, DifferentiableAt ℝ (φ x) (loc o x A)) (y : S) (v : W) :
    fderiv ℝ (localSum o φ) A (Pi.single y v) =
      ∑ ℓ, fderiv ℝ (φ (y - o ℓ)) (loc o (y - o ℓ) A) (Pi.single ℓ v) := by
  rw [(hasFDerivAt_localSum o φ A hφ).fderiv]
  simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply, loc_single,
    map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have : ∀ x, fderiv ℝ (φ x) (loc o x A) (if x = y - o ℓ then (Pi.single ℓ v : Fin k → W) else 0)
      = if x = y - o ℓ then fderiv ℝ (φ x) (loc o x A) (Pi.single ℓ v) else 0 := by
    intro x; split_ifs <;> simp
  simp_rw [this]
  simp

/-- The site-`y` partial derivative of a local sum, as a continuous linear map on `W`. -/
theorem fderiv_localSum_comp_single (o : Fin k → S) (φ : S → (Fin k → W) → ℝ) (A : S → W)
    (hφ : ∀ x, DifferentiableAt ℝ (φ x) (loc o x A)) (y : S) :
    (fderiv ℝ (localSum o φ) A).comp (ContinuousLinearMap.single ℝ (fun _ : S => W) y) =
      ∑ ℓ, (fderiv ℝ (φ (y - o ℓ)) (loc o (y - o ℓ) A)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin k => W) ℓ) := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply,
    fderiv_localSum_single o φ A hφ y v, _root_.sum_apply]
  rfl

/-- The coordinate injection `W → (ι → W)` has operator norm at most one. -/
theorem norm_single_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    ‖ContinuousLinearMap.single ℝ (fun _ : ι => W) i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simp [Pi.norm_single]

/-- Sup bound for the site-wise derivative: `k` times a bound on the local derivatives. -/
theorem norm_fderiv_localSum_single_le (o : Fin k → S) (φ : S → (Fin k → W) → ℝ) (A : S → W)
    (hφ : ∀ x, DifferentiableAt ℝ (φ x) (loc o x A)) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ (φ x) (loc o x A)‖ ≤ M) (y : S) :
    ‖(fderiv ℝ (localSum o φ) A).comp (ContinuousLinearMap.single ℝ (fun _ : S => W) y)‖ ≤
      k * M := by
  rw [fderiv_localSum_comp_single o φ A hφ y]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ ℓ : Fin k, ‖(fderiv ℝ (φ (y - o ℓ)) (loc o (y - o ℓ) A)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin k => W) ℓ)‖ ≤ M := fun ℓ =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans <| by
      have h0 := hM (y - o ℓ)
      have h1 := norm_single_le_one (W := W) ℓ
      have h2 : 0 ≤ M := (norm_nonneg _).trans h0
      nlinarith [norm_nonneg (fderiv ℝ (φ (y - o ℓ)) (loc o (y - o ℓ) A))]
  refine (Finset.sum_le_sum fun ℓ _ => hterm ℓ).trans ?_
  simp

/-- **Cutoff-uniform Lipschitz bound** for the site-wise derivative of a local sum: if the
local derivatives are `L`-Lipschitz on the ball of radius `R`, then so is every site-wise
derivative, with constant `k * L` (independent of `card S`). -/
theorem norm_fderiv_localSum_single_sub_le (o : Fin k → S) (φ : S → (Fin k → W) → ℝ)
    {R L : ℝ} (hL : 0 ≤ L)
    (hdiff : ∀ x (a : Fin k → W), ‖a‖ ≤ R → DifferentiableAt ℝ (φ x) a)
    (hlip : ∀ x (a ã : Fin k → W), ‖a‖ ≤ R → ‖ã‖ ≤ R →
      ‖fderiv ℝ (φ x) a - fderiv ℝ (φ x) ã‖ ≤ L * ‖a - ã‖)
    {A Ã : S → W} (hA : ‖A‖ ≤ R) (hÃ : ‖Ã‖ ≤ R) (y : S) :
    ‖(fderiv ℝ (localSum o φ) A).comp (ContinuousLinearMap.single ℝ (fun _ : S => W) y) -
        (fderiv ℝ (localSum o φ) Ã).comp (ContinuousLinearMap.single ℝ (fun _ : S => W) y)‖ ≤
      k * L * ‖A - Ã‖ := by
  have hlA : ∀ x, ‖loc o x A‖ ≤ R := fun x => (norm_loc_apply_le o x A).trans hA
  have hlÃ : ∀ x, ‖loc o x Ã‖ ≤ R := fun x => (norm_loc_apply_le o x Ã).trans hÃ
  rw [fderiv_localSum_comp_single o φ A (fun x => hdiff x _ (hlA x)) y,
    fderiv_localSum_comp_single o φ Ã (fun x => hdiff x _ (hlÃ x)) y,
    ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ ℓ : Fin k,
      ‖(fderiv ℝ (φ (y - o ℓ)) (loc o (y - o ℓ) A)).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin k => W) ℓ) -
        (fderiv ℝ (φ (y - o ℓ)) (loc o (y - o ℓ) Ã)).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin k => W) ℓ)‖ ≤ L * ‖A - Ã‖ := by
    intro ℓ
    rw [← ContinuousLinearMap.sub_comp]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h0 := hlip (y - o ℓ) _ _ (hlA (y - o ℓ)) (hlÃ (y - o ℓ))
    have h1 := norm_single_le_one (W := W) ℓ
    have h2 : ‖loc o (y - o ℓ) A - loc o (y - o ℓ) Ã‖ ≤ ‖A - Ã‖ := by
      rw [← map_sub]; exact norm_loc_apply_le _ _ _
    have h3 := norm_nonneg (fderiv ℝ (φ (y - o ℓ)) (loc o (y - o ℓ) A) -
      fderiv ℝ (φ (y - o ℓ)) (loc o (y - o ℓ) Ã))
    calc _ ≤ ‖fderiv ℝ (φ (y - o ℓ)) (loc o (y - o ℓ) A) -
          fderiv ℝ (φ (y - o ℓ)) (loc o (y - o ℓ) Ã)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 h3
      _ ≤ L * ‖A - Ã‖ := by
          rw [mul_one]; exact h0.trans (mul_le_mul_of_nonneg_left h2 hL)
  refine (Finset.sum_le_sum fun ℓ _ => hterm ℓ).trans ?_
  simp [mul_assoc]

/-! ### Gradient fields -/

/-- The site-wise gradient field of a function `f` of the field: at site `y`, the partial
derivative `∂_y f A ∈ W →L[ℝ] ℝ`, identified with a vector by `rieszInv` and divided by the
weight `w`. -/
def siteGrad (rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W) (w : ℝ) (f : (S → W) → ℝ) (A : S → W) :
    S → W :=
  fun y => w⁻¹ • rieszInv ((fderiv ℝ f A).comp (ContinuousLinearMap.single ℝ (fun _ : S => W) y))

/-- The gradient field of a local sum. -/
def grad (o : Fin k → S) (φ : S → (Fin k → W) → ℝ) (rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W)
    (w : ℝ) (A : S → W) : S → W :=
  siteGrad rieszInv w (localSum o φ) A

/-- Unfolding the gradient field of a local sum. -/
theorem grad_apply (o : Fin k → S) (φ : S → (Fin k → W) → ℝ)
    (rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W) (w : ℝ) (A : S → W) (y : S) :
    grad o φ rieszInv w A y = w⁻¹ • rieszInv ((fderiv ℝ (localSum o φ) A).comp
      (ContinuousLinearMap.single ℝ (fun _ : S => W) y)) := rfl

omit [AddCommGroup S] in
/-- Sup-norm Lipschitz transfer from site-wise derivatives to the gradient field. -/
theorem norm_siteGrad_sub_le (rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W) {w : ℝ} (hw : 0 < w)
    (f : (S → W) → ℝ) (A Ã : S → W) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ y, ‖(fderiv ℝ f A).comp (ContinuousLinearMap.single ℝ (fun _ : S => W) y) -
        (fderiv ℝ f Ã).comp (ContinuousLinearMap.single ℝ (fun _ : S => W) y)‖ ≤ C) :
    ‖siteGrad rieszInv w f A - siteGrad rieszInv w f Ã‖ ≤ w⁻¹ * ‖rieszInv‖ * C := by
  have hw' : 0 ≤ w⁻¹ := inv_nonneg.2 hw.le
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun y => ?_
  simp only [Pi.sub_apply, siteGrad, ← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hw', mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hw'
  exact (rieszInv.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h y) (norm_nonneg _))

/-- **Cutoff-uniform Lipschitz bound for the gradient field** of a local sum, in the sup norm:
`‖grad A - grad Ã‖ ≤ w⁻¹ * ‖rieszInv‖ * k * L * ‖A - Ã‖`. -/
theorem grad_lipschitz (o : Fin k → S) (φ : S → (Fin k → W) → ℝ)
    (rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W) {w : ℝ} (hw : 0 < w)
    {R L : ℝ} (hL : 0 ≤ L)
    (hdiff : ∀ x (a : Fin k → W), ‖a‖ ≤ R → DifferentiableAt ℝ (φ x) a)
    (hlip : ∀ x (a ã : Fin k → W), ‖a‖ ≤ R → ‖ã‖ ≤ R →
      ‖fderiv ℝ (φ x) a - fderiv ℝ (φ x) ã‖ ≤ L * ‖a - ã‖)
    {A Ã : S → W} (hA : ‖A‖ ≤ R) (hÃ : ‖Ã‖ ≤ R) :
    ‖grad o φ rieszInv w A - grad o φ rieszInv w Ã‖ ≤
      w⁻¹ * ‖rieszInv‖ * k * L * ‖A - Ã‖ := by
  have := norm_siteGrad_sub_le rieszInv hw (localSum o φ) A Ã (C := k * L * ‖A - Ã‖)
    (by positivity) fun y => norm_fderiv_localSum_single_sub_le o φ hL hdiff hlip hA hÃ y
  simpa [grad, mul_assoc] using this

omit [AddCommGroup S] in
/-- The gradient field represents the derivative in the weighted pairing:
`fderiv ℝ f A δ = w * ∑ y, pair (siteGrad f A y) (δ y)` whenever `pair (rieszInv ℓ) v = ℓ v`.
No differentiability hypothesis is needed. -/
theorem fderiv_eq_sum_siteGrad (rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W) {w : ℝ} (hw : w ≠ 0)
    (pair : W →L[ℝ] W →L[ℝ] ℝ) (hpair : ∀ ℓ v, pair (rieszInv ℓ) v = ℓ v)
    (f : (S → W) → ℝ) (A δ : S → W) :
    fderiv ℝ f A δ = w * ∑ y, pair (siteGrad rieszInv w f A y) (δ y) := by
  simp only [siteGrad, map_smul, smul_apply, hpair,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, smul_eq_mul,
    ← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hw, one_mul]
  rw [← map_sum, Finset.univ_sum_single]

/-- The gradient field of a local sum represents its derivative in the weighted pairing. -/
theorem fderiv_localSum_eq_sum_grad (o : Fin k → S) (φ : S → (Fin k → W) → ℝ)
    (rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W) {w : ℝ} (hw : w ≠ 0)
    (pair : W →L[ℝ] W →L[ℝ] ℝ) (hpair : ∀ ℓ v, pair (rieszInv ℓ) v = ℓ v) (A δ : S → W) :
    fderiv ℝ (localSum o φ) A δ = w * ∑ y, pair (grad o φ rieszInv w A y) (δ y) :=
  fderiv_eq_sum_siteGrad rieszInv hw pair hpair _ A δ

/-! ### Combining several term types -/

/-- Precomposition distributes over finite sums of continuous linear maps. -/
theorem sum_comp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ι : Type*} (s : Finset ι) (L : ι → F →L[ℝ] G) (M : E →L[ℝ] F) :
    (∑ i ∈ s, L i).comp M = ∑ i ∈ s, (L i).comp M :=
  ContinuousLinearMap.ext fun v => by simp [_root_.sum_apply]

set_option linter.unusedFintypeInType false in
omit [AddCommGroup S] in
/-- The gradient field is additive on functions differentiable at the base point. -/
theorem siteGrad_add (rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W) (w : ℝ) {f g : (S → W) → ℝ}
    {A : S → W} (hf : DifferentiableAt ℝ f A) (hg : DifferentiableAt ℝ g A) :
    siteGrad rieszInv w (f + g) A = siteGrad rieszInv w f A + siteGrad rieszInv w g A := by
  funext y
  simp [siteGrad, fderiv_add hf hg, ContinuousLinearMap.add_comp, smul_add]

set_option linter.unusedFintypeInType false in
omit [AddCommGroup S] in
/-- The gradient field of a finite sum of functions differentiable at the base point. -/
theorem siteGrad_sum (rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W) (w : ℝ) {ι : Type*} (s : Finset ι)
    {f : ι → (S → W) → ℝ} {A : S → W} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) A) :
    siteGrad rieszInv w (fun B => ∑ i ∈ s, f i B) A = ∑ i ∈ s, siteGrad rieszInv w (f i) A := by
  funext y
  simp [siteGrad, fderiv_fun_sum hf, sum_comp, Finset.smul_sum, Finset.sum_apply]

/-- The gradient field of a sum of two local sums (possibly with different offsets). -/
theorem grad_add {k' : ℕ} (o : Fin k → S) (φ : S → (Fin k → W) → ℝ)
    (o' : Fin k' → S) (φ' : S → (Fin k' → W) → ℝ) (rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W) (w : ℝ)
    (A : S → W) (hφ : ∀ x, DifferentiableAt ℝ (φ x) (loc o x A))
    (hφ' : ∀ x, DifferentiableAt ℝ (φ' x) (loc o' x A)) :
    siteGrad rieszInv w (localSum o φ + localSum o' φ') A =
      grad o φ rieszInv w A + grad o' φ' rieszInv w A :=
  siteGrad_add rieszInv w (differentiableAt_localSum o φ A hφ)
    (differentiableAt_localSum o' φ' A hφ')

/-- **Cutoff-uniform Lipschitz bound for several term types**: for a finite family of local
sums with offsets `o i : Fin (k i) → S` and local functions `φ i`, each with `L i`-Lipschitz
local derivatives on the ball of radius `R`, the gradient field of the total is Lipschitz in
the sup norm with constant `w⁻¹ * ‖rieszInv‖ * ∑ i, k i * L i`. -/
theorem norm_siteGrad_sum_localSum_sub_le {ι : Type*} [Fintype ι] {k : ι → ℕ}
    (o : ∀ i, Fin (k i) → S) (φ : ∀ i, S → (Fin (k i) → W) → ℝ)
    (rieszInv : (W →L[ℝ] ℝ) →L[ℝ] W) {w : ℝ} (hw : 0 < w) {R : ℝ} {L : ι → ℝ}
    (hL : ∀ i, 0 ≤ L i)
    (hdiff : ∀ i x (a : Fin (k i) → W), ‖a‖ ≤ R → DifferentiableAt ℝ (φ i x) a)
    (hlip : ∀ i x (a ã : Fin (k i) → W), ‖a‖ ≤ R → ‖ã‖ ≤ R →
      ‖fderiv ℝ (φ i x) a - fderiv ℝ (φ i x) ã‖ ≤ L i * ‖a - ã‖)
    {A Ã : S → W} (hA : ‖A‖ ≤ R) (hÃ : ‖Ã‖ ≤ R) :
    ‖siteGrad rieszInv w (fun B => ∑ i, localSum (o i) (φ i) B) A -
        siteGrad rieszInv w (fun B => ∑ i, localSum (o i) (φ i) B) Ã‖ ≤
      w⁻¹ * ‖rieszInv‖ * ((∑ i, k i * L i) * ‖A - Ã‖) := by
  have hdA : ∀ i ∈ (Finset.univ : Finset ι), DifferentiableAt ℝ (localSum (o i) (φ i)) A :=
    fun i _ => differentiableAt_localSum _ _ _ fun x =>
      hdiff i x _ ((norm_loc_apply_le _ _ _).trans hA)
  have hdÃ : ∀ i ∈ (Finset.univ : Finset ι), DifferentiableAt ℝ (localSum (o i) (φ i)) Ã :=
    fun i _ => differentiableAt_localSum _ _ _ fun x =>
      hdiff i x _ ((norm_loc_apply_le _ _ _).trans hÃ)
  refine norm_siteGrad_sub_le rieszInv hw _ A Ã ?_ fun y => ?_
  · exact mul_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hL i))
      (norm_nonneg _)
  rw [fderiv_fun_sum hdA, fderiv_fun_sum hdÃ, sum_comp, sum_comp, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact norm_fderiv_localSum_single_sub_le (o i) (φ i) (hL i) (hdiff i) (hlip i) hA hÃ y

end

end RenewalGeometry.LocalSumGradient
