/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.InformationGeometry
import NCG.Grand.FiniteGibbsActionGap

/-!
# The affine information projection of a finite exponential family

Exact formalization for `thm:SMYM-affine-information-projection` (CY.13b–CY.13f).

* **CY.13b** (`hasDerivAt_linePsi`, `hasDerivAt_lineM`, `directional_variance_pos`):
  along every direction `u`, the log-partition `Ψ_g` has first derivative the tilted
  mean pairing and second derivative the tilted variance of `⟪u, X⟫`, strictly
  positive whenever `u` separates two response points;
* **CY.13d** (`kl_pythagoras`): the exact information Pythagoras
  `D(q‖g) = D(q‖q_{g,λ}) + D(q_{g,λ}‖g)` over the affine fibre, hence `q_{g,λ}` is
  the unique minimum-relative-entropy comparator (`unique_min`);
* **CY.13e** (`kl_eq_action`): `𝓘_g(θ) = ⟪λ_θ, θ⟫ - Ψ_g(λ_θ)`;
* **CY.13f** (`bregman_exact`, `bregman_nonneg`): the exact Bregman expansion
  `𝓘_g(θ') - 𝓘_g(θ) - ⟪λ_θ, θ' - θ⟫ = D(q_{g,θ'}‖q_{g,θ}) ≥ 0`, so `λ_θ` is the
  exact (sub)gradient of the response-moment action, strictly convex across distinct
  comparators.

The formalization parametrizes the fibre by the natural parameter `λ` (CY.13c's
analytic bijection `∇Ψ_g : V_Γ → ri conv{x_i}` supplies `λ_θ` in the manuscript and
is not re-derived here). The 1D derivative layer (`hasDerivAt_igZ`,
`hasDerivAt_igPsi`, `hasDerivAt_igM`, `igVar_eq_sum_sq`) extends
`NCG.InformationGeometry`; the KL layer reuses `NCG.finiteKL` and Gibbs' equality
case from `NCG.FiniteGibbsActionGap`.
-/

open Finset
open scoped RealInnerProductSpace

namespace NCG
namespace AffineProjection

/-! ### 1D derivative layer for the tilted family of `NCG.InformationGeometry` -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Tilted variance of the observable `f`. -/
noncomputable def igVar (p₀ f : ι → ℝ) (θ : ℝ) : ℝ :=
  (∑ a, igP p₀ f θ a * f a ^ 2) - igM p₀ f θ ^ 2

omit [Nonempty ι] in
theorem hasDerivAt_igZ (p₀ f : ι → ℝ) (θ : ℝ) :
    HasDerivAt (igZ p₀ f) (∑ a, p₀ a * f a * Real.exp (θ * f a)) θ := by
  have h : ∀ a ∈ Finset.univ, HasDerivAt (fun t => p₀ a * Real.exp (t * f a))
      (p₀ a * (Real.exp (θ * f a) * f a)) θ := by
    intro a _
    have h1 : HasDerivAt (fun t : ℝ => t * f a) (f a) θ := hasDerivAt_mul_const (f a)
    exact ((Real.hasDerivAt_exp (θ * f a)).comp θ h1).const_mul (p₀ a)
  have hval : ∑ a, p₀ a * f a * Real.exp (θ * f a)
      = ∑ a, p₀ a * (Real.exp (θ * f a) * f a) :=
    Finset.sum_congr rfl fun a _ => by ring
  rw [hval]
  exact HasDerivAt.fun_sum h

theorem hasDerivAt_igPsi (p₀ f : ι → ℝ) (hp : ∀ a, 0 < p₀ a) (θ : ℝ) :
    HasDerivAt (igPsi p₀ f) (igM p₀ f θ) θ := by
  have hZ : 0 < igZ p₀ f θ :=
    Finset.sum_pos (fun a _ => mul_pos (hp a) (Real.exp_pos _)) Finset.univ_nonempty
  have h1 := (hasDerivAt_igZ p₀ f θ).log hZ.ne'
  have hM : (∑ a, p₀ a * f a * Real.exp (θ * f a)) / igZ p₀ f θ = igM p₀ f θ := by
    rw [igM, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [igP]
    ring
  rw [hM] at h1
  exact h1

theorem hasDerivAt_igM (p₀ f : ι → ℝ) (hp : ∀ a, 0 < p₀ a) (θ : ℝ) :
    HasDerivAt (igM p₀ f) (igVar p₀ f θ) θ := by
  have hZ : ∀ t, 0 < igZ p₀ f t := fun t =>
    Finset.sum_pos (fun a _ => mul_pos (hp a) (Real.exp_pos _)) Finset.univ_nonempty
  have hMdef : ∀ t, igM p₀ f t
      = (∑ a, p₀ a * f a * Real.exp (t * f a)) / igZ p₀ f t := by
    intro t
    rw [igM, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [igP]
    ring
  have hN2 : HasDerivAt (fun t => ∑ a, p₀ a * f a * Real.exp (t * f a))
      (∑ a, p₀ a * f a ^ 2 * Real.exp (θ * f a)) θ := by
    have h : ∀ a ∈ Finset.univ, HasDerivAt (fun t => p₀ a * f a * Real.exp (t * f a))
        (p₀ a * f a * (Real.exp (θ * f a) * f a)) θ := by
      intro a _
      have h1 : HasDerivAt (fun t : ℝ => t * f a) (f a) θ := hasDerivAt_mul_const (f a)
      exact ((Real.hasDerivAt_exp (θ * f a)).comp θ h1).const_mul (p₀ a * f a)
    have hval2 : ∑ a, p₀ a * f a ^ 2 * Real.exp (θ * f a)
        = ∑ a, p₀ a * f a * (Real.exp (θ * f a) * f a) :=
      Finset.sum_congr rfl fun a _ => by ring
    rw [hval2]
    exact HasDerivAt.fun_sum h
  have hdiv := hN2.div (hasDerivAt_igZ p₀ f θ) (hZ θ).ne'
  have hfun : HasDerivAt (igM p₀ f)
      (((∑ a, p₀ a * f a ^ 2 * Real.exp (θ * f a)) * igZ p₀ f θ -
          (∑ a, p₀ a * f a * Real.exp (θ * f a)) *
            (∑ a, p₀ a * f a * Real.exp (θ * f a))) / igZ p₀ f θ ^ 2) θ :=
    hdiv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hMdef t)
  have hval : ((∑ a, p₀ a * f a ^ 2 * Real.exp (θ * f a)) * igZ p₀ f θ -
      (∑ a, p₀ a * f a * Real.exp (θ * f a)) *
        (∑ a, p₀ a * f a * Real.exp (θ * f a))) / igZ p₀ f θ ^ 2
      = igVar p₀ f θ := by
    have h2 : ∑ a, igP p₀ f θ a * f a ^ 2
        = (∑ a, p₀ a * f a ^ 2 * Real.exp (θ * f a)) / igZ p₀ f θ := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [igP]
      ring
    have generic : ∀ A N Z : ℝ, Z ≠ 0 →
        (A * Z - N * N) / Z ^ 2 = A / Z - (N / Z) ^ 2 := by
      intro A N Z hZ0
      field_simp
    rw [igVar, h2, hMdef θ]
    exact generic _ _ _ (hZ θ).ne'
  rw [hval] at hfun
  exact hfun

theorem igVar_eq_sum_sq (p₀ f : ι → ℝ) (hp : ∀ a, 0 < p₀ a) (θ : ℝ) :
    igVar p₀ f θ = ∑ a, igP p₀ f θ a * (f a - igM p₀ f θ) ^ 2 := by
  have hPsum : ∑ a, igP p₀ f θ a = 1 :=
    (primitive_information_geometry p₀ f hp).2.2.1 θ
  have hM : igM p₀ f θ = ∑ a, igP p₀ f θ a * f a := rfl
  have hexp : ∀ a, igP p₀ f θ a * (f a - igM p₀ f θ) ^ 2
      = igP p₀ f θ a * f a ^ 2
        - 2 * igM p₀ f θ * (igP p₀ f θ a * f a)
        + igM p₀ f θ ^ 2 * igP p₀ f θ a := fun a => by ring
  rw [Finset.sum_congr rfl fun a _ => hexp a, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hPsum, ← hM, igVar]
  ring

theorem igVar_nonneg (p₀ f : ι → ℝ) (hp : ∀ a, 0 < p₀ a) (θ : ℝ) :
    0 ≤ igVar p₀ f θ := by
  rw [igVar_eq_sum_sq p₀ f hp θ]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg ((primitive_information_geometry p₀ f hp).2.1 θ a).le (sq_nonneg _)

theorem igVar_pos (p₀ f : ι → ℝ) (hp : ∀ a, 0 < p₀ a) (θ : ℝ)
    {a b : ι} (hab : f a ≠ f b) : 0 < igVar p₀ f θ := by
  have hPpos := (primitive_information_geometry p₀ f hp).2.1
  rw [igVar_eq_sum_sq p₀ f hp θ]
  have hnn : ∀ c ∈ Finset.univ, 0 ≤ igP p₀ f θ c * (f c - igM p₀ f θ) ^ 2 :=
    fun c _ => mul_nonneg (hPpos θ c).le (sq_nonneg _)
  have hsq : ∀ c : ι, f c ≠ igM p₀ f θ → 0 < igP p₀ f θ c * (f c - igM p₀ f θ) ^ 2 := by
    intro c hc
    refine mul_pos (hPpos θ c) ?_
    exact lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hc)))
  rcases ne_or_eq (f a) (igM p₀ f θ) with h | h
  · exact Finset.sum_pos' hnn ⟨a, Finset.mem_univ a, hsq a h⟩
  · have hb : f b ≠ igM p₀ f θ := by
      rw [← h]
      exact hab.symm
    exact Finset.sum_pos' hnn ⟨b, Finset.mem_univ b, hsq b hb⟩

/-! ### The multivariate affine exponential family (CY.13a) -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Partition sum of the affine family. -/
noncomputable def expZ (g : ι → ℝ) (X : ι → E) (l : E) : ℝ :=
  ∑ i, g i * Real.exp ⟪l, X i⟫

/-- Log-partition function `Ψ_g`. -/
noncomputable def expPsi (g : ι → ℝ) (X : ι → E) (l : E) : ℝ :=
  Real.log (expZ g X l)

/-- The tilted comparator `q_{g,λ}`. -/
noncomputable def expQ (g : ι → ℝ) (X : ι → E) (l : E) (i : ι) : ℝ :=
  g i * Real.exp ⟪l, X i⟫ / expZ g X l

theorem expZ_pos (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l : E) :
    0 < expZ g X l :=
  Finset.sum_pos (fun i _ => mul_pos (hg i) (Real.exp_pos _)) Finset.univ_nonempty

theorem expQ_pos (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l : E) (i : ι) :
    0 < expQ g X l i :=
  div_pos (mul_pos (hg i) (Real.exp_pos _)) (expZ_pos g X hg l)

theorem expQ_sum (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l : E) :
    ∑ i, expQ g X l i = 1 := by
  have h : ∑ i, expQ g X l i = (∑ i, g i * Real.exp ⟪l, X i⟫) / expZ g X l := by
    rw [Finset.sum_div]
    rfl
  rw [h]
  exact div_self (expZ_pos g X hg l).ne'

theorem log_expQ_div (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l : E) (i : ι) :
    Real.log (expQ g X l i / g i) = ⟪l, X i⟫ - expPsi g X l := by
  have hZ := expZ_pos g X hg l
  have hnum : expQ g X l i / g i = Real.exp ⟪l, X i⟫ / expZ g X l := by
    rw [expQ, div_div, mul_comm (expZ g X l) (g i),
      mul_div_mul_left _ _ (hg i).ne']
  rw [hnum, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp, expPsi]

theorem selector_cross (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l : E)
    (p : ι → ℝ) (hpsum : ∑ i, p i = 1) :
    ∑ i, p i * Real.log (expQ g X l i / g i)
      = ⟪l, ∑ i, p i • X i⟫ - expPsi g X l := by
  have h1 : ∀ i, p i * Real.log (expQ g X l i / g i)
      = p i * ⟪l, X i⟫ - p i * expPsi g X l := by
    intro i
    rw [log_expQ_div g X hg l i]
    ring
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hpsum, one_mul, inner_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_right]

/-- The KL shift identity: the divergence gap to the family member depends only on
the affine mean of the selector. -/
theorem kl_shift (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l : E)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hrsum : ∑ i, r i = 1) :
    finiteKL r g - finiteKL r (expQ g X l)
      = ⟪l, ∑ i, r i • X i⟫ - expPsi g X l := by
  have hq : ∀ i, 0 < expQ g X l i := expQ_pos g X hg l
  have h1 : ∀ i, r i * Real.log (r i / g i) - r i * Real.log (r i / expQ g X l i)
      = r i * Real.log (expQ g X l i / g i) := by
    intro i
    rw [Real.log_div (hr i).ne' (hg i).ne', Real.log_div (hr i).ne' (hq i).ne',
      Real.log_div (hq i).ne' (hg i).ne']
    ring
  rw [finiteKL, finiteKL, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun i _ => h1 i]
  exact selector_cross g X hg l r hrsum

theorem finiteKL_self_expQ (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l : E) :
    finiteKL (expQ g X l) (expQ g X l) = 0 := by
  have h : ∀ i, expQ g X l i / expQ g X l i = 1 :=
    fun i => div_self (expQ_pos g X hg l i).ne'
  rw [finiteKL]
  simp [h]

/-- **CY.13e**: the response-moment action identity
`𝓘_g(θ) = D(q_{g,λ}‖g) = ⟪λ, θ⟫ - Ψ_g(λ)`. -/
theorem kl_eq_action (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l : E) :
    finiteKL (expQ g X l) g
      = ⟪l, ∑ i, expQ g X l i • X i⟫ - expPsi g X l := by
  have h2 := kl_shift g X hg l (expQ g X l) (expQ_pos g X hg l) (expQ_sum g X hg l)
  have hself := finiteKL_self_expQ g X hg l
  linarith

/-- **CY.13d**: the exact information Pythagoras over the affine fibre. -/
theorem kl_pythagoras (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l : E)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (hmean : ∑ i, p i • X i = ∑ i, expQ g X l i • X i) :
    finiteKL p g = finiteKL p (expQ g X l) + finiteKL (expQ g X l) g := by
  have h1 := kl_shift g X hg l p hp hpsum
  have h2 := kl_eq_action g X hg l
  rw [hmean] at h1
  linarith

/-- The comparator is the unique minimum-relative-entropy element of its affine
fibre. -/
theorem unique_min (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l : E)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (hmean : ∑ i, p i • X i = ∑ i, expQ g X l i • X i) :
    finiteKL (expQ g X l) g ≤ finiteKL p g
      ∧ (finiteKL p g = finiteKL (expQ g X l) g ↔ p = expQ g X l) := by
  have hpy := kl_pythagoras g X hg l p hp hpsum hmean
  have hgibbs := NCG.finiteKL_nonneg_eq_iff p (expQ g X l) hp (expQ_pos g X hg l)
    hpsum (expQ_sum g X hg l)
  refine ⟨by linarith [hgibbs.1], ?_, ?_⟩
  · intro h
    exact hgibbs.2.mp (by linarith)
  · intro h
    rw [h]

/-- **CY.13f, exact Bregman expansion**: `λ` is the exact (sub)gradient of the
response-moment action, with Bregman remainder the KL divergence inside the
family. -/
theorem bregman_exact (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l l' : E) :
    finiteKL (expQ g X l') g - finiteKL (expQ g X l) g
        - ⟪l, (∑ i, expQ g X l' i • X i) - ∑ i, expQ g X l i • X i⟫
      = finiteKL (expQ g X l') (expQ g X l) := by
  have h1 := kl_shift g X hg l (expQ g X l') (expQ_pos g X hg l') (expQ_sum g X hg l')
  have h2 := kl_eq_action g X hg l
  rw [inner_sub_right]
  linarith

/-- The Bregman remainder is nonnegative, vanishing only on the same comparator:
`𝓘_g` is strictly convex across distinct family members. -/
theorem bregman_nonneg (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i) (l l' : E) :
    0 ≤ finiteKL (expQ g X l') (expQ g X l)
      ∧ (finiteKL (expQ g X l') (expQ g X l) = 0 ↔ expQ g X l' = expQ g X l) :=
  NCG.finiteKL_nonneg_eq_iff (expQ g X l') (expQ g X l) (expQ_pos g X hg l')
    (expQ_pos g X hg l) (expQ_sum g X hg l') (expQ_sum g X hg l)

/-! ### CY.13b: directional calculus of `Ψ_g` along `V_Γ` -/

omit [Nonempty ι] in
theorem expZ_line (g : ι → ℝ) (X : ι → E) (l u : E) (t : ℝ) :
    expZ g X (l + t • u)
      = igZ (fun i => g i * Real.exp ⟪l, X i⟫) (fun i => ⟪u, X i⟫) t := by
  rw [expZ, igZ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_add_left, real_inner_smul_left, Real.exp_add]
  ring

omit [Nonempty ι] in
theorem expPsi_line (g : ι → ℝ) (X : ι → E) (l u : E) (t : ℝ) :
    expPsi g X (l + t • u)
      = igPsi (fun i => g i * Real.exp ⟪l, X i⟫) (fun i => ⟪u, X i⟫) t := by
  rw [expPsi, igPsi, expZ_line]

omit [Nonempty ι] in
theorem expQ_line (g : ι → ℝ) (X : ι → E) (l u : E) (t : ℝ) (i : ι) :
    expQ g X (l + t • u) i
      = igP (fun i => g i * Real.exp ⟪l, X i⟫) (fun i => ⟪u, X i⟫) t i := by
  rw [expQ, igP, expZ_line]
  congr 1
  rw [inner_add_left, real_inner_smul_left, Real.exp_add]
  ring

omit [Nonempty ι] in
theorem lineM_eq (g : ι → ℝ) (X : ι → E) (l u : E) (t : ℝ) :
    ∑ i, expQ g X (l + t • u) i * ⟪u, X i⟫
      = igM (fun i => g i * Real.exp ⟪l, X i⟫) (fun i => ⟪u, X i⟫) t := by
  rw [igM]
  exact Finset.sum_congr rfl fun i _ => by rw [expQ_line g X l u t i]

/-- **CY.13b, first derivative**: `∂_t Ψ_g(λ + t u) = E_{q_{g,λ+tu}}⟪u, X⟫`. -/
theorem hasDerivAt_linePsi (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i)
    (l u : E) (t : ℝ) :
    HasDerivAt (fun s => expPsi g X (l + s • u))
      (∑ i, expQ g X (l + t • u) i * ⟪u, X i⟫) t := by
  have hp' : ∀ i, 0 < g i * Real.exp ⟪l, X i⟫ :=
    fun i => mul_pos (hg i) (Real.exp_pos _)
  have h1 := hasDerivAt_igPsi (fun i => g i * Real.exp ⟪l, X i⟫)
    (fun i => ⟪u, X i⟫) hp' t
  have h3 : HasDerivAt (fun s => expPsi g X (l + s • u))
      (igM (fun i => g i * Real.exp ⟪l, X i⟫) (fun i => ⟪u, X i⟫) t) t :=
    h1.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => expPsi_line g X l u s)
  rw [lineM_eq g X l u t]
  exact h3

/-- **CY.13b, second derivative**: `∂²_t Ψ_g(λ + t u)` is the tilted variance of
`⟪u, X⟫` along the line. -/
theorem hasDerivAt_lineM (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i)
    (l u : E) (t : ℝ) :
    HasDerivAt (fun s => ∑ i, expQ g X (l + s • u) i * ⟪u, X i⟫)
      (igVar (fun i => g i * Real.exp ⟪l, X i⟫) (fun i => ⟪u, X i⟫) t) t := by
  have hp' : ∀ i, 0 < g i * Real.exp ⟪l, X i⟫ :=
    fun i => mul_pos (hg i) (Real.exp_pos _)
  have h1 := hasDerivAt_igM (fun i => g i * Real.exp ⟪l, X i⟫)
    (fun i => ⟪u, X i⟫) hp' t
  exact h1.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => lineM_eq g X l u s)

/-- **CY.13b, strict positivity on `V_Γ`**: the directional entropy Hessian is
strictly positive along any direction separating two response points. -/
theorem directional_variance_pos (g : ι → ℝ) (X : ι → E) (hg : ∀ i, 0 < g i)
    (l u : E) (hsep : ∃ a b, ⟪u, X a⟫ ≠ ⟪u, X b⟫) :
    0 < ∑ i, expQ g X l i
      * (⟪u, X i⟫ - ∑ j, expQ g X l j * ⟪u, X j⟫) ^ 2 := by
  obtain ⟨a, b, hab⟩ := hsep
  have hp' : ∀ i, 0 < g i * Real.exp ⟪l, X i⟫ :=
    fun i => mul_pos (hg i) (Real.exp_pos _)
  have h0 : l + (0 : ℝ) • u = l := by rw [zero_smul, add_zero]
  have hQ : ∀ i, expQ g X l i
      = igP (fun i => g i * Real.exp ⟪l, X i⟫) (fun i => ⟪u, X i⟫) 0 i := by
    intro i
    calc expQ g X l i = expQ g X (l + (0 : ℝ) • u) i := by rw [h0]
      _ = igP (fun i => g i * Real.exp ⟪l, X i⟫) (fun i => ⟪u, X i⟫) 0 i :=
        expQ_line g X l u 0 i
  have hM' : ∑ j, expQ g X l j * ⟪u, X j⟫
      = igM (fun i => g i * Real.exp ⟪l, X i⟫) (fun i => ⟪u, X i⟫) 0 := by
    rw [igM]
    exact Finset.sum_congr rfl fun j _ => by rw [hQ j]
  have hkey : ∑ i, expQ g X l i
      * (⟪u, X i⟫ - ∑ j, expQ g X l j * ⟪u, X j⟫) ^ 2
      = igVar (fun i => g i * Real.exp ⟪l, X i⟫) (fun i => ⟪u, X i⟫) 0 := by
    rw [igVar_eq_sum_sq _ _ hp' 0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hQ i, hM']
  rw [hkey]
  exact igVar_pos _ _ hp' 0 hab

/-- **Bundle for `thm:SMYM-affine-information-projection`** (CY.13b, CY.13d–CY.13f),
parametrized by the natural parameter `λ` of the fibre (CY.13c's bijection
`∇Ψ_g : V_Γ → ri conv{x_i}` supplies `λ_θ` and is not re-derived). -/
theorem smym_affine_information_projection (g : ι → ℝ) (X : ι → E)
    (hg : ∀ i, 0 < g i) (l : E) :
    -- CY.13b: directional first and second derivative of Ψ_g, strict positivity
    (∀ u : E, ∀ t : ℝ, HasDerivAt (fun s => expPsi g X (l + s • u))
        (∑ i, expQ g X (l + t • u) i * ⟪u, X i⟫) t) ∧
    (∀ u : E, (∃ a b, ⟪u, X a⟫ ≠ ⟪u, X b⟫) →
        0 < ∑ i, expQ g X l i
          * (⟪u, X i⟫ - ∑ j, expQ g X l j * ⟪u, X j⟫) ^ 2) ∧
    -- CY.13d: Pythagoras and unique minimality over the affine fibre
    (∀ p : ι → ℝ, (∀ i, 0 < p i) → ∑ i, p i = 1 →
      ∑ i, p i • X i = ∑ i, expQ g X l i • X i →
      finiteKL p g = finiteKL p (expQ g X l) + finiteKL (expQ g X l) g
        ∧ finiteKL (expQ g X l) g ≤ finiteKL p g
        ∧ (finiteKL p g = finiteKL (expQ g X l) g ↔ p = expQ g X l)) ∧
    -- CY.13e: the response-moment action identity
    (finiteKL (expQ g X l) g
      = ⟪l, ∑ i, expQ g X l i • X i⟫ - expPsi g X l) ∧
    -- CY.13f: exact Bregman gradient expansion with KL remainder
    (∀ l' : E, finiteKL (expQ g X l') g - finiteKL (expQ g X l) g
        - ⟪l, (∑ i, expQ g X l' i • X i) - ∑ i, expQ g X l i • X i⟫
      = finiteKL (expQ g X l') (expQ g X l)
        ∧ 0 ≤ finiteKL (expQ g X l') (expQ g X l)) := by
  refine ⟨fun u t => hasDerivAt_linePsi g X hg l u t,
    fun u hsep => directional_variance_pos g X hg l u hsep,
    fun p hp hpsum hmean => ⟨kl_pythagoras g X hg l p hp hpsum hmean,
      (unique_min g X hg l p hp hpsum hmean).1,
      (unique_min g X hg l p hp hpsum hmean).2⟩,
    kl_eq_action g X hg l,
    fun l' => ⟨bregman_exact g X hg l l', (bregman_nonneg g X hg l l').1⟩⟩

end AffineProjection
end NCG
