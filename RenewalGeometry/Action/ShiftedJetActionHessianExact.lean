/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniform upper Hessian scale of a shifted-first-jet lattice action
  (`lem:native-action-Hessian`, Einstein–Standard-Model action-closure manuscript)

On the periodic grid `Grid n = Fin 4 → ZMod n` with mesh `h`, a field
`y : Grid n → V` has normalized forward differences
`δ⁺_μ y (x) = (y(x + e_μ) - y(x))/h` (`fwdDiff`), mass norm
`‖u‖²_{0,h} = h⁴ Σ_x ‖u(x)‖²` (`massNormSq`, `eq:prefix-mass`) and first norm
`‖u‖²_{1,h} = ‖u‖²_{0,h} + Σ_μ ‖δ⁺_μ u‖²_{0,h}` (`firstNormSq`).

A *shifted-first-jet action* (the normal form of
`lem:native-firstjet-normal-form`, `eq:native-firstjet-normal-form`) is
`𝒜_h(y) = h⁴ Σ_x F(Ξ_x y)`, where the stencil
`Ξ_x y = ((y(x + σ i))_i, (δ⁺_μ y(x + σ i))_{i,μ})` collects a fixed finite
family of shifted values and normalized first differences (`stencil`, a
continuous linear map), and `F` is a `C²` density.

Proved here, with constants depending only on the stencil size `card ι` and
on a bound `M` for the Hessian of `F` along the record (never on `h` or on the
number of nodes):

* `iteratedFDeriv_action`: the exact chain-rule formula
  `D²𝒜_h(y)[u,v] = h⁴ Σ_x D²F(Ξ_x y)[Ξ_x u, Ξ_x v]`;
* `abs_iteratedFDeriv_action_le` (`eq:action-Hessian-bilinear`):
  `|D²𝒜_h(y)[u,v]| ≤ M · card ι · ‖u‖_{1,h} ‖v‖_{1,h}`;
* `massNormSq_fwdDiff_le`: the inverse estimate `‖δ⁺_μ u‖_{0,h} ≤ 2 h⁻¹ ‖u‖_{0,h}`;
* `abs_iteratedFDeriv_action_le_mass` (`eq:action-Hessian-scale`):
  `|D²𝒜_h(y)[u,v]| ≤ 17 M · card ι · h⁻² ‖u‖_{0,h} ‖v‖_{0,h}` for `0 < h ≤ 1`,
  i.e. the mass-norm operator norm of the Hessian is at most `K₀ h⁻²`;
* `abs_action_sub_le` (`eq:action-span`): the oscillation of `𝒜_h` over a
  set on which the density is bounded by `B` is at most `2B · h⁴ n⁴`.
-/

open Finset

namespace RenewalGeometry
namespace ShiftedJetAction

/-- The periodic four-dimensional grid with `n` nodes per direction. -/
abbrev Grid (n : ℕ) := Fin 4 → ZMod n

variable {n : ℕ} [NeZero n]

/-- The lattice unit vector in direction `μ`. -/
def unitVec (n : ℕ) (μ : Fin 4) : Grid n := Pi.single μ 1

/-- The normalized forward difference `δ⁺_μ u (x) = (u(x + e_μ) - u(x))/h`. -/
noncomputable def fwdDiff {V : Type*} [AddCommGroup V] [Module ℝ V] (h : ℝ) (μ : Fin 4)
    (u : Grid n → V) (x : Grid n) : V :=
  h⁻¹ • (u (x + unitVec n μ) - u x)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {ι : Type*} [Fintype ι]

/-- The squared mass norm `‖u‖²_{0,h} = h⁴ Σ_x ‖u(x)‖²` (`eq:prefix-mass`). -/
noncomputable def massNormSq (h : ℝ) (u : Grid n → V) : ℝ := h ^ 4 * ∑ x, ‖u x‖ ^ 2

/-- The squared first norm `‖u‖²_{1,h} = ‖u‖²_{0,h} + Σ_μ ‖δ⁺_μ u‖²_{0,h}`. -/
noncomputable def firstNormSq (h : ℝ) (u : Grid n → V) : ℝ :=
  massNormSq h u + ∑ μ : Fin 4, massNormSq h (fwdDiff h μ u)

theorem massNormSq_nonneg (h : ℝ) (u : Grid n → V) : 0 ≤ massNormSq h u := by
  unfold massNormSq
  positivity

theorem firstNormSq_nonneg (h : ℝ) (u : Grid n → V) : 0 ≤ firstNormSq h u := by
  unfold firstNormSq
  have := massNormSq_nonneg h u
  have : 0 ≤ ∑ μ : Fin 4, massNormSq h (fwdDiff h μ u) :=
    sum_nonneg fun μ _ => massNormSq_nonneg h _
  linarith

/-- Translation invariance of grid sums. -/
theorem sum_translate (g : Grid n → ℝ) (a : Grid n) : ∑ x, g (x + a) = ∑ x, g x :=
  Equiv.sum_comp (Equiv.addRight a) g

/-- The inverse estimate `‖δ⁺_μ u‖²_{0,h} ≤ 4 h⁻² ‖u‖²_{0,h}`. -/
theorem massNormSq_fwdDiff_le (h : ℝ) (μ : Fin 4) (u : Grid n → V) :
    massNormSq h (fwdDiff h μ u) ≤ 4 * h⁻¹ ^ 2 * massNormSq h u := by
  unfold massNormSq fwdDiff
  have hpt : ∀ x, ‖h⁻¹ • (u (x + unitVec n μ) - u x)‖ ^ 2 ≤
      h⁻¹ ^ 2 * (2 * (‖u (x + unitVec n μ)‖ ^ 2 + ‖u x‖ ^ 2)) := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    gcongr
    have := norm_sub_le (u (x + unitVec n μ)) (u x)
    nlinarith [norm_nonneg (u (x + unitVec n μ)), norm_nonneg (u x),
      sq_nonneg (‖u (x + unitVec n μ)‖ - ‖u x‖), norm_nonneg (u (x + unitVec n μ) - u x)]
  calc h ^ 4 * ∑ x, ‖h⁻¹ • (u (x + unitVec n μ) - u x)‖ ^ 2
      ≤ h ^ 4 * ∑ x, h⁻¹ ^ 2 * (2 * (‖u (x + unitVec n μ)‖ ^ 2 + ‖u x‖ ^ 2)) := by
        gcongr with x _
        exact hpt x
    _ = h ^ 4 * (h⁻¹ ^ 2 * (2 * (∑ x, ‖u (x + unitVec n μ)‖ ^ 2 + ∑ x, ‖u x‖ ^ 2))) := by
        rw [← mul_sum, ← mul_sum, sum_add_distrib]
    _ = 4 * h⁻¹ ^ 2 * (h ^ 4 * ∑ x, ‖u x‖ ^ 2) := by
        rw [sum_translate (fun x => ‖u x‖ ^ 2) (unitVec n μ)]
        ring

/-- `‖u‖²_{1,h} ≤ 17 h⁻² ‖u‖²_{0,h}` for `0 < h ≤ 1`. -/
theorem firstNormSq_le {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (u : Grid n → V) :
    firstNormSq h u ≤ 17 * h⁻¹ ^ 2 * massNormSq h u := by
  unfold firstNormSq
  have hsum : ∑ μ : Fin 4, massNormSq h (fwdDiff h μ u) ≤
      ∑ _μ : Fin 4, 4 * h⁻¹ ^ 2 * massNormSq h u :=
    sum_le_sum fun μ _ => massNormSq_fwdDiff_le h μ u
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hm := massNormSq_nonneg h u
  have hinv : 1 ≤ h⁻¹ ^ 2 := by
    have : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
    nlinarith
  push_cast at hsum
  nlinarith

/-! ### The stencil map and the shifted-first-jet action -/

/-- The stencil `Ξ_x u = ((u(x + σ i))_i, (δ⁺_μ u (x + σ i))_{i,μ})` of shifted values
and normalized first differences, as a continuous linear map of the field `u`. -/
noncomputable def stencil (h : ℝ) (σ : ι → Grid n) (x : Grid n) :
    (Grid n → V) →L[ℝ] (ι → V) × (ι × Fin 4 → V) :=
  (ContinuousLinearMap.pi fun i =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Grid n => V) (x + σ i)).prod
    (ContinuousLinearMap.pi fun p : ι × Fin 4 =>
      h⁻¹ • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Grid n => V)
          (x + σ p.1 + unitVec n p.2) -
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Grid n => V) (x + σ p.1)))

theorem stencil_apply (h : ℝ) (σ : ι → Grid n) (x : Grid n) (u : Grid n → V) :
    stencil h σ x u = (fun i => u (x + σ i), fun p => fwdDiff h p.2 u (x + σ p.1)) := by
  ext <;> simp [stencil, fwdDiff]

/-- The shifted-first-jet action `𝒜_h(y) = h⁴ Σ_x F(Ξ_x y)`
(`eq:native-firstjet-normal-form`, bulk term). -/
noncomputable def action (F : (ι → V) × (ι × Fin 4 → V) → ℝ) (h : ℝ) (σ : ι → Grid n)
    (y : Grid n → V) : ℝ :=
  h ^ 4 * ∑ x, F (stencil h σ x y)

theorem stencil_contDiff (h : ℝ) (σ : ι → Grid n) (x : Grid n) :
    ContDiff ℝ 2 (stencil (V := V) h σ x) :=
  ContinuousLinearMap.contDiff (n := 2) _

variable {F : (ι → V) × (ι × Fin 4 → V) → ℝ} {h : ℝ} {σ : ι → Grid n}

theorem contDiff_action (hF : ContDiff ℝ 2 F) : ContDiff ℝ 2 (action F h σ) := by
  unfold action
  exact contDiff_const.mul (ContDiff.sum fun x _ => hF.comp (stencil_contDiff h σ x))

/-- Exact chain rule: `D²𝒜_h(y)[u,v] = h⁴ Σ_x D²F(Ξ_x y)[Ξ_x u, Ξ_x v]`. -/
theorem iteratedFDeriv_action (hF : ContDiff ℝ 2 F) (y u v : Grid n → V) :
    iteratedFDeriv ℝ 2 (action F h σ) y ![u, v] =
      h ^ 4 * ∑ x, iteratedFDeriv ℝ 2 F (stencil h σ x y)
        ![stencil h σ x u, stencil h σ x v] := by
  have hsum : ContDiff ℝ 2 (fun y : Grid n → V => ∑ x, F (stencil h σ x y)) :=
    ContDiff.sum fun x _ => hF.comp (stencil_contDiff h σ x)
  have e1 : action F h σ = fun y => (h ^ 4) • (∑ x, F (stencil h σ x y)) := by
    funext y
    simp [action]
  rw [e1, iteratedFDeriv_const_smul_apply' hsum.contDiffAt,
    smul_apply, smul_eq_mul]
  congr 1
  have e3 : iteratedFDeriv ℝ 2 (fun y : Grid n → V => ∑ x, F (stencil h σ x y)) y =
      ∑ x, iteratedFDeriv ℝ 2 (F ∘ stencil h σ x) y := by
    have := congrFun (iteratedFDeriv_sum (𝕜 := ℝ) (f := fun x => F ∘ stencil h σ x)
      (u := univ) (i := 2) (fun x _ => hF.comp (stencil_contDiff h σ x))) y
    rw [Finset.sum_apply] at this
    exact this
  rw [e3, _root_.sum_apply]
  refine sum_congr rfl fun x _ => ?_
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hF _ le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The squared Euclidean size of the stencil values. -/
noncomputable def stencilSq (h : ℝ) (σ : ι → Grid n) (x : Grid n) (u : Grid n → V) : ℝ :=
  ∑ i, ‖u (x + σ i)‖ ^ 2 + ∑ p : ι × Fin 4, ‖fwdDiff h p.2 u (x + σ p.1)‖ ^ 2

theorem stencilSq_nonneg (h : ℝ) (σ : ι → Grid n) (x : Grid n) (u : Grid n → V) :
    0 ≤ stencilSq h σ x u := by
  unfold stencilSq
  positivity

/-- The (sup-)norm of the stencil is controlled by its Euclidean size. -/
theorem norm_stencil_le (h : ℝ) (σ : ι → Grid n) (x : Grid n) (u : Grid n → V) :
    ‖stencil h σ x u‖ ≤ Real.sqrt (stencilSq h σ x u) := by
  have hS := stencilSq_nonneg h σ x u
  have ha : ‖fun i => u (x + σ i)‖ ≤ Real.sqrt (stencilSq h σ x u) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.le_sqrt (norm_nonneg _) hS]
    unfold stencilSq
    have this : ‖u (x + σ i)‖ ^ 2 ≤ ∑ j, ‖u (x + σ j)‖ ^ 2 :=
      single_le_sum (f := fun i => ‖u (x + σ i)‖ ^ 2) (fun j _ => by positivity) (mem_univ i)
    have h2 : 0 ≤ ∑ p : ι × Fin 4, ‖fwdDiff h p.2 u (x + σ p.1)‖ ^ 2 := by positivity
    linarith
  have hb : ‖fun p : ι × Fin 4 => fwdDiff h p.2 u (x + σ p.1)‖ ≤
      Real.sqrt (stencilSq h σ x u) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro p
    rw [Real.le_sqrt (norm_nonneg _) hS]
    unfold stencilSq
    have this : ‖fwdDiff h p.2 u (x + σ p.1)‖ ^ 2 ≤
        ∑ q : ι × Fin 4, ‖fwdDiff h q.2 u (x + σ q.1)‖ ^ 2 :=
      single_le_sum (f := fun p : ι × Fin 4 => ‖fwdDiff h p.2 u (x + σ p.1)‖ ^ 2)
        (fun j _ => by positivity) (mem_univ p)
    have h2 : 0 ≤ ∑ i, ‖u (x + σ i)‖ ^ 2 := by positivity
    linarith
  rw [stencil_apply]
  exact (le_of_eq (Prod.norm_def _)).trans (max_le ha hb)

/-- Translation invariance: `Σ_x ‖Ξ_x u‖²_{Eucl} = card ι · h⁻⁴ ‖u‖²_{1,h}`. -/
theorem sum_stencilSq (hh : h ≠ 0) (σ : ι → Grid n) (u : Grid n → V) :
    ∑ x, stencilSq h σ x u = (Fintype.card ι : ℝ) * (h ^ 4)⁻¹ * firstNormSq h u := by
  have h1 : ∀ i, ∑ x, ‖u (x + σ i)‖ ^ 2 = ∑ x, ‖u x‖ ^ 2 := fun i =>
    sum_translate (fun z => ‖u z‖ ^ 2) (σ i)
  have h2 : ∀ p : ι × Fin 4, ∑ x, ‖fwdDiff h p.2 u (x + σ p.1)‖ ^ 2 =
      ∑ x, ‖fwdDiff h p.2 u x‖ ^ 2 := fun p =>
    sum_translate (fun z => ‖fwdDiff h p.2 u z‖ ^ 2) (σ p.1)
  unfold stencilSq
  rw [sum_add_distrib, sum_comm, sum_comm (f := fun x (p : ι × Fin 4) =>
    ‖fwdDiff h p.2 u (x + σ p.1)‖ ^ 2)]
  simp only [h1, h2, sum_const, card_univ, nsmul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  unfold firstNormSq massNormSq
  rw [← mul_sum]
  field_simp

/-- `lem:native-action-Hessian`, `eq:action-Hessian-bilinear`: the Hessian of the
shifted-first-jet action is bounded by `M · card ι · ‖u‖_{1,h} ‖v‖_{1,h}`, where `M`
bounds the Hessian of the density along the record and `card ι` is the stencil size. -/
theorem abs_iteratedFDeriv_action_le (hF : ContDiff ℝ 2 F) (hh : h ≠ 0) {y : Grid n → V}
    {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 2 F (stencil h σ x y)‖ ≤ M) (u v : Grid n → V) :
    |iteratedFDeriv ℝ 2 (action F h σ) y ![u, v]| ≤
      M * Fintype.card ι * (Real.sqrt (firstNormSq h u) * Real.sqrt (firstNormSq h v)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [iteratedFDeriv_action hF]
  have hterm : ∀ x, |iteratedFDeriv ℝ 2 F (stencil h σ x y)
      ![stencil h σ x u, stencil h σ x v]| ≤ M * (‖stencil h σ x u‖ * ‖stencil h σ x v‖) := by
    intro x
    rw [← Real.norm_eq_abs]
    calc ‖iteratedFDeriv ℝ 2 F (stencil h σ x y) ![stencil h σ x u, stencil h σ x v]‖
        ≤ ‖iteratedFDeriv ℝ 2 F (stencil h σ x y)‖ *
          ∏ i, ‖(![stencil h σ x u, stencil h σ x v] : Fin 2 → _) i‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 2 F (stencil h σ x y)‖ *
          (‖stencil h σ x u‖ * ‖stencil h σ x v‖) := by
          simp [Fin.prod_univ_two]
      _ ≤ M * (‖stencil h σ x u‖ * ‖stencil h σ x v‖) := by
          gcongr
          exact hM x
  have hcs : ∑ x, ‖stencil h σ x u‖ * ‖stencil h σ x v‖ ≤
      Real.sqrt (∑ x, stencilSq h σ x u) * Real.sqrt (∑ x, stencilSq h σ x v) := by
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
    gcongr with x _ x _
    · exact (le_of_eq rfl).trans
        (by rw [← Real.le_sqrt (norm_nonneg _) (stencilSq_nonneg h σ x u)]
            exact norm_stencil_le h σ x u)
    · rw [← Real.le_sqrt (norm_nonneg _) (stencilSq_nonneg h σ x v)]
      exact norm_stencil_le h σ x v
  have hkey : h ^ 4 * (Real.sqrt ((Fintype.card ι : ℝ) * (h ^ 4)⁻¹) *
      Real.sqrt ((Fintype.card ι : ℝ) * (h ^ 4)⁻¹)) = Fintype.card ι := by
    rw [Real.mul_self_sqrt (by positivity)]
    field_simp
  calc |h ^ 4 * ∑ x, iteratedFDeriv ℝ 2 F (stencil h σ x y)
        ![stencil h σ x u, stencil h σ x v]|
      = h ^ 4 * |∑ x, iteratedFDeriv ℝ 2 F (stencil h σ x y)
        ![stencil h σ x u, stencil h σ x v]| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ h ^ 4 * ∑ x, |iteratedFDeriv ℝ 2 F (stencil h σ x y)
        ![stencil h σ x u, stencil h σ x v]| := by
        gcongr
        exact abs_sum_le_sum_abs _ _
    _ ≤ h ^ 4 * ∑ x, M * (‖stencil h σ x u‖ * ‖stencil h σ x v‖) := by
        gcongr with x _
        exact hterm x
    _ = h ^ 4 * M * ∑ x, ‖stencil h σ x u‖ * ‖stencil h σ x v‖ := by
        rw [← mul_sum]
        ring
    _ ≤ h ^ 4 * M * (Real.sqrt (∑ x, stencilSq h σ x u) *
        Real.sqrt (∑ x, stencilSq h σ x v)) := by
        gcongr
    _ = M * Fintype.card ι * (Real.sqrt (firstNormSq h u) * Real.sqrt (firstNormSq h v)) := by
        rw [sum_stencilSq hh, sum_stencilSq hh,
          Real.sqrt_mul (x := (Fintype.card ι : ℝ) * (h ^ 4)⁻¹) (by positivity),
          Real.sqrt_mul (x := (Fintype.card ι : ℝ) * (h ^ 4)⁻¹) (by positivity)]
        linear_combination
          (M * Real.sqrt (firstNormSq h u) * Real.sqrt (firstNormSq h v)) * hkey

/-- `lem:native-action-Hessian`, `eq:action-Hessian-scale`: in the mass norm the
Hessian scale is `K₀ h⁻²` with `K₀ = 17 M · card ι` independent of `h` and of the
number of nodes (`0 < h ≤ 1`). -/
theorem abs_iteratedFDeriv_action_le_mass (hF : ContDiff ℝ 2 F) (hh : 0 < h) (hh1 : h ≤ 1)
    {y : Grid n → V} {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 2 F (stencil h σ x y)‖ ≤ M)
    (u v : Grid n → V) :
    |iteratedFDeriv ℝ 2 (action F h σ) y ![u, v]| ≤
      (17 * M * Fintype.card ι) * h⁻¹ ^ 2 *
        (Real.sqrt (massNormSq h u) * Real.sqrt (massNormSq h v)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine (abs_iteratedFDeriv_action_le hF hh.ne' hM u v).trans ?_
  have hsq : ∀ w : Grid n → V, Real.sqrt (firstNormSq h w) ≤
      Real.sqrt 17 * h⁻¹ * Real.sqrt (massNormSq h w) := by
    intro w
    have hinv : 0 ≤ h⁻¹ := by positivity
    rw [← Real.sqrt_sq hinv, ← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (firstNormSq_le hh hh1 w)
  have h17 : Real.sqrt 17 * Real.sqrt 17 = 17 := Real.mul_self_sqrt (by norm_num)
  calc M * Fintype.card ι * (Real.sqrt (firstNormSq h u) * Real.sqrt (firstNormSq h v))
      ≤ M * Fintype.card ι * ((Real.sqrt 17 * h⁻¹ * Real.sqrt (massNormSq h u)) *
          (Real.sqrt 17 * h⁻¹ * Real.sqrt (massNormSq h v))) := by
        gcongr
        · exact hsq u
        · exact hsq v
    _ = (17 * M * Fintype.card ι) * h⁻¹ ^ 2 *
        (Real.sqrt (massNormSq h u) * Real.sqrt (massNormSq h v)) := by
        linear_combination (M * Fintype.card ι * h⁻¹ ^ 2 * Real.sqrt (massNormSq h u) *
          Real.sqrt (massNormSq h v)) * h17

/-- `lem:native-action-Hessian`, `eq:action-span`: on a set where the density is
bounded by `B`, the action oscillates by at most `2B · (h⁴ n⁴)`, the fixed
`h⁴ × (number of cells)` volume factor. -/
theorem abs_action_sub_le {y y' : Grid n → V} {B : ℝ}
    (hy : ∀ x, |F (stencil h σ x y)| ≤ B) (hy' : ∀ x, |F (stencil h σ x y')| ≤ B) :
    |action F h σ y - action F h σ y'| ≤ 2 * B * (h ^ 4 * (n : ℝ) ^ 4) := by
  unfold action
  rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_nonneg (by positivity)]
  calc h ^ 4 * |∑ x, (F (stencil h σ x y) - F (stencil h σ x y'))|
      ≤ h ^ 4 * ∑ x, |F (stencil h σ x y) - F (stencil h σ x y')| := by
        gcongr
        exact abs_sum_le_sum_abs _ _
    _ ≤ h ^ 4 * ∑ _x : Grid n, 2 * B := by
        gcongr with x _
        exact (abs_sub _ _).trans (by linarith [hy x, hy' x])
    _ = 2 * B * (h ^ 4 * (n : ℝ) ^ 4) := by
        rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        push_cast
        ring

end ShiftedJetAction
end RenewalGeometry
