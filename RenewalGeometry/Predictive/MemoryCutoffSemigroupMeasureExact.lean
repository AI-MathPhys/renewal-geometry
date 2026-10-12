/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.SystemsTheory.OperatorTailMeasureSesquilinear
import RenewalGeometry.Predictive.MemoryCutoffSemigroupExact
open MathPhys
/-!
# The exact memory RG semigroup for general positive operator-valued tail measures

Paper `predictive_spectral_geometry`, label `thm:supp-memory-RG`, for the general (weakly
countably additive) positive operator-valued tail measures of `def:supp-POVM`
(`OperatorTailMeasure.PositiveTailMeasure`).  The finite atomic case is in
`MemoryCutoffSemigroupExact`; here the Stieltjes integrals are Mathlib vector-measure
integrals.

For `μ` a positive tail measure, `A : Matrix H H ℂ` and a cutoff `Λ`:

* `dynamicFunction μ A z = F_{A,μ}(z) = A - z - Σ_μ(z)`;
* `headCorrection μ Λ = Q_{>Λ} = ∫_{(Λ,∞)} λ⁻¹ dμ(λ)`, `cutoff μ Λ = μ|_{(0,Λ]}` and
  `rg μ A Λ = RG_Λ(A, μ) = (A - Q_{>Λ}, μ|_{(0,Λ]})` (`eq:supp-memory-head`, `eq:supp-memory-RG`);
* `eq:supp-memory-static-preserved` (`dynamicFunction_rg_zero`): `F_{RG_Λ(A,μ)}(0) = F_{A,μ}(0)`,
  under the standing hypothesis that `λ⁻¹` is `μ`-integrable (this is exactly the condition
  that `F_{A,μ}(0)` exists);
* `eq:supp-memory-screen-error` (`norm_dynamicFunction_sub_rg_le`): for `‖z‖ ≤ r < Λ` and
  `z ∉ [0,∞)`, `‖F_{A,μ}(z) - F_{RG_Λ(A,μ)}(z)‖ ≤ r/(Λ - r) ‖Q_{>Λ}‖` in the operator norm;
* `eq:supp-memory-semigroup` (`rg_rg`): `RG_{Λ₂} ∘ RG_{Λ₁} = RG_{Λ₂}` for `0 < Λ₂ ≤ Λ₁`.

The analytic core (now in `OperatorTailMeasureSesquilinear`) is the **positive-weighted operator-norm bound for operator integrals**
(`l2_opNorm_integral_le_of_norm_le`): if `‖c‖ ≤ κ w` `μ`-a.e. with `w ≥ 0`, then
`‖∫ c dμ‖ ≤ κ ‖∫ w dμ‖`.  It is proved by scalarising along the sesquilinear forms
`⟨x, μ(·) y⟩`, whose total variation is dominated by `(t ⟨x, μ x⟩ + t⁻¹ ⟨y, μ y⟩)/2` for every
`t > 0` (Cauchy–Schwarz for positive semidefinite matrices), integrating and optimising in `t`.
-/

open MeasureTheory Filter Topology Set
open scoped ComplexOrder ENNReal Matrix InnerProductSpace Matrix.Norms.L2Operator

namespace MathPhys
namespace OperatorTailMeasure

variable {H : Type*} [Fintype H] [DecidableEq H]

namespace PositiveTailMeasure

variable (μ : PositiveTailMeasure H)

/-! ## The memory RG data -/

/-- The cutoff measure `μ|_{(0,Λ]}` (`eq:supp-memory-RG`). -/
noncomputable def cutoff (Λ : ℝ) : PositiveTailMeasure H where
  toVectorMeasure := μ.toVectorMeasure.restrict (Iic Λ)
  posSemidef s hs := by
    rw [VectorMeasure.restrict_apply _ measurableSet_Iic hs]
    exact μ.posSemidef _ (hs.inter measurableSet_Iic)
  eq_zero_of_subset_Iic s hs hsub := by
    rw [VectorMeasure.restrict_apply _ measurableSet_Iic hs]
    exact μ.eq_zero_of_subset_Iic _ (hs.inter measurableSet_Iic) (inter_subset_left.trans hsub)

theorem cutoff_toVectorMeasure (Λ : ℝ) :
    (μ.cutoff Λ).toVectorMeasure = μ.toVectorMeasure.restrict (Iic Λ) := rfl

/-- The inverse-moment head correction `Q_{>Λ} = ∫_{(Λ,∞)} λ⁻¹ dμ(λ)` (`eq:supp-memory-head`). -/
noncomputable def headCorrection (Λ : ℝ) : Matrix H H ℂ :=
  Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
    (fun lam : ℝ => ((lam : ℂ))⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ))

/-- The dynamic function `F_{A,μ}(z) = A - z - Σ_μ(z)` (`eq:supp-memory-head`). -/
noncomputable def dynamicFunction (A : Matrix H H ℂ) (z : ℂ) : Matrix H H ℂ :=
  A - z • (1 : Matrix H H ℂ) - μ.stieltjesSelfEnergy z

/-- **`eq:supp-memory-RG`.**  The memory cutoff map `RG_Λ(A, μ) = (A - Q_{>Λ}, μ|_{(0,Λ]})`. -/
noncomputable def rg (A : Matrix H H ℂ) (Λ : ℝ) : Matrix H H ℂ × PositiveTailMeasure H :=
  (A - μ.headCorrection Λ, μ.cutoff Λ)

/-- Bounded measurable functions are integrable on a set against the variation of `μ`. -/
theorem integrableOn_of_norm_le {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℂ}
    (hf : Measurable f) {K : ℝ} (hK : ∀ x ∈ s, ‖f x‖ ≤ K) :
    Integrable f (μ.toVectorMeasure.restrict s).variation := by
  rw [VectorMeasure.variation_restrict hs]
  refine Integrable.mono' (integrable_const K) hf.aestronglyMeasurable ?_
  rw [ae_restrict_iff' hs]
  exact ae_of_all _ hK

/-- The resolvent kernel at `z = 0` is the inverse-moment kernel. -/
theorem resolvent_zero : (fun lam : ℝ => ((lam : ℂ) - 0)⁻¹) = fun lam : ℝ => ((lam : ℂ))⁻¹ := by
  funext lam
  rw [sub_zero]

/-- Splitting the Stieltjes integral at the cutoff. -/
theorem stieltjesSelfEnergy_split (Λ : ℝ) {z : ℂ}
    (hz : Integrable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) μ.toVectorMeasure.variation) :
    μ.stieltjesSelfEnergy z = (μ.cutoff Λ).stieltjesSelfEnergy z +
      Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
        (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ)) := by
  have h := VectorMeasure.setIntegral_add_compl (μ := μ.toVectorMeasure)
    (B := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))
    (f := fun lam : ℝ => ((lam : ℂ) - z)⁻¹) (s := Iic Λ) measurableSet_Iic hz
  rw [Set.compl_Iic] at h
  unfold stieltjesSelfEnergy
  rw [cutoff_toVectorMeasure, ← h]
  rfl

/-- **`eq:supp-memory-static-preserved`.**  The static value is preserved by the cutoff:
`F_{RG_Λ(A,μ)}(0) = F_{A,μ}(0)`, provided `λ⁻¹` is `μ`-integrable (i.e. `F_{A,μ}(0)` exists). -/
theorem dynamicFunction_rg_zero (A : Matrix H H ℂ) (Λ : ℝ)
    (hint : Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹) μ.toVectorMeasure.variation) :
    (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 0 = μ.dynamicFunction A 0 := by
  have hint' : Integrable (fun lam : ℝ => ((lam : ℂ) - 0)⁻¹) μ.toVectorMeasure.variation := by
    rw [resolvent_zero]; exact hint
  simp only [rg, dynamicFunction]
  rw [μ.stieltjesSelfEnergy_split Λ hint']
  unfold headCorrection
  rw [resolvent_zero]
  abel

/-- The inverse-moment kernel `λ⁻¹` is integrable on `(Λ, ∞)` for `Λ > 0`. -/
theorem integrableOn_inv_Ioi {Λ : ℝ} (hΛ : 0 < Λ) :
    Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹) (μ.toVectorMeasure.restrict (Ioi Λ)).variation := by
  refine μ.integrableOn_of_norm_le measurableSet_Ioi Complex.measurable_ofReal.inv (K := Λ⁻¹)
    fun x hx => ?_
  have hx' : Λ < x := hx
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hΛ.trans hx')]
  exact inv_anti₀ hΛ hx'.le

/-- The screening difference is the head-corrected tail integral. -/
theorem dynamicFunction_sub_rg (A : Matrix H H ℂ) {Λ : ℝ} (hΛ : 0 < Λ) {z : ℂ}
    (hz : Integrable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) μ.toVectorMeasure.variation) :
    μ.dynamicFunction A z - (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 z =
      Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
        (fun lam : ℝ => ((lam : ℂ))⁻¹ - ((lam : ℂ) - z)⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ)) := by
  simp only [rg, dynamicFunction]
  rw [μ.stieltjesSelfEnergy_split Λ hz]
  unfold headCorrection
  have hsub := VectorMeasure.integral_fun_sub (μ := μ.toVectorMeasure.restrict (Ioi Λ))
    (B := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))
    (f := fun lam : ℝ => ((lam : ℂ))⁻¹) (g := fun lam : ℝ => ((lam : ℂ) - z)⁻¹)
    (μ.integrableOn_inv_Ioi hΛ)
    (VectorMeasure.Integrable.integrableOn (μ := μ.toVectorMeasure) hz)
  have : Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
      (fun lam : ℝ => ((lam : ℂ))⁻¹ - ((lam : ℂ) - z)⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ)) =
      Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
        (fun lam : ℝ => ((lam : ℂ))⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ)) -
      Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
        (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ)) := by
    rw [hsub]
    rfl
  rw [this]
  abel

/-- **`eq:supp-memory-screen-error`** (integrability form).  For `‖z‖ ≤ r < Λ`, if
`(λ - z)⁻¹` is `μ`-integrable, then
`‖F_{A,μ}(z) - F_{RG_Λ(A,μ)}(z)‖ ≤ r/(Λ - r) ‖Q_{>Λ}‖` in the operator norm. -/
theorem norm_dynamicFunction_sub_rg_le_of_integrable (A : Matrix H H ℂ) {Λ r : ℝ} (hr : r < Λ)
    {z : ℂ} (hz : ‖z‖ ≤ r)
    (hzint : Integrable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) μ.toVectorMeasure.variation) :
    ‖μ.dynamicFunction A z - (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 z‖ ≤
      r / (Λ - r) * ‖μ.headCorrection Λ‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hΛr : 0 < Λ - r := sub_pos.mpr hr
  have hΛ : 0 < Λ := lt_of_le_of_lt hr0 hr
  rw [μ.dynamicFunction_sub_rg A hΛ hzint]
  -- the tail measure as a positive tail measure
  set ν : PositiveTailMeasure H :=
    { toVectorMeasure := μ.toVectorMeasure.restrict (Ioi Λ)
      posSemidef := fun s hs => by
        rw [VectorMeasure.restrict_apply _ measurableSet_Ioi hs]
        exact μ.posSemidef _ (hs.inter measurableSet_Ioi)
      eq_zero_of_subset_Iic := fun s hs hsub => by
        rw [VectorMeasure.restrict_apply _ measurableSet_Ioi hs]
        exact μ.eq_zero_of_subset_Iic _ (hs.inter measurableSet_Ioi)
          (inter_subset_left.trans hsub) } with hν
  have hνmeas : ν.toVectorMeasure = μ.toVectorMeasure.restrict (Ioi Λ) := rfl
  have hvar : ν.toVectorMeasure.variation = μ.toVectorMeasure.variation.restrict (Ioi Λ) := by
    rw [hνmeas, VectorMeasure.variation_restrict measurableSet_Ioi]
  have hmem : ∀ᵐ lam ∂ν.toVectorMeasure.variation, Λ < lam := by
    rw [hvar, ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ fun lam h => h
  have hc : Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹ - ((lam : ℂ) - z)⁻¹)
      ν.toVectorMeasure.variation := by
    rw [hνmeas]
    have h1 : Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹)
        (μ.toVectorMeasure.restrict (Ioi Λ)).variation := μ.integrableOn_inv_Ioi hΛ
    have h2 : Integrable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹)
        (μ.toVectorMeasure.restrict (Ioi Λ)).variation :=
      VectorMeasure.Integrable.integrableOn (μ := μ.toVectorMeasure) hzint
    exact h1.sub h2
  have hw : Integrable (fun lam : ℝ => lam⁻¹) ν.toVectorMeasure.variation := by
    rw [hvar]
    refine Integrable.mono' (integrable_const Λ⁻¹) measurable_inv.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun lam (h : Λ < lam) => ?_
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hΛ.trans h))]
    exact inv_anti₀ hΛ h.le
  have hw0 : ∀ᵐ lam ∂ν.toVectorMeasure.variation, 0 ≤ lam⁻¹ := by
    filter_upwards [hmem] with lam h
    exact (inv_pos.mpr (hΛ.trans h)).le
  have hcw : ∀ᵐ (lam : ℝ) ∂ν.toVectorMeasure.variation,
      ‖((lam : ℂ))⁻¹ - ((lam : ℂ) - z)⁻¹‖ ≤ r / (Λ - r) * lam⁻¹ := by
    filter_upwards [hmem] with lam h
    exact RenewalGeometry.MemoryRG.FiniteAtomicTailMeasure.norm_inv_sub_inv_le h hr hz
  have key := ν.l2_opNorm_integral_le_of_norm_le hc hw hw0 (div_nonneg hr0 hΛr.le) hcw
  have hhead : μ.headCorrection Λ = Matrix.of (VectorMeasure.integral ν.toVectorMeasure
      (fun a : ℝ => ((a⁻¹ : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ)) := by
    unfold headCorrection
    rw [hνmeas]
    congr 1
    funext a
    push_cast
    rfl
  rw [hhead]
  exact key

/-- **`eq:supp-memory-screen-error`.**  For `‖z‖ ≤ r < Λ` with `z ∉ [0,∞)` (the domain of the
Stieltjes self-energy): `‖F_{A,μ}(z) - F_{RG_Λ(A,μ)}(z)‖ ≤ r/(Λ - r) ‖Q_{>Λ}‖`. -/
theorem norm_dynamicFunction_sub_rg_le (A : Matrix H H ℂ) {Λ r : ℝ} (hr : r < Λ)
    {z : ℂ} (hz : ‖z‖ ≤ r) (hzdom : ¬ (z.im = 0 ∧ 0 ≤ z.re)) :
    ‖μ.dynamicFunction A z - (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 z‖ ≤
      r / (Λ - r) * ‖μ.headCorrection Λ‖ :=
  μ.norm_dynamicFunction_sub_rg_le_of_integrable A hr hz (μ.integrable_resolvent hzdom)

/-- The cutoff measures compose: `(μ|_{(0,Λ₁]})|_{(0,Λ₂]} = μ|_{(0,Λ₂]}` for `Λ₂ ≤ Λ₁`. -/
theorem cutoff_cutoff {Λ₁ Λ₂ : ℝ} (h : Λ₂ ≤ Λ₁) : (μ.cutoff Λ₁).cutoff Λ₂ = μ.cutoff Λ₂ := by
  rw [ext_iff', cutoff_toVectorMeasure, cutoff_toVectorMeasure, cutoff_toVectorMeasure,
    VectorMeasure.restrict_restrict _ measurableSet_Iic measurableSet_Iic, Set.Iic_inter_Iic,
    min_eq_left h]

/-- The head corrections add over disjoint shells: `Q^{μ}_{>Λ₁} + Q^{μ|Λ₁}_{>Λ₂} = Q^{μ}_{>Λ₂}`
for `0 < Λ₂ ≤ Λ₁`. -/
theorem headCorrection_add_headCorrection_cutoff {Λ₁ Λ₂ : ℝ} (h2 : 0 < Λ₂) (h : Λ₂ ≤ Λ₁) :
    μ.headCorrection Λ₁ + (μ.cutoff Λ₁).headCorrection Λ₂ = μ.headCorrection Λ₂ := by
  unfold headCorrection
  rw [cutoff_toVectorMeasure,
    VectorMeasure.restrict_restrict _ measurableSet_Ioi measurableSet_Iic]
  have hint : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ Ioi Λ₂ →
      Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹) (μ.toVectorMeasure.restrict s).variation := by
    intro s hs hsub
    refine μ.integrableOn_of_norm_le hs (Complex.measurable_ofReal.inv) (K := Λ₂⁻¹)
      fun x hx => ?_
    have hx' : Λ₂ < x := hsub hx
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h2.trans hx')]
    exact inv_anti₀ h2 hx'.le
  have hu := VectorMeasure.setIntegral_union (μ := μ.toVectorMeasure)
    (B := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))
    (f := fun lam : ℝ => ((lam : ℂ))⁻¹) (s := Ioi Λ₁) (t := Ioi Λ₂ ∩ Iic Λ₁)
    (by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd (show x ≤ Λ₁ from hx'.2) (not_le.mpr (show Λ₁ < x from hx)))
    measurableSet_Ioi (measurableSet_Ioi.inter measurableSet_Iic)
    (hint measurableSet_Ioi fun x hx => lt_of_le_of_lt h hx)
    (hint (measurableSet_Ioi.inter measurableSet_Iic) fun x hx => hx.1)
  have hset : Ioi Λ₁ ∪ Ioi Λ₂ ∩ Iic Λ₁ = Ioi Λ₂ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_inter_iff, Set.mem_Iic]
    constructor
    · rintro (hx | ⟨hx, _⟩)
      · exact lt_of_le_of_lt h hx
      · exact hx
    · intro hx
      by_cases hx' : Λ₁ < x
      · exact Or.inl hx'
      · exact Or.inr ⟨hx, not_lt.mp hx'⟩
  rw [hset] at hu
  rw [hu]
  rfl

/-- **`eq:supp-memory-semigroup`.**  Two successive cutoffs `0 < Λ₂ ≤ Λ₁` compose to the lower
cutoff: `RG_{Λ₂} ∘ RG_{Λ₁} = RG_{Λ₂}`. -/
theorem rg_rg (A : Matrix H H ℂ) {Λ₁ Λ₂ : ℝ} (h2 : 0 < Λ₂) (h : Λ₂ ≤ Λ₁) :
    (μ.rg A Λ₁).2.rg (μ.rg A Λ₁).1 Λ₂ = μ.rg A Λ₂ := by
  simp only [rg]
  refine Prod.ext ?_ (μ.cutoff_cutoff h)
  show A - μ.headCorrection Λ₁ - (μ.cutoff Λ₁).headCorrection Λ₂ = A - μ.headCorrection Λ₂
  rw [← μ.headCorrection_add_headCorrection_cutoff h2 h]
  abel

/-- **`thm:supp-memory-RG` (Exact memory RG semigroup)** for general positive operator-valued
tail measures (`def:supp-POVM`): the static value is preserved whenever it exists (`λ⁻¹`
`μ`-integrable), the screening error for `‖z‖ ≤ r < Λ`, `z ∉ [0,∞)` is at most
`r/(Λ - r) ‖Q_{>Λ}‖` in operator norm, and `RG_{Λ₂} ∘ RG_{Λ₁} = RG_{Λ₂}` for `0 < Λ₂ ≤ Λ₁`. -/
theorem memory_rg_semigroup (A : Matrix H H ℂ) :
    (Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹) μ.toVectorMeasure.variation →
      ∀ Λ : ℝ, (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 0 = μ.dynamicFunction A 0) ∧
    (∀ (Λ r : ℝ), r < Λ → ∀ z : ℂ, ‖z‖ ≤ r → ¬ (z.im = 0 ∧ 0 ≤ z.re) →
      ‖μ.dynamicFunction A z - (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 z‖ ≤
        r / (Λ - r) * ‖μ.headCorrection Λ‖) ∧
    (∀ Λ₁ Λ₂ : ℝ, 0 < Λ₂ → Λ₂ ≤ Λ₁ → (μ.rg A Λ₁).2.rg (μ.rg A Λ₁).1 Λ₂ = μ.rg A Λ₂) :=
  ⟨fun hint Λ => μ.dynamicFunction_rg_zero A Λ hint,
    fun _ _ hr _ hz hzdom => μ.norm_dynamicFunction_sub_rg_le A hr hz hzdom,
    fun _ _ h2 h => μ.rg_rg A h2 h⟩

end PositiveTailMeasure

end OperatorTailMeasure
end MathPhys
