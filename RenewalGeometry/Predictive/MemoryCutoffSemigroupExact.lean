/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The exact memory RG semigroup (finite atomic tail measures)

Paper `predictive_spectral_geometry`, label `thm:supp-memory-RG`, for a
positive operator-valued tail measure (`def:supp-POVM`) that is **finite
atomic**: `μ = ∑_i Q_i δ_{λ_i}` with atoms `λ_i > 0` and positive weights
`Q_i` (`FiniteAtomicTailMeasure`).  For such `μ`,

* `selfEnergy μ z = Σ_μ(z) = ∑_i (λ_i - z)⁻¹ Q_i` (`eq:supp-Stieltjes`),
  `dynamicFunction A μ z = F_{A,μ}(z) = A - z - Σ_μ(z)`,
  `headCorrection μ Λ = Q_{>Λ} = ∑_{λ_i > Λ} λ_i⁻¹ Q_i` (`eq:supp-memory-head`),
  `restrict μ Λ = μ|_{(0,Λ]}` and `rg A μ Λ = RG_Λ(A, μ)` (`eq:supp-memory-RG`);
* `eq:supp-memory-static-preserved` — `dynamicFunction_rg_zero`:
  `F_{RG_Λ(A,μ)}(0) = F_{A,μ}(0)`;
* `eq:supp-memory-screen-error` — `norm_dynamicFunction_sub_rg_le`:
  `‖F_{A,μ}(z) - F_{RG_Λ(A,μ)}(z)‖ ≤ r/(Λ - r) ‖Q_{>Λ}‖` for `‖z‖ ≤ r < Λ`,
  through the positive-weighted operator-norm bound
  `norm_sum_smul_le_of_isPositive` (`‖∑ c_i Q_i‖ ≤ κ ‖∑ w_i Q_i‖` when
  `Q_i ⪰ 0` and `|c_i| ≤ κ w_i`);
* `eq:supp-memory-semigroup` — `rg_rg`: `RG_{Λ₂} ∘ RG_{Λ₁} = RG_{Λ₂}` for
  `Λ₂ ≤ Λ₁`.

The general (weakly countably additive) measure of `def:supp-POVM` is not
treated here; the finite atomic case is the one used by the paper's explicit
memory examples.
-/

open scoped InnerProductSpace
open Finset

namespace RenewalGeometry
namespace MemoryRG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ### Cauchy–Schwarz for positive operators and the weighted norm bound -/

/-- Cauchy–Schwarz for the form of a positive operator:
`|⟪x, Q y⟫| ≤ √⟪x, Q x⟫ √⟪y, Q y⟫`. -/
theorem norm_inner_map_le_of_isPositive {Q : E →L[ℂ] E} (hQ : Q.IsPositive) (x y : E) :
    ‖⟪x, Q y⟫_ℂ‖ ≤
      Real.sqrt (RCLike.re ⟪x, Q x⟫_ℂ) * Real.sqrt (RCLike.re ⟪y, Q y⟫_ℂ) := by
  have hQ0 : 0 ≤ Q := (ContinuousLinearMap.nonneg_iff_isPositive Q).mpr hQ
  set S := CFC.sqrt Q with hS
  have hSS : S * S = Q := CFC.sqrt_mul_sqrt_self Q hQ0
  have hSsa : IsSelfAdjoint S := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Q)
  have hadj : ContinuousLinearMap.adjoint S = S :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hSsa
  have key : ∀ u v, ⟪u, Q v⟫_ℂ = ⟪S u, S v⟫_ℂ := by
    intro u v
    rw [← hSS, ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left S, hadj]
  rw [key x y]
  calc ‖⟪S x, S y⟫_ℂ‖ ≤ ‖S x‖ * ‖S y‖ := norm_inner_le_norm _ _
    _ = Real.sqrt (RCLike.re ⟪x, Q x⟫_ℂ) * Real.sqrt (RCLike.re ⟪y, Q y⟫_ℂ) := by
        rw [key x x, key y y, inner_self_eq_norm_sq, inner_self_eq_norm_sq,
          Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The quadratic form of a positive operator is bounded by its norm. -/
theorem re_inner_map_le_norm (W : E →L[ℂ] E) (x : E) :
    RCLike.re ⟪x, W x⟫_ℂ ≤ ‖W‖ * ‖x‖ ^ 2 := by
  calc RCLike.re ⟪x, W x⟫_ℂ ≤ ‖x‖ * ‖W x‖ := re_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖W‖ * ‖x‖) := by gcongr; exact W.le_opNorm x
    _ = ‖W‖ * ‖x‖ ^ 2 := by ring

/-- **Positive-weighted operator-norm bound.**  For positive `Q_i` and complex
coefficients with `|c_i| ≤ κ w_i` (`w_i ≥ 0`), `‖∑ c_i Q_i‖ ≤ κ ‖∑ w_i Q_i‖`. -/
theorem norm_sum_smul_le_of_isPositive {ι : Type*} (s : Finset ι) (Q : ι → E →L[ℂ] E)
    (hQ : ∀ i ∈ s, (Q i).IsPositive) (c : ι → ℂ) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (κ : ℝ) (hκ : 0 ≤ κ) (hc : ∀ i ∈ s, ‖c i‖ ≤ κ * w i) :
    ‖∑ i ∈ s, c i • Q i‖ ≤ κ * ‖∑ i ∈ s, (w i : ℂ) • Q i‖ := by
  set W : E →L[ℂ] E := ∑ i ∈ s, (w i : ℂ) • Q i with hW
  set C : E →L[ℂ] E := ∑ i ∈ s, c i • Q i with hC
  have hWx : ∀ x, RCLike.re ⟪x, W x⟫_ℂ = ∑ i ∈ s, w i * RCLike.re ⟪x, Q i x⟫_ℂ := by
    intro x
    simp only [hW, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, inner_sum,
      inner_smul_right, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact RCLike.re_ofReal_mul _ _
  have hQnn : ∀ i ∈ s, ∀ x, 0 ≤ RCLike.re ⟪x, Q i x⟫_ℂ :=
    fun i hi x => (hQ i hi).re_inner_nonneg_right x
  have hbound : ∀ x y, ‖⟪x, C y⟫_ℂ‖ ≤ κ * ‖W‖ * (‖x‖ * ‖y‖) := by
    intro x y
    have hCxy : ⟪x, C y⟫_ℂ = ∑ i ∈ s, c i * ⟪x, Q i y⟫_ℂ := by
      simp [hC, ContinuousLinearMap.sum_apply, inner_sum, inner_smul_right]
    rw [hCxy]
    have hf : ∀ i ∈ s, (Real.sqrt (w i) * Real.sqrt (RCLike.re ⟪x, Q i x⟫_ℂ)) ^ 2 =
        w i * RCLike.re ⟪x, Q i x⟫_ℂ := by
      intro i hi
      rw [mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hQnn i hi x)]
    have hg : ∀ i ∈ s, (Real.sqrt (w i) * Real.sqrt (RCLike.re ⟪y, Q i y⟫_ℂ)) ^ 2 =
        w i * RCLike.re ⟪y, Q i y⟫_ℂ := by
      intro i hi
      rw [mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hQnn i hi y)]
    calc ‖∑ i ∈ s, c i * ⟪x, Q i y⟫_ℂ‖
        ≤ ∑ i ∈ s, ‖c i * ⟪x, Q i y⟫_ℂ‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, κ * w i *
            (Real.sqrt (RCLike.re ⟪x, Q i x⟫_ℂ) * Real.sqrt (RCLike.re ⟪y, Q i y⟫_ℂ)) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul]
          exact mul_le_mul (hc i hi) (norm_inner_map_le_of_isPositive (hQ i hi) x y)
            (norm_nonneg _) (mul_nonneg hκ (hw i hi))
      _ = κ * ∑ i ∈ s, (Real.sqrt (w i) * Real.sqrt (RCLike.re ⟪x, Q i x⟫_ℂ)) *
            (Real.sqrt (w i) * Real.sqrt (RCLike.re ⟪y, Q i y⟫_ℂ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have h := Real.mul_self_sqrt (hw i hi)
          calc κ * w i * (Real.sqrt (RCLike.re ⟪x, Q i x⟫_ℂ) *
                Real.sqrt (RCLike.re ⟪y, Q i y⟫_ℂ))
              = κ * ((Real.sqrt (w i) * Real.sqrt (w i)) *
                (Real.sqrt (RCLike.re ⟪x, Q i x⟫_ℂ) *
                  Real.sqrt (RCLike.re ⟪y, Q i y⟫_ℂ))) := by rw [h]; ring
            _ = _ := by ring
      _ ≤ κ * (Real.sqrt (∑ i ∈ s, w i * RCLike.re ⟪x, Q i x⟫_ℂ) *
            Real.sqrt (∑ i ∈ s, w i * RCLike.re ⟪y, Q i y⟫_ℂ)) := by
          gcongr
          rw [← Real.sqrt_mul (Finset.sum_nonneg fun i hi =>
            mul_nonneg (hw i hi) (hQnn i hi x))]
          apply Real.le_sqrt_of_sq_le
          calc (∑ i ∈ s, (Real.sqrt (w i) * Real.sqrt (RCLike.re ⟪x, Q i x⟫_ℂ)) *
                  (Real.sqrt (w i) * Real.sqrt (RCLike.re ⟪y, Q i y⟫_ℂ))) ^ 2
              ≤ (∑ i ∈ s, (Real.sqrt (w i) * Real.sqrt (RCLike.re ⟪x, Q i x⟫_ℂ)) ^ 2) *
                  ∑ i ∈ s, (Real.sqrt (w i) * Real.sqrt (RCLike.re ⟪y, Q i y⟫_ℂ)) ^ 2 :=
                Finset.sum_mul_sq_le_sq_mul_sq s _ _
            _ = _ := by
                rw [Finset.sum_congr rfl hf, Finset.sum_congr rfl hg]
      _ ≤ κ * (Real.sqrt (‖W‖ * ‖x‖ ^ 2) * Real.sqrt (‖W‖ * ‖y‖ ^ 2)) := by
          gcongr
          · rw [← hWx]; exact re_inner_map_le_norm W x
          · rw [← hWx]; exact re_inner_map_le_norm W y
      _ = κ * ‖W‖ * (‖x‖ * ‖y‖) := by
          rw [Real.sqrt_mul (norm_nonneg W), Real.sqrt_mul (norm_nonneg W),
            Real.sqrt_sq (norm_nonneg x), Real.sqrt_sq (norm_nonneg y)]
          have h := Real.mul_self_sqrt (norm_nonneg W)
          calc κ * (Real.sqrt ‖W‖ * ‖x‖ * (Real.sqrt ‖W‖ * ‖y‖))
              = κ * ((Real.sqrt ‖W‖ * Real.sqrt ‖W‖) * (‖x‖ * ‖y‖)) := by ring
            _ = _ := by rw [h]; ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  by_cases hCy : ‖C y‖ = 0
  · rw [hCy]; positivity
  · have hpos : 0 < ‖C y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hCy)
    have h := hbound (C y) y
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at h
    have h' : ‖C y‖ * ‖C y‖ ≤ (κ * ‖W‖ * ‖y‖) * ‖C y‖ := by
      calc ‖C y‖ * ‖C y‖ = ‖C y‖ ^ 2 := (sq _).symm
        _ ≤ κ * ‖W‖ * (‖C y‖ * ‖y‖) := h
        _ = (κ * ‖W‖ * ‖y‖) * ‖C y‖ := by ring
    exact le_of_mul_le_mul_right h' hpos

/-! ### Finite atomic tail measures and the cutoff semigroup -/

/-- A finite atomic positive operator-valued tail measure
`μ = ∑_i Q_i δ_{λ_i}` (`def:supp-POVM`, atomic case): atoms `λ_i > 0` and
positive weights `Q_i`. -/
structure FiniteAtomicTailMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι : Type*) where
  /-- The atoms `λ_i ∈ (0, ∞)`. -/
  atom : ι → ℝ
  atom_pos : ∀ i, 0 < atom i
  /-- The positive weights `Q_i = μ({λ_i})`. -/
  weight : ι → E →L[ℂ] E
  weight_pos : ∀ i, (weight i).IsPositive

variable {ι : Type*} [Fintype ι]

namespace FiniteAtomicTailMeasure

variable (μ : FiniteAtomicTailMeasure E ι)

/-- The Stieltjes self-energy `Σ_μ(z) = ∑_i (λ_i - z)⁻¹ Q_i` (`eq:supp-Stieltjes`). -/
noncomputable def selfEnergy (z : ℂ) : E →L[ℂ] E :=
  ∑ i, ((μ.atom i : ℂ) - z)⁻¹ • μ.weight i

/-- The dynamic function `F_{A,μ}(z) = A - z - Σ_μ(z)` (`eq:supp-memory-head`). -/
noncomputable def dynamicFunction (A : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  A - z • (1 : E →L[ℂ] E) - μ.selfEnergy z

/-- The inverse-moment head correction `Q_{>Λ} = ∑_{λ_i > Λ} λ_i⁻¹ Q_i`. -/
noncomputable def headCorrection (Λ : ℝ) : E →L[ℂ] E :=
  ∑ i, if Λ < μ.atom i then ((μ.atom i : ℂ))⁻¹ • μ.weight i else 0

/-- The restricted measure `μ|_{(0,Λ]}` (weights above the cutoff set to zero). -/
noncomputable def restrict (Λ : ℝ) : FiniteAtomicTailMeasure E ι where
  atom := μ.atom
  atom_pos := μ.atom_pos
  weight := fun i => if μ.atom i ≤ Λ then μ.weight i else 0
  weight_pos := fun i => by
    split_ifs
    · exact μ.weight_pos i
    · exact ContinuousLinearMap.isPositive_zero

/-- **`eq:supp-memory-RG`.**  The memory cutoff map
`RG_Λ(A, μ) = (A - Q_{>Λ}, μ|_{(0,Λ]})`. -/
noncomputable def rg (A : E →L[ℂ] E) (Λ : ℝ) : (E →L[ℂ] E) × FiniteAtomicTailMeasure E ι :=
  (A - μ.headCorrection Λ, μ.restrict Λ)

theorem selfEnergy_restrict (Λ : ℝ) (z : ℂ) :
    (μ.restrict Λ).selfEnergy z =
      ∑ i, if μ.atom i ≤ Λ then ((μ.atom i : ℂ) - z)⁻¹ • μ.weight i else 0 := by
  unfold selfEnergy restrict
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : μ.atom i ≤ Λ
  · simp [h]
  · simp [h]

/-- **`eq:supp-memory-static-preserved`.**  The static value is preserved:
`F_{RG_Λ(A,μ)}(0) = F_{A,μ}(0)`. -/
theorem dynamicFunction_rg_zero (A : E →L[ℂ] E) (Λ : ℝ) :
    (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 0 = μ.dynamicFunction A 0 := by
  simp only [rg, dynamicFunction]
  rw [selfEnergy_restrict]
  unfold selfEnergy
  simp only [zero_smul, sub_zero]
  have hsplit : μ.headCorrection Λ +
      (∑ i, if μ.atom i ≤ Λ then ((μ.atom i : ℂ))⁻¹ • μ.weight i else 0) =
      ∑ i, ((μ.atom i : ℂ))⁻¹ • μ.weight i := by
    unfold headCorrection
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : Λ < μ.atom i
    · simp [h, not_le.mpr h]
    · simp [h, not_lt.mp h]
  rw [← hsplit]
  abel

/-- **`eq:supp-memory-semigroup`.**  Two successive cutoffs `Λ₂ ≤ Λ₁` compose
to the lower cutoff: `RG_{Λ₂} ∘ RG_{Λ₁} = RG_{Λ₂}`. -/
theorem rg_rg (A : E →L[ℂ] E) {Λ₁ Λ₂ : ℝ} (h : Λ₂ ≤ Λ₁) :
    (μ.rg A Λ₁).2.rg (μ.rg A Λ₁).1 Λ₂ = μ.rg A Λ₂ := by
  simp only [rg]
  refine Prod.ext ?_ ?_
  · show A - μ.headCorrection Λ₁ - (μ.restrict Λ₁).headCorrection Λ₂ = A - μ.headCorrection Λ₂
    have hsum : μ.headCorrection Λ₁ + (μ.restrict Λ₁).headCorrection Λ₂ =
        μ.headCorrection Λ₂ := by
      unfold headCorrection restrict
      simp only
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h1 : Λ₁ < μ.atom i
      · have h2 : Λ₂ < μ.atom i := lt_of_le_of_lt h h1
        simp [h1, h2, not_le.mpr h1]
      · by_cases h2 : Λ₂ < μ.atom i
        · simp [h1, h2, not_lt.mp h1]
        · simp [h1, h2]
    rw [← hsum]
    abel
  · show (μ.restrict Λ₁).restrict Λ₂ = μ.restrict Λ₂
    unfold restrict
    simp only [FiniteAtomicTailMeasure.mk.injEq, true_and]
    funext i
    by_cases h2 : μ.atom i ≤ Λ₂
    · simp [h2, le_trans h2 h]
    · simp [h2]

/-- The screening difference is the head-corrected tail:
`F_{A,μ}(z) - F_{RG_Λ(A,μ)}(z) = ∑_{λ_i > Λ} (λ_i⁻¹ - (λ_i - z)⁻¹) Q_i`. -/
theorem dynamicFunction_sub_rg (A : E →L[ℂ] E) (Λ : ℝ) (z : ℂ) :
    μ.dynamicFunction A z - (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 z =
      ∑ i ∈ Finset.univ.filter (fun i => Λ < μ.atom i),
        (((μ.atom i : ℂ))⁻¹ - ((μ.atom i : ℂ) - z)⁻¹) • μ.weight i := by
  simp only [rg, dynamicFunction]
  rw [selfEnergy_restrict]
  unfold selfEnergy
  rw [Finset.sum_filter]
  have hhead : μ.headCorrection Λ =
      ∑ i, if Λ < μ.atom i then ((μ.atom i : ℂ))⁻¹ • μ.weight i else 0 := rfl
  have htail : (∑ i, ((μ.atom i : ℂ) - z)⁻¹ • μ.weight i) -
      (∑ i, if μ.atom i ≤ Λ then ((μ.atom i : ℂ) - z)⁻¹ • μ.weight i else 0) =
      ∑ i, if Λ < μ.atom i then ((μ.atom i : ℂ) - z)⁻¹ • μ.weight i else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : Λ < μ.atom i
    · simp [h, not_le.mpr h]
    · simp [h, not_lt.mp h]
  have hsplit : (∑ i, if Λ < μ.atom i then ((μ.atom i : ℂ))⁻¹ • μ.weight i else 0) -
      (∑ i, if Λ < μ.atom i then ((μ.atom i : ℂ) - z)⁻¹ • μ.weight i else 0) =
      ∑ i, if Λ < μ.atom i then
        (((μ.atom i : ℂ))⁻¹ - ((μ.atom i : ℂ) - z)⁻¹) • μ.weight i else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    · rw [sub_smul]
    · simp
  rw [← hsplit, ← htail, hhead]
  abel

/-- Scalar estimate for the tail coefficients: for `λ > Λ > r ≥ ‖z‖`,
`|λ⁻¹ - (λ - z)⁻¹| ≤ (r/(Λ - r)) λ⁻¹`. -/
theorem norm_inv_sub_inv_le {lam Λ r : ℝ} (hΛ : Λ < lam) (hr : r < Λ) {z : ℂ}
    (hz : ‖z‖ ≤ r) :
    ‖((lam : ℂ))⁻¹ - ((lam : ℂ) - z)⁻¹‖ ≤ r / (Λ - r) * lam⁻¹ := by
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hlam : 0 < lam := lt_trans (lt_of_le_of_lt hr0 hr) hΛ
  have hΛr : 0 < Λ - r := sub_pos.mpr hr
  have hlamz : Λ - r ≤ ‖(lam : ℂ) - z‖ := by
    calc Λ - r ≤ lam - ‖z‖ := by linarith
      _ = ‖(lam : ℂ)‖ - ‖z‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
      _ ≤ ‖(lam : ℂ) - z‖ := norm_sub_norm_le _ _
  have hne : (lam : ℂ) - z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlamz
    linarith
  have hlamne : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hid : ((lam : ℂ))⁻¹ - ((lam : ℂ) - z)⁻¹ = -z / ((lam : ℂ) * ((lam : ℂ) - z)) := by
    field_simp
    ring
  rw [hid, norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
  rw [div_le_iff₀ (mul_pos hlam (lt_of_lt_of_le hΛr hlamz))]
  calc ‖z‖ ≤ r := hz
    _ = r / (Λ - r) * lam⁻¹ * (lam * (Λ - r)) := by
        field_simp
    _ ≤ r / (Λ - r) * lam⁻¹ * (lam * ‖(lam : ℂ) - z‖) := by
        gcongr

/-- **`eq:supp-memory-screen-error`.**  For `‖z‖ ≤ r < Λ`,
`‖F_{A,μ}(z) - F_{RG_Λ(A,μ)}(z)‖ ≤ r/(Λ - r) ‖Q_{>Λ}‖`. -/
theorem norm_dynamicFunction_sub_rg_le (A : E →L[ℂ] E) {Λ r : ℝ} (hr : r < Λ) {z : ℂ}
    (hz : ‖z‖ ≤ r) :
    ‖μ.dynamicFunction A z - (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 z‖ ≤
      r / (Λ - r) * ‖μ.headCorrection Λ‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hΛr : 0 < Λ - r := sub_pos.mpr hr
  rw [dynamicFunction_sub_rg]
  have hhead : μ.headCorrection Λ =
      ∑ i ∈ Finset.univ.filter (fun i => Λ < μ.atom i),
        (((μ.atom i)⁻¹ : ℝ) : ℂ) • μ.weight i := by
    unfold headCorrection
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hhead]
  apply norm_sum_smul_le_of_isPositive
  · intro i _
    exact μ.weight_pos i
  · intro i _
    exact (inv_pos.mpr (μ.atom_pos i)).le
  · exact div_nonneg hr0 hΛr.le
  · intro i hi
    rw [Finset.mem_filter] at hi
    exact norm_inv_sub_inv_le hi.2 hr hz

/-- **`thm:supp-memory-RG` (assembled, finite atomic tail measures).** -/
theorem memory_rg_semigroup (A : E →L[ℂ] E) :
    (∀ Λ : ℝ, (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 0 = μ.dynamicFunction A 0) ∧
      (∀ (Λ r : ℝ), r < Λ → ∀ z : ℂ, ‖z‖ ≤ r →
        ‖μ.dynamicFunction A z - (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 z‖ ≤
          r / (Λ - r) * ‖μ.headCorrection Λ‖) ∧
      (∀ Λ₁ Λ₂ : ℝ, Λ₂ ≤ Λ₁ → (μ.rg A Λ₁).2.rg (μ.rg A Λ₁).1 Λ₂ = μ.rg A Λ₂) :=
  ⟨fun Λ => μ.dynamicFunction_rg_zero A Λ,
    fun _ _ hr _ hz => μ.norm_dynamicFunction_sub_rg_le A hr hz,
    fun _ _ h => μ.rg_rg A h⟩

end FiniteAtomicTailMeasure

end MemoryRG
end RenewalGeometry
