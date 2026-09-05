/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FinitePinskerExact

/-!
# KL domination of the affine and quadratic residuals

Exact encoding of `cor:SMYM-affine-KL-control` (CY.13g–CY.13h).

Faithful selector rows `q g : L → Fin m → ℝ` (strictly positive probability vectors on
the response atoms `z i`) have affine coordinates `θ^q_ℓ = ∑ q_ℓ,i (z_i - z_*)`.

* `affine_residual_le` (CY.13g): `Δ_aff(q, g) = ∑ μ_ℓ ‖θ^q_ℓ - θ^g_ℓ‖² ≤ 2 B² ∑ μ_ℓ KL(q_ℓ ‖ g_ℓ)`
  when `‖z_i - z_*‖ ≤ B`, from `‖θ^q - θ^g‖ ≤ B ‖q - g‖₁` and Pinsker;
* `cross_block_bound` / `response_block_bound` (CY.13h): with one common source profile
  `s_ℓ`, the quadratic blocks `C_σ v = ∑ μ_ℓ ⟪t^σ_ℓ, v⟫ s_ℓ` and `D_σ v = ∑ μ_ℓ ⟪t^σ_ℓ, v⟫ t^σ_ℓ`
  satisfy `‖(C_q - C_g) v‖ ≤ M_S √Δ ‖v‖` and `‖(D_q - D_g) v‖ ≤ 2 M_T √Δ ‖v‖`
  (Cauchy–Schwarz), where `M_S² = ∑ μ_ℓ ‖s_ℓ‖²` and `M_T` bounds every `‖t^σ_ℓ‖`.
-/

open Finset Real NCG.FinitePinsker
open scoped RealInnerProductSpace

namespace NCG
namespace SMYMAffineKLControl

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ} (z : Fin m → E) (zs : E)

/-- The affine coordinate `θ^q = ∑ q_i (z_i - z_*)` of a selector row. -/
noncomputable def affineCoord (q : Fin m → ℝ) : E := ∑ i, q i • (z i - zs)

theorem affineCoord_sub (q g : Fin m → ℝ) :
    affineCoord z zs q - affineCoord z zs g = ∑ i, (q i - g i) • (z i - zs) := by
  unfold affineCoord
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sub_smul]

/-- `‖θ^q - θ^g‖ ≤ B ‖q - g‖₁`. -/
theorem norm_affineCoord_sub_le {B : ℝ} (hB : ∀ i, ‖z i - zs‖ ≤ B) (q g : Fin m → ℝ) :
    ‖affineCoord z zs q - affineCoord z zs g‖ ≤ B * tv q g := by
  rw [affineCoord_sub]
  refine (norm_sum_le _ _).trans ?_
  unfold tv
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB i) (abs_nonneg _)

/-- `‖θ^q - θ^g‖² ≤ 2 B² KL(q ‖ g)`. -/
theorem sq_norm_affineCoord_sub_le {B : ℝ} (hB : ∀ i, ‖z i - zs‖ ≤ B) {q g : Fin m → ℝ}
    (hq : ∀ i, 0 < q i) (hg : ∀ i, 0 < g i) (hq1 : ∑ i, q i = 1) (hg1 : ∑ i, g i = 1) :
    ‖affineCoord z zs q - affineCoord z zs g‖ ^ 2 ≤ 2 * B ^ 2 * kl q g := by
  have h1 := norm_affineCoord_sub_le z zs hB q g
  have h2 := pinsker hq hg hq1 hg1
  have h3 : ‖affineCoord z zs q - affineCoord z zs g‖ ^ 2 ≤ (B * tv q g) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ‖affineCoord z zs q - affineCoord z zs g‖ ^ 2 ≤ (B * tv q g) ^ 2 := h3
    _ = B ^ 2 * tv q g ^ 2 := by ring
    _ ≤ B ^ 2 * (2 * kl q g) := mul_le_mul_of_nonneg_left h2 (sq_nonneg B)
    _ = 2 * B ^ 2 * kl q g := by ring

variable {L : Type*} [Fintype L]

/-- **(CY.13g)**: the affine residual `Δ_aff(q, g) = ∑ μ_ℓ ‖θ^q_ℓ - θ^g_ℓ‖²`. -/
noncomputable def affineResidual (μ : L → ℝ) (q g : L → Fin m → ℝ) : ℝ :=
  ∑ ℓ, μ ℓ * ‖affineCoord z zs (q ℓ) - affineCoord z zs (g ℓ)‖ ^ 2

/-- **(CY.13g)**: `Δ_aff(q, g) ≤ 2 B² ∑ μ_ℓ KL(q_ℓ ‖ g_ℓ)`. -/
theorem affine_residual_le {B : ℝ} (hB : ∀ i, ‖z i - zs‖ ≤ B) (μ : L → ℝ) (hμ : ∀ ℓ, 0 ≤ μ ℓ)
    {q g : L → Fin m → ℝ} (hq : ∀ ℓ i, 0 < q ℓ i) (hg : ∀ ℓ i, 0 < g ℓ i)
    (hq1 : ∀ ℓ, ∑ i, q ℓ i = 1) (hg1 : ∀ ℓ, ∑ i, g ℓ i = 1) :
    affineResidual z zs μ q g ≤ 2 * B ^ 2 * ∑ ℓ, μ ℓ * kl (q ℓ) (g ℓ) := by
  unfold affineResidual
  rw [mul_sum]
  refine sum_le_sum fun ℓ _ => ?_
  have := sq_norm_affineCoord_sub_le z zs hB (hq ℓ) (hg ℓ) (hq1 ℓ) (hg1 ℓ)
  calc μ ℓ * ‖affineCoord z zs (q ℓ) - affineCoord z zs (g ℓ)‖ ^ 2
      ≤ μ ℓ * (2 * B ^ 2 * kl (q ℓ) (g ℓ)) := mul_le_mul_of_nonneg_left this (hμ ℓ)
    _ = 2 * B ^ 2 * (μ ℓ * kl (q ℓ) (g ℓ)) := by ring

/-! ### The quadratic blocks -/

/-- Cauchy–Schwarz in the form `∑ μ a b ≤ √(∑ μ a²) √(∑ μ b²)` for `μ ≥ 0`. -/
theorem weighted_cauchy_schwarz (μ a b : L → ℝ) (hμ : ∀ ℓ, 0 ≤ μ ℓ) :
    ∑ ℓ, μ ℓ * (a ℓ * b ℓ) ≤ Real.sqrt (∑ ℓ, μ ℓ * a ℓ ^ 2) * Real.sqrt (∑ ℓ, μ ℓ * b ℓ ^ 2) := by
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun ℓ => Real.sqrt (μ ℓ) * a ℓ)
    (fun ℓ => Real.sqrt (μ ℓ) * b ℓ)
  have e1 : ∑ ℓ, (Real.sqrt (μ ℓ) * a ℓ) * (Real.sqrt (μ ℓ) * b ℓ) = ∑ ℓ, μ ℓ * (a ℓ * b ℓ) := by
    refine sum_congr rfl fun ℓ _ => ?_
    have := Real.mul_self_sqrt (hμ ℓ)
    calc (Real.sqrt (μ ℓ) * a ℓ) * (Real.sqrt (μ ℓ) * b ℓ)
        = (Real.sqrt (μ ℓ) * Real.sqrt (μ ℓ)) * (a ℓ * b ℓ) := by ring
      _ = _ := by rw [this]
  have e2 : ∑ ℓ, (Real.sqrt (μ ℓ) * a ℓ) ^ 2 = ∑ ℓ, μ ℓ * a ℓ ^ 2 := by
    refine sum_congr rfl fun ℓ _ => ?_
    rw [mul_pow, Real.sq_sqrt (hμ ℓ)]
  have e3 : ∑ ℓ, (Real.sqrt (μ ℓ) * b ℓ) ^ 2 = ∑ ℓ, μ ℓ * b ℓ ^ 2 := by
    refine sum_congr rfl fun ℓ _ => ?_
    rw [mul_pow, Real.sq_sqrt (hμ ℓ)]
  rw [e1, e2, e3] at hcs
  rw [← Real.sqrt_mul (sum_nonneg fun ℓ _ => mul_nonneg (hμ ℓ) (sq_nonneg _))]
  exact Real.le_sqrt_of_sq_le hcs

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The cross block `C v = ∑ μ_ℓ ⟪t_ℓ, v⟫ s_ℓ` (the map `v ↦ ∑ μ s t^* v`). -/
noncomputable def crossBlock (μ : L → ℝ) (s : L → F) (t : L → E) (v : E) : F :=
  ∑ ℓ, (μ ℓ * ⟪t ℓ, v⟫) • s ℓ

/-- The response block `D v = ∑ μ_ℓ ⟪t_ℓ, v⟫ t_ℓ`. -/
noncomputable def responseBlock (μ : L → ℝ) (t : L → E) (v : E) : E :=
  ∑ ℓ, (μ ℓ * ⟪t ℓ, v⟫) • t ℓ

/-- **(CY.13h)**: `‖(C_q - C_g) v‖ ≤ M_S √Δ_aff ‖v‖` with `M_S² = ∑ μ_ℓ ‖s_ℓ‖²`. -/
theorem cross_block_bound (μ : L → ℝ) (hμ : ∀ ℓ, 0 ≤ μ ℓ) (s : L → F) (q g : L → Fin m → ℝ)
    (v : E) :
    ‖crossBlock μ s (fun ℓ => affineCoord z zs (q ℓ)) v
        - crossBlock μ s (fun ℓ => affineCoord z zs (g ℓ)) v‖
      ≤ Real.sqrt (∑ ℓ, μ ℓ * ‖s ℓ‖ ^ 2) * Real.sqrt (affineResidual z zs μ q g) * ‖v‖ := by
  set tq := fun ℓ => affineCoord z zs (q ℓ) with htq
  set tg := fun ℓ => affineCoord z zs (g ℓ) with htg
  have e : crossBlock μ s tq v - crossBlock μ s tg v
      = ∑ ℓ, (μ ℓ * ⟪tq ℓ - tg ℓ, v⟫) • s ℓ := by
    unfold crossBlock
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun ℓ _ => ?_
    rw [inner_sub_left, mul_sub, sub_smul]
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ ℓ, ‖(μ ℓ * ⟪tq ℓ - tg ℓ, v⟫) • s ℓ‖
      ≤ μ ℓ * (‖s ℓ‖ * ‖tq ℓ - tg ℓ‖) * ‖v‖ := by
    intro ℓ
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hμ ℓ)]
    have := abs_real_inner_le_norm (tq ℓ - tg ℓ) v
    have hμℓ := hμ ℓ
    calc μ ℓ * |⟪tq ℓ - tg ℓ, v⟫| * ‖s ℓ‖
        ≤ μ ℓ * (‖tq ℓ - tg ℓ‖ * ‖v‖) * ‖s ℓ‖ := by
          gcongr
      _ = μ ℓ * (‖s ℓ‖ * ‖tq ℓ - tg ℓ‖) * ‖v‖ := by ring
  refine (sum_le_sum fun ℓ _ => hterm ℓ).trans ?_
  rw [← sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
  have := weighted_cauchy_schwarz μ (fun ℓ => ‖s ℓ‖) (fun ℓ => ‖tq ℓ - tg ℓ‖) hμ
  unfold affineResidual
  exact this

/-- **(CY.13h)**: `‖(D_q - D_g) v‖ ≤ 2 M_T √Δ_aff ‖v‖` when `∑ μ = 1` and `‖t^σ_ℓ‖ ≤ M_T`. -/
theorem response_block_bound (μ : L → ℝ) (hμ : ∀ ℓ, 0 ≤ μ ℓ) (hμ1 : ∑ ℓ, μ ℓ = 1)
    (q g : L → Fin m → ℝ) {MT : ℝ}
    (hT : ∀ ℓ, ‖affineCoord z zs (q ℓ)‖ ≤ MT ∧ ‖affineCoord z zs (g ℓ)‖ ≤ MT) (v : E) :
    ‖responseBlock μ (fun ℓ => affineCoord z zs (q ℓ)) v
        - responseBlock μ (fun ℓ => affineCoord z zs (g ℓ)) v‖
      ≤ 2 * MT * Real.sqrt (affineResidual z zs μ q g) * ‖v‖ := by
  set tq := fun ℓ => affineCoord z zs (q ℓ) with htq
  set tg := fun ℓ => affineCoord z zs (g ℓ) with htg
  have e : responseBlock μ tq v - responseBlock μ tg v
      = ∑ ℓ, ((μ ℓ * ⟪tq ℓ - tg ℓ, v⟫) • tq ℓ + (μ ℓ * ⟪tg ℓ, v⟫) • (tq ℓ - tg ℓ)) := by
    unfold responseBlock
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun ℓ _ => ?_
    rw [inner_sub_left, mul_sub, sub_smul, smul_sub]
    abel
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ ℓ, ‖(μ ℓ * ⟪tq ℓ - tg ℓ, v⟫) • tq ℓ + (μ ℓ * ⟪tg ℓ, v⟫) • (tq ℓ - tg ℓ)‖
      ≤ μ ℓ * (2 * MT * ‖tq ℓ - tg ℓ‖) * ‖v‖ := by
    intro ℓ
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (hμ ℓ)]
    have h1 := abs_real_inner_le_norm (tq ℓ - tg ℓ) v
    have h2 := abs_real_inner_le_norm (tg ℓ) v
    have hq := (hT ℓ).1
    have hg := (hT ℓ).2
    have hv := norm_nonneg v
    have hd := norm_nonneg (tq ℓ - tg ℓ)
    have hμℓ := hμ ℓ
    have hMT : 0 ≤ MT := le_trans (norm_nonneg _) hq
    calc μ ℓ * |⟪tq ℓ - tg ℓ, v⟫| * ‖tq ℓ‖ + μ ℓ * |⟪tg ℓ, v⟫| * ‖tq ℓ - tg ℓ‖
        ≤ μ ℓ * (‖tq ℓ - tg ℓ‖ * ‖v‖) * MT + μ ℓ * (‖tg ℓ‖ * ‖v‖) * ‖tq ℓ - tg ℓ‖ := by
          gcongr
      _ ≤ μ ℓ * (‖tq ℓ - tg ℓ‖ * ‖v‖) * MT + μ ℓ * (MT * ‖v‖) * ‖tq ℓ - tg ℓ‖ := by
          gcongr
      _ = μ ℓ * (2 * MT * ‖tq ℓ - tg ℓ‖) * ‖v‖ := by ring
  refine (sum_le_sum fun ℓ _ => hterm ℓ).trans ?_
  rw [← sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
  have hcs := weighted_cauchy_schwarz μ (fun _ => (1 : ℝ)) (fun ℓ => ‖tq ℓ - tg ℓ‖) hμ
  simp only [one_pow, mul_one, one_mul, hμ1, Real.sqrt_one] at hcs
  have hsum : ∑ ℓ, μ ℓ * (2 * MT * ‖tq ℓ - tg ℓ‖) = 2 * MT * ∑ ℓ, μ ℓ * ‖tq ℓ - tg ℓ‖ := by
    rw [mul_sum]
    refine sum_congr rfl fun ℓ _ => ?_
    ring
  rw [hsum]
  unfold affineResidual
  by_cases hL : Nonempty L
  · have hMT : 0 ≤ MT := le_trans (norm_nonneg _) (hT (Classical.arbitrary L)).1
    exact mul_le_mul_of_nonneg_left hcs (by positivity)
  · rw [not_nonempty_iff] at hL
    simp

end SMYMAffineKLControl
end NCG
