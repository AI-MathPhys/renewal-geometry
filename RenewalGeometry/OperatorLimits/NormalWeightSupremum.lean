/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Normal weights on `B(H)` and suprema of increasing families

Mathlib has no theory of weights on von Neumann algebras.  This file records the elementary
part used for semifinite completions of finite-stage data:

* `NormalWeight H`: a weight on the positive cone of `B(H) = H →L[ℂ] H`, i.e. a map to
  `[0, ∞]` that is additive and positively homogeneous on positive operators, and **normal** in
  the sequential sense: for every increasing (Loewner order) sequence of positive operators
  `T_k` converging strongly to `S`, `φ S = sup_k φ T_k`;
* `NormalWeight.IsSemifinite`: finite on an increasing sequence of orthogonal projections
  converging strongly to the identity;
* `NormalWeight.iSupWeight`: **the supremum of an increasing sequence of normal weights is a
  normal weight** (additivity by monotone convergence of sums, normality by exchanging the two
  suprema), with `tendsto_iSupWeight` (the stage weights increase to it);
* `NormalWeight.vectorWeight`: the vector weight `T ↦ Re ⟪T v, v⟫` is normal (non-vacuity).

Normality is the sequential (σ-normal) form; on a separable Hilbert space this is the usual
normality of weights.
-/

open Filter Topology
open scoped InnerProductSpace NNReal ENNReal

noncomputable section

namespace RenewalGeometry

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `T_k ↑ S`: an increasing (Loewner order) sequence of positive operators converging strongly
to `S`. -/
def IsIncreasingStrongLimit (T : ℕ → H →L[ℂ] H) (S : H →L[ℂ] H) : Prop :=
  (∀ k, (T k).IsPositive) ∧ (∀ k, (T (k + 1) - T k).IsPositive) ∧
    ∀ x, Tendsto (fun k => T k x) atTop (𝓝 (S x))

/-- A **normal weight** on `B(H)`: additive and positively homogeneous on positive operators,
and sequentially normal (`φ (sup_k T_k) = sup_k φ T_k` for increasing strongly convergent
sequences of positive operators). -/
structure NormalWeight (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The weight. -/
  toFun : (H →L[ℂ] H) → ℝ≥0∞
  map_add' : ∀ T U, T.IsPositive → U.IsPositive → toFun (T + U) = toFun T + toFun U
  map_smul' : ∀ (c : ℝ≥0) T, T.IsPositive → toFun (((c : ℝ) : ℂ) • T) = c * toFun T
  normal' : ∀ T S, IsIncreasingStrongLimit T S → toFun S = ⨆ k, toFun (T k)

namespace NormalWeight

instance : CoeFun (NormalWeight H) (fun _ => (H →L[ℂ] H) → ℝ≥0∞) := ⟨NormalWeight.toFun⟩

@[ext] theorem ext {φ ψ : NormalWeight H} (h : ∀ T, φ T = ψ T) : φ = ψ := by
  cases φ
  cases ψ
  congr
  funext T
  exact h T

theorem map_add (φ : NormalWeight H) {T U : H →L[ℂ] H} (hT : T.IsPositive) (hU : U.IsPositive) :
    φ (T + U) = φ T + φ U := φ.map_add' T U hT hU

theorem map_smul (φ : NormalWeight H) (c : ℝ≥0) {T : H →L[ℂ] H} (hT : T.IsPositive) :
    φ (((c : ℝ) : ℂ) • T) = c * φ T := φ.map_smul' c T hT

theorem normal (φ : NormalWeight H) {T : ℕ → H →L[ℂ] H} {S : H →L[ℂ] H}
    (h : IsIncreasingStrongLimit T S) : φ S = ⨆ k, φ (T k) := φ.normal' T S h

/-- A weight is monotone on positive operators. -/
theorem mono (φ : NormalWeight H) {T U : H →L[ℂ] H} (hT : T.IsPositive)
    (hUT : (U - T).IsPositive) : φ T ≤ φ U := by
  have := φ.map_add hT hUT
  rw [add_sub_cancel] at this
  rw [this]
  exact le_self_add

/-- **Semifiniteness**: `φ` is finite on an increasing sequence of orthogonal projections
converging strongly to the identity. -/
def IsSemifinite (φ : NormalWeight H) : Prop :=
  ∃ P : ℕ → H →L[ℂ] H, (∀ n, (P n : H →ₗ[ℂ] H).IsSymmetricProjection) ∧
    (∀ n, P (n + 1) * P n = P n) ∧ (∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) ∧
    ∀ n, φ (P n) < ⊤

/-! ### Suprema of increasing sequences of normal weights -/

section iSup

variable (τ : ℕ → NormalWeight H) (hmono : ∀ n T, T.IsPositive → τ n T ≤ τ (n + 1) T)

theorem monotone_apply (hmono : ∀ n T, T.IsPositive → τ n T ≤ τ (n + 1) T)
    {T : H →L[ℂ] H} (hT : T.IsPositive) : Monotone fun n => τ n T :=
  monotone_nat_of_le_succ fun n => hmono n T hT

/-- **The supremum of an increasing sequence of normal weights is a normal weight.** -/
def iSupWeight : NormalWeight H where
  toFun T := ⨆ n, τ n T
  map_add' T U hT hU := by
    have h : ∀ n, τ n (T + U) = τ n T + τ n U := fun n => (τ n).map_add hT hU
    simp only [h]
    exact (ENNReal.iSup_add_iSup_of_monotone (monotone_apply τ hmono hT)
      (monotone_apply τ hmono hU)).symm
  map_smul' c T hT := by
    have h : ∀ n, τ n (((c : ℝ) : ℂ) • T) = c * τ n T := fun n => (τ n).map_smul c hT
    simp only [h]
    exact (ENNReal.mul_iSup _ _).symm
  normal' T S hTS := by
    have h : ∀ n, τ n S = ⨆ k, τ n (T k) := fun n => (τ n).normal hTS
    simp only [h]
    exact iSup_comm

theorem iSupWeight_apply (T : H →L[ℂ] H) : iSupWeight τ hmono T = ⨆ n, τ n T := rfl

/-- The stage weights increase to their supremum. -/
theorem tendsto_iSupWeight {T : H →L[ℂ] H} (hT : T.IsPositive) :
    Tendsto (fun n => τ n T) atTop (𝓝 (iSupWeight τ hmono T)) :=
  tendsto_atTop_iSup (monotone_apply τ hmono hT)

theorem le_iSupWeight (n : ℕ) (T : H →L[ℂ] H) : τ n T ≤ iSupWeight τ hmono T :=
  le_iSup (fun n => τ n T) n

/-- Uniqueness: a normal weight with `ψ T = sup_n τ_n T` is the supremum weight. -/
theorem eq_iSupWeight {ψ : NormalWeight H} (h : ∀ T, ψ T = ⨆ n, τ n T) :
    ψ = iSupWeight τ hmono :=
  NormalWeight.ext h

end iSup

/-! ### Vector weights -/

section vector

/-- The real part of `⟪T x, x⟫` for a positive `T` is nonnegative. -/
theorem re_inner_nonneg {T : H →L[ℂ] H} (hT : T.IsPositive) (x : H) :
    0 ≤ (⟪T x, x⟫_ℂ).re := hT.re_inner_nonneg_left x

/-- The vector weight `T ↦ Re ⟪T v, v⟫` (a normal state when `‖v‖ = 1`). -/
def vectorWeight (v : H) : NormalWeight H where
  toFun T := ENNReal.ofReal (⟪T v, v⟫_ℂ).re
  map_add' T U hT hU := by
    simp only [ContinuousLinearMap.add_apply, inner_add_left, Complex.add_re]
    exact ENNReal.ofReal_add (re_inner_nonneg hT v) (re_inner_nonneg hU v)
  map_smul' c T hT := by
    simp only [ContinuousLinearMap.smul_apply, inner_smul_left, Complex.conj_ofReal,
      Complex.re_ofReal_mul]
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg c), ENNReal.ofReal_coe_nnreal]
  normal' T S hTS := by
    obtain ⟨hpos, hinc, hlim⟩ := hTS
    have hmono : Monotone fun k => ENNReal.ofReal (⟪T k v, v⟫_ℂ).re := by
      refine monotone_nat_of_le_succ fun k => ENNReal.ofReal_le_ofReal ?_
      have := re_inner_nonneg (hinc k) v
      simp only [ContinuousLinearMap.sub_apply, inner_sub_left, Complex.sub_re] at this
      linarith
    have hl : Tendsto (fun k => ENNReal.ofReal (⟪T k v, v⟫_ℂ).re) atTop
        (𝓝 (ENNReal.ofReal (⟪S v, v⟫_ℂ).re)) := by
      apply ENNReal.tendsto_ofReal
      exact (Complex.continuous_re.tendsto _).comp ((hlim v).inner tendsto_const_nhds)
    exact tendsto_nhds_unique hl (tendsto_atTop_iSup hmono)

theorem vectorWeight_apply (v : H) (T : H →L[ℂ] H) :
    vectorWeight v T = ENNReal.ofReal (⟪T v, v⟫_ℂ).re := rfl

theorem vectorWeight_lt_top (v : H) (T : H →L[ℂ] H) : vectorWeight v T < ⊤ :=
  ENNReal.ofReal_lt_top

end vector

end NormalWeight

end RenewalGeometry
