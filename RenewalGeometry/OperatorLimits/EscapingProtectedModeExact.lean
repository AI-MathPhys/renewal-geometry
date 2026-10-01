/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.TransportedMoscoAsymptoticCompactness
import RenewalGeometry.OperatorLimits.VaryingHilbertWeakBoundedness
import RenewalGeometry.OperatorLimits.VaryingHilbertWeakNormLowerSemicontinuity

/-!
# A uniformly gapped protected mode can escape

Covers `cth:escaping-protected-mode` of the spacetime–gauge duality manuscript.

On `ℓ²(ℕ)` with standard basis `e_n`, protected lines `M_n = ℂ e_n` and forms
`q_n[x] = ‖(I − P_n) x‖²` (`eq:escaping-mode-form`), on the constant varying system
`J_n = id`:

* `Ker q_n = M_n`, `dim M_n = 1`, and the complementary gap is exactly one
  (`q_n[x] = 1 · ‖x‖²` on `M_nᗮ`, so `q_n[x] ≥ 1 · ‖(I − P_n)x‖²` with equality);
* `q_n` converges in the transported Mosco sense (`def:transported-mosco`, limit stage
  `ℓ²(ℕ)` embedded by the identity) to `q_∞[x] = ‖x‖²`, whose kernel is zero;
* the protected lines have no nonzero strong limit: any sequence `x_n ∈ M_n` converging
  strongly has limit `0`, so no unit vectors `u_n ∈ M_n` converge strongly — the basis
  transport hypothesis of `lem:protected-basis-transport` fails.
-/

open Filter Topology
open scoped ENNReal ComplexConjugate

noncomputable section

namespace RenewalGeometry.VaryingHilbert.EscapingProtectedMode

/-- The Hilbert space `ℓ²(ℕ)`. -/
abbrev L2 : Type := lp (fun _ : ℕ => ℂ) 2

/-- The standard basis vector `e_n`. -/
def basisVec (n : ℕ) : L2 := lp.single 2 n (1 : ℂ)

/-- The protected line `M_n = ℂ e_n`. -/
abbrev protectedLine (n : ℕ) : Submodule ℂ L2 := ℂ ∙ basisVec n

/-- The stage form `q_n[x] = ‖(I − P_n) x‖²` (`eq:escaping-mode-form`). -/
def escapingForm (n : ℕ) (x : L2) : ℝ≥0∞ :=
  ENNReal.ofReal (‖x - (protectedLine n).starProjection x‖ ^ 2)

/-- The limit form `q_∞[x] = ‖x‖²`. -/
def escapingLimitForm (x : L2) : ℝ≥0∞ := ENNReal.ofReal (‖x‖ ^ 2)

theorem inner_basisVec (n : ℕ) (x : L2) : inner ℂ (basisVec n) x = x n := by
  simp [basisVec, lp.inner_single_left]

theorem norm_basisVec (n : ℕ) : ‖basisVec n‖ = 1 := by
  simp [basisVec, lp.norm_single]

theorem starProjection_protectedLine (n : ℕ) (x : L2) :
    (protectedLine n).starProjection x = x n • basisVec n := by
  rw [Submodule.starProjection_singleton, norm_basisVec, inner_basisVec]
  simp

theorem escapingForm_eq (n : ℕ) (x : L2) :
    escapingForm n x = ENNReal.ofReal (‖x - x n • basisVec n‖ ^ 2) := by
  rw [escapingForm, starProjection_protectedLine]

/-- Coordinates of an `ℓ²` vector tend to zero. -/
theorem tendsto_coord_zero (x : L2) : Tendsto (fun n => x n) atTop (𝓝 0) := by
  have hsum : Summable fun i => ‖x i‖ ^ ((2 : ℝ≥0∞).toReal) :=
    (lp.memℓp x).summable (by norm_num)
  have h2 : Tendsto (fun i => ‖x i‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
    have := hsum.tendsto_atTop_zero
    simpa [Real.rpow_natCast] using this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hs := (Real.continuous_sqrt.tendsto 0).comp h2
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hs

/-- `|⟨e_n, x⟩| ≤ ‖x‖`. -/
theorem norm_coord_le (n : ℕ) (x : L2) : ‖x n‖ ≤ ‖x‖ := by
  have := norm_inner_le_norm (𝕜 := ℂ) (basisVec n) x
  rwa [inner_basisVec, norm_basisVec, one_mul] at this

/-- A bounded scalar sequence times the coordinates of a fixed vector tends to zero. -/
theorem tendsto_bounded_mul_coord (a : ℕ → ℂ) (C : ℝ) (ha : ∀ n, ‖a n‖ ≤ C) (y : L2) :
    Tendsto (fun n => a n * y n) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun n => ?_) ((tendsto_coord_zero y).norm.const_mul C |>.trans ?_)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _)
  · simp

/-- **A uniformly gapped protected mode can escape (`cth:escaping-protected-mode`).** -/
theorem escapingProtectedMode_exact :
    (∀ n x, escapingForm n x = 0 ↔ x ∈ protectedLine n) ∧
      (∀ n, Module.finrank ℂ (protectedLine n) = 1) ∧
      (∀ n x, ENNReal.ofReal (1 * ‖x - (protectedLine n).starProjection x‖ ^ 2) ≤
        escapingForm n x) ∧
      (∀ n, ∀ x ∈ (protectedLine n)ᗮ, escapingForm n x = ENNReal.ofReal (1 * ‖x‖ ^ 2)) ∧
      (constantSystem ℂ L2).TransportedMoscoConverges (LinearIsometry.id)
        escapingForm escapingLimitForm ∧
      (∀ x, escapingLimitForm x = 0 ↔ x = 0) ∧
      (∀ x : ℕ → L2, (∀ n, x n ∈ protectedLine n) → ∀ y, Tendsto x atTop (𝓝 y) → y = 0) ∧
      (∀ u : ℕ → L2, (∀ n, u n ∈ protectedLine n) → (∀ n, ‖u n‖ = 1) →
        ¬ ∃ y, Tendsto u atTop (𝓝 y)) := by
  have hkernel : ∀ n x, escapingForm n x = 0 ↔ x ∈ protectedLine n := by
    intro n x
    rw [escapingForm, ENNReal.ofReal_eq_zero]
    constructor
    · intro h
      have h2 : ‖x - (protectedLine n).starProjection x‖ ^ 2 = 0 := le_antisymm h (sq_nonneg _)
      have h3 : x - (protectedLine n).starProjection x = 0 :=
        norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
      rw [sub_eq_zero] at h3
      rw [h3]
      exact Submodule.starProjection_apply_mem _ x
    · intro hx
      rw [Submodule.starProjection_eq_self_iff.mpr hx, sub_self, norm_zero]
      norm_num
  have hlimzero : ∀ x : ℕ → L2, (∀ n, x n ∈ protectedLine n) → ∀ y,
      Tendsto x atTop (𝓝 y) → y = 0 := by
    intro x hx y hy
    obtain ⟨C, hC⟩ : ∃ C, ∀ n, ‖x n‖ ≤ C := by
      obtain ⟨C, -, hC⟩ := Metric.isBounded_range_of_tendsto x hy |>.exists_pos_norm_le
      exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
    have hrep : ∀ n, x n = (x n) n • basisVec n := by
      intro n
      conv_lhs => rw [← Submodule.starProjection_eq_self_iff.mpr (hx n)]
      exact starProjection_protectedLine n (x n)
    have hinner : Tendsto (fun n => inner ℂ (x n) y) atTop (𝓝 (inner ℂ y y)) :=
      hy.inner tendsto_const_nhds
    have hzero : Tendsto (fun n => inner ℂ (x n) y) atTop (𝓝 0) := by
      have hform : (fun n => inner ℂ (x n) y) = fun n => conj ((x n) n) * y n := by
        funext n
        conv_lhs => rw [hrep n]
        rw [inner_smul_left, inner_basisVec]
      rw [hform]
      exact tendsto_bounded_mul_coord _ C
        (fun n => by rw [RCLike.norm_conj]; exact (norm_coord_le n (x n)).trans (hC n)) y
    have hyy : inner ℂ y y = (0 : ℂ) := tendsto_nhds_unique hinner hzero
    exact inner_self_eq_zero.mp hyy
  refine ⟨hkernel, ?_, ?_, ?_, ?_, ?_, hlimzero, ?_⟩
  · intro n
    rw [finrank_span_singleton]
    intro h
    have := norm_basisVec n
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · intro n x
    rw [one_mul, escapingForm]
  · intro n x hx
    have hxn : x n = 0 := by
      rw [← inner_basisVec]
      exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp hx
    rw [escapingForm_eq, hxn, zero_smul, sub_zero, one_mul]
  · constructor
    · intro x B hx
      refine ⟨B, rfl, ?_⟩
      have hx' : ∀ y, Tendsto (fun n => inner ℂ (x n) y) atTop (𝓝 (inner ℂ B y)) :=
        (System.constantSystem_weaklyConverges_iff x B).mp hx
      obtain ⟨C, hC0, hC⟩ :=
        System.WeaklyConverges.exists_uniform_norm_bound (constantSystem ℂ L2) hx
      let z : ℕ → L2 := fun n => x n - (x n) n • basisVec n
      have hzweak : (constantSystem ℂ L2).WeaklyConverges z B := by
        rw [System.constantSystem_weaklyConverges_iff]
        intro y
        have hform : (fun n => inner ℂ (z n) y) =
            fun n => inner ℂ (x n) y - conj ((x n) n) * y n := by
          funext n
          simp only [z, inner_sub_left, inner_smul_left, inner_basisVec]
        rw [hform]
        simpa using (hx' y).sub (tendsto_bounded_mul_coord _ C
          (fun n => by rw [RCLike.norm_conj]; exact (norm_coord_le n (x n)).trans (hC n)) y)
      have hzbound : ∀ n, ‖z n‖ ≤ 2 * C := by
        intro n
        calc ‖z n‖ ≤ ‖x n‖ + ‖(x n) n • basisVec n‖ := norm_sub_le _ _
          _ = ‖x n‖ + ‖(x n) n‖ := by rw [norm_smul, norm_basisVec, mul_one]
          _ ≤ C + C := add_le_add (hC n) ((norm_coord_le n (x n)).trans (hC n))
          _ = 2 * C := by ring
      have hreal : ‖B‖ ^ 2 ≤ liminf (fun n => ‖z n‖ ^ 2) atTop :=
        System.WeaklyConverges.norm_sq_le_liminf (constantSystem ℂ L2) hzweak (2 * C) hzbound
      have hbddAbove : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖z n‖ ^ 2) :=
        isBoundedUnder_of ⟨(2 * C) ^ 2, fun n =>
          pow_le_pow_left₀ (norm_nonneg _) (hzbound n) 2⟩
      have hbddBelow : IsBoundedUnder (· ≥ ·) atTop (fun n => ‖z n‖ ^ 2) :=
        isBoundedUnder_of ⟨0, fun n => sq_nonneg _⟩
      have hmap := (ENNReal.ofReal_mono : Monotone ENNReal.ofReal).map_liminf_of_continuousAt
        (fun n => ‖z n‖ ^ 2) ENNReal.continuous_ofReal.continuousAt
        hbddAbove.isCobounded_flip hbddBelow
      calc escapingLimitForm B = ENNReal.ofReal (‖B‖ ^ 2) := rfl
        _ ≤ ENNReal.ofReal (liminf (fun n => ‖z n‖ ^ 2) atTop) := ENNReal.ofReal_le_ofReal hreal
        _ = liminf (ENNReal.ofReal ∘ fun n => ‖z n‖ ^ 2) atTop := hmap
        _ = liminf (fun n => escapingForm n (x n)) atTop := by
          congr 1
          funext n
          simp only [Function.comp_apply, z, escapingForm_eq]
    · intro A _
      refine ⟨fun _ => A, ?_, ?_⟩
      · rw [System.constantSystem_stronglyConverges_iff]
        exact tendsto_const_nhds
      · simp only [escapingForm_eq, escapingLimitForm]
        apply ENNReal.tendsto_ofReal
        apply Tendsto.pow
        apply Tendsto.norm
        have hsmall : Tendsto (fun n => A n • basisVec n) atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          simp only [norm_smul, norm_basisVec, mul_one]
          exact (tendsto_coord_zero A).norm.trans (by simp)
        simpa using (tendsto_const_nhds (x := A)).sub hsmall
  · intro x
    rw [escapingLimitForm, ENNReal.ofReal_eq_zero]
    constructor
    · intro h
      have h2 : ‖x‖ ^ 2 = 0 := le_antisymm h (sq_nonneg _)
      exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
    · intro h
      simp [h]
  · intro u hu hnorm ⟨y, hy⟩
    have hy0 := hlimzero u hu y hy
    have hn : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖y‖) := hy.norm
    simp only [hnorm, hy0, norm_zero] at hn
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hn)

end RenewalGeometry.VaryingHilbert.EscapingProtectedMode
