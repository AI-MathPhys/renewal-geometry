/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.FrozenWilsonSymbolExact
import RenewalGeometry.Analysis.VectorLineTaylorRemainderBound

/-!
# Smooth-core consistency of the frozen Wilson operator

Paper `predictive_spectral_geometry`, label `lem:supp-general-core`
(`eq:supp-general-core`, `eq:Wilson-core-smallness`), in the frozen chart surrogate.

The lattice operator is the frozen (constant-coefficient, trivial spin transport, constant
density) doubled Wilson operator `frozenWilson h ϖ c Γ` of `FrozenWilsonSymbolExact.lean` on
lattice sections `ℤ^d → ℂ^N`, applied to the point samples `S_h ψ (x) = ψ(h x)` of a smooth
`ψ : ℝ^d → ℂ^N`; the continuum operator is the frozen doubled Dirac operator
`D̂_0 ψ = Σ_j ĉ^j (-i ∂_j ψ)` (`frozenDirac`).  Sobolev norms are replaced by `C^k` bounds
`‖D^k ψ‖ ≤ M_k`, and the `L²` norm by the pointwise (sup) norm.

* `norm_wilsonTerm_sample_le` (**`eq:Wilson-core-smallness`**, `C²` form):
  `‖W_h S_h ψ (x)‖ ≤ d M₂ h`.
* `norm_frozenWilson_sample_sub_frozenDirac_le` (**`eq:supp-general-core`**, `C³` form):
  `‖(D̃^W_h S_h ψ)(x) - (D̂_0 ψ)(h x)‖ ≤ C h (M₂ + M₃)` for `0 < h ≤ 1`, with `C` depending only
  on the Clifford coefficients and the Wilson parameter.
-/

open Finset Matrix
open RenewalGeometry.FrozenWilsonSymbol RenewalGeometry.VectorLineTaylor

namespace RenewalGeometry.FrozenWilsonCoreConsistency

variable {d N : ℕ}

/-! ### Sampling and lines -/

/-- Continuum coordinates `h x` of the lattice point `x`. -/
def latticePoint (h : ℝ) (x : Fin d → ℤ) : Fin d → ℝ := fun j => h * (x j : ℝ)

/-- Point sampling `S_h ψ (x) = ψ(h x)`. -/
def sample (h : ℝ) (ψ : (Fin d → ℝ) → (Fin N → ℂ)) : LatticeSection d N :=
  fun x => ψ (latticePoint h x)

/-- The coordinate direction `e_j`. -/
def dir (j : Fin d) : Fin d → ℝ := Pi.single j 1

theorem norm_dir (j : Fin d) : ‖dir j‖ = 1 := by
  simp [dir, Pi.norm_single]

theorem latticePoint_add_single (h : ℝ) (x : Fin d → ℤ) (j : Fin d) :
    latticePoint h (x + Pi.single j 1) = latticePoint h x + h • dir j := by
  funext i
  simp only [latticePoint, dir, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add]
  by_cases hij : i = j
  · subst hij; simp; ring
  · simp [hij]

theorem latticePoint_sub_single (h : ℝ) (x : Fin d → ℤ) (j : Fin d) :
    latticePoint h (x - Pi.single j 1) = latticePoint h x + (-h) • dir j := by
  funext i
  simp only [latticePoint, dir, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    Int.cast_sub]
  by_cases hij : i = j
  · subst hij; simp; ring
  · simp [hij]

theorem shift_sample (h : ℝ) (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (j : Fin d) (x : Fin d → ℤ) :
    shift j (sample h ψ) x = lineMap ψ (latticePoint h x) (dir j) h := by
  simp [shift, sample, lineMap, latticePoint_add_single]

theorem shiftAdj_sample (h : ℝ) (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (j : Fin d) (x : Fin d → ℤ) :
    shiftAdj j (sample h ψ) x = lineMap ψ (latticePoint h x) (dir j) (-h) := by
  simp [shiftAdj, sample, lineMap, latticePoint_sub_single]

theorem sample_eq_lineMap_zero (h : ℝ) (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (j : Fin d)
    (x : Fin d → ℤ) : sample h ψ x = lineMap ψ (latticePoint h x) (dir j) 0 := by
  simp [sample, lineMap]

/-! ### The frozen continuum operator -/

/-- The frozen continuum doubled Dirac operator `D̂_0 ψ (y) = Σ_j ĉ^j (-i ∂_j ψ)(y)`, with the
partial derivatives as directional derivatives `lineDeriv ℝ ψ y e_j`. -/
noncomputable def frozenDirac (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (y : Fin d → ℝ) : Fin N → ℂ :=
  ∑ j, c j *ᵥ ((-Complex.I) • lineDeriv ℝ ψ y (dir j))

/-- For differentiable `ψ` the directional derivatives are `fderiv ℝ ψ y e_j`. -/
theorem frozenDirac_eq_fderiv (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (y : Fin d → ℝ) (hψ : DifferentiableAt ℝ ψ y) :
    frozenDirac c ψ y = ∑ j, c j *ᵥ ((-Complex.I) • fderiv ℝ ψ y (dir j)) := by
  unfold frozenDirac
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hψ.lineDeriv_eq_fderiv]

/-! ### Matrix bound -/

/-- The crude entrywise bound `Σ_{i,k} ‖M i k‖` on a matrix. -/
noncomputable def matBound (M : Matrix (Fin N) (Fin N) ℂ) : ℝ := ∑ i, ∑ k, ‖M i k‖

theorem matBound_nonneg (M : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ matBound M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- `‖M v‖ ≤ (Σ_{i,k} ‖M i k‖) ‖v‖` in the sup norm. -/
theorem norm_mulVec_le (M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    ‖M *ᵥ v‖ ≤ matBound M * ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (matBound_nonneg M) (norm_nonneg v))]
  intro i
  calc ‖(M *ᵥ v) i‖ = ‖∑ k, M i k * v k‖ := rfl
    _ ≤ ∑ k, ‖M i k * v k‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖M i k‖ * ‖v‖ := by
        gcongr with k
        rw [norm_mul]
        gcongr
        exact norm_le_pi_norm v k
    _ = (∑ k, ‖M i k‖) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ matBound M * ‖v‖ := by
        gcongr
        exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (Finset.mem_univ i)

/-! ### The two Taylor estimates on samples -/

/-- The symmetric difference of the samples along `e_j` in line form. -/
theorem symmetricDifference_sample (h : ℝ) (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (j : Fin d)
    (x : Fin d → ℤ) :
    symmetricDifference h j (sample h ψ) x =
      (2 * Complex.I * (h : ℂ))⁻¹ • (lineMap ψ (latticePoint h x) (dir j) h -
        lineMap ψ (latticePoint h x) (dir j) (-h)) := by
  simp [symmetricDifference, shift_sample, shiftAdj_sample]

/-- **Centered-difference consistency.** `‖P_j S_h ψ (x) - (-i ∂_j ψ)(h x)‖ ≤ M₃ h² / 2`. -/
theorem norm_symmetricDifference_sample_sub_le (h : ℝ) (hh : 0 < h)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (hψ : ContDiff ℝ 3 ψ) (M₃ : ℝ)
    (hM3 : ∀ y, ‖iteratedFDeriv ℝ 3 ψ y‖ ≤ M₃) (j : Fin d) (x : Fin d → ℤ) :
    ‖symmetricDifference h j (sample h ψ) x -
        (-Complex.I) • lineDeriv ℝ ψ (latticePoint h x) (dir j)‖ ≤ M₃ * h ^ 2 / 2 := by
  set φ := lineMap ψ (latticePoint h x) (dir j)
  have hφ : ContDiff ℝ 3 φ := contDiff_lineMap hψ _ _
  have hMφ : ∀ t, ‖iteratedDeriv 3 φ t‖ ≤ M₃ := by
    intro t
    have := norm_iteratedDeriv_lineMap_le_of_bound hψ (le_refl 3) hM3 (latticePoint h x)
      (dir j) t
    rwa [norm_dir, one_pow, mul_one] at this
  have hcoef : (2 * Complex.I * (h : ℂ))⁻¹ = (-Complex.I) * (((2 * h)⁻¹ : ℝ) : ℂ) := by
    rw [show (2 * Complex.I * (h : ℂ)) = Complex.I * ((2 * h : ℝ) : ℂ) by push_cast; ring,
      mul_inv, Complex.inv_I, Complex.ofReal_inv]
  have hrw : symmetricDifference h j (sample h ψ) x -
      (-Complex.I) • lineDeriv ℝ ψ (latticePoint h x) (dir j) =
      (-Complex.I) • ((2 * h)⁻¹ • (lineMap ψ (latticePoint h x) (dir j) h -
        lineMap ψ (latticePoint h x) (dir j) (-h)) -
        iteratedDeriv 1 (lineMap ψ (latticePoint h x) (dir j)) 0) := by
    rw [symmetricDifference_sample, hcoef, ← iteratedDeriv_one_lineMap_zero_eq_lineDeriv,
      RCLike.real_smul_eq_coe_smul (K := ℂ) (2 * h)⁻¹, smul_sub (-Complex.I), mul_smul]
    rfl
  rw [hrw, norm_smul, norm_neg, Complex.norm_I, one_mul]
  exact norm_centered_difference_sub_deriv_le _ M₃ hφ hMφ hh

/-- **`eq:Wilson-core-smallness`** (`C²` form): `‖W_h S_h ψ (x)‖ ≤ d M₂ h`. -/
theorem norm_wilsonTerm_sample_le (h : ℝ) (hh : 0 < h)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (hψ : ContDiff ℝ 2 ψ) (M₂ : ℝ)
    (hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 ψ y‖ ≤ M₂) (x : Fin d → ℤ) :
    ‖wilsonTerm h (sample h ψ) x‖ ≤ d * M₂ * h := by
  have hterm : ∀ j : Fin d,
      ‖(2 : ℂ) • sample h ψ x - shift j (sample h ψ) x - shiftAdj j (sample h ψ) x‖ ≤
        2 * M₂ * h ^ 2 := by
    intro j
    set φ := lineMap ψ (latticePoint h x) (dir j)
    have hφ : ContDiff ℝ 2 φ := contDiff_lineMap hψ _ _
    have hMφ : ∀ t, ‖iteratedDeriv 2 φ t‖ ≤ M₂ := by
      intro t
      have := norm_iteratedDeriv_lineMap_le_of_bound hψ (le_refl 2) hM2 (latticePoint h x)
        (dir j) t
      rwa [norm_dir, one_pow, mul_one] at this
    have hrw : (2 : ℂ) • sample h ψ x - shift j (sample h ψ) x - shiftAdj j (sample h ψ) x =
        (2 : ℝ) • lineMap ψ (latticePoint h x) (dir j) 0 -
          lineMap ψ (latticePoint h x) (dir j) h - lineMap ψ (latticePoint h x) (dir j) (-h) := by
      rw [shift_sample, shiftAdj_sample, sample_eq_lineMap_zero h ψ j,
        RCLike.real_smul_eq_coe_smul (K := ℂ)]
      norm_num
    rw [hrw]
    exact norm_second_difference_le _ M₂ hφ hMφ hh.le
  have hcoef : ‖(2 * (h : ℂ))⁻¹‖ = (2 * h)⁻¹ := by
    rw [norm_inv]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖wilsonTerm h (sample h ψ) x‖
      = (2 * h)⁻¹ * ‖∑ j, ((2 : ℂ) • sample h ψ x - shift j (sample h ψ) x
          - shiftAdj j (sample h ψ) x)‖ := by
        rw [wilsonTerm, norm_smul, hcoef]
    _ ≤ (2 * h)⁻¹ * ∑ j : Fin d, (2 * M₂ * h ^ 2) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
    _ = d * M₂ * h := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, inv_mul_eq_div,
          div_eq_iff (by positivity)]
        ring

/-! ### The consistency estimate -/

/-- The frozen Wilson operator on any section, with the symmetrised Clifford term collapsed:
`D̃^W ψ = Σ_j ĉ^j P_j ψ + ϖ Γ W ψ`. -/
theorem frozenWilson_eq (h ϖ : ℝ) (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (ψ : LatticeSection d N) (x : Fin d → ℤ) :
    frozenWilson h ϖ c Γ ψ x =
      ∑ j, c j *ᵥ symmetricDifference h j ψ x + (ϖ : ℂ) • Γ *ᵥ wilsonTerm h ψ x := by
  unfold frozenWilson
  rw [show (fun j => matMul (c j) (symmetricDifference h j ψ) x +
      symmetricDifference h j (matMul (c j) ψ) x) =
      fun j => (2 : ℂ) • (c j *ᵥ symmetricDifference h j ψ x) from by
    funext j
    rw [symmetricDifference_matMul, two_smul]
    rfl]
  rw [← Finset.smul_sum, smul_smul]
  norm_num
  rfl

/-- The consistency constant `C = (Σ_j ‖ĉ^j‖)/2 + |ϖ| ‖Γ‖ d`. -/
noncomputable def consistencyConstant (ϖ : ℝ) (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (∑ j, matBound (c j)) / 2 + |ϖ| * matBound Γ * d

/-- **`eq:supp-general-core`** (frozen chart, `C³` form, exact constants):
`‖(D̃^W_h S_h ψ)(x) - (D̂_0 ψ)(h x)‖ ≤ h [(Σ_j ‖ĉ^j‖) M₃ h / 2 + |ϖ| ‖Γ‖ d M₂]`. -/
theorem norm_frozenWilson_sample_sub_frozenDirac_le' (h ϖ : ℝ) (hh : 0 < h)
    (c : Fin d → Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin N) (Fin N) ℂ)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (hψ : ContDiff ℝ 3 ψ) (M₂ M₃ : ℝ)
    (hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 ψ y‖ ≤ M₂) (hM3 : ∀ y, ‖iteratedFDeriv ℝ 3 ψ y‖ ≤ M₃)
    (x : Fin d → ℤ) :
    ‖frozenWilson h ϖ c Γ (sample h ψ) x - frozenDirac c ψ (latticePoint h x)‖ ≤
      h * ((∑ j, matBound (c j)) * (M₃ * h / 2) + |ϖ| * matBound Γ * (d * M₂)) := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have hrw : frozenWilson h ϖ c Γ (sample h ψ) x - frozenDirac c ψ (latticePoint h x) =
      ∑ j, c j *ᵥ (symmetricDifference h j (sample h ψ) x -
        (-Complex.I) • lineDeriv ℝ ψ (latticePoint h x) (dir j)) +
      (ϖ : ℂ) • Γ *ᵥ wilsonTerm h (sample h ψ) x := by
    rw [frozenWilson_eq, frozenDirac]
    simp only [Matrix.mulVec_sub, Finset.sum_sub_distrib]
    abel
  rw [hrw]
  calc ‖∑ j, c j *ᵥ (symmetricDifference h j (sample h ψ) x -
        (-Complex.I) • lineDeriv ℝ ψ (latticePoint h x) (dir j)) +
        (ϖ : ℂ) • Γ *ᵥ wilsonTerm h (sample h ψ) x‖
      ≤ ‖∑ j, c j *ᵥ (symmetricDifference h j (sample h ψ) x -
          (-Complex.I) • lineDeriv ℝ ψ (latticePoint h x) (dir j))‖ +
        ‖(ϖ : ℂ) • Γ *ᵥ wilsonTerm h (sample h ψ) x‖ := norm_add_le _ _
    _ ≤ ∑ j, matBound (c j) * (M₃ * h ^ 2 / 2) + |ϖ| * (matBound Γ * (d * M₂ * h)) := by
        gcongr
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left
            (norm_symmetricDifference_sample_sub_le h hh ψ hψ M₃ hM3 j x) (matBound_nonneg _))
        · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left
            (norm_wilsonTerm_sample_le h hh ψ hψ2 M₂ hM2 x) (matBound_nonneg _))
    _ = h * ((∑ j, matBound (c j)) * (M₃ * h / 2) + |ϖ| * matBound Γ * (d * M₂)) := by
        rw [← Finset.sum_mul]
        ring

/-- **`lem:supp-general-core`, `eq:supp-general-core`** (frozen chart, `C³` form): for
`0 < h ≤ 1`, `‖(D̃^W_h S_h ψ)(x) - (D̂_0 ψ)(h x)‖ ≤ C h (M₂ + M₃)`, where `M₂, M₃` bound the
second and third differentials of `ψ` and `C = consistencyConstant ϖ c Γ` depends only on the
Clifford coefficients and the Wilson parameter. -/
theorem norm_frozenWilson_sample_sub_frozenDirac_le (h ϖ : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (c : Fin d → Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin N) (Fin N) ℂ)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (hψ : ContDiff ℝ 3 ψ) (M₂ M₃ : ℝ)
    (hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 ψ y‖ ≤ M₂) (hM3 : ∀ y, ‖iteratedFDeriv ℝ 3 ψ y‖ ≤ M₃)
    (x : Fin d → ℤ) :
    ‖frozenWilson h ϖ c Γ (sample h ψ) x - frozenDirac c ψ (latticePoint h x)‖ ≤
      consistencyConstant ϖ c Γ * h * (M₂ + M₃) := by
  have hM2n : 0 ≤ M₂ := (norm_nonneg _).trans (hM2 0)
  have hM3n : 0 ≤ M₃ := (norm_nonneg _).trans (hM3 0)
  have hc : 0 ≤ ∑ j, matBound (c j) := Finset.sum_nonneg fun j _ => matBound_nonneg _
  have hΓ : 0 ≤ matBound Γ := matBound_nonneg Γ
  refine (norm_frozenWilson_sample_sub_frozenDirac_le' h ϖ hh c Γ ψ hψ M₂ M₃ hM2 hM3 x).trans ?_
  unfold consistencyConstant
  have h1 : (∑ j, matBound (c j)) * (M₃ * h / 2) ≤ (∑ j, matBound (c j)) / 2 * (M₂ + M₃) := by
    have : M₃ * h ≤ M₃ := by
      calc M₃ * h ≤ M₃ * 1 := by gcongr
        _ = M₃ := mul_one _
    calc (∑ j, matBound (c j)) * (M₃ * h / 2) ≤ (∑ j, matBound (c j)) * (M₃ / 2) := by
          gcongr
      _ ≤ (∑ j, matBound (c j)) / 2 * (M₂ + M₃) := by
          rw [div_mul_eq_mul_div, mul_add, ← mul_div_assoc]
          have : 0 ≤ (∑ j, matBound (c j)) * M₂ / 2 := by positivity
          linarith [show (∑ j, matBound (c j)) * (M₃ / 2) = (∑ j, matBound (c j)) * M₃ / 2 by
            ring]
  have h2 : |ϖ| * matBound Γ * (d * M₂) ≤ |ϖ| * matBound Γ * d * (M₂ + M₃) := by
    rw [mul_assoc (|ϖ| * matBound Γ) (d : ℝ)]
    gcongr
    · linarith
  calc h * ((∑ j, matBound (c j)) * (M₃ * h / 2) + |ϖ| * matBound Γ * (d * M₂))
      ≤ h * ((∑ j, matBound (c j)) / 2 * (M₂ + M₃) + |ϖ| * matBound Γ * d * (M₂ + M₃)) := by
        gcongr
    _ = ((∑ j, matBound (c j)) / 2 + |ϖ| * matBound Γ * d) * h * (M₂ + M₃) := by ring

end RenewalGeometry.FrozenWilsonCoreConsistency
