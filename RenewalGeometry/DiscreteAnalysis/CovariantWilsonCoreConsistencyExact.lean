/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.FrozenWilsonCoreConsistencyExact

/-!
# Smooth-core consistency of the covariant variable-coefficient Wilson operator

Paper `predictive_spectral_geometry`, label `lem:supp-general-core`
(`eq:supp-general-core`, `eq:Wilson-core-smallness`), chart form with variable Clifford
coefficients `ĉ^j(x)` and spin links.

The lattice operator is the covariant doubled Wilson operator of `eq:supp-general-Wilson`,
`D̃^W_h = ½ Σ_j (M_{ĉ^j_h} P^Ω_j + P^Ω_j M_{ĉ^j_h}) + ϖ Γ_⊥ W^Ω_h` (`covariantWilson`), built from the
covariant shifts `T^Ω_j ψ(x) = U_j(x) ψ(x + e_j)` (`covShift`, spin links `U_j`) and their
adjoints `(T^Ω_j)^* ψ(x) = U_j(x - e_j)^* ψ(x - e_j)` (`covShiftAdj`), the covariant symmetric
differences `P^Ω_j = (T^Ω_j - (T^Ω_j)^*)/(2ih)` and the Wilson term
`W^Ω = (2h)⁻¹ Σ_j (2 - T^Ω_j - (T^Ω_j)^*)` (`eq:supp-covariant-differences`), with the
sampled coefficients `M_{ĉ^j_h} ψ(x) = ĉ^j(hx) ψ(x)`.  The continuum operator is the
density-symmetric Dirac operator of `lem:supp-density-symmetric`,
`U_ρ D̂_g U_ρ⁻¹ = -(i/2) Σ_j (M_{ĉ^j} ∇_j + ∇_j M_{ĉ^j})`, `∇_j = ∂_j + Ω_j`
(`densitySymmetricDirac`).

The spin links are exact parallel transports `U_j(x) = I + h Ω_j(hx) + O(h²)` (hypothesis
`LinkExpansion`, with the same expansion for the adjoints, i.e. `Ω_j` anti-Hermitian to
leading order); the connection coefficients `Ω_j` are bounded and Lipschitz
(`ConnectionBounds`).

* `norm_covSymmetricDifference_sample_sub_le`: `‖P^Ω_j S_h ψ (x) - (-i ∇_j ψ)(hx)‖ ≤ C h`.
* `norm_covWilsonTerm_sample_le` (**`eq:Wilson-core-smallness`**): `‖W^Ω_h S_h ψ (x)‖ ≤ C h`.
* `norm_covariantWilson_sample_sub_densitySymmetricDirac_le` (**`eq:supp-general-core`**):
  `‖(D̃^W_h S_h ψ)(x) - (U_ρ D̂_g U_ρ⁻¹ ψ)(hx)‖ ≤ C h` for `0 < h ≤ 1`, with `C` explicit in the
  `C³` bounds of `ψ` and of the products `ĉ^j ψ`, the coefficient bound, the connection
  bounds, the link constant and the Wilson data.

Sobolev norms are replaced by `C^k` bounds and the `L²` norm by the pointwise sup norm at the
lattice points; cell-average sampling is replaced by point sampling.
-/

open Finset Matrix
open RenewalGeometry.FrozenWilsonSymbol RenewalGeometry.FrozenWilsonCoreConsistency
open RenewalGeometry.VectorLineTaylor

namespace RenewalGeometry.CovariantWilsonCoreConsistency

variable {d N : ℕ}

/-- Spin links: `U j x` is the parallel transport on the edge `x → x + e_j`. -/
abbrev Links (d N : ℕ) := Fin d → (Fin d → ℤ) → Matrix (Fin N) (Fin N) ℂ

/-- Continuum matrix coefficients on the chart (`ĉ^j`, `Ω_j`). -/
abbrev Coefficients (d N : ℕ) := Fin d → (Fin d → ℝ) → Matrix (Fin N) (Fin N) ℂ

/-! ### Covariant lattice operators -/

/-- The covariant shift `T^Ω_j ψ (x) = U_j(x) ψ(x + e_j)`. -/
def covShift (U : Links d N) (j : Fin d) (ψ : LatticeSection d N) : LatticeSection d N :=
  fun x => U j x *ᵥ ψ (x + Pi.single j 1)

/-- The adjoint covariant shift `(T^Ω_j)^* ψ (x) = U_j(x - e_j)^* ψ(x - e_j)`. -/
def covShiftAdj (U : Links d N) (j : Fin d) (ψ : LatticeSection d N) : LatticeSection d N :=
  fun x => (U j (x - Pi.single j 1))ᴴ *ᵥ ψ (x - Pi.single j 1)

/-- The covariant symmetric difference `P^Ω_j = (T^Ω_j - (T^Ω_j)^*) / (2ih)`. -/
noncomputable def covSymmetricDifference (h : ℝ) (U : Links d N) (j : Fin d)
    (ψ : LatticeSection d N) : LatticeSection d N :=
  fun x => (2 * Complex.I * (h : ℂ))⁻¹ • (covShift U j ψ x - covShiftAdj U j ψ x)

/-- The covariant Wilson term `W^Ω = (2h)⁻¹ Σ_j (2 - T^Ω_j - (T^Ω_j)^*)`. -/
noncomputable def covWilsonTerm (h : ℝ) (U : Links d N) (ψ : LatticeSection d N) :
    LatticeSection d N :=
  fun x => (2 * (h : ℂ))⁻¹ • ∑ j, ((2 : ℂ) • ψ x - covShift U j ψ x - covShiftAdj U j ψ x)

/-- Multiplication by the sampled coefficient `ĉ^j(hx)`. -/
def varMul (c : Coefficients d N) (h : ℝ) (j : Fin d) (ψ : LatticeSection d N) :
    LatticeSection d N :=
  fun x => c j (latticePoint h x) *ᵥ ψ x

/-- The covariant doubled Wilson operator of `eq:supp-general-Wilson`:
`½ Σ_j (M_{ĉ^j_h} P^Ω_j + P^Ω_j M_{ĉ^j_h}) + ϖ Γ_⊥ W^Ω_h`. -/
noncomputable def covariantWilson (h ϖ : ℝ) (c : Coefficients d N) (U : Links d N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (ψ : LatticeSection d N) : LatticeSection d N :=
  fun x => (2 : ℂ)⁻¹ • ∑ j, (varMul c h j (covSymmetricDifference h U j ψ) x +
      covSymmetricDifference h U j (varMul c h j ψ) x) +
    (ϖ : ℂ) • Γ *ᵥ covWilsonTerm h U ψ x

/-! ### The continuum density-symmetric Dirac operator -/

/-- The covariant derivative `∇_j ψ = ∂_j ψ + Ω_j ψ` (directional derivative form). -/
noncomputable def covDeriv (Ω : Coefficients d N) (j : Fin d) (ψ : (Fin d → ℝ) → (Fin N → ℂ))
    (y : Fin d → ℝ) : Fin N → ℂ :=
  lineDeriv ℝ ψ y (dir j) + Ω j y *ᵥ ψ y

/-- The density-symmetric Dirac operator `-(i/2) Σ_j (M_{ĉ^j} ∇_j + ∇_j M_{ĉ^j})` of
`eq:supp-density-symmetric`. -/
noncomputable def densitySymmetricDirac (c Ω : Coefficients d N)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (y : Fin d → ℝ) : Fin N → ℂ :=
  (-(Complex.I / 2)) • ∑ j, (c j y *ᵥ covDeriv Ω j ψ y +
    covDeriv Ω j (fun z => c j z *ᵥ ψ z) y)

/-! ### Hypotheses on links and connection -/

/-- The links are parallel transports to second order: `U_j(x) = I + h Ω_j(hx) + O(h²)` and
`U_j(x)^* = I - h Ω_j(hx) + O(h²)` (operator form, constant `CU`). -/
def LinkExpansion (h : ℝ) (U : Links d N) (Ω : Coefficients d N) (CU : ℝ) : Prop :=
  ∀ (j : Fin d) (x : Fin d → ℤ) (v : Fin N → ℂ),
    ‖(U j x - 1 - (h : ℂ) • Ω j (latticePoint h x)) *ᵥ v‖ ≤ CU * h ^ 2 * ‖v‖ ∧
    ‖((U j x)ᴴ - 1 + (h : ℂ) • Ω j (latticePoint h x)) *ᵥ v‖ ≤ CU * h ^ 2 * ‖v‖

/-- Bounded, Lipschitz connection coefficients (operator form). -/
def ConnectionBounds (Ω : Coefficients d N) (B0 B1 : ℝ) : Prop :=
  (∀ (j : Fin d) (y : Fin d → ℝ) (v : Fin N → ℂ), ‖Ω j y *ᵥ v‖ ≤ B0 * ‖v‖) ∧
  (∀ (j : Fin d) (y z : Fin d → ℝ) (v : Fin N → ℂ),
    ‖(Ω j y - Ω j z) *ᵥ v‖ ≤ B1 * ‖y - z‖ * ‖v‖)

/-! ### Elementary bounds -/

theorem norm_inv_two_I_mul (h : ℝ) (hh : 0 < h) :
    ‖(2 * Complex.I * (h : ℂ))⁻¹‖ = (2 * h)⁻¹ := by
  rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh]
  norm_num

theorem norm_inv_two_mul (h : ℝ) (hh : 0 < h) : ‖(2 * (h : ℂ))⁻¹‖ = (2 * h)⁻¹ := by
  rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  norm_num

theorem norm_inv_two_I : ‖(2 * Complex.I)⁻¹‖ = (1 / 2 : ℝ) := by
  rw [norm_inv, norm_mul, Complex.norm_I]
  norm_num

theorem norm_inv_two : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by
  rw [norm_inv]
  norm_num

theorem taylorSum_zero' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : ℝ → F)
    (x : ℝ) : taylorSum φ 0 x = φ 0 := by
  simp [taylorSum]

/-- Lipschitz bound along a coordinate line from the `C¹` bound. -/
theorem norm_lineMap_sub_le (h : ℝ) (hh : 0 < h) (ψ : (Fin d → ℝ) → (Fin N → ℂ))
    (hψ : ContDiff ℝ 1 ψ) (M₁ : ℝ) (hM1 : ∀ y, ‖iteratedFDeriv ℝ 1 ψ y‖ ≤ M₁) (p : Fin d → ℝ)
    (j : Fin d) :
    ‖lineMap ψ p (dir j) h - ψ p‖ ≤ M₁ * h ∧ ‖lineMap ψ p (dir j) (-h) - ψ p‖ ≤ M₁ * h := by
  set φ := lineMap ψ p (dir j)
  have hφ : ContDiff ℝ 1 φ := contDiff_lineMap hψ _ _
  have hMφ : ∀ t, ‖iteratedDeriv 1 φ t‖ ≤ M₁ := by
    intro t
    have := norm_iteratedDeriv_lineMap_le_of_bound hψ (le_refl 1) hM1 p (dir j) t
    rwa [norm_dir, one_pow, mul_one] at this
  have h0 : φ 0 = ψ p := by simp [φ, lineMap]
  have h1 := norm_sub_taylorSum_le φ 0 M₁ hφ hMφ hh.le
  have h2 := norm_sub_taylorSum_neg_le φ 0 M₁ hφ hMφ hh.le
  rw [taylorSum_zero', h0] at h1 h2
  simp only [zero_add, pow_one, Nat.factorial_zero, Nat.cast_one, div_one] at h1 h2
  exact ⟨h1, h2⟩

/-- The sampled coefficient product is the sample of the continuum product. -/
theorem varMul_sample (c : Coefficients d N) (h : ℝ) (j : Fin d)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) :
    varMul c h j (sample h ψ) = sample h (fun z => c j z *ᵥ ψ z) := rfl

theorem norm_neg_smul_dir (h : ℝ) (j : Fin d) : ‖(-h) • dir j‖ = |h| := by
  rw [norm_smul, norm_dir, mul_one, Real.norm_eq_abs, abs_neg]

/-! ### The covariant shifts on samples -/

section shifts

variable (h : ℝ) (U : Links d N) (Ω : Coefficients d N) (ψ : (Fin d → ℝ) → (Fin N → ℂ))
  (j : Fin d) (x : Fin d → ℤ)

/-- The forward link remainder `(U_j(x) - I - h Ω_j(hx)) ψ(h(x+e_j))`. -/
noncomputable def forwardRemainder : Fin N → ℂ :=
  (U j x - 1 - (h : ℂ) • Ω j (latticePoint h x)) *ᵥ lineMap ψ (latticePoint h x) (dir j) h

/-- The backward link remainder `(U_j(x-e_j)^* - I + h Ω_j(h(x-e_j))) ψ(h(x-e_j))`. -/
noncomputable def backwardRemainder : Fin N → ℂ :=
  ((U j (x - Pi.single j 1))ᴴ - 1 + (h : ℂ) • Ω j (latticePoint h x + (-h) • dir j)) *ᵥ
    lineMap ψ (latticePoint h x) (dir j) (-h)

theorem covShift_sample :
    covShift U j (sample h ψ) x = lineMap ψ (latticePoint h x) (dir j) h +
      (h : ℂ) • (Ω j (latticePoint h x) *ᵥ lineMap ψ (latticePoint h x) (dir j) h) +
      forwardRemainder h U Ω ψ j x := by
  simp only [covShift, sample, latticePoint_add_single, forwardRemainder, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, lineMap]
  abel

theorem covShiftAdj_sample :
    covShiftAdj U j (sample h ψ) x = lineMap ψ (latticePoint h x) (dir j) (-h) -
      (h : ℂ) • (Ω j (latticePoint h x + (-h) • dir j) *ᵥ
        lineMap ψ (latticePoint h x) (dir j) (-h)) +
      backwardRemainder h U Ω ψ j x := by
  simp only [covShiftAdj, sample, latticePoint_sub_single, backwardRemainder, Matrix.sub_mulVec,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, lineMap]
  abel

theorem norm_forwardRemainder_le {CU : ℝ} (hU : LinkExpansion h U Ω CU) (hCU : 0 ≤ CU)
    {M₀ : ℝ} (hM0 : ∀ y, ‖ψ y‖ ≤ M₀) :
    ‖forwardRemainder h U Ω ψ j x‖ ≤ CU * h ^ 2 * M₀ :=
  ((hU j x _).1).trans (mul_le_mul_of_nonneg_left (hM0 _) (by positivity))

theorem norm_backwardRemainder_le {CU : ℝ} (hU : LinkExpansion h U Ω CU) (hCU : 0 ≤ CU)
    {M₀ : ℝ} (hM0 : ∀ y, ‖ψ y‖ ≤ M₀) :
    ‖backwardRemainder h U Ω ψ j x‖ ≤ CU * h ^ 2 * M₀ := by
  have := (hU j (x - Pi.single j 1) (lineMap ψ (latticePoint h x) (dir j) (-h))).2
  rw [latticePoint_sub_single] at this
  exact this.trans (mul_le_mul_of_nonneg_left (hM0 _) (by positivity))

end shifts

/-! ### Two algebraic decompositions -/

theorem decomp_identity (a b : ℂ) (h : ℝ) (hab : a * (h : ℂ) = b)
    (hneg : (-Complex.I) = b * 2) (Ωp Ωm : Matrix (Fin N) (Fin N) ℂ)
    (ψp ψm ψ0 L Rp Rm : Fin N → ℂ) :
    a • ((ψp + (h : ℂ) • (Ωp *ᵥ ψp) + Rp) - (ψm - (h : ℂ) • (Ωm *ᵥ ψm) + Rm)) -
      (-Complex.I) • (L + Ωp *ᵥ ψ0) =
    (a • (ψp - ψm) - (-Complex.I) • L) +
      b • (Ωp *ᵥ (ψp - ψ0) + Ωp *ᵥ (ψm - ψ0) + (Ωm - Ωp) *ᵥ ψm) + a • (Rp - Rm) := by
  simp only [Matrix.mulVec_sub, Matrix.sub_mulVec]
  rw [hneg, ← hab]
  module

theorem wilson_decomp_identity (h : ℝ) (Ωp Ωm : Matrix (Fin N) (Fin N) ℂ)
    (ψp ψm ψ0 Rp Rm : Fin N → ℂ) :
    (2 : ℂ) • ψ0 - (ψp + (h : ℂ) • (Ωp *ᵥ ψp) + Rp) - (ψm - (h : ℂ) • (Ωm *ᵥ ψm) + Rm) =
    ((2 : ℂ) • ψ0 - ψp - ψm) - (h : ℂ) • (Ωp *ᵥ (ψp - ψm) + (Ωp - Ωm) *ᵥ ψm) - (Rp + Rm) := by
  simp only [Matrix.mulVec_sub, Matrix.sub_mulVec]
  module

/-! ### The covariant centered difference on samples -/

/-- The consistency constant of the covariant centered difference. -/
noncomputable def covariantConsistencyConstant (M₀ M₁ M₃ B0 B1 CU : ℝ) : ℝ :=
  M₃ / 2 + B0 * M₁ + B1 * M₀ / 2 + CU * M₀

/-- **Covariant centered-difference consistency.**
`‖P^Ω_j S_h ψ (x) - (-i ∇_j ψ)(hx)‖ ≤ h (M₃/2 + B₀ M₁ + B₁ M₀/2 + C_U M₀)` for `0 < h ≤ 1`. -/
theorem norm_covSymmetricDifference_sample_sub_le (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (U : Links d N) (Ω : Coefficients d N) (CU B0 B1 : ℝ) (hCU : 0 ≤ CU) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hU : LinkExpansion h U Ω CU) (hΩ : ConnectionBounds Ω B0 B1)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (hψ : ContDiff ℝ 3 ψ)
    (M₀ M₁ M₃ : ℝ) (hM0 : ∀ y, ‖ψ y‖ ≤ M₀) (hM1 : ∀ y, ‖iteratedFDeriv ℝ 1 ψ y‖ ≤ M₁)
    (hM3 : ∀ y, ‖iteratedFDeriv ℝ 3 ψ y‖ ≤ M₃) (j : Fin d) (x : Fin d → ℤ) :
    ‖covSymmetricDifference h U j (sample h ψ) x -
        (-Complex.I) • covDeriv Ω j ψ (latticePoint h x)‖ ≤
      h * covariantConsistencyConstant M₀ M₁ M₃ B0 B1 CU := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hah : (2 * Complex.I * (h : ℂ))⁻¹ * (h : ℂ) = (2 * Complex.I)⁻¹ := by
    field_simp
  have hneg : (-Complex.I) = (2 * Complex.I)⁻¹ * 2 := by
    field_simp
    rw [Complex.I_sq]
    norm_num
  have hM0n : 0 ≤ M₀ := (norm_nonneg _).trans (hM0 0)
  have hM3n : 0 ≤ M₃ := (norm_nonneg _).trans (hM3 0)
  -- decomposition
  have hdecomp : covSymmetricDifference h U j (sample h ψ) x -
      (-Complex.I) • covDeriv Ω j ψ (latticePoint h x) =
      (symmetricDifference h j (sample h ψ) x -
        (-Complex.I) • lineDeriv ℝ ψ (latticePoint h x) (dir j)) +
      (2 * Complex.I)⁻¹ • (Ω j (latticePoint h x) *ᵥ
          (lineMap ψ (latticePoint h x) (dir j) h - ψ (latticePoint h x)) +
        Ω j (latticePoint h x) *ᵥ
          (lineMap ψ (latticePoint h x) (dir j) (-h) - ψ (latticePoint h x)) +
        (Ω j (latticePoint h x + (-h) • dir j) - Ω j (latticePoint h x)) *ᵥ
          lineMap ψ (latticePoint h x) (dir j) (-h)) +
      (2 * Complex.I * (h : ℂ))⁻¹ • (forwardRemainder h U Ω ψ j x - backwardRemainder h U Ω ψ j x) := by
    rw [symmetricDifference_sample]
    unfold covSymmetricDifference covDeriv
    rw [covShift_sample, covShiftAdj_sample]
    exact decomp_identity _ _ h hah hneg _ _ _ _ _ _ _ _
  rw [hdecomp]
  -- the three bounds
  have hT1 := norm_symmetricDifference_sample_sub_le h hh ψ hψ M₃ hM3 j x
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  obtain ⟨hL1, hL2⟩ := norm_lineMap_sub_le h hh ψ hψ1 M₁ hM1 (latticePoint h x) j
  have e1 : ‖Ω j (latticePoint h x) *ᵥ
      (lineMap ψ (latticePoint h x) (dir j) h - ψ (latticePoint h x))‖ ≤ B0 * (M₁ * h) :=
    (hΩ.1 j _ _).trans (mul_le_mul_of_nonneg_left hL1 hB0)
  have e2 : ‖Ω j (latticePoint h x) *ᵥ
      (lineMap ψ (latticePoint h x) (dir j) (-h) - ψ (latticePoint h x))‖ ≤ B0 * (M₁ * h) :=
    (hΩ.1 j _ _).trans (mul_le_mul_of_nonneg_left hL2 hB0)
  have e3 : ‖(Ω j (latticePoint h x + (-h) • dir j) - Ω j (latticePoint h x)) *ᵥ
      lineMap ψ (latticePoint h x) (dir j) (-h)‖ ≤ B1 * h * M₀ := by
    refine (hΩ.2 j _ _ _).trans ?_
    rw [add_sub_cancel_left, norm_neg_smul_dir, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left (hM0 _) (by positivity)
  have hT2 : ‖(2 * Complex.I)⁻¹ • (Ω j (latticePoint h x) *ᵥ
          (lineMap ψ (latticePoint h x) (dir j) h - ψ (latticePoint h x)) +
        Ω j (latticePoint h x) *ᵥ
          (lineMap ψ (latticePoint h x) (dir j) (-h) - ψ (latticePoint h x)) +
        (Ω j (latticePoint h x + (-h) • dir j) - Ω j (latticePoint h x)) *ᵥ
          lineMap ψ (latticePoint h x) (dir j) (-h))‖ ≤
      (1 / 2) * (B0 * (M₁ * h) + B0 * (M₁ * h) + B1 * h * M₀) := by
    rw [norm_smul, norm_inv_two_I]
    exact mul_le_mul_of_nonneg_left ((norm_add₃_le).trans (add_le_add (add_le_add e1 e2) e3))
      (by norm_num)
  have hT3 : ‖(2 * Complex.I * (h : ℂ))⁻¹ •
      (forwardRemainder h U Ω ψ j x - backwardRemainder h U Ω ψ j x)‖ ≤
      (2 * h)⁻¹ * (CU * h ^ 2 * M₀ + CU * h ^ 2 * M₀) := by
    rw [norm_smul, norm_inv_two_I_mul h hh]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add
      (norm_forwardRemainder_le h U Ω ψ j x hU hCU hM0)
      (norm_backwardRemainder_le h U Ω ψ j x hU hCU hM0))) (by positivity)
  have hsum : (2 * h)⁻¹ * (CU * h ^ 2 * M₀ + CU * h ^ 2 * M₀) = CU * M₀ * h := by
    field_simp
    ring
  have hsq : M₃ * h ^ 2 / 2 ≤ M₃ * h / 2 := by
    have : M₃ * h ^ 2 ≤ M₃ * h := by
      rw [sq, ← mul_assoc]
      exact mul_le_of_le_one_right (by positivity) hh1
    linarith
  calc _ ≤ _ := norm_add₃_le
    _ ≤ M₃ * h ^ 2 / 2 + (1 / 2) * (B0 * (M₁ * h) + B0 * (M₁ * h) + B1 * h * M₀) +
        (2 * h)⁻¹ * (CU * h ^ 2 * M₀ + CU * h ^ 2 * M₀) := add_le_add (add_le_add hT1 hT2) hT3
    _ ≤ h * covariantConsistencyConstant M₀ M₁ M₃ B0 B1 CU := by
        rw [hsum]
        unfold covariantConsistencyConstant
        nlinarith

/-! ### The Wilson term on samples -/

/-- The constant of the covariant Wilson smallness estimate. -/
noncomputable def wilsonConsistencyConstant (M₀ M₁ M₂ B0 B1 CU : ℝ) : ℝ :=
  M₂ + B0 * M₁ + B1 * M₀ / 2 + CU * M₀

/-- **`eq:Wilson-core-smallness`** (covariant, `C²` form):
`‖W^Ω_h S_h ψ (x)‖ ≤ d h (M₂ + B₀ M₁ + B₁ M₀/2 + C_U M₀)`. -/
theorem norm_covWilsonTerm_sample_le (h : ℝ) (hh : 0 < h)
    (U : Links d N) (Ω : Coefficients d N) (CU B0 B1 : ℝ) (hCU : 0 ≤ CU) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hU : LinkExpansion h U Ω CU) (hΩ : ConnectionBounds Ω B0 B1)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (hψ : ContDiff ℝ 2 ψ)
    (M₀ M₁ M₂ : ℝ) (hM0 : ∀ y, ‖ψ y‖ ≤ M₀) (hM1 : ∀ y, ‖iteratedFDeriv ℝ 1 ψ y‖ ≤ M₁)
    (hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 ψ y‖ ≤ M₂) (x : Fin d → ℤ) :
    ‖covWilsonTerm h U (sample h ψ) x‖ ≤ d * h * wilsonConsistencyConstant M₀ M₁ M₂ B0 B1 CU := by
  have hM0n : 0 ≤ M₀ := (norm_nonneg _).trans (hM0 0)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hterm : ∀ j : Fin d,
      ‖(2 : ℂ) • sample h ψ x - covShift U j (sample h ψ) x - covShiftAdj U j (sample h ψ) x‖ ≤
        h ^ 2 * (2 * wilsonConsistencyConstant M₀ M₁ M₂ B0 B1 CU) := by
    intro j
    rw [covShift_sample, covShiftAdj_sample, wilson_decomp_identity]
    set p := latticePoint h x with hp
    -- second difference
    have hA : ‖(2 : ℂ) • sample h ψ x - lineMap ψ p (dir j) h - lineMap ψ p (dir j) (-h)‖ ≤
        2 * M₂ * h ^ 2 := by
      set φ := lineMap ψ p (dir j)
      have hφ : ContDiff ℝ 2 φ := contDiff_lineMap hψ _ _
      have hMφ : ∀ t, ‖iteratedDeriv 2 φ t‖ ≤ M₂ := by
        intro t
        have := norm_iteratedDeriv_lineMap_le_of_bound hψ (le_refl 2) hM2 p (dir j) t
        rwa [norm_dir, one_pow, mul_one] at this
      have h0 : φ 0 = ψ p := by simp [φ, lineMap]
      have hrw : (2 : ℂ) • sample h ψ x - φ h - φ (-h) = (2 : ℝ) • φ 0 - φ h - φ (-h) := by
        show (2 : ℂ) • ψ p - φ h - φ (-h) = (2 : ℝ) • φ 0 - φ h - φ (-h)
        rw [h0, RCLike.real_smul_eq_coe_smul (K := ℂ)]
        norm_num
      rw [hrw]
      exact norm_second_difference_le φ M₂ hφ hMφ hh.le
    obtain ⟨hL1, hL2⟩ := norm_lineMap_sub_le h hh ψ hψ1 M₁ hM1 p j
    have hpm : ‖lineMap ψ p (dir j) h - lineMap ψ p (dir j) (-h)‖ ≤ 2 * M₁ * h := by
      calc ‖lineMap ψ p (dir j) h - lineMap ψ p (dir j) (-h)‖
          ≤ ‖lineMap ψ p (dir j) h - ψ p‖ + ‖ψ p - lineMap ψ p (dir j) (-h)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ M₁ * h + M₁ * h := add_le_add hL1 (by rw [norm_sub_rev]; exact hL2)
        _ = 2 * M₁ * h := by ring
    have hB : ‖(h : ℂ) • (Ω j p *ᵥ (lineMap ψ p (dir j) h - lineMap ψ p (dir j) (-h)) +
        (Ω j p - Ω j (p + (-h) • dir j)) *ᵥ lineMap ψ p (dir j) (-h))‖ ≤
        h * (B0 * (2 * M₁ * h) + B1 * h * M₀) := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
      refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hh.le
      · exact (hΩ.1 j _ _).trans (mul_le_mul_of_nonneg_left hpm hB0)
      · refine (hΩ.2 j _ _ _).trans ?_
        rw [sub_add_cancel_left, norm_neg, norm_neg_smul_dir, abs_of_pos hh]
        exact mul_le_mul_of_nonneg_left (hM0 _) (by positivity)
    have hC : ‖forwardRemainder h U Ω ψ j x + backwardRemainder h U Ω ψ j x‖ ≤
        CU * h ^ 2 * M₀ + CU * h ^ 2 * M₀ :=
      (norm_add_le _ _).trans (add_le_add (norm_forwardRemainder_le h U Ω ψ j x hU hCU hM0)
        (norm_backwardRemainder_le h U Ω ψ j x hU hCU hM0))
    calc ‖((2 : ℂ) • sample h ψ x - lineMap ψ p (dir j) h - lineMap ψ p (dir j) (-h)) -
          (h : ℂ) • (Ω j p *ᵥ (lineMap ψ p (dir j) h - lineMap ψ p (dir j) (-h)) +
            (Ω j p - Ω j (p + (-h) • dir j)) *ᵥ lineMap ψ p (dir j) (-h)) -
          (forwardRemainder h U Ω ψ j x + backwardRemainder h U Ω ψ j x)‖
        ≤ ‖(2 : ℂ) • sample h ψ x - lineMap ψ p (dir j) h - lineMap ψ p (dir j) (-h)‖ +
          ‖(h : ℂ) • (Ω j p *ᵥ (lineMap ψ p (dir j) h - lineMap ψ p (dir j) (-h)) +
            (Ω j p - Ω j (p + (-h) • dir j)) *ᵥ lineMap ψ p (dir j) (-h))‖ +
          ‖forwardRemainder h U Ω ψ j x + backwardRemainder h U Ω ψ j x‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ 2 * M₂ * h ^ 2 + h * (B0 * (2 * M₁ * h) + B1 * h * M₀) +
          (CU * h ^ 2 * M₀ + CU * h ^ 2 * M₀) := add_le_add (add_le_add hA hB) hC
      _ = h ^ 2 * (2 * wilsonConsistencyConstant M₀ M₁ M₂ B0 B1 CU) := by
          unfold wilsonConsistencyConstant
          ring
  calc ‖covWilsonTerm h U (sample h ψ) x‖
      = (2 * h)⁻¹ * ‖∑ j, ((2 : ℂ) • sample h ψ x - covShift U j (sample h ψ) x -
          covShiftAdj U j (sample h ψ) x)‖ := by
        rw [covWilsonTerm, norm_smul, norm_inv_two_mul h hh]
    _ ≤ (2 * h)⁻¹ * ∑ _j : Fin d, (h ^ 2 * (2 * wilsonConsistencyConstant M₀ M₁ M₂ B0 B1 CU)) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
    _ = d * h * wilsonConsistencyConstant M₀ M₁ M₂ B0 B1 CU := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        try ring

/-! ### The consistency estimate -/

/-- The core-consistency constant `(d C₀ K_ψ + d K_{cψ})/2 + |ϖ| ‖Γ‖ d W`. -/
noncomputable def coreConstant (d : ℕ) (C0 Kψ Kc W ϖ ΓB : ℝ) : ℝ :=
  (d * C0 * Kψ + d * Kc) / 2 + |ϖ| * ΓB * d * W

/-- **`lem:supp-general-core`, `eq:supp-general-core`** (chart form, variable coefficients,
spin links, `C³` bounds): for `0 < h ≤ 1`,
`‖(D̃^W_h S_h ψ)(x) - (U_ρ D̂_g U_ρ⁻¹ ψ)(hx)‖ ≤ C h`, where `C = coreConstant …` depends on the
`C³` bounds `M_k` of `ψ` and `M'_k` of the products `ĉ^j ψ`, the coefficient bound `C₀`, the
connection bounds `B₀, B₁`, the link constant `C_U`, and the Wilson data `ϖ, ‖Γ_⊥‖`. -/
theorem norm_covariantWilson_sample_sub_densitySymmetricDirac_le (h ϖ : ℝ) (hh : 0 < h)
    (hh1 : h ≤ 1) (c : Coefficients d N) (U : Links d N) (Ω : Coefficients d N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (CU B0 B1 C0 : ℝ) (hCU : 0 ≤ CU) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hC0 : 0 ≤ C0) (hU : LinkExpansion h U Ω CU)
    (hΩ : ConnectionBounds Ω B0 B1) (hc0 : ∀ j y, matBound (c j y) ≤ C0)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (hψ : ContDiff ℝ 3 ψ) (M₀ M₁ M₂ M₃ : ℝ)
    (hM0 : ∀ y, ‖ψ y‖ ≤ M₀) (hM1 : ∀ y, ‖iteratedFDeriv ℝ 1 ψ y‖ ≤ M₁)
    (hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 ψ y‖ ≤ M₂) (hM3 : ∀ y, ‖iteratedFDeriv ℝ 3 ψ y‖ ≤ M₃)
    (hcψ : ∀ j, ContDiff ℝ 3 (fun z => c j z *ᵥ ψ z)) (M'₀ M'₁ M'₃ : ℝ)
    (hM'0 : ∀ j y, ‖c j y *ᵥ ψ y‖ ≤ M'₀)
    (hM'1 : ∀ j y, ‖iteratedFDeriv ℝ 1 (fun z => c j z *ᵥ ψ z) y‖ ≤ M'₁)
    (hM'3 : ∀ j y, ‖iteratedFDeriv ℝ 3 (fun z => c j z *ᵥ ψ z) y‖ ≤ M'₃) (x : Fin d → ℤ) :
    ‖covariantWilson h ϖ c U Γ (sample h ψ) x - densitySymmetricDirac c Ω ψ (latticePoint h x)‖ ≤
      h * coreConstant d C0 (covariantConsistencyConstant M₀ M₁ M₃ B0 B1 CU)
        (covariantConsistencyConstant M'₀ M'₁ M'₃ B0 B1 CU)
        (wilsonConsistencyConstant M₀ M₁ M₂ B0 B1 CU) ϖ (matBound Γ) := by
  set Kψ := covariantConsistencyConstant M₀ M₁ M₃ B0 B1 CU with hKψ
  set Kc := covariantConsistencyConstant M'₀ M'₁ M'₃ B0 B1 CU with hKc
  set W := wilsonConsistencyConstant M₀ M₁ M₂ B0 B1 CU with hW
  set E1 : Fin d → Fin N → ℂ := fun j => covSymmetricDifference h U j (sample h ψ) x -
    (-Complex.I) • covDeriv Ω j ψ (latticePoint h x) with hE1
  set E2 : Fin d → Fin N → ℂ := fun j =>
    covSymmetricDifference h U j (varMul c h j (sample h ψ)) x -
      (-Complex.I) • covDeriv Ω j (fun z => c j z *ᵥ ψ z) (latticePoint h x) with hE2
  have hsum : ∑ j, (c j (latticePoint h x) *ᵥ E1 j + E2 j) =
      ∑ j, (c j (latticePoint h x) *ᵥ covSymmetricDifference h U j (sample h ψ) x +
        covSymmetricDifference h U j (varMul c h j (sample h ψ)) x) -
      (-Complex.I) • ∑ j, (c j (latticePoint h x) *ᵥ covDeriv Ω j ψ (latticePoint h x) +
        covDeriv Ω j (fun z => c j z *ᵥ ψ z) (latticePoint h x)) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hE1, hE2, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add]
    abel
  have hdec : covariantWilson h ϖ c U Γ (sample h ψ) x -
      densitySymmetricDirac c Ω ψ (latticePoint h x) =
      (2 : ℂ)⁻¹ • ∑ j, (c j (latticePoint h x) *ᵥ E1 j + E2 j) +
        (ϖ : ℂ) • Γ *ᵥ covWilsonTerm h U (sample h ψ) x := by
    rw [hsum, smul_sub, smul_smul, show (2 : ℂ)⁻¹ * (-Complex.I) = -(Complex.I / 2) by ring]
    simp only [covariantWilson, densitySymmetricDirac, varMul]
    module
  rw [hdec]
  have hE1b : ∀ j, ‖E1 j‖ ≤ h * Kψ := fun j =>
    norm_covSymmetricDifference_sample_sub_le h hh hh1 U Ω CU B0 B1 hCU hB0 hB1 hU hΩ ψ hψ
      M₀ M₁ M₃ hM0 hM1 hM3 j x
  have hE2b : ∀ j, ‖E2 j‖ ≤ h * Kc := fun j =>
    norm_covSymmetricDifference_sample_sub_le h hh hh1 U Ω CU B0 B1 hCU hB0 hB1 hU hΩ _ (hcψ j)
      M'₀ M'₁ M'₃ (hM'0 j) (hM'1 j) (hM'3 j) j x
  have hWb := norm_covWilsonTerm_sample_le h hh U Ω CU B0 B1 hCU hB0 hB1 hU hΩ ψ
    (hψ.of_le (by norm_num)) M₀ M₁ M₂ hM0 hM1 hM2 x
  calc ‖(2 : ℂ)⁻¹ • ∑ j, (c j (latticePoint h x) *ᵥ E1 j + E2 j) +
        (ϖ : ℂ) • Γ *ᵥ covWilsonTerm h U (sample h ψ) x‖
      ≤ ‖(2 : ℂ)⁻¹ • ∑ j, (c j (latticePoint h x) *ᵥ E1 j + E2 j)‖ +
        ‖(ϖ : ℂ) • Γ *ᵥ covWilsonTerm h U (sample h ψ) x‖ := norm_add_le _ _
    _ ≤ (1 / 2) * ∑ _j : Fin d, (C0 * (h * Kψ) + h * Kc) +
        |ϖ| * (matBound Γ * (d * h * W)) := by
        rw [norm_smul, norm_inv_two, norm_smul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
            (norm_add_le _ _).trans (add_le_add ((norm_mulVec_le _ _).trans
              (mul_le_mul (hc0 j _) (hE1b j) (norm_nonneg _) hC0)) (hE2b j)))
        · exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left hWb (matBound_nonneg Γ))
    _ = h * coreConstant d C0 Kψ Kc W ϖ (matBound Γ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        unfold coreConstant
        ring

end RenewalGeometry.CovariantWilsonCoreConsistency
