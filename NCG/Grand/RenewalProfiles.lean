/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Concrete renewal profiles
  (`thm:renewal-continuous-completion`,
   `thm:accepted-response-pressure`,
   `thm:accepted-phase-feedback`,
   `thm:concrete-renewal-continuum-profile`, Gran-Tensor
   manuscript)

* `completion_lst` / `completion_mean`: the boxed Laplace
  transform of the two-stage completion time
  `𝔼e^{-s𝒯} = 8λ²/((4λ+5s)(2λ+3s))` (product of the two
  exponential-stage transforms) and the boxed mean/intensity
  `𝔼𝒯 = 11/(4λ)`, `j_phys = 4λ/11`;
* `pressure_root`: the boxed pressure formula — with
  `A_θ(q) = 7 + 8θ(e^{-q}-1)`, the accepted-response pressure
  equation `e^{-q}F_{T_θ}(x) = 1` for the proved transform
  `F_T(z) = 8θz²/(15-8z+(8θ-7)z²)` is the quadratic
  `Ax² + 8x - 15 = 0`, solved by
  `x = (-8+√(64+60A))/(2A)`;
* `phase_contrast_*`: the boxed phase-feedback block table —
  `πM₀ = π`, `M₀φ̂ = -(7/15)φ̂` for the normalized contrast
  `φ̂ = (6,-5)/√30`, and the three π-weighted couplings
  `⟨1, C₀1⟩_π = 4/11`, `⟨1, C₀φ̂⟩_π = 24/(11√30)`,
  `⟨φ̂, C₀1⟩_π = -20/(11√30)` — exactly the coefficients in the
  boxed blocks `A_θ, B_θ, C_θ`.  The operator blocks, returned-kernel
  series, sharp norm estimates, and uniform continuum limit are proved in
  `NCG.Grand.AcceptedPhaseFeedbackExact`;
* `profile_eigen` / `profile_variance` / `profile_two_cell`: the
  boxed continuum profile — `M₀φ = -(7/15)φ`,
  `Var_π(1_P) = 30/121`, and the two-cell Walsh eigenvalue
  `(M₀⊗M₀)(φ⊗φ) = (49/225)(φ⊗φ)` (Kronecker eigenvector).

Rendering disclosed: the distributional identification of `𝒯`
as the independent two-stage sum (renewal probability layer), the
`m`-cell Walsh statement for general `m` (two-cell case proved,
induction identical) is the manuscript's framing on top of the identities
proved here.
-/

open Matrix Kronecker

namespace NCG

/-- Boxed Laplace transform: the product of the two stage
transforms equals `8λ²/((4λ+5s)(2λ+3s))`. -/
theorem completion_lst (lam s : ℝ) (hlam : 0 < lam)
    (hs : 0 ≤ s) :
    (4 * lam / 5) / (4 * lam / 5 + s)
      * ((2 * lam / 3) / (2 * lam / 3 + s))
    = 8 * lam ^ 2 / ((4 * lam + 5 * s) * (2 * lam + 3 * s)) := by
  have h1 : 4 * lam / 5 + s ≠ 0 := by positivity
  have h2 : 2 * lam / 3 + s ≠ 0 := by positivity
  have h3 : 4 * lam + 5 * s ≠ 0 := by positivity
  have h4 : 2 * lam + 3 * s ≠ 0 := by positivity
  field_simp
  ring

/-- Boxed mean and physical intensity:
`𝔼𝒯 = 5/(4λ) + 3/(2λ) = 11/(4λ)`, `j_phys = 4λ/11`. -/
theorem completion_mean (lam : ℝ) (hlam : 0 < lam) :
    5 / (4 * lam) + 3 / (2 * lam) = 11 / (4 * lam)
    ∧ (11 / (4 * lam))⁻¹ = 4 * lam / 11 := by
  refine ⟨?_, ?_⟩
  · field_simp
    ring
  · rw [inv_div]

/-- `thm:accepted-response-pressure`, boxed root: with
`A = 7 + 8θ(e^{-q}-1)`, the pressure equation
`e^{-q}·8θx² = 15 - 8x + (8θ-7)x²` is `Ax² + 8x - 15 = 0`,
solved by `x = (-8+√(64+60A))/(2A)`. -/
theorem pressure_root (θ q A x : ℝ)
    (hA : A = 7 + 8 * θ * (Real.exp (-q) - 1)) (hA0 : A ≠ 0)
    (hx : x = (-8 + Real.sqrt (64 + 60 * A)) / (2 * A))
    (hdisc : 0 ≤ 64 + 60 * A) :
    A * x ^ 2 + 8 * x - 15 = 0
    ∧ (∀ y : ℝ, A * y ^ 2 + 8 * y - 15 = 0
        ↔ Real.exp (-q) * (8 * θ * y ^ 2)
          = 15 - 8 * y + (8 * θ - 7) * y ^ 2) := by
  constructor
  · have hs := Real.sq_sqrt hdisc
    set s : ℝ := Real.sqrt (64 + 60 * A) with hsdef
    have hnum : (-8 + s) ^ 2 + 16 * (-8 + s) - 60 * A = 0 := by
      nlinarith [hs]
    rw [hx]
    field_simp
    linear_combination hs
  · intro y
    have hAy : A * y ^ 2
        = (7 + 8 * θ * (Real.exp (-q) - 1)) * y ^ 2 := by
      rw [hA]
    constructor <;> intro h <;> nlinarith [h, hAy]

/-- Block table, stationarity: `πM₀ = π` for
`π = (5/11, 6/11)`. -/
theorem phase_contrast_stationary :
    (5 / 11 : ℝ) * (1 / 5) + (6 / 11) * (2 / 3) = 5 / 11
    ∧ (5 / 11 : ℝ) * (4 / 5) + (6 / 11) * (1 / 3) = 6 / 11 := by
  norm_num

/-- Block table, contrast eigenvalue: `M₀(6,-5)ᵀ = -(7/15)(6,-5)ᵀ`
— the normalized contrast is an eigenvector with the boxed
mean-zero contraction `7/15`. -/
theorem phase_contrast_eigen :
    (1 / 5 : ℝ) * 6 + (4 / 5) * (-5) = -(7 / 15) * 6
    ∧ (2 / 3 : ℝ) * 6 + (1 / 3) * (-5) = -(7 / 15) * (-5) := by
  norm_num

/-- Block table, the three π-weighted couplings of the boxed
blocks: `⟨1, C₀1⟩_π = 4/11`, `⟨1, C₀φ̂⟩_π = 24/(11√30)`,
`⟨φ̂, C₀1⟩_π = -20/(11√30)`, with `φ̂ = (6,-5)/√30` and
`C₀ = [[0,0],[2/3,0]]`. -/
theorem phase_contrast_couplings :
    ((5 / 11 : ℝ) * 0 + (6 / 11) * (2 / 3) = 4 / 11)
    ∧ ((5 / 11 : ℝ) * 0
        + (6 / 11) * (2 / 3 * (6 / Real.sqrt 30))
      = 24 / (11 * Real.sqrt 30))
    ∧ ((5 / 11 : ℝ) * (6 / Real.sqrt 30) * 0
        + (6 / 11) * (-5 / Real.sqrt 30) * (2 / 3)
      = -20 / (11 * Real.sqrt 30)) := by
  have h30 : Real.sqrt 30 ≠ 0 := by
    have : (0:ℝ) < Real.sqrt 30 := Real.sqrt_pos.mpr (by norm_num)
    exact this.ne'
  refine ⟨by norm_num, ?_, ?_⟩ <;> field_simp <;> ring

/-- `thm:concrete-renewal-continuum-profile`, variance:
`Var_π(1_P) = (5/11)(6/11)² + (6/11)(5/11)² = 30/121`. -/
theorem profile_variance :
    (5 / 11 : ℝ) * (6 / 11) ^ 2 + (6 / 11) * (5 / 11) ^ 2
      = 30 / 121 := by
  norm_num

/-- Real Kronecker eigenvector lemma (real coefficients). -/
theorem kronecker_eigen_real {ι κ : Type*} [Fintype ι]
    [Fintype κ] (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (u : ι → ℝ) (v : κ → ℝ) (a b : ℝ)
    (ha : A.mulVec u = a • u) (hb : B.mulVec v = b • v) :
    (A ⊗ₖ B).mulVec (fun p => u p.1 * v p.2)
      = (a * b) • fun p => u p.1 * v p.2 := by
  have hprod : (A ⊗ₖ B).mulVec (fun p => u p.1 * v p.2)
      = fun p => A.mulVec u p.1 * B.mulVec v p.2 := by
    ext ⟨i, j⟩
    simp only [Matrix.mulVec, dotProduct, kroneckerMap_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => by ring
  rw [hprod, ha, hb]
  ext ⟨i, j⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Two-cell Walsh eigenvalue: the contrast tensor is an
eigenvector of `M₀ ⊗ M₀` with eigenvalue `(7/15)² = 49/225`. -/
theorem profile_two_cell :
    let M0 : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.of ![![1/5, 4/5], ![2/3, 1/3]]
    let φ : Fin 2 → ℝ := ![6, -5]
    (M0 ⊗ₖ M0).mulVec (fun p => φ p.1 * φ p.2)
      = (49 / 225 : ℝ) • fun p => φ p.1 * φ p.2 := by
  intro M0 φ
  have heig : M0.mulVec φ = (-(7/15) : ℝ) • φ := by
    ext i
    fin_cases i <;>
      norm_num [M0, φ, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
  have h := kronecker_eigen_real M0 M0 φ φ _ _ heig heig
  rw [h]
  norm_num

end NCG
