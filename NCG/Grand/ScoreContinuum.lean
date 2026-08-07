/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Resolved score bank and the score fluctuation–dissipation
  continuum (`thm:concrete-renewal-score-profile`,
  `cor:primitive-score-continuum`, Gran-Tensor manuscript)

* `score_gram_floor`: the boxed Gram `G₀ = diag(176/225, 1, 1)`
  has uniform frame floor `176/225` — the quadratic form
  dominates `176/225·‖v‖²`;
* `k4_laplacian_gap`: the `K₄` coboundary Gram acts as `4·I` on
  the mean-zero space `W₀ = 𝟏₄^⊥` (the spectral input for the
  fibre-frame identity);
* `tetrad_gram_kronecker`: the boxed fibre-frame identity —
  `d*d = 4·I` gives `(d ⊗ I)*(I ⊗ G₀)(d ⊗ I) = 4·(I ⊗ G₀)`, so
  the local fibre-frame floor is `4·176/225 = 704/225`;
* `frame_floor_scaling`: `4·(176/225) = 704/225`;
* `schur_innovation_telescope`: the boxed innovation telescope —
  with `Gₙ = t·G₀`, `Cₙ = t·G₀`, `H₂,ₙ = (t+τ)·G₀`, the Schur
  complement is exactly `H₂,ₙ - Cₙ*Gₙ⁻¹Cₙ = τ·G₀`;
* `diffusion_identity` / `diffusion_value`: the boxed diffusion
  coefficient — `(1-ρ²)/(1-ρ)² = (1+ρ)/(1-ρ)`, and at the proved
  renewal correlation `ρ = -7/15` it equals `4/11`.

Rendering disclosed: the martingale-difference property, the
`S₄`-covariance of the tetrahedral triplets, the Donsker
convergence `Z_τ ⟹ G₀^{1/2}B₃` in `D([0,T],ℝ³)`, and the
compound-Poisson thinning limit are the manuscript's stochastic
layer; the Gram data, the frame floors, the Kronecker fibre
identity, the innovation telescope, and the diffusion
coefficient are proved here.
-/

open Matrix Kronecker

namespace NCG

/-- Boxed score Gram floor: `G₀ = diag(176/225, 1, 1)` dominates
`176/225` times the Euclidean form. -/
theorem score_gram_floor (v : Fin 3 → ℝ) :
    176 / 225 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)
      ≤ 176 / 225 * v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]

/-- The `K₄` coboundary Gram (graph Laplacian) acts as `4·I` on
the mean-zero space `W₀ = 𝟏₄^⊥`. -/
theorem k4_laplacian_gap (v : Fin 4 → ℂ)
    (hv : v 0 + v 1 + v 2 + v 3 = 0) :
    (Matrix.of fun i j : Fin 4 =>
        if i = j then (3 : ℂ) else -1).mulVec v
      = (4 : ℂ) • v := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    linear_combination -hv

/-- Boxed fibre-frame identity: `d*d = 4·I` transfers through
the Kronecker frame — `(d ⊗ I)*(I ⊗ G₀)(d ⊗ I) = 4·(I ⊗ G₀)`. -/
theorem tetrad_gram_kronecker {n m k : Type*}
    [Fintype m] [Fintype k] [DecidableEq n] [DecidableEq m]
    [DecidableEq k] (d : Matrix m n ℂ) (G : Matrix k k ℂ)
    (hd : dᴴ * d = (4 : ℂ) • 1) :
    (d ⊗ₖ (1 : Matrix k k ℂ))ᴴ
        * ((1 : Matrix m m ℂ) ⊗ₖ G)
        * (d ⊗ₖ (1 : Matrix k k ℂ))
      = (4 : ℂ) • ((1 : Matrix n n ℂ) ⊗ₖ G) := by
  have hct : (d ⊗ₖ (1 : Matrix k k ℂ))ᴴ
      = dᴴ ⊗ₖ (1 : Matrix k k ℂ) := by
    ext ⟨i, p⟩ ⟨j, q⟩
    rw [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply]
    by_cases hpq : p = q <;>
      simp [hpq, Matrix.one_apply, eq_comm]
  rw [hct, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  rw [hd, Matrix.smul_kronecker]

/-- The fibre-frame floor: `4·(176/225) = 704/225`. -/
theorem frame_floor_scaling : (4 : ℝ) * (176 / 225) = 704 / 225 := by
  norm_num

/-- The concrete score Gram `G₀` over `ℂ`. -/
noncomputable def scoreGram : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![176 / 225, 1, 1]

/-- Boxed innovation telescope: with `Gₙ = t·G₀`, `Cₙ = t·G₀`,
`H₂,ₙ = (t+τ)·G₀`, the Schur complement is exactly `τ·G₀`. -/
theorem schur_innovation_telescope (t τ : ℂ) (ht : t ≠ 0) :
    (t + τ) • scoreGram
        - (t • scoreGram) * (t • scoreGram)⁻¹ * (t • scoreGram)
      = τ • scoreGram := by
  have hsd : t • scoreGram
      = Matrix.diagonal ![t * (176 / 225), t, t] := by
    unfold scoreGram
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    fin_cases i <;> simp [smul_eq_mul]
  have hright : (t • scoreGram)
      * Matrix.diagonal ![225 / 176 * t⁻¹, t⁻¹, t⁻¹] = 1 := by
    rw [hsd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp <;> field_simp
  have hinv : (t • scoreGram)⁻¹
      = Matrix.diagonal ![225 / 176 * t⁻¹, t⁻¹, t⁻¹] :=
    Matrix.inv_eq_right_inv hright
  rw [hinv, hsd, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  unfold scoreGram
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · fin_cases i <;> simp [Matrix.diagonal]
    field_simp
    ring
  · simp [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij]

/-- Boxed diffusion algebra: `(1-ρ²)/(1-ρ)² = (1+ρ)/(1-ρ)`. -/
theorem diffusion_identity (ρ : ℝ) (hρ : ρ ≠ 1) :
    (1 - ρ ^ 2) / (1 - ρ) ^ 2 = (1 + ρ) / (1 - ρ) := by
  have h : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  field_simp
  ring

/-- At the proved renewal correlation `ρ = -7/15`, the diffusion
coefficient is `4/11`. -/
theorem diffusion_value :
    (1 + (-7 / 15 : ℝ)) / (1 - (-7 / 15)) = 4 / 11 := by
  norm_num

end NCG
