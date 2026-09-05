/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Causal-diamond curvature tomography
  (`lem:vvm-average`, `prop:explicit-tomography`,
   `prop:least-squares-tomography`, GR_emergence)

The van Vleck diamond response mixes the longitudinal and scalar
curvature channels through the rotationally symmetric second moments
`∫σσρ = τ²(A·uu + B·ĥ)` and the contraction `ĥ^{μν}R̂_{μν} = R̂ + R̂_uu`:

* `vvm_response_coefficients` — the mixing `(a, b) = ((A+B)/12, B/12)`
  of `lem:vvm-average`;
* `momentA`/`momentB` — the exact Beta-moment values of the
  polynomial profile family;
* `tomography_matrix_d3` — the `d = 3`, `(m,n) ∈ {(0,0),(0,2)}`
  moment matrix `M = [[1/240, 1/360], [19/6480, 1/648]]`;
* `tomography_det`, `tomography_inverse` — `det M = -1/583200` and
  `M⁻¹ = [[-900, 1620], [1710, -2430]]` (exact integer inverse);
* `ricci_reconstruction` — the responses determine both curvature
  channels;
* `rayleigh_row_addition` — adding a profile row adds `rrᵀ ⪰ 0` to
  the Gram matrix, so the least-squares Rayleigh lower bound (hence
  `σ_min`, hence `1/C_rec`) cannot decrease.

The Synge–DeWitt expansion `log Δ^{1/2} = (1/12)R̂_{μν}σ^μσ^ν + O(σ³)`
and the Beta-function evaluation of the profile moments are the
declared inputs.
-/

namespace NCG

/-- `lem:vvm-average` (coefficient collection): with second moments
`τ²(A·uu + B·ĥ)` and the contraction `ĥ^{μν}R̂_{μν} = R̂ + R̂_uu`, the
van Vleck response has coefficients `a = (A+B)/12`, `b = B/12`. -/
theorem vvm_response_coefficients {A B Ruu R hContr resp : ℝ}
    (hcontr : hContr = R + Ruu)
    (hresp : resp = 1 / 12 * (A * Ruu + B * hContr)) :
    resp = (A + B) / 12 * Ruu + B / 12 * R := by
  rw [hresp, hcontr]
  ring

/-- The longitudinal Beta moment of the polynomial diamond profile
family. -/
def momentA (m d : ℚ) : ℚ := 1 / (2 * (m + d + 2) * (m + d + 3))

/-- The transverse Beta moment of the polynomial diamond profile
family. -/
def momentB (m n d : ℚ) : ℚ :=
  (m + d + 1) / (4 * (d + 2 * n + 2) * (m + d + 3))

/-- `prop:explicit-tomography` (moment matrix): in `d = 3` the pair
`(m,n) = (0,0)` and `(0,2)` gives the exact matrix
`M = [[1/240, 1/360], [19/6480, 1/648]]`. -/
theorem tomography_matrix_d3 :
    (momentA 0 3 + momentB 0 0 3) / 12 = 1 / 240
      ∧ momentB 0 0 3 / 12 = 1 / 360
      ∧ (momentA 0 3 + momentB 0 2 3) / 12 = 19 / 6480
      ∧ momentB 0 2 3 / 12 = 1 / 648 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [momentA, momentB]

/-- `prop:explicit-tomography` (determinant): `det M = -1/583200`. -/
theorem tomography_det :
    (1 / 240 : ℚ) * (1 / 648) - 1 / 360 * (19 / 6480)
      = -(1 / 583200) := by
  norm_num

/-- `prop:explicit-tomography` (exact inverse): the displayed integer
matrix `[[-900, 1620], [1710, -2430]]` is a two-sided inverse of
`M`. -/
theorem tomography_inverse :
    (!![1 / 240, 1 / 360; 19 / 6480, 1 / 648] : Matrix (Fin 2) (Fin 2) ℚ)
        * !![-900, 1620; 1710, -2430] = 1
      ∧ (!![-900, 1620; 1710, -2430] : Matrix (Fin 2) (Fin 2) ℚ)
        * !![1 / 240, 1 / 360; 19 / 6480, 1 / 648] = 1 := by
  constructor <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        norm_num

/-- `prop:explicit-tomography` (reconstruction): the two diamond
responses determine both curvature channels through the exact integer
inverse. -/
theorem ricci_reconstruction {D1 D2 Ruu R : ℚ}
    (h1 : D1 = 1 / 240 * Ruu + 1 / 360 * R)
    (h2 : D2 = 19 / 6480 * Ruu + 1 / 648 * R) :
    Ruu = -900 * D1 + 1620 * D2 ∧ R = 1710 * D1 - 2430 * D2 := by
  constructor
  · rw [h1, h2]
    ring
  · rw [h1, h2]
    ring

/-- `prop:least-squares-tomography` (Rayleigh monotonicity): adding a
profile row `r` adds the positive-semidefinite Gram increment `rrᵀ`,
so any Rayleigh lower bound `m·‖x‖² ≤ ⟨x, Ax⟩` survives — the
least-squares `σ_min` cannot decrease and `C_rec = 1/σ_min` cannot
increase. -/
theorem rayleigh_row_addition {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (mval : ℝ)
    (hA : ∀ x : Fin n → ℝ,
      mval * (∑ i, x i ^ 2) ≤ ∑ i, x i * A.mulVec x i) :
    ∀ x : Fin n → ℝ,
      mval * (∑ i, x i ^ 2)
        ≤ ∑ i, x i * (A + Matrix.vecMulVec r r).mulVec x i := by
  intro x
  have hsplit : (∑ i, x i * (A + Matrix.vecMulVec r r).mulVec x i)
      = (∑ i, x i * A.mulVec x i)
        + ∑ i, x i * (Matrix.vecMulVec r r).mulVec x i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.add_mulVec]
    simp only [Pi.add_apply]
    ring
  have hrank1 : (∑ i, x i * (Matrix.vecMulVec r r).mulVec x i)
      = (∑ i, r i * x i) ^ 2 := by
    have hterm : ∀ i, (Matrix.vecMulVec r r).mulVec x i
        = r i * ∑ j, r j * x j := by
      intro i
      simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    calc (∑ i, x i * (Matrix.vecMulVec r r).mulVec x i)
        = ∑ i, x i * (r i * ∑ j, r j * x j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hterm i]
    _ = (∑ i, r i * x i) * ∑ j, r j * x j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (∑ i, r i * x i) ^ 2 := by ring
  rw [hsplit, hrank1]
  have h := hA x
  nlinarith [sq_nonneg (∑ i, r i * x i)]

end NCG
