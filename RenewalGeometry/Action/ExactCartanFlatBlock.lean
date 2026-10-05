/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactPhaseCompatibleConnection

/-!
# The flat Cartan block: explicit inverse, sup-norm lower bound, inertia `(12,12)` and coframe
  congruence (`eq:supp-exact-connection-normal-form`; the quadratic connection matrix of the
  emergent-spacetime manuscript)

The manuscript asserts that the quadratic connection matrix has inertia `(12,12)` and a uniform
least singular value, the Cartan quadratic block being "a coframe congruence of the invertible
flat Cartan block".  This file proves the flat statements exactly and the congruence.

* **Flat coefficient arrays.** `palCoeff_one`: `W_{ρσ}(1)^{KL} = δ^ρ_K δ^σ_L - δ^ρ_L δ^σ_K`;
  `piArr_one_zero/one/two`: `Π_i(1) = χ K_i` (boosts); `sigmaArr_one_zero_one`,
  `sigmaArr_one_zero_two`, `sigmaArr_one_one_two`: `Σ_12(1) = -χ J_3`, `Σ_13(1) = χ J_2`,
  `Σ_23(1) = -χ J_1` (i.e. `Σ_ij(1) = -χ ε_{ijk} J_k`); in coordinates `piArr_one`,
  `sigmaArr_one`.
* **Lie coordinates.** `bracket_iota_iota`: `[ι a, ι b] = ι (lieCoord a b)` with the explicit
  structure constants of `𝔰𝔬(1,3)` in the basis `lorBasis`.
* **The flat Cartan operator.** `cartanOp_flat`: `C(1) A (x) = χ · cartFlat (A x)`, where
  `cartFlat` lists the 24 coordinates, each `± a_{νl} ± a_{ν'l'}`.  It is block diagonal with
  eight `3 × 3` blocks (e.g. coordinates `(0,0), (2,5), (3,4)`), and `cartFlatInv` is its exact
  inverse (`cartFlatInv_cartFlat`, `cartFlat_cartFlatInv`), each entry `(±y ± y' ± y'')/2`.
* **Uniform lower bound (sup norm).** `cartanOp_flat_lower_bound_explicit`:
  `(2|χ|/3) ‖A‖ ≤ ‖C(1) A‖` for every `A : Conn N` (the constant is optimal for the sup norm:
  every row of `cartFlatInv` has absolute row sum `3/2`); `cartanOp_flat_lower_bound` (the
  existential form), `cartanOp_flat_injective`, `cartanOp_flat_surjective`.
* **Inertia `(12,12)`.** `flatHessForm a = ⟨cartFlat a, a⟩_b = Σ_{μk} g_k (cartFlat a)_{μk} a_{μk}`
  is the quadratic form of `H_{(μk),(νl)} = g_k · ∂(C A)_{μk}/∂A_{νl}` at `χ = 1`, and
  `qc_flat`: `q_1(A)(x) = (χ/2) · flatHessForm (A x)`.  `flatHess_inertia`: there are
  `12`-dimensional subspaces on which the form is positive, resp. negative, definite (explicit
  orthogonal eigenvectors `posEmbed`, `negEmbed`, `flatHessForm_posEmbed`,
  `flatHessForm_negEmbed`), and every positive (negative) definite subspace has dimension
  `≤ 12`; so the inertia is exactly `(12,12)`.
* **Coframe congruence.** `qc_congr`: for `det e ≠ 0`,
  `q_e(A)(x) = det e · q_1(T A)(x)` with `(T A)_K = Σ_μ (e⁻¹)_{μK} A_μ` (`congrConn e⁻¹`), from
  `q_e = χ det(e) r(e, [A, A])` (`qc_eq_chi_detR`) and `palatiniDensity_eq_det_mul_scalar`;
  `bdot_cartanOp_congr`: `⟨C(e)A, δ⟩_b = det e ⟨C(1)(TA), Tδ⟩_b`; and
  `cartanOp_injective_of_det_ne_zero`: `C(e)` is injective for every invertible constant
  coframe `e` and `χ ≠ 0`.
-/

open Finset

noncomputable section

namespace RenewalGeometry.ExactPhaseAction

open PalatiniEinsteinAlgebra

set_option linter.unusedSectionVars false

/-! ### The flat coefficient arrays -/

set_option maxRecDepth 100000 in
/-- Double contraction of permutation symbols:
`Σ_{μν} ε_{μνρσ} ε_{μνKL} = 2(δ_{ρK} δ_{σL} - δ_{ρL} δ_{σK})`. -/
theorem eps4_contract_flat : ∀ ρ σ K L : Fin 4,
    (∑ μ : Fin 4, ∑ ν : Fin 4, eps4 μ ν ρ σ * eps4 μ ν K L) =
      2 * (kdz ρ K * kdz σ L - kdz ρ L * kdz σ K) := by
  decide

/-- The flat coefficient bivector: `W_{ρσ}(1)^{KL} = δ^ρ_K δ^σ_L - δ^ρ_L δ^σ_K`. -/
theorem palCoeff_one (ρ σ K L : Fin 4) :
    palCoeff 1 ρ σ K L =
      (if ρ = K then 1 else 0) * (if σ = L then 1 else 0) -
        (if ρ = L then 1 else 0) * (if σ = K then 1 else 0) := by
  have h : (∑ μ : Fin 4, ∑ ν : Fin 4, epsR μ ν ρ σ * epsR μ ν K L) =
      2 * ((if ρ = K then 1 else 0) * (if σ = L then 1 else 0) -
        (if ρ = L then 1 else 0) * (if σ = K then 1 else 0)) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) (eps4_contract_flat ρ σ K L)
    simp only [Int.cast_sum, Int.cast_mul] at this
    rw [this]
    simp [kdz]
  have h2 : palCoeff 1 ρ σ K L =
      (1 / 2 : ℝ) * ∑ μ : Fin 4, ∑ ν : Fin 4, epsR μ ν ρ σ * epsR μ ν K L := by
    simp only [palCoeff, Matrix.of_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [h2, h]; ring

/-- `Π_1(1) = χ K_1`. -/
theorem piArr_one_zero (χ : ℝ) : piArr χ 1 0 = χ • lorBasis 0 := by
  ext K L
  fin_cases K <;> fin_cases L <;>
    simp [piArr, dualCoeff, Matrix.mul_apply, palCoeff_one, eta, minkowski, lorBasis,
      Matrix.transpose_apply]

/-- `Π_2(1) = χ K_2`. -/
theorem piArr_one_one (χ : ℝ) : piArr χ 1 1 = χ • lorBasis 1 := by
  ext K L
  fin_cases K <;> fin_cases L <;>
    simp [piArr, dualCoeff, Matrix.mul_apply, palCoeff_one, eta, minkowski, lorBasis,
      Matrix.transpose_apply]

/-- `Π_3(1) = χ K_3`. -/
theorem piArr_one_two (χ : ℝ) : piArr χ 1 2 = χ • lorBasis 2 := by
  ext K L
  fin_cases K <;> fin_cases L <;>
    simp [piArr, dualCoeff, Matrix.mul_apply, palCoeff_one, eta, minkowski, lorBasis,
      Matrix.transpose_apply]

/-- `Σ_12(1) = -χ J_3`. -/
theorem sigmaArr_one_zero_one (χ : ℝ) : sigmaArr χ 1 0 1 = -(χ • lorBasis 5) := by
  ext K L
  fin_cases K <;> fin_cases L <;>
    simp [sigmaArr, dualCoeff, Matrix.mul_apply, palCoeff_one, eta, minkowski, lorBasis,
      Matrix.transpose_apply]

/-- `Σ_13(1) = χ J_2`. -/
theorem sigmaArr_one_zero_two (χ : ℝ) : sigmaArr χ 1 0 2 = χ • lorBasis 4 := by
  ext K L
  fin_cases K <;> fin_cases L <;>
    simp [sigmaArr, dualCoeff, Matrix.mul_apply, palCoeff_one, eta, minkowski, lorBasis,
      Matrix.transpose_apply]

/-- `Σ_23(1) = -χ J_1`. -/
theorem sigmaArr_one_one_two (χ : ℝ) : sigmaArr χ 1 1 2 = -(χ • lorBasis 3) := by
  ext K L
  fin_cases K <;> fin_cases L <;>
    simp [sigmaArr, dualCoeff, Matrix.mul_apply, palCoeff_one, eta, minkowski, lorBasis,
      Matrix.transpose_apply]

/-- A basis element is `ι` of a coordinate unit vector. -/
theorem lorBasis_eq_iota (k : Fin 6) : lorBasis k = iota (Pi.single k 1) := by
  simp [iota, Pi.single_apply]

/-- `ι (c e_k) = c G_k`. -/
theorem iota_single (k : Fin 6) (c : ℝ) : iota (Pi.single k c) = c • lorBasis k := by
  rw [lorBasis_eq_iota, ← iota_smul]
  congr 1
  ext l
  by_cases h : l = k
  · subst h; simp
  · simp [h]

/-- Lorentz coordinates of the flat `Π_i(1) = χ K_i`. -/
def piVec (χ : ℝ) (i : Fin 3) : Fin 6 → ℝ := Pi.single (Fin.castLE (by norm_num) i) χ

/-- Lorentz coordinates of the flat `Σ_ij(1) = -χ ε_{ijk} J_k`. -/
def sigVec (χ : ℝ) : Fin 3 → Fin 3 → Fin 6 → ℝ :=
  ![![0, Pi.single 5 (-χ), Pi.single 4 χ],
    ![Pi.single 5 χ, 0, Pi.single 3 (-χ)],
    ![Pi.single 4 (-χ), Pi.single 3 χ, 0]]

/-- `Π_i(1) = ι (piVec χ i)`. -/
theorem piArr_one (χ : ℝ) (i : Fin 3) : piArr χ 1 i = iota (piVec χ i) := by
  rw [piVec, iota_single]
  fin_cases i
  · exact piArr_one_zero χ
  · exact piArr_one_one χ
  · exact piArr_one_two χ

/-- `Σ_ij(1) = ι (sigVec χ i j)` for all ordered pairs. -/
theorem sigmaArr_one (χ : ℝ) (i j : Fin 3) : sigmaArr χ 1 i j = iota (sigVec χ i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [sigVec, iota_single, sigmaArr_diag, iota_zero, sigmaArr_one_zero_one,
      sigmaArr_one_zero_two, sigmaArr_one_one_two, sigmaArr_swap χ 1 0 1, sigmaArr_swap χ 1 0 2,
      sigmaArr_swap χ 1 1 2]

/-! ### Structure constants -/

/-- The Lie bracket of `𝔰𝔬(1,3)` in the coordinates of `lorBasis`:
`[ι a, ι b] = ι (lieCoord a b)`. -/
def lieCoord (a b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![a 2 * b 4 - a 4 * b 2 - a 1 * b 5 + a 5 * b 1,
    a 0 * b 5 - a 5 * b 0 - a 2 * b 3 + a 3 * b 2,
    a 1 * b 3 - a 3 * b 1 - a 0 * b 4 + a 4 * b 0,
    a 1 * b 2 - a 2 * b 1 - a 4 * b 5 + a 5 * b 4,
    a 3 * b 5 - a 5 * b 3 - a 0 * b 2 + a 2 * b 0,
    a 0 * b 1 - a 1 * b 0 - a 3 * b 4 + a 4 * b 3]

set_option maxHeartbeats 1000000 in
-- 16 entrywise cases of a 6-term matrix sum
/-- **Structure constants**: `[ι a, ι b] = ι (lieCoord a b)`. -/
theorem bracket_iota_iota (a b : Fin 6 → ℝ) :
    bracket (iota a) (iota b) = iota (lieCoord a b) := by
  ext K L
  fin_cases K <;> fin_cases L <;>
    simp [bracket, iota, Fin.sum_univ_succ, lorBasis, lieCoord, Matrix.sum_apply] <;> ring

/-! ### The flat Cartan operator and its inverse -/

/-- The flat Cartan block (`χ = 1`, `e = 1`) on the 24 local coordinates `a_{μk}`. -/
def cartFlat (a : Fin 4 → Fin 6 → ℝ) : Fin 4 → Fin 6 → ℝ :=
  ![![a 2 5 - a 3 4, -a 1 5 + a 3 3, a 1 4 - a 2 3, -a 2 2 + a 3 1, a 1 2 - a 3 0, -a 1 1 + a 2 0],
    ![a 2 1 + a 3 2, a 0 5 - a 2 0, -a 0 4 - a 3 0, a 2 4 + a 3 5, -a 0 2 - a 2 3, a 0 1 - a 3 3],
    ![-a 0 5 - a 1 1, a 1 0 + a 3 2, a 0 3 - a 3 1, a 0 2 - a 1 4, a 1 3 + a 3 5, -a 0 0 - a 3 4],
    ![a 0 4 - a 1 2, -a 0 3 - a 2 2, a 1 0 + a 2 1, -a 0 1 - a 1 5, a 0 0 - a 2 5, a 1 3 + a 2 4]]

/-- The exact inverse of the flat Cartan block (blockwise inverse of the eight `3 × 3`
blocks). -/
def cartFlatInv (y : Fin 4 → Fin 6 → ℝ) : Fin 4 → Fin 6 → ℝ :=
  ![![(y 0 0 - y 2 5 + y 3 4) / 2, (y 0 1 + y 1 5 - y 3 3) / 2, (y 0 2 - y 1 4 + y 2 3) / 2,
      (y 0 3 + y 2 2 - y 3 1) / 2, (y 0 4 - y 1 2 + y 3 0) / 2, (y 0 5 + y 1 1 - y 2 0) / 2],
    ![(-y 1 0 + y 2 1 + y 3 2) / 2, (-y 0 5 - y 1 1 - y 2 0) / 2, (y 0 4 - y 1 2 - y 3 0) / 2,
      (-y 1 3 + y 2 4 + y 3 5) / 2, (y 0 2 - y 1 4 - y 2 3) / 2, (-y 0 1 - y 1 5 - y 3 3) / 2],
    ![(y 0 5 - y 1 1 - y 2 0) / 2, (y 1 0 - y 2 1 + y 3 2) / 2, (-y 0 3 - y 2 2 - y 3 1) / 2,
      (-y 0 2 - y 1 4 - y 2 3) / 2, (y 1 3 - y 2 4 + y 3 5) / 2, (y 0 0 - y 2 5 - y 3 4) / 2],
    ![(-y 0 4 - y 1 2 - y 3 0) / 2, (y 0 3 - y 2 2 - y 3 1) / 2, (y 1 0 + y 2 1 - y 3 2) / 2,
      (y 0 1 - y 1 5 - y 3 3) / 2, (-y 0 0 - y 2 5 - y 3 4) / 2, (y 1 3 + y 2 4 - y 3 5) / 2]]

/-- `cartFlatInv` is a left inverse of `cartFlat`. -/
theorem cartFlatInv_cartFlat (a : Fin 4 → Fin 6 → ℝ) : cartFlatInv (cartFlat a) = a := by
  funext μ k
  fin_cases μ <;> fin_cases k <;> simp [cartFlatInv, cartFlat] <;> ring

/-- `cartFlatInv` is a right inverse of `cartFlat`. -/
theorem cartFlat_cartFlatInv (y : Fin 4 → Fin 6 → ℝ) : cartFlat (cartFlatInv y) = y := by
  funext μ k
  fin_cases μ <;> fin_cases k <;> simp [cartFlatInv, cartFlat] <;> ring

/-- Entrywise bound for the inverse: `|cartFlatInv y|_{μk} ≤ (3/2) max |y|`. -/
theorem abs_cartFlatInv_le (y : Fin 4 → Fin 6 → ℝ) (M : ℝ) (h : ∀ ν l, |y ν l| ≤ M)
    (μ : Fin 4) (k : Fin 6) : |cartFlatInv y μ k| ≤ 3 / 2 * M := by
  rw [abs_le]
  fin_cases μ <;> fin_cases k <;> simp only [cartFlatInv] <;> simp
  · constructor <;>
      linarith [h 0 0, h 2 5, h 3 4, le_abs_self (y 0 0), le_abs_self (y 2 5),
        le_abs_self (y 3 4), neg_abs_le (y 0 0), neg_abs_le (y 2 5), neg_abs_le (y 3 4)]
  · constructor <;>
      linarith [h 0 1, h 1 5, h 3 3, le_abs_self (y 0 1), le_abs_self (y 1 5),
        le_abs_self (y 3 3), neg_abs_le (y 0 1), neg_abs_le (y 1 5), neg_abs_le (y 3 3)]
  · constructor <;>
      linarith [h 0 2, h 1 4, h 2 3, le_abs_self (y 0 2), le_abs_self (y 1 4),
        le_abs_self (y 2 3), neg_abs_le (y 0 2), neg_abs_le (y 1 4), neg_abs_le (y 2 3)]
  · constructor <;>
      linarith [h 0 3, h 2 2, h 3 1, le_abs_self (y 0 3), le_abs_self (y 2 2),
        le_abs_self (y 3 1), neg_abs_le (y 0 3), neg_abs_le (y 2 2), neg_abs_le (y 3 1)]
  · constructor <;>
      linarith [h 0 4, h 1 2, h 3 0, le_abs_self (y 0 4), le_abs_self (y 1 2),
        le_abs_self (y 3 0), neg_abs_le (y 0 4), neg_abs_le (y 1 2), neg_abs_le (y 3 0)]
  · constructor <;>
      linarith [h 0 5, h 1 1, h 2 0, le_abs_self (y 0 5), le_abs_self (y 1 1),
        le_abs_self (y 2 0), neg_abs_le (y 0 5), neg_abs_le (y 1 1), neg_abs_le (y 2 0)]
  · constructor <;>
      linarith [h 1 0, h 2 1, h 3 2, le_abs_self (y 1 0), le_abs_self (y 2 1),
        le_abs_self (y 3 2), neg_abs_le (y 1 0), neg_abs_le (y 2 1), neg_abs_le (y 3 2)]
  · constructor <;>
      linarith [h 0 5, h 1 1, h 2 0, le_abs_self (y 0 5), le_abs_self (y 1 1),
        le_abs_self (y 2 0), neg_abs_le (y 0 5), neg_abs_le (y 1 1), neg_abs_le (y 2 0)]
  · constructor <;>
      linarith [h 0 4, h 1 2, h 3 0, le_abs_self (y 0 4), le_abs_self (y 1 2),
        le_abs_self (y 3 0), neg_abs_le (y 0 4), neg_abs_le (y 1 2), neg_abs_le (y 3 0)]
  · constructor <;>
      linarith [h 1 3, h 2 4, h 3 5, le_abs_self (y 1 3), le_abs_self (y 2 4),
        le_abs_self (y 3 5), neg_abs_le (y 1 3), neg_abs_le (y 2 4), neg_abs_le (y 3 5)]
  · constructor <;>
      linarith [h 0 2, h 1 4, h 2 3, le_abs_self (y 0 2), le_abs_self (y 1 4),
        le_abs_self (y 2 3), neg_abs_le (y 0 2), neg_abs_le (y 1 4), neg_abs_le (y 2 3)]
  · constructor <;>
      linarith [h 0 1, h 1 5, h 3 3, le_abs_self (y 0 1), le_abs_self (y 1 5),
        le_abs_self (y 3 3), neg_abs_le (y 0 1), neg_abs_le (y 1 5), neg_abs_le (y 3 3)]
  · constructor <;>
      linarith [h 0 5, h 1 1, h 2 0, le_abs_self (y 0 5), le_abs_self (y 1 1),
        le_abs_self (y 2 0), neg_abs_le (y 0 5), neg_abs_le (y 1 1), neg_abs_le (y 2 0)]
  · constructor <;>
      linarith [h 1 0, h 2 1, h 3 2, le_abs_self (y 1 0), le_abs_self (y 2 1),
        le_abs_self (y 3 2), neg_abs_le (y 1 0), neg_abs_le (y 2 1), neg_abs_le (y 3 2)]
  · constructor <;>
      linarith [h 0 3, h 2 2, h 3 1, le_abs_self (y 0 3), le_abs_self (y 2 2),
        le_abs_self (y 3 1), neg_abs_le (y 0 3), neg_abs_le (y 2 2), neg_abs_le (y 3 1)]
  · constructor <;>
      linarith [h 0 2, h 1 4, h 2 3, le_abs_self (y 0 2), le_abs_self (y 1 4),
        le_abs_self (y 2 3), neg_abs_le (y 0 2), neg_abs_le (y 1 4), neg_abs_le (y 2 3)]
  · constructor <;>
      linarith [h 1 3, h 2 4, h 3 5, le_abs_self (y 1 3), le_abs_self (y 2 4),
        le_abs_self (y 3 5), neg_abs_le (y 1 3), neg_abs_le (y 2 4), neg_abs_le (y 3 5)]
  · constructor <;>
      linarith [h 0 0, h 2 5, h 3 4, le_abs_self (y 0 0), le_abs_self (y 2 5),
        le_abs_self (y 3 4), neg_abs_le (y 0 0), neg_abs_le (y 2 5), neg_abs_le (y 3 4)]
  · constructor <;>
      linarith [h 0 4, h 1 2, h 3 0, le_abs_self (y 0 4), le_abs_self (y 1 2),
        le_abs_self (y 3 0), neg_abs_le (y 0 4), neg_abs_le (y 1 2), neg_abs_le (y 3 0)]
  · constructor <;>
      linarith [h 0 3, h 2 2, h 3 1, le_abs_self (y 0 3), le_abs_self (y 2 2),
        le_abs_self (y 3 1), neg_abs_le (y 0 3), neg_abs_le (y 2 2), neg_abs_le (y 3 1)]
  · constructor <;>
      linarith [h 1 0, h 2 1, h 3 2, le_abs_self (y 1 0), le_abs_self (y 2 1),
        le_abs_self (y 3 2), neg_abs_le (y 1 0), neg_abs_le (y 2 1), neg_abs_le (y 3 2)]
  · constructor <;>
      linarith [h 0 1, h 1 5, h 3 3, le_abs_self (y 0 1), le_abs_self (y 1 5),
        le_abs_self (y 3 3), neg_abs_le (y 0 1), neg_abs_le (y 1 5), neg_abs_le (y 3 3)]
  · constructor <;>
      linarith [h 0 0, h 2 5, h 3 4, le_abs_self (y 0 0), le_abs_self (y 2 5),
        le_abs_self (y 3 4), neg_abs_le (y 0 0), neg_abs_le (y 2 5), neg_abs_le (y 3 4)]
  · constructor <;>
      linarith [h 1 3, h 2 4, h 3 5, le_abs_self (y 1 3), le_abs_self (y 2 4),
        le_abs_self (y 3 5), neg_abs_le (y 1 3), neg_abs_le (y 2 4), neg_abs_le (y 3 5)]

variable {N : ℕ} [NeZero N]

set_option maxHeartbeats 1000000 in
-- 24 coordinate cases unfolding the structure constants
/-- **The flat Cartan operator in coordinates**: `C(1) A (x) = χ · cartFlat (A x)`. -/
theorem cartanOp_flat (χ : ℝ) (A : Conn N) (x : Site N) :
    cartanOp χ (fun _ => 1) A x = χ • cartFlat (A x) := by
  funext μ k
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp only [cartanOp, Fin.cases_zero, cart0, toA, piArr_one, bracket_iota_iota, coord_sum,
      coord_iota]
    fin_cases k <;> simp [Fin.sum_univ_three, lieCoord, piVec, cartFlat, Pi.single_apply] <;> ring
  · simp only [cartanOp, Fin.cases_succ, cartSp, toA0, toA, piArr_one, sigmaArr_one,
      bracket_iota_iota, coord_sum, coord_add, coord_iota]
    fin_cases i <;> fin_cases k <;>
      simp [Fin.sum_univ_three, lieCoord, piVec, sigVec, cartFlat] <;> ring

/-! ### Uniform lower bound, injectivity and surjectivity at the flat coframe -/

/-- **Sup-norm lower bound for the flat Cartan operator**:
`(2|χ|/3) ‖A‖ ≤ ‖C(1) A‖`. -/
theorem cartanOp_flat_lower_bound_explicit (χ : ℝ) (hχ : χ ≠ 0) (A : Conn N) :
    2 * |χ| / 3 * ‖A‖ ≤ ‖cartanOp χ (fun _ => 1) A‖ := by
  set M := ‖cartanOp χ (fun _ => 1) A‖ with hMdef
  have hM : 0 ≤ M := norm_nonneg _
  have hχ' : 0 < |χ| := abs_pos.mpr hχ
  have hentry : ∀ x ν l, |cartFlat (A x) ν l| * |χ| ≤ M := by
    intro x ν l
    have h1 : ‖cartanOp χ (fun _ => 1) A x ν l‖ ≤ M :=
      (norm_le_pi_norm _ l).trans ((norm_le_pi_norm _ ν).trans (norm_le_pi_norm _ x))
    rw [cartanOp_flat, Real.norm_eq_abs] at h1
    simpa [abs_mul, mul_comm] using h1
  have hnn : 0 ≤ 3 / 2 * (M / |χ|) := mul_nonneg (by norm_num) (div_nonneg hM hχ'.le)
  have hA : ‖A‖ ≤ 3 / 2 * (M / |χ|) := by
    refine (pi_norm_le_iff_of_nonneg hnn).mpr fun x => ?_
    refine (pi_norm_le_iff_of_nonneg hnn).mpr fun μ => ?_
    refine (pi_norm_le_iff_of_nonneg hnn).mpr fun k => ?_
    rw [Real.norm_eq_abs, ← cartFlatInv_cartFlat (A x)]
    refine abs_cartFlatInv_le _ _ (fun ν l => ?_) μ k
    rw [le_div_iff₀ hχ']
    exact hentry x ν l
  calc 2 * |χ| / 3 * ‖A‖ ≤ 2 * |χ| / 3 * (3 / 2 * (M / |χ|)) := by gcongr
    _ = M := by field_simp

/-- **Uniform least singular value of the flat Cartan operator** (sup norm): there is
`c > 0` (namely `c = 2|χ|/3`) with `c ‖A‖ ≤ ‖C(1) A‖` for all `A`. -/
theorem cartanOp_flat_lower_bound (χ : ℝ) (hχ : χ ≠ 0) :
    ∃ c > 0, ∀ A : Conn N, c * ‖A‖ ≤ ‖cartanOp χ (fun _ => 1) A‖ :=
  ⟨2 * |χ| / 3, by have := abs_pos.mpr hχ; positivity,
    cartanOp_flat_lower_bound_explicit χ hχ⟩

/-- The flat Cartan operator is injective (`χ ≠ 0`). -/
theorem cartanOp_flat_injective (χ : ℝ) (hχ : χ ≠ 0) :
    Function.Injective (cartanOp χ (fun _ : Site N => (1 : M4))) := by
  intro A B h
  funext x
  have h1 := congrFun h x
  rw [cartanOp_flat, cartanOp_flat] at h1
  have h2 := smul_right_injective _ hχ h1
  rw [← cartFlatInv_cartFlat (A x), h2, cartFlatInv_cartFlat]

/-- The flat Cartan operator is surjective (`χ ≠ 0`); with injectivity it is invertible. -/
theorem cartanOp_flat_surjective (χ : ℝ) (hχ : χ ≠ 0) :
    Function.Surjective (cartanOp χ (fun _ : Site N => (1 : M4))) := by
  intro B
  refine ⟨fun x => cartFlatInv (χ⁻¹ • B x), ?_⟩
  funext x
  rw [cartanOp_flat, cartFlat_cartFlatInv, smul_smul, mul_inv_cancel₀ hχ, one_smul]

/-! ### Inertia `(12,12)` of the flat Cartan Hessian -/

/-- The flat Cartan Hessian form `a ↦ ⟨cartFlat a, a⟩_b = Σ_{μk} g_k (cartFlat a)_{μk} a_{μk}`,
the quadratic form of `H_{(μk),(νl)} = g_k ∂(cartFlat a)_{μk}/∂a_{νl}`. -/
def flatHessForm (a : Fin 4 → Fin 6 → ℝ) : ℝ := bdot (cartFlat a) a

/-- The flat Cartan form: `q_1(A)(x) = (χ/2) · flatHessForm (A x)`. -/
theorem qc_flat (χ : ℝ) (A : Conn N) (x : Site N) :
    qc χ (fun _ => 1) (toA0 A) (toA A) x = χ / 2 * flatHessForm (A x) := by
  have h : ∀ u v : Fin 4 → Fin 6 → ℝ, bdot (χ • u) v = χ * bdot u v := by
    intro u v
    simp only [bdot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [qc_eq_half, cartanOp_flat, flatHessForm, h]
  ring

/-- Twelve mutually `H`-orthogonal positive eigendirections of the flat Hessian. -/
def posEmbed (c : Fin 12 → ℝ) : Fin 4 → Fin 6 → ℝ :=
  ![![c 0 + c 1, c 2 - c 3, c 4 + c 5, c 6, -c 7, c 8],
    ![-c 9, c 8, c 7, -c 10 + c 11, c 4 - c 5, -c 2 - c 3],
    ![-c 8, -c 9, c 6, -2 * c 5, c 10 + c 11, c 0 - c 1],
    ![-c 7, -c 6, -c 9, -2 * c 3, -2 * c 1, -2 * c 11]]

/-- Twelve mutually `H`-orthogonal negative eigendirections of the flat Hessian. -/
def negEmbed (c : Fin 12 → ℝ) : Fin 4 → Fin 6 → ℝ :=
  ![![-c 0, c 1, -c 2, c 3 - c 4, c 5 + c 6, c 7 - c 8],
    ![-c 9 + c 10, -c 7 - c 8, c 5 - c 6, -c 11, c 2, c 1],
    ![-2 * c 8, c 9 + c 10, -c 3 - c 4, -c 2, -c 11, c 0],
    ![-2 * c 6, -2 * c 4, -2 * c 10, -c 1, -c 0, -c 11]]

/-- The positive weights `λ_i |f_i|²` of `posEmbed`. -/
def posWeight : Fin 12 → ℝ := ![4, 12, 4, 12, 4, 12, 12, 12, 12, 12, 4, 12]

/-- The absolute values of the negative weights of `negEmbed`. -/
def negWeight : Fin 12 → ℝ := ![12, 12, 12, 4, 12, 4, 12, 4, 12, 4, 12, 12]

set_option maxHeartbeats 1000000 in
-- expands a 24-term quadratic form in 12 variables
/-- Diagonalization on the positive part: `flatHessForm (posEmbed c) = Σ_i w⁺_i c_i²`. -/
theorem flatHessForm_posEmbed (c : Fin 12 → ℝ) :
    flatHessForm (posEmbed c) = ∑ i, posWeight i * c i ^ 2 := by
  simp [flatHessForm, bdot, cartFlat, posEmbed, posWeight, gram, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 1000000 in
-- expands a 24-term quadratic form in 12 variables
/-- Diagonalization on the negative part: `flatHessForm (negEmbed c) = -Σ_i w⁻_i c_i²`. -/
theorem flatHessForm_negEmbed (c : Fin 12 → ℝ) :
    flatHessForm (negEmbed c) = -∑ i, negWeight i * c i ^ 2 := by
  simp [flatHessForm, bdot, cartFlat, negEmbed, negWeight, gram, Fin.sum_univ_succ]
  ring

/-- `posEmbed` as a linear map. -/
def posEmbedL : (Fin 12 → ℝ) →ₗ[ℝ] (Fin 4 → Fin 6 → ℝ) where
  toFun := posEmbed
  map_add' c d := by funext μ k; fin_cases μ <;> fin_cases k <;> simp [posEmbed] <;> ring
  map_smul' r c := by funext μ k; fin_cases μ <;> fin_cases k <;> simp [posEmbed] <;> ring

/-- `negEmbed` as a linear map. -/
def negEmbedL : (Fin 12 → ℝ) →ₗ[ℝ] (Fin 4 → Fin 6 → ℝ) where
  toFun := negEmbed
  map_add' c d := by funext μ k; fin_cases μ <;> fin_cases k <;> simp [negEmbed] <;> ring
  map_smul' r c := by funext μ k; fin_cases μ <;> fin_cases k <;> simp [negEmbed] <;> ring

/-- The flat Hessian form vanishes at `0`. -/
theorem flatHessForm_zero : flatHessForm 0 = 0 := by simp [flatHessForm, bdot]

/-- A positively weighted sum of squares of a nonzero vector is positive. -/
theorem weighted_sq_sum_pos (w c : Fin 12 → ℝ) (hw : ∀ j, 0 < w j) (hc : c ≠ 0) :
    0 < ∑ i, w i * c i ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j).le (sq_nonneg _))
    ⟨i, Finset.mem_univ _,
      mul_pos (hw i) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))⟩

/-- The flat Hessian form is positive on `posEmbed c`, `c ≠ 0`. -/
theorem flatHessForm_posEmbed_pos (c : Fin 12 → ℝ) (hc : c ≠ 0) :
    0 < flatHessForm (posEmbed c) := by
  rw [flatHessForm_posEmbed]
  exact weighted_sq_sum_pos _ _ (fun j => by fin_cases j <;> norm_num [posWeight]) hc

/-- The flat Hessian form is negative on `negEmbed c`, `c ≠ 0`. -/
theorem flatHessForm_negEmbed_neg (c : Fin 12 → ℝ) (hc : c ≠ 0) :
    flatHessForm (negEmbed c) < 0 := by
  rw [flatHessForm_negEmbed, neg_lt_zero]
  exact weighted_sq_sum_pos _ _ (fun j => by fin_cases j <;> norm_num [negWeight]) hc

/-- `posEmbedL` is injective. -/
theorem posEmbedL_injective : Function.Injective posEmbedL := by
  refine (injective_iff_map_eq_zero posEmbedL).mpr fun c hc => ?_
  by_contra hne
  have h := flatHessForm_posEmbed_pos c hne
  have hc' : posEmbed c = 0 := hc
  rw [hc', flatHessForm_zero] at h
  exact lt_irrefl _ h

/-- `negEmbedL` is injective. -/
theorem negEmbedL_injective : Function.Injective negEmbedL := by
  refine (injective_iff_map_eq_zero negEmbedL).mpr fun c hc => ?_
  by_contra hne
  have h := flatHessForm_negEmbed_neg c hne
  have hc' : negEmbed c = 0 := hc
  rw [hc', flatHessForm_zero] at h
  exact lt_irrefl _ h

/-- The positive subspace has dimension `12`. -/
theorem finrank_range_posEmbedL : Module.finrank ℝ (LinearMap.range posEmbedL) = 12 := by
  rw [LinearMap.finrank_range_of_inj posEmbedL_injective, Module.finrank_fin_fun]

/-- The negative subspace has dimension `12`. -/
theorem finrank_range_negEmbedL : Module.finrank ℝ (LinearMap.range negEmbedL) = 12 := by
  rw [LinearMap.finrank_range_of_inj negEmbedL_injective, Module.finrank_fin_fun]

/-- Positivity on the positive subspace. -/
theorem flatHessForm_pos_of_mem_range {a : Fin 4 → Fin 6 → ℝ}
    (ha : a ∈ LinearMap.range posEmbedL) (h0 : a ≠ 0) : 0 < flatHessForm a := by
  obtain ⟨c, rfl⟩ := ha
  refine flatHessForm_posEmbed_pos c fun hc => h0 ?_
  rw [hc, map_zero]

/-- Negativity on the negative subspace. -/
theorem flatHessForm_neg_of_mem_range {a : Fin 4 → Fin 6 → ℝ}
    (ha : a ∈ LinearMap.range negEmbedL) (h0 : a ≠ 0) : flatHessForm a < 0 := by
  obtain ⟨c, rfl⟩ := ha
  refine flatHessForm_negEmbed_neg c fun hc => h0 ?_
  rw [hc, map_zero]

/-- The local coordinate space has dimension `24`. -/
theorem finrank_flatConn : Module.finrank ℝ (Fin 4 → Fin 6 → ℝ) = 24 := by
  simp [Module.finrank_pi_fintype]

/-- A subspace meeting a `12`-dimensional subspace trivially has dimension `≤ 12`. -/
theorem finrank_le_twelve_of_disjoint (V W : Submodule ℝ (Fin 4 → Fin 6 → ℝ))
    (hW : Module.finrank ℝ W = 12) (hVW : V ⊓ W = ⊥) : Module.finrank ℝ V ≤ 12 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V W
  rw [hVW, finrank_bot, add_zero, hW] at h1
  have h2 : Module.finrank ℝ (V ⊔ W : Submodule ℝ (Fin 4 → Fin 6 → ℝ)) ≤ 24 :=
    (Submodule.finrank_le _).trans_eq finrank_flatConn
  omega

/-- **Inertia `(12,12)` of the flat Cartan Hessian**: the form `flatHessForm` is positive
definite on a `12`-dimensional subspace and negative definite on a `12`-dimensional subspace,
and every subspace on which it is positive (negative) definite has dimension `≤ 12`. -/
theorem flatHess_inertia :
    (∃ P : Submodule ℝ (Fin 4 → Fin 6 → ℝ), Module.finrank ℝ P = 12 ∧
      ∀ a ∈ P, a ≠ 0 → 0 < flatHessForm a) ∧
    (∃ Q : Submodule ℝ (Fin 4 → Fin 6 → ℝ), Module.finrank ℝ Q = 12 ∧
      ∀ a ∈ Q, a ≠ 0 → flatHessForm a < 0) ∧
    (∀ V : Submodule ℝ (Fin 4 → Fin 6 → ℝ), (∀ a ∈ V, a ≠ 0 → 0 < flatHessForm a) →
      Module.finrank ℝ V ≤ 12) ∧
    (∀ V : Submodule ℝ (Fin 4 → Fin 6 → ℝ), (∀ a ∈ V, a ≠ 0 → flatHessForm a < 0) →
      Module.finrank ℝ V ≤ 12) := by
  refine ⟨⟨_, finrank_range_posEmbedL, fun a ha h0 => flatHessForm_pos_of_mem_range ha h0⟩,
    ⟨_, finrank_range_negEmbedL, fun a ha h0 => flatHessForm_neg_of_mem_range ha h0⟩,
    fun V hV => ?_, fun V hV => ?_⟩
  · refine finrank_le_twelve_of_disjoint V _ finrank_range_negEmbedL ?_
    rw [eq_bot_iff]
    rintro a ⟨haV, haW⟩
    rw [Submodule.mem_bot]
    by_contra h0
    exact lt_asymm (hV a haV h0) (flatHessForm_neg_of_mem_range haW h0)
  · refine finrank_le_twelve_of_disjoint V _ finrank_range_posEmbedL ?_
    rw [eq_bot_iff]
    rintro a ⟨haV, haW⟩
    rw [Submodule.mem_bot]
    by_contra h0
    exact lt_asymm (hV a haV h0) (flatHessForm_pos_of_mem_range haW h0)

/-! ### Coframe congruence and injectivity for every invertible coframe -/

/-- `ι` commutes with sums over the four spacetime directions. -/
theorem iota_finsum (c : Fin 4 → Fin 6 → ℝ) : iota (∑ μ, c μ) = ∑ μ, iota (c μ) := by
  simp [Fin.sum_univ_four, iota_add]

/-- Bilinearity of the bracket on finite combinations. -/
theorem bracket_finsum_finsum (a b : Fin 4 → ℝ) (X : Fin 4 → M4) :
    bracket (∑ μ, a μ • X μ) (∑ σ, b σ • X σ) =
      ∑ μ, ∑ σ, (a μ * b σ) • bracket (X μ) (X σ) := by
  simp only [bracket, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_comm]

/-- For `Z ∈ 𝔰𝔬(1,3)` the internal array `Z η` is antisymmetric. -/
theorem IsLorentz.mul_eta_transpose {Z : M4} (hZ : IsLorentz Z) :
    Matrix.transpose (Z * eta) = -(Z * eta) := by
  have h : Matrix.transpose Z * eta = -(eta * Z) := eq_neg_of_add_eq_zero_left hZ
  calc Matrix.transpose (Z * eta) = eta * Matrix.transpose Z := by
        rw [Matrix.transpose_mul, eta_transpose]
    _ = eta * (Matrix.transpose Z * eta) * eta := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, eta_mul_eta, Matrix.mul_one]
    _ = -(Z * eta) := by
        rw [h, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, eta_mul_eta, Matrix.one_mul]

/-- The curvature form with `E_i = [X_0, X_i]`, `B_ij = [X_i, X_j]` is `F_{ρσ} = [X_ρ, X_σ]`. -/
theorem curvForm_brackets (X : Fin 4 → M4) :
    curvForm (fun i => bracket (X 0) (X i.succ)) (fun i j => bracket (X i.succ) (X j.succ)) =
      fun ρ σ => bracket (X ρ) (X σ) := by
  funext ρ σ
  fin_cases ρ <;> fin_cases σ <;> simp [curvForm, bracket]

/-- `det(e) r(e, [X, X]) = det e · Σ (e⁻¹)_{μK} (e⁻¹)_{σL} ([X_μ, X_σ] η)^{KL}` for an
invertible coframe and Lorentz `X`. -/
theorem detR_brackets_eq (e : M4) (hdet : e.det ≠ 0) (X : Fin 4 → M4)
    (hX : ∀ μ, IsLorentz (X μ)) :
    detR e (fun i => bracket (X 0) (X i.succ)) (fun i j => bracket (X i.succ) (X j.succ)) =
      e.det * ∑ μ, ∑ σ, ∑ K, ∑ L, e⁻¹ μ K * e⁻¹ σ L * (bracket (X μ) (X σ) * eta) K L := by
  have hcf := curvForm_brackets X
  have h1 : ∀ K L ρ σ,
      curvArray (fun i => bracket (X 0) (X i.succ)) (fun i j => bracket (X i.succ) (X j.succ))
        L K ρ σ =
      -curvArray (fun i => bracket (X 0) (X i.succ)) (fun i j => bracket (X i.succ) (X j.succ))
        K L ρ σ := by
    intro K L ρ σ
    simp only [curvArray, hcf]
    have hL := ((hX ρ).bracket (hX σ)).mul_eta_transpose
    have := congrFun (congrFun hL K) L
    simpa [Matrix.transpose_apply, bracket] using this
  have h2 : ∀ K L ρ σ,
      curvArray (fun i => bracket (X 0) (X i.succ)) (fun i j => bracket (X i.succ) (X j.succ))
        K L σ ρ =
      -curvArray (fun i => bracket (X 0) (X i.succ)) (fun i j => bracket (X i.succ) (X j.succ))
        K L ρ σ := by
    intro K L ρ σ
    simp only [curvArray, curvForm_swap _ _ ρ σ, Matrix.neg_mul, Matrix.neg_apply]
  unfold detR
  rw [palatiniDensity_eq_det_mul_scalar e hdet _ h1 h2]
  congr 1
  simp only [scalarOf, ricciOf, coordCurvature, curvArray, hcf]

/-- At the flat coframe: `det(1) r(1, [Y, Y]) = Σ_{KL} ([Y_K, Y_L] η)^{KL}`. -/
theorem detR_one_brackets (Y : Fin 4 → M4) (hY : ∀ K, IsLorentz (Y K)) :
    detR 1 (fun i => bracket (Y 0) (Y i.succ)) (fun i j => bracket (Y i.succ) (Y j.succ)) =
      ∑ K, ∑ L, (bracket (Y K) (Y L) * eta) K L := by
  rw [detR_brackets_eq 1 (by simp) Y hY]
  simp [Matrix.one_apply]

/-- **Coframe congruence of the Palatini bracket density**: with `Y_K = Σ_μ (e⁻¹)_{μK} X_μ`,
`det(e) r(e, [X, X]) = det e · det(1) r(1, [Y, Y])`. -/
theorem detR_brackets_congr (e : M4) (hdet : e.det ≠ 0) (X Y : Fin 4 → M4)
    (hX : ∀ μ, IsLorentz (X μ)) (hY : ∀ K, Y K = ∑ μ, e⁻¹ μ K • X μ) :
    detR e (fun i => bracket (X 0) (X i.succ)) (fun i j => bracket (X i.succ) (X j.succ)) =
      e.det * detR 1 (fun i => bracket (Y 0) (Y i.succ))
        (fun i j => bracket (Y i.succ) (Y j.succ)) := by
  have hYL : ∀ K, IsLorentz (Y K) := by
    intro K
    rw [hY K]
    exact so13.sum_mem fun μ _ => so13.smul_mem _ (hX μ)
  rw [detR_brackets_eq e hdet X hX, detR_one_brackets Y hYL]
  congr 1
  simp only [hY, bracket_finsum_finsum, Finset.sum_mul, Matrix.smul_mul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  symm
  calc ∑ K, ∑ L, ∑ μ, ∑ σ, e⁻¹ μ K * e⁻¹ σ L * (bracket (X μ) (X σ) * eta) K L
      = ∑ K, ∑ μ, ∑ L, ∑ σ, e⁻¹ μ K * e⁻¹ σ L * (bracket (X μ) (X σ) * eta) K L :=
        Finset.sum_congr rfl fun K _ => Finset.sum_comm
    _ = ∑ μ, ∑ K, ∑ L, ∑ σ, e⁻¹ μ K * e⁻¹ σ L * (bracket (X μ) (X σ) * eta) K L :=
        Finset.sum_comm
    _ = ∑ μ, ∑ K, ∑ σ, ∑ L, e⁻¹ μ K * e⁻¹ σ L * (bracket (X μ) (X σ) * eta) K L :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun K _ => Finset.sum_comm
    _ = ∑ μ, ∑ σ, ∑ K, ∑ L, e⁻¹ μ K * e⁻¹ σ L * (bracket (X μ) (X σ) * eta) K L :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_comm

/-- The Cartan form is the Palatini density of the bracket curvature:
`q_e(A) = χ det(e) r(e, F)` with `E_i = [A_0, A_i]`, `B_ij = [A_i, A_j]`. -/
theorem qc_eq_chi_detR (χ : ℝ) (e A0 : Site N → M4) (A : Fin 3 → Site N → M4) (x : Site N) :
    qc χ e A0 A x =
      χ * detR (e x) (fun i => bracket (A0 x) (A i x)) (fun i j => bracket (A i x) (A j x)) := by
  rw [palatini_contraction]
  rfl

/-- The spacetime congruence `(T_E A)_{x,K} = Σ_μ E_{μK} A_{x,μ}` on coordinate connections. -/
def congrConn (E : M4) (A : Conn N) : Conn N := fun x K => ∑ μ, E μ K • A x μ

/-- Composition of congruences: `T_E ∘ T_{E'} = T_{E' E}`. -/
theorem congrConn_congrConn (E E' : M4) (A : Conn N) :
    congrConn E (congrConn E' A) = congrConn (E' * E) A := by
  funext x K k
  simp only [congrConn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
  ring

/-- `T_1 = id`. -/
theorem congrConn_one (A : Conn N) : congrConn 1 A = A := by
  funext x K
  simp [congrConn, Matrix.one_apply, ite_smul]

/-- `T_E` is additive. -/
theorem congrConn_add (E : M4) (A B : Conn N) :
    congrConn E (A + B) = congrConn E A + congrConn E B := by
  funext x K
  simp [congrConn, smul_add, Finset.sum_add_distrib]

/-- **Coframe congruence of the Cartan form**: for `det e ≠ 0`,
`q_e(A)(x) = det e · q_1(T_{e⁻¹} A)(x)`. -/
theorem qc_congr (χ : ℝ) (e : M4) (hdet : e.det ≠ 0) (A : Conn N) (x : Site N) :
    qc χ (fun _ => e) (toA0 A) (toA A) x =
      e.det * qc χ (fun _ => 1) (toA0 (congrConn e⁻¹ A)) (toA (congrConn e⁻¹ A)) x := by
  rw [qc_eq_chi_detR, qc_eq_chi_detR]
  have h := detR_brackets_congr e hdet (fun μ => iota (A x μ))
    (fun K => iota (congrConn e⁻¹ A x K)) (fun μ => isLorentz_iota _)
    (fun K => by simp only [congrConn, iota_finsum, iota_smul])
  simp only [toA0, toA]
  rw [h]
  ring

/-- Pairing with a coordinate unit vector: `⟨u, e_{μk}⟩_b = g_k u_{μk}`. -/
theorem bdot_single (u : Fin 4 → Fin 6 → ℝ) (μ : Fin 4) (k : Fin 6) :
    bdot u (Pi.single μ (Pi.single k 1)) = gram k * u μ k := by
  unfold bdot
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single k]
  · simp
  · intro l _ hl; simp [hl]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro ν _ hν; simp [hν]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Congruence of the Cartan operator**: `⟨C(e)A, δ⟩_b = det e · ⟨C(1)(TA), Tδ⟩_b`,
`T = T_{e⁻¹}`. -/
theorem bdot_cartanOp_congr (χ : ℝ) (e : M4) (hdet : e.det ≠ 0) (A δ : Conn N) (x : Site N) :
    bdot (cartanOp χ (fun _ => e) A x) (δ x) =
      e.det * bdot (cartanOp χ (fun _ => 1) (congrConn e⁻¹ A) x) (congrConn e⁻¹ δ x) := by
  have h1 := qc_add χ (fun _ => e) A δ x
  have h2 := qc_add χ (fun _ => 1) (congrConn e⁻¹ A) (congrConn e⁻¹ δ) x
  rw [← congrConn_add] at h2
  rw [qc_congr χ e hdet (A + δ), qc_congr χ e hdet A, qc_congr χ e hdet δ, h2] at h1
  linear_combination (-1 : ℝ) * h1

/-- **Injectivity of the Cartan operator for every invertible coframe** (`χ ≠ 0`,
`det e ≠ 0`): the Cartan block is a coframe congruence of the invertible flat block. -/
theorem cartanOp_injective_of_det_ne_zero (χ : ℝ) (hχ : χ ≠ 0) (e : M4) (hdet : e.det ≠ 0) :
    Function.Injective (cartanOp χ (fun _ : Site N => e)) := by
  intro A B hAB
  have hinv1 : e⁻¹ * e = 1 := Matrix.nonsing_inv_mul e (isUnit_iff_ne_zero.mpr hdet)
  have hinv2 : e * e⁻¹ = 1 := Matrix.mul_nonsing_inv e (isUnit_iff_ne_zero.mpr hdet)
  have hT : ∀ A : Conn N, congrConn e (congrConn e⁻¹ A) = A := fun A => by
    rw [congrConn_congrConn, hinv1, congrConn_one]
  have hT' : ∀ A : Conn N, congrConn e⁻¹ (congrConn e A) = A := fun A => by
    rw [congrConn_congrConn, hinv2, congrConn_one]
  have hflat : cartanOp χ (fun _ => 1) (congrConn e⁻¹ A) =
      cartanOp χ (fun _ => 1) (congrConn e⁻¹ B) := by
    funext x μ k
    have hA := bdot_cartanOp_congr χ e hdet A
      (congrConn e (fun _ => Pi.single μ (Pi.single k 1))) x
    have hB := bdot_cartanOp_congr χ e hdet B
      (congrConn e (fun _ => Pi.single μ (Pi.single k 1))) x
    rw [hAB, hB, hT'] at hA
    simp only [bdot_single] at hA
    have h3 := mul_left_cancel₀ hdet hA
    exact (mul_left_cancel₀ (gram_ne_zero k) h3).symm
  have h4 := cartanOp_flat_injective χ hχ hflat
  rw [← hT A, ← hT B, h4]

end RenewalGeometry.ExactPhaseAction

