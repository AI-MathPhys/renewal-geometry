/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactSqrtTriad
import RenewalGeometry.Action.ExactCartanFlatBlock

/-!
# Flat linearization of the Palatini coefficient arrays `Π_i(e)`, `Σ_ij(e)`
  (`eq:supp-exact-PiSigma`; ingredient of `thm:supp-exact-action-provenance` (iv),
  emergent-spacetime manuscript)

The coefficient bivector `W_{ρσ}(e) = ½ ε^{μνρσ} ε_{IJKL} e^I_μ e^J_ν` is a quadratic form in the
coframe, `W(e) = palBil e e`.  At the flat coframe `e = 1`:

* `palBil_one_add`: `W(1 + δ) = W(1) + W'(δ) + W(δ)` exactly, with the linear part
  `W'(δ)_{ρσ}^{KL} = Σ_{μ,I} δ^{μρσ}_{IKL} δ^I_μ` (`palLinA`, generalized Kronecker symbol
  `gdR`, from the contraction `eps4_contract_one`).
* Explicit flat linearizations in Lorentz coordinates (`coord`):
  `coordP (piLinA χ i δ) = χ • piLinVec δ i` (`Π_i`) and
  `coordP (sigLinA χ i j δ) = χ • sigLinVec δ i j` (`Σ_ij`).
* `hasFDerivAt_piArrP`, `hasFDerivAt_sigArrP`: the derivatives of the coordinate arrays
  `δ ↦ coord Π_i(1 + δ)`, `coord Σ_ij(1 + δ)` at the flat coframe are these explicit linear maps.

Arrays are plain functions `A4 = Fin 4 → Fin 4 → ℝ` with the sup norm.
-/

open Finset Matrix

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.QuadJet

open PalatiniEinsteinAlgebra

set_option linter.unusedSectionVars false

/-! ### Generic: quadratic remainders given by a continuous bilinear map -/

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- If `f(x₀ + d) - f(x₀) - L d = B d d` for a continuous bilinear `B`, then `f` has derivative
`L` at `x₀`. -/
theorem hasFDerivAt_of_bilinear_remainder {f : E → F} {L : E →L[ℝ] F} {x₀ : E}
    (B : E →L[ℝ] E →L[ℝ] F) (h : ∀ d, f (x₀ + d) - f x₀ - L d = B d d) :
    HasFDerivAt f L x₀ := by
  refine hasFDerivAt_of_sq_remainder ‖B‖ fun d => ?_
  rw [h]
  calc ‖B d d‖ ≤ ‖B d‖ * ‖d‖ := (B d).le_opNorm d
    _ ≤ ‖B‖ * ‖d‖ * ‖d‖ := by gcongr; exact B.le_opNorm d
    _ = ‖B‖ * ‖d‖ ^ 2 := by ring

/-- A bilinear map on a finite-dimensional space as a continuous bilinear map. -/
def toCLM₂ [FiniteDimensional ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] F) : E →L[ℝ] E →L[ℝ] F :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] F) ≃ₗ[ℝ] (E →L[ℝ] F)).toLinearMap ∘ₗ B)

@[simp] theorem toCLM₂_apply [FiniteDimensional ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] F) (a b : E) :
    toCLM₂ B a b = B a b := rfl

end Generic

/-! ### The bilinear coefficient bivector -/

/-- Plain `4 × 4` arrays (sup norm). -/
abbrev A4 := Fin 4 → Fin 4 → ℝ

/-- The flat coframe as an array. -/
def one4 : A4 := (1 : M4)

theorem one4_apply (a b : Fin 4) : one4 a b = if a = b then 1 else 0 := by
  simp [one4, Matrix.one_apply]

/-- The polarized coefficient bivector `½ ε^{μνρσ} ε_{IJKL} e^I_μ f^J_ν`. -/
def palBil (e f : A4) (ρ σ : Fin 4) : A4 := fun K L =>
  (1 / 2 : ℝ) * ∑ μ, ∑ ν, epsR μ ν ρ σ * ∑ I, ∑ J, epsR I J K L * e I μ * f J ν

theorem palCoeff_of (e : A4) (ρ σ : Fin 4) :
    palCoeff (Matrix.of e) ρ σ = Matrix.of (palBil e e ρ σ) := rfl

theorem palBil_add_left (e e' f : A4) (ρ σ : Fin 4) :
    palBil (e + e') f ρ σ = palBil e f ρ σ + palBil e' f ρ σ := by
  funext K L
  simp only [palBil, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

theorem palBil_add_right (e f f' : A4) (ρ σ : Fin 4) :
    palBil e (f + f') ρ σ = palBil e f ρ σ + palBil e f' ρ σ := by
  funext K L
  simp only [palBil, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

theorem palBil_smul_left (c : ℝ) (e f : A4) (ρ σ : Fin 4) :
    palBil (c • e) f ρ σ = c • palBil e f ρ σ := by
  funext K L
  simp only [palBil, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem palBil_smul_right (c : ℝ) (e f : A4) (ρ σ : Fin 4) :
    palBil e (c • f) ρ σ = c • palBil e f ρ σ := by
  funext K L
  simp only [palBil, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- `palBil` as a bilinear map. -/
def palBilLin (ρ σ : Fin 4) : A4 →ₗ[ℝ] A4 →ₗ[ℝ] A4 :=
  LinearMap.mk₂ ℝ (fun e f => palBil e f ρ σ) (fun e e' f => palBil_add_left e e' f ρ σ)
    (fun c e f => palBil_smul_left c e f ρ σ) (fun e f f' => palBil_add_right e f f' ρ σ)
    (fun c e f => palBil_smul_right c e f ρ σ)

/-- The generalized Kronecker symbol `δ^{mrs}_{gab} = Σ_n ε_{nmrs} ε_{ngab}`. -/
def gdR (m r s g a b : Fin 4) : ℝ := ∑ n, epsR n m r s * epsR n g a b

theorem gdR_eq (m r s g a b : Fin 4) :
    gdR m r s g a b =
      ((kdz m g * (kdz r a * kdz s b - kdz r b * kdz s a)
      - kdz m a * (kdz r g * kdz s b - kdz r b * kdz s g)
      + kdz m b * (kdz r g * kdz s a - kdz r a * kdz s g) : ℤ) : ℝ) := by
  rw [← eps4_contract_one]
  simp [gdR, epsR]

/-- The flat linearization `W'(δ)_{ρσ}^{KL} = Σ_{μ,I} δ^{μρσ}_{IKL} δ^I_μ`. -/
def palLinA (δ : A4) (ρ σ : Fin 4) : A4 := fun K L => ∑ μ, ∑ I, gdR μ ρ σ I K L * δ I μ

theorem palBil_one_left (δ : A4) (ρ σ K L : Fin 4) :
    palBil one4 δ ρ σ K L = (1 / 2 : ℝ) * ∑ μ, ∑ I, gdR μ ρ σ I K L * δ I μ := by
  unfold palBil gdR
  congr 1
  have h1 : ∀ μ ν : Fin 4, (∑ I, ∑ J, epsR I J K L * one4 I μ * δ J ν) =
      ∑ J, epsR μ J K L * δ J ν := by
    intro μ ν
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp [one4_apply, mul_comm, mul_left_comm]
  simp only [h1, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  refine Finset.sum_congr rfl fun μ _ => by ring

theorem palBil_one_right (δ : A4) (ρ σ K L : Fin 4) :
    palBil δ one4 ρ σ K L = (1 / 2 : ℝ) * ∑ μ, ∑ I, gdR μ ρ σ I K L * δ I μ := by
  unfold palBil gdR
  congr 1
  have h1 : ∀ μ ν : Fin 4, (∑ I, ∑ J, epsR I J K L * δ I μ * one4 J ν) =
      ∑ I, epsR I ν K L * δ I μ := by
    intro μ ν
    refine Finset.sum_congr rfl fun I _ => ?_
    simp [one4_apply, mul_comm]
  simp only [h1, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [epsR_swap01 μ ν ρ σ, epsR_swap01 ν I K L]
  ring

/-- **Exact flat expansion** `W(1 + δ) = W(1) + W'(δ) + W(δ)`. -/
theorem palBil_one_add (δ : A4) (ρ σ : Fin 4) :
    palBil (one4 + δ) (one4 + δ) ρ σ =
      palBil one4 one4 ρ σ + palLinA δ ρ σ + palBil δ δ ρ σ := by
  rw [palBil_add_left, palBil_add_right, palBil_add_right]
  funext K L
  simp only [Pi.add_apply, palBil_one_left, palBil_one_right, palLinA]
  ring

theorem palLinA_add (δ δ' : A4) (ρ σ : Fin 4) :
    palLinA (δ + δ') ρ σ = palLinA δ ρ σ + palLinA δ' ρ σ := by
  funext K L; simp [palLinA, mul_add, Finset.sum_add_distrib]

theorem palLinA_smul (c : ℝ) (δ : A4) (ρ σ : Fin 4) :
    palLinA (c • δ) ρ σ = c • palLinA δ ρ σ := by
  funext K L
  simp only [palLinA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ### Coordinates -/

/-- Lorentz coordinates of an array, `coordP X k = coord (Matrix.of X) k`. -/
def coordP (X : A4) : Fin 6 → ℝ := coord (Matrix.of X)

theorem coordP_add (X Y : A4) : coordP (X + Y) = coordP X + coordP Y := coord_add _ _

theorem coordP_smul (c : ℝ) (X : A4) : coordP (c • X) = c • coordP X := coord_smul _ _

/-- `coordP` as a linear map. -/
def coordPLin : A4 →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun := coordP
  map_add' := coordP_add
  map_smul' := coordP_smul

/-- The `b`-dual array `χ η Wᵀ` (the arrays `Π_i = χ η W_{0i}ᵀ`, `Σ_ij = χ η W_{ij}ᵀ`). -/
def dualA (χ : ℝ) (W : A4) : A4 := fun K L => χ * (eta * (Matrix.of W)ᵀ) K L

theorem dualA_add (χ : ℝ) (W W' : A4) : dualA χ (W + W') = dualA χ W + dualA χ W' := by
  funext K L
  simp only [dualA, Pi.add_apply]
  rw [show (Matrix.of (W + W'))ᵀ = (Matrix.of W)ᵀ + (Matrix.of W')ᵀ from rfl, Matrix.mul_add]
  simp [mul_add]

theorem dualA_smul (χ c : ℝ) (W : A4) : dualA χ (c • W) = c • dualA χ W := by
  funext K L
  simp only [dualA, Pi.smul_apply, smul_eq_mul]
  rw [show (Matrix.of (c • W))ᵀ = c • (Matrix.of W)ᵀ from rfl, Matrix.mul_smul]
  simp only [Matrix.smul_apply, smul_eq_mul]; ring

theorem piArr_of (χ : ℝ) (e : A4) (i : Fin 3) :
    piArr χ (Matrix.of e) i = Matrix.of (dualA χ (palBil e e 0 i.succ)) := by
  ext K L
  simp [piArr, dualCoeff, dualA, palCoeff_of, Matrix.smul_apply]

theorem sigmaArr_of (χ : ℝ) (e : A4) (i j : Fin 3) :
    sigmaArr χ (Matrix.of e) i j = Matrix.of (dualA χ (palBil e e i.succ j.succ)) := by
  ext K L
  simp [sigmaArr, dualCoeff, dualA, palCoeff_of, Matrix.smul_apply]

/-- The coordinate array `coord Π_i(e)` of an array coframe. -/
def piArrP (χ : ℝ) (i : Fin 3) (e : A4) : Fin 6 → ℝ := coordP (dualA χ (palBil e e 0 i.succ))

/-- The coordinate array `coord Σ_ij(e)` of an array coframe. -/
def sigArrP (χ : ℝ) (i j : Fin 3) (e : A4) : Fin 6 → ℝ :=
  coordP (dualA χ (palBil e e i.succ j.succ))

theorem piArrP_eq (χ : ℝ) (i : Fin 3) (e : A4) : piArrP χ i e = coord (piArr χ (Matrix.of e) i) := by
  rw [piArr_of]; rfl

theorem sigArrP_eq (χ : ℝ) (i j : Fin 3) (e : A4) :
    sigArrP χ i j e = coord (sigmaArr χ (Matrix.of e) i j) := by
  rw [sigmaArr_of]; rfl

/-! ### Explicit flat linearizations -/

/-- Coordinates of the flat linearization of `Π_i` (per unit `χ`). -/
def piLinVec (δ : A4) : Fin 3 → Fin 6 → ℝ :=
  ![![δ 2 2 + δ 3 3, -δ 1 2, -δ 1 3, 0, δ 0 3, -δ 0 2],
    ![-δ 2 1, δ 1 1 + δ 3 3, -δ 2 3, -δ 0 3, 0, δ 0 1],
    ![-δ 3 1, -δ 3 2, δ 1 1 + δ 2 2, δ 0 2, -δ 0 1, 0]]

/-- Coordinates of the flat linearization of `Σ_ij` (per unit `χ`; antisymmetric in `ij`). -/
def sigLinVec (δ : A4) : Fin 3 → Fin 3 → Fin 6 → ℝ :=
  ![![0, ![δ 2 0, -δ 1 0, 0, -δ 1 3, -δ 2 3, -δ 0 0 - δ 3 3],
        ![δ 3 0, 0, -δ 1 0, δ 1 2, δ 0 0 + δ 2 2, δ 3 2]],
    ![![-δ 2 0, δ 1 0, 0, δ 1 3, δ 2 3, δ 0 0 + δ 3 3], 0,
        ![0, δ 3 0, -δ 2 0, -δ 0 0 - δ 1 1, -δ 2 1, -δ 3 1]],
    ![![-δ 3 0, 0, δ 1 0, -δ 1 2, -δ 0 0 - δ 2 2, -δ 3 2],
        ![0, -δ 3 0, δ 2 0, δ 0 0 + δ 1 1, δ 2 1, δ 3 1], 0]]

/-- Entries of the `b`-dual array: `(χ η Wᵀ)_{KL} = χ η_{KK} W_{LK}`. -/
theorem dualA_apply (χ : ℝ) (W : A4) (K L : Fin 4) : dualA χ W K L = χ * (eta K K * W L K) := by
  simp only [dualA, eta, minkowski, Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.of_apply]
  rw [Matrix.diagonal_apply_eq]

/-- The explicit linearizations `W'(δ)_{0i}` and `W'(δ)_{ij}` (`i < j`). -/
def palLinE (δ : A4) : Fin 4 → Fin 4 → A4 := fun ρ σ =>
  match ρ, σ with
  | 0, 1 => ![![0, δ 2 2 + δ 3 3, -δ 1 2, -δ 1 3], ![-δ 2 2 - δ 3 3, 0, δ 0 2, δ 0 3],
      ![δ 1 2, -δ 0 2, 0, 0], ![δ 1 3, -δ 0 3, 0, 0]]
  | 0, 2 => ![![0, -δ 2 1, δ 1 1 + δ 3 3, -δ 2 3], ![δ 2 1, 0, -δ 0 1, 0],
      ![-δ 1 1 - δ 3 3, δ 0 1, 0, δ 0 3], ![δ 2 3, 0, -δ 0 3, 0]]
  | 0, 3 => ![![0, -δ 3 1, -δ 3 2, δ 1 1 + δ 2 2], ![δ 3 1, 0, 0, -δ 0 1],
      ![δ 3 2, 0, 0, -δ 0 2], ![-δ 1 1 - δ 2 2, δ 0 1, δ 0 2, 0]]
  | 1, 2 => ![![0, δ 2 0, -δ 1 0, 0], ![-δ 2 0, 0, δ 0 0 + δ 3 3, -δ 2 3],
      ![δ 1 0, -δ 0 0 - δ 3 3, 0, δ 1 3], ![0, δ 2 3, -δ 1 3, 0]]
  | 1, 3 => ![![0, δ 3 0, 0, -δ 1 0], ![-δ 3 0, 0, -δ 3 2, δ 0 0 + δ 2 2],
      ![0, δ 3 2, 0, -δ 1 2], ![δ 1 0, -δ 0 0 - δ 2 2, δ 1 2, 0]]
  | 2, 3 => ![![0, 0, δ 3 0, -δ 2 0], ![0, 0, δ 3 1, -δ 2 1],
      ![-δ 3 0, -δ 3 1, 0, δ 0 0 + δ 1 1], ![δ 2 0, δ 2 1, -δ 0 0 - δ 1 1, 0]]
  | _, _ => 0

set_option maxHeartbeats 4000000 in
-- 96 entries of generalized Kronecker sums
theorem palLinA_eq_palLinE (δ : A4) (ρ σ : Fin 4) (h : ρ < σ) :
    palLinA δ ρ σ = palLinE δ ρ σ := by
  funext K L
  fin_cases ρ <;> fin_cases σ <;> simp at h <;> fin_cases K <;> fin_cases L <;>
    simp [palLinA, palLinE, gdR_eq, kdz, Fin.sum_univ_four] <;> ring

theorem palLinA_swap (δ : A4) (ρ σ : Fin 4) : palLinA δ σ ρ = -palLinA δ ρ σ := by
  have h : ∀ m g a b : Fin 4, gdR m σ ρ g a b = -gdR m ρ σ g a b := by
    intro m g a b
    simp only [gdR, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [epsR_swap23 n m ρ σ]; ring
  funext K L
  simp only [palLinA, h, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem palLinA_diag (δ : A4) (ρ : Fin 4) : palLinA δ ρ ρ = 0 := by
  have := palLinA_swap δ ρ ρ
  funext K L
  have h := congrFun (congrFun this K) L
  simp only [Pi.neg_apply] at h
  simp only [Pi.zero_apply]
  linarith

set_option maxHeartbeats 4000000 in
-- 48 entries
/-- **Flat linearization of `Π_i`**: `χ η W'(δ)_{0i}ᵀ = ι(χ piLinVec δ i)`. -/
theorem of_dualA_palLinA_pi (χ : ℝ) (δ : A4) (i : Fin 3) :
    Matrix.of (dualA χ (palLinA δ 0 i.succ)) = iota (χ • piLinVec δ i) := by
  rw [palLinA_eq_palLinE δ 0 i.succ (Fin.succ_pos i)]
  ext K L
  fin_cases i <;> fin_cases K <;> fin_cases L <;>
    simp [dualA_apply, palLinE, iota, lorBasis, Fin.sum_univ_succ, piLinVec, eta, minkowski] <;>
    first | ring1 | (ring_nf; simp)

set_option maxHeartbeats 4000000 in
-- 48 entries
theorem of_dualA_palLinA_sig_lt (χ : ℝ) (δ : A4) (i j : Fin 3) (h : i < j) :
    Matrix.of (dualA χ (palLinA δ i.succ j.succ)) = iota (χ • sigLinVec δ i j) := by
  rw [palLinA_eq_palLinE δ i.succ j.succ (Fin.succ_lt_succ_iff.2 h)]
  ext K L
  fin_cases i <;> fin_cases j <;> simp at h <;> fin_cases K <;> fin_cases L <;>
    simp [dualA_apply, palLinE, iota, lorBasis, Fin.sum_univ_succ, sigLinVec, eta, minkowski] <;>
    first | ring1 | (ring_nf; simp)

theorem sigLinVec_swap (δ : A4) (i j : Fin 3) : sigLinVec δ j i = -sigLinVec δ i j := by
  funext k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [sigLinVec] <;> ring1

theorem sigLinVec_diag (δ : A4) (i : Fin 3) : sigLinVec δ i i = 0 := by
  funext k; fin_cases i <;> fin_cases k <;> simp [sigLinVec]

/-- **Flat linearization of `Π_i` in coordinates.** -/
theorem coordP_dualA_palLinA_pi (χ : ℝ) (δ : A4) (i : Fin 3) :
    coordP (dualA χ (palLinA δ 0 i.succ)) = χ • piLinVec δ i := by
  rw [coordP, of_dualA_palLinA_pi, coord_iota]

/-- **Flat linearization of `Σ_ij` in coordinates.** -/
theorem coordP_dualA_palLinA_sig (χ : ℝ) (δ : A4) (i j : Fin 3) :
    coordP (dualA χ (palLinA δ i.succ j.succ)) = χ • sigLinVec δ i j := by
  rcases lt_trichotomy i j with h | h | h
  · rw [coordP, of_dualA_palLinA_sig_lt χ δ i j h, coord_iota]
  · subst h
    rw [palLinA_diag, sigLinVec_diag]
    have : dualA χ (0 : A4) = 0 := by
      have := dualA_smul χ 0 (0 : A4); simpa using this
    rw [this, show (0 : A4) = (0 : ℝ) • (0 : A4) by simp, coordP_smul]; simp
  · rw [palLinA_swap, show -palLinA δ j.succ i.succ = (-1 : ℝ) • palLinA δ j.succ i.succ by simp,
      dualA_smul, coordP_smul, coordP, of_dualA_palLinA_sig_lt χ δ j i h, coord_iota,
      sigLinVec_swap]
    simp

/-! ### Derivatives at the flat coframe -/

/-- `dualA χ` as a linear map. -/
def dualALin (χ : ℝ) : A4 →ₗ[ℝ] A4 where
  toFun := dualA χ
  map_add' := dualA_add χ
  map_smul' c W := dualA_smul χ c W

/-- `palLinA · ρ σ` as a linear map. -/
def palLinALin (ρ σ : Fin 4) : A4 →ₗ[ℝ] A4 where
  toFun δ := palLinA δ ρ σ
  map_add' δ δ' := palLinA_add δ δ' ρ σ
  map_smul' c δ := palLinA_smul c δ ρ σ

/-- The derivative of `e ↦ coord Π_i(e)` at the flat coframe. -/
def piLinCLM (χ : ℝ) (i : Fin 3) : A4 →L[ℝ] (Fin 6 → ℝ) :=
  LinearMap.toContinuousLinearMap (coordPLin ∘ₗ dualALin χ ∘ₗ palLinALin 0 i.succ)

/-- The derivative of `e ↦ coord Σ_ij(e)` at the flat coframe. -/
def sigLinCLM (χ : ℝ) (i j : Fin 3) : A4 →L[ℝ] (Fin 6 → ℝ) :=
  LinearMap.toContinuousLinearMap (coordPLin ∘ₗ dualALin χ ∘ₗ palLinALin i.succ j.succ)

theorem piLinCLM_apply (χ : ℝ) (i : Fin 3) (δ : A4) : piLinCLM χ i δ = χ • piLinVec δ i :=
  coordP_dualA_palLinA_pi χ δ i

theorem sigLinCLM_apply (χ : ℝ) (i j : Fin 3) (δ : A4) :
    sigLinCLM χ i j δ = χ • sigLinVec δ i j :=
  coordP_dualA_palLinA_sig χ δ i j

theorem palBil_one4_add (δ : A4) (ρ σ : Fin 4) :
    palBil (one4 + δ) (one4 + δ) ρ σ =
      palBil one4 one4 ρ σ + palLinA δ ρ σ + palBil δ δ ρ σ := palBil_one_add δ ρ σ

/-- **`D coord Π_i(1) = χ piLinVec(·) i`.** -/
theorem hasFDerivAt_piArrP (χ : ℝ) (i : Fin 3) :
    HasFDerivAt (piArrP χ i) (piLinCLM χ i) one4 := by
  refine hasFDerivAt_of_bilinear_remainder
    (toCLM₂ ((palBilLin 0 i.succ).compr₂ (coordPLin ∘ₗ dualALin χ))) fun δ => ?_
  simp only [piArrP, palBil_one4_add, dualA_add, coordP_add, toCLM₂_apply,
    LinearMap.compr₂_apply, LinearMap.comp_apply]
  simp [piLinCLM, palBilLin, coordPLin, dualALin, palLinALin]
  abel

/-- **`D coord Σ_ij(1) = χ sigLinVec(·) i j`.** -/
theorem hasFDerivAt_sigArrP (χ : ℝ) (i j : Fin 3) :
    HasFDerivAt (sigArrP χ i j) (sigLinCLM χ i j) one4 := by
  refine hasFDerivAt_of_bilinear_remainder
    (toCLM₂ ((palBilLin i.succ j.succ).compr₂ (coordPLin ∘ₗ dualALin χ))) fun δ => ?_
  simp only [sigArrP, palBil_one4_add, dualA_add, coordP_add, toCLM₂_apply,
    LinearMap.compr₂_apply, LinearMap.comp_apply]
  simp [sigLinCLM, palBilLin, coordPLin, dualALin, palLinALin]
  abel

end RenewalGeometry.ExactPhaseAction.QuadJet
