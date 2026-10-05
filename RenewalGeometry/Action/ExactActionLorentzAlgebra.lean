/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.PalatiniEinsteinVariationAlgebra

/-!
# Lorentz algebra, invariant pairing and the Palatini coefficient arrays `Π_i(e)`, `Σ_ij(e)`
  (`eq:supp-exact-PiSigma`, `eq:supp-exact-full-palatini`; subsection
  `subsec:supp-exact-action-provenance` of the emergent-spacetime manuscript)

Internal algebra of the explicit phase-compatible finite action.

* `M4 = Matrix (Fin 4) (Fin 4) ℝ`; a connection value `X` is a matrix `X^I_J`; the Lorentz
  algebra `𝔰𝔬(1,3)` is `IsLorentz X ↔ Xᵀ η + η X = 0`, `η = diag(-1,1,1,1)`
  (`PalatiniEinsteinAlgebra.minkowski`).  `so13` is the corresponding submodule; it is closed
  under the bracket (`IsLorentz.bracket`).
* The invariant pairing `b(X, Y) = tr(X Y)` (`pairing`): `Ad`-invariant
  (`pairing_bracket` : `b(X, [Y, Z]) = b([X, Y], Z)`) and nondegenerate on `𝔰𝔬(1,3)`
  (`pairing_self_transpose`: `b(X, Xᵀ) = ‖X‖²_F` with `Xᵀ ∈ 𝔰𝔬(1,3)`).
* The curvature `F` of a connection is assembled from its electric components `E_i = F_{0i}`
  and its plaquette components `B_ij = F_ij` (`i < j`) as an antisymmetric array of
  `𝔰𝔬(1,3)` matrices (`curvForm`); its internal-index array is `F^{KL}_{ρσ} = (F_{ρσ} η)^{KL}`
  (`curvArray`).
* `det(e) r(e, F)` is the Palatini density in the permutation-symbol form
  `¼ ε^{μνρσ} ε_{IJKL} e^I_μ e^J_ν F^{KL}_{ρσ}` (`PalatiniEinsteinAlgebra.palatiniDensity`), a
  polynomial in `e`; for an invertible coframe it equals `det e · r(e, F)` with
  `r(e,F) = E^ρ_K E^σ_L F^{KL}_{ρσ}`, `E = e⁻¹` (`palatiniDensity_eq_det_mul_scalar`).
* The coefficient bivectors `W_{ρσ}(e)^{KL} = ½ ε^{μνρσ} ε_{IJKL} e^I_μ e^J_ν` (`palCoeff`) and
  the arrays `Π_i(e) = χ η W_{0i}(e)ᵀ`, `Σ_ij(e) = χ η W_{ij}(e)ᵀ` (`piArr`, `sigmaArr`).
  **Contraction identity `eq:supp-exact-PiSigma`** (`palatini_contraction`):
  `χ det(e) r(e,F) = Σ_i b(Π_i, E_i) + Σ_{i<j} b(Σ_ij, B_ij)` for all `E`, `B`.
  `Π_i, Σ_ij ∈ 𝔰𝔬(1,3)` (`isLorentz_piArr`, `isLorentz_sigmaArr`), `Σ_ji = -Σ_ij`.
-/

open Finset Matrix

noncomputable section

namespace RenewalGeometry.ExactPhaseAction

open PalatiniEinsteinAlgebra

/-- Real `4 × 4` matrices, the ambient algebra of `𝔰𝔬(1,3)` and of the coframe `e^I_μ`. -/
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

/-- The Minkowski fibre metric `η = diag(-1, 1, 1, 1)`. -/
abbrev eta : M4 := minkowski

theorem eta_transpose : etaᵀ = eta := by
  ext I K; simp [Matrix.transpose_apply, minkowski_symm]

theorem eta_mul_eta : eta * eta = 1 := by
  simp only [eta, minkowski, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num

/-! ### The Lorentz algebra -/

/-- `X ∈ 𝔰𝔬(1,3)`: `Xᵀ η + η X = 0` (i.e. `η X` is antisymmetric). -/
def IsLorentz (X : M4) : Prop := Xᵀ * eta + eta * X = 0

/-- The Lorentz algebra `𝔰𝔬(1,3)` as a submodule of `M4`. -/
def so13 : Submodule ℝ M4 where
  carrier := {X | IsLorentz X}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq, IsLorentz] at *
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᵀ * eta + Yᵀ * eta + (eta * X + eta * Y)
        = (Xᵀ * eta + eta * X) + (Yᵀ * eta + eta * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp [IsLorentz]
  smul_mem' c X hX := by
    simp only [Set.mem_ofPred_eq, IsLorentz] at *
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem mem_so13 {X : M4} : X ∈ so13 ↔ IsLorentz X := Iff.rfl

theorem IsLorentz.eta_mul {X : M4} (hX : IsLorentz X) : eta * X = -(Xᵀ * eta) :=
  eq_neg_of_add_eq_zero_right hX

/-- `𝔰𝔬(1,3)` is closed under the commutator `[X, Y] = XY - YX`. -/
theorem IsLorentz.bracket {X Y : M4} (hX : IsLorentz X) (hY : IsLorentz Y) :
    IsLorentz (X * Y - Y * X) := by
  have hX' := hX.eta_mul
  have hY' := hY.eta_mul
  unfold IsLorentz
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_sub,
    Matrix.sub_mul, ← Matrix.mul_assoc eta X Y, ← Matrix.mul_assoc eta Y X, hX', hY']
  simp only [Matrix.mul_assoc, Matrix.neg_mul, hX', hY', Matrix.mul_neg, neg_neg]
  abel

/-- A matrix `η A` with `A` antisymmetric lies in `𝔰𝔬(1,3)`. -/
theorem isLorentz_eta_mul {A : M4} (hA : Aᵀ = -A) : IsLorentz (eta * A) := by
  unfold IsLorentz
  rw [Matrix.transpose_mul, eta_transpose, hA]
  have h1 : eta * (eta * A) = A := by rw [← Matrix.mul_assoc, eta_mul_eta, Matrix.one_mul]
  rw [h1]
  simp only [Matrix.neg_mul, Matrix.mul_assoc, eta_mul_eta, Matrix.mul_one, neg_add_cancel]

/-- `𝔰𝔬(1,3)` is closed under transposition. -/
theorem IsLorentz.transpose {X : M4} (hX : IsLorentz X) : IsLorentz Xᵀ := by
  have hT : Xᵀ = -(eta * X * eta) := by
    calc Xᵀ = Xᵀ * eta * eta := by rw [Matrix.mul_assoc, eta_mul_eta, Matrix.mul_one]
      _ = -(eta * X) * eta := by rw [eq_neg_of_add_eq_zero_left hX]
      _ = -(eta * X * eta) := by rw [Matrix.neg_mul]
  unfold IsLorentz
  rw [Matrix.transpose_transpose, hT, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    eta_mul_eta, Matrix.one_mul, add_neg_cancel]

/-! ### The invariant pairing -/

/-- The fixed nondegenerate invariant pairing `b(X, Y) = tr(X Y)` on `𝔰𝔬(1,3)`. -/
def pairing (X Y : M4) : ℝ := Matrix.trace (X * Y)

theorem pairing_comm (X Y : M4) : pairing X Y = pairing Y X := Matrix.trace_mul_comm X Y

theorem pairing_add_left (X X' Y : M4) : pairing (X + X') Y = pairing X Y + pairing X' Y := by
  simp [pairing, Matrix.add_mul, Matrix.trace_add]

theorem pairing_add_right (X Y Y' : M4) : pairing X (Y + Y') = pairing X Y + pairing X Y' := by
  simp [pairing, Matrix.mul_add, Matrix.trace_add]

theorem pairing_sub_right (X Y Y' : M4) : pairing X (Y - Y') = pairing X Y - pairing X Y' := by
  simp [pairing, Matrix.mul_sub, Matrix.trace_sub]

theorem pairing_sub_left (X X' Y : M4) : pairing (X - X') Y = pairing X Y - pairing X' Y := by
  simp [pairing, Matrix.sub_mul, Matrix.trace_sub]

theorem pairing_neg_right (X Y : M4) : pairing X (-Y) = -pairing X Y := by
  simp [pairing]

theorem pairing_neg_left (X Y : M4) : pairing (-X) Y = -pairing X Y := by
  simp [pairing]

theorem pairing_smul_right (c : ℝ) (X Y : M4) : pairing X (c • Y) = c * pairing X Y := by
  simp [pairing, Matrix.trace_smul]

theorem pairing_smul_left (c : ℝ) (X Y : M4) : pairing (c • X) Y = c * pairing X Y := by
  simp [pairing, Matrix.trace_smul]

theorem pairing_zero_right (X : M4) : pairing X 0 = 0 := by simp [pairing]

theorem pairing_zero_left (X : M4) : pairing 0 X = 0 := by simp [pairing]

theorem pairing_sum_right {ι : Type*} (s : Finset ι) (X : M4) (Y : ι → M4) :
    pairing X (∑ i ∈ s, Y i) = ∑ i ∈ s, pairing X (Y i) := by
  simp [pairing, Finset.mul_sum, Matrix.trace_sum]

theorem pairing_sum_left {ι : Type*} (s : Finset ι) (X : ι → M4) (Y : M4) :
    pairing (∑ i ∈ s, X i) Y = ∑ i ∈ s, pairing (X i) Y := by
  simp [pairing, Finset.sum_mul, Matrix.trace_sum]

/-- The pairing as a bilinear map. -/
def pairingBilin : M4 →ₗ[ℝ] M4 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ pairing pairing_add_left (fun c X Y => pairing_smul_left c X Y)
    pairing_add_right (fun c X Y => pairing_smul_right c X Y)

@[simp] theorem pairingBilin_apply (X Y : M4) : pairingBilin X Y = pairing X Y := rfl

/-- **Invariance**: `b(X, [Y, Z]) = b([X, Y], Z)`. -/
theorem pairing_bracket (X Y Z : M4) :
    pairing X (Y * Z - Z * Y) = pairing (X * Y - Y * X) Z := by
  unfold pairing
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub, ← Matrix.mul_assoc X Y Z,
    ← Matrix.mul_assoc X Z Y, Matrix.trace_mul_cycle X Z Y]

/-- `Ad`-invariance of the pairing under conjugation. -/
theorem pairing_conj (X Y U V : M4) (hUV : V * U = 1) :
    pairing (U * X * V) (U * Y * V) = pairing X Y := by
  unfold pairing
  have : U * X * V * (U * Y * V) = U * (X * Y) * V := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V U, hUV, Matrix.one_mul]
  rw [this, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hUV, Matrix.one_mul]

/-- `b(X, Xᵀ) = Σ X_{IJ}²` (the Frobenius norm squared). -/
theorem pairing_self_transpose (X : M4) : pairing X Xᵀ = ∑ I, ∑ J, X I J ^ 2 := by
  simp [pairing, Matrix.trace, Matrix.mul_apply, sq]

/-- **Nondegeneracy on `𝔰𝔬(1,3)`**: if `b(X, Y) = 0` for all `Y ∈ 𝔰𝔬(1,3)` and
`X ∈ 𝔰𝔬(1,3)`, then `X = 0`. -/
theorem eq_zero_of_pairing_eq_zero {X : M4} (hX : IsLorentz X)
    (h : ∀ Y, IsLorentz Y → pairing X Y = 0) : X = 0 := by
  have h0 := h Xᵀ hX.transpose
  rw [pairing_self_transpose] at h0
  have hsq : ∀ I J, X I J ^ 2 = 0 := by
    intro I J
    have hnn : ∀ I, 0 ≤ ∑ J, X I J ^ 2 := fun I => sum_nonneg fun J _ => sq_nonneg _
    have hI := (sum_eq_zero_iff_of_nonneg (fun I _ => hnn I)).mp h0 I (mem_univ _)
    exact (sum_eq_zero_iff_of_nonneg (fun J _ => sq_nonneg (X I J))).mp hI J (mem_univ _)
  ext I J
  simpa using hsq I J

/-! ### The curvature two-form and its internal array -/

/-- The curvature two-form `F_{ρσ}` assembled from the electric components `E_i = F_{0i}` and
the plaquette components `B_ij = F_{ij}` (`i < j`), antisymmetrically.  Spacetime index `0` is
time, `i.succ` is the spatial direction `i`. -/
def curvForm (E : Fin 3 → M4) (B : Fin 3 → Fin 3 → M4) : Fin 4 → Fin 4 → M4 :=
  ![![0, E 0, E 1, E 2],
    ![-E 0, 0, B 0 1, B 0 2],
    ![-E 1, -B 0 1, 0, B 1 2],
    ![-E 2, -B 0 2, -B 1 2, 0]]

/-- The internal-index array `F^{KL}_{ρσ} = (F_{ρσ} η)^{KL}` (`F^{KL} = F^K{}_M η^{ML}`). -/
def curvArray (E : Fin 3 → M4) (B : Fin 3 → Fin 3 → M4) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun K L ρ σ => (curvForm E B ρ σ * eta) K L

/-- The scalar `r(e, F) = E^ρ_K E^σ_L F^{KL}_{ρσ}` (`E = e⁻¹`), i.e. the scalar of the
coordinate curvature. -/
def scalarR (e : M4) (E : Fin 3 → M4) (B : Fin 3 → Fin 3 → M4) : ℝ :=
  scalarOf (coordCurvature e (curvArray E B))

/-- `det(e) r(e, F)` in the paper's permutation-symbol form: the Palatini density
`¼ ε^{μνρσ} ε_{IJKL} e^I_μ e^J_ν F^{KL}_{ρσ}` (a polynomial in `e`, linear in `F`). -/
def detR (e : M4) (E : Fin 3 → M4) (B : Fin 3 → Fin 3 → M4) : ℝ :=
  palatiniDensity e (curvArray E B)

/-! ### Coefficient bivectors -/

/-- The coefficient bivector `W_{ρσ}(e)^{KL} = ½ ε^{μνρσ} ε_{IJKL} e^I_μ e^J_ν` of
`F^{KL}_{ρσ}` in the Palatini density. -/
def palCoeff (e : M4) (ρ σ : Fin 4) : M4 :=
  Matrix.of fun K L => (1 / 2 : ℝ) * ∑ μ, ∑ ν, epsR μ ν ρ σ *
    ∑ I, ∑ J, epsR I J K L * e I μ * e J ν

set_option maxRecDepth 100000 in
theorem eps4_swap23 : ∀ a b c d : Fin 4, eps4 a b d c = -eps4 a b c d := by decide

theorem epsR_swap23 (a b c d : Fin 4) : epsR a b d c = -epsR a b c d := by
  rw [epsR, epsR, eps4_swap23, Int.cast_neg]

set_option maxRecDepth 100000 in
theorem eps4_diag23 : ∀ a b c : Fin 4, eps4 a b c c = 0 := by decide

theorem palCoeff_swap (e : M4) (ρ σ : Fin 4) : palCoeff e σ ρ = -palCoeff e ρ σ := by
  ext K L
  simp only [palCoeff, Matrix.of_apply, Matrix.neg_apply]
  rw [← mul_neg]; congr 1
  rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun ν _ => ?_
  rw [epsR_swap23]; ring

theorem palCoeff_diag (e : M4) (ρ : Fin 4) : palCoeff e ρ ρ = 0 := by
  ext K L
  simp [palCoeff, epsR, eps4_diag23]

theorem palCoeff_transpose (e : M4) (ρ σ : Fin 4) : (palCoeff e ρ σ)ᵀ = -palCoeff e ρ σ := by
  ext K L
  simp only [palCoeff, Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply]
  rw [← mul_neg]; congr 1
  rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← mul_neg]; congr 1
  rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun I _ => ?_
  rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun J _ => ?_
  rw [epsR_swap23]; ring

/-- The `b`-dual of the coefficient bivector: `𝒲 = η Wᵀ`, so that
`b(𝒲, X) = Σ_{KL} W^{KL} (X η)^{KL}`. -/
def dualCoeff (W : M4) : M4 := eta * Wᵀ

theorem pairing_dualCoeff (W X : M4) :
    pairing (dualCoeff W) X = ∑ K, ∑ L, W K L * (X * eta) K L := by
  simp only [pairing, dualCoeff, eta, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun L _ => ?_
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [minkowski_symm]; ring

/-- `Π_i(e) = χ η W_{0i}(e)ᵀ`: the coefficient array of the electric curvature `E_i`. -/
def piArr (χ : ℝ) (e : M4) (i : Fin 3) : M4 := χ • dualCoeff (palCoeff e 0 i.succ)

/-- `Σ_ij(e) = χ η W_{ij}(e)ᵀ`: the coefficient array of the plaquette curvature `B_ij`
(defined for all ordered pairs; `Σ_ji = -Σ_ij`). -/
def sigmaArr (χ : ℝ) (e : M4) (i j : Fin 3) : M4 := χ • dualCoeff (palCoeff e i.succ j.succ)

theorem sigmaArr_swap (χ : ℝ) (e : M4) (i j : Fin 3) : sigmaArr χ e j i = -sigmaArr χ e i j := by
  simp [sigmaArr, dualCoeff, palCoeff_swap e i.succ j.succ, Matrix.transpose_neg]

theorem sigmaArr_diag (χ : ℝ) (e : M4) (i : Fin 3) : sigmaArr χ e i i = 0 := by
  simp [sigmaArr, dualCoeff, palCoeff_diag]

theorem isLorentz_dualCoeff_palCoeff (e : M4) (ρ σ : Fin 4) :
    IsLorentz (dualCoeff (palCoeff e ρ σ)) :=
  isLorentz_eta_mul (by rw [Matrix.transpose_transpose, palCoeff_transpose, neg_neg])

theorem IsLorentz.smul {X : M4} (hX : IsLorentz X) (c : ℝ) : IsLorentz (c • X) :=
  so13.smul_mem c hX

theorem isLorentz_piArr (χ : ℝ) (e : M4) (i : Fin 3) : IsLorentz (piArr χ e i) :=
  (isLorentz_dualCoeff_palCoeff e _ _).smul χ

theorem isLorentz_sigmaArr (χ : ℝ) (e : M4) (i j : Fin 3) : IsLorentz (sigmaArr χ e i j) :=
  (isLorentz_dualCoeff_palCoeff e _ _).smul χ

/-! ### The contraction identity `eq:supp-exact-PiSigma` -/

/-- The Palatini density as a sum over ordered spacetime pairs of coefficient contractions. -/
theorem palatiniDensity_eq_sum_palCoeff (e : M4) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    palatiniDensity e R =
      ∑ ρ, ∑ σ, (1 / 2 : ℝ) * ∑ K, ∑ L, palCoeff e ρ σ K L * R K L ρ σ := by
  unfold palatiniDensity pal4
  simp only [palCoeff, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [sum_block_swap]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
  conv_lhs => arg 2; ext μ; arg 2; ext ν; rw [sum_block_swap]
  rw [sum_block_swap]
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ =>
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
      Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
  ring

theorem curvForm_swap (E : Fin 3 → M4) (B : Fin 3 → Fin 3 → M4) (ρ σ : Fin 4) :
    curvForm E B σ ρ = -curvForm E B ρ σ := by
  fin_cases ρ <;> fin_cases σ <;> simp [curvForm]

@[simp] theorem curvForm_zero_succ (E : Fin 3 → M4) (B : Fin 3 → Fin 3 → M4) (i : Fin 3) :
    curvForm E B 0 i.succ = E i := by fin_cases i <;> simp [curvForm]

theorem curvForm_succ_succ_of_lt (E : Fin 3 → M4) (B : Fin 3 → Fin 3 → M4) {i j : Fin 3}
    (h : i < j) : curvForm E B i.succ j.succ = B i j := by
  fin_cases i <;> fin_cases j <;> simp_all [curvForm]

/-- `Σ_{i<j} g_ij` over the three spatial pairs. -/
def sumLt (g : Fin 3 → Fin 3 → ℝ) : ℝ := ∑ i, ∑ j, if i < j then g i j else 0

theorem sumLt_eq (g : Fin 3 → Fin 3 → ℝ) : sumLt g = g 0 1 + g 0 2 + g 1 2 := by
  simp [sumLt, Fin.sum_univ_three]

/-- **The contraction identity `eq:supp-exact-PiSigma`**:
`χ det(e) r(e, F) = Σ_i b(Π_i, E_i) + Σ_{i<j} b(Σ_ij, B_ij)` for all electric and plaquette
components `E_i`, `B_ij` (with `det(e) r(e, F)` in the permutation-symbol form). -/
theorem palatini_contraction (χ : ℝ) (e : M4) (E : Fin 3 → M4) (B : Fin 3 → Fin 3 → M4) :
    χ * detR e E B =
      ∑ i, pairing (piArr χ e i) (E i) +
        sumLt fun i j => pairing (sigmaArr χ e i j) (B i j) := by
  set g : Fin 4 → Fin 4 → ℝ := fun ρ σ =>
    pairing (dualCoeff (palCoeff e ρ σ)) (curvForm E B ρ σ) with hg
  have hdet : detR e E B = ∑ ρ, ∑ σ, (1 / 2 : ℝ) * g ρ σ := by
    unfold detR
    rw [palatiniDensity_eq_sum_palCoeff]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
    simp only [hg]
    rw [pairing_dualCoeff]
    rfl
  have hsym : ∀ ρ σ, g σ ρ = g ρ σ := by
    intro ρ σ
    simp only [hg, palCoeff_swap e ρ σ, curvForm_swap E B ρ σ, dualCoeff, Matrix.transpose_neg,
      Matrix.mul_neg, pairing_neg_left, pairing_neg_right, neg_neg]
  have hdiag : ∀ ρ, g ρ ρ = 0 := by
    intro ρ
    simp [hg, palCoeff_diag, dualCoeff, pairing_zero_left]
  have hpi : ∀ i : Fin 3, pairing (piArr χ e i) (E i) = χ * g 0 i.succ := by
    intro i
    simp [hg, piArr, pairing_smul_left]
  have hsig : ∀ i j : Fin 3, i < j → pairing (sigmaArr χ e i j) (B i j) = χ * g i.succ j.succ := by
    intro i j hij
    simp [hg, sigmaArr, pairing_smul_left, curvForm_succ_succ_of_lt E B hij]
  rw [hdet, sumLt_eq, Fin.sum_univ_three, hpi, hpi, hpi, hsig 0 1 (by decide),
    hsig 0 2 (by decide), hsig 1 2 (by decide)]
  simp only [Fin.sum_univ_four]
  rw [hsym 0 1, hsym 0 2, hsym 0 3, hsym 1 2, hsym 1 3, hsym 2 3, hdiag 0, hdiag 1, hdiag 2,
    hdiag 3]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  have h3 : (2 : Fin 3).succ = 3 := rfl
  rw [h3]
  ring

/-- For an invertible coframe and a curvature array antisymmetric in both index pairs, the
permutation-symbol Palatini density is `det e · r(e, F)`, `r = E^ρ_K E^σ_L F^{KL}_{ρσ}`. -/
theorem palatiniDensity_eq_det_mul_scalar (e : M4) (hdet : e.det ≠ 0)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (h1 : ∀ K L ρ σ, R L K ρ σ = -R K L ρ σ)
    (h2 : ∀ K L ρ σ, R K L σ ρ = -R K L ρ σ) :
    palatiniDensity e R = e.det * scalarOf (coordCurvature e R) := by
  have hv := palatiniVariation_mul_eq e 1 R (coordCurvature e R)
    (fun K L ρ σ => coordCurvature_spec e hdet R K L ρ σ)
    (fun α β ρ σ => coordCurvature_antisymm_left e R h1 α β ρ σ)
    (fun α β ρ σ => coordCurvature_antisymm_right e R h2 α β ρ σ)
  rw [Matrix.mul_one] at hv
  have h2P : palatiniVariation e e R = 2 * palatiniDensity e R := by
    have : palatiniVariation e e R = palatiniDensity e R + palatiniDensity e R := by
      unfold palatiniVariation palatiniDensity
      simp only [mul_add, Finset.sum_add_distrib]
    rw [this]; ring
  have hscal : ∑ γ : Fin 4, ∑ μ : Fin 4, (1 : Matrix (Fin 4) (Fin 4) ℝ) γ μ *
      ricciOf (coordCurvature e R) μ γ =
      scalarOf (coordCurvature e R) := by
    simp [Matrix.one_apply, scalarOf]
  rw [hscal, Matrix.trace_one, Fintype.card_fin, h2P] at hv
  push_cast at hv
  linarith

end RenewalGeometry.ExactPhaseAction
