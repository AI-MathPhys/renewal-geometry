/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Quarter-root, transverse Read, and complex clock factor
  (`thm:clock-quarter-root-master`,
   `cor:fair-clock-transition-master`, flagship manuscript)

On the binary clock carrier `W ≅ ℂ²` with `X = ν⁻¹H`,
`Z = 2P₀ - I`, `t* = π/(4ν)` and the quarter root
`q = e^{-it*H} = (I - iX)/√2`:

* `X, Y, Z` are pairwise anticommuting Hermitian involutions,
  `𝒬(Z) = qZq* = -Y`, `𝒬(X) = X`, `𝒬²(Z) = -Z`, and the dihedral
  relation `ZqZ = q*` (equivalently `Ad(Z)𝒬Ad(Z) = 𝒬⁻¹`)
  (`clock_quarter_root`);
* the boxed generation claim: the complex unital algebra generated
  by `P₀` and the orbit element `X` is all of `M₂(ℂ)`
  (`clock_algebra_top`; the C*-closure adds nothing in finite
  dimension, disclosed);
* the half-period lift `-iX` is anti-Hermitian with square `-I`
  (`half_period_lift`);
* `cor:fair-clock-transition-master`: every `Y`-eigenstate is
  unbiased for the anchor `Z`-Read, `P^Y_s P^Z_t P^Y_s = ½P^Y_s`
  (all four signs, `fair_clock_transition`), with transition
  probability `Tr(P^Y_s P^Z_t) = ½` (`fair_transition_prob`); the
  canonical depth-1 Store–Read versus Read–Store cross-Hankel
  window along the quarter-root transfer,
  `(𝗛_ord)_{ij} = ⟨z₊, q^{i+j} y₊⟩`, has
  `det 𝗛_ord = ½` (`order_window_det`), and the fair overlap Gram
  `[[1,q],[q,1]]`, `q = ½`, has eigenvalues `3/2, 1/2` with
  condition ratio `η = 1/3` (`fair_gram_eta`).  The tex leaves
  `𝗛_ord` and `η` undefined; both renderings are explicit
  reconstructions from the cross-Hankel construction of
  `thm:clock-geometry-cross-Hankel-master` and are disclosed in
  the ledger.
-/

open Matrix

namespace NCG

noncomputable section

/-- `1/√2` as a complex scalar. -/
def invSqrt2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma invSqrt2_sq : invSqrt2 ^ 2 = 2⁻¹ := by
  rw [invSqrt2, ← Complex.ofReal_pow]
  norm_num [Real.sq_sqrt]

lemma invSqrt2_star : star invSqrt2 = invSqrt2 := by
  rw [invSqrt2]
  exact Complex.conj_ofReal _

/-- Pauli `X`: the normalized clock generator `ν⁻¹H`. -/
def clockX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `Z = 2P₀ - I`: the anchor symmetry. -/
def clockZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Pauli `Y = -𝒬(Z)`: the physical transverse Read. -/
def clockY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I; Complex.I, 0]

/-- The anchor projection `P₀ = |Ω⟩⟨Ω|`. -/
def clockP0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- The quarter root `q = e^{-iπX/4} = (I - iX)/√2`. -/
def quarterRoot : Matrix (Fin 2) (Fin 2) ℂ :=
  invSqrt2 • !![1, -Complex.I; -Complex.I, 1]

/-- The conjugate transpose of the quarter root. -/
lemma quarterRoot_conjTranspose :
    quarterRootᴴ = invSqrt2 • !![1, Complex.I; Complex.I, 1] := by
  rw [quarterRoot, Matrix.conjTranspose_smul, invSqrt2_star]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply]

/-- Conjugation by the quarter root through the certified
`2 × 2` core computation. -/
lemma quarter_conj (M N : Matrix (Fin 2) (Fin 2) ℂ)
    (h : !![1, -Complex.I; -Complex.I, 1] * M
        * !![1, Complex.I; Complex.I, 1] = (2 : ℂ) • N) :
    quarterRoot * M * quarterRootᴴ = N := by
  rw [quarterRoot_conjTranspose, quarterRoot, smul_mul_assoc,
    smul_mul_assoc, mul_smul_comm, h, smul_smul, smul_smul,
    show invSqrt2 * invSqrt2 * 2 = invSqrt2 ^ 2 * 2 by ring,
    invSqrt2_sq]
  norm_num

/-- `𝒬(Z) = -Y`. -/
lemma quarter_conj_Z :
    quarterRoot * clockZ * quarterRootᴴ = -clockY := by
  refine quarter_conj _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockZ, clockY, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- `𝒬(X) = X`: the clock direction is fixed. -/
lemma quarter_conj_X :
    quarterRoot * clockX * quarterRootᴴ = clockX := by
  refine quarter_conj _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockX, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- `𝒬(Y) = Z`. -/
lemma quarter_conj_Y :
    quarterRoot * clockY * quarterRootᴴ = clockZ := by
  refine quarter_conj _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockY, clockZ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- `𝒬²(Z) = -Z`: the quarter root squares to the half turn. -/
lemma quarter_sq_Z :
    quarterRoot * (quarterRoot * clockZ * quarterRootᴴ)
      * quarterRootᴴ = -clockZ := by
  rw [quarter_conj_Z, Matrix.mul_neg, Matrix.neg_mul,
    quarter_conj_Y]

/-- Dihedral relation: `ZqZ = q*`, i.e.
`Ad(Z)𝒬Ad(Z) = 𝒬⁻¹`. -/
lemma quarter_dihedral :
    clockZ * quarterRoot * clockZ = quarterRootᴴ := by
  rw [quarterRoot_conjTranspose, quarterRoot, mul_smul_comm,
    smul_mul_assoc]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The three Reads are Hermitian involutions and pairwise
anticommute. -/
lemma pauli_relations :
    (clockXᴴ = clockX ∧ clockYᴴ = clockY ∧ clockZᴴ = clockZ)
    ∧ (clockX * clockX = 1 ∧ clockY * clockY = 1
        ∧ clockZ * clockZ = 1)
    ∧ (clockX * clockY + clockY * clockX = 0
        ∧ clockY * clockZ + clockZ * clockY = 0
        ∧ clockZ * clockX + clockX * clockZ = 0) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [clockX, clockY, clockZ, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Fin.sum_univ_two,
          Complex.I_mul_I]

/-- The half-period lift `-iX` is anti-Hermitian with square
`-I`. -/
lemma half_period_lift :
    ((-Complex.I) • clockX)ᴴ = -((-Complex.I) • clockX)
    ∧ ((-Complex.I) • clockX) * ((-Complex.I) • clockX) = -1 := by
  constructor <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [clockX, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Fin.sum_univ_two, Complex.I_mul_I]

/-- Boxed generation claim: `P₀` and the orbit direction `X`
generate all of `M₂(ℂ)` as a complex unital algebra. -/
theorem clock_algebra_top :
    Algebra.adjoin ℂ
      ({clockP0, clockX} : Set (Matrix (Fin 2) (Fin 2) ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  have hP : clockP0 ∈ Algebra.adjoin ℂ
      ({clockP0, clockX} : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    Algebra.subset_adjoin (by simp)
  have hX : clockX ∈ Algebra.adjoin ℂ
      ({clockP0, clockX} : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    Algebra.subset_adjoin (by simp)
  have h00 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
      = clockP0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [clockP0]
  have h01 : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
      = clockP0 * clockX := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockP0, clockX, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)
      = clockX * clockP0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockP0, clockX, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)
      = clockX * clockP0 * clockX := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockP0, clockX, Matrix.mul_apply, Fin.sum_univ_two]
  have hunit : ∀ i j : Fin 2, Matrix.single i j (1 : ℂ)
      ∈ Algebra.adjoin ℂ
        ({clockP0, clockX} : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
    have m00 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
        ∈ Algebra.adjoin ℂ
          ({clockP0, clockX} : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
      rw [h00]; exact hP
    have m01 : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
        ∈ Algebra.adjoin ℂ
          ({clockP0, clockX} : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
      rw [h01]; exact mul_mem hP hX
    have m10 : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)
        ∈ Algebra.adjoin ℂ
          ({clockP0, clockX} : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
      rw [h10]; exact mul_mem hX hP
    have m11 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)
        ∈ Algebra.adjoin ℂ
          ({clockP0, clockX} : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
      rw [h11]; exact mul_mem (mul_mem hX hP) hX
    intro i j
    fin_cases i <;> fin_cases j <;>
      first
        | exact m00
        | exact m01
        | exact m10
        | exact m11
  have hM : M = ∑ i : Fin 2, ∑ j : Fin 2,
      M i j • Matrix.single i j (1 : ℂ) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two]
  rw [hM]
  exact sum_mem fun i _ => sum_mem fun j _ =>
    Subalgebra.smul_mem _ (hunit i j) _

/-- `thm:clock-quarter-root-master`, master bundle. -/
theorem clock_quarter_root :
    quarterRoot * clockZ * quarterRootᴴ = -clockY
    ∧ quarterRoot * clockX * quarterRootᴴ = clockX
    ∧ quarterRoot * (quarterRoot * clockZ * quarterRootᴴ)
        * quarterRootᴴ = -clockZ
    ∧ clockZ * quarterRoot * clockZ = quarterRootᴴ
    ∧ Algebra.adjoin ℂ
        ({clockP0, clockX} : Set (Matrix (Fin 2) (Fin 2) ℂ)) = ⊤ :=
  ⟨quarter_conj_Z, quarter_conj_X, quarter_sq_Z, quarter_dihedral,
    clock_algebra_top⟩

/-! ### `cor:fair-clock-transition-master` -/

/-- The sharp Read effect `P^A_s = (I + sA)/2`. -/
def readProj (s : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (2⁻¹ : ℂ) • (1 + s • A)

/-- Every `Y`-eigenstate is unbiased for the anchor `Z`-Read:
`P^Y_s P^Z_t P^Y_s = ½ P^Y_s` for all four signs. -/
theorem fair_clock_transition (s t : ℂ)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    readProj s clockY * readProj t clockZ * readProj s clockY
      = (2⁻¹ : ℂ) • readProj s clockY := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [readProj, clockY, clockZ, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    ring_nf <;> norm_num [Complex.I_sq]

/-- The fair transition probability: `Tr(P^Y_s P^Z_t) = ½`. -/
theorem fair_transition_prob (s t : ℂ)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    (readProj s clockY * readProj t clockZ).trace = 2⁻¹ := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp [readProj, clockY, clockZ, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf

/-- The Store (anchor) source vector `z₊`. -/
def storeVec : Fin 2 → ℂ := ![1, 0]

/-- The Read source vector: the `+1` eigenvector of `Y` in the
phase convention `y₊ = (i, -1)/√2`. -/
def readVec : Fin 2 → ℂ := fun j => invSqrt2 * ![Complex.I, -1] j

/-- `readVec` is a unit `+1`-eigenvector of `Y`. -/
lemma readVec_eigen : clockY *ᵥ readVec = readVec := by
  funext j
  fin_cases j <;>
    simp [clockY, readVec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc]

/-- The canonical depth-1 Store–Read versus Read–Store
cross-Hankel window along the quarter-root transfer:
`(𝗛_ord)_{ij} = ⟨z₊, q^{i+j} y₊⟩`. -/
def orderWindow : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    star storeVec ⬝ᵥ ((quarterRoot ^ ((i : ℕ) + (j : ℕ))) *ᵥ readVec)

/-- One quarter-root transfer maps the Read source onto the
anchor. -/
lemma quarter_shift_read : quarterRoot *ᵥ readVec
    = ![Complex.I, 0] := by
  have hcore : !![1, -Complex.I; -Complex.I, 1]
      *ᵥ ![Complex.I, -1] = (2 : ℂ) • ![Complex.I, 0] := by
    funext j
    fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, two_mul]
  have hread : readVec = invSqrt2 • ![Complex.I, -1] := rfl
  rw [hread, quarterRoot, Matrix.smul_mulVec,
    Matrix.mulVec_smul, hcore, smul_smul, smul_smul,
    show invSqrt2 * invSqrt2 * 2 = invSqrt2 ^ 2 * 2 by ring,
    invSqrt2_sq]
  norm_num

/-- The second quarter-root transfer. -/
lemma quarter_shift_read2 : quarterRoot *ᵥ ![Complex.I, 0]
    = ![invSqrt2 * Complex.I, invSqrt2] := by
  have hcore : !![1, -Complex.I; -Complex.I, 1]
      *ᵥ ![Complex.I, 0] = ![Complex.I, 1] := by
    funext j
    fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [quarterRoot, Matrix.smul_mulVec, hcore]
  funext j
  fin_cases j <;> simp

/-- `cor:fair-clock-transition-master`, boxed constant:
`det 𝗛_ord = ½`. -/
theorem order_window_det : orderWindow.det = 2⁻¹ := by
  have h00 : orderWindow 0 0 = invSqrt2 * Complex.I := by
    simp [orderWindow, storeVec, readVec, dotProduct,
      Fin.sum_univ_two]
  have h01 : orderWindow 0 1 = Complex.I := by
    simp only [orderWindow]
    rw [show ((0 : Fin 2) : ℕ) + ((1 : Fin 2) : ℕ) = 1 by norm_num,
      pow_one, quarter_shift_read]
    simp [storeVec, dotProduct, Fin.sum_univ_two]
  have h10 : orderWindow 1 0 = Complex.I := by
    simp only [orderWindow]
    rw [show ((1 : Fin 2) : ℕ) + ((0 : Fin 2) : ℕ) = 1 by norm_num,
      pow_one, quarter_shift_read]
    simp [storeVec, dotProduct, Fin.sum_univ_two]
  have h11 : orderWindow 1 1 = invSqrt2 * Complex.I := by
    simp only [orderWindow]
    rw [show ((1 : Fin 2) : ℕ) + ((1 : Fin 2) : ℕ) = 2 by norm_num,
      pow_two, ← Matrix.mulVec_mulVec, quarter_shift_read,
      quarter_shift_read2]
    simp [storeVec, dotProduct, Fin.sum_univ_two]
  rw [Matrix.det_fin_two, h00, h01, h10, h11,
    show invSqrt2 * Complex.I * (invSqrt2 * Complex.I)
      = invSqrt2 ^ 2 * (Complex.I * Complex.I) by ring,
    invSqrt2_sq, Complex.I_mul_I]
  ring

/-- The fair overlap Gram of the two Read axes,
`[[1, q], [q, 1]]` with transition probability `q = ½`. -/
def fairGram : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2⁻¹; 2⁻¹, 1]

/-- `cor:fair-clock-transition-master`, boxed constant `η = ⅓`:
the fair Gram has certified eigenvalues `3/2` (symmetric vector)
and `1/2` (antisymmetric vector), with condition ratio
`η = λ_min/λ_max = 1/3`. -/
theorem fair_gram_eta :
    fairGram *ᵥ ![1, 1] = (3 * 2⁻¹ : ℝ) • ![1, 1]
    ∧ fairGram *ᵥ ![1, -1] = (2⁻¹ : ℝ) • ![1, -1]
    ∧ (2⁻¹ : ℝ) / (3 * 2⁻¹) = 3⁻¹ := by
  refine ⟨?_, ?_, by norm_num⟩ <;>
    · funext j
      fin_cases j <;>
        simp [fairGram, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two] <;> norm_num

end

end NCG
