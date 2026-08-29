/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExteriorSecondQuantizationRankExact

/-!
# Operator-norm bounds for finite exterior powers

This module supplies the analytic norm layer for the concrete compound-matrix
realization of exterior powers.  All matrix norms below are the Euclidean
operator norm.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NCG
namespace ExteriorPowerOperatorNormBounds

set_option maxHeartbeats 800000

open FiniteCompoundMatrixExteriorPower
open ExteriorSecondQuantizationUnitaryCovariance

variable {d : ℕ}

/-- The Euclidean operator norm of the identity matrix is at most one,
including on the zero-dimensional carrier. -/
theorem matrix_norm_one_le (n : Type*) [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  have hid : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
      (1 : Matrix n n ℂ) = 1 := map_one _
  rw [← Matrix.l2_opNorm_toEuclideanCLM, hid]
  change ‖ContinuousLinearMap.id ℂ (EuclideanSpace ℂ n)‖ ≤ 1
  exact ContinuousLinearMap.norm_id_le

/-- Every exterior grade of a unitary one-particle operator is a contraction.
The formulation remains valid in the zero-dimensional grades, where the
operator norm of the identity may be zero. -/
theorem compound_unitary_norm_le_one
    {U : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) (r : ℕ) :
    ‖cmpd r U‖ ≤ 1 := by
  have h := congrArg norm (compound_unitary hU r)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at h
  have hone : ‖(1 : Matrix (GradeIdx r d) (GradeIdx r d) ℂ)‖ ≤ 1 :=
    matrix_norm_one_le _
  nlinarith [norm_nonneg (cmpd r U)]

/-- A diagonal exterior power has norm at most the corresponding power of a
uniform bound on its diagonal entries. -/
theorem cmpd_diagonal_norm_le (v : Fin d → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hv : ∀ i, ‖v i‖ ≤ M) (r : ℕ) :
    ‖cmpd r (Matrix.diagonal v)‖ ≤ M ^ r := by
  rw [cmpd_diagonal, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (pow_nonneg hM r)).2 fun S => ?_
  rw [norm_prod]
  calc
    ∏ i ∈ S.1, ‖v i‖ ≤ ∏ _i ∈ S.1, M := by
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hv i)
    _ = M ^ S.1.card := by simp
    _ = M ^ r := by rw [S.2]

/-- Every eigenvalue of a Hermitian matrix is bounded in modulus by its
Euclidean operator norm. -/
theorem hermitian_eigenvalue_norm_le
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) (i : Fin d) :
    ‖((hP.eigenvalues i : ℝ) : ℂ)‖ ≤ ‖P‖ := by
  have hmem : ((hP.eigenvalues i : ℝ) : ℂ) ∈ spectrum ℂ P := by
    rw [hP.spectrum_eq_image_range]
    exact ⟨hP.eigenvalues i, ⟨i, rfl⟩, rfl⟩
  have hbound := spectrum.norm_le_norm_mul_of_mem hmem
  exact hbound.trans <| by
    simpa using mul_le_mul_of_nonneg_left
      (matrix_norm_one_le (Fin d)) (norm_nonneg P)

/-- Hermitian exterior powers obey the sharp functorial bound. -/
theorem cmpd_hermitian_norm_le
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) (r : ℕ) :
    ‖cmpd r P‖ ≤ ‖P‖ ^ r := by
  let U : Matrix (Fin d) (Fin d) ℂ := hP.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues)
  have hUmem : U ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    hP.eigenvectorUnitary.property
  have hU : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hUmem
    rwa [Matrix.star_eq_conjTranspose] at h
  have hdec : P = U * D * Uᴴ := by
    have h := hP.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [U, D, Matrix.star_eq_conjTranspose] using h
  have hD : ‖cmpd r D‖ ≤ ‖P‖ ^ r := by
    apply cmpd_diagonal_norm_le (RCLike.ofReal ∘ hP.eigenvalues)
      ‖P‖ (norm_nonneg P)
    intro i
    simpa [Function.comp_apply] using hermitian_eigenvalue_norm_le P hP i
  have hUH : ‖cmpd r Uᴴ‖ ≤ 1 := by
    rw [cmpd_conjTranspose, Matrix.l2_opNorm_conjTranspose]
    exact compound_unitary_norm_le_one hU r
  conv_lhs => rw [hdec, cmpd_mul, cmpd_mul]
  calc
    ‖cmpd r U * cmpd r D * cmpd r Uᴴ‖
        ≤ ‖cmpd r U * cmpd r D‖ * ‖cmpd r Uᴴ‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖cmpd r U‖ * ‖cmpd r D‖) * ‖cmpd r Uᴴ‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * (‖P‖ ^ r)) * 1 := by
      gcongr
      · exact compound_unitary_norm_le_one hU r
    _ = ‖P‖ ^ r := by ring

/-- **Exterior-power operator-norm bound.**  For every finite complex matrix,
`‖⋀^r A‖ ≤ ‖A‖^r`. -/
theorem cmpd_norm_le_pow (A : Matrix (Fin d) (Fin d) ℂ) (r : ℕ) :
    ‖cmpd r A‖ ≤ ‖A‖ ^ r := by
  let P := Aᴴ * A
  have hP : P.IsHermitian := by
    exact Matrix.isHermitian_conjTranspose_mul_self A
  have hcompound : (cmpd r A)ᴴ * cmpd r A = cmpd r P := by
    rw [← cmpd_conjTranspose, ← cmpd_mul]
  have hsq : ‖cmpd r A‖ * ‖cmpd r A‖ = ‖cmpd r P‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hcompound]
  have hp := cmpd_hermitian_norm_le P hP r
  have hPnorm : ‖P‖ = ‖A‖ * ‖A‖ := by
    exact Matrix.l2_opNorm_conjTranspose_mul_self A
  have hpow : (‖A‖ * ‖A‖) ^ r = ‖A‖ ^ r * ‖A‖ ^ r := by
    rw [mul_pow]
  have hsquare : ‖cmpd r A‖ * ‖cmpd r A‖ ≤
      ‖A‖ ^ r * ‖A‖ ^ r := by
    rw [hsq]
    exact hp.trans_eq (by rw [hPnorm, hpow])
  nlinarith [norm_nonneg (cmpd r A), pow_nonneg (norm_nonneg A) r]

/-! ## Heterogeneous tensor-slot norm -/

theorem slotProd_conjTranspose {r : ℕ}
    (C : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    (slotProd C)ᴴ = slotProd fun k => (C k)ᴴ := by
  ext f g
  simp [slotProd_apply, map_prod]

theorem slotProd_one {r : ℕ} :
    slotProd (fun _ : Fin r => (1 : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  classical
  ext f g
  by_cases hfg : f = g
  · subst g
    simp [slotProd_apply]
  · have hex : ∃ k, f k ≠ g k := by
      by_contra h
      push_neg at h
      exact hfg (funext h)
    obtain ⟨k, hk⟩ := hex
    rw [Matrix.one_apply_ne hfg]
    rw [slotProd_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact Matrix.one_apply_ne hk

theorem slotProd_unitary {r : ℕ}
    (U : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ k, (U k)ᴴ * U k = 1) :
    (slotProd U)ᴴ * slotProd U = 1 := by
  rw [slotProd_conjTranspose, slotProd_mul]
  calc
    slotProd (fun k => (U k)ᴴ * U k) =
        slotProd (fun _ : Fin r => (1 : Matrix (Fin d) (Fin d) ℂ)) := by
      congr 1
      funext k
      exact hU k
    _ = 1 := slotProd_one

theorem slotProd_unitary_norm_le_one {r : ℕ}
    (U : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ k, (U k)ᴴ * U k = 1) :
    ‖slotProd U‖ ≤ 1 := by
  have h := congrArg norm (slotProd_unitary U hU)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at h
  have hone : ‖(1 : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)‖ ≤ 1 :=
    matrix_norm_one_le _
  nlinarith [norm_nonneg (slotProd U)]

theorem slotProd_diagonal {r : ℕ} (v : Fin r → Fin d → ℂ) :
    slotProd (fun k => Matrix.diagonal (v k)) =
      Matrix.diagonal (fun f => ∏ k, v k (f k)) := by
  classical
  ext f g
  by_cases hfg : f = g
  · subst g
    simp [slotProd_apply]
  · have hex : ∃ k, f k ≠ g k := by
      by_contra h
      push_neg at h
      exact hfg (funext h)
    obtain ⟨k, hk⟩ := hex
    rw [Matrix.diagonal_apply_ne _ hfg, slotProd_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact Matrix.diagonal_apply_ne _ hk

/-- Slotwise Hermitian matrices have tensor-product norm bounded by the
product of their individual norms. -/
theorem slotProd_hermitian_norm_le {r : ℕ}
    (P : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ k, (P k).IsHermitian) :
    ‖slotProd P‖ ≤ ∏ k, ‖P k‖ := by
  let U : Fin r → Matrix (Fin d) (Fin d) ℂ :=
    fun k => (hP k).eigenvectorUnitary
  let D : Fin r → Matrix (Fin d) (Fin d) ℂ :=
    fun k => Matrix.diagonal (RCLike.ofReal ∘ (hP k).eigenvalues)
  have hU : ∀ k, (U k)ᴴ * U k = 1 := by
    intro k
    have h := Matrix.mem_unitaryGroup_iff'.mp (hP k).eigenvectorUnitary.property
    rwa [Matrix.star_eq_conjTranspose] at h
  have hdec : ∀ k, P k = U k * D k * (U k)ᴴ := by
    intro k
    have h := (hP k).spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [U, D, Matrix.star_eq_conjTranspose] using h
  have hD : ‖slotProd D‖ ≤ ∏ k, ‖P k‖ := by
    rw [slotProd_diagonal, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg
      (Finset.prod_nonneg fun k _ => norm_nonneg (P k))).2 fun f => ?_
    rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun k _ => by
        simpa [D, Function.comp_apply] using
          hermitian_eigenvalue_norm_le (P k) (hP k) (f k))
  have hUH : ‖slotProd (fun k => (U k)ᴴ)‖ ≤ 1 := by
    rw [← slotProd_conjTranspose, Matrix.l2_opNorm_conjTranspose]
    exact slotProd_unitary_norm_le_one U hU
  have hfactor : slotProd P =
      slotProd U * slotProd D * slotProd (fun k => (U k)ᴴ) := by
    rw [slotProd_mul, slotProd_mul]
    congr 1
    funext k
    exact hdec k
  rw [hfactor]
  calc
    ‖slotProd U * slotProd D * slotProd (fun k => (U k)ᴴ)‖
        ≤ ‖slotProd U * slotProd D‖ * ‖slotProd (fun k => (U k)ᴴ)‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖slotProd U‖ * ‖slotProd D‖) *
        ‖slotProd (fun k => (U k)ᴴ)‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * (∏ k, ‖P k‖)) * 1 := by
      gcongr
      exact slotProd_unitary_norm_le_one U hU
    _ = ∏ k, ‖P k‖ := by ring

/-- The Euclidean operator norm of a heterogeneous finite tensor product is
at most the product of the slot norms. -/
theorem slotProd_norm_le_prod {r : ℕ}
    (C : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    ‖slotProd C‖ ≤ ∏ k, ‖C k‖ := by
  let P : Fin r → Matrix (Fin d) (Fin d) ℂ := fun k => (C k)ᴴ * C k
  have hP : ∀ k, (P k).IsHermitian := fun k =>
    Matrix.isHermitian_conjTranspose_mul_self (C k)
  have hcompound : (slotProd C)ᴴ * slotProd C = slotProd P := by
    rw [slotProd_conjTranspose, slotProd_mul]
  have hsq : ‖slotProd C‖ * ‖slotProd C‖ = ‖slotProd P‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hcompound]
  have hp := slotProd_hermitian_norm_le P hP
  have hprodP : (∏ k, ‖P k‖) =
      (∏ k, ‖C k‖) * (∏ k, ‖C k‖) := by
    simp_rw [P, Matrix.l2_opNorm_conjTranspose_mul_self]
    rw [← Finset.prod_mul_distrib]
  have hsquare : ‖slotProd C‖ * ‖slotProd C‖ ≤
      (∏ k, ‖C k‖) * (∏ k, ‖C k‖) := by
    rw [hsq]
    exact hp.trans_eq hprodP
  have hprod : 0 ≤ ∏ k, ‖C k‖ :=
    Finset.prod_nonneg fun k _ => norm_nonneg (C k)
  nlinarith [norm_nonneg (slotProd C)]

/-! ## Sharp telescoping perturbation bound -/

/-- Change the first `j` tensor slots from `B` to `A`. -/
def tensorPathSlots {r : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (j : ℕ) :
    Fin r → Matrix (Fin d) (Fin d) ℂ :=
  fun k => if k.1 < j then A else B

/-- The single mixed tensor occurring when slot `j` is changed. -/
def tensorDifferenceSlots {r : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (j : Fin r) : Fin r → Matrix (Fin d) (Fin d) ℂ :=
  fun k => if k = j then A - B else tensorPathSlots A B j.1 k

theorem tensorPathSlots_zero {r : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    slotProd (tensorPathSlots (r := r) A B 0) = tpow r B := by
  congr 1

theorem tensorPathSlots_full {r : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    slotProd (tensorPathSlots (r := r) A B r) = tpow r A := by
  congr 1
  funext k
  simp [tensorPathSlots, tpow, k.2]

/-- Consecutive tensor paths differ in exactly one slot. -/
theorem tensorPathSlots_succ_sub (A B : Matrix (Fin d) (Fin d) ℂ)
    {r : ℕ} (j : Fin r) :
    slotProd (tensorPathSlots A B (j.1 + 1)) -
        slotProd (tensorPathSlots A B j.1) =
      slotProd (tensorDifferenceSlots A B j) := by
  classical
  ext f g
  simp only [Matrix.sub_apply, slotProd_apply]
  let next : Fin r → ℂ := fun k => tensorPathSlots A B (j.1 + 1) k (f k) (g k)
  let prev : Fin r → ℂ := fun k => tensorPathSlots A B j.1 k (f k) (g k)
  let diff : Fin r → ℂ := fun k => tensorDifferenceSlots A B j k (f k) (g k)
  have hnextj : next j = A (f j) (g j) := by
    simp [next, tensorPathSlots]
  have hprevj : prev j = B (f j) (g j) := by
    simp [prev, tensorPathSlots]
  have hdiffj : diff j = (A - B) (f j) (g j) := by
    simp [diff, tensorDifferenceSlots]
  have hother : ∀ k ∈ (Finset.univ.erase j), next k = prev k ∧ diff k = prev k := by
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    constructor
    · by_cases hlt : k < j
      · have hle : k ≤ j := hlt.le
        simp [next, prev, tensorPathSlots, hlt, hle]
      · have hnle : ¬k ≤ j := fun hle => hlt (lt_of_le_of_ne hle hkj)
        simp [next, prev, tensorPathSlots, hlt, hnle]
    · simp [diff, prev, tensorDifferenceSlots, hkj]
  have hprodNext : ∏ k ∈ Finset.univ.erase j, next k =
      ∏ k ∈ Finset.univ.erase j, prev k :=
    Finset.prod_congr rfl fun k hk => (hother k hk).1
  have hprodDiff : ∏ k ∈ Finset.univ.erase j, diff k =
      ∏ k ∈ Finset.univ.erase j, prev k :=
    Finset.prod_congr rfl fun k hk => (hother k hk).2
  rw [← Finset.mul_prod_erase Finset.univ next (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ prev (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ diff (Finset.mem_univ j),
    hnextj, hprevj, hdiffj, hprodNext, hprodDiff]
  simp [Matrix.sub_apply]
  ring

/-- Exact tensor-power telescoping identity. -/
theorem tpow_sub_tpow_eq_sum (A B : Matrix (Fin d) (Fin d) ℂ) (r : ℕ) :
    tpow r A - tpow r B =
      ∑ j : Fin r, slotProd (tensorDifferenceSlots A B j) := by
  rw [← tensorPathSlots_full A B, ← tensorPathSlots_zero A B]
  calc
    slotProd (tensorPathSlots A B r) - slotProd (tensorPathSlots A B 0) =
        ∑ j ∈ Finset.range r,
          (slotProd (tensorPathSlots A B (j + 1)) -
            slotProd (tensorPathSlots A B j)) :=
      (Finset.sum_range_sub
        (fun j => slotProd (tensorPathSlots (r := r) A B j)) r).symm
    _ = ∑ j : Fin r,
        (slotProd (tensorPathSlots A B (j.1 + 1)) -
          slotProd (tensorPathSlots A B j.1)) := by
      rw [← Fin.sum_univ_eq_sum_range]
    _ = ∑ j : Fin r, slotProd (tensorDifferenceSlots A B j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact tensorPathSlots_succ_sub A B j

/-- Tensor powers obey the sharp product telescoping estimate. -/
theorem tpow_sub_tpow_norm_le (A B : Matrix (Fin d) (Fin d) ℂ)
    (r : ℕ) (hr : 1 ≤ r) :
    ‖tpow r A - tpow r B‖ ≤
      r * max ‖A‖ ‖B‖ ^ (r - 1) * ‖A - B‖ := by
  let M := max ‖A‖ ‖B‖
  have hM : 0 ≤ M := le_trans (norm_nonneg A) (le_max_left _ _)
  rw [tpow_sub_tpow_eq_sum]
  calc
    ‖∑ j : Fin r, slotProd (tensorDifferenceSlots A B j)‖
        ≤ ∑ j : Fin r, ‖slotProd (tensorDifferenceSlots A B j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin r, M ^ (r - 1) * ‖A - B‖ := by
      apply Finset.sum_le_sum
      intro j _
      calc
        ‖slotProd (tensorDifferenceSlots A B j)‖
            ≤ ∏ k, ‖tensorDifferenceSlots A B j k‖ :=
          slotProd_norm_le_prod _
        _ ≤ M ^ (r - 1) * ‖A - B‖ := by
          rw [← Finset.mul_prod_erase Finset.univ
            (fun k => ‖tensorDifferenceSlots A B j k‖) (Finset.mem_univ j)]
          have hcard : (Finset.univ.erase j).card = r - 1 := by simp
          have hrest : ∏ k ∈ Finset.univ.erase j,
              ‖tensorPathSlots A B j.1 k‖ ≤ M ^ (r - 1) := by
            calc
              _ ≤ ∏ _k ∈ Finset.univ.erase j, M := by
                exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k hk => by
                  unfold tensorPathSlots
                  split_ifs <;> simp [M]
              _ = M ^ (r - 1) := by simp [hcard]
          have hsame : ∏ k ∈ Finset.univ.erase j,
              ‖tensorDifferenceSlots A B j k‖ =
              ∏ k ∈ Finset.univ.erase j, ‖tensorPathSlots A B j.1 k‖ := by
            apply Finset.prod_congr rfl
            intro k hk
            have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
            simp [tensorDifferenceSlots, hkj]
          rw [hsame]
          simp only [tensorDifferenceSlots, if_pos]
          calc
            ‖A - B‖ * ∏ k ∈ Finset.univ.erase j,
                ‖tensorPathSlots A B j.1 k‖
                ≤ ‖A - B‖ * M ^ (r - 1) :=
              mul_le_mul_of_nonneg_left hrest (norm_nonneg _)
            _ = M ^ (r - 1) * ‖A - B‖ := mul_comm _ _
    _ = r * M ^ (r - 1) * ‖A - B‖ := by simp [mul_assoc]

/-- The antisymmetric compression does not increase the tensor-power
perturbation norm. -/
theorem cmpd_sub_norm_le_tpow_sub_norm
    (A B : Matrix (Fin d) (Fin d) ℂ) (r : ℕ) :
    ‖cmpd r A - cmpd r B‖ ≤ ‖tpow r A - tpow r B‖ := by
  let J := asym r d
  let C := cmpd r A - cmpd r B
  let T := tpow r A - tpow r B
  have hinter : J * C = T * J := by
    simp only [J, C, T, Matrix.mul_sub, Matrix.sub_mul]
    rw [← tpow_mul_asym A, ← tpow_mul_asym B]
  have hscaled : ((r.factorial : ℂ) • C) = Jᴴ * T * J := by
    calc
      (r.factorial : ℂ) • C =
          (((r.factorial : ℂ) •
            (1 : Matrix (GradeIdx r d) (GradeIdx r d) ℂ)) * C) := by
        rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (Jᴴ * J) * C := by
        change _ = ((asym r d)ᴴ * asym r d) * C
        rw [conjTranspose_asym_mul_asym]
      _ = Jᴴ * (J * C) := by rw [Matrix.mul_assoc]
      _ = Jᴴ * (T * J) := by rw [hinter]
      _ = Jᴴ * T * J := by rw [Matrix.mul_assoc]
  have hJ2 : ‖J‖ * ‖J‖ ≤ (r.factorial : ℝ) := by
    have h := congrArg norm (conjTranspose_asym_mul_asym (r := r) (d := d))
    change ‖Jᴴ * J‖ =
      ‖((r.factorial : ℂ) •
        (1 : Matrix (GradeIdx r d) (GradeIdx r d) ℂ))‖ at h
    rw [Matrix.l2_opNorm_conjTranspose_mul_self, norm_smul] at h
    have hone : ‖(1 : Matrix (GradeIdx r d) (GradeIdx r d) ℂ)‖ ≤ 1 :=
      matrix_norm_one_le _
    have hcast : ‖(r.factorial : ℂ)‖ = (r.factorial : ℝ) := by simp
    rw [hcast] at h
    have hfacnonneg : 0 ≤ (r.factorial : ℝ) := by positivity
    nlinarith
  have hright : ‖Jᴴ * T * J‖ ≤
      (r.factorial : ℝ) * ‖T‖ := by
    calc
      ‖Jᴴ * T * J‖ ≤ ‖Jᴴ * T‖ * ‖J‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Jᴴ‖ * ‖T‖) * ‖J‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
      _ = (‖J‖ * ‖J‖) * ‖T‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]
        ring
      _ ≤ (r.factorial : ℝ) * ‖T‖ :=
        mul_le_mul_of_nonneg_right hJ2 (norm_nonneg T)
  have hnorm := congrArg norm hscaled
  have hleft : ‖((r.factorial : ℂ) • C)‖ =
      (r.factorial : ℝ) * ‖C‖ := by simp [norm_smul]
  rw [hleft] at hnorm
  have hfac : 0 < (r.factorial : ℝ) := by positivity
  have : (r.factorial : ℝ) * ‖C‖ ≤
      (r.factorial : ℝ) * ‖T‖ := hnorm.trans_le hright
  exact le_of_mul_le_mul_left this hfac

/-- **`lem:SMQG-exterior-bound`.**  Sharp finite exterior-power perturbation
bound in the concrete orthonormal wedge basis. -/
theorem exterior_power_perturbation_bound
    (A B : Matrix (Fin d) (Fin d) ℂ) (r : ℕ) (hr : 1 ≤ r) :
    ‖cmpd r A - cmpd r B‖ ≤
      r * max ‖A‖ ‖B‖ ^ (r - 1) * ‖A - B‖ :=
  (cmpd_sub_norm_le_tpow_sub_norm A B r).trans
    (tpow_sub_tpow_norm_le A B r hr)

end ExteriorPowerOperatorNormBounds
end NCG
