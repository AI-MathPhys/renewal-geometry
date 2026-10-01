/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.ColourNaturalitySpectrumExact

/-!
# Determinant selector, population, and branchwise purity

Covers `thm:determinant-skeleton-population` of the spacetime–gauge duality manuscript.

The selector pair `(H_nat, P_det)` is `NaturalitySpectrum.natDefect` (the defect operator built
from the factor actions alone, `natDefectOp_eq_tensorSum`) and its kernel projector
`NaturalitySpectrum.natDetProj`; neither depends on any source `J`.

**Abstract part.**  For a positive operator `H`, a rank-one orthogonal projector `P`
(`P* = P`, `P² = P`, `P J P = Tr(P J) P`, `Tr P = 1`) and the two-sided bound
`2 (I − P) ⪯ H ⪯ 10 (I − P)`, and for positive branches `J_b ⪰ 0` with
`m_b = Tr J_b`, `d_b = Tr(H J_b)`, `m_{D,b} = Tr(P J_b)` (real parts):

* `defect_nonneg`: `d_b ≥ 0`;
* `leakage_le`: `Tr[(I − P) J_b] ≤ d_b / 2`;
* `det_mass_lower`, `det_mass_upper`: `max{0, m_b − d_b/2} ≤ m_{D,b} ≤ m_b − d_b/10`;
* `branch_purity`: `d_b = 0 ⇒ J_b = m_b P`;
* `total_purity`: `∑ d_b = 0 ⇒` every `J_b = m_b P` and `∑ J_b = m P`;
* `occurrence_of_defect_lt`: `d < 2 m ⇒ m_D > 0`;
* `unitary_invariance`: simultaneous unitary conjugation of `H`, `P`, `J` preserves
  `m`, `d`, `m_D` and the two-sided gap.

**Instance.**  `determinant_skeleton_population` instantiates everything with
`H_nat` and `P_det`, using `natDefect_gap_lower/upper` (`eq:naturality-two-sided-gap`).
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace RenewalGeometry
namespace DeterminantSkeleton

open NaturalitySpectrum

section Abstract

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem psd_factor {J : Matrix n n ℂ} (hJ : J.PosSemidef) : ∃ B : Matrix n n ℂ, J = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hJ.nonneg
  exact ⟨B, by rw [hB, star_eq_conjTranspose]⟩

theorem trace_mul_psd_nonneg {A J : Matrix n n ℂ} (hA : A.PosSemidef) (hJ : J.PosSemidef) :
    0 ≤ (A * J).trace := by
  obtain ⟨B, rfl⟩ := psd_factor hJ
  rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
  exact (hA.mul_mul_conjTranspose_same B).trace_nonneg

theorem re_trace_mul_psd_nonneg {A J : Matrix n n ℂ} (hA : A.PosSemidef) (hJ : J.PosSemidef) :
    0 ≤ (A * J).trace.re := by
  have := Complex.le_def.mp (trace_mul_psd_nonneg hA hJ)
  simpa using this.1

/-- Branch mass `m_b = Tr J_b` (`eq:determinant-branch-masses`). -/
noncomputable def branchMass (J : Matrix n n ℂ) : ℝ := J.trace.re

/-- Branch defect `d_b = Tr(H J_b)`. -/
noncomputable def branchDefect (H J : Matrix n n ℂ) : ℝ := (H * J).trace.re

/-- Determinant mass `m_{D,b} = Tr(P J_b)`. -/
noncomputable def branchDet (P J : Matrix n n ℂ) : ℝ := (P * J).trace.re

/-- Additivity of the three branch functionals. -/
theorem branchMass_sum {ι : Type*} (s : Finset ι) (J : ι → Matrix n n ℂ) :
    branchMass (∑ b ∈ s, J b) = ∑ b ∈ s, branchMass (J b) := by
  simp [branchMass, trace_sum]

theorem branchDefect_sum {ι : Type*} (H : Matrix n n ℂ) (s : Finset ι) (J : ι → Matrix n n ℂ) :
    branchDefect H (∑ b ∈ s, J b) = ∑ b ∈ s, branchDefect H (J b) := by
  simp [branchDefect, Matrix.mul_sum, trace_sum]

theorem branchDet_sum {ι : Type*} (P : Matrix n n ℂ) (s : Finset ι) (J : ι → Matrix n n ℂ) :
    branchDet P (∑ b ∈ s, J b) = ∑ b ∈ s, branchDet P (J b) := by
  simp [branchDet, Matrix.mul_sum, trace_sum]

theorem posSemidef_sum' {ι : Type*} (s : Finset ι) {J : ι → Matrix n n ℂ}
    (hJ : ∀ b ∈ s, (J b).PosSemidef) : (∑ b ∈ s, J b).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PosSemidef.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hJ a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hJ b (Finset.mem_insert_of_mem hb))

variable {H P : Matrix n n ℂ}

/-- `d_b ≥ 0`. -/
theorem defect_nonneg (hH : H.PosSemidef) {J : Matrix n n ℂ} (hJ : J.PosSemidef) :
    0 ≤ branchDefect H J := re_trace_mul_psd_nonneg hH hJ

theorem leakage_eq (J : Matrix n n ℂ) :
    ((1 - P) * J).trace.re = branchMass J - branchDet P J := by
  simp [branchMass, branchDet, Matrix.sub_mul, trace_sub]

/-- **Leakage bound** `Tr[(I − P) J] ≤ d / 2` (`eq:determinant-branch-bounds`). -/
theorem leakage_le (hlow : (H - (2 : ℂ) • (1 - P)).PosSemidef) {J : Matrix n n ℂ}
    (hJ : J.PosSemidef) : ((1 - P) * J).trace.re ≤ branchDefect H J / 2 := by
  have h := re_trace_mul_psd_nonneg hlow hJ
  simp only [Matrix.sub_mul, Matrix.smul_mul, trace_sub, trace_smul, Complex.sub_re,
    smul_eq_mul, Complex.mul_re] at h
  have h2 := leakage_eq (P := P) J
  simp only [branchDefect, branchMass, branchDet] at h2 ⊢
  norm_num at h
  linarith

theorem proj_posSemidef (hPh : Pᴴ = P) (hPP : P * P = P) : P.PosSemidef := by
  have := posSemidef_conjTranspose_mul_self P
  rwa [hPh, hPP] at this

/-- **Lower determinant mass** `max{0, m − d/2} ≤ m_D`. -/
theorem det_mass_lower (hlow : (H - (2 : ℂ) • (1 - P)).PosSemidef) (hPh : Pᴴ = P)
    (hPP : P * P = P) {J : Matrix n n ℂ} (hJ : J.PosSemidef) :
    max 0 (branchMass J - branchDefect H J / 2) ≤ branchDet P J := by
  have h1 := leakage_le hlow hJ
  rw [leakage_eq] at h1
  have h2 : 0 ≤ branchDet P J := re_trace_mul_psd_nonneg (proj_posSemidef hPh hPP) hJ
  exact max_le h2 (by linarith)

/-- **Upper determinant mass** `m_D ≤ m − d/10`. -/
theorem det_mass_upper (hup : ((10 : ℂ) • (1 - P) - H).PosSemidef) {J : Matrix n n ℂ}
    (hJ : J.PosSemidef) : branchDet P J ≤ branchMass J - branchDefect H J / 10 := by
  have h := re_trace_mul_psd_nonneg hup hJ
  simp only [Matrix.sub_mul, Matrix.smul_mul, trace_sub, trace_smul, Complex.sub_re,
    smul_eq_mul, Complex.mul_re] at h
  have h2 := leakage_eq (P := P) J
  simp only [branchDefect, branchMass, branchDet] at h2 ⊢
  norm_num at h
  linarith

/-- **Branchwise purity** (`eq:determinant-branch-purity`): zero defect forces
`J = m P`. -/
theorem branch_purity (hlow : (H - (2 : ℂ) • (1 - P)).PosSemidef) (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPJP : ∀ J : Matrix n n ℂ, P * J * P = (P * J).trace • P)
    (htrP : P.trace = 1) {J : Matrix n n ℂ} (hJ : J.PosSemidef) (hd : branchDefect H J = 0) :
    J = ((branchMass J : ℝ) : ℂ) • P := by
  set Q : Matrix n n ℂ := 1 - P with hQ
  have hQh : Qᴴ = Q := by rw [hQ, conjTranspose_sub, conjTranspose_one, hPh]
  have hQQ : Q * Q = Q := by
    rw [hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]; simp
  -- `Tr(Q J Q) = Tr(Q J)` has real part `≤ 0`
  have hle := leakage_le hlow hJ
  rw [hd, zero_div] at hle
  have hQJQ : (Q * J * Q).PosSemidef := by
    have := hJ.mul_mul_conjTranspose_same Q
    rwa [hQh] at this
  have htr : (Q * J * Q).trace = (Q * J).trace := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hQQ]
  have hnn := Complex.le_def.mp hQJQ.trace_nonneg
  have hzero : (Q * J * Q).trace = 0 := by
    apply Complex.ext
    · simp only [Complex.zero_re] at hnn ⊢
      rw [htr] at hnn ⊢
      linarith [hnn.1]
    · simp only [Complex.zero_im] at hnn ⊢
      linarith [hnn.2]
  have hQJQ0 : Q * J * Q = 0 := hQJQ.trace_eq_zero_iff.mp hzero
  obtain ⟨B, hB⟩ := psd_factor hJ
  have hBQ : B * Q = 0 := by
    have : (B * Q)ᴴ * (B * Q) = 0 := by
      rw [conjTranspose_mul, hQh, Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ, ← hB,
        ← Matrix.mul_assoc]
      exact hQJQ0
    exact Matrix.conjTranspose_mul_self_eq_zero.mp this
  have hJQ : J * Q = 0 := by rw [hB, Matrix.mul_assoc, hBQ, Matrix.mul_zero]
  have hQJ : Q * J = 0 := by
    have : (J * Q)ᴴ = 0 := by rw [hJQ, conjTranspose_zero]
    rwa [conjTranspose_mul, hQh, hJ.isHermitian.eq] at this
  have hJP : J = P * J * P := by
    have e1 : J = J * P := by
      have : J * Q = J - J * P := by rw [hQ, Matrix.mul_sub, Matrix.mul_one]
      rw [hJQ] at this
      exact (sub_eq_zero.mp this.symm)
    have e2 : J = P * J := by
      have : Q * J = J - P * J := by rw [hQ, Matrix.sub_mul, Matrix.one_mul]
      rw [hQJ] at this
      exact (sub_eq_zero.mp this.symm)
    calc J = J * P := e1
      _ = P * J * P := by rw [← e2]
  have hform : J = (P * J).trace • P := hJP.trans (hPJP J)
  have htrJ : J.trace = (P * J).trace := by
    conv_lhs => rw [hform]
    rw [trace_smul, htrP, smul_eq_mul, mul_one]
  have him : J.trace.im = 0 := by
    have := Complex.le_def.mp hJ.trace_nonneg
    simp only [Complex.zero_im] at this
    linarith [this.2]
  have hreal : ((branchMass J : ℝ) : ℂ) = J.trace := by
    apply Complex.ext <;> simp [branchMass, him]
  rw [hreal, htrJ]
  exact hform

/-- **Total purity**: zero total defect forces every branch to be pure, and the total. -/
theorem total_purity {ι : Type*} (s : Finset ι) {J : ι → Matrix n n ℂ}
    (hH : H.PosSemidef) (hlow : (H - (2 : ℂ) • (1 - P)).PosSemidef) (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPJP : ∀ J : Matrix n n ℂ, P * J * P = (P * J).trace • P)
    (htrP : P.trace = 1) (hJ : ∀ b ∈ s, (J b).PosSemidef)
    (hd : branchDefect H (∑ b ∈ s, J b) = 0) :
    (∀ b ∈ s, J b = ((branchMass (J b) : ℝ) : ℂ) • P) ∧
      ∑ b ∈ s, J b = ((branchMass (∑ b ∈ s, J b) : ℝ) : ℂ) • P := by
  rw [branchDefect_sum] at hd
  have hdb : ∀ b ∈ s, branchDefect H (J b) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun b hb => defect_nonneg hH (hJ b hb)).mp hd
  have hpure : ∀ b ∈ s, J b = ((branchMass (J b) : ℝ) : ℂ) • P :=
    fun b hb => branch_purity hlow hPh hPP hPJP htrP (hJ b hb) (hdb b hb)
  refine ⟨hpure, ?_⟩
  rw [branchMass_sum, Finset.sum_congr rfl hpure, ← Finset.sum_smul]
  push_cast
  rfl

/-- **Occurrence**: `d < 2 m` forces `m_D > 0`. -/
theorem occurrence_of_defect_lt (hlow : (H - (2 : ℂ) • (1 - P)).PosSemidef) (hPh : Pᴴ = P)
    (hPP : P * P = P) {J : Matrix n n ℂ} (hJ : J.PosSemidef)
    (hlt : branchDefect H J < 2 * branchMass J) : 0 < branchDet P J := by
  have h := det_mass_lower hlow hPh hPP hJ
  have := le_max_right 0 (branchMass J - branchDefect H J / 2)
  linarith

/-- **Unitary invariance**: simultaneous conjugation by a unitary preserves the masses,
the defect, and the two-sided gap. -/
theorem unitary_invariance {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (J : Matrix n n ℂ) :
    branchMass (U * J * Uᴴ) = branchMass J ∧
      branchDefect (U * H * Uᴴ) (U * J * Uᴴ) = branchDefect H J ∧
      branchDet (U * P * Uᴴ) (U * J * Uᴴ) = branchDet P J ∧
      ((H - (2 : ℂ) • (1 - P)).PosSemidef →
        (U * H * Uᴴ - (2 : ℂ) • (1 - U * P * Uᴴ)).PosSemidef) ∧
      (((10 : ℂ) • (1 - P) - H).PosSemidef →
        ((10 : ℂ) • (1 - U * P * Uᴴ) - U * H * Uᴴ).PosSemidef) := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have conj_mul : ∀ A B : Matrix n n ℂ, U * A * Uᴴ * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
    intro A B
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  have tr_conj : ∀ A : Matrix n n ℂ, (U * A * Uᴴ).trace = A.trace := by
    intro A
    rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have conj_lin : ∀ (A B : Matrix n n ℂ) (c : ℂ),
      U * (c • (1 - A) - B) * Uᴴ = c • (1 - U * A * Uᴴ) - U * B * Uᴴ := by
    intro A B c
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hU']
  have conj_lin' : ∀ (A B : Matrix n n ℂ) (c : ℂ),
      U * (B - c • (1 - A)) * Uᴴ = U * B * Uᴴ - c • (1 - U * A * Uᴴ) := by
    intro A B c
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hU']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [branchMass, tr_conj]
  · simp only [branchDefect, conj_mul, tr_conj]
  · simp only [branchDet, conj_mul, tr_conj]
  · intro h
    have := h.mul_mul_conjTranspose_same U
    rw [conj_lin'] at this
    exact this
  · intro h
    have := h.mul_mul_conjTranspose_same U
    rw [conj_lin] at this
    exact this

end Abstract

/-! ## The determinant selector on the naturality port -/

section Instance

/-- Rank-one structure: `|k⟩⟨k| J |k⟩⟨k| = ⟨k|J|k⟩ |k⟩⟨k|`. -/
theorem vecMulVec_mul_mul_vecMulVec {n : Type*} [Fintype n] (k : n → ℂ) (J : Matrix n n ℂ) :
    vecMulVec k (star k) * J * vecMulVec k (star k) =
      (star k ⬝ᵥ (J *ᵥ k)) • vecMulVec k (star k) := by
  ext i j
  simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem trace_vecMulVec_mul {n : Type*} [Fintype n] (k : n → ℂ) (J : Matrix n n ℂ) :
    (vecMulVec k (star k) * J).trace = star k ⬝ᵥ (J *ᵥ k) := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.star_apply]
  ring

theorem natKernelVec_normSq : star natKernelVec ⬝ᵥ natKernelVec = 6 := by
  simp [natKernelVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
    weakAlternating, one_apply]
  norm_num

theorem natDetProj_conjTranspose : natDetProjᴴ = natDetProj := by
  rw [natDetProj_eq, conjTranspose_smul, conjTranspose_vecMulVec]
  simp

theorem natDetProj_mul_mul (J : Matrix NatPort NatPort ℂ) :
    natDetProj * J * natDetProj = (natDetProj * J).trace • natDetProj := by
  rw [natDetProj_eq, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_mul_vecMulVec, trace_smul, trace_vecMulVec_mul, smul_smul, smul_smul,
    smul_smul]
  congr 1
  ring

theorem natDetProj_trace : natDetProj.trace = 1 := by
  have h := trace_vecMulVec_mul natKernelVec 1
  rw [Matrix.mul_one, one_mulVec, natKernelVec_normSq] at h
  rw [natDetProj_eq, trace_smul, h]
  norm_num

theorem natDetProj_mul_self : natDetProj * natDetProj = natDetProj := by
  have h := natDetProj_mul_mul 1
  rw [Matrix.mul_one, natDetProj_trace, one_smul] at h
  exact h

theorem natDefect_posSemidef : natDefect.PosSemidef := by
  rw [natEigenbasis.H_eq_specMat]
  exact natEigenbasis.specMat_posSemidef fun i => by
    rw [natEigenbasis_ev]; linarith [colourEv_nonneg i.1, weakEv_nonneg i.2]

/-- **Determinant selector, population, and branchwise purity
(`thm:determinant-skeleton-population`).**  For any finite family of positive branches
`J_b ⪰ 0` on the naturality port, with `H = H_nat`, `P = P_det`:
the two-sided gap `2 (I − P) ⪯ H ⪯ 10 (I − P)` holds (`eq:naturality-two-sided-gap`);
branchwise `d_b ≥ 0`, `Tr[(I − P) J_b] ≤ d_b/2` and
`max{0, m_b − d_b/2} ≤ m_{D,b} ≤ m_b − d_b/10`, and likewise for the totals
(`eq:determinant-branch-bounds`); the totals are the sums of the branch quantities;
`d = 0` forces `J_b = m_b P` for every branch and `J = m P`
(`eq:determinant-branch-purity`); `d < 2m` forces `m_D > 0`. -/
theorem determinant_skeleton_population {ι : Type*} (s : Finset ι)
    (J : ι → Matrix NatPort NatPort ℂ) (hJ : ∀ b ∈ s, (J b).PosSemidef) :
    (natDefect - (2 : ℂ) • (1 - natDetProj)).PosSemidef ∧
    ((10 : ℂ) • (1 - natDetProj) - natDefect).PosSemidef ∧
    (∀ b ∈ s, 0 ≤ branchDefect natDefect (J b) ∧
      ((1 - natDetProj) * J b).trace.re ≤ branchDefect natDefect (J b) / 2 ∧
      max 0 (branchMass (J b) - branchDefect natDefect (J b) / 2) ≤ branchDet natDetProj (J b) ∧
      branchDet natDetProj (J b) ≤ branchMass (J b) - branchDefect natDefect (J b) / 10) ∧
    (branchMass (∑ b ∈ s, J b) = ∑ b ∈ s, branchMass (J b) ∧
      branchDefect natDefect (∑ b ∈ s, J b) = ∑ b ∈ s, branchDefect natDefect (J b) ∧
      branchDet natDetProj (∑ b ∈ s, J b) = ∑ b ∈ s, branchDet natDetProj (J b)) ∧
    (0 ≤ branchDefect natDefect (∑ b ∈ s, J b) ∧
      ((1 - natDetProj) * ∑ b ∈ s, J b).trace.re ≤ branchDefect natDefect (∑ b ∈ s, J b) / 2 ∧
      max 0 (branchMass (∑ b ∈ s, J b) - branchDefect natDefect (∑ b ∈ s, J b) / 2) ≤
        branchDet natDetProj (∑ b ∈ s, J b) ∧
      branchDet natDetProj (∑ b ∈ s, J b) ≤
        branchMass (∑ b ∈ s, J b) - branchDefect natDefect (∑ b ∈ s, J b) / 10) ∧
    (branchDefect natDefect (∑ b ∈ s, J b) = 0 →
      (∀ b ∈ s, J b = ((branchMass (J b) : ℝ) : ℂ) • natDetProj) ∧
        ∑ b ∈ s, J b = ((branchMass (∑ b ∈ s, J b) : ℝ) : ℂ) • natDetProj) ∧
    (branchDefect natDefect (∑ b ∈ s, J b) < 2 * branchMass (∑ b ∈ s, J b) →
      0 < branchDet natDetProj (∑ b ∈ s, J b)) := by
  have hlow := natDefect_gap_lower
  have hup := natDefect_gap_upper
  have hPh := natDetProj_conjTranspose
  have hPP := natDetProj_mul_self
  have hJs := posSemidef_sum' s hJ
  refine ⟨hlow, hup, fun b hb => ⟨defect_nonneg natDefect_posSemidef (hJ b hb),
    leakage_le hlow (hJ b hb), det_mass_lower hlow hPh hPP (hJ b hb),
    det_mass_upper hup (hJ b hb)⟩, ⟨branchMass_sum s J, branchDefect_sum _ s J,
    branchDet_sum _ s J⟩, ⟨defect_nonneg natDefect_posSemidef hJs, leakage_le hlow hJs,
    det_mass_lower hlow hPh hPP hJs, det_mass_upper hup hJs⟩, fun hd => ?_,
    fun hlt => occurrence_of_defect_lt hlow hPh hPP hJs hlt⟩
  exact total_purity s natDefect_posSemidef hlow hPh hPP natDetProj_mul_mul natDetProj_trace hJ hd

end Instance

end DeterminantSkeleton
end RenewalGeometry
