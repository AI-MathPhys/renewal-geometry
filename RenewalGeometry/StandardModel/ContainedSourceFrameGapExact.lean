/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.EndpointAllocationCompilerExact

/-!
# Contained-source frame separation
  (`prop:contained-source-frame-gap`, spacetime–gauge duality manuscript)

`U : E → ℋ` (a matrix `Matrix H E ℂ`) has range `H_U` and satisfies the frame bound
`U U* ⪰ m P_{H_U}`, `m > 0`; equivalently `‖U* x‖² ≥ m ‖x‖²` for `x ∈ H_U`
(`frameGap_of_loewner` derives this from the Loewner form, using only `P_{H_U} U = U`).
`K ⊆ H_U` is given by its orthogonal projection `P = P_K` (`P* = P`, `P² = P`,
`Ran P ⊆ Ran U`).  With `C_{U|K} = U*(I − P_K)U` and `r = dim H_U − dim K`:

* `frameGap_rank`: `rank C_{U|K} = r` (and `rank C + dim K = dim H_U`);
* `frameGap_eigen_ge`: every eigenvector of `C_{U|K}` with positive eigenvalue `μ` has `μ ≥ m`;
  `frameGap_eigenvalues_ge`: every nonzero eigenvalue of the Hermitian `C_{U|K}` is `≥ m`;
* `frameGap_trace_ge`: `Tr C_{U|K} ≥ m r` (`eq:contained-source-frame-trace`);
* `frameGap_opNorm_ge`: `C_{U|K} ≠ 0 ⟹ ‖C_{U|K}‖_op ≥ m` (ℓ² operator norm);
* `frameGap_trace_lt`: `Tr C_{U|K} < m ⟹ r = 0 ∧ C_{U|K} = 0`.

`contained_source_frame_gap` packages all clauses.
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace RenewalGeometry
namespace ContainedSourceFrameGap

variable {H E : Type*} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]

/-- Squared Euclidean norm `‖x‖² = ∑ |x_i|²`. -/
noncomputable def vnormSq {n : Type*} [Fintype n] (x : n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (x i)

theorem star_dotProduct_self_eq {n : Type*} [Fintype n] (x : n → ℂ) :
    star x ⬝ᵥ x = (vnormSq x : ℂ) := by
  simp only [dotProduct, Pi.star_apply, vnormSq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]

theorem vnormSq_pos {n : Type*} [Fintype n] {x : n → ℂ} (hx : x ≠ 0) : 0 < vnormSq x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
    (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i))

omit [DecidableEq H] [DecidableEq E] in
theorem star_mulVec_dotProduct_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (x y : n → ℂ) :
    star (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = star x ⬝ᵥ ((Aᴴ * A) *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

/-- The completeness residual `C_{U|K} = U*(I − P_K)U`. -/
def frameResidual (U : Matrix H E ℂ) (P : Matrix H H ℂ) : Matrix E E ℂ :=
  Uᴴ * (1 - P) * U

omit [Fintype E] [DecidableEq E] in
theorem frameResidual_eq_gram (U : Matrix H E ℂ) {P : Matrix H H ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) :
    frameResidual U P = ((1 - P) * U)ᴴ * ((1 - P) * U) := by
  have hQh : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self,
      sub_zero]
  rw [Matrix.conjTranspose_mul, hQh, frameResidual]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 - P) (1 - P), hQQ]

omit [DecidableEq H] [DecidableEq E] in
/-- A range inclusion `Ran P ⊆ Ran U` is a factorisation `P = U J`. -/
theorem exists_eq_mul_of_range_le (U : Matrix H E ℂ) (P : Matrix H H ℂ)
    (hPU : LinearMap.range P.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    ∃ J : Matrix E H ℂ, P = U * J := by
  classical
  have hcol : ∀ g : H, ∃ x : E → ℂ, U *ᵥ x = fun n => P n g := by
    intro g
    have hmem : (fun n => P n g) ∈ LinearMap.range P.mulVecLin :=
      ⟨Pi.single g 1, by
        ext n
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]⟩
    obtain ⟨x, hx⟩ := hPU hmem
    exact ⟨x, hx⟩
  choose f hf using hcol
  refine ⟨Matrix.of fun i g => f g i, ?_⟩
  ext n g
  have := congrFun (hf g) n
  rw [Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct] using this.symm

/-- **Rank clause**: `rank C_{U|K} + dim K = dim H_U`. -/
theorem frameGap_rank_add (U : Matrix H E ℂ) {P : Matrix H H ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPU : LinearMap.range P.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    (frameResidual U P).rank + P.rank = U.rank := by
  obtain ⟨J, hJ⟩ := exists_eq_mul_of_range_le U P hPU
  have hT2 : Pᵀ * Pᵀ = Pᵀ := by rw [← Matrix.transpose_mul, hPP]
  have hstack := RenewalGeometry.stacked_rank_innovation Pᵀ Uᵀ Pᵀ hT2 hT2 rfl
  have hrows : (Matrix.fromRows Pᵀ Uᵀ).rank = U.rank := by
    rw [← Matrix.transpose_fromCols, Matrix.rank_transpose, hJ,
      EndpointAllocationCompiler.rank_fromCols_mul_self]
  have hres : (Uᵀ * (1 - Pᵀ)).rank = (frameResidual U P).rank := by
    rw [frameResidual_eq_gram U hPh hPP, Matrix.rank_conjTranspose_mul_self,
      ← Matrix.rank_transpose ((1 - P) * U), Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one]
  have hle : P.rank ≤ U.rank := by
    rw [hJ]; exact Matrix.rank_mul_le_left U J
  rw [hrows, hres, Matrix.rank_transpose] at hstack
  omega

/-- **`eq:contained-source-frame-trace`, rank**: `rank C_{U|K} = dim H_U − dim K`. -/
theorem frameGap_rank (U : Matrix H E ℂ) {P : Matrix H H ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPU : LinearMap.range P.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    (frameResidual U P).rank = U.rank - P.rank := by
  have := frameGap_rank_add U hPh hPP hPU
  omega

/-- **Eigenvalue floor**: under the frame bound `‖U* x‖² ≥ m ‖x‖²` on `H_U` and `K ⊆ H_U`,
every eigenvector of `C_{U|K}` with positive eigenvalue `μ` has `μ ≥ m`. -/
theorem frameGap_eigen_ge (U : Matrix H E ℂ) {P : Matrix H H ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPU : LinearMap.range P.mulVecLin ≤ LinearMap.range U.mulVecLin)
    {m : ℝ} (hframe : ∀ x ∈ LinearMap.range U.mulVecLin, m * vnormSq x ≤ vnormSq (Uᴴ *ᵥ x))
    {μ : ℝ} {e : E → ℂ} (he : e ≠ 0) (hμ : 0 < μ)
    (heig : frameResidual U P *ᵥ e = (μ : ℂ) • e) : m ≤ μ := by
  set W := (1 - P) * U with hW
  have hC : frameResidual U P = Wᴴ * W := frameResidual_eq_gram U hPh hPP
  set w := W *ᵥ e with hw
  -- `‖w‖² = μ ‖e‖² > 0`
  have hwnorm : (vnormSq w : ℂ) = (μ : ℂ) * vnormSq e := by
    rw [← star_dotProduct_self_eq, hw, star_mulVec_dotProduct_mulVec, ← hC, heig,
      dotProduct_smul, star_dotProduct_self_eq, smul_eq_mul]
  have hwpos : 0 < vnormSq w := by
    have h' : vnormSq w = μ * vnormSq e := by exact_mod_cast hwnorm
    rw [h']
    exact mul_pos hμ (vnormSq_pos he)
  -- `W W* w = μ w`
  have hWW : (W * Wᴴ) *ᵥ w = (μ : ℂ) • w := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← hC, heig,
      Matrix.mulVec_smul]
  -- `w ∈ H_U`
  have hwU : w ∈ LinearMap.range U.mulVecLin := by
    have : w = U *ᵥ e - P *ᵥ (U *ᵥ e) := by
      rw [hw, hW, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [this]
    refine Submodule.sub_mem _ ⟨e, rfl⟩ (hPU ⟨U *ᵥ e, rfl⟩)
  -- `W* w = U* w`
  have hQw : (1 - P) *ᵥ w = w := by
    have hQQ : (1 - P) * (1 - P) = 1 - P := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self,
        sub_zero]
    rw [hw, hW, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hQQ]
  have hWstar : Wᴴ *ᵥ w = Uᴴ *ᵥ w := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh,
      ← Matrix.mulVec_mulVec, hQw]
  have hUw : (vnormSq (Uᴴ *ᵥ w) : ℂ) = (μ : ℂ) * vnormSq w := by
    rw [← hWstar, ← star_dotProduct_self_eq, star_mulVec_dotProduct_mulVec,
      Matrix.conjTranspose_conjTranspose, hWW, dotProduct_smul, star_dotProduct_self_eq,
      smul_eq_mul]
  have hUw' : vnormSq (Uᴴ *ᵥ w) = μ * vnormSq w := by exact_mod_cast hUw
  have := hframe w hwU
  rw [hUw'] at this
  exact le_of_mul_le_mul_right this hwpos

theorem frameResidual_posSemidef (U : Matrix H E ℂ) {P : Matrix H H ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) : (frameResidual U P).PosSemidef := by
  rw [frameResidual_eq_gram U hPh hPP]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **Eigenvalue floor (spectral form)**: every nonzero eigenvalue of `C_{U|K}` is `≥ m`. -/
theorem frameGap_eigenvalues_ge (U : Matrix H E ℂ) {P : Matrix H H ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPU : LinearMap.range P.mulVecLin ≤ LinearMap.range U.mulVecLin)
    {m : ℝ} (hframe : ∀ x ∈ LinearMap.range U.mulVecLin, m * vnormSq x ≤ vnormSq (Uᴴ *ᵥ x))
    (i : E) (hi : (frameResidual_posSemidef U hPh hPP).1.eigenvalues i ≠ 0) :
    m ≤ (frameResidual_posSemidef U hPh hPP).1.eigenvalues i := by
  set hC := frameResidual_posSemidef U hPh hPP
  have hnn := hC.eigenvalues_nonneg i
  have hpos : 0 < hC.1.eigenvalues i := lt_of_le_of_ne hnn (Ne.symm hi)
  have hne : (⇑(hC.1.eigenvectorBasis i) : E → ℂ) ≠ 0 := by
    intro h0
    have h1 := (hC.1.eigenvectorBasis).orthonormal.1 i
    have : hC.1.eigenvectorBasis i = 0 := by
      ext j
      exact congrFun h0 j
    rw [this, norm_zero] at h1
    exact zero_ne_one h1
  refine frameGap_eigen_ge U hPh hPP hPU hframe hne hpos ?_
  rw [hC.1.mulVec_eigenvectorBasis i]
  ext j
  simp [Complex.real_smul]

/-- **`eq:contained-source-frame-trace`, trace**: `Tr C_{U|K} ≥ m r`. -/
theorem frameGap_trace_ge (U : Matrix H E ℂ) {P : Matrix H H ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPU : LinearMap.range P.mulVecLin ≤ LinearMap.range U.mulVecLin)
    {m : ℝ} (_hm : 0 < m)
    (hframe : ∀ x ∈ LinearMap.range U.mulVecLin, m * vnormSq x ≤ vnormSq (Uᴴ *ᵥ x)) :
    m * ((U.rank - P.rank : ℕ) : ℝ) ≤ (frameResidual U P).trace.re := by
  set hC := frameResidual_posSemidef U hPh hPP
  rw [← frameGap_rank U hPh hPP hPU, hC.1.rank_eq_card_non_zero_eigs, hC.1.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum]
  have hterm : ∀ i, (if hC.1.eigenvalues i ≠ 0 then m else 0) ≤ hC.1.eigenvalues i := by
    intro i
    split_ifs with hi
    · exact frameGap_eigenvalues_ge U hPh hPP hPU hframe i hi
    · exact hC.eigenvalues_nonneg i
  calc m * (Fintype.card {i // hC.1.eigenvalues i ≠ 0} : ℝ)
      = ∑ i, (if hC.1.eigenvalues i ≠ 0 then m else 0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          Fintype.card_subtype, mul_comm]
    _ ≤ ∑ i, hC.1.eigenvalues i := Finset.sum_le_sum fun i _ => hterm i

/-- **Operator-norm separation**: `C_{U|K} ≠ 0 ⟹ ‖C_{U|K}‖_op ≥ m`. -/
theorem frameGap_opNorm_ge (U : Matrix H E ℂ) {P : Matrix H H ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPU : LinearMap.range P.mulVecLin ≤ LinearMap.range U.mulVecLin)
    {m : ℝ} (hframe : ∀ x ∈ LinearMap.range U.mulVecLin, m * vnormSq x ≤ vnormSq (Uᴴ *ᵥ x))
    (hne : frameResidual U P ≠ 0) : m ≤ ‖frameResidual U P‖ := by
  set hC := frameResidual_posSemidef U hPh hPP
  obtain ⟨i, hi⟩ : ∃ i, hC.1.eigenvalues i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (hC.1.eigenvalues_eq_zero_iff.mp (funext h))
  have hge := frameGap_eigenvalues_ge U hPh hPP hPU hframe i hi
  have hnn := hC.eigenvalues_nonneg i
  have hb := Matrix.l2_opNorm_mulVec (frameResidual U P) (hC.1.eigenvectorBasis i)
  have h1 : ‖hC.1.eigenvectorBasis i‖ = 1 := (hC.1.eigenvectorBasis).orthonormal.1 i
  have heq : (EuclideanSpace.equiv E ℂ).symm (frameResidual U P *ᵥ hC.1.eigenvectorBasis i)
      = (hC.1.eigenvalues i : ℂ) • hC.1.eigenvectorBasis i := by
    rw [hC.1.mulVec_eigenvectorBasis i]
    ext j
    simp [Complex.real_smul]
  rw [heq, norm_smul, h1, mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnn] at hb
  exact hge.trans hb

/-- **Threshold**: `Tr C_{U|K} < m ⟹ r = 0 ∧ C_{U|K} = 0`. -/
theorem frameGap_trace_lt (U : Matrix H E ℂ) {P : Matrix H H ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPU : LinearMap.range P.mulVecLin ≤ LinearMap.range U.mulVecLin)
    {m : ℝ} (hm : 0 < m)
    (hframe : ∀ x ∈ LinearMap.range U.mulVecLin, m * vnormSq x ≤ vnormSq (Uᴴ *ᵥ x))
    (hlt : (frameResidual U P).trace.re < m) :
    U.rank - P.rank = 0 ∧ frameResidual U P = 0 := by
  have htr := frameGap_trace_ge U hPh hPP hPU hm hframe
  have hr : U.rank - P.rank = 0 := by
    by_contra h
    have h1 : (1 : ℝ) ≤ ((U.rank - P.rank : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    nlinarith
  refine ⟨hr, ?_⟩
  rw [← frameGap_rank U hPh hPP hPU] at hr
  exact EndpointAllocationCompiler.eq_zero_of_rank_eq_zero hr

/-- The frame bound in Loewner form `U U* ⪰ m P_{H_U}` (with `P_{H_U} U = U`) gives
`‖U* x‖² ≥ m ‖x‖²` on `H_U`. -/
theorem frameGap_of_loewner (U : Matrix H E ℂ) (PU : Matrix H H ℂ) (hPUfix : PU * U = U)
    {m : ℝ} (hL : (U * Uᴴ - (m : ℂ) • PU).PosSemidef) :
    ∀ x ∈ LinearMap.range U.mulVecLin, m * vnormSq x ≤ vnormSq (Uᴴ *ᵥ x) := by
  rintro x ⟨y, rfl⟩
  change m * vnormSq (U *ᵥ y) ≤ vnormSq (Uᴴ *ᵥ (U *ᵥ y))
  have hfix : PU *ᵥ (U *ᵥ y) = U *ᵥ y := by rw [Matrix.mulVec_mulVec, hPUfix]
  have h0 := hL.dotProduct_mulVec_nonneg (U *ᵥ y)
  have hUU : star (U *ᵥ y) ⬝ᵥ ((U * Uᴴ) *ᵥ (U *ᵥ y)) = (vnormSq (Uᴴ *ᵥ (U *ᵥ y)) : ℂ) := by
    rw [← star_dotProduct_self_eq, star_mulVec_dotProduct_mulVec,
      Matrix.conjTranspose_conjTranspose]
  have hsplit : star (U *ᵥ y) ⬝ᵥ ((U * Uᴴ - (m : ℂ) • PU) *ᵥ (U *ᵥ y))
      = ((vnormSq (Uᴴ *ᵥ (U *ᵥ y)) - m * vnormSq (U *ᵥ y) : ℝ) : ℂ) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, hfix, dotProduct_smul, hUU,
      star_dotProduct_self_eq, smul_eq_mul]
    push_cast
    ring
  rw [hsplit] at h0
  have := Complex.zero_le_real.mp h0
  linarith

/-- **`prop:contained-source-frame-gap`.**  For `U` with frame bound `m > 0` on `H_U` and an
orthogonal projection `P = P_K` with `K ⊆ H_U`, `C_{U|K} = U*(I − P_K)U` satisfies
`rank C = r = dim H_U − dim K`, `Tr C ≥ m r`, every nonzero (hence positive) eigenvalue of `C`
is `≥ m`, `C ≠ 0 ⟹ ‖C‖_op ≥ m`, and `Tr C < m ⟹ r = 0 ∧ C = 0`. -/
theorem contained_source_frame_gap (U : Matrix H E ℂ) {P : Matrix H H ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPU : LinearMap.range P.mulVecLin ≤ LinearMap.range U.mulVecLin)
    {m : ℝ} (hm : 0 < m)
    (hframe : ∀ x ∈ LinearMap.range U.mulVecLin, m * vnormSq x ≤ vnormSq (Uᴴ *ᵥ x)) :
    (frameResidual U P).rank = U.rank - P.rank ∧
    m * ((U.rank - P.rank : ℕ) : ℝ) ≤ (frameResidual U P).trace.re ∧
    (∀ i, (frameResidual_posSemidef U hPh hPP).1.eigenvalues i ≠ 0 →
      m ≤ (frameResidual_posSemidef U hPh hPP).1.eigenvalues i) ∧
    (frameResidual U P ≠ 0 → m ≤ ‖frameResidual U P‖) ∧
    ((frameResidual U P).trace.re < m → U.rank - P.rank = 0 ∧ frameResidual U P = 0) :=
  ⟨frameGap_rank U hPh hPP hPU, frameGap_trace_ge U hPh hPP hPU hm hframe,
    frameGap_eigenvalues_ge U hPh hPP hPU hframe, frameGap_opNorm_ge U hPh hPP hPU hframe,
    frameGap_trace_lt U hPh hPP hPU hm hframe⟩

end ContainedSourceFrameGap
end RenewalGeometry
