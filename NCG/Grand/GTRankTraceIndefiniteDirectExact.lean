/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTRankTraceIndefinite
import NCG.Grand.SMSTReflectionPositivityExact
import NCG.Grand.SMYMColourRestrictionExact
import NCG.Upstream.PrimitiveWeight

/-!
# Direct rank--trace certificate for indefinite compressions

This closes the spectral-layer gap in `thm:GT-rank-trace-indefinite`.
The proof starts from the literal positivity, rank, and positive-inertia
hypotheses.  It constructs the Jordan parts of `Q` by Hermitian functional
calculus and diagonalizes `P` where needed; no adapted basis is assumed.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace GTRankTraceIndefiniteDirectExact

set_option maxHeartbeats 2400000

abbrev frobeniusSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

theorem frobeniusSq_eq_hsNormSq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    frobeniusSq A = SMSTReflectionPositivity.hsNormSq A := by
  rw [SMSTReflectionPositivity.hsNormSq_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact Complex.normSq_eq_norm_sq _

/-- Spectral formula for the Frobenius square of a Hermitian matrix. -/
theorem frobeniusSq_hermitian_eigenvalues {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    frobeniusSq A = ∑ i, (hA.eigenvalues i) ^ 2 := by
  rw [show frobeniusSq A = ((Aᴴ * A).trace).re from
    (gt_frobenius_trace A).symm]
  have hAA : Aᴴ * A = hA.cfc (fun x => x * x) := by
    rw [hA.eq]
    calc
      A * A = hA.cfc id * hA.cfc id := by
        rw [Upstream.PrimitiveWeight.cfc_id' hA]
      _ = hA.cfc (fun x => id x * id x) :=
        Upstream.PrimitiveWeight.cfc_mul hA id id
      _ = hA.cfc (fun x => x * x) := by rfl
  rw [hAA, Upstream.PrimitiveWeight.cfc_trace]
  simp [pow_two]

/-- A PSD matrix of rank at most `k` satisfies the completed-square
rank--trace lower bound. -/
theorem psd_rank_trace_bound {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (k : ℕ) (hrank : A.rank ≤ k) (a : ℝ) :
    a * A.trace.re - a ^ 2 / 4 * k ≤ frobeniusSq A := by
  let S : Finset (Fin n) := Finset.univ.filter fun i => hA.1.eigenvalues i ≠ 0
  have hpoint : ∀ i : Fin n,
      a * hA.1.eigenvalues i -
          (if hA.1.eigenvalues i ≠ 0 then a ^ 2 / 4 else 0)
        ≤ (hA.1.eigenvalues i) ^ 2 := by
    intro i
    by_cases hi : hA.1.eigenvalues i = 0
    · simp [hi]
    · simp only [if_pos hi]
      nlinarith [sq_nonneg (hA.1.eigenvalues i - a / 2)]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpoint i
  have htrace : A.trace.re = ∑ i, hA.1.eigenvalues i := by
    rw [hA.1.trace_eq_sum_eigenvalues]
    simp
  have hpenalty :
      ∑ i, (if hA.1.eigenvalues i ≠ 0 then a ^ 2 / 4 else 0) =
        a ^ 2 / 4 * S.card := by
    rw [Finset.sum_ite]
    simp [S, nsmul_eq_mul, mul_comm]
  have hcard : S.card = A.rank := by
    calc
      S.card = #{i | hA.1.eigenvalues i ≠ 0} := by rfl
      _ = Fintype.card {i // hA.1.eigenvalues i ≠ 0} :=
        (Fintype.card_subtype _).symm
      _ = A.rank := hA.1.rank_eq_card_non_zero_eigs.symm
  have hcast : (A.rank : ℝ) ≤ k := by exact_mod_cast hrank
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← htrace, hpenalty,
    hcard] at hsum
  rw [frobeniusSq_hermitian_eigenvalues hA.1]
  have hcoef : 0 ≤ a ^ 2 / 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcast hcoef]

/-- Diagonalizing `P` constructs the missing range-adapted coordinates for
the mixed positive-minus-positive term. -/
theorem psd_sub_psd_rank_trace_bound {n : ℕ}
    {P R : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosSemidef) (hR : R.PosSemidef)
    (r : ℕ) (hrank : P.rank ≤ r) (c : ℝ) (hc : 0 < c) :
    c * P.trace.re - c ^ 2 / 4 * r - 2 * c * R.trace.re
      ≤ frobeniusSq (P - R) := by
  let U := hP.1.eigenvectorUnitary
  let V : Matrix (Fin n) (Fin n) ℂ := U
  let T : Matrix (Fin n) (Fin n) ℂ :=
    Vᴴ * R * V
  have hT : T.PosSemidef := by
    dsimp only [T]
    exact hR.conjTranspose_mul_mul_same V
  have hdiagP :
      Vᴴ * P * V =
        Matrix.diagonal (RCLike.ofReal ∘ hP.1.eigenvalues) := by
    have h := hP.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa only [V, U, star_eq_conjTranspose] using h
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Vᴴ * (P - R) * V
  have hD : D = Matrix.diagonal
      (RCLike.ofReal ∘ hP.1.eigenvalues) - T := by
    dsimp only [D, T]
    rw [Matrix.mul_sub, Matrix.sub_mul, hdiagP]
  have hVstarV : Vᴴ * V = 1 := by
    change (star U : Matrix (Fin n) (Fin n) ℂ) * U = 1
    exact Unitary.coe_star_mul_self U
  have hVVstar : V * Vᴴ = 1 := by
    change (U : Matrix (Fin n) (Fin n) ℂ) * star U = 1
    exact Unitary.coe_mul_star_self U
  have hfrob : frobeniusSq D = frobeniusSq (P - R) := by
    have hgram : Dᴴ * D = Vᴴ * (((P - R)ᴴ * (P - R)) * V) := by
      dsimp only [D]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc V Vᴴ ((P - R) * V), hVVstar,
        Matrix.one_mul]
    have htrace : (Dᴴ * D).trace = ((P - R)ᴴ * (P - R)).trace := by
      rw [hgram, Matrix.trace_mul_comm, Matrix.mul_assoc, hVVstar,
        Matrix.mul_one]
    rw [show frobeniusSq D = ((Dᴴ * D).trace).re from
      (gt_frobenius_trace D).symm]
    rw [show frobeniusSq (P - R) =
      (((P - R)ᴴ * (P - R)).trace).re from
      (gt_frobenius_trace (P - R)).symm]
    rw [htrace]
  have hdiagLower :
      ∑ i, (D i i).re ^ 2 ≤ frobeniusSq D := by
    apply Finset.sum_le_sum
    intro i _
    calc
      (D i i).re ^ 2 ≤ Complex.normSq (D i i) := by
        rw [Complex.normSq_apply]
        nlinarith [sq_nonneg (D i i).im]
      _ ≤ ∑ j, Complex.normSq (D i j) :=
        Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _)
          (Finset.mem_univ i)
  have hTdiag : ∀ i, 0 ≤ (T i i).re := by
    intro i
    exact (Complex.le_def.mp hT.diag_nonneg).1
  have hpoint : ∀ i : Fin n,
      c * hP.1.eigenvalues i - 2 * c * (T i i).re -
          (if hP.1.eigenvalues i ≠ 0 then c ^ 2 / 4 else 0)
        ≤ (D i i).re ^ 2 := by
    intro i
    have hde : (D i i).re = hP.1.eigenvalues i - (T i i).re := by
      rw [hD]
      simp [Function.comp_apply]
    by_cases hi : hP.1.eigenvalues i = 0
    · simp [hi]
      rw [hde, hi, zero_sub]
      nlinarith [hTdiag i, sq_nonneg (T i i).re]
    · simp only [if_pos hi]
      rw [hde]
      nlinarith [hTdiag i,
        sq_nonneg (hP.1.eigenvalues i - (T i i).re - c / 2)]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpoint i
  let S : Finset (Fin n) := Finset.univ.filter fun i => hP.1.eigenvalues i ≠ 0
  have htraceP : P.trace.re = ∑ i, hP.1.eigenvalues i := by
    rw [hP.1.trace_eq_sum_eigenvalues]
    simp
  have htraceT : T.trace = R.trace := by
    calc
      T.trace = ((V * Vᴴ) * R).trace := by
        dsimp only [T]
        exact Matrix.trace_mul_cycle _ _ _
      _ = R.trace := by rw [hVVstar, Matrix.one_mul]
  have hsumT : ∑ i, (T i i).re = R.trace.re := by
    rw [← Complex.re_sum]
    change T.trace.re = R.trace.re
    rw [htraceT]
  have hpenalty :
      ∑ i, (if hP.1.eigenvalues i ≠ 0 then c ^ 2 / 4 else 0) =
        c ^ 2 / 4 * S.card := by
    rw [Finset.sum_ite]
    simp [S, nsmul_eq_mul, mul_comm]
  have hcard : S.card = P.rank := by
    calc
      S.card = #{i | hP.1.eigenvalues i ≠ 0} := by rfl
      _ = Fintype.card {i // hP.1.eigenvalues i ≠ 0} :=
        (Fintype.card_subtype _).symm
      _ = P.rank := hP.1.rank_eq_card_non_zero_eigs.symm
  have hcast : (P.rank : ℝ) ≤ r := by exact_mod_cast hrank
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← htraceP, hsumT, hpenalty,
    hcard] at hsum
  have hcoef : 0 ≤ c ^ 2 / 4 := by positivity
  nlinarith [hsum, hdiagLower, hfrob,
    mul_le_mul_of_nonneg_left hcast hcoef]

/-- Literal version of SC.7 and SC.8, starting only from `P ⪰ 0`, the rank
bound on `P`, Hermiticity of `Q`, and the bound on the number of positive
eigenvalues of `Q` (encoded as the rank of its positive Jordan part). -/
theorem gt_rank_trace_indefinite_direct {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (r b : ℕ) (hr : P.rank ≤ r)
    (hb : (Upstream.PrimitiveWeight.posPart hQ).rank ≤ b) :
    (∀ c : ℝ, 0 < c →
      c * P.trace.re - c ^ 2 / 4 * r + 2 * c * Q.trace.re - c ^ 2 * b
        ≤ frobeniusSq (P + Q))
      ∧ ((r : ℝ) ≥ 2 * P.trace.re + 4 * Q.trace.re - 4 * b -
        frobeniusSq (P + Q)) := by
  let Qp := Upstream.PrimitiveWeight.posPart hQ
  let Qm := Upstream.PrimitiveWeight.negPart hQ
  have hQp : Qp.PosSemidef := Upstream.PrimitiveWeight.posPart_posSemidef hQ
  have hQm : Qm.PosSemidef := Upstream.PrimitiveWeight.negPart_posSemidef hQ
  have hsplit : Qp - Qm = Q := Upstream.PrimitiveWeight.posPart_sub_negPart hQ
  have horth : Qm * Qp = 0 := by
    dsimp only [Qm, Qp, Upstream.PrimitiveWeight.negPart,
      Upstream.PrimitiveWeight.posPart]
    rw [Upstream.PrimitiveWeight.cfc_mul]
    calc
      hQ.cfc (fun x => max (-x) 0 * max x 0) =
          hQ.cfc (fun _ => (0 : ℝ)) := by
        apply Upstream.PrimitiveWeight.cfc_congr hQ
        intro i
        by_cases hi : 0 ≤ hQ.eigenvalues i
        · simp [max_eq_right (neg_nonpos.mpr hi)]
        · have hi' : hQ.eigenvalues i ≤ 0 := le_of_not_ge hi
          simp [max_eq_right hi', max_eq_left (neg_nonneg.mpr hi')]
      _ = 0 := by rw [Upstream.PrimitiveWeight.cfc_const]; simp
  have htraceSplit : Q.trace.re = Qp.trace.re - Qm.trace.re := by
    rw [← hsplit, Matrix.trace_sub, Complex.sub_re]
  have htotal : ∀ c : ℝ, 0 < c →
      c * P.trace.re - c ^ 2 / 4 * r + 2 * c * Q.trace.re - c ^ 2 * b
        ≤ frobeniusSq (P + Q) := by
    intro c hc
    have hA := psd_sub_psd_rank_trace_bound hP hQm r hr c hc
    have hB := psd_rank_trace_bound hQp b hb (2 * c)
    have hcross : 0 ≤ (Matrix.trace ((P - Qm)ᴴ * Qp)).re := by
      rw [Matrix.conjTranspose_sub, hP.isHermitian.eq, hQm.isHermitian.eq,
        Matrix.sub_mul, horth, sub_zero]
      exact SMSTReflectionPositivity.trace_mul_nonneg_of_posSemidef hP hQp
    have hadd :
        frobeniusSq (P - Qm) + frobeniusSq Qp ≤
          frobeniusSq ((P - Qm) + Qp) := by
      rw [frobeniusSq_eq_hsNormSq, frobeniusSq_eq_hsNormSq,
        frobeniusSq_eq_hsNormSq]
      have hexp := SMSTReflectionPositivity.hsNormSq_sub (P - Qm) (-Qp)
      have hneg : SMSTReflectionPositivity.hsNormSq (-Qp) =
          SMSTReflectionPositivity.hsNormSq Qp := by
        unfold SMSTReflectionPositivity.hsNormSq
        rw [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg]
      have htrneg :
          (Matrix.trace ((P - Qm)ᴴ * (-Qp))).re =
            -(Matrix.trace ((P - Qm)ᴴ * Qp)).re := by
        rw [Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re]
      rw [sub_neg_eq_add, hneg, htrneg] at hexp
      linarith
    have hmatrix : (P - Qm) + Qp = P + Q := by
      rw [← hsplit]
      abel
    rw [hmatrix] at hadd
    have hbcast : (Qp.rank : ℝ) ≤ b := by exact_mod_cast hb
    rw [htraceSplit]
    nlinarith [hA, hB, hadd, sq_nonneg c]
  refine ⟨htotal, ?_⟩
  have h2 := htotal 2 (by norm_num)
  nlinarith

end GTRankTraceIndefiniteDirectExact
end NCG
