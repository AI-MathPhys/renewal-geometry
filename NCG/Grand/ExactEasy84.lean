/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniversalFeedback
import NCG.Grand.FeedbackRealization
import NCG.Grand.HankelMinimality
import NCG.Grand.PreRenewalRecovery

open Matrix
open scoped Norms.L2Operator

namespace NCG

/-- Analytic Schur-resolvent form of the feedback generating series.  The
two norm hypotheses are precisely the convergence domain of the two Neumann
series occurring in the displayed manuscript identity. -/
theorem feedback_resolvent_series {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (A : Matrix d d ℂ) (B : Matrix d e ℂ)
    (C : Matrix e d ℂ) (D : Matrix e e ℂ) (z : ℂ)
    (hT : ‖z • Matrix.fromBlocks A B C D‖ < 1)
    (hD : ‖z • D‖ < 1) :
    (∑' n : ℕ, z ^ n •
        ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁) =
      (1 - z • A - z ^ 2 •
        (B * (1 - z • D)⁻¹ * C))⁻¹ := by
  let T : Matrix (d ⊕ e) (d ⊕ e) ℂ := Matrix.fromBlocks A B C D
  let Q : Matrix (d ⊕ e) (d ⊕ e) ℂ := 1 - z • T
  let R : Matrix (d ⊕ e) (d ⊕ e) ℂ := ∑' n : ℕ, (z • T) ^ n
  have hsT : Summable (fun n : ℕ => (z • T) ^ n) :=
    summable_geometric_of_norm_lt_one hT
  have hQR : Q * R = 1 := by
    simpa [Q, R] using hsT.one_sub_mul_tsum_pow
  have hRQ : R * Q = 1 := by
    simpa [Q, R] using hsT.tsum_pow_mul_one_sub
  have hQunit : IsUnit Q.det := Matrix.isUnit_det_of_right_inverse hQR
  have hRinv : R = Q⁻¹ := by
    rw [Matrix.inv_eq_right_inv hQR]
  have hsD : Summable (fun n : ℕ => (z • D) ^ n) :=
    summable_geometric_of_norm_lt_one hD
  have hDright : (1 - z • D) * (∑' n : ℕ, (z • D) ^ n) = 1 :=
    hsD.one_sub_mul_tsum_pow
  have hDinv : (∑' n : ℕ, (z • D) ^ n) = (1 - z • D)⁻¹ := by
    rw [Matrix.inv_eq_right_inv hDright]
  have hQblocks : Q = Matrix.fromBlocks
      (1 - z • A) (-(z • B)) (-(z • C)) (1 - z • D) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Q, T, Matrix.fromBlocks, Matrix.one_apply]
  have hRblocks : R = Matrix.fromBlocks R.toBlocks₁₁ R.toBlocks₁₂
      R.toBlocks₂₁ R.toBlocks₂₂ := (Matrix.fromBlocks_toBlocks R).symm
  have hblockeq := hQR
  rw [hQblocks, hRblocks, Matrix.fromBlocks_multiply] at hblockeq
  rw [← Matrix.fromBlocks_one] at hblockeq
  have h11 : (1 - z • A) * R.toBlocks₁₁ -
      (z • B) * R.toBlocks₂₁ = 1 := by
    have := congrArg Matrix.toBlocks₁₁ hblockeq
    simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.neg_mul,
      Matrix.smul_mul, sub_eq_add_neg] using this
  have h21 : -(z • C) * R.toBlocks₁₁ +
      (1 - z • D) * R.toBlocks₂₁ = 0 := by
    have := congrArg Matrix.toBlocks₂₁ hblockeq
    simpa only [Matrix.toBlocks_fromBlocks₂₁] using this
  have hY : R.toBlocks₂₁ =
      (1 - z • D)⁻¹ * (z • C) * R.toBlocks₁₁ := by
    have hbase : (1 - z • D) * R.toBlocks₂₁ =
        (z • C) * R.toBlocks₁₁ := by
      rw [Matrix.neg_mul, neg_add_eq_sub] at h21
      exact sub_eq_zero.mp h21
    calc
      R.toBlocks₂₁ = (∑' n : ℕ, (z • D) ^ n) *
          ((1 - z • D) * R.toBlocks₂₁) := by
            rw [← Matrix.mul_assoc, hsD.tsum_pow_mul_one_sub,
              Matrix.one_mul]
      _ = (∑' n : ℕ, (z • D) ^ n) *
          ((z • C) * R.toBlocks₁₁) := by rw [hbase]
      _ = (1 - z • D)⁻¹ * (z • C) * R.toBlocks₁₁ := by
        rw [hDinv, Matrix.mul_assoc]
  let S : Matrix d d ℂ :=
    1 - z • A - z ^ 2 • (B * (1 - z • D)⁻¹ * C)
  have hSR : S * R.toBlocks₁₁ = 1 := by
    dsimp only [S]
    rw [Matrix.sub_mul]
    have hz : (z • B) * ((1 - z • D)⁻¹ * (z • C) * R.toBlocks₁₁) =
        (z ^ 2 • (B * (1 - z • D)⁻¹ * C)) * R.toBlocks₁₁ := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.mul_assoc]
      congr 1
      ring
    rw [← hz, ← hY]
    exact h11
  have hSinv : R.toBlocks₁₁ = S⁻¹ := by
    exact (Matrix.inv_eq_right_inv hSR).symm
  have hsumBlocks : (∑' n : ℕ, z ^ n • (T ^ n).toBlocks₁₁) =
      R.toBlocks₁₁ := by
    have hpow : ∀ n : ℕ, (z • T) ^ n = z ^ n • T ^ n := by
      intro n
      rw [smul_pow]
    ext i j
    have hs1 : ∀ i : d ⊕ e, Summable (fun n => ((z • T) ^ n) i) :=
      Pi.summable.mp hsT
    have hs2 : ∀ i : d ⊕ e, ∀ j : d ⊕ e,
        Summable (fun n => ((z • T) ^ n) i j) := fun i =>
      Pi.summable.mp (hs1 i)
    have hsBlock : Summable
        (fun n : ℕ => z ^ n • (T ^ n).toBlocks₁₁) := by
      apply Pi.summable.mpr
      intro i
      apply Pi.summable.mpr
      intro j
      exact (hs2 (Sum.inl i) (Sum.inl j)).congr fun n => by
        rw [hpow]
        rfl
    have hLi := tsum_apply (f := fun n : ℕ =>
      z ^ n • (T ^ n).toBlocks₁₁) (x := i) hsBlock
    have hLij := tsum_apply (f := fun n : ℕ =>
      (z ^ n • (T ^ n).toBlocks₁₁) i) (x := j)
      ((Pi.summable.mp hsBlock) i)
    have hRi := tsum_apply (f := fun n : ℕ => (z • T) ^ n)
      (x := Sum.inl i) hsT
    have hRij := tsum_apply (f := fun n : ℕ =>
      ((z • T) ^ n) (Sum.inl i)) (x := Sum.inl j)
      (hs1 (Sum.inl i))
    calc
      (∑' n : ℕ, z ^ n • (T ^ n).toBlocks₁₁) i j
          = ∑' n : ℕ, (z ^ n • (T ^ n).toBlocks₁₁) i j :=
            (congrFun hLi j).trans hLij
      _ = ∑' n : ℕ, ((z • T) ^ n) (Sum.inl i) (Sum.inl j) := by
        apply tsum_congr
        intro n
        rw [hpow]
        rfl
      _ = R (Sum.inl i) (Sum.inl j) := by
        dsimp only [R]
        exact (hRij.symm.trans (congrFun hRi (Sum.inl j)).symm)
      _ = R.toBlocks₁₁ i j := rfl
  simpa only [T, S] using hsumBlocks.trans hSinv

/-- Iterating the one-step feedback error inequality gives exactly the
triangular weights in the manuscript's contraction estimate. -/
theorem feedback_error_telescoping
    (err kernel : ℕ → ℝ) (a : ℝ)
    (hzero : err 0 = 0)
    (hstep : ∀ n, err (n + 1) ≤ err n + a +
      ∑ k ∈ Finset.range n, kernel k) :
    ∀ n, err n ≤ (n : ℝ) * a +
      ∑ k ∈ Finset.range (n - 1),
        ((n - 1 - k : ℕ) : ℝ) * kernel k := by
  intro n
  induction n with
  | zero => simpa using le_of_eq hzero
  | succ n ih =>
      calc
        err (n + 1) ≤ err n + a +
            ∑ k ∈ Finset.range n, kernel k := hstep n
        _ ≤ ((n : ℝ) * a +
              ∑ k ∈ Finset.range (n - 1),
                ((n - 1 - k : ℕ) : ℝ) * kernel k) + a +
              ∑ k ∈ Finset.range n, kernel k := by gcongr
        _ = ((n + 1 : ℕ) : ℝ) * a +
              ∑ k ∈ Finset.range ((n + 1) - 1),
                (((n + 1) - 1 - k : ℕ) : ℝ) * kernel k := by
          cases n with
          | zero => simp
          | succ m =>
              simp only [Nat.succ_sub_one, Finset.sum_range_succ]
              have hterm : ∀ k ∈ Finset.range m,
                  (((m - k : ℕ) : ℝ) * kernel k + kernel k) =
                    (((m + 1 - k : ℕ) : ℝ) * kernel k) := by
                intro k hk
                have hk' : k < m := Finset.mem_range.mp hk
                have hn : m + 1 - k = (m - k) + 1 := by omega
                rw [hn]
                push_cast
                ring
              have hsum :
                  (∑ k ∈ Finset.range m,
                      ((m - k : ℕ) : ℝ) * kernel k) +
                    ∑ k ∈ Finset.range m, kernel k =
                  ∑ k ∈ Finset.range m,
                    ((m + 1 - k : ℕ) : ℝ) * kernel k := by
                rw [← Finset.sum_add_distrib,
                  Finset.sum_congr rfl hterm]
              calc
                ((m + 1 : ℕ) : ℝ) * a +
                    (∑ k ∈ Finset.range m,
                      ((m - k : ℕ) : ℝ) * kernel k) + a +
                    ((∑ k ∈ Finset.range m, kernel k) + kernel m) =
                    (((m + 2 : ℕ) : ℝ) * a) +
                    ((∑ k ∈ Finset.range m,
                        ((m - k : ℕ) : ℝ) * kernel k) +
                      ∑ k ∈ Finset.range m, kernel k) + kernel m := by
                        push_cast
                        ring
                _ = (((m + 2 : ℕ) : ℝ) * a) +
                    (∑ k ∈ Finset.range m,
                      ((m + 1 - k : ℕ) : ℝ) * kernel k) + kernel m := by
                        rw [hsum]
                _ = ((m + 1 + 1 : ℕ) : ℝ) * a +
                    ((∑ k ∈ Finset.range m,
                      ((m + 1 - k : ℕ) : ℝ) * kernel k) +
                      ((m + 1 - m : ℕ) : ℝ) * kernel m) := by
                        push_cast
                        simp
                        ring

/-- Norm form of the feedback estimate.  `hA` and `hX` are the two
compression-contraction consequences of contractivity of the full block
transfer; spelling them out makes the estimate reusable in any normed ring. -/
theorem feedback_contraction_bound {R : Type*} [NormedRing R]
    (X kernel : ℕ → R) (A T0 : R)
    (hX0 : X 0 = 1)
    (hrec : ∀ n, X (n + 1) = A * X n +
      ∑ j ∈ Finset.range n, kernel (n - 1 - j) * X j)
    (hOne : ‖(1 : R)‖ ≤ 1)
    (hA : ‖A‖ ≤ 1) (hT0 : ‖T0‖ ≤ 1)
    (hX : ∀ n, ‖X n‖ ≤ 1) :
    ∀ n, ‖X n - T0 ^ n‖ ≤
      (n : ℝ) * ‖A - T0‖ +
        ∑ k ∈ Finset.range (n - 1),
          ((n - 1 - k : ℕ) : ℝ) * ‖kernel k‖ := by
  have hTpow : ∀ n : ℕ, ‖T0 ^ n‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simpa using hOne
    | succ n ih =>
        rw [pow_succ']
        calc
          ‖T0 * T0 ^ n‖ ≤ ‖T0‖ * ‖T0 ^ n‖ := norm_mul_le _ _
          _ ≤ 1 * 1 := mul_le_mul hT0 ih (norm_nonneg _) (by positivity)
          _ = 1 := one_mul 1
  have hstep : ∀ n, ‖X (n + 1) - T0 ^ (n + 1)‖ ≤
      ‖X n - T0 ^ n‖ + ‖A - T0‖ +
        ∑ k ∈ Finset.range n, ‖kernel k‖ := by
    intro n
    have hdecomp : X (n + 1) - T0 ^ (n + 1) =
        A * (X n - T0 ^ n) + (A - T0) * T0 ^ n +
          ∑ j ∈ Finset.range n, kernel (n - 1 - j) * X j := by
      rw [hrec, pow_succ']
      noncomm_ring
    have hsum : ‖∑ j ∈ Finset.range n,
        kernel (n - 1 - j) * X j‖ ≤
        ∑ k ∈ Finset.range n, ‖kernel k‖ := by
      calc
        ‖∑ j ∈ Finset.range n, kernel (n - 1 - j) * X j‖ ≤
            ∑ j ∈ Finset.range n,
              ‖kernel (n - 1 - j) * X j‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.range n, ‖kernel (n - 1 - j)‖ := by
          apply Finset.sum_le_sum
          intro j hj
          calc
            ‖kernel (n - 1 - j) * X j‖ ≤
                ‖kernel (n - 1 - j)‖ * ‖X j‖ := norm_mul_le _ _
            _ ≤ ‖kernel (n - 1 - j)‖ * 1 := by
              gcongr
              exact hX j
            _ = ‖kernel (n - 1 - j)‖ := mul_one _
        _ = ∑ k ∈ Finset.range n, ‖kernel k‖ :=
          Finset.sum_range_reflect (fun k => ‖kernel k‖) n
    rw [hdecomp]
    calc
      ‖A * (X n - T0 ^ n) + (A - T0) * T0 ^ n +
          ∑ j ∈ Finset.range n, kernel (n - 1 - j) * X j‖ ≤
          ‖A * (X n - T0 ^ n)‖ + ‖(A - T0) * T0 ^ n‖ +
            ‖∑ j ∈ Finset.range n,
              kernel (n - 1 - j) * X j‖ := by
                exact (norm_add_le _ _).trans
                  (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (‖A‖ * ‖X n - T0 ^ n‖) +
          (‖A - T0‖ * ‖T0 ^ n‖) +
            ∑ k ∈ Finset.range n, ‖kernel k‖ := by
              gcongr
              · exact norm_mul_le _ _
              · exact norm_mul_le _ _
      _ ≤ ‖X n - T0 ^ n‖ + ‖A - T0‖ +
            ∑ k ∈ Finset.range n, ‖kernel k‖ := by
              gcongr
              · exact mul_le_of_le_one_left (norm_nonneg _) hA
              · exact mul_le_of_le_one_right (norm_nonneg _) (hTpow n)
  exact feedback_error_telescoping
    (fun n => ‖X n - T0 ^ n‖) (fun k => ‖kernel k‖)
    ‖A - T0‖ (by simp [hX0]) hstep

/-- Isometric inclusion of the old carrier into an old/external block sum. -/
def oldCarrierInjection (d e : Type*) [DecidableEq d] [DecidableEq e] :
    Matrix (d ⊕ e) d ℂ := fun x j => if x = Sum.inl j then 1 else 0

theorem oldCarrierInjection_gram {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e] :
    (oldCarrierInjection d e)ᴴ * oldCarrierInjection d e = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (Sum.inl i)]
  · simp [oldCarrierInjection, Matrix.one_apply]
  · intro k hk hki
    have hne : k ≠ Sum.inl i := by
      intro h
      exact hki h
    simp [oldCarrierInjection, hne]
  · simp

theorem matrix_l2_norm_one_le {n : Type*}
    [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_def]
  have hmap :
      ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := n) (n := n)) ≪≫ₗ
          LinearMap.toContinuousLinearMap) (1 : Matrix n n ℂ) =
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ n) := by
    ext x
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
      LinearEquiv.trans_apply, Matrix.toLin_one]
    rfl
  rw [hmap]
  exact ContinuousLinearMap.norm_id_le

theorem oldCarrierInjection_norm_le {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e] :
    ‖oldCarrierInjection d e‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self
    (oldCarrierInjection d e)
  have hOne : ‖(1 : Matrix d d ℂ)‖ ≤ 1 :=
    matrix_l2_norm_one_le
  rw [oldCarrierInjection_gram] at h
  nlinarith [norm_nonneg (oldCarrierInjection d e)]

/-- A principal old-carrier compression cannot increase the Hilbert operator
norm. -/
theorem old_compression_norm_le {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (M : Matrix (d ⊕ e) (d ⊕ e) ℂ) :
    ‖M.toBlocks₁₁‖ ≤ ‖M‖ := by
  let J := oldCarrierInjection d e
  have hcompress : M.toBlocks₁₁ = Jᴴ * M * J := by
    classical
    ext i j
    simp [J, oldCarrierInjection, Matrix.mul_apply,
      Matrix.toBlocks₁₁]
  rw [hcompress]
  calc
    ‖Jᴴ * M * J‖ ≤ ‖Jᴴ * M‖ * ‖J‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Jᴴ‖ * ‖M‖) * ‖J‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
      gcongr
      · rw [Matrix.l2_opNorm_conjTranspose]
        exact oldCarrierInjection_norm_le
      · exact oldCarrierInjection_norm_le
    _ = ‖M‖ := by ring

/-- The displayed feedback error estimate directly from contractivity of the
full enlarged transfer and of the old transfer. -/
theorem matrix_feedback_contraction_bound {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (T0 A : Matrix d d ℂ) (B : Matrix d e ℂ)
    (C : Matrix e d ℂ) (D : Matrix e e ℂ)
    (hfull : ‖Matrix.fromBlocks A B C D‖ ≤ 1)
    (hT0 : ‖T0‖ ≤ 1) :
    ∀ n : ℕ, ‖((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁ - T0 ^ n‖ ≤
      (n : ℝ) * ‖A - T0‖ +
        ∑ k ∈ Finset.range (n - 1),
          ((n - 1 - k : ℕ) : ℝ) * ‖B * D ^ k * C‖ := by
  let T := Matrix.fromBlocks A B C D
  let X : ℕ → Matrix d d ℂ := fun n => (T ^ n).toBlocks₁₁
  have hX0 : X 0 = 1 := by
    simp [X, T, ← Matrix.fromBlocks_one]
  have hrec : ∀ n, X (n + 1) = A * X n +
      ∑ j ∈ Finset.range n, (B * D ^ (n - 1 - j) * C) * X j := by
    intro n
    cases n with
    | zero =>
        rw [show X 1 = A from (pre_renewal_visible_recovery A B C D).1]
        simp [hX0]
    | succ m =>
        simpa [X, T] using
          (pre_renewal_visible_recovery A B C D).2.1 m
  have hA : ‖A‖ ≤ 1 := by
    have hblock : T.toBlocks₁₁ = A := by simp [T]
    rw [← hblock]
    exact (old_compression_norm_le T).trans hfull
  have hX : ∀ n, ‖X n‖ ≤ 1 := by
    have hOneFull : ‖(1 : Matrix (d ⊕ e) (d ⊕ e) ℂ)‖ ≤ 1 :=
      matrix_l2_norm_one_le
    have hTpow : ∀ n : ℕ, ‖T ^ n‖ ≤ 1 := by
      intro n
      induction n with
      | zero => simpa using hOneFull
      | succ n ih =>
          rw [pow_succ']
          calc
            ‖T * T ^ n‖ ≤ ‖T‖ * ‖T ^ n‖ := Matrix.l2_opNorm_mul _ _
            _ ≤ 1 * 1 := mul_le_mul hfull ih (norm_nonneg _) (by positivity)
            _ = 1 := one_mul 1
    intro n
    calc
      ‖X n‖ ≤ ‖T ^ n‖ := old_compression_norm_le _
      _ ≤ 1 := hTpow n
  have hOne : ‖(1 : Matrix d d ℂ)‖ ≤ 1 :=
    matrix_l2_norm_one_le
  exact feedback_contraction_bound X (fun k => B * D ^ k * C)
    A T0 hX0 hrec hOne hA hT0 hX

end NCG
