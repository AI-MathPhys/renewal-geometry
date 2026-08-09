import NCG.Grand.PeanoStability
import NCG.Grand.HolonomyCoercivity

/-!
# Exact EASY 75: finite contraction-chain stability

This is the quantitative engine used by both Peano residual estimates.  It is
the contraction analogue of the unitary tree-path estimate in
`operational_holonomy_coercivity`.
-/

open Finset Matrix

namespace NCG

/-- A length-`X` chain driven by contractions is controlled by `X²` times its
sum of squared edge defects.  The zero initial vertex makes the first defect
the anchor residual. -/
theorem contraction_chain_stability {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (U : ℕ → V →ₗ[ℂ] V) (hU : ∀ i x, ‖U i x‖ ≤ ‖x‖)
    (f : ℕ → V) (X : ℕ) (hf0 : f 0 = 0) :
    ∑ x ∈ Finset.range (X + 1), ‖f x‖ ^ 2
      ≤ (X : ℝ) ^ 2 *
        ∑ i ∈ Finset.range X, ‖f (i + 1) - U i (f i)‖ ^ 2 := by
  have hpt : ∀ x, ‖f x‖ ≤
      ∑ i ∈ Finset.range x, ‖f (i + 1) - U i (f i)‖ := by
    intro x
    induction x with
    | zero => simp [hf0]
    | succ x ih =>
        rw [Finset.sum_range_succ]
        have hkey : ‖f (x + 1)‖ ≤
            ‖f (x + 1) - U x (f x)‖ + ‖f x‖ := by
          calc
            ‖f (x + 1)‖
                = ‖(f (x + 1) - U x (f x)) + U x (f x)‖ := by
                    congr 1
                    abel
            _ ≤ ‖f (x + 1) - U x (f x)‖ + ‖U x (f x)‖ :=
                  norm_add_le _ _
            _ ≤ ‖f (x + 1) - U x (f x)‖ + ‖f x‖ :=
                  add_le_add_right (hU x (f x)) _
        linarith
  by_cases hX0 : X = 0
  · subst X
    simp [hf0]
  have hXpos : 0 < X := Nat.pos_of_ne_zero hX0
  have hstep : ∀ x ∈ Finset.range (X + 1),
      ‖f x‖ ^ 2 ≤ (x : ℝ) *
        ∑ i ∈ Finset.range X, ‖f (i + 1) - U i (f i)‖ ^ 2 := by
    intro x hx
    have hxle : x ≤ X := by
      simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hx
    have h1 : ‖f x‖ ^ 2 ≤
        (∑ i ∈ Finset.range x, ‖f (i + 1) - U i (f i)‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (hpt x) 2
    have h2 :
        (∑ i ∈ Finset.range x, ‖f (i + 1) - U i (f i)‖) ^ 2
          ≤ (x : ℝ) *
            ∑ i ∈ Finset.range x, ‖f (i + 1) - U i (f i)‖ ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := Finset.range x)
        (f := fun i => ‖f (i + 1) - U i (f i)‖))
    have h3 : ∑ i ∈ Finset.range x,
          ‖f (i + 1) - U i (f i)‖ ^ 2
        ≤ ∑ i ∈ Finset.range X,
          ‖f (i + 1) - U i (f i)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hi) hxle))
        (fun _ _ _ => sq_nonneg _)
    calc
      ‖f x‖ ^ 2
          ≤ (x : ℝ) * ∑ i ∈ Finset.range x,
              ‖f (i + 1) - U i (f i)‖ ^ 2 := h1.trans h2
      _ ≤ (x : ℝ) * ∑ i ∈ Finset.range X,
              ‖f (i + 1) - U i (f i)‖ ^ 2 :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
  have hcoeff : (∑ x ∈ Finset.range (X + 1), (x : ℝ))
      ≤ (X : ℝ) ^ 2 := by
    have hnat : (∑ i ∈ Finset.range (X + 1), i) * 2
        = (X + 1) * X := by
      simpa using Finset.sum_range_id_mul_two (X + 1)
    have hreal : (∑ x ∈ Finset.range (X + 1), (x : ℝ)) * 2
        = ((X : ℝ) + 1) * X := by
      have hc := congrArg (fun k : ℕ => (k : ℝ)) hnat
      push_cast at hc
      linarith
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hXpos
    nlinarith
  have henergy : 0 ≤ ∑ i ∈ Finset.range X,
      ‖f (i + 1) - U i (f i)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    ∑ x ∈ Finset.range (X + 1), ‖f x‖ ^ 2
        ≤ ∑ x ∈ Finset.range (X + 1),
            (x : ℝ) * ∑ i ∈ Finset.range X,
              ‖f (i + 1) - U i (f i)‖ ^ 2 :=
          Finset.sum_le_sum hstep
    _ = (∑ x ∈ Finset.range (X + 1), (x : ℝ)) *
          ∑ i ∈ Finset.range X, ‖f (i + 1) - U i (f i)‖ ^ 2 := by
          rw [Finset.sum_mul]
    _ ≤ (X : ℝ) ^ 2 *
          ∑ i ∈ Finset.range X, ‖f (i + 1) - U i (f i)‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right hcoeff henergy

/-- Recurrence form of the same estimate.  It is the exact scalar inequality
used after writing the columns of `A-L` (or `D-N`) as
`d_{b+1} = T d_b + R e_b`. -/
theorem finite_recurrence_stability {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (T : V →ₗ[ℂ] V) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (d q : ℕ → V) (r : V)
    (hd0 : d 0 = r)
    (hrec : ∀ n, d (n + 1) = T (d n) + q n)
    (X : ℕ) :
    ∑ n ∈ Finset.range X, ‖d n‖ ^ 2
      ≤ (X : ℝ) ^ 2 *
        (‖r‖ ^ 2 + ∑ n ∈ Finset.range X, ‖q n‖ ^ 2) := by
  let f : ℕ → V
    | 0 => 0
    | n + 1 => d n
  let U : ℕ → V →ₗ[ℂ] V
    | 0 => 0
    | _ + 1 => T
  have hU : ∀ i x, ‖U i x‖ ≤ ‖x‖ := by
    intro i x
    cases i with
    | zero => simp [U]
    | succ i => simpa [U] using hT x
  have hmain := contraction_chain_stability U hU f X (by rfl)
  have hleft_all : ∀ Y : ℕ,
      ∑ x ∈ Finset.range (Y + 1), ‖f x‖ ^ 2
        = ∑ n ∈ Finset.range Y, ‖d n‖ ^ 2 := by
    intro Y
    induction Y with
    | zero => simp [f]
    | succ Y ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
  have hleft := hleft_all X
  have hedge_eq : ∀ Y : ℕ,
      ∑ i ∈ Finset.range (Y + 1), ‖f (i + 1) - U i (f i)‖ ^ 2
        = ‖r‖ ^ 2 + ∑ n ∈ Finset.range Y, ‖q n‖ ^ 2 := by
    intro Y
    induction Y with
    | zero => simp [f, U, hd0]
    | succ Y ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        simp only [f, U]
        rw [hrec Y, add_sub_cancel_left]
        ac_rfl
  have hedge : ∑ i ∈ Finset.range X, ‖f (i + 1) - U i (f i)‖ ^ 2
      ≤ ‖r‖ ^ 2 + ∑ n ∈ Finset.range X, ‖q n‖ ^ 2 := by
    cases X with
    | zero => simp
    | succ X =>
        rw [hedge_eq X]
        exact add_le_add_right
          (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.le_succ X))
            (fun _ _ _ => sq_nonneg _)) _
  rw [hleft] at hmain
  exact hmain.trans (mul_le_mul_of_nonneg_left hedge (sq_nonneg _))

/-- A matrix column regarded as a vector in the Hilbert `ℓ²` norm. -/
noncomputable def matrixColumnL2 {m n : Type*} [Fintype m]
    (M : Matrix m n ℂ) (j : n) : EuclideanSpace ℂ m :=
  WithLp.toLp 2 (fun i => M i j)

/-- Matrix-column specialization of `finite_recurrence_stability`.  This is
the exact Hilbert--Schmidt estimate used for both residuals in
`thm:ar-Peano-stability`. -/
theorem matrix_column_recurrence_stability {X : ℕ} (hX : 0 < X)
    (T B R : Matrix (Fin X) (Fin X) ℂ)
    (hT : ∀ x : EuclideanSpace ℂ (Fin X),
      ‖T.toEuclideanLin x‖ ≤ ‖x‖)
    (hstep : ∀ n (hn : n + 1 < X),
      matrixColumnL2 B (⟨n + 1, hn⟩ : Fin X)
        = T.toEuclideanLin (matrixColumnL2 B (⟨n, by omega⟩ : Fin X))
          + matrixColumnL2 R (⟨n, by omega⟩ : Fin X)) :
    (((Bᴴ * B).trace).re
      ≤ (X : ℝ) ^ 2 *
        (‖matrixColumnL2 B (⟨0, hX⟩ : Fin X)‖ ^ 2
          + ((Rᴴ * R).trace).re)) := by
  let q : ℕ → EuclideanSpace ℂ (Fin X) := fun n =>
    if hn : n < X then matrixColumnL2 R (⟨n, hn⟩ : Fin X) else 0
  let d : ℕ → EuclideanSpace ℂ (Fin X) := fun n =>
    Nat.rec (matrixColumnL2 B (⟨0, hX⟩ : Fin X))
      (fun k prev => T.toEuclideanLin prev + q k) n
  have hd0 : d 0 = matrixColumnL2 B (⟨0, hX⟩ : Fin X) := rfl
  have hdrec : ∀ n, d (n + 1) = T.toEuclideanLin (d n) + q n := by
    intro n
    rfl
  have hdcol : ∀ n (hn : n < X),
      d n = matrixColumnL2 B (⟨n, hn⟩ : Fin X) := by
    intro n
    induction n with
    | zero =>
        intro hn
        congr
    | succ n ih =>
        intro hn
        have hn0 : n < X := by omega
        rw [hdrec, ih hn0]
        simp only [q, dif_pos hn0]
        exact (hstep n hn).symm
  have hbound := finite_recurrence_stability T.toEuclideanLin hT d q
    (matrixColumnL2 B (⟨0, hX⟩ : Fin X)) hd0 hdrec X
  have hcolnorm : ∀ (M : Matrix (Fin X) (Fin X) ℂ) (j : Fin X),
      ‖matrixColumnL2 M j‖ ^ 2 = ∑ i, Complex.normSq (M i j) := by
    intro M j
    rw [EuclideanSpace.norm_sq_eq]
    simp only [matrixColumnL2, WithLp.ofLp_toLp,
      Complex.normSq_eq_norm_sq]
  have hB : ((Bᴴ * B).trace).re =
      ∑ n ∈ Finset.range X, ‖d n‖ ^ 2 := by
    rw [trace_conj_self_re]
    calc
      (∑ j, ∑ i, Complex.normSq (B i j))
          = ∑ j : Fin X, ‖matrixColumnL2 B j‖ ^ 2 := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hcolnorm]
      _ = ∑ n ∈ Finset.range X, ‖d n‖ ^ 2 := by
              rw [← Fin.sum_univ_eq_sum_range]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hdcol j j.isLt]
  have hR : (∑ n ∈ Finset.range X, ‖q n‖ ^ 2)
      = ((Rᴴ * R).trace).re := by
    rw [trace_conj_self_re]
    calc
      (∑ n ∈ Finset.range X, ‖q n‖ ^ 2)
          = ∑ j : Fin X, ‖matrixColumnL2 R j‖ ^ 2 := by
              rw [← Fin.sum_univ_eq_sum_range]
              refine Finset.sum_congr rfl fun j _ => ?_
              simp [q, j.isLt]
      _ = ∑ j, ∑ i, Complex.normSq (R i j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hcolnorm]
  rw [hB, ← hR]
  exact hbound

/-- The abstract matrix estimate specialized to the truncated-shift column
recurrence. -/
theorem matrix_shift_residual_stability {X : ℕ} (hX : 0 < X)
    (a : ℕ) (B : Matrix (Fin X) (Fin X) ℂ)
    (hcontract : ∀ x : EuclideanSpace ℂ (Fin X),
      ‖((recS X) ^ a).toEuclideanLin x‖ ≤ ‖x‖) :
    ((Bᴴ * B).trace).re ≤ (X : ℝ) ^ 2 *
      (‖matrixColumnL2 B (⟨0, hX⟩ : Fin X)‖ ^ 2
        + ((((B * recS X - (recS X) ^ a * B)ᴴ
          * (B * recS X - (recS X) ^ a * B)).trace).re)) := by
  apply matrix_column_recurrence_stability hX ((recS X) ^ a) B
    (B * recS X - (recS X) ^ a * B) hcontract
  intro n hn
  apply WithLp.ofLp_injective
  funext i
  simp only [matrixColumnL2, WithLp.ofLp_add, WithLp.ofLp_toLp,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Pi.add_apply,
    Matrix.sub_apply, Matrix.mulVec, dotProduct]
  have hfirst : ∑ k, B i k * recS X k (⟨n, by omega⟩ : Fin X)
      = B i (⟨n + 1, hn⟩ : Fin X) := by
    rw [Finset.sum_eq_single (⟨n + 1, hn⟩ : Fin X)]
    · simp [recS]
    · intro k _ hk
      rw [recS, Matrix.of_apply, if_neg]
      · simp
      · intro heq
        apply hk
        exact Fin.ext heq
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [hfirst]
  ring

/-- Truncated successor powers are contractions in the genuine Hilbert `ℓ²`
norm. -/
theorem recS_pow_euclidean_contraction (X a : ℕ)
    (x : EuclideanSpace ℂ (Fin X)) :
    ‖((recS X) ^ a).toEuclideanLin x‖ ≤ ‖x‖ := by
  let back : Fin X → Fin X := fun j =>
    ⟨(j : ℕ) - a, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
  have hout : ∀ j : Fin X,
      WithLp.ofLp (((recS X) ^ a).toEuclideanLin x) j =
        if a ≤ (j : ℕ) then WithLp.ofLp x (back j) else 0 := by
    intro j
    rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, recS_pow]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    by_cases hj : a ≤ (j : ℕ)
    · rw [if_pos hj]
      rw [Finset.sum_eq_single (back j)]
      · rw [if_pos]
        · simp
        · simp [back]
          omega
      · intro k _ hk
        have hne : (j : ℕ) ≠ (k : ℕ) + a := by
          intro heq
          apply hk
          apply Fin.ext
          simp only [back]
          omega
        simp [hne]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · rw [if_neg hj]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hne : (j : ℕ) ≠ (k : ℕ) + a := by omega
      simp [hne]
  have hsquare : ‖((recS X) ^ a).toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp_rw [hout]
    let s : Finset (Fin X) := Finset.univ.filter fun j => a ≤ (j : ℕ)
    have hsum : (∑ j : Fin X,
        ‖if a ≤ (j : ℕ) then WithLp.ofLp x (back j) else 0‖ ^ 2)
        = ∑ j ∈ s, ‖WithLp.ofLp x (back j)‖ ^ 2 := by
      rw [show (∑ j : Fin X,
          ‖if a ≤ (j : ℕ) then WithLp.ofLp x (back j) else 0‖ ^ 2)
          = ∑ j : Fin X,
              if a ≤ (j : ℕ) then ‖WithLp.ofLp x (back j)‖ ^ 2 else 0 from by
            refine Finset.sum_congr rfl fun j _ => ?_
            split_ifs <;> simp]
      rw [← Finset.sum_filter]
    rw [hsum]
    calc
      (∑ j ∈ s, ‖WithLp.ofLp x (back j)‖ ^ 2)
          = ∑ i ∈ s.image back, ‖WithLp.ofLp x i‖ ^ 2 := by
              symm
              apply Finset.sum_image
              intro j hj k hk heq
              change j ∈ s at hj
              change k ∈ s at hk
              simp only [s, Finset.mem_filter, Finset.mem_univ,
                true_and] at hj hk
              apply Fin.ext
              have hsub : (j : ℕ) - a = (k : ℕ) - a :=
                congrArg Fin.val heq
              omega
      _ ≤ ∑ i, ‖WithLp.ofLp x i‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ _)
              (fun _ _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (((recS X) ^ a).toEuclideanLin x), norm_nonneg x]

/-- Squared Hilbert norm of a matrix column, in the entrywise form used by the
manuscript's anchor residual. -/
theorem matrixColumnL2_norm_sq {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) (j : n) :
    ‖matrixColumnL2 M j‖ ^ 2 =
      ∑ i, Complex.normSq ((M *ᵥ Pi.single j 1) i) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [matrixColumnL2, WithLp.ofLp_toLp,
    Complex.normSq_eq_norm_sq, Matrix.mulVec_single_one, Matrix.col_apply]

/-- Squared Hilbert--Schmidt norm in the trace convention of the manuscript. -/
def hsMatrixSq {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : ℝ := ((Mᴴ * M).trace).re

/-- Positive Peano covariance/anchor residual. -/
def peanoResidual {X : ℕ} (hX : 0 < X) (a : ℕ)
    (A : Matrix (Fin X) (Fin X) ℂ) : ℝ :=
  (∑ j, Complex.normSq
      ((A *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
        - (recS X) ^ (a - 1)
          *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j))
    + hsMatrixSq (A * recS X - (recS X) ^ a * A)

/-- Positive count commutator/anchor residual. -/
def countResidual {X : ℕ} (hX : 0 < X)
    (D : Matrix (Fin X) (Fin X) ℂ) : ℝ :=
  (∑ j, Complex.normSq
      ((D *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
        - (Pi.single (⟨0, hX⟩ : Fin X) 1 : Fin X → ℂ)) j))
    + hsMatrixSq (D * recS X - recS X * D - recS X)

/-- The complete `thm:ar-Peano-stability` package: the existing exact
zero-residual characterizations together with both boxed `X²`
Hilbert--Schmidt estimates. -/
theorem ar_peano_stability_exact {X : ℕ} (hX : 0 < X) (a : ℕ)
    (ha : 1 ≤ a) (A D : Matrix (Fin X) (Fin X) ℂ) :
    ((peanoResidual hX a A = 0 ↔ A = peanoL X a)
      ∧ (countResidual hX D = 0 ↔
        D = Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ))))
    ∧ hsMatrixSq (A - peanoL X a)
        ≤ (X : ℝ) ^ 2 * peanoResidual hX a A
    ∧ hsMatrixSq
        (D - Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ)))
        ≤ (X : ℝ) ^ 2 * countResidual hX D := by
  let η : Fin X → ℂ := Pi.single (⟨0, hX⟩ : Fin X) 1
  let N : Matrix (Fin X) (Fin X) ℂ :=
    Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ))
  have hzero := peano_stability hX a ha A D
  have hA := matrix_shift_residual_stability hX a (A - peanoL X a)
    (recS_pow_euclidean_contraction X a)
  have hAR : (A - peanoL X a) * recS X
        - (recS X) ^ a * (A - peanoL X a)
      = A * recS X - (recS X) ^ a * A := by
    rw [Matrix.sub_mul, Matrix.mul_sub, peanoL_covariance a ha]
    abel
  have hAη : (A - peanoL X a) *ᵥ η
      = A *ᵥ η - (recS X) ^ (a - 1) *ᵥ η := by
    rw [Matrix.sub_mulVec, peanoL_anchor hX a ha]
  have hAcol : ‖matrixColumnL2 (A - peanoL X a)
        (⟨0, hX⟩ : Fin X)‖ ^ 2
      = ∑ j, Complex.normSq
          ((A *ᵥ η - (recS X) ^ (a - 1) *ᵥ η) j) := by
    rw [matrixColumnL2_norm_sq]
    rw [show Pi.single (⟨0, hX⟩ : Fin X) 1 = η from rfl, hAη]
  have hNcomm : N * recS X - recS X * N = recS X := by
    exact (recS_relations (show 1 ≤ X from hX)).2.2
  have hNη : N *ᵥ η = η := by
    funext j
    simp only [N, η]
    rw [mulVec_single_col, Matrix.diagonal_apply, Pi.single_apply]
    by_cases hj : j = (⟨0, hX⟩ : Fin X)
    · rw [if_pos hj, if_pos hj, hj]
      norm_num
    · rw [if_neg hj, if_neg hj]
  have hD := matrix_shift_residual_stability hX 1 (D - N)
    (recS_pow_euclidean_contraction X 1)
  have hDR : (D - N) * recS X - (recS X) ^ 1 * (D - N)
      = D * recS X - recS X * D - recS X := by
    rw [pow_one, Matrix.sub_mul, Matrix.mul_sub]
    rw [show N * recS X = recS X * N + recS X from by
      calc
        N * recS X = recS X + recS X * N := sub_eq_iff_eq_add.mp hNcomm
        _ = recS X * N + recS X := add_comm _ _]
    abel
  have hDη : (D - N) *ᵥ η = D *ᵥ η - η := by
    rw [Matrix.sub_mulVec, hNη]
  have hDcol : ‖matrixColumnL2 (D - N) (⟨0, hX⟩ : Fin X)‖ ^ 2
      = ∑ j, Complex.normSq ((D *ᵥ η - η) j) := by
    rw [matrixColumnL2_norm_sq]
    rw [show Pi.single (⟨0, hX⟩ : Fin X) 1 = η from rfl, hDη]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [peanoResidual, countResidual, hsMatrixSq] using hzero
  · simpa only [hsMatrixSq, peanoResidual, η, hAR, hAcol] using hA
  · rw [hDR, hDcol] at hD
    simpa only [hsMatrixSq, countResidual, N, η, pow_one] using hD

end NCG
