/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.DetDerivative

/-!
# Spectral-source determinant Ward theorem
  (`thm:spectral-source-Ward-master`, flagship manuscript)

For the determinant-loaded source `v(q) = (det q/det q₀)^{1/2}e₀`
and any positive `F`:

* the boxed determinant response
  `ℛ_F(q) = c_F·det q/det q₀`, `c_F = ⟨e₀,Fe₀⟩ ≥ 0`
  (`ward_scalar_response`);
* the boxed Hessian identity
  `D²det(q)[h,k] = det q(Tr(q⁻¹h)Tr(q⁻¹k) - Tr(q⁻¹h·q⁻¹k))`
  (`hessian_det`, genuine iterated real derivatives: the inner
  derivative is the Jacobi adjugate formula `hasDerivAt_det`;
  the outer derivative differentiates the adjugate entrywise
  through its minor representation and is solved from the
  differentiated Cramer identity `M·adj M = det M·1`) — this is
  the boxed normalized negative configuration Hessian `𝔅_q`;
* the boxed signature data: `𝔅(X,X) = Tr(X₀²) - 6x²` on the
  trace decomposition `X = X₀ + xI`
  (`ward_trace_decomposition`), positive on nonzero symmetric
  traceless directions (`ward_traceless_pos`) and negative on
  the scalar line (`ward_scalar_neg`) — the `(5,1)` signature;
* the boxed cotangent inverse `Tr(PQ) - ½Tr(P)Tr(Q)`: the trace
  representers `X ↦ X - Tr(X)·1` and `P ↦ P - ½Tr(P)·1` are
  two-sided inverses (`ward_inverse_left`, `ward_inverse_right`).

The remark that additional cyclic modes enter only through `c_F`
is the abstract `F`-dependence of `ward_scalar_response`.
-/

namespace NCG

open Matrix

attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] RCLike.innerProductSpace
attribute [local instance 2000] NormedField.toNormedSpace

variable {n : ℕ}

/-- Entrywise line derivative helper. -/
lemma hasDerivAt_entry (q k : Matrix (Fin n) (Fin n) ℝ)
    (a c : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (q + s • k) a c) (k a c) t := by
  simp only [Matrix.add_apply, Matrix.smul_apply]
  have h9 := ((hasDerivAt_id t).smul_const (k a c)).const_add
    (q a c)
  rw [one_smul] at h9
  exact h9

/-- Entrywise differentiability of the adjugate along a line,
through the minor representation of each entry. -/
lemma hasDerivAt_adjugate (q k : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => adjugate (q + s • k) i j)
      (Matrix.trace (adjugate
          ((q + t • k).updateRow j (Pi.single i 1))
        * (k.updateRow j 0))) t := by
  have h1 : ∀ a b, HasDerivAt (fun s : ℝ =>
      ((q + s • k).updateRow j (Pi.single i 1)) a b)
      ((k.updateRow j 0) a b) t := by
    intro a b
    by_cases hab : a = j
    · subst hab
      simp only [Matrix.updateRow_self]
      exact hasDerivAt_const t _
    · simp only [Matrix.updateRow_ne hab]
      exact hasDerivAt_entry q k a b t
  have h2 : (fun s : ℝ => adjugate (q + s • k) i j)
      = fun s => ((q + s • k).updateRow j
          (Pi.single i 1)).det := by
    funext s
    rw [adjugate_apply]
  rw [h2]
  exact hasDerivAt_det h1

/-- The entrywise line derivative of the adjugate at `t = 0`. -/
noncomputable def adjDeriv (q k : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Matrix.trace (adjugate
    (q.updateRow j (Pi.single i 1)) * (k.updateRow j 0))

lemma hasDerivAt_adjugate_zero (q k : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    HasDerivAt (fun s : ℝ => adjugate (q + s • k) i j)
      (adjDeriv q k i j) 0 := by
  have h := hasDerivAt_adjugate q k i j 0
  simpa [adjDeriv] using h

/-- The Jacobi derivative of the determinant along the line. -/
lemma hasDerivAt_det_line (q k : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => (q + s • k).det)
      (Matrix.trace (adjugate (q + t • k) * k)) t := by
  exact hasDerivAt_det fun i j => hasDerivAt_entry q k i j t

/-- The differentiated Cramer identity
`k·adj q + q·(adj)' = Tr(adj q·k)·1`. -/
lemma cramer_derivative_identity
    (q k : Matrix (Fin n) (Fin n) ℝ) :
    k * adjugate q + q * adjDeriv q k
      = Matrix.trace (adjugate q * k)
        • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext a b
  have hL : HasDerivAt
      (fun t : ℝ => ((q + t • k) * adjugate (q + t • k)) a b)
      ((k * adjugate q + q * adjDeriv q k) a b) 0 := by
    have hexp : (fun t : ℝ =>
        ((q + t • k) * adjugate (q + t • k)) a b)
        = fun t => ∑ c, (q + t • k) a c
            * adjugate (q + t • k) c b := by
      funext t
      rw [Matrix.mul_apply]
    rw [hexp]
    have hsum : HasDerivAt (fun t : ℝ => ∑ c, (q + t • k) a c
        * adjugate (q + t • k) c b)
        (∑ c, (k a c * adjugate q c b
          + q a c * adjDeriv q k c b)) 0 := by
      refine HasDerivAt.fun_sum fun c _ => ?_
      have hqe := hasDerivAt_entry q k a c 0
      have hae := hasDerivAt_adjugate_zero q k c b
      have h2 := hqe.mul hae
      have h4 : q + (0 : ℝ) • k = q := by simp
      rw [h4] at h2
      exact h2
    convert hsum using 1
    simp only [Matrix.add_apply, Matrix.mul_apply,
      Finset.sum_add_distrib]
  have hR : HasDerivAt
      (fun t : ℝ => ((q + t • k) * adjugate (q + t • k)) a b)
      ((Matrix.trace (adjugate q * k)
        • (1 : Matrix (Fin n) (Fin n) ℝ)) a b) 0 := by
    have hfun : (fun t : ℝ =>
        ((q + t • k) * adjugate (q + t • k)) a b)
        = fun t => (q + t • k).det
            * (1 : Matrix (Fin n) (Fin n) ℝ) a b := by
      funext t
      rw [Matrix.mul_adjugate]
      simp [Matrix.smul_apply]
    rw [hfun]
    have hdet := (hasDerivAt_det_line q k 0).mul_const
      ((1 : Matrix (Fin n) (Fin n) ℝ) a b)
    simpa [Matrix.smul_apply] using hdet
  exact hL.unique hR

/-- Closed form for the outer derivative of the mixed trace
pairing, for invertible `q`. -/
lemma trace_adjDeriv_mul (q k h : Matrix (Fin n) (Fin n) ℝ)
    (hq : IsUnit q.det) :
    Matrix.trace (adjDeriv q k * h)
      = q.det * (Matrix.trace (q⁻¹ * k)
          * Matrix.trace (q⁻¹ * h)
        - Matrix.trace (q⁻¹ * k * (q⁻¹ * h))) := by
  have hadj : q.det • q⁻¹ = adjugate q := by
    rw [Matrix.inv_def, smul_smul,
      Ring.mul_inverse_cancel _ hq, one_smul]
  have h5 : q * adjDeriv q k
      = Matrix.trace (adjugate q * k)
        • (1 : Matrix (Fin n) (Fin n) ℝ) - k * adjugate q :=
    eq_sub_of_add_eq' (cramer_derivative_identity q k)
  have hD : adjDeriv q k
      = Matrix.trace (adjugate q * k) • q⁻¹
        - q⁻¹ * (k * adjugate q) := by
    calc adjDeriv q k = q⁻¹ * (q * adjDeriv q k) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul q hq,
            Matrix.one_mul]
      _ = q⁻¹ * (Matrix.trace (adjugate q * k)
            • (1 : Matrix (Fin n) (Fin n) ℝ) - k * adjugate q)
          := by rw [h5]
      _ = Matrix.trace (adjugate q * k) • q⁻¹
            - q⁻¹ * (k * adjugate q) := by
          rw [Matrix.mul_sub, mul_smul_comm, Matrix.mul_one]
  rw [hD, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul, ← hadj]
  rw [show (q.det • q⁻¹) * k = q.det • (q⁻¹ * k) from
      Matrix.smul_mul _ _ _,
    Matrix.trace_smul, smul_eq_mul]
  rw [show q⁻¹ * (k * (q.det • q⁻¹)) * h
      = q.det • (q⁻¹ * k * (q⁻¹ * h)) from by
    rw [mul_smul_comm, mul_smul_comm, Matrix.smul_mul]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc],
    Matrix.trace_smul, smul_eq_mul]
  ring

/-- `thm:spectral-source-Ward-master`, boxed Hessian identity:
`D²det(q)[h,k] = det q(Tr(q⁻¹h)Tr(q⁻¹k) - Tr(q⁻¹h·q⁻¹k))` as a
genuine iterated derivative. -/
theorem hessian_det (q h k : Matrix (Fin n) (Fin n) ℝ)
    (hq : IsUnit q.det) :
    deriv (fun t : ℝ =>
      deriv (fun s : ℝ => (q + s • h + t • k).det) 0) 0
      = q.det * (Matrix.trace (q⁻¹ * h)
          * Matrix.trace (q⁻¹ * k)
        - Matrix.trace (q⁻¹ * h * (q⁻¹ * k))) := by
  have hinner : ∀ t : ℝ,
      deriv (fun s : ℝ => (q + s • h + t • k).det) 0
      = Matrix.trace (adjugate (q + t • k) * h) := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (q + s • h + t • k).det)
        (Matrix.trace (adjugate (q + t • k) * h)) 0 := by
      have h2 := hasDerivAt_det_line (q + t • k) h 0
      have h3 : (fun s : ℝ => (q + t • k + s • h).det)
          = fun s => (q + s • h + t • k).det := by
        funext s
        congr 1
        abel
      rw [h3] at h2
      simpa using h2
    exact h1.deriv
  rw [funext hinner]
  have h4 : HasDerivAt
      (fun t : ℝ => Matrix.trace (adjugate (q + t • k) * h))
      (Matrix.trace (adjDeriv q k * h)) 0 := by
    have hexp : (fun t : ℝ =>
        Matrix.trace (adjugate (q + t • k) * h))
        = fun t => ∑ i, ∑ j,
            adjugate (q + t • k) i j * h j i := by
      funext t
      rw [Matrix.trace]
      simp only [Matrix.diag_apply, Matrix.mul_apply]
    have hval : Matrix.trace (adjDeriv q k * h)
        = ∑ i, ∑ j, adjDeriv q k i j * h j i := by
      rw [Matrix.trace]
      simp only [Matrix.diag_apply, Matrix.mul_apply]
    rw [hexp, hval]
    refine HasDerivAt.fun_sum fun i _ => ?_
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact (hasDerivAt_adjugate_zero q k i j).mul_const (h j i)
  rw [h4.deriv, trace_adjDeriv_mul q k h hq]
  rw [show Matrix.trace (q⁻¹ * h * (q⁻¹ * k))
      = Matrix.trace (q⁻¹ * k * (q⁻¹ * h)) from
    Matrix.trace_mul_comm (q⁻¹ * h) (q⁻¹ * k)]
  ring

/-- `thm:spectral-source-Ward-master`, boxed determinant
response: `ℛ_F(q) = c_F·det q/det q₀` with
`c_F = ⟨e₀,Fe₀⟩ ≥ 0`. -/
theorem ward_scalar_response {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e0 : H) (F : H →ₗ[ℝ] H)
    (hF : ∀ x, 0 ≤ (inner ℝ x (F x) : ℝ))
    (dq dq0 : ℝ) (hdq : 0 ≤ dq / dq0) :
    (inner ℝ (Real.sqrt (dq / dq0) • e0)
        (F (Real.sqrt (dq / dq0) • e0)) : ℝ)
      = dq / dq0 * (inner ℝ e0 (F e0) : ℝ)
    ∧ 0 ≤ (inner ℝ e0 (F e0) : ℝ) := by
  constructor
  · rw [map_smul, real_inner_smul_left, real_inner_smul_right,
      ← mul_assoc, Real.mul_self_sqrt hdq]
  · exact hF e0

/-- Boxed trace decomposition of the Ward form:
`𝔅(X,X) = Tr(X₀²) - 6x²` for `X = X₀ + xI`, `x = Tr X/3`. -/
theorem ward_trace_decomposition
    (X : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (X * X) - Matrix.trace X ^ 2
      = Matrix.trace
          ((X - (Matrix.trace X / 3) • 1)
            * (X - (Matrix.trace X / 3) • 1))
        - 6 * (Matrix.trace X / 3) ^ 2 := by
  have h1 : Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℝ) = 3 := by
    simp [Matrix.trace_one]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.one_mul, Matrix.mul_one, h1, smul_eq_mul]
  ring

/-- The Ward form is positive on nonzero symmetric traceless
directions (the five positive directions). -/
theorem ward_traceless_pos (X : Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : Xᵀ = X) (h0 : Matrix.trace X = 0) (hX : X ≠ 0) :
    0 < Matrix.trace (X * X) - Matrix.trace X ^ 2 := by
  have h1 : Matrix.trace (X * X) = ∑ i, ∑ j, X i j ^ 2 := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sq]
    congr 1
    rw [show X j i = Xᵀ i j from rfl, hsym]
  have h2 : ∃ i j, X i j ≠ 0 := by
    by_contra hcon
    refine hX ?_
    ext i j
    by_contra hij
    exact hcon ⟨i, j, hij⟩
  obtain ⟨i0, j0, hij⟩ := h2
  have h3 : (0 : ℝ) < ∑ j, X i0 j ^ 2 := by
    refine Finset.sum_pos' (fun j _ => sq_nonneg _)
      ⟨j0, Finset.mem_univ _, by positivity⟩
  have h4 : (0 : ℝ) < ∑ i, ∑ j, X i j ^ 2 := by
    calc (0 : ℝ) < ∑ j, X i0 j ^ 2 := h3
      _ ≤ ∑ i, ∑ j, X i j ^ 2 :=
        Finset.single_le_sum
          (f := fun i => ∑ j, X i j ^ 2)
          (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
          (Finset.mem_univ i0)
  rw [h0, h1]
  simpa using h4

/-- The Ward form is negative on the nonzero scalar line (the
one negative trace direction). -/
theorem ward_scalar_neg (c : ℝ) (hc : c ≠ 0) :
    Matrix.trace ((c • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        * (c • (1 : Matrix (Fin 3) (Fin 3) ℝ)))
      - Matrix.trace (c • (1 : Matrix (Fin 3) (Fin 3) ℝ)) ^ 2
      < 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  push_cast
  nlinarith [sq_pos_of_ne_zero hc]

/-- Boxed cotangent inverse, left identity: `P ↦ P - ½Tr(P)·1`
inverts `X ↦ X - Tr(X)·1`. -/
theorem ward_inverse_left (X : Matrix (Fin 3) (Fin 3) ℝ) :
    (X - Matrix.trace X • 1)
        - (1 / 2 * Matrix.trace (X - Matrix.trace X • 1)) • 1
      = X := by
  have h1 : Matrix.trace (X - Matrix.trace X • 1)
      = -2 * Matrix.trace X := by
    rw [Matrix.trace_sub, Matrix.trace_smul,
      show Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℝ) = 3 from
        by simp [Matrix.trace_one]]
    simp only [smul_eq_mul]
    ring
  rw [h1]
  rw [show (1 / 2 * (-2 * Matrix.trace X)) = -Matrix.trace X
    from by ring]
  rw [neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- Boxed cotangent inverse, right identity. -/
theorem ward_inverse_right (P : Matrix (Fin 3) (Fin 3) ℝ) :
    (P - (1 / 2 * Matrix.trace P) • 1)
        - Matrix.trace (P - (1 / 2 * Matrix.trace P) • 1) • 1
      = P := by
  have h1 : Matrix.trace (P - (1 / 2 * Matrix.trace P) • 1)
      = -(1 / 2) * Matrix.trace P := by
    rw [Matrix.trace_sub, Matrix.trace_smul,
      show Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℝ) = 3 from
        by simp [Matrix.trace_one]]
    simp only [smul_eq_mul]
    ring
  rw [h1]
  have h2 : (-(1 / 2) * Matrix.trace P) • (1 : Matrix (Fin 3)
      (Fin 3) ℝ) = -((1 / 2 * Matrix.trace P) • 1) := by
    rw [← neg_smul]
    congr 1
    ring
  rw [h2, sub_neg_eq_add]
  abel

end NCG
