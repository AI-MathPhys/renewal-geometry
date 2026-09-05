/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Worked-channel slice invariants and the isotropic Wilson ray
  (`lem:gv-three`, `lem:slice-closed`, `thm:one-param`, GR_emergence)

* `gv_three_collapse` — the three-dimensional Gray–Vanhecke collapse:
  with `|Riem⁽³⁾|² = 4|Ric⁽³⁾|² - R₍₃₎²` (vanishing Weyl in `n = 3`)
  the `r⁴` numerator `-3|Riem|² + 8|Ric|² + 5R²` collapses to
  `8R₍₃₎² - 4|Ric⁽³⁾|²`, with prefactor `1/(360·5·7) = 1/12600`;
* `slice_projection_invariant` — the projection identity
  `tr((hTh)²) = tr(T²) - 2·u(T²)u + (uTu)²` for `h = 1 - uuᵀ`,
  `|u| = 1`, proved as exact matrix algebra;
* `slice_closed_form` — the boxed frame-resolved response
  `Ψ(u) = 8R² - 32R·R_uu + 28R_uu² - 4Ric² + 8W₁ - 4W₂ + 8(R²)_uu`;
* `isotropic_four_contraction` — the Isserlis contraction
  `K⁽⁴⁾_{ijkl}A_{ij}B_{kl} = Q(tr A·tr B + 2⟨A,B⟩)` for the unique
  isotropic four-tensor — the single-scale linearity behind the
  one-parameter Wilson ray of `thm:one-param`;
* `single_scale_ray` — standardization by `D²` keeps the triple on
  the fixed ray with scale `Q/D²`.

The Gray–Vanhecke expansion itself and the Gauss-equation
identification of the slice curvatures are the declared inputs.
-/

namespace NCG

/-- `lem:gv-three`: the three-dimensional Gray–Vanhecke collapse
`-3|Riem|² + 8|Ric|² + 5R² = 8R² - 4|Ric|²` (mod `ΔR`), with
prefactor `360·5·7 = 12600`. -/
theorem gv_three_collapse {Riem2 Ric2 R2 num : ℝ}
    (h3d : Riem2 = 4 * Ric2 - R2)
    (hnum : num = -3 * Riem2 + 8 * Ric2 + 5 * R2) :
    num = 8 * R2 - 4 * Ric2 ∧ (360 : ℕ) * 5 * 7 = 12600 := by
  constructor
  · rw [hnum, h3d]
    ring
  · norm_num

section Projection

variable {n : ℕ}

/-- `lem:slice-closed` (projection identity): for the slice projector
`h = 1 - uuᵀ` with `|u| = 1`,
`tr((hTh)²) = tr(T²) - 2·u(T²)u + (uTu)²` — exact matrix algebra, no
symmetry of `T` required. -/
theorem slice_projection_invariant (u : Fin n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hu : (∑ k, u k * u k) = 1) :
    Matrix.trace ((1 - Matrix.vecMulVec u u) * T
        * (1 - Matrix.vecMulVec u u)
      * ((1 - Matrix.vecMulVec u u) * T
        * (1 - Matrix.vecMulVec u u)))
      = Matrix.trace (T * T)
        - 2 * (∑ i, u i * (T * T).mulVec u i)
        + (∑ i, u i * T.mulVec u i) ^ 2 := by
  classical
  set P : Matrix (Fin n) (Fin n) ℝ := Matrix.vecMulVec u u with hP
  -- generic vecMulVec calculus
  have hmulvv : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ),
      M * Matrix.vecMulVec a u
        = Matrix.vecMulVec (M.mulVec a) u := by
    intro M a
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply,
      Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have htrvv : ∀ a : Fin n → ℝ,
      Matrix.trace (Matrix.vecMulVec a u) = ∑ i, u i * a i := by
    intro a
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hPmulu : P.mulVec u = u := by
    funext i
    simp only [hP, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
    calc (∑ j, u i * u j * u j)
        = u i * ∑ j, u j * u j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = u i := by rw [hu, mul_one]
  have hPP : P * P = P := by
    calc P * P = Matrix.vecMulVec (P.mulVec u) u := by
          rw [hP]
          exact hmulvv P u
    _ = P := by rw [hPmulu, hP]
  have h1P : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]
    simp only [Matrix.mul_one, Matrix.one_mul]
    abel
  -- traces against the projector
  have htr : ∀ M : Matrix (Fin n) (Fin n) ℝ,
      Matrix.trace (M * P) = ∑ i, u i * M.mulVec u i := by
    intro M
    rw [hP, hmulvv M u, htrvv]
  -- the rank-one square
  have hTP2 : Matrix.trace (T * P * (T * P))
      = (∑ i, u i * T.mulVec u i) ^ 2 := by
    have hTP : T * P = Matrix.vecMulVec (T.mulVec u) u := by
      rw [hP]
      exact hmulvv T u
    have hsq : T * P * (T * P)
        = (∑ i, u i * T.mulVec u i) • (T * P) := by
      rw [hTP]
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply,
        Matrix.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsq, Matrix.trace_smul, hTP, htrvv, smul_eq_mul]
    ring
  -- collapse the idempotent sandwich
  have hAA : (1 - P) * T * (1 - P) * ((1 - P) * T * (1 - P))
      = (1 - P) * (T * ((1 - P) * (T * (1 - P)))) := by
    have hmid : (1 - P) * ((1 - P) * (T * (1 - P)))
        = (1 - P) * (T * (1 - P)) := by
      rw [← Matrix.mul_assoc, h1P]
    simp only [Matrix.mul_assoc]
    rw [hmid]
  have hcyc : Matrix.trace
      ((1 - P) * (T * ((1 - P) * (T * (1 - P)))))
      = Matrix.trace (T * ((1 - P) * (T * (1 - P)))) := by
    rw [Matrix.trace_mul_comm]
    have h2 : T * ((1 - P) * (T * (1 - P))) * (1 - P)
        = T * ((1 - P) * (T * (1 - P))) := by
      simp only [Matrix.mul_assoc]
      rw [show (1 - P) * ((1 - P) : Matrix (Fin n) (Fin n) ℝ)
        = 1 - P from h1P]
    rw [h2]
  -- expand the remaining product
  have hexpand : T * ((1 - P) * (T * (1 - P)))
      = T * T - T * (T * P) - T * (P * T) + T * (P * (T * P)) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul]
    abel
  rw [hAA, hcyc, hexpand]
  simp only [Matrix.trace_add, Matrix.trace_sub]
  have e1 : Matrix.trace (T * (T * P))
      = ∑ i, u i * (T * T).mulVec u i := by
    rw [← Matrix.mul_assoc, htr]
  have e2 : Matrix.trace (T * (P * T))
      = ∑ i, u i * (T * T).mulVec u i := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, htr]
  have e3 : Matrix.trace (T * (P * (T * P)))
      = (∑ i, u i * T.mulVec u i) ^ 2 := by
    rw [show T * (P * (T * P)) = T * P * (T * P) from by
      simp only [Matrix.mul_assoc], hTP2]
  rw [e1, e2, e3]
  ring

end Projection

/-- `lem:slice-closed` (boxed closed form): substituting the
projection decomposition `|Ric⁽³⁾|² = |T|² - 2|Tu|² + (uTu)²` with
`|T|² = Ric² - 2W₁ + W₂`, `uTu = R_uu`, `|Tu|² = (R²)_uu` into
`Ψ = 8(R - 2R_uu)² - 4|Ric⁽³⁾|²` gives the frame-resolved response. -/
theorem slice_closed_form
    {R Ruu Ric2 W1 W2 R2uu T2 Tu2 Psi Ric3sq : ℝ}
    (hRic3 : Ric3sq = T2 - 2 * Tu2 + Ruu ^ 2)
    (hT2 : T2 = Ric2 - 2 * W1 + W2)
    (hTu2 : Tu2 = R2uu)
    (hPsi : Psi = 8 * (R - 2 * Ruu) ^ 2 - 4 * Ric3sq) :
    Psi = 8 * R ^ 2 - 32 * R * Ruu + 28 * Ruu ^ 2 - 4 * Ric2
      + 8 * W1 - 4 * W2 + 8 * R2uu := by
  rw [hPsi, hRic3, hT2, hTu2]
  ring

/-- `thm:one-param` (single-scale mechanism): the unique isotropic
four-tensor `K⁽⁴⁾_{ijkl} = Q(δ_{ij}δ_{kl} + δ_{ik}δ_{jl} +
δ_{il}δ_{jk})` contracts a pair of matrices to
`Q(tr A·tr B + 2⟨A, B⟩)` — one overall scale `Q`, so the
quadratic-curvature response of any channel in the isotropic class
lies on a fixed ray. -/
theorem isotropic_four_contraction {d : ℕ} (Q : ℝ)
    (A B : Matrix (Fin d) (Fin d) ℝ) (hB : ∀ i j, B i j = B j i) :
    (∑ i, ∑ j, (if i = j then (1 : ℝ) else 0)
        * ∑ k, ∑ l, (if k = l then (1 : ℝ) else 0)
          * (Q * A i j * B k l))
      + (∑ i, ∑ j, ∑ k, (if i = k then (1 : ℝ) else 0)
          * ∑ l, (if j = l then (1 : ℝ) else 0) * (Q * A i j * B k l))
      + (∑ i, ∑ j, ∑ k, (if j = k then (1 : ℝ) else 0)
          * ∑ l, (if i = l then (1 : ℝ) else 0) * (Q * A i j * B k l))
      = Q * (Matrix.trace A * Matrix.trace B
          + 2 * ∑ i, ∑ j, A i j * B i j) := by
  classical
  have hcol : ∀ (g : Fin d → ℝ) (a : Fin d),
      (∑ x, (if a = x then (1 : ℝ) else 0) * g x) = g a := by
    intro g a
    simp [ite_mul, Finset.sum_ite_eq]
  have h1 : (∑ i, ∑ j, (if i = j then (1 : ℝ) else 0)
        * ∑ k, ∑ l, (if k = l then (1 : ℝ) else 0)
          * (Q * A i j * B k l))
      = Q * (Matrix.trace A * Matrix.trace B) := by
    calc (∑ i, ∑ j, (if i = j then (1 : ℝ) else 0)
          * ∑ k, ∑ l, (if k = l then (1 : ℝ) else 0)
            * (Q * A i j * B k l))
        = ∑ i, ∑ j, (if i = j then (1 : ℝ) else 0)
            * ∑ k, Q * A i j * B k k := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          exact hcol (fun l => Q * A i j * B k l) k
    _ = ∑ i, ∑ k, Q * A i i * B k k := by
          apply Finset.sum_congr rfl
          intro i _
          exact hcol (fun j => ∑ k, Q * A i j * B k k) i
    _ = Q * (Matrix.trace A * Matrix.trace B) := by
          simp only [Matrix.trace, Matrix.diag]
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
  have h2 : (∑ i, ∑ j, ∑ k, (if i = k then (1 : ℝ) else 0)
        * ∑ l, (if j = l then (1 : ℝ) else 0) * (Q * A i j * B k l))
      = Q * ∑ i, ∑ j, A i j * B i j := by
    calc (∑ i, ∑ j, ∑ k, (if i = k then (1 : ℝ) else 0)
          * ∑ l, (if j = l then (1 : ℝ) else 0) * (Q * A i j * B k l))
        = ∑ i, ∑ j, ∑ k, (if i = k then (1 : ℝ) else 0)
            * (Q * A i j * B k j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          congr 1
          exact hcol (fun l => Q * A i j * B k l) j
    _ = ∑ i, ∑ j, Q * A i j * B i j := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hcol (fun k => Q * A i j * B k j) i
    _ = Q * ∑ i, ∑ j, A i j * B i j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
  have h3 : (∑ i, ∑ j, ∑ k, (if j = k then (1 : ℝ) else 0)
        * ∑ l, (if i = l then (1 : ℝ) else 0) * (Q * A i j * B k l))
      = Q * ∑ i, ∑ j, A i j * B i j := by
    calc (∑ i, ∑ j, ∑ k, (if j = k then (1 : ℝ) else 0)
          * ∑ l, (if i = l then (1 : ℝ) else 0) * (Q * A i j * B k l))
        = ∑ i, ∑ j, ∑ k, (if j = k then (1 : ℝ) else 0)
            * (Q * A i j * B k i) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          congr 1
          exact hcol (fun l => Q * A i j * B k l) i
    _ = ∑ i, ∑ j, Q * A i j * B j i := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hcol (fun k => Q * A i j * B k i) j
    _ = Q * ∑ i, ∑ j, A i j * B i j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [hB j i]
          ring
  rw [h1, h2, h3]
  ring

/-- `thm:one-param` (standardization): dividing the single-scale
response by the covariance normalization `D²` keeps the triple on the
fixed ray with scale `Q/D²`. -/
theorem single_scale_ray (Q D : ℝ) (Psi1 : Fin 3 → ℝ) :
    (fun i => Q * Psi1 i / D ^ 2)
      = fun i => Q / D ^ 2 * Psi1 i := by
  funext i
  ring

end NCG
