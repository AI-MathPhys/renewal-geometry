/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# `det (exp X) = exp (tr X)` and the local injectivity chart of the matrix exponential

Mathlib lists `Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)` as a TODO
(`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`).  We prove it for square matrices
over `𝕂 = ℝ` or `ℂ` (any `RCLike` field), for an arbitrary finite index type, by the ODE
argument:

* `hasDerivAt_det_of_entries`: the determinant of a curve of matrices whose entries are
  differentiable is differentiable, with the explicit Leibniz-expansion derivative
  `detDerivAt (γ t) D`;
* `detDerivAt_one`: along any curve through `1` with velocity `D`, that derivative is
  `tr D` (compared with the polynomial line `s ↦ det (1 + s D)`, whose derivative at `0` is
  `tr D` by `Matrix.derivative_det_one_add_X_smul`);
* `hasDerivAt_det_exp_smul`: `ψ(s) = det (exp (s X))` satisfies `ψ' = tr X · ψ`
  (from `exp ((t+s) X) = exp (t X) exp (s X)`), so `ψ(s) exp (-s tr X)` is constant;
* `Matrix.det_exp_eq_exp_trace`: `det (exp X) = exp (tr X)`;
  `det_exp_eq_complex_exp_trace`: the complex form with `Complex.exp`.

The local chart (`exists_injOn_exp_nhds`, `exists_injOn_exp_entry_ball`,
`exists_partialHomeomorph_exp`): the matrix exponential has strict derivative the identity at
`0`, hence restricts to a homeomorphism from an open neighbourhood of `0` onto an open
neighbourhood of `1`; in particular it is injective on an entrywise ball
`{X | ∀ i j, ‖X i j‖ < r}`.

These are the two analytic inputs named in `prop:native-determinant-split`
(Einstein–SM action closure): `χ(e^X) = e^{i ℓ_c(X)}` and the injectivity chart of the
exponential.
-/

open Matrix Polynomial

namespace RenewalGeometry

namespace MatrixDetExp

variable {𝕂 : Type*} [RCLike 𝕂] {n : Type*} [Fintype n] [DecidableEq n]

/-- The Leibniz-expansion derivative of `det` at `A` in the direction `D`:
`∑_σ sgn σ ∑_i (∏_{j ≠ i} A_{σ j, j}) D_{σ i, i}`. -/
noncomputable def detDerivAt (A D : Matrix n n 𝕂) : 𝕂 :=
  ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : 𝕂) *
    ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * D (σ i) i

/-- **Derivative of the determinant along a curve.**  If every entry of `γ` has derivative
`D a b` at `t`, then `s ↦ det (γ s)` has derivative `detDerivAt (γ t) D` at `t`. -/
theorem hasDerivAt_det_of_entries {γ : 𝕂 → Matrix n n 𝕂} {D : Matrix n n 𝕂} {t : 𝕂}
    (h : ∀ a b, HasDerivAt (fun s => γ s a b) (D a b) t) :
    HasDerivAt (fun s => (γ s).det) (detDerivAt (γ t) D) t := by
  have hfun : (fun s => (γ s).det) =
      fun s => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : 𝕂) * ∏ i, γ s (σ i) i := by
    funext s
    rw [Matrix.det_apply']
  rw [hfun]
  unfold detDerivAt
  apply HasDerivAt.fun_sum
  intro σ _
  apply HasDerivAt.const_mul
  have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s => γ s (σ i) i)
    (f' := fun i => D (σ i) i) (fun i _ => h _ _)
  simpa [smul_eq_mul] using this

/-- The polynomial line: `s ↦ det (1 + s X)` has derivative `tr X` at `0`. -/
theorem hasDerivAt_det_one_add_smul (X : Matrix n n 𝕂) :
    HasDerivAt (fun s : 𝕂 => (1 + s • X).det) (trace X) 0 := by
  set P : 𝕂[X] := det (1 + (Polynomial.X : 𝕂[X]) • X.map Polynomial.C)
  have hP : ∀ s : 𝕂, P.eval s = (1 + s • X).det := by
    intro s
    simp [P, eval_det, ← smul_eq_mul_diagonal]
  have hd := P.hasDerivAt 0
  rw [Matrix.derivative_det_one_add_X_smul] at hd
  simpa only [hP] using hd

/-- **The derivative of `det` at `1` is the trace**: `detDerivAt 1 D = tr D`. -/
theorem detDerivAt_one (D : Matrix n n 𝕂) : detDerivAt (1 : Matrix n n 𝕂) D = trace D := by
  have h1 := hasDerivAt_det_of_entries (γ := fun s : 𝕂 => 1 + s • D) (D := D) (t := 0)
    (fun a b => by
      simpa using ((hasDerivAt_id (0 : 𝕂)).mul_const (D a b)).const_add ((1 : Matrix n n 𝕂) a b))
  have h2 := hasDerivAt_det_one_add_smul D
  simpa using h1.unique h2

/-- Entries of `s ↦ exp (s X)` have derivative `(exp (t X) * X) a b`. -/
theorem hasDerivAt_exp_smul_entry (X : Matrix n n 𝕂) (t : 𝕂) (a b : n) :
    HasDerivAt (fun s : 𝕂 => NormedSpace.exp (s • X) a b)
      ((NormedSpace.exp (t • X) * X) a b) t := by
  open scoped Matrix.Norms.Operator in
  have hγ : HasDerivAt (fun s : 𝕂 => NormedSpace.exp (s • X)) (NormedSpace.exp (t • X) * X) t :=
    hasDerivAt_exp_smul_const X t
  open scoped Matrix.Norms.Operator in
  let L : Matrix n n 𝕂 →L[𝕂] 𝕂 := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap 𝕂 𝕂 a b)
  open scoped Matrix.Norms.Operator in
  exact L.hasFDerivAt.comp_hasDerivAt t hγ

/-- `exp ((t + u) X) = exp (t X) exp (u X)`. -/
theorem exp_smul_add_smul (X : Matrix n n 𝕂) (t u : 𝕂) :
    NormedSpace.exp ((t + u) • X) = NormedSpace.exp (t • X) * NormedSpace.exp (u • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left t).smul_right u)

/-- **Liouville's ODE**: `ψ(s) = det (exp (s X))` has derivative `tr X · ψ(t)` at every `t`. -/
theorem hasDerivAt_det_exp_smul (X : Matrix n n 𝕂) (t : 𝕂) :
    HasDerivAt (fun s : 𝕂 => (NormedSpace.exp (s • X)).det)
      ((NormedSpace.exp (t • X)).det * trace X) t := by
  have h0 : HasDerivAt (fun u : 𝕂 => (NormedSpace.exp (u • X)).det) (trace X) 0 := by
    have := hasDerivAt_det_of_entries (γ := fun u : 𝕂 => NormedSpace.exp (u • X))
      (D := NormedSpace.exp ((0 : 𝕂) • X) * X) (t := 0) (fun a b => hasDerivAt_exp_smul_entry X 0 a b)
    simpa [detDerivAt_one] using this
  have h1 : HasDerivAt (fun s : 𝕂 => (NormedSpace.exp ((s - t) • X)).det) (trace X) t := by
    have h0' : HasDerivAt (fun u : 𝕂 => (NormedSpace.exp (u • X)).det) (trace X) (t - t) := by
      rwa [sub_self]
    exact h0'.comp_sub_const t t
  have h2 := h1.const_mul (NormedSpace.exp (t • X)).det
  have hfun : (fun s : 𝕂 => (NormedSpace.exp (s • X)).det) =
      fun s => (NormedSpace.exp (t • X)).det * (NormedSpace.exp ((s - t) • X)).det := by
    funext s
    rw [← Matrix.det_mul, ← exp_smul_add_smul, add_sub_cancel]
  rw [hfun]
  exact h2

/-- **`det (exp X) = exp (tr X)`** for square matrices over `ℝ` or `ℂ` (the TODO of
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`). -/
theorem det_exp_eq_exp_trace (X : Matrix n n 𝕂) :
    (NormedSpace.exp X).det = NormedSpace.exp (trace X) := by
  set g : 𝕂 → 𝕂 := fun s =>
    (NormedSpace.exp (s • X)).det * NormedSpace.exp (s • (-trace X)) with hg
  have hder : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h := (hasDerivAt_det_exp_smul X s).fun_mul (hasDerivAt_exp_smul_const (-trace X) s)
    convert h using 1
    · rfl
    · ring
  have hconst := is_const_of_deriv_eq_zero (f := g) (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) 1 0
  simp only [hg, one_smul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, one_mul] at hconst
  have hinv : NormedSpace.exp (-trace X) * NormedSpace.exp (trace X) = (1 : 𝕂) := by
    rw [← NormedSpace.exp_add, neg_add_cancel, NormedSpace.exp_zero]
  calc (NormedSpace.exp X).det
      = (NormedSpace.exp X).det * (NormedSpace.exp (-trace X) * NormedSpace.exp (trace X)) := by
        rw [hinv, mul_one]
    _ = NormedSpace.exp (trace X) := by rw [← mul_assoc, hconst, one_mul]

/-- **`det (exp X) = exp (tr X)`** (complex form with `Complex.exp`). -/
theorem det_exp_eq_complex_exp_trace
    (X : Matrix n n ℂ) : (NormedSpace.exp X).det = Complex.exp (trace X) := by
  rw [det_exp_eq_exp_trace, Complex.exp_eq_exp_ℂ]

/-! ### The local injectivity chart of the matrix exponential -/

/-- **Inverse function theorem for the matrix exponential**: there is an open partial
homeomorphism of `Matrix n n 𝕂` whose underlying map is `exp` and whose source contains `0`
(so its target is an open neighbourhood of `1`, on which its inverse is a continuous
logarithm). -/
theorem exists_openPartialHomeomorph_exp :
    ∃ e : OpenPartialHomeomorph (Matrix n n 𝕂) (Matrix n n 𝕂),
      (0 : Matrix n n 𝕂) ∈ e.source ∧ (e : Matrix n n 𝕂 → Matrix n n 𝕂) = NormedSpace.exp := by
  open scoped Matrix.Norms.Operator in
  have hf : HasStrictFDerivAt (NormedSpace.exp : Matrix n n 𝕂 → Matrix n n 𝕂)
      ((ContinuousLinearEquiv.refl 𝕂 (Matrix n n 𝕂) : Matrix n n 𝕂 →L[𝕂] Matrix n n 𝕂))
      (0 : Matrix n n 𝕂) := by
    rw [ContinuousLinearEquiv.coe_refl, ← ContinuousLinearMap.one_def]
    exact hasStrictFDerivAt_exp_zero
  open scoped Matrix.Norms.Operator in
  exact ⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source, rfl⟩

/-- **Local injectivity chart**: `exp` is injective on an open neighbourhood of `0`. -/
theorem exists_injOn_exp_nhds :
    ∃ U ∈ nhds (0 : Matrix n n 𝕂), IsOpen U ∧ Set.InjOn NormedSpace.exp U := by
  obtain ⟨e, he0, hexp⟩ := exists_openPartialHomeomorph_exp (𝕂 := 𝕂) (n := n)
  refine ⟨e.source, e.open_source.mem_nhds he0, e.open_source, ?_⟩
  rw [← hexp]
  exact e.injOn

/-- **Entrywise injectivity chart**: there is `r > 0` such that `exp` is injective on the
entrywise ball `{X | ∀ i j, ‖X i j‖ < r}`. -/
theorem exists_injOn_exp_entry_ball :
    ∃ r : ℝ, 0 < r ∧ Set.InjOn NormedSpace.exp {X : Matrix n n 𝕂 | ∀ i j, ‖X i j‖ < r} := by
  obtain ⟨U, hU, -, hinj⟩ := exists_injOn_exp_nhds (𝕂 := 𝕂) (n := n)
  open scoped Matrix.Norms.Elementwise in
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r, hr, hinj.mono ?_⟩
  intro X hX
  apply hball
  open scoped Matrix.Norms.Elementwise in
  rw [Metric.mem_ball, dist_zero_right, Matrix.norm_lt_iff hr]
  exact hX

end MatrixDetExp

end RenewalGeometry
