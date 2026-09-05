/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.TraceExpDerivative

/-!
# Complete classical–quantum cut-memory short
  (`thm:renewal-memory-cumulant`)

A resolved finite cut-memory coordinate carries the faithful
classical–quantum state `ρ_cq = ⊕_ω p_ω ρ_ω` with linear face
perturbation `K_cq(z) = ⊕_ω K_ω(z)`.  Writing `ρ_ω = exp(H_ω)`
(faithfulness) and evaluating the perturbation along the plane
`z = t·x + u·y`, the complete memory log-partition is

  `M_cq(t,u) = log ∑_ω p_ω Tr exp(H_ω + t Kx_ω + u Ky_ω)
                 − (t x̄ + u ȳ)`.

This file proves, exactly:

* `memoryLogPartition_zero`: `M_cq(0) = 0`;
* `memory_first_deriv_t/u`: `DM_cq(0) = 0`;
* `memory_hessian` (**the boxed identity**):
  `D²M_cq(0)[x,y] = ∑_ω p_ω (m_ω(x)−x̄)(m_ω(y)−ȳ)
     + ∑_ω p_ω ∫₀¹ Tr(ρ_ω^s K̃_ω(x) ρ_ω^{1−s} K̃_ω(y)) ds`,
  with `ρ^s = exp(sH)` and `K̃ = K − m·1` the centered
  perturbation, via the Duhamel/BKM machinery of
  `NCG.Grand.TraceExpDerivative`;
* `classical_summand_nonneg` / `bkmIntegral_self_nonneg`
  (Kubo–Mori positivity): both summands are nonnegative;
* `classical_summand_eq_zero_iff` /
  `bkmIntegral_self_eq_zero_iff` / `quantum_branch_vanish_iff`:
  they vanish exactly when all branch mean slopes agree and
  every quantum perturbation is scalar on its (full) support;
* `shortedScore` / `shortedScore_def`:
  `A_sh = A_coarse − M_cq` subtracts the complete memory
  log-partition, not only its quadratic Taylor coefficient.
-/

open Matrix NCG.TraceExp
open scoped Matrix.Norms.Operator

namespace NCG
namespace RenewalMemory

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
variable {Ω : Type} [Fintype Ω]

/-! ### Derivative helpers -/

/-- Real part of a complex-valued derivative. -/
theorem hasDerivAt_re {f : ℝ → ℂ} {w : ℂ} {t : ℝ}
    (hf : HasDerivAt f w t) :
    HasDerivAt (fun s => (f s).re) w.re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf

/-- Termwise derivative of a finite sum, in lambda form. -/
theorem hasDerivAt_finset_sum {ι : Type} {s : Finset ι}
    {f : ι → ℝ → ℝ} {f' : ι → ℝ} {x : ℝ}
    (h : ∀ i ∈ s, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun t => ∑ i ∈ s, f i t)
      (∑ i ∈ s, f' i) x := by
  have h0 := HasDerivAt.sum h
  have hfun : (∑ i ∈ s, f i) = fun t => ∑ i ∈ s, f i t := by
    funext t
    simp [Finset.sum_apply]
  rw [hfun] at h0
  exact h0

omit [Fintype n] [DecidableEq n] [Nonempty n] in
/-- A real multiple of a Hermitian matrix is Hermitian. -/
theorem smul_real_hermitian {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (t : ℝ) : (t • A).IsHermitian := by
  have h : (t • A)ᴴ = t • A := by
    rw [Matrix.conjTranspose_smul, star_trivial, hA.eq]
  exact h

omit [Fintype n] [DecidableEq n] [Nonempty n] in
/-- The perturbed generator stays Hermitian along the plane. -/
theorem hermitian_path {A B C : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (t u : ℝ) :
    (A + t • B + u • C).IsHermitian :=
  (hA.add (smul_real_hermitian hB t)).add
    (smul_real_hermitian hC u)

omit [Nonempty n] in
/-- The trace of a Hermitian exponential is the real sum of
eigenvalue exponentials. -/
theorem traceExp_real (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    (NormedSpace.exp A).trace
      = ((∑ i : n, Real.exp (hA.eigenvalues i) : ℝ) : ℂ) := by
  have h := exp_smul_hermitian A hA 1
  rw [one_smul] at h
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    eigenvectorUnitary_conjTranspose_mul A hA,
    Matrix.one_mul, Matrix.trace_diagonal]
  push_cast
  simp [one_mul]

/-- The trace of a Hermitian exponential is strictly
positive. -/
theorem traceExp_re_pos (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    0 < ((NormedSpace.exp A).trace).re := by
  rw [traceExp_real A hA, Complex.ofReal_re]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _)
    Finset.univ_nonempty

/-! ### The complete memory log-partition -/

variable (p : Ω → ℝ) (H Kx Ky : Ω → Matrix n n ℂ)

/-- The mixture partition function
`G(t,u) = ∑_ω p_ω Tr exp(H_ω + t Kx_ω + u Ky_ω)`. -/
noncomputable def mixturePartition (t u : ℝ) : ℝ :=
  ∑ ω : Ω, p ω * ((NormedSpace.exp
    (H ω + t • Kx ω + u • Ky ω)).trace).re

/-- The mixture mean slope `∑_ω p_ω Tr(ρ_ω K_ω)`. -/
noncomputable def meanBar (K : Ω → Matrix n n ℂ) : ℝ :=
  ∑ ω : Ω, p ω * ((NormedSpace.exp (H ω) * K ω).trace).re

/-- **The complete memory log-partition** along the plane
`z = t·x + u·y`:
`M_cq(t,u) = log G(t,u) − (t x̄ + u ȳ)`. -/
noncomputable def memoryLogPartition (t u : ℝ) : ℝ :=
  Real.log (mixturePartition p H Kx Ky t u)
    - (t * meanBar p H Kx + u * meanBar p H Ky)

/-- The centered face perturbation `K̃ = K − Tr(ρK)·1`. -/
noncomputable def centered (K : Ω → Matrix n n ℂ) (ω : Ω) :
    Matrix n n ℂ :=
  K ω - ((NormedSpace.exp (H ω) * K ω).trace)
    • (1 : Matrix n n ℂ)

/-- The Duhamel/BKM integral
`∫₀¹ Tr(e^{sA} P e^{(1−s)A} Q) ds`. -/
noncomputable def bkmIntegral (A P Q : Matrix n n ℂ) : ℂ :=
  ∫ s in (0:ℝ)..1, (NormedSpace.exp (s • A) * P
    * (NormedSpace.exp ((1 - s) • A) * Q)).trace

omit [Nonempty n] in
/-- Normalization of the mixture partition at the origin. -/
theorem mixturePartition_zero
    (hsum : ∑ ω : Ω, p ω = 1)
    (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    mixturePartition p H Kx Ky 0 0 = 1 := by
  unfold mixturePartition
  have hω : ∀ ω : Ω,
      H ω + (0:ℝ) • Kx ω + (0:ℝ) • Ky ω = H ω := by
    intro ω
    rw [zero_smul, zero_smul, add_zero, add_zero]
  rw [Finset.sum_congr rfl fun ω _ => by rw [hω ω, htr ω]]
  simp only [Complex.one_re, mul_one]
  exact hsum

/-- Strict positivity of the mixture partition everywhere. -/
theorem mixturePartition_pos [Nonempty Ω]
    (hp : ∀ ω, 0 < p ω)
    (hH : ∀ ω, (H ω).IsHermitian)
    (hKx : ∀ ω, (Kx ω).IsHermitian)
    (hKy : ∀ ω, (Ky ω).IsHermitian) (t u : ℝ) :
    0 < mixturePartition p H Kx Ky t u :=
  Finset.sum_pos (fun ω _ => mul_pos (hp ω)
    (traceExp_re_pos _
      (hermitian_path (hH ω) (hKx ω) (hKy ω) t u)))
    Finset.univ_nonempty

omit [Nonempty n] in
/-- **Normalization**: `M_cq(0) = 0`. -/
theorem memoryLogPartition_zero
    (hsum : ∑ ω : Ω, p ω = 1)
    (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    memoryLogPartition p H Kx Ky 0 0 = 0 := by
  unfold memoryLogPartition
  rw [mixturePartition_zero p H Kx Ky hsum htr,
    Real.log_one]
  ring

/-- Derivative of the mixture partition in the first slot. -/
theorem hasDerivAt_mixture_t (u : ℝ) :
    HasDerivAt (fun t => mixturePartition p H Kx Ky t u)
      (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω + u • Ky ω)
        * Kx ω).trace).re) 0 := by
  refine hasDerivAt_finset_sum fun ω _ => ?_
  have h1 := hasDerivAt_traceExp (H ω + u • Ky ω) (Kx ω)
  have h2 : (fun t : ℝ => (NormedSpace.exp
      (H ω + u • Ky ω + t • Kx ω)).trace)
      = fun t : ℝ => (NormedSpace.exp
        (H ω + t • Kx ω + u • Ky ω)).trace := by
    funext t
    rw [add_right_comm]
  rw [h2] at h1
  exact (hasDerivAt_re h1).const_mul (p ω)

/-- Derivative of the mixture partition in the second slot at
the origin. -/
theorem hasDerivAt_mixture_u :
    HasDerivAt (fun u => mixturePartition p H Kx Ky 0 u)
      (meanBar p H Ky) 0 := by
  refine hasDerivAt_finset_sum fun ω _ => ?_
  have h1 := hasDerivAt_traceExp (H ω) (Ky ω)
  have h2 : (fun u : ℝ => (NormedSpace.exp
      (H ω + u • Ky ω)).trace)
      = fun u : ℝ => (NormedSpace.exp
        (H ω + (0:ℝ) • Kx ω + u • Ky ω)).trace := by
    funext u
    rw [zero_smul, add_zero]
  rw [h2] at h1
  exact (hasDerivAt_re h1).const_mul (p ω)

/-- **First derivative vanishes** (`x`-direction):
`∂_t M_cq(0,0) = 0`. -/
theorem memory_first_deriv_t
    (hsum : ∑ ω : Ω, p ω = 1)
    (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    HasDerivAt (fun t => memoryLogPartition p H Kx Ky t 0)
      0 0 := by
  have hG := hasDerivAt_mixture_t p H Kx Ky 0
  have hd : (∑ ω : Ω, p ω * ((NormedSpace.exp
      (H ω + (0:ℝ) • Ky ω) * Kx ω).trace).re)
      = meanBar p H Kx := by
    unfold meanBar
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [zero_smul, add_zero]
  rw [hd] at hG
  have hG0 : mixturePartition p H Kx Ky 0 0 = 1 :=
    mixturePartition_zero p H Kx Ky hsum htr
  have hlog := hG.log (by rw [hG0]; exact one_ne_zero)
  rw [hG0, div_one] at hlog
  have hlin : HasDerivAt (fun t : ℝ =>
      t * meanBar p H Kx + 0 * meanBar p H Ky)
      (meanBar p H Kx) 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).mul_const
      (meanBar p H Kx)).add_const (0 * meanBar p H Ky)
    rw [one_mul] at h
    exact h
  have h := hlog.sub hlin
  rw [sub_self] at h
  exact h

/-- **First derivative vanishes** (`y`-direction):
`∂_u M_cq(0,0) = 0`. -/
theorem memory_first_deriv_u
    (hsum : ∑ ω : Ω, p ω = 1)
    (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    HasDerivAt (fun u => memoryLogPartition p H Kx Ky 0 u)
      0 0 := by
  have hG := hasDerivAt_mixture_u p H Kx Ky
  have hG0 : mixturePartition p H Kx Ky 0 0 = 1 :=
    mixturePartition_zero p H Kx Ky hsum htr
  have hlog := hG.log (by rw [hG0]; exact one_ne_zero)
  rw [hG0, div_one] at hlog
  have hlin : HasDerivAt (fun u : ℝ =>
      0 * meanBar p H Kx + u * meanBar p H Ky)
      (meanBar p H Ky) 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).mul_const
      (meanBar p H Ky)).const_add (0 * meanBar p H Kx)
    rw [one_mul] at h
    exact h
  have h := hlog.sub hlin
  rw [sub_self] at h
  exact h

/-! ### Hermitian realness and exponential merging -/

omit [Nonempty n] in
/-- The exponential of a Hermitian matrix is Hermitian. -/
theorem exp_hermitian (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    (NormedSpace.exp A).IsHermitian := by
  have h := exp_smul_hermitian A hA 1
  rw [one_smul] at h
  have hD : (Matrix.diagonal (fun i =>
      Complex.exp ((1 * hA.eigenvalues i : ℝ) : ℂ)))ᴴ
      = Matrix.diagonal (fun i =>
          Complex.exp ((1 * hA.eigenvalues i : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    rw [Pi.star_apply, ← Complex.ofReal_exp]
    exact Complex.conj_ofReal _
  have hgoal : (NormedSpace.exp A)ᴴ = NormedSpace.exp A := by
    rw [h]
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hD]
    simp only [Matrix.mul_assoc]
  exact hgoal

omit [DecidableEq n] [Nonempty n] in
/-- The trace of a product of Hermitian matrices is real. -/
theorem trace_mul_hermitian_real {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((A * B).trace).im = 0 := by
  have h1 : ((A * B)ᴴ).trace = (A * B).trace := by
    rw [Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  have h2 : ((A * B)ᴴ).trace = star ((A * B).trace) :=
    Matrix.trace_conjTranspose _
  have h3 : star ((A * B).trace) = (A * B).trace := by
    rw [← h2, h1]
  exact Complex.conj_eq_iff_im.mp h3

omit [Nonempty n] in
/-- Exponential merge `e^{sA} e^{(1−s)A} = e^A`. -/
theorem exp_smul_merge (A : Matrix n n ℂ) (s : ℝ) :
    NormedSpace.exp (s • A) * NormedSpace.exp ((1 - s) • A)
      = NormedSpace.exp A := by
  have hcomm : Commute (s • A) ((1 - s) • A) :=
    ((Commute.refl A).smul_left s).smul_right (1 - s)
  have h1 : NormedSpace.exp (s • A)
      * NormedSpace.exp ((1 - s) • A)
      = NormedSpace.exp (s • A + (1 - s) • A) :=
    (NormedSpace.exp_add_of_commute hcomm).symm
  rw [h1, ← add_smul,
    show s + (1 - s) = (1:ℝ) from by ring, one_smul]

omit [Nonempty n] in
/-- Exponential merge `e^{(1−s)A} e^{sA} = e^A`. -/
theorem exp_smul_merge' (A : Matrix n n ℂ) (s : ℝ) :
    NormedSpace.exp ((1 - s) • A) * NormedSpace.exp (s • A)
      = NormedSpace.exp A := by
  have hcomm : Commute ((1 - s) • A) (s • A) :=
    ((Commute.refl A).smul_left (1 - s)).smul_right s
  have h1 : NormedSpace.exp ((1 - s) • A)
      * NormedSpace.exp (s • A)
      = NormedSpace.exp ((1 - s) • A + s • A) :=
    (NormedSpace.exp_add_of_commute hcomm).symm
  rw [h1, ← add_smul,
    show 1 - s + s = (1:ℝ) from by ring, one_smul]

/-! ### Centering the BKM integrand -/

omit [Nonempty n] in
/-- Pointwise centering: subtracting the means from both
perturbations shifts the Duhamel integrand by `−m_P m_Q`. -/
theorem bkm_centering_pointwise (A P Q : Matrix n n ℂ)
    (htr : (NormedSpace.exp A).trace = 1) (s : ℝ) :
    (NormedSpace.exp (s • A)
      * (P - ((NormedSpace.exp A * P).trace)
          • (1 : Matrix n n ℂ))
      * (NormedSpace.exp ((1 - s) • A)
        * (Q - ((NormedSpace.exp A * Q).trace)
            • (1 : Matrix n n ℂ)))).trace
    = (NormedSpace.exp (s • A) * P
        * (NormedSpace.exp ((1 - s) • A) * Q)).trace
      - (NormedSpace.exp A * P).trace
        * (NormedSpace.exp A * Q).trace := by
  set E1 := NormedSpace.exp (s • A) with hE1
  set E2 := NormedSpace.exp ((1 - s) • A) with hE2
  set mP := (NormedSpace.exp A * P).trace with hmP
  set mQ := (NormedSpace.exp A * Q).trace with hmQ
  have hmerge : E1 * E2 = NormedSpace.exp A :=
    exp_smul_merge A s
  have hmerge' : E2 * E1 = NormedSpace.exp A :=
    exp_smul_merge' A s
  have hv1 : (E1 * P * E2).trace = mP := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hmerge']
  have hv2 : (E1 * (E2 * Q)).trace = mQ := by
    rw [← Matrix.mul_assoc, hmerge]
  have hv3 : (E1 * E2).trace = (1 : ℂ) := by
    rw [hmerge, htr]
  simp only [Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  rw [hv1, hv2, hv3]
  ring

omit [Nonempty n] in
/-- Integral-level centering:
`∫ Tr(e^{sA} K̃_P e^{(1−s)A} K̃_Q) = ∫ Tr(e^{sA} P e^{(1−s)A} Q)
  − m_P m_Q`. -/
theorem bkm_centering (A P Q : Matrix n n ℂ)
    (htr : (NormedSpace.exp A).trace = 1) :
    bkmIntegral A
      (P - ((NormedSpace.exp A * P).trace)
        • (1 : Matrix n n ℂ))
      (Q - ((NormedSpace.exp A * Q).trace)
        • (1 : Matrix n n ℂ))
    = bkmIntegral A P Q
      - (NormedSpace.exp A * P).trace
        * (NormedSpace.exp A * Q).trace := by
  unfold bkmIntegral
  rw [intervalIntegral.integral_congr
    (g := fun s : ℝ => (NormedSpace.exp (s • A) * P
      * (NormedSpace.exp ((1 - s) • A) * Q)).trace
      - (NormedSpace.exp A * P).trace
        * (NormedSpace.exp A * Q).trace)
    (fun s _ => bkm_centering_pointwise A P Q htr s)]
  have hcont : Continuous (fun s : ℝ =>
      (NormedSpace.exp (s • A) * P
        * (NormedSpace.exp ((1 - s) • A) * Q)).trace) := by
    fun_prop
  rw [intervalIntegral.integral_sub
    (hcont.intervalIntegrable 0 1) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, one_smul]

omit [Nonempty n] in
/-- Symmetry of the Duhamel integral under swapping the two
perturbations (trace cyclicity and `s ↔ 1−s`). -/
theorem bkmIntegral_comm (A P Q : Matrix n n ℂ) :
    bkmIntegral A P Q = bkmIntegral A Q P := by
  unfold bkmIntegral
  have h1 : ∀ s : ℝ,
      (NormedSpace.exp (s • A) * P
        * (NormedSpace.exp ((1 - s) • A) * Q)).trace
      = (fun σ : ℝ => (NormedSpace.exp (σ • A) * Q
          * (NormedSpace.exp ((1 - σ) • A) * P)).trace)
          (1 - s) := by
    intro s
    simp only [sub_sub_cancel]
    rw [Matrix.trace_mul_comm]
  rw [intervalIntegral.integral_congr (fun s _ => h1 s),
    intervalIntegral.integral_comp_sub_left
      (fun σ : ℝ => (NormedSpace.exp (σ • A) * Q
        * (NormedSpace.exp ((1 - σ) • A) * P)).trace) 1]
  norm_num

/-! ### The boxed Hessian identity -/

omit [Nonempty n] [Fintype Ω] in
/-- Per-branch split of the BKM series into the centered
Duhamel integral plus the product of mean slopes. -/
theorem bkm_branch_split (hH : ∀ ω, (H ω).IsHermitian)
    (hKx : ∀ ω, (Kx ω).IsHermitian)
    (hKy : ∀ ω, (Ky ω).IsHermitian)
    (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) (ω : Ω) :
    (bkmSeries (H ω) (Ky ω) (Kx ω)).re
    = (bkmIntegral (H ω) (centered H Kx ω)
        (centered H Ky ω)).re
      + ((NormedSpace.exp (H ω) * Kx ω).trace).re
        * ((NormedSpace.exp (H ω) * Ky ω).trace).re := by
  have h1 : bkmSeries (H ω) (Ky ω) (Kx ω)
      = bkmIntegral (H ω) (Ky ω) (Kx ω) :=
    bkmSeries_eq_integral (H ω) (Ky ω) (Kx ω) (hH ω)
  have h2' : bkmIntegral (H ω) (centered H Ky ω)
      (centered H Kx ω)
      = bkmIntegral (H ω) (Ky ω) (Kx ω)
        - (NormedSpace.exp (H ω) * Ky ω).trace
          * (NormedSpace.exp (H ω) * Kx ω).trace :=
    bkm_centering (H ω) (Ky ω) (Kx ω) (htr ω)
  have h3 := bkmIntegral_comm (H ω) (centered H Ky ω)
    (centered H Kx ω)
  rw [h3] at h2'
  have h4 : bkmSeries (H ω) (Ky ω) (Kx ω)
      = bkmIntegral (H ω) (centered H Kx ω)
          (centered H Ky ω)
        + (NormedSpace.exp (H ω) * Ky ω).trace
          * (NormedSpace.exp (H ω) * Kx ω).trace := by
    rw [h1, h2']
    ring
  have hix := trace_mul_hermitian_real
    (exp_hermitian (H ω) (hH ω)) (hKx ω)
  have hiy := trace_mul_hermitian_real
    (exp_hermitian (H ω) (hH ω)) (hKy ω)
  have hmul : ((NormedSpace.exp (H ω) * Ky ω).trace
      * (NormedSpace.exp (H ω) * Kx ω).trace).re
      = ((NormedSpace.exp (H ω) * Kx ω).trace).re
        * ((NormedSpace.exp (H ω) * Ky ω).trace).re := by
    rw [Complex.mul_re, hiy, hix]
    ring
  rw [h4, Complex.add_re, hmul]

omit [Nonempty n] in
/-- The mixture covariance identity. -/
theorem covariance_split (hsum : ∑ ω : Ω, p ω = 1) :
    (∑ ω : Ω, p ω
      * ((((NormedSpace.exp (H ω) * Kx ω).trace).re
          - meanBar p H Kx)
        * (((NormedSpace.exp (H ω) * Ky ω).trace).re
          - meanBar p H Ky)))
    = (∑ ω : Ω, p ω
        * (((NormedSpace.exp (H ω) * Kx ω).trace).re
          * ((NormedSpace.exp (H ω) * Ky ω).trace).re))
      - meanBar p H Kx * meanBar p H Ky := by
  have hterm : ∀ ω ∈ Finset.univ (α := Ω),
      p ω * ((((NormedSpace.exp (H ω) * Kx ω).trace).re
          - meanBar p H Kx)
        * (((NormedSpace.exp (H ω) * Ky ω).trace).re
          - meanBar p H Ky))
      = p ω * (((NormedSpace.exp (H ω) * Kx ω).trace).re
            * ((NormedSpace.exp (H ω) * Ky ω).trace).re)
        - meanBar p H Ky
            * (p ω * ((NormedSpace.exp (H ω)
                * Kx ω).trace).re)
        - meanBar p H Kx
            * (p ω * ((NormedSpace.exp (H ω)
                * Ky ω).trace).re)
        + meanBar p H Kx * meanBar p H Ky * p ω :=
    fun ω _ => by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    hsum]
  have hmx : (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω)
      * Kx ω).trace).re) = meanBar p H Kx := rfl
  have hmy : (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω)
      * Ky ω).trace).re) = meanBar p H Ky := rfl
  rw [hmx, hmy]
  ring

/-- **The boxed Hessian identity**: the mixed second
derivative of the complete memory log-partition splits into
the classical mean-slope covariance plus the branch-averaged
centered Duhamel/BKM (Kubo–Mori) form:
`D²M_cq(0)[x,y] = ∑_ω p_ω (m_ω(x)−x̄)(m_ω(y)−ȳ)
  + ∑_ω p_ω ∫₀¹ Tr(ρ_ω^s K̃_ω(x) ρ_ω^{1−s} K̃_ω(y)) ds`. -/
theorem memory_hessian [Nonempty Ω]
    (hp : ∀ ω, 0 < p ω) (hsum : ∑ ω : Ω, p ω = 1)
    (hH : ∀ ω, (H ω).IsHermitian)
    (hKx : ∀ ω, (Kx ω).IsHermitian)
    (hKy : ∀ ω, (Ky ω).IsHermitian)
    (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    deriv (fun u => deriv
      (fun t => memoryLogPartition p H Kx Ky t u) 0) 0
    = (∑ ω : Ω, p ω
        * ((((NormedSpace.exp (H ω) * Kx ω).trace).re
            - meanBar p H Kx)
          * (((NormedSpace.exp (H ω) * Ky ω).trace).re
            - meanBar p H Ky)))
      + ∑ ω : Ω, p ω * (bkmIntegral (H ω)
          (centered H Kx ω) (centered H Ky ω)).re := by
  have hGpos : ∀ u : ℝ,
      0 < mixturePartition p H Kx Ky 0 u := fun u =>
    mixturePartition_pos p H Kx Ky hp hH hKx hKy 0 u
  have hslice : ∀ u : ℝ,
      deriv (fun t => memoryLogPartition p H Kx Ky t u) 0
      = (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω + u • Ky ω)
            * Kx ω).trace).re)
          / mixturePartition p H Kx Ky 0 u
        - meanBar p H Kx := by
    intro u
    have hG := hasDerivAt_mixture_t p H Kx Ky u
    have hlog := hG.log (ne_of_gt (hGpos u))
    have hlin : HasDerivAt (fun t : ℝ =>
        t * meanBar p H Kx + u * meanBar p H Ky)
        (meanBar p H Kx) 0 := by
      have h := ((hasDerivAt_id (0:ℝ)).mul_const
        (meanBar p H Kx)).add_const (u * meanBar p H Ky)
      rw [one_mul] at h
      exact h
    exact (hlog.sub hlin).deriv
  have houter : (fun u => deriv
      (fun t => memoryLogPartition p H Kx Ky t u) 0)
      = fun u : ℝ => (∑ ω : Ω, p ω
          * ((NormedSpace.exp (H ω + u • Ky ω)
            * Kx ω).trace).re)
          / mixturePartition p H Kx Ky 0 u
        - meanBar p H Kx := funext hslice
  rw [houter]
  have hNx : HasDerivAt (fun u : ℝ => ∑ ω : Ω, p ω
      * ((NormedSpace.exp (H ω + u • Ky ω)
        * Kx ω).trace).re)
      (∑ ω : Ω, p ω
        * (bkmSeries (H ω) (Ky ω) (Kx ω)).re) (0 : ℝ) := by
    refine hasDerivAt_finset_sum fun ω _ => ?_
    exact (hasDerivAt_re (hasDerivAt_traceExpMul_zero
      (H ω) (Ky ω) (Kx ω))).const_mul (p ω)
  have hGu := hasDerivAt_mixture_u p H Kx Ky
  have hG00 : mixturePartition p H Kx Ky 0 0 = 1 :=
    mixturePartition_zero p H Kx Ky hsum htr
  have hne : mixturePartition p H Kx Ky 0 0 ≠ 0 := by
    rw [hG00]
    exact one_ne_zero
  have hNx0 : (∑ ω : Ω, p ω * ((NormedSpace.exp
      (H ω + (0:ℝ) • Ky ω) * Kx ω).trace).re)
      = meanBar p H Kx := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [zero_smul, add_zero]
  have hfull := (hNx.div hGu hne).sub_const
    (meanBar p H Kx)
  have hderiv2 : deriv (fun u : ℝ => (∑ ω : Ω, p ω
      * ((NormedSpace.exp (H ω + u • Ky ω)
        * Kx ω).trace).re)
      / mixturePartition p H Kx Ky 0 u
      - meanBar p H Kx) 0
      = ((∑ ω : Ω, p ω
          * (bkmSeries (H ω) (Ky ω) (Kx ω)).re)
            * mixturePartition p H Kx Ky 0 0
          - (∑ ω : Ω, p ω * ((NormedSpace.exp
              (H ω + (0:ℝ) • Ky ω) * Kx ω).trace).re)
            * meanBar p H Ky)
          / mixturePartition p H Kx Ky 0 0 ^ 2 :=
    hfull.deriv
  rw [hderiv2, hG00, hNx0, one_pow, div_one, mul_one]
  rw [Finset.sum_congr rfl fun ω _ =>
    congrArg (fun z => p ω * z)
      (bkm_branch_split H Kx Ky hH hKx hKy htr ω)]
  have hsplit : (∑ ω : Ω, p ω
      * ((bkmIntegral (H ω) (centered H Kx ω)
          (centered H Ky ω)).re
        + ((NormedSpace.exp (H ω) * Kx ω).trace).re
          * ((NormedSpace.exp (H ω) * Ky ω).trace).re))
      = (∑ ω : Ω, p ω * (bkmIntegral (H ω)
          (centered H Kx ω) (centered H Ky ω)).re)
        + ∑ ω : Ω, p ω
          * (((NormedSpace.exp (H ω) * Kx ω).trace).re
            * ((NormedSpace.exp (H ω) * Ky ω).trace).re) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [hsplit, covariance_split p H Kx Ky hsum]
  ring

/-! ### Kubo–Mori positivity and the vanishing clause -/

omit [DecidableEq n] [Nonempty n] in
/-- Conjugation by any matrix on both sides preserves
Hermiticity. -/
theorem conj_hermitian (U M : Matrix n n ℂ)
    (hM : M.IsHermitian) : (Uᴴ * M * U).IsHermitian := by
  have h : (Uᴴ * M * U)ᴴ = Uᴴ * M * U := by
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hM.eq,
      Matrix.mul_assoc]
  exact h

/-- The spectral Kubo–Mori kernel: eigenweighted squared
moduli of the rotated perturbation. -/
noncomputable def bkmKernel (A K : Matrix n n ℂ)
    (hA : A.IsHermitian) (s : ℝ) : ℝ :=
  ∑ i : n, ∑ k : n, Real.exp (s * hA.eigenvalues i)
    * (Real.exp ((1 - s) * hA.eigenvalues k)
      * Complex.normSq
          (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * K
            * (hA.eigenvectorUnitary : Matrix n n ℂ)) i k))

omit [Nonempty n] in
theorem bkmKernel_nonneg (A K : Matrix n n ℂ)
    (hA : A.IsHermitian) (s : ℝ) :
    0 ≤ bkmKernel A K hA s :=
  Finset.sum_nonneg fun _i _ => Finset.sum_nonneg fun _k _ =>
    mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le
        (Complex.normSq_nonneg _))

omit [Nonempty n] in
/-- Diagonal-sandwich trace of a Hermitian matrix against
itself: manifestly nonnegative real form. -/
theorem trace_diag_self (dv ev : n → ℝ) (M : Matrix n n ℂ)
    (hM : M.IsHermitian) :
    ((Matrix.diagonal fun i =>
        Complex.exp ((dv i : ℝ) : ℂ)) * M
      * ((Matrix.diagonal fun i =>
          Complex.exp ((ev i : ℝ) : ℂ)) * M)).trace
    = ((∑ i : n, ∑ k : n, Real.exp (dv i)
        * (Real.exp (ev k)
          * Complex.normSq (M i k)) : ℝ) : ℂ) := by
  rw [trace_diag_sandwich]
  push_cast
  refine Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun k _ => ?_
  have hki : M k i = starRingEnd ℂ (M i k) := by
    have h1 : starRingEnd ℂ (M k i) = M i k := by
      rw [← Complex.star_def]
      exact hM.apply i k
    rw [← h1, Complex.conj_conj]
  rw [hki, show Complex.exp ((dv i : ℝ) : ℂ) * M i k
      * (Complex.exp ((ev k : ℝ) : ℂ)
        * starRingEnd ℂ (M i k))
      = Complex.exp ((dv i : ℝ) : ℂ)
        * (Complex.exp ((ev k : ℝ) : ℂ)
          * (M i k * starRingEnd ℂ (M i k))) from by ring,
    Complex.mul_conj]

omit [Nonempty n] in
/-- The self-paired Duhamel integrand is the spectral
Kubo–Mori kernel. -/
theorem bkm_self_integrand (A K : Matrix n n ℂ)
    (hA : A.IsHermitian) (hK : K.IsHermitian) (s : ℝ) :
    (NormedSpace.exp (s • A) * K
      * (NormedSpace.exp ((1 - s) • A) * K)).trace
    = ((bkmKernel A K hA s : ℝ) : ℂ) := by
  have h1 : (NormedSpace.exp (s • A) * K
      * (NormedSpace.exp ((1 - s) • A) * K)).trace
      = ((Matrix.diagonal fun i => Complex.exp
            ((s * hA.eigenvalues i : ℝ) : ℂ))
          * ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * K
            * (hA.eigenvectorUnitary : Matrix n n ℂ))
          * ((Matrix.diagonal fun i => Complex.exp
              (((1 - s) * hA.eigenvalues i : ℝ) : ℂ))
            * ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * K
              * (hA.eigenvectorUnitary
                : Matrix n n ℂ)))).trace := by
    rw [exp_smul_hermitian A hA s,
      exp_smul_hermitian A hA (1 - s), trace_conj_sandwich]
    congr 1
    simp only [Matrix.mul_assoc]
  rw [h1]
  exact trace_diag_self _ _ _
    (conj_hermitian (hA.eigenvectorUnitary : Matrix n n ℂ)
      K hK)

omit [Nonempty n] in
/-- The self-paired Duhamel integral is the (real, manifestly
nonnegative) integrated Kubo–Mori kernel. -/
theorem bkmIntegral_self_eq (A K : Matrix n n ℂ)
    (hA : A.IsHermitian) (hK : K.IsHermitian) :
    bkmIntegral A K K
      = ((∫ s in (0:ℝ)..1, bkmKernel A K hA s : ℝ) : ℂ) := by
  unfold bkmIntegral
  rw [intervalIntegral.integral_congr
    (g := fun s : ℝ => ((bkmKernel A K hA s : ℝ) : ℂ))
    (fun s _ => bkm_self_integrand A K hA hK s),
    intervalIntegral.integral_ofReal]

omit [Nonempty n] in
/-- **Kubo–Mori positivity**: the quantum summand is
nonnegative. -/
theorem bkmIntegral_self_nonneg (A K : Matrix n n ℂ)
    (hA : A.IsHermitian) (hK : K.IsHermitian) :
    0 ≤ (bkmIntegral A K K).re := by
  rw [bkmIntegral_self_eq A K hA hK, Complex.ofReal_re]
  exact intervalIntegral.integral_nonneg zero_le_one
    (fun s _ => bkmKernel_nonneg A K hA s)

omit [Nonempty n] in
/-- **Vanishing clause (quantum)**: the self-paired Duhamel
integral vanishes iff the perturbation vanishes. -/
theorem bkmIntegral_self_eq_zero_iff (A K : Matrix n n ℂ)
    (hA : A.IsHermitian) (hK : K.IsHermitian) :
    (bkmIntegral A K K).re = 0 ↔ K = 0 := by
  constructor
  · intro h0
    rw [bkmIntegral_self_eq A K hA hK,
      Complex.ofReal_re] at h0
    set B := ∑ i : n, |hA.eigenvalues i| with hB
    set T := ∑ i : n, ∑ k : n, Complex.normSq
      (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * K
        * (hA.eigenvectorUnitary : Matrix n n ℂ)) i k)
      with hT
    have hTnn : 0 ≤ T := Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
    have hBnn : ∀ i, |hA.eigenvalues i| ≤ B := fun i =>
      Finset.single_le_sum
        (f := fun i => |hA.eigenvalues i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have hlow : ∀ s ∈ Set.Icc (0:ℝ) 1,
        Real.exp (-B) * (Real.exp (-B) * T)
          ≤ bkmKernel A K hA s := by
      intro s hs
      obtain ⟨hs0, hs1⟩ := hs
      have hexpand : Real.exp (-B) * (Real.exp (-B) * T)
          = ∑ i : n, ∑ k : n, Real.exp (-B)
            * (Real.exp (-B) * Complex.normSq
                (((hA.eigenvectorUnitary
                  : Matrix n n ℂ)ᴴ * K
                  * (hA.eigenvectorUnitary
                    : Matrix n n ℂ)) i k)) := by
        rw [hT]
        simp only [Finset.mul_sum]
      rw [hexpand]
      unfold bkmKernel
      refine Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun k _ => ?_
      have hei : Real.exp (-B)
          ≤ Real.exp (s * hA.eigenvalues i) := by
        refine Real.exp_le_exp.mpr ?_
        have h2 : |s * hA.eigenvalues i| ≤ B := by
          rw [abs_mul]
          calc |s| * |hA.eigenvalues i|
              ≤ 1 * |hA.eigenvalues i| := by
                refine mul_le_mul_of_nonneg_right ?_
                  (abs_nonneg _)
                rw [abs_of_nonneg hs0]
                exact hs1
            _ = |hA.eigenvalues i| := one_mul _
            _ ≤ B := hBnn i
        linarith [neg_abs_le (s * hA.eigenvalues i)]
      have hek : Real.exp (-B)
          ≤ Real.exp ((1 - s) * hA.eigenvalues k) := by
        refine Real.exp_le_exp.mpr ?_
        have h2 : |(1 - s) * hA.eigenvalues k| ≤ B := by
          rw [abs_mul]
          calc |1 - s| * |hA.eigenvalues k|
              ≤ 1 * |hA.eigenvalues k| := by
                refine mul_le_mul_of_nonneg_right ?_
                  (abs_nonneg _)
                rw [abs_of_nonneg (by linarith)]
                linarith
            _ = |hA.eigenvalues k| := one_mul _
            _ ≤ B := hBnn k
        linarith [neg_abs_le ((1 - s) * hA.eigenvalues k)]
      have hnn := Complex.normSq_nonneg
        ((((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * K
          * (hA.eigenvectorUnitary : Matrix n n ℂ))) i k)
      gcongr
    have hcont : Continuous (fun s : ℝ =>
        bkmKernel A K hA s) := by
      unfold bkmKernel
      fun_prop
    have hmono := intervalIntegral.integral_mono_on
      (μ := MeasureTheory.volume)
      zero_le_one intervalIntegrable_const
      (hcont.intervalIntegrable 0 1) hlow
    rw [intervalIntegral.integral_const, sub_zero,
      one_smul, h0] at hmono
    have hTle : T ≤ 0 := by
      by_contra hT'
      have hTpos : 0 < T := not_le.mp hT'
      have h1 : 0 < Real.exp (-B) * (Real.exp (-B) * T) :=
        mul_pos (Real.exp_pos _)
          (mul_pos (Real.exp_pos _) hTpos)
      linarith
    have hT0 : T = 0 := le_antisymm hTle hTnn
    have hsum0 : (∑ i : n, ∑ k : n, Complex.normSq
        (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * K
          * (hA.eigenvectorUnitary
            : Matrix n n ℂ)) i k)) = 0 := by
      rw [← hT]
      exact hT0
    have hK' : ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * K
        * (hA.eigenvectorUnitary : Matrix n n ℂ)) = 0 := by
      ext i k
      rw [Matrix.zero_apply]
      refine Complex.normSq_eq_zero.mp ?_
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun k _ =>
          Complex.normSq_nonneg _)).mp hsum0 i
        (Finset.mem_univ i)
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => Complex.normSq_nonneg _)).mp h1 k
        (Finset.mem_univ k)
    have hrec : K = (hA.eigenvectorUnitary : Matrix n n ℂ)
        * ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * K
          * (hA.eigenvectorUnitary : Matrix n n ℂ))
        * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
      have h1 : (hA.eigenvectorUnitary : Matrix n n ℂ)
          * ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * K
            * (hA.eigenvectorUnitary : Matrix n n ℂ))
          * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ
          = ((hA.eigenvectorUnitary : Matrix n n ℂ)
              * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
            * K * ((hA.eigenvectorUnitary : Matrix n n ℂ)
              * (hA.eigenvectorUnitary
                : Matrix n n ℂ)ᴴ) := by
        simp only [Matrix.mul_assoc]
      rw [h1, eigenvectorUnitary_mul_conjTranspose A hA,
        Matrix.one_mul, Matrix.mul_one]
    rw [hK', Matrix.mul_zero, Matrix.zero_mul] at hrec
    exact hrec
  · intro h0
    rw [h0]
    unfold bkmIntegral
    simp [Matrix.trace_zero]

omit [Nonempty n] [Fintype Ω] in
/-- Centered perturbations of Hermitian data are Hermitian. -/
theorem centered_hermitian (K : Ω → Matrix n n ℂ)
    (hH : ∀ ω, (H ω).IsHermitian)
    (hK : ∀ ω, (K ω).IsHermitian) (ω : Ω) :
    (centered H K ω).IsHermitian := by
  have him := trace_mul_hermitian_real
    (exp_hermitian (H ω) (hH ω)) (hK ω)
  have hstar : star ((NormedSpace.exp (H ω) * K ω).trace)
      = (NormedSpace.exp (H ω) * K ω).trace :=
    Complex.conj_eq_iff_im.mpr him
  have h : (centered H K ω)ᴴ = centered H K ω := by
    unfold centered
    rw [Matrix.conjTranspose_sub, (hK ω).eq,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      hstar]
  exact h

omit [Nonempty n] in
/-- **Positivity (classical summand)**: the branch mean-slope
variance is nonnegative. -/
theorem classical_summand_nonneg (hp : ∀ ω, 0 < p ω) :
    0 ≤ ∑ ω : Ω, p ω
      * ((((NormedSpace.exp (H ω) * Kx ω).trace).re
          - meanBar p H Kx)
        * (((NormedSpace.exp (H ω) * Kx ω).trace).re
          - meanBar p H Kx)) :=
  Finset.sum_nonneg fun ω _ =>
    mul_nonneg (hp ω).le (mul_self_nonneg _)

omit [Nonempty n] in
/-- **Vanishing clause (classical)**: the variance summand
vanishes iff all branch mean slopes agree with the mixture
mean. -/
theorem classical_summand_eq_zero_iff (hp : ∀ ω, 0 < p ω) :
    (∑ ω : Ω, p ω
      * ((((NormedSpace.exp (H ω) * Kx ω).trace).re
          - meanBar p H Kx)
        * (((NormedSpace.exp (H ω) * Kx ω).trace).re
          - meanBar p H Kx))) = 0
    ↔ ∀ ω : Ω, ((NormedSpace.exp (H ω) * Kx ω).trace).re
        = meanBar p H Kx := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun ω _ =>
    mul_nonneg (hp ω).le (mul_self_nonneg _))]
  constructor
  · intro h ω
    have h1 := h ω (Finset.mem_univ ω)
    have h2 : (((NormedSpace.exp (H ω) * Kx ω).trace).re
        - meanBar p H Kx)
        * (((NormedSpace.exp (H ω) * Kx ω).trace).re
          - meanBar p H Kx) = 0 := by
      rcases mul_eq_zero.mp h1 with h3 | h3
      · exact absurd h3 (hp ω).ne'
      · exact h3
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)
  · intro h ω _
    rw [h ω, sub_self, zero_mul, mul_zero]

omit [Nonempty n] [Fintype Ω] in
/-- **Positivity (quantum summand)**: each branch Kubo–Mori
integral is nonnegative in the diagonal direction. -/
theorem quantum_summand_nonneg
    (hH : ∀ ω, (H ω).IsHermitian)
    (hKx : ∀ ω, (Kx ω).IsHermitian) (ω : Ω) :
    0 ≤ (bkmIntegral (H ω) (centered H Kx ω)
      (centered H Kx ω)).re :=
  bkmIntegral_self_nonneg (H ω) (centered H Kx ω) (hH ω)
    (centered_hermitian H Kx hH hKx ω)

omit [Nonempty n] [Fintype Ω] in
/-- **Vanishing clause (quantum)**: a branch Kubo–Mori
summand vanishes iff that branch's perturbation is scalar on
its (full) support. -/
theorem quantum_branch_vanish_iff
    (hH : ∀ ω, (H ω).IsHermitian)
    (hKx : ∀ ω, (Kx ω).IsHermitian) (ω : Ω) :
    (bkmIntegral (H ω) (centered H Kx ω)
      (centered H Kx ω)).re = 0
    ↔ Kx ω = ((NormedSpace.exp (H ω) * Kx ω).trace)
        • (1 : Matrix n n ℂ) := by
  rw [bkmIntegral_self_eq_zero_iff (H ω)
    (centered H Kx ω) (hH ω)
    (centered_hermitian H Kx hH hKx ω)]
  unfold centered
  exact sub_eq_zero

/-! ### The fully memory-shorted face score -/

/-- **The canonical fully memory-shorted face score**
`A_sh = A_coarse − M_cq`: the subtraction removes the complete
memory log-partition, not only its quadratic Taylor
coefficient. -/
noncomputable def shortedScore (Acoarse : ℝ → ℝ → ℝ)
    (t u : ℝ) : ℝ :=
  Acoarse t u - memoryLogPartition p H Kx Ky t u

omit [Nonempty n] in
theorem shortedScore_def (Acoarse : ℝ → ℝ → ℝ) (t u : ℝ) :
    shortedScore p H Kx Ky Acoarse t u
      = Acoarse t u - memoryLogPartition p H Kx Ky t u :=
  rfl

end RenewalMemory
end NCG
