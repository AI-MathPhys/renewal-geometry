/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DeterminantWindingExact
import NCG.Grand.TraceExpDerivative

/-!
# Same-operator chiral Berezin shell

Finite-dimensional determinant-line and response identities for
`thm:SMFS-same-operator-shell` (FS.13--FS.16).
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace NCG
namespace SameOperatorChiralBerezinShell

attribute [local instance 10000]
  Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Square complex matrices with the operator norm used for differentiation. -/
abbrev CMatrix (n : Type) := Matrix n n ℂ

/-- Matrix differentiation in the submultiplicative operator norm.  This
wrapper prevents Lean from silently choosing the incompatible product norm
on complex matrix entries. -/
def HasMatrixDerivAt (f : ℝ → CMatrix n) (f' : CMatrix n) (t : ℝ) : Prop :=
  let G := Matrix.linftyOpNormedAddCommGroup
    (m := n) (n := n) (α := ℂ)
  let S := Matrix.linftyOpNormedSpace
    (R := ℝ) (m := n) (n := n) (α := ℂ)
  @HasDerivAt ℝ _ (CMatrix n)
    G.toAddCommGroup S.toModule
    G.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (by
      letI : NormedAddCommGroup (CMatrix n) := G
      letI : NormedSpace ℝ (CMatrix n) := S
      infer_instance)
    f f' t

/-- Coordinate representative of the top-exterior-power Berezin section. -/
def berezinSection (D : Matrix n n ℂ) : ℂ := D.det

/-- The Hermitian determinant-line metric of the Berezin section. -/
def sectionMetric (D : Matrix n n ℂ) : ℝ :=
  ((Dᴴ * D).det).re

/-- The determinant of the Gram operator is the squared determinant norm. -/
theorem sectionMetric_eq_normSq (D : Matrix n n ℂ) :
    sectionMetric D = Complex.normSq (berezinSection D) := by
  simp [sectionMetric, berezinSection, Matrix.det_mul,
    Complex.normSq_apply, Complex.mul_re]

/-- FS.14: the induced determinant-line metric is the squared modulus of
the determinant and is strictly positive on the invertible chart. -/
theorem sectionMetric_eq_normSq_and_pos (D : Matrix n n ℂ)
    (hD : D.det ≠ 0) :
    sectionMetric D = Complex.normSq (berezinSection D) ∧
      0 < sectionMetric D := by
  have hmetric := sectionMetric_eq_normSq D
  refine ⟨hmetric, ?_⟩
  rw [hmetric]
  exact Complex.normSq_pos.mpr hD

/-- FS.15: first Jacobi response of the determinant-line metric. -/
theorem hasDerivAt_log_sectionMetric
    (D : ℝ → Matrix n n ℂ) (D' : Matrix n n ℂ) (t : ℝ)
    (hD : ∀ i j, HasDerivAt (fun s => D s i j) (D' i j) t)
    (hdet : (D t).det ≠ 0) :
    HasDerivAt (fun s => Real.log (sectionMetric (D s)))
      (2 * (Matrix.trace ((D t)⁻¹ * D')).re) t := by
  let z : ℝ → ℂ := fun s => (D s).det
  let T : ℂ := Matrix.trace ((D t)⁻¹ * D')
  have hz : HasDerivAt z (z t * T) t := by
    simpa [z, T] using
      DeterminantWinding.hasDerivAt_det_of_det_ne_zero hD hdet
  have hre : HasDerivAt (fun s => (z s).re) (z t * T).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz
  have him : HasDerivAt (fun s => (z s).im) (z t * T).im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
  have hnormSq : HasDerivAt (fun s => Complex.normSq (z s))
      (2 * Complex.normSq (z t) * T.re) t := by
    have hraw := (hre.fun_mul hre).fun_add (him.fun_mul him)
    have hfun :
        (fun s => (z s).re * (z s).re + (z s).im * (z s).im)
          = fun s => Complex.normSq (z s) := by
      funext s
      rw [Complex.normSq_apply]
    rw [hfun] at hraw
    refine hraw.congr_deriv ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    ring
  have hnz : Complex.normSq (z t) ≠ 0 := by
    simp [z, hdet]
  have hlog :
      HasDerivAt (fun s => Real.log (Complex.normSq (z s)))
        ((2 * Complex.normSq (z t) * T.re) /
          Complex.normSq (z t)) t :=
    hnormSq.log hnz
  have hvalue :
      (2 * Complex.normSq (z t) * T.re) /
          Complex.normSq (z t) = 2 * T.re := by
    field_simp
  rw [hvalue] at hlog
  have hfun :
      (fun s => Real.log (sectionMetric (D s)))
        = fun s => Real.log (Complex.normSq (z s)) := by
    funext s
    rw [sectionMetric_eq_normSq]
    rfl
  rw [hfun]
  simpa [T] using hlog

/-- The derivative of the nonsingular matrix inverse along a real parameter. -/
theorem hasDerivAt_matrixInv
    (D : ℝ → CMatrix n) (D' : CMatrix n) (t : ℝ)
    (hD : HasMatrixDerivAt D D' t) (hdet : (D t).det ≠ 0) :
    HasMatrixDerivAt (fun s => (D s)⁻¹)
      (-((D t)⁻¹ * D' * (D t)⁻¹)) t := by
  unfold HasMatrixDerivAt at hD ⊢
  have hdetUnit : IsUnit (D t).det := isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit (D t) :=
    (Matrix.isUnit_iff_isUnit_det (D t)).mpr hdetUnit
  obtain ⟨u, hu⟩ := hunit
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hinv
  have h := hinv.comp_hasDerivAt t hD
  simp only [Function.comp_def, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] at h
  have hval : (↑u⁻¹ : CMatrix n) = Ring.inverse (D t) := by
    rw [← hu, Ring.inverse_unit]
  rw [hval] at h
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using h

/-- FS.16: differentiating the first Jacobi response gives the mixed
second response, including the derivative of the inverse. -/
theorem hasDerivAt_firstResponse
    [Nonempty n]
    (D Ds : ℝ → CMatrix n)
    (Dt Dst : CMatrix n) (t : ℝ)
    (hDt : HasMatrixDerivAt D Dt t)
    (hDst : HasMatrixDerivAt Ds Dst t)
    (hdet : (D t).det ≠ 0) :
    HasDerivAt
      (fun u => 2 * (Matrix.trace ((D u)⁻¹ * Ds u)).re)
      (2 * (Matrix.trace
        ((D t)⁻¹ * Dst
          - (D t)⁻¹ * Dt * (D t)⁻¹ * Ds t)).re) t := by
  unfold HasMatrixDerivAt at hDt hDst
  have hinv := hasDerivAt_matrixInv D Dt t hDt hdet
  unfold HasMatrixDerivAt at hinv
  have hprod := hinv.mul hDst
  let L : CMatrix n →L[ℝ] ℂ :=
    (TraceExp.traceMulCLM (1 : CMatrix n)).restrictScalars ℝ
  have htrace := L.hasFDerivAt.comp_hasDerivAt t hprod
  have htrace' : HasDerivAt
      (fun u => Matrix.trace ((D u)⁻¹ * Ds u))
      (Matrix.trace
        (-((D t)⁻¹ * Dt * (D t)⁻¹) * Ds t
          + (D t)⁻¹ * Dst)) t := by
    change HasDerivAt
      (fun u => Matrix.trace (((D u)⁻¹ * Ds u) * 1))
      (Matrix.trace
        ((-((D t)⁻¹ * Dt * (D t)⁻¹) * Ds t
          + (D t)⁻¹ * Dst) * 1)) t at htrace
    simpa using htrace
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t htrace'
  have htwo := hre.const_mul 2
  simp only [Function.comp_apply] at htwo
  refine htwo.congr_deriv ?_
  congr 1
  apply congrArg Complex.re
  apply congrArg Matrix.trace
  noncomm_ring

/-! ### Explicit finite-screen response bounds -/

/-- A basis-independent finite matrix estimate may be fed by any uniform
entry bound; on a compact coefficient chart these constants are attained. -/
def EntryBound (A : CMatrix n) (C : ℝ) : Prop :=
  ∀ i j, ‖A i j‖ ≤ C

/-- Literal smallest-singular-value floor, expressed by its variational
characterization. -/
def HasSingularFloor (D : CMatrix n) (τ : ℝ) : Prop :=
  ∀ x : n → ℂ, τ * ‖x‖ ≤ ‖D *ᵥ x‖

/-- A positive singular floor makes the chiral block invertible. -/
theorem det_ne_zero_of_singularFloor
    (D : CMatrix n) (τ : ℝ) (hτ : 0 < τ)
    (hfloor : HasSingularFloor D τ) :
    D.det ≠ 0 := by
  have hinj : Function.Injective D.mulVec := by
    intro x y hxy
    have h := hfloor (x - y)
    have hzero : D *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    rw [hzero, norm_zero] at h
    have hnorm : ‖x - y‖ = 0 := by
      have hn := norm_nonneg (x - y)
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hunit : IsUnit D :=
    Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact ((Matrix.isUnit_iff_isUnit_det D).mp hunit).ne_zero

/-- The variational singular floor gives the entrywise inverse bound
`|(D⁻¹)ᵢⱼ| ≤ τ⁻¹`, so it feeds the explicit response estimates below. -/
theorem inverse_entryBound_of_singularFloor [Nonempty n]
    (D : CMatrix n) (τ : ℝ) (hτ : 0 < τ)
    (hfloor : HasSingularFloor D τ) :
    EntryBound D⁻¹ τ⁻¹ := by
  have hdet := det_ne_zero_of_singularFloor D τ hτ hfloor
  have hdetUnit : IsUnit D.det := isUnit_iff_ne_zero.mpr hdet
  have hmul : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hdetUnit
  intro i j
  let e : n → ℂ := Pi.single j 1
  let x : n → ℂ := D⁻¹ *ᵥ e
  have hDx : D *ᵥ x = e := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  have hbound := hfloor x
  rw [hDx] at hbound
  have heNorm : ‖e‖ = 1 := by
    simp [e, Pi.norm_single]
  rw [heNorm] at hbound
  have hx : ‖x‖ ≤ τ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hτ).2
    simpa [mul_comm] using hbound
  have hcoord : ‖(D⁻¹) i j‖ ≤ ‖x‖ := by
    have hi := norm_le_pi_norm x i
    simpa [x, e, Matrix.mulVec_single_one] using hi
  exact hcoord.trans hx

/-- FS.12--FS.14 in one certificate: a positive chiral singular floor
produces a nowhere-zero Berezin section, its positive determinant-line
metric, and the inverse control used by FS.15--FS.16. -/
theorem singularFloor_shell [Nonempty n]
    (D : CMatrix n) (τ : ℝ) (hτ : 0 < τ)
    (hfloor : HasSingularFloor D τ) :
    D.det ≠ 0
      ∧ sectionMetric D = Complex.normSq (berezinSection D)
      ∧ 0 < sectionMetric D
      ∧ EntryBound D⁻¹ τ⁻¹ := by
  have hdet := det_ne_zero_of_singularFloor D τ hτ hfloor
  have hmetric := sectionMetric_eq_normSq_and_pos D hdet
  exact ⟨hdet, hmetric.1, hmetric.2,
    inverse_entryBound_of_singularFloor D τ hτ hfloor⟩

omit [DecidableEq n] in
theorem entryBound_mul [Nonempty n]
    (A B : CMatrix n) (a b : ℝ)
    (ha : 0 ≤ a)
    (hA : EntryBound A a) (hB : EntryBound B b) :
    EntryBound (A * B) ((Fintype.card n : ℝ) * a * b) := by
  intro i k
  rw [Matrix.mul_apply]
  calc
    ‖∑ j, A i j * B j k‖ ≤ ∑ j, ‖A i j * B j k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : n, a * b := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (hA i j) (hB j k) (norm_nonneg _) ha
    _ = (Fintype.card n : ℝ) * a * b := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring

omit [DecidableEq n] in
theorem norm_trace_le_of_entryBound [Nonempty n]
    (A : CMatrix n) (a : ℝ) (hA : EntryBound A a) :
    ‖A.trace‖ ≤ (Fintype.card n : ℝ) * a := by
  rw [Matrix.trace]
  calc
    ‖∑ i, A i i‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, a :=
      Finset.sum_le_sum fun i _ => hA i i
    _ = (Fintype.card n : ℝ) * a := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- FS.15 finite-screen estimate.  With
`q = τ_*⁻¹`, this is the claimed inverse-floor control. -/
theorem firstResponse_abs_le [Nonempty n]
    (D Ds : CMatrix n) (q Ms : ℝ)
    (hq : 0 ≤ q)
    (hInv : EntryBound D⁻¹ q) (hDs : EntryBound Ds Ms) :
    |2 * (Matrix.trace (D⁻¹ * Ds)).re|
      ≤ 2 * (Fintype.card n : ℝ) ^ 2 * q * Ms := by
  have hmul := entryBound_mul D⁻¹ Ds q Ms hq hInv hDs
  have htr := norm_trace_le_of_entryBound (D⁻¹ * Ds)
    ((Fintype.card n : ℝ) * q * Ms) hmul
  have hre := Complex.abs_re_le_norm (Matrix.trace (D⁻¹ * Ds))
  calc
    |2 * (Matrix.trace (D⁻¹ * Ds)).re|
        = 2 * |(Matrix.trace (D⁻¹ * Ds)).re| := by
          rw [abs_mul]
          norm_num
    _ ≤ 2 * ‖Matrix.trace (D⁻¹ * Ds)‖ :=
      mul_le_mul_of_nonneg_left hre (by norm_num)
    _ ≤ 2 * ((Fintype.card n : ℝ)
        * ((Fintype.card n : ℝ) * q * Ms)) :=
      mul_le_mul_of_nonneg_left htr (by norm_num)
    _ = 2 * (Fintype.card n : ℝ) ^ 2 * q * Ms := by ring

/-- FS.16 finite-screen estimate for the mixed response.  The first term is
linear in `τ_*⁻¹`; differentiating the inverse produces the quadratic term
in `τ_*⁻²`. -/
theorem secondResponse_abs_le [Nonempty n]
    (D Dt Ds Dst : CMatrix n) (q Mt Ms Mst : ℝ)
    (hq : 0 ≤ q) (hMt : 0 ≤ Mt)
    (hInv : EntryBound D⁻¹ q)
    (hDt : EntryBound Dt Mt) (hDs : EntryBound Ds Ms)
    (hDst : EntryBound Dst Mst) :
    |2 * (Matrix.trace
      (D⁻¹ * Dst - D⁻¹ * Dt * D⁻¹ * Ds)).re|
      ≤ 2 * ((Fintype.card n : ℝ) ^ 2 * q * Mst
        + (Fintype.card n : ℝ) ^ 4 * q ^ 2 * Mt * Ms) := by
  let N : ℝ := Fintype.card n
  have hN : 0 ≤ N := by positivity
  have hfast := entryBound_mul D⁻¹ Dst q Mst hq hInv hDst
  have hfastTr := norm_trace_le_of_entryBound (D⁻¹ * Dst)
    (N * q * Mst) hfast
  have h12 := entryBound_mul D⁻¹ Dt q Mt hq hInv hDt
  have h12nonneg : 0 ≤ N * q * Mt := by positivity
  have h123 := entryBound_mul (D⁻¹ * Dt) D⁻¹
    (N * q * Mt) q h12nonneg h12 hInv
  have h123nonneg : 0 ≤ N * (N * q * Mt) * q := by positivity
  have h1234 := entryBound_mul (D⁻¹ * Dt * D⁻¹) Ds
    (N * (N * q * Mt) * q) Ms h123nonneg h123 hDs
  have hslowTr := norm_trace_le_of_entryBound
    (D⁻¹ * Dt * D⁻¹ * Ds)
    (N * (N * (N * q * Mt) * q) * Ms) h1234
  have htrace :
      ‖Matrix.trace (D⁻¹ * Dst - D⁻¹ * Dt * D⁻¹ * Ds)‖
        ≤ N ^ 2 * q * Mst + N ^ 4 * q ^ 2 * Mt * Ms := by
    rw [Matrix.trace_sub]
    calc
      ‖Matrix.trace (D⁻¹ * Dst)
          - Matrix.trace (D⁻¹ * Dt * D⁻¹ * Ds)‖
          ≤ ‖Matrix.trace (D⁻¹ * Dst)‖
            + ‖Matrix.trace (D⁻¹ * Dt * D⁻¹ * Ds)‖ :=
        norm_sub_le _ _
      _ ≤ N * (N * q * Mst)
          + N * (N * (N * (N * q * Mt) * q) * Ms) :=
        add_le_add hfastTr hslowTr
      _ = N ^ 2 * q * Mst + N ^ 4 * q ^ 2 * Mt * Ms := by ring
  have hre := Complex.abs_re_le_norm
    (Matrix.trace (D⁻¹ * Dst - D⁻¹ * Dt * D⁻¹ * Ds))
  calc
    |2 * (Matrix.trace
        (D⁻¹ * Dst - D⁻¹ * Dt * D⁻¹ * Ds)).re|
        = 2 * |(Matrix.trace
          (D⁻¹ * Dst - D⁻¹ * Dt * D⁻¹ * Ds)).re| := by
            rw [abs_mul]
            norm_num
    _ ≤ 2 * ‖Matrix.trace
        (D⁻¹ * Dst - D⁻¹ * Dt * D⁻¹ * Ds)‖ :=
      mul_le_mul_of_nonneg_left hre (by norm_num)
    _ ≤ 2 * (N ^ 2 * q * Mst + N ^ 4 * q ^ 2 * Mt * Ms) :=
      mul_le_mul_of_nonneg_left htrace (by norm_num)
    _ = 2 * ((Fintype.card n : ℝ) ^ 2 * q * Mst
        + (Fintype.card n : ℝ) ^ 4 * q ^ 2 * Mt * Ms) := by rfl

end SameOperatorChiralBerezinShell
end NCG
