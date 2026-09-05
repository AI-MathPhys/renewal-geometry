/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.PsdBlockSchurExact
import NCG.Grand.GrandOrder

/-!
# Easy exact records, batch 00 (Gran-Tensor manuscript)

Exact formalizations of the following manuscript records:

* `cor:GT-projective-head-telescope` — the promotion telescope (ML.10–ML.11):
  `R^{(h-1)} = G_h^head + R^{(h)}`, hence `R^{(-1)} = ∑_h G_h^head + G^irr`
  and `R^{(H)} = G^irr`, for the head residuals of one source-level
  martingale increment under a fixed contraction and nested heads.
* `cth:GT-terminal-marginals-no-novelty` — the explicit `2×2` witness
  (ML.12): both contractions give every source terminal energy `1/4`, yet
  the final terminal novelty of the second source is `0` for `𝓡∥` and
  `1/4` for `𝓡⊥`.
* `cor:GT-projective-head-pruning` — target-local pruning (ML.18c): a
  retained level set reproduces the summed positive irreducible target
  exactly when it contains every level with `G_ℓ^irr ≠ 0`; a single level
  may be removed exactly when its packet vanishes.
* `thm:GT-stage-gauge-classification` — the complete multiplicative-gauge
  classification (STG.3–STG.5) of positive factorizations of one terminal
  density, with uniqueness, the coboundary converse, and gauge removal by
  intermediate-law occurrence on the surviving support.
* `thm:GT-stage-defect-telescope` — the exact stage-defect telescope
  (STG.8), the route cocycle (STG.9), and the total-variation and bounded
  writer bounds (STG.10).
* `thm:GT-mediator-loss-Gram` — the complete mediator-loss Gram
  (PSR.6–PSR.8): decomposition, positivity, Moore–Penrose Schur bound,
  Cauchy–Schwarz, the mediated-exactness criterion `C_loss = 0`, and the
  strict-separation witness.
* `thm:GT-constraint-first-action` — the constraint-first Riesz–Thomson
  action (PSR.10–PSR.12): the `G`-orthogonal projection onto `Ker L`, the
  Riesz representation, infeasibility on `d = 0`, the unique minimum-action
  solution, the Pythagoras split, and the action ratio `d₀/d ≥ 1`.
* `cth:GT-old-block-no-short-transport` — the explicit `2×2` packet with
  exact old compression and unit diagonal floor whose variational source
  short is `δ/(1+δ) → 0` (ST.2).
* `thm:GT-source-short-cutoff-transport` — exact adjacent-cutoff source
  short transport (ST.5–ST.7): the one-step Loewner recursion, the
  telescoped comparison, and the uniform least-eigenvalue reserve under
  norm summability, together with the existence of the variational short.
* `thm:GT-Feshbach-source-debit` — the Feshbach characterization (ST.9) of
  admissible returning-memory debits, the additivity of old and returning
  debits, and the `κ⁻¹ X` high-shell bound.
* `thm:GT-exact-trace-dynamic-memory` — the canonical traced response
  (ET.15–ET.20): variational Schur form, spectral floor, exact Green
  identity, associativity of nested tracing, the reducing-subspace
  equivalences, and the dynamic-memory angle bound.

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset
open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank NCG.PsdBlockSchur
open scoped ComplexOrder

-- decidability/fintype instances enter only through the spectral support calculus in proofs
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace NCG

/-! ### Shared Hermitian-form helpers

Real-part quadratic-form calculus for Hermitian complex matrices, the
spectral square root, spectral descriptions of `M ± c•1`, eigenvalue
bounds from Loewner comparisons, and the extreme eigenvalues `hermLamMin`,
`hermLamMax`.  These serve the records ST.5–ST.7, ST.9 and ET.15–ET.20. -/

section SharedForms

variable {n : Type*} [Fintype n]

/-- A Hermitian quadratic form is its own conjugate, hence real. -/
theorem hermitian_form_ofReal {M : Matrix n n ℂ} (hM : M.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ (M *ᵥ x) = (((star x ⬝ᵥ (M *ᵥ x)).re : ℝ) : ℂ) := by
  have hconj : star (star x ⬝ᵥ (M *ᵥ x)) = star x ⬝ᵥ (M *ᵥ x) :=
    calc star (star x ⬝ᵥ (M *ᵥ x)) = star (M *ᵥ x) ⬝ᵥ x := (star_dotProduct _ _).symm
      _ = star x ⬝ᵥ (M *ᵥ x) := (dotProduct_mulVec_hermitian hM x x).symm
  have him : (star x ⬝ᵥ (M *ᵥ x)).im = 0 := by
    have := congrArg Complex.im hconj
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  exact Complex.ext (by simp) (by simp [him])

/-- A Hermitian matrix with pointwise nonnegative real quadratic form is PSD. -/
theorem posSemidef_of_re_form {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (h : ∀ x, 0 ≤ (star x ⬝ᵥ (M *ᵥ x)).re) : M.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg hM fun x => ?_
  rw [hermitian_form_ofReal hM x]
  exact_mod_cast Complex.zero_le_real.mpr (h x)

/-- The real part of a PSD quadratic form is nonnegative. -/
theorem re_form_nonneg {M : Matrix n n ℂ} (hM : M.PosSemidef) (x : n → ℂ) :
    0 ≤ (star x ⬝ᵥ (M *ᵥ x)).re := by
  have := (Complex.le_def.mp (hM.dotProduct_mulVec_nonneg x)).1
  simpa using this

/-- The real part of a positive-definite quadratic form is positive off `0`. -/
theorem re_form_pos {M : Matrix n n ℂ} (hM : M.PosDef) {x : n → ℂ} (hx : x ≠ 0) :
    0 < (star x ⬝ᵥ (M *ᵥ x)).re := by
  have := (Complex.lt_def.mp (hM.dotProduct_mulVec_pos hx)).1
  simpa using this

/-- The squared Euclidean weight `star x ⬝ᵥ x` as a real sum of squares. -/
theorem star_dot_self_eq_sum_sq (x : n → ℂ) :
    star x ⬝ᵥ x = ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

/-- Conjugate symmetry of a Hermitian sesquilinear form. -/
theorem hermitian_form_conj_symm {M : Matrix n n ℂ} (hM : M.IsHermitian) (a b : n → ℂ) :
    star a ⬝ᵥ (M *ᵥ b) = star (star b ⬝ᵥ (M *ᵥ a)) := by
  rw [dotProduct_mulVec_hermitian hM a b, star_dotProduct]

/-- Quadratic-form expansion along a form-null direction. -/
theorem form_add_of_cross_zero {M : Matrix n n ℂ} (u w : n → ℂ)
    (h1 : star u ⬝ᵥ (M *ᵥ w) = 0) (h2 : star w ⬝ᵥ (M *ᵥ u) = 0) :
    star (u + w) ⬝ᵥ (M *ᵥ (u + w)) = star u ⬝ᵥ (M *ᵥ u) + star w ⬝ᵥ (M *ᵥ w) := by
  rw [mulVec_add, star_add, add_dotProduct, dotProduct_add, dotProduct_add, h1, h2]
  ring

/-- Two Hermitian matrices with the same real quadratic form are equal
(complex polarization). -/
theorem hermitian_eq_of_re_forms {M N : Matrix n n ℂ} (hM : M.IsHermitian)
    (hN : N.IsHermitian)
    (h : ∀ x, (star x ⬝ᵥ (M *ᵥ x)).re = (star x ⬝ᵥ (N *ᵥ x)).re) : M = N := by
  have hPh : (M - N).IsHermitian := hM.sub hN
  have hP : ∀ x, star x ⬝ᵥ ((M - N) *ᵥ x) = 0 := by
    intro x
    have hre : (star x ⬝ᵥ ((M - N) *ᵥ x)).re = 0 := by
      rw [sub_mulVec, dotProduct_sub, Complex.sub_re, h x, sub_self]
    rw [hermitian_form_ofReal hPh x, hre, Complex.ofReal_zero]
  have hre2 : ∀ u v : n → ℂ, (star u ⬝ᵥ ((M - N) *ᵥ v)).re = 0 := by
    intro u v
    have h1 := hP (u + v)
    rw [mulVec_add, star_add, add_dotProduct, dotProduct_add, dotProduct_add, hP u, hP v,
      zero_add, add_zero] at h1
    rw [hermitian_form_conj_symm hPh v u] at h1
    have h2 := congrArg Complex.re h1
    rw [Complex.add_re, Complex.zero_re] at h2
    have h3 : (star (star u ⬝ᵥ ((M - N) *ᵥ v))).re = (star u ⬝ᵥ ((M - N) *ᵥ v)).re := by
      rw [Complex.star_def, Complex.conj_re]
    linarith
  have hB : ∀ u v : n → ℂ, star u ⬝ᵥ ((M - N) *ᵥ v) = 0 := by
    intro u v
    have hima := hre2 u (Complex.I • v)
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.I_mul_re] at hima
    refine Complex.ext ?_ ?_
    · rw [Complex.zero_re]
      exact hre2 u v
    · rw [Complex.zero_im]
      linarith
  have hzero : M - N = 0 := by
    rw [ext_iff_mulVec]
    intro v
    rw [zero_mulVec]
    exact dotProduct_star_self_eq_zero.mp (hB ((M - N) *ᵥ v) v)
  exact sub_eq_zero.mp hzero

/-- Transport of a quadratic form along an index equivalence. -/
theorem form_submatrix_equiv {m : Type*} [Fintype m] (M : Matrix n n ℂ) (e : m ≃ n)
    (z : m → ℂ) :
    star z ⬝ᵥ (M.submatrix e e *ᵥ z) = star (z ∘ e.symm) ⬝ᵥ (M *ᵥ (z ∘ e.symm)) := by
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [dotProduct]
  refine Fintype.sum_equiv e _ _ fun i => ?_
  simp only [Function.comp_apply, Pi.star_apply, Equiv.symm_apply_apply]

/-- Full quadratic-form expansion of a difference. -/
theorem form_sub_expand (M : Matrix n n ℂ) (u w : n → ℂ) :
    star (u - w) ⬝ᵥ (M *ᵥ (u - w))
      = star u ⬝ᵥ (M *ᵥ u) - star u ⬝ᵥ (M *ᵥ w) - star w ⬝ᵥ (M *ᵥ u)
        + star w ⬝ᵥ (M *ᵥ w) := by
  rw [mulVec_sub, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  ring

end SharedForms

section SharedSpectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Shifting a Hermitian matrix by `-c•1` is the spectral function `λ ↦ λ - c`. -/
theorem sub_smul_one_eq_spectral {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ) :
    M - (c : ℂ) • 1 = spectralFunction hM (fun l => l - c) := by
  have h := spectralFunction_sub hM id (fun _ => c)
  rw [spectralFunction_id, spectralFunction_const] at h
  exact h.symm

/-- The reflected shift `c•1 - M` is the spectral function `λ ↦ c - λ`. -/
theorem smul_one_sub_eq_spectral {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ) :
    (c : ℂ) • 1 - M = spectralFunction hM (fun l => c - l) := by
  have h := spectralFunction_sub hM (fun _ => c) id
  rw [spectralFunction_id, spectralFunction_const] at h
  exact h.symm

/-- The squared norm of an eigenvector of the orthonormal eigenbasis is one. -/
theorem star_dot_self_eigenvectorBasis {M : Matrix n n ℂ} (hM : M.IsHermitian) (i : n) :
    star ⇑(hM.eigenvectorBasis i) ⬝ᵥ ⇑(hM.eigenvectorBasis i) = ((1 : ℝ) : ℂ) := by
  have h1 : ‖hM.eigenvectorBasis i‖ = 1 := hM.eigenvectorBasis.orthonormal.1 i
  have h2 : ‖hM.eigenvectorBasis i‖ ^ 2 = 1 := by rw [h1]; norm_num
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)] at h2
  rw [star_dot_self_eq_sum_sq, h2]

/-- The Hermitian quadratic form at an eigenvector is the eigenvalue. -/
theorem form_eigenvectorBasis {M : Matrix n n ℂ} (hM : M.IsHermitian) (i : n) :
    star ⇑(hM.eigenvectorBasis i) ⬝ᵥ (M *ᵥ ⇑(hM.eigenvectorBasis i))
      = ((hM.eigenvalues i : ℝ) : ℂ) := by
  rw [hM.mulVec_eigenvectorBasis i]
  have hsmul : (hM.eigenvalues i • ⇑(hM.eigenvectorBasis i) : n → ℂ)
      = ((hM.eigenvalues i : ℝ) : ℂ) • ⇑(hM.eigenvectorBasis i) := by
    funext j
    simp [Complex.real_smul]
  rw [hsmul, dotProduct_smul, star_dot_self_eigenvectorBasis hM i, smul_eq_mul]
  norm_num

/-- A Loewner lower bound `M ⪰ c•1` bounds every eigenvalue from below. -/
theorem le_eigenvalues_of_loewner {M : Matrix n n ℂ} (hM : M.IsHermitian) {c : ℝ}
    (h : (M - (c : ℂ) • 1).PosSemidef) (i : n) : c ≤ hM.eigenvalues i := by
  have hform := re_form_nonneg h ⇑(hM.eigenvectorBasis i)
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
    form_eigenvectorBasis hM i, star_dot_self_eigenvectorBasis hM i] at hform
  simp only [smul_eq_mul, Complex.ofReal_one, mul_one, Complex.sub_re,
    Complex.ofReal_re] at hform
  linarith

/-- A Loewner upper bound `M ⪯ c•1` bounds every eigenvalue from above. -/
theorem eigenvalues_le_of_loewner {M : Matrix n n ℂ} (hM : M.IsHermitian) {c : ℝ}
    (h : ((c : ℂ) • 1 - M).PosSemidef) (i : n) : hM.eigenvalues i ≤ c := by
  have hform := re_form_nonneg h ⇑(hM.eigenvectorBasis i)
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
    form_eigenvectorBasis hM i, star_dot_self_eigenvectorBasis hM i] at hform
  simp only [smul_eq_mul, Complex.ofReal_one, mul_one, Complex.sub_re,
    Complex.ofReal_re] at hform
  linarith

/-- The least eigenvalue of a Hermitian matrix. -/
noncomputable def hermLamMin {M : Matrix n n ℂ} (hM : M.IsHermitian) : ℝ :=
  ⨅ i, hM.eigenvalues i

/-- The greatest eigenvalue of a Hermitian matrix. -/
noncomputable def hermLamMax {M : Matrix n n ℂ} (hM : M.IsHermitian) : ℝ :=
  ⨆ i, hM.eigenvalues i

/-- `hermLamMin` is below every eigenvalue. -/
theorem hermLamMin_le {M : Matrix n n ℂ} (hM : M.IsHermitian) [Nonempty n] (i : n) :
    hermLamMin hM ≤ hM.eigenvalues i :=
  ciInf_le (Set.finite_range _).bddBelow i

/-- Every eigenvalue is below `hermLamMax`. -/
theorem le_hermLamMax {M : Matrix n n ℂ} (hM : M.IsHermitian) [Nonempty n] (i : n) :
    hM.eigenvalues i ≤ hermLamMax hM :=
  le_ciSup (Set.finite_range _).bddAbove i

/-- The spectral floor `M ⪰ hermLamMin•1`. -/
theorem hermLamMin_floor {M : Matrix n n ℂ} (hM : M.IsHermitian) [Nonempty n] :
    (M - (hermLamMin hM : ℂ) • 1).PosSemidef := by
  rw [sub_smul_one_eq_spectral hM]
  exact spectralFunction_posSemidef hM _ fun i => sub_nonneg.mpr (hermLamMin_le hM i)

/-- The spectral ceiling `M ⪯ hermLamMax•1`. -/
theorem hermLamMax_ceiling {M : Matrix n n ℂ} (hM : M.IsHermitian) [Nonempty n] :
    ((hermLamMax hM : ℂ) • 1 - M).PosSemidef := by
  rw [smul_one_sub_eq_spectral hM]
  exact spectralFunction_posSemidef hM _ fun i => sub_nonneg.mpr (le_hermLamMax hM i)

/-- `hermLamMin` is the greatest Loewner floor: `M ⪰ c•1` forces `c ≤ hermLamMin`. -/
theorem le_hermLamMin_of_loewner {M : Matrix n n ℂ} (hM : M.IsHermitian) [Nonempty n] {c : ℝ}
    (h : (M - (c : ℂ) • 1).PosSemidef) : c ≤ hermLamMin hM :=
  le_ciInf (le_eigenvalues_of_loewner hM h)

/-- `hermLamMax` of a PSD matrix is nonnegative; it renders the operator norm
of a positive debit. -/
theorem hermLamMax_nonneg {M : Matrix n n ℂ} (hM : M.PosSemidef) [Nonempty n] :
    0 ≤ hermLamMax hM.1 := by
  have i := Classical.arbitrary n
  exact le_trans (hM.eigenvalues_nonneg i) (le_hermLamMax hM.1 i)

/-- The spectral square root of a Hermitian matrix. -/
noncomputable def psdSqrt {M : Matrix n n ℂ} (hM : M.IsHermitian) : Matrix n n ℂ :=
  spectralFunction hM Real.sqrt

/-- The spectral square root is PSD (hence Hermitian). -/
theorem psdSqrt_posSemidef {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (psdSqrt hM).PosSemidef :=
  spectralFunction_posSemidef hM _ fun _ => Real.sqrt_nonneg _

/-- On a PSD matrix the spectral square root squares back to the matrix. -/
theorem psdSqrt_mul_self {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    psdSqrt hM.1 * psdSqrt hM.1 = M :=
  calc psdSqrt hM.1 * psdSqrt hM.1
      = spectralFunction hM.1 (fun l => Real.sqrt l * Real.sqrt l) :=
        spectralFunction_mul hM.1 Real.sqrt Real.sqrt
    _ = spectralFunction hM.1 id :=
        spectralFunction_congr hM.1 fun i => Real.mul_self_sqrt (hM.eigenvalues_nonneg i)
    _ = M := spectralFunction_id hM.1

/-- The inverse of a positive-definite matrix is the spectral function `λ⁻¹`. -/
theorem posDef_inv_eq_spectral {M : Matrix n n ℂ} (hM : M.PosDef) :
    M⁻¹ = spectralFunction hM.1 (fun l => l⁻¹) := by
  refine inv_eq_left_inv ?_
  calc spectralFunction hM.1 (fun l => l⁻¹) * M
      = spectralFunction hM.1 (fun l => l⁻¹) * spectralFunction hM.1 id := by
        rw [spectralFunction_id]
    _ = spectralFunction hM.1 (fun l => l⁻¹ * id l) :=
        spectralFunction_mul hM.1 _ _
    _ = spectralFunction hM.1 (fun _ => 1) :=
        spectralFunction_congr hM.1 fun i =>
          inv_mul_cancel₀ (hM.1.posDef_iff_eigenvalues_pos.mp hM i).ne'
    _ = 1 := by rw [spectralFunction_const, Complex.ofReal_one, one_smul]

/-- The inverse spectral square root of a Hermitian matrix. -/
noncomputable def psdInvSqrt {M : Matrix n n ℂ} (hM : M.IsHermitian) : Matrix n n ℂ :=
  spectralFunction hM (fun l => (Real.sqrt l)⁻¹)

/-- For a positive-definite matrix, `A^{-1/2} A^{1/2} = 1`. -/
theorem psdInvSqrt_mul_psdSqrt {M : Matrix n n ℂ} (hM : M.PosDef) :
    psdInvSqrt hM.1 * psdSqrt hM.1 = 1 :=
  calc psdInvSqrt hM.1 * psdSqrt hM.1
      = spectralFunction hM.1 (fun l => (Real.sqrt l)⁻¹ * Real.sqrt l) :=
        spectralFunction_mul hM.1 _ _
    _ = spectralFunction hM.1 (fun _ => 1) :=
        spectralFunction_congr hM.1 fun i => inv_mul_cancel₀
          (Real.sqrt_ne_zero'.mpr (hM.1.posDef_iff_eigenvalues_pos.mp hM i))
    _ = 1 := by rw [spectralFunction_const, Complex.ofReal_one, one_smul]

/-- For a positive-definite matrix, `A^{1/2} A^{-1/2} = 1`. -/
theorem psdSqrt_mul_psdInvSqrt {M : Matrix n n ℂ} (hM : M.PosDef) :
    psdSqrt hM.1 * psdInvSqrt hM.1 = 1 :=
  calc psdSqrt hM.1 * psdInvSqrt hM.1
      = spectralFunction hM.1 (fun l => Real.sqrt l * (Real.sqrt l)⁻¹) :=
        spectralFunction_mul hM.1 _ _
    _ = spectralFunction hM.1 (fun _ => 1) :=
        spectralFunction_congr hM.1 fun i => mul_inv_cancel₀
          (Real.sqrt_ne_zero'.mpr (hM.1.posDef_iff_eigenvalues_pos.mp hM i))
    _ = 1 := by rw [spectralFunction_const, Complex.ofReal_one, one_smul]

/-- `M⁻¹ M = 1` for a positive-definite matrix. -/
theorem posDef_inv_mul_cancel {M : Matrix n n ℂ} (hM : M.PosDef) : M⁻¹ * M = 1 :=
  Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit)

/-- `M M⁻¹ = 1` for a positive-definite matrix. -/
theorem posDef_mul_inv_cancel {M : Matrix n n ℂ} (hM : M.PosDef) : M * M⁻¹ = 1 :=
  Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit)

end SharedSpectral

/-! ### `cor:GT-projective-head-telescope` — Promotion telescope

The corollary is stated for one fixed source level `ℓ`: `D` is the
martingale increment at that level (valued in operators `E → H_src`),
`𝓡 : H_src → 𝒴` the protocol-fixed contraction, and `Π k` the nested
represented heads on `𝒴`.  The manuscript index `h` runs over
`-1, 0, …, H`; we shift it by one, so `Π 0` renders `Π_{-1} = 0`
(hypothesis `hP0` where used) and `promoResidual … k` renders
`R_ℓ^{(k-1)}` (ML.9).  The occurring history law is rendered as a
weighted expectation over a finite event carrier, which is where a
cutoff compiler evaluates the packet; the telescope itself is exact
linear algebra in the heads and needs no property of the weights. -/

section PromotionTelescope

variable {Ω E S Y : Type*} [Fintype Ω] [Fintype S] [Fintype Y] [DecidableEq Y]

/-- Weighted finite expectation of a matrix observable over the event carrier. -/
noncomputable def promoExpect (w : Ω → ℝ) (F : Ω → Matrix E E ℂ) : Matrix E E ℂ :=
  ∑ ω, w ω • F ω

/-- The provisional head residual `R_ℓ^{(k-1)} = 𝔼[D^* 𝓡^* (I - Π_k) 𝓡 D]`
(ML.9, index shifted by one). -/
noncomputable def promoResidual (w : Ω → ℝ) (D : Ω → Matrix S E ℂ) (R : Matrix Y S ℂ)
    (P : ℕ → Matrix Y Y ℂ) (k : ℕ) : Matrix E E ℂ :=
  promoExpect w fun ω => (D ω)ᴴ * Rᴴ * (1 - P k) * R * D ω

/-- The represented-head packet `G_{ℓ,h}^head = 𝔼[D^* 𝓡^* Q_h 𝓡 D]` with
`Q_h = Π_{h+1} - Π_h` (ML.3/ML.5, index shifted by one). -/
noncomputable def promoHead (w : Ω → ℝ) (D : Ω → Matrix S E ℂ) (R : Matrix Y S ℂ)
    (P : ℕ → Matrix Y Y ℂ) (h : ℕ) : Matrix E E ℂ :=
  promoExpect w fun ω => (D ω)ᴴ * Rᴴ * (P (h + 1) - P h) * R * D ω

/-- The irreducible packet `G_ℓ^irr = 𝔼[D^* 𝓡^* (I - Π_H) 𝓡 D]` (ML.5),
with `Q_irr = I - Π_H` rendered at shifted index `H + 1`. -/
noncomputable def promoIrr (w : Ω → ℝ) (D : Ω → Matrix S E ℂ) (R : Matrix Y S ℂ)
    (P : ℕ → Matrix Y Y ℂ) (H : ℕ) : Matrix E E ℂ :=
  promoExpect w fun ω => (D ω)ᴴ * Rᴴ * (1 - P (H + 1)) * R * D ω

/-- Grounding of the index shift: when `Π_{-1} = 0` the residual at the
lowest index is the full response energy `𝔼[D^* 𝓡^* 𝓡 D]`. -/
theorem promoResidual_zero (w : Ω → ℝ) (D : Ω → Matrix S E ℂ) (R : Matrix Y S ℂ)
    (P : ℕ → Matrix Y Y ℂ) (hP0 : P 0 = 0) :
    promoResidual w D R P 0 = promoExpect w fun ω => (D ω)ᴴ * Rᴴ * R * D ω := by
  unfold promoResidual promoExpect
  refine Finset.sum_congr rfl fun ω _ => ?_
  beta_reduce
  rw [hP0, sub_zero, Matrix.mul_one]

/-- **(ML.10)** One promotion step: `R^{(h-1)} = G_h^head + R^{(h)}`. -/
theorem promo_telescope_step (w : Ω → ℝ) (D : Ω → Matrix S E ℂ) (R : Matrix Y S ℂ)
    (P : ℕ → Matrix Y Y ℂ) (h : ℕ) :
    promoResidual w D R P h = promoHead w D R P h + promoResidual w D R P (h + 1) := by
  unfold promoResidual promoHead promoExpect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  beta_reduce
  rw [← smul_add]
  congr 1
  have hsplit : (1 - P h : Matrix Y Y ℂ) = (P (h + 1) - P h) + (1 - P (h + 1)) := by abel
  rw [hsplit, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]

/-- **(ML.11, first display)** The full telescope
`R^{(-1)} = ∑_{h=0}^{H} G_h^head + G^irr`. -/
theorem promo_telescope_sum (w : Ω → ℝ) (D : Ω → Matrix S E ℂ) (R : Matrix Y S ℂ)
    (P : ℕ → Matrix Y Y ℂ) (H : ℕ) :
    promoResidual w D R P 0
      = ∑ h ∈ Finset.range (H + 1), promoHead w D R P h + promoIrr w D R P H := by
  have key : ∀ N : ℕ, promoResidual w D R P 0
      = ∑ h ∈ Finset.range N, promoHead w D R P h + promoResidual w D R P N := by
    intro N
    induction N with
    | zero => rw [Finset.range_zero, Finset.sum_empty, zero_add]
    | succ N ih =>
      rw [ih, promo_telescope_step w D R P N, Finset.sum_range_succ]
      abel
  exact key (H + 1)

/-- **(ML.11, second display)** The terminal residual is exactly the
irreducible packet: `R^{(H)} = G^irr` (with `Q_irr = I - Π_H`, this is
the defining identification, recorded for the boxed display). -/
theorem promo_residual_last (w : Ω → ℝ) (D : Ω → Matrix S E ℂ) (R : Matrix Y S ℂ)
    (P : ℕ → Matrix Y Y ℂ) (H : ℕ) :
    promoResidual w D R P (H + 1) = promoIrr w D R P H := rfl

end PromotionTelescope

/-! ### `cth:GT-terminal-marginals-no-novelty`

The explicit witness (ML.12): source levels are the coordinate vectors of
`ℝ²`; `𝓡∥` and `𝓡⊥` are the displayed matrices.  The old head is the
span of the image of the first source; for both contractions this image
spans the first coordinate axis, and `margHeadProj` is verified to be the
orthogonal projection onto it.  Terminal energies agree (`1/4` in all
four cases) while the final terminal novelty of the second source is `0`
for `𝓡∥` and `1/4` for `𝓡⊥`. -/

section MarginalNovelty

/-- The parallel contraction `𝓡∥` of (ML.12). -/
noncomputable def margRpar : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/2; 0, 0]

/-- The perpendicular contraction `𝓡⊥` of (ML.12). -/
noncomputable def margRperp : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 0; 0, 1/2]

/-- The first source level: the first coordinate vector of `ℝ²`. -/
def margSrc0 : Fin 2 → ℝ := ![1, 0]

/-- The second source level: the second coordinate vector of `ℝ²`. -/
def margSrc1 : Fin 2 → ℝ := ![0, 1]

/-- The orthogonal projection onto the old head (the span of the image of
the first source). -/
def margHeadProj : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- Terminal energy of a source under a contraction: `‖𝓡 e‖²`. -/
noncomputable def margEnergy (R : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2 → ℝ) : ℝ :=
  (R *ᵥ e) ⬝ᵥ (R *ᵥ e)

/-- Final terminal novelty of the second source relative to the old head:
`‖(I - Π) 𝓡 e₂‖²`. -/
noncomputable def margNovelty (R : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ((1 - margHeadProj) *ᵥ (R *ᵥ margSrc1)) ⬝ᵥ ((1 - margHeadProj) *ᵥ (R *ᵥ margSrc1))

/-- `margHeadProj` is symmetric and idempotent. -/
theorem margHeadProj_projection :
    margHeadProjᵀ = margHeadProj ∧ margHeadProj * margHeadProj = margHeadProj := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [margHeadProj]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [margHeadProj, Matrix.mul_apply, Fin.sum_univ_two]

/-- `margHeadProj` fixes the image of the first source under either
contraction: the old head is generated by the first source. -/
theorem margHeadProj_fixes_first :
    margHeadProj *ᵥ (margRpar *ᵥ margSrc0) = margRpar *ᵥ margSrc0 ∧
    margHeadProj *ᵥ (margRperp *ᵥ margSrc0) = margRperp *ᵥ margSrc0 := by
  constructor
  · funext i
    fin_cases i <;>
      simp [margHeadProj, margRpar, margSrc0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · funext i
    fin_cases i <;>
      simp [margHeadProj, margRperp, margSrc0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The range of `margHeadProj` lies in the span of the first source image,
and the complement is orthogonal to it: `margHeadProj` is exactly the
orthogonal projection onto the old head. -/
theorem margHeadProj_range_and_orth (v : Fin 2 → ℝ) :
    (∃ c : ℝ, margHeadProj *ᵥ v = c • (margRpar *ᵥ margSrc0)) ∧
    (v - margHeadProj *ᵥ v) ⬝ᵥ (margRpar *ᵥ margSrc0) = 0 := by
  constructor
  · refine ⟨2 * v 0, ?_⟩
    funext i
    fin_cases i
    · simp [margHeadProj, margRpar, margSrc0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [margHeadProj, margRpar, margSrc0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [margHeadProj, margRpar, margSrc0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Each individual source has terminal energy `1/4` for both contractions. -/
theorem marg_energies :
    margEnergy margRpar margSrc0 = 1/4 ∧ margEnergy margRpar margSrc1 = 1/4 ∧
    margEnergy margRperp margSrc0 = 1/4 ∧ margEnergy margRperp margSrc1 = 1/4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [margEnergy, margRpar, margRperp, margSrc0, margSrc1, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-- The final terminal novelty of the second source vanishes for `𝓡∥`. -/
theorem marg_novelty_par : margNovelty margRpar = 0 := by
  simp [margNovelty, margRpar, margHeadProj, margSrc1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]

/-- The final terminal novelty of the second source is `1/4` for `𝓡⊥`. -/
theorem marg_novelty_perp : margNovelty margRperp = 1/4 := by
  simp only [margNovelty, margRperp, margHeadProj, margSrc1]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]

/-- **`cth:GT-terminal-marginals-no-novelty`**: the two contractions give
identical separate terminal energies on both sources, yet different final
terminal novelties.  Separate source Grams and separate terminal energies
therefore do not determine the promotion packet or the final irreducible
range. -/
theorem marginal_terminals_do_not_determine_novelty :
    (margEnergy margRpar margSrc0 = margEnergy margRperp margSrc0 ∧
     margEnergy margRpar margSrc1 = margEnergy margRperp margSrc1) ∧
    margNovelty margRpar ≠ margNovelty margRperp := by
  obtain ⟨h1, h2, h3, h4⟩ := marg_energies
  refine ⟨⟨by rw [h1, h3], by rw [h2, h4]⟩, ?_⟩
  rw [marg_novelty_par, marg_novelty_perp]
  norm_num

end MarginalNovelty

/-! ### `cor:GT-projective-head-pruning`

The frozen target consumes only the final irreducible packet, i.e. the sum
of the positive blocks `G_ℓ^irr`.  We prove (ML.18c): a retained level set
reproduces the target exactly when it contains every level with
`G_ℓ^irr ≠ 0` — so the active level set is `{ℓ : G_ℓ^irr ≠ 0}` — and a
single level may be removed exactly when its packet is provably zero.
The freeze policy (analytic bounds or an independent pilot stream fixed
before the terminal population is inspected) is protocol prose and is not
a mathematical claim. -/

section PruningFreeze

variable {ι n : Type*} [Fintype ι] [Fintype n]

omit [Fintype ι] in
/-- A finite sum of PSD matrices vanishes only if each summand vanishes. -/
theorem prune_eq_zero_of_sum_eq_zero (G : ι → Matrix n n ℂ)
    (hG : ∀ i, (G i).PosSemidef) (T : Finset ι) (h : ∑ i ∈ T, G i = 0) :
    ∀ i ∈ T, G i = 0 := by
  intro i hi
  rw [ext_iff_mulVec]
  intro v
  rw [zero_mulVec]
  have hterm : star v ⬝ᵥ (G i *ᵥ v) = 0 := by
    have hsum : ∑ j ∈ T, star v ⬝ᵥ (G j *ᵥ v) = 0 := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec, h, zero_mulVec, dotProduct_zero]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      (hG j).dotProduct_mulVec_nonneg v).mp hsum i hi
  exact ((hG i).dotProduct_mulVec_zero_iff v).mp hterm

/-- **(ML.18c)** A retained level set `S` reproduces the frozen irreducible
target exactly when it contains the active level set
`𝓛_irr = {ℓ : G_ℓ^irr ≠ 0}`. -/
theorem prune_active_level_iff (G : ι → Matrix n n ℂ) (hG : ∀ i, (G i).PosSemidef)
    (S : Finset ι) :
    ∑ i ∈ S, G i = ∑ i, G i ↔ ∀ i, G i ≠ 0 → i ∈ S := by
  constructor
  · intro h i hGi
    by_contra hi
    classical
    have hsplit := Finset.sum_sdiff (f := G) (Finset.subset_univ S)
    rw [h] at hsplit
    have hz : ∑ j ∈ Finset.univ \ S, G j = 0 := by
      have h0 : ∑ j ∈ Finset.univ \ S, G j + ∑ i, G i = 0 + ∑ i, G i := by
        rw [zero_add, hsplit]
      exact add_right_cancel h0
    exact hGi (prune_eq_zero_of_sum_eq_zero G hG _ hz i
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩))
  · intro h
    refine Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_
    by_contra hGi
    exact hi (h i hGi)

/-- A single level may be removed from the target exactly when its
irreducible packet is provably zero — the exact-certificate criterion. -/
theorem prune_remove_single_iff [DecidableEq ι] (G : ι → Matrix n n ℂ)
    (hG : ∀ i, (G i).PosSemidef) (l : ι) :
    ∑ i ∈ Finset.univ.erase l, G i = ∑ i, G i ↔ G l = 0 := by
  rw [prune_active_level_iff G hG]
  constructor
  · intro h
    by_contra hl
    exact (Finset.notMem_erase l Finset.univ) (h l hl)
  · intro h i hGi
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
    rintro rfl
    exact hGi h

end PruningFreeze

/-! ### `thm:GT-stage-gauge-classification`

Positive factorizations of one terminal density on the surviving support
`S = {W > 0}`, rendered — per the finite-audit reading of the record — on
a state space `σ` carrying the support pointwise, with the base measure
`μ₀` a weight function.  Stages are 0-indexed: `a 0, …, a (r-1)` with
`A_j = ∏_{i<j} a_i` (`stageProd`), so `A_0 = 1` and `A_r = W`.  We prove
existence, the boxed formulas (STG.4), positivity and normalization
(STG.3), uniqueness, the measure transport (STG.5), the coboundary
converse, and the occurrence-based gauge removal on the surviving
support of `μ₀`. -/

section StageGauge

variable {σ : Type*}

/-- The running stage product `A_j = ∏_{i<j} a_i` (STG.2, 0-indexed). -/
def stageProd (a : ℕ → σ → ℝ) (j : ℕ) (x : σ) : ℝ := ∏ i ∈ Finset.range j, a i x

/-- The multiplicative gauge `h_j = B_j / A_j` of two factorizations (STG.4). -/
noncomputable def stageGauge (a b : ℕ → σ → ℝ) (j : ℕ) (x : σ) : ℝ :=
  stageProd b j x / stageProd a j x

/-- One-step expansion of the stage product. -/
theorem stageProd_succ (a : ℕ → σ → ℝ) (j : ℕ) (x : σ) :
    stageProd a (j + 1) x = stageProd a j x * a j x :=
  Finset.prod_range_succ _ _

/-- Positivity of the running product of positive stage factors. -/
theorem stageProd_pos {a : ℕ → σ → ℝ} {r : ℕ} (ha : ∀ i, i < r → ∀ x, 0 < a i x)
    {j : ℕ} (hj : j ≤ r) (x : σ) : 0 < stageProd a j x :=
  Finset.prod_pos fun i hi => ha i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj) x

/-- **(STG.3, ends)** The gauge is normalized at the initial stage. -/
theorem stageGauge_zero (a b : ℕ → σ → ℝ) (x : σ) : stageGauge a b 0 x = 1 := by
  simp [stageGauge, stageProd]

/-- **(STG.3, ends)** Two factorizations of the same terminal density have
gauge one at the terminal stage. -/
theorem stageGauge_last {a b : ℕ → σ → ℝ} {r : ℕ} (ha : ∀ i, i < r → ∀ x, 0 < a i x)
    (hW : ∀ x, stageProd b r x = stageProd a r x) (x : σ) :
    stageGauge a b r x = 1 := by
  unfold stageGauge
  rw [hW x]
  exact div_self (stageProd_pos ha le_rfl x).ne'

/-- **(STG.3, interior)** The gauge is strictly positive at every stage. -/
theorem stageGauge_pos {a b : ℕ → σ → ℝ} {r : ℕ} (ha : ∀ i, i < r → ∀ x, 0 < a i x)
    (hb : ∀ i, i < r → ∀ x, 0 < b i x) {j : ℕ} (hj : j ≤ r) (x : σ) :
    0 < stageGauge a b j x :=
  div_pos (stageProd_pos hb hj x) (stageProd_pos ha hj x)

/-- **(STG.4)** The gauge relation `b_j = a_j · h_{j+1} / h_j` holds for
`h_j = B_j / A_j`. -/
theorem stageGauge_step {a b : ℕ → σ → ℝ} {r : ℕ} (ha : ∀ i, i < r → ∀ x, 0 < a i x)
    (hb : ∀ i, i < r → ∀ x, 0 < b i x) {j : ℕ} (hj : j < r) (x : σ) :
    b j x = a j x * stageGauge a b (j + 1) x / stageGauge a b j x := by
  have hA : stageProd a j x ≠ 0 := (stageProd_pos ha hj.le x).ne'
  have hB : stageProd b j x ≠ 0 := (stageProd_pos hb hj.le x).ne'
  have haj : a j x ≠ 0 := (ha j hj x).ne'
  simp only [stageGauge, stageProd_succ]
  field_simp

/-- **(STG.4, uniqueness)** Any gauge list with `h_0 = 1`, nonvanishing
interior values, and the relation `b_j = a_j h_{j+1}/h_j` agrees with
`B_j / A_j` at every stage. -/
theorem stageGauge_unique {a b : ℕ → σ → ℝ} {r : ℕ} (ha : ∀ i, i < r → ∀ x, 0 < a i x)
    (hb : ∀ i, i < r → ∀ x, 0 < b i x) (h' : ℕ → σ → ℝ)
    (h'0 : ∀ x, h' 0 x = 1) (h'ne : ∀ j, j ≤ r → ∀ x, h' j x ≠ 0)
    (hrel : ∀ j, j < r → ∀ x, b j x = a j x * h' (j + 1) x / h' j x) :
    ∀ j, j ≤ r → ∀ x, h' j x = stageGauge a b j x := by
  intro j
  induction j with
  | zero =>
    intro _ x
    rw [h'0 x, stageGauge_zero]
  | succ j ih =>
    intro hj x
    have hjr : j < r := hj
    have hne : h' j x ≠ 0 := h'ne j hjr.le x
    have haj : a j x ≠ 0 := (ha j hjr x).ne'
    have hgz : stageGauge a b j x ≠ 0 := (stageGauge_pos ha hb hjr.le x).ne'
    have e1 : h' (j + 1) x = b j x * h' j x / a j x := by
      rw [hrel j hjr x]
      field_simp
    have e2 : stageGauge a b (j + 1) x = b j x * stageGauge a b j x / a j x := by
      rw [stageGauge_step ha hb hjr x]
      field_simp
    rw [e1, ih hjr.le x, ← e2]

/-- **(STG.5)** The intermediate laws transform by the gauge:
`μ_j^b = h_j · μ_j^a` against any base weight `μ₀`. -/
theorem stageGauge_measure {a b : ℕ → σ → ℝ} {r : ℕ} (ha : ∀ i, i < r → ∀ x, 0 < a i x)
    (μ0 : σ → ℝ) {j : ℕ} (hj : j ≤ r) (x : σ) :
    stageProd b j x * μ0 x = stageGauge a b j x * (stageProd a j x * μ0 x) := by
  have hA : stageProd a j x ≠ 0 := (stageProd_pos ha hj x).ne'
  simp only [stageGauge]
  field_simp

/-- **(converse)** Every list satisfying (STG.3) produces another positive
factorization of the same terminal density through (STG.4). -/
theorem stageGauge_converse {a : ℕ → σ → ℝ} {r : ℕ} (ha : ∀ i, i < r → ∀ x, 0 < a i x)
    (h : ℕ → σ → ℝ) (h0 : ∀ x, h 0 x = 1) (hr : ∀ x, h r x = 1)
    (hpos : ∀ j, 0 < j → j < r → ∀ x, 0 < h j x) :
    (∀ j, j < r → ∀ x, 0 < a j x * h (j + 1) x / h j x) ∧
    (∀ x, stageProd (fun j y => a j y * h (j + 1) y / h j y) r x = stageProd a r x) := by
  have hpos' : ∀ j, j ≤ r → ∀ x, 0 < h j x := by
    intro j hj x
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [h0 x]; norm_num
    · rcases eq_or_lt_of_le hj with rfl | hjr
      · rw [hr x]; norm_num
      · exact hpos j hj0 hjr x
  refine ⟨fun j hj x => div_pos (mul_pos (ha j hj x) (hpos' (j + 1) hj x)) (hpos' j hj.le x),
    fun x => ?_⟩
  have key : ∀ m, m ≤ r →
      stageProd (fun j y => a j y * h (j + 1) y / h j y) m x = stageProd a m x * h m x := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [stageProd, h0 x]
    | succ m ih =>
      intro hm
      have hmr : m < r := hm
      have hhm : h m x ≠ 0 := (hpos' m hmr.le x).ne'
      rw [stageProd_succ, stageProd_succ, ih hmr.le]
      field_simp
  rw [key r le_rfl, hr x, mul_one]

/-- **(occurrence removes the gauge)** If the two factorizations reproduce
the same occurring intermediate laws, the gauge is one and the stage
factors agree on the surviving support of `μ₀`. -/
theorem stageGauge_occurrence {a b : ℕ → σ → ℝ} {r : ℕ} (ha : ∀ i, i < r → ∀ x, 0 < a i x)
    (hb : ∀ i, i < r → ∀ x, 0 < b i x) (μ0 : σ → ℝ)
    (hocc : ∀ j, j ≤ r → ∀ x, stageProd b j x * μ0 x = stageProd a j x * μ0 x) :
    ∀ x, μ0 x ≠ 0 → (∀ j, j ≤ r → stageGauge a b j x = 1) ∧ ∀ j, j < r → b j x = a j x := by
  intro x hx
  have hg1 : ∀ j, j ≤ r → stageGauge a b j x = 1 := by
    intro j hj
    have hA : stageProd a j x ≠ 0 := (stageProd_pos ha hj x).ne'
    have hBA : stageProd b j x = stageProd a j x :=
      mul_right_cancel₀ hx (hocc j hj x)
    simp only [stageGauge]
    rw [hBA]
    exact div_self hA
  refine ⟨hg1, fun j hj => ?_⟩
  have hstep := stageGauge_step ha hb hj x
  rw [hg1 (j + 1) hj, hg1 j hj.le] at hstep
  simpa using hstep

end StageGauge

/-! ### `thm:GT-stage-defect-telescope`

Actual finite positive measures `μ_0, …, μ_r` and proposed nonnegative
stage densities `a_0, …, a_{r-1}` on a finite carrier (signed defects are
`ℝ`-valued weight functions; total variation is the finite Jordan sum
`∑ |·|`).  Stages are 0-indexed: the manuscript defect
`δ_j^occ = μ_j - a_j μ_{j-1}` is `stageOcc … (j-1)`.  We prove the exact
telescope (STG.8), the route cocycle (STG.9), the total-variation bound
(STG.10) under the essential bounds `‖∏_{k>j} a_k‖_∞ ≤ M j`, and the
bounded-writer consequence. -/

section StageDefect

variable {σ : Type*}

/-- Stage-occurrence defect `δ_{j+1}^occ = μ_{j+1} - a_j μ_j` (STG.6). -/
def stageOcc (a μ : ℕ → σ → ℝ) (j : ℕ) (x : σ) : ℝ :=
  μ (j + 1) x - a j x * μ j x

/-- Composite transition density `A_{j←i} = ∏_{k∈[i,j)} a_k` (STG.7). -/
def stageWindow (a : ℕ → σ → ℝ) (i j : ℕ) (x : σ) : ℝ := ∏ k ∈ Finset.Ico i j, a k x

/-- Direct route defect `δ_{j←i} = μ_j - A_{j←i} μ_i` (STG.7). -/
def stageRoute (a μ : ℕ → σ → ℝ) (i j : ℕ) (x : σ) : ℝ :=
  μ j x - stageWindow a i j x * μ i x

/-- Total variation of a signed weight on the finite carrier (finite
Jordan decomposition: `‖ν‖_TV = ∑ |ν|`). -/
def stageTV [Fintype σ] (ν : σ → ℝ) : ℝ := ∑ x, |ν x|

/-- **(STG.8)** The exact stage-defect telescope: the terminal discrepancy
is the sum of the occurrence defects propagated by the later factors. -/
theorem stage_defect_telescope (a μ : ℕ → σ → ℝ) (r : ℕ) (x : σ) :
    μ r x - (∏ j ∈ Finset.range r, a j x) * μ 0 x
      = ∑ j ∈ Finset.range r, stageWindow a (j + 1) r x * stageOcc a μ j x := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hW1 : stageWindow a (r + 1) (r + 1) x = 1 := by
      simp [stageWindow]
    have hsum : ∑ j ∈ Finset.range r, stageWindow a (j + 1) (r + 1) x * stageOcc a μ j x
        = a r x * ∑ j ∈ Finset.range r, stageWindow a (j + 1) r x * stageOcc a μ j x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j + 1 ≤ r := Finset.mem_range.mp hj
      have hsplit : stageWindow a (j + 1) (r + 1) x = stageWindow a (j + 1) r x * a r x := by
        simp only [stageWindow]
        exact Finset.prod_Ico_succ_top hj' _
      rw [hsplit]
      ring
    rw [Finset.sum_range_succ, hsum, hW1, ← ih]
    simp only [stageOcc, Finset.prod_range_succ]
    ring

/-- **(STG.9)** The route cocycle: for `i ≤ j ≤ ℓ`,
`δ_{ℓ←i} = δ_{ℓ←j} + A_{ℓ←j} δ_{j←i}`. -/
theorem stage_route_cocycle (a μ : ℕ → σ → ℝ) {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l)
    (x : σ) :
    stageRoute a μ i l x = stageRoute a μ j l x + stageWindow a j l x * stageRoute a μ i j x := by
  have hprod : stageWindow a i j x * stageWindow a j l x = stageWindow a i l x := by
    simp only [stageWindow]
    exact Finset.prod_Ico_consecutive _ hij hjl
  simp only [stageRoute]
  rw [← hprod]
  ring

/-- **(STG.10)** The total-variation bound: with the later products
essentially bounded by `M j`, the terminal discrepancy is controlled by
the weighted occurrence costs `∑ M_j ℂ_j^occ`. -/
theorem stage_defect_tv_bound [Fintype σ] (a μ : ℕ → σ → ℝ) (r : ℕ) (M : ℕ → ℝ)
    (ha : ∀ k, ∀ x : σ, 0 ≤ a k x)
    (hM : ∀ j, j < r → ∀ x : σ, stageWindow a (j + 1) r x ≤ M j) :
    stageTV (fun x => μ r x - (∏ j ∈ Finset.range r, a j x) * μ 0 x)
      ≤ ∑ j ∈ Finset.range r, M j * stageTV (fun x => stageOcc a μ j x) := by
  unfold stageTV
  calc ∑ x, |μ r x - (∏ j ∈ Finset.range r, a j x) * μ 0 x|
      = ∑ x, |∑ j ∈ Finset.range r, stageWindow a (j + 1) r x * stageOcc a μ j x| := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [stage_defect_telescope]
    _ ≤ ∑ x, ∑ j ∈ Finset.range r, |stageWindow a (j + 1) r x * stageOcc a μ j x| :=
        Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range r, ∑ x, |stageWindow a (j + 1) r x * stageOcc a μ j x| :=
        Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range r, ∑ x, M j * |stageOcc a μ j x| := by
        refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun x _ => ?_
        rw [abs_mul]
        have hw0 : 0 ≤ stageWindow a (j + 1) r x := Finset.prod_nonneg fun k _ => ha k x
        rw [abs_of_nonneg hw0]
        exact mul_le_mul_of_nonneg_right (hM j (Finset.mem_range.mp hj) x) (abs_nonneg _)
    _ = ∑ j ∈ Finset.range r, M j * ∑ x, |stageOcc a μ j x| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]

/-- **(STG.10, writer form)** The same right side multiplied by `‖f‖_∞`
bounds the error of every bounded terminal writer `f`. -/
theorem stage_writer_bound [Fintype σ] (a μ : ℕ → σ → ℝ) (r : ℕ) (M : ℕ → ℝ)
    (ha : ∀ k, ∀ x : σ, 0 ≤ a k x)
    (hM : ∀ j, j < r → ∀ x : σ, stageWindow a (j + 1) r x ≤ M j)
    (f : σ → ℝ) (F : ℝ) (hF : 0 ≤ F) (hf : ∀ x, |f x| ≤ F) :
    |∑ x, f x * (μ r x - (∏ j ∈ Finset.range r, a j x) * μ 0 x)|
      ≤ F * ∑ j ∈ Finset.range r, M j * stageTV (fun x => stageOcc a μ j x) := by
  calc |∑ x, f x * (μ r x - (∏ j ∈ Finset.range r, a j x) * μ 0 x)|
      ≤ ∑ x, |f x * (μ r x - (∏ j ∈ Finset.range r, a j x) * μ 0 x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, F * |μ r x - (∏ j ∈ Finset.range r, a j x) * μ 0 x| := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)
    _ = F * stageTV (fun x => μ r x - (∏ j ∈ Finset.range r, a j x) * μ 0 x) := by
        rw [stageTV, Finset.mul_sum]
    _ ≤ F * ∑ j ∈ Finset.range r, M j * stageTV (fun x => stageOcc a μ j x) :=
        mul_le_mul_of_nonneg_left (stage_defect_tv_bound a μ r M ha hM) hF

end StageDefect

/-! ### `cth:GT-old-block-no-short-transport`

The explicit coarse/fine packet: `A₀ = (1)`, `T₀ = 1`, and
`A_δ = [[1, 1], [1, 1+δ]]` with source analysis `T_δ(x,y) = x`.  We
verify that `A_δ` is a genuine positive-definite fine form, that its
compression to the old subspace is exactly the coarse form, that the new
diagonal entry has the unit floor, that the variational source short
(ST.1) is exactly `K_δ = δ/(1+δ)` (as an attained least value), and that
`K_δ → 0` as `δ → 0⁺` (ST.2). -/

section OldBlockShort

/-- The fine two-dimensional form `A_δ`. -/
noncomputable def oldBlockFine (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1 + δ]

/-- The quadratic form of `A_δ`. -/
noncomputable def oldBlockQuad (δ : ℝ) (u : Fin 2 → ℝ) : ℝ := u ⬝ᵥ (oldBlockFine δ *ᵥ u)

/-- Explicit expansion of the fine quadratic form. -/
theorem oldBlockQuad_eq (δ s y : ℝ) :
    oldBlockQuad δ ![s, y] = s ^ 2 + 2 * s * y + (1 + δ) * y ^ 2 := by
  simp [oldBlockQuad, oldBlockFine, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The fine form is a genuine positive-definite determining form for
`δ > 0`. -/
theorem oldBlockFine_posDef {δ : ℝ} (hδ : 0 < δ) : (oldBlockFine δ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [oldBlockFine, Matrix.conjTranspose_apply]
  · have hval : star x ⬝ᵥ (oldBlockFine δ *ᵥ x) = (x 0 + x 1) ^ 2 + δ * x 1 ^ 2 := by
      simp [oldBlockFine, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hval]
    rcases eq_or_ne (x 1) 0 with h1 | h1
    · have h0 : x 0 ≠ 0 := by
        intro h0
        apply hx
        funext i
        fin_cases i <;> simp [h0, h1]
      rw [h1]
      have hpos : 0 < x 0 ^ 2 := by positivity
      nlinarith
    · have hpos : 0 < x 1 ^ 2 := by positivity
      nlinarith [sq_nonneg (x 0 + x 1), mul_pos hδ hpos]

/-- The old compression of the fine form is exactly the coarse form
`A₀ = (1)`: on the old subspace the fine energy is `s²`. -/
theorem oldBlock_compression_exact (δ s : ℝ) : oldBlockQuad δ ![s, 0] = s * s := by
  rw [oldBlockQuad_eq]
  ring

/-- The new diagonal block has the unit floor: `(A_δ)₁₁ = 1 + δ ≥ 1`. -/
theorem oldBlock_diagonal_floor {δ : ℝ} (hδ : 0 ≤ δ) : 1 ≤ oldBlockFine δ 1 1 := by
  simp only [oldBlockFine]
  norm_num [hδ]

/-- **(ST.1/ST.2)** The variational source short of the packet is exactly
`K_δ = δ/(1+δ)`: the attained least fine energy over the fibre
`T_δ u = s` is `δ/(1+δ) · s²`. -/
theorem oldBlock_short_isLeast {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    IsLeast {e : ℝ | ∃ y : ℝ, e = oldBlockQuad δ ![s, y]} (δ / (1 + δ) * s ^ 2) := by
  have h1δ : (0 : ℝ) < 1 + δ := by linarith
  constructor
  · refine ⟨-s / (1 + δ), ?_⟩
    rw [oldBlockQuad_eq]
    field_simp
    ring
  · rintro e ⟨y, rfl⟩
    rw [oldBlockQuad_eq]
    have key : s ^ 2 + 2 * s * y + (1 + δ) * y ^ 2 - δ / (1 + δ) * s ^ 2
        = (1 + δ) * (y + s / (1 + δ)) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg h1δ.le (sq_nonneg (y + s / (1 + δ)))]

/-- **(ST.2)** The short collapses: `K_δ = δ/(1+δ) → 0` as `δ → 0⁺`. -/
theorem oldBlock_short_limit :
    Filter.Tendsto (fun δ : ℝ => δ / (1 + δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcont : ContinuousAt (fun δ : ℝ => δ / (1 + δ)) 0 := by
    refine ContinuousAt.div continuousAt_id (continuousAt_const.add continuousAt_id) ?_
    norm_num
  have htend := hcont.tendsto
  norm_num at htend
  exact htend.mono_left nhdsWithin_le_nhds

/-- **`cth:GT-old-block-no-short-transport`**: the packet has exact old
compression and a unit fine diagonal floor, yet its variational source
short is `δ/(1+δ)`, which tends to `0`.  Old-block agreement and a
positive fine diagonal floor do not control the returning-memory
relaxation. -/
theorem old_block_no_short_transport :
    (∀ δ s : ℝ, oldBlockQuad δ ![s, 0] = s * s) ∧
    (∀ δ : ℝ, 0 ≤ δ → 1 ≤ oldBlockFine δ 1 1) ∧
    (∀ δ : ℝ, 0 < δ → ∀ s : ℝ,
      IsLeast {e : ℝ | ∃ y : ℝ, e = oldBlockQuad δ ![s, y]} (δ / (1 + δ) * s ^ 2)) ∧
    Filter.Tendsto (fun δ : ℝ => δ / (1 + δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  ⟨oldBlock_compression_exact, fun _ hδ => oldBlock_diagonal_floor hδ,
    fun _ hδ => oldBlock_short_isLeast hδ, oldBlock_short_limit⟩

end OldBlockShort

/-! ### `thm:GT-mediator-loss-Gram`

For `ℤ = [B Y]` and a contraction `T` (i.e. `I - T^*T ⪰ 0`) we prove:
the block description of `Γ_loss = ℤ^*(I - T^*T)ℤ` (PSR.6), the exact
decomposition `ℤ^*ℤ = ℤ^*T^*Tℤ + Γ_loss` with `Γ_loss ⪰ 0` (PSR.7), the
Moore–Penrose Schur bound `C_loss^* L_B^† C_loss ⪯ L_Y` and the mixed
Cauchy–Schwarz bound (PSR.8), the criterion that the complete cross
response is mediated exactly iff `C_loss = 0`, and the explicit `ℝ³`
witness showing this does not require `L_B = 0` or `L_Y = 0`. -/

section MediatorLoss

variable {H W P Q : Type*} [Fintype H] [Fintype W] [Fintype P] [Fintype Q]
variable [DecidableEq H]

/-- The joint block synthesis `ℤ = [B Y]`. -/
def mediatorZ (B : Matrix H P ℂ) (Y : Matrix H Q ℂ) : Matrix H (P ⊕ Q) ℂ :=
  fromCols B Y

/-- The mediator-loss form `I - T^*T`. -/
def mediatorLossForm (T : Matrix W H ℂ) : Matrix H H ℂ := 1 - Tᴴ * T

/-- The complete mediator-loss Gram `Γ_loss = ℤ^*(I - T^*T)ℤ` (PSR.6). -/
def mediatorLossGram (T : Matrix W H ℂ) (B : Matrix H P ℂ) (Y : Matrix H Q ℂ) :
    Matrix (P ⊕ Q) (P ⊕ Q) ℂ :=
  (mediatorZ B Y)ᴴ * mediatorLossForm T * mediatorZ B Y

/-- The diagonal source loss `L_B = B^*(I - T^*T)B`. -/
def mediatorLB (T : Matrix W H ℂ) (B : Matrix H P ℂ) : Matrix P P ℂ :=
  Bᴴ * mediatorLossForm T * B

/-- The cross loss `C_loss = B^*(I - T^*T)Y`. -/
def mediatorCloss (T : Matrix W H ℂ) (B : Matrix H P ℂ) (Y : Matrix H Q ℂ) : Matrix P Q ℂ :=
  Bᴴ * mediatorLossForm T * Y

/-- The diagonal target loss `L_Y = Y^*(I - T^*T)Y`. -/
def mediatorLY (T : Matrix W H ℂ) (Y : Matrix H Q ℂ) : Matrix Q Q ℂ :=
  Yᴴ * mediatorLossForm T * Y

omit [Fintype H] in
/-- The mediator-loss form is Hermitian. -/
theorem mediatorLossForm_isHermitian (T : Matrix W H ℂ) :
    (mediatorLossForm T).IsHermitian := by
  unfold mediatorLossForm
  rw [Matrix.IsHermitian, conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
    conjTranspose_conjTranspose]

omit [Fintype P] [Fintype Q] in
/-- **(PSR.6)** The mediator-loss Gram has the displayed block structure. -/
theorem mediatorLossGram_blocks (T : Matrix W H ℂ) (B : Matrix H P ℂ) (Y : Matrix H Q ℂ) :
    mediatorLossGram T B Y
      = fromBlocks (mediatorLB T B) (mediatorCloss T B Y)
          (mediatorCloss T B Y)ᴴ (mediatorLY T Y) := by
  unfold mediatorLossGram mediatorZ mediatorLB mediatorCloss mediatorLY
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols]
  congr 1
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    (mediatorLossForm_isHermitian T).eq, Matrix.mul_assoc]

omit [Fintype P] [Fintype Q] in
/-- **(PSR.7, decomposition)** `ℤ^*ℤ = ℤ^*T^*Tℤ + Γ_loss`. -/
theorem mediator_gram_decomposition (T : Matrix W H ℂ) (B : Matrix H P ℂ)
    (Y : Matrix H Q ℂ) :
    (mediatorZ B Y)ᴴ * mediatorZ B Y
      = (mediatorZ B Y)ᴴ * (Tᴴ * T) * mediatorZ B Y + mediatorLossGram T B Y := by
  unfold mediatorLossGram mediatorLossForm
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  abel

/-- **(PSR.7, positivity)** `Γ_loss ⪰ 0` for a contraction `T`. -/
theorem mediator_loss_posSemidef (T : Matrix W H ℂ) (B : Matrix H P ℂ) (Y : Matrix H Q ℂ)
    (hT : (mediatorLossForm T).PosSemidef) : (mediatorLossGram T B Y).PosSemidef :=
  hT.conjTranspose_mul_mul_same (mediatorZ B Y)

/-- The diagonal source loss is PSD. -/
theorem mediatorLB_posSemidef (T : Matrix W H ℂ) (B : Matrix H P ℂ)
    (hT : (mediatorLossForm T).PosSemidef) : (mediatorLB T B).PosSemidef :=
  hT.conjTranspose_mul_mul_same B

/-- **(PSR.8, Schur)** The Moore–Penrose Schur bound
`C_loss^* L_B^† C_loss ⪯ L_Y`. -/
theorem mediator_schur_bound [DecidableEq P] (T : Matrix W H ℂ) (B : Matrix H P ℂ)
    (Y : Matrix H Q ℂ) (hT : (mediatorLossForm T).PosSemidef) :
    (mediatorLY T Y - (mediatorCloss T B Y)ᴴ * pinv (mediatorLB_posSemidef T B hT).1
      * mediatorCloss T B Y).PosSemidef := by
  refine schur_posSemidef (mediatorLB_posSemidef T B hT) (mediatorCloss T B Y)
    (mediatorLY T Y) ?_
  rw [← mediatorLossGram_blocks]
  exact mediator_loss_posSemidef T B Y hT

/-- **(PSR.8, Cauchy–Schwarz)** The mixed loss bound
`|⟨x, C_loss y⟩|² ≤ ⟨x, L_B x⟩ ⟨y, L_Y y⟩`. -/
theorem mediator_cross_cauchy_schwarz (T : Matrix W H ℂ) (B : Matrix H P ℂ)
    (Y : Matrix H Q ℂ) (hT : (mediatorLossForm T).PosSemidef) (x : P → ℂ) (y : Q → ℂ) :
    ‖star x ⬝ᵥ (mediatorCloss T B Y *ᵥ y)‖ ^ 2
      ≤ (star x ⬝ᵥ (mediatorLB T B *ᵥ x)).re * (star y ⬝ᵥ (mediatorLY T Y *ᵥ y)).re := by
  have hW := psdSqrt_mul_self hT
  have hWH : (psdSqrt hT.1)ᴴ = psdSqrt hT.1 := (psdSqrt_posSemidef hT.1).1
  have hWWY : psdSqrt hT.1 * (psdSqrt hT.1 * Y) = mediatorLossForm T * Y := by
    rw [← Matrix.mul_assoc, hW]
  have hWWB : psdSqrt hT.1 * (psdSqrt hT.1 * B) = mediatorLossForm T * B := by
    rw [← Matrix.mul_assoc, hW]
  have hCB : mediatorCloss T B Y = (psdSqrt hT.1 * B)ᴴ * (psdSqrt hT.1 * Y) := by
    unfold mediatorCloss
    rw [conjTranspose_mul, hWH]
    simp only [Matrix.mul_assoc]
    rw [hWWY]
  have hLBf : mediatorLB T B = (psdSqrt hT.1 * B)ᴴ * (psdSqrt hT.1 * B) := by
    unfold mediatorLB
    rw [conjTranspose_mul, hWH]
    simp only [Matrix.mul_assoc]
    rw [hWWB]
  have hLYf : mediatorLY T Y = (psdSqrt hT.1 * Y)ᴴ * (psdSqrt hT.1 * Y) := by
    unfold mediatorLY
    rw [conjTranspose_mul, hWH]
    simp only [Matrix.mul_assoc]
    rw [hWWY]
  rw [hCB, hLBf, hLYf]
  exact block_cauchy_schwarz _ _ x y

omit [Fintype P] [Fintype Q] in
/-- **(mediated exactness)** The complete cross response is mediated
exactly, `B^*Y = (TB)^*(TY)`, iff `C_loss = 0`. -/
theorem mediator_exact_iff (T : Matrix W H ℂ) (B : Matrix H P ℂ) (Y : Matrix H Q ℂ) :
    Bᴴ * Y = (T * B)ᴴ * (T * Y) ↔ mediatorCloss T B Y = 0 := by
  have hexp : mediatorCloss T B Y = Bᴴ * Y - (T * B)ᴴ * (T * Y) := by
    unfold mediatorCloss mediatorLossForm
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hexp]
  exact sub_eq_zero.symm

/-- Witness source column `B` (first coordinate of `ℝ³`). -/
def mediatorWitB : Matrix (Fin 3) (Fin 1) ℂ := !![1; 0; 0]

/-- Witness target column `Y` (second coordinate of `ℝ³`). -/
def mediatorWitY : Matrix (Fin 3) (Fin 1) ℂ := !![0; 1; 0]

/-- Witness mediator `T = P_{e₃}`. -/
def mediatorWitT : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, 0; 0, 0, 1]

/-- The witness loss form is the diagonal `diag(1,1,0)`. -/
theorem mediatorWit_form_eq : mediatorLossForm mediatorWitT
    = Matrix.diagonal ![1, 1, 0] := by
  unfold mediatorLossForm mediatorWitT
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal]

/-- **(strict separation witness)** `T = P_{e₃}` is a contraction with
`C_loss = 0` but `L_B ≠ 0` and `L_Y ≠ 0`: exact cross mediation does not
require the diagonal losses to vanish. -/
theorem mediator_witness_separation :
    (mediatorLossForm mediatorWitT).PosSemidef ∧
    mediatorCloss mediatorWitT mediatorWitB mediatorWitY = 0 ∧
    mediatorLB mediatorWitT mediatorWitB ≠ 0 ∧
    mediatorLY mediatorWitT mediatorWitY ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mediatorWit_form_eq]
    rw [posSemidef_diagonal_iff]
    intro i
    fin_cases i
    · exact zero_le_one
    · exact zero_le_one
    · exact le_refl 0
  · unfold mediatorCloss
    rw [mediatorWit_form_eq]
    ext i j
    fin_cases i
    fin_cases j
    simp [mediatorWitB, mediatorWitY, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal]
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) h
    rw [mediatorLB, mediatorWit_form_eq] at h00
    simp [mediatorWitB, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] at h00
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) h
    rw [mediatorLY, mediatorWit_form_eq] at h00
    simp [mediatorWitY, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] at h00

end MediatorLoss

/-! ### `thm:GT-constraint-first-action`

The constraint-first Riesz–Thomson action (PSR.10–PSR.12), rendered on
the finite Hermitian coefficient carrier `ℂ^E` (containing the stated
real case): `G ≻ 0`, a constraint matrix `L`, target `t`, the projector
`Q_{G,L} = I - G⁻¹L^*(LG⁻¹L^*)^† L` (`cfProjector`), the Riesz vector
`r = Q G⁻¹ t` (`cfRiesz`), and the action `d = ⟨r, Gr⟩` (`cfAction`).
We prove that `Q` is the `G`-orthogonal projection onto `Ker L` (kills,
fixes, idempotent, `G`-self-adjoint), the representation `⟨t, x⟩ = ⟨r,
Gx⟩` on `Ker L`, infeasibility on `d = 0`, the unique minimum-action
solution `x_q = (q/d) r` with action `|q|²/d` (PSR.11), the Pythagoras
split against the ambient solution (PSR.12), and `d ≤ d₀`, giving the
action ratio `d₀/d ≥ 1`. -/

section ConstraintFirst

variable {E Z : Type*} [Fintype E] [Fintype Z] [DecidableEq E] [DecidableEq Z]
variable {G : Matrix E E ℂ}

omit [Fintype Z] [DecidableEq Z] in
/-- The constraint Gram `A = L G⁻¹ L^*` is Hermitian. -/
theorem cfGram_isHermitian (hG : G.PosDef) (L : Matrix Z E ℂ) :
    (L * G⁻¹ * Lᴴ).IsHermitian :=
  isHermitian_mul_mul_conjTranspose L hG.inv.1

omit [DecidableEq Z] in
/-- The constraint Gram `A = L G⁻¹ L^*` is PSD. -/
theorem cfGram_posSemidef (hG : G.PosDef) (L : Matrix Z E ℂ) :
    (L * G⁻¹ * Lᴴ).PosSemidef :=
  hG.inv.posSemidef.mul_mul_conjTranspose_same L

/-- The `G`-orthogonal constraint projector `Q_{G,L}` (PSR.10). -/
noncomputable def cfProjector (hG : G.PosDef) (L : Matrix Z E ℂ) : Matrix E E ℂ :=
  1 - G⁻¹ * Lᴴ * pinv (cfGram_isHermitian hG L) * L

/-- The Riesz vector `r = Q_{G,L} G⁻¹ t` (PSR.10). -/
noncomputable def cfRiesz (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ) : E → ℂ :=
  cfProjector hG L *ᵥ (G⁻¹ *ᵥ t)

/-- The constrained action `d = ⟨r, G r⟩` (PSR.10). -/
noncomputable def cfAction (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ) : ℝ :=
  (star (cfRiesz hG L t) ⬝ᵥ (G *ᵥ cfRiesz hG L t)).re

/-- The ambient action `d₀ = ⟨t, G⁻¹ t⟩` (PSR.12). -/
noncomputable def cfAmbientAction (_hG : G.PosDef) (t : E → ℂ) : ℝ :=
  (star t ⬝ᵥ (G⁻¹ *ᵥ t)).re

omit [DecidableEq Z] in
/-- Kernel inclusion of the constraint Gram: `A x = 0 → L^* x = 0`. -/
theorem cfGram_kernel (hG : G.PosDef) (L : Matrix Z E ℂ) {x : Z → ℂ}
    (hx : (L * G⁻¹ * Lᴴ) *ᵥ x = 0) : Lᴴ *ᵥ x = 0 := by
  have hform : star x ⬝ᵥ ((L * G⁻¹ * Lᴴ) *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
  have hfact : star x ⬝ᵥ ((L * G⁻¹ * Lᴴ) *ᵥ x)
      = star (Lᴴ *ᵥ x) ⬝ᵥ (G⁻¹ *ᵥ (Lᴴ *ᵥ x)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, adjoint_dot]
  rw [hfact] at hform
  have hzero := (hG.inv.posSemidef.dotProduct_mulVec_zero_iff _).mp hform
  calc Lᴴ *ᵥ x = (G * G⁻¹) *ᵥ (Lᴴ *ᵥ x) := by rw [posDef_mul_inv_cancel hG, one_mulVec]
    _ = G *ᵥ (G⁻¹ *ᵥ (Lᴴ *ᵥ x)) := by rw [← mulVec_mulVec]
    _ = 0 := by rw [hzero, mulVec_zero]

/-- The Moore–Penrose range condition `A A^† L = L` for the constraint
Gram: `Ran L ⊆ Ran A`. -/
theorem cfGram_range (hG : G.PosDef) (L : Matrix Z E ℂ) :
    (L * G⁻¹ * Lᴴ) * pinv (cfGram_isHermitian hG L) * L = L := by
  have hpsd := cfGram_posSemidef hG L
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc, mul_pinv_eq_supportProj]
  have hker : Lᴴ * (1 - supportProj (cfGram_isHermitian hG L)) = 0 := by
    rw [ext_iff_mulVec]
    intro v
    rw [zero_mulVec, ← mulVec_mulVec]
    have h1 : (1 - supportProj (cfGram_isHermitian hG L)) *ᵥ v
        = v - supportProj (cfGram_isHermitian hG L) *ᵥ v := by
      rw [sub_mulVec, one_mulVec]
    rw [h1]
    exact cfGram_kernel hG L (mulVec_sub_supportProj hpsd v)
  have hker2 := congrArg conjTranspose hker
  rw [conjTranspose_mul, conjTranspose_zero, conjTranspose_conjTranspose] at hker2
  have hQH : (1 - supportProj (cfGram_isHermitian hG L))ᴴ
      = 1 - supportProj (cfGram_isHermitian hG L) := by
    rw [conjTranspose_sub, conjTranspose_one,
      (supportProj_posSemidef (cfGram_isHermitian hG L)).1.eq]
  rw [hQH, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hker2
  exact hker2.symm

/-- The projector annihilates the constraint: `L Q_{G,L} = 0`. -/
theorem cfProjector_kills (hG : G.PosDef) (L : Matrix Z E ℂ) :
    L * cfProjector hG L = 0 := by
  unfold cfProjector
  rw [Matrix.mul_sub, Matrix.mul_one]
  have hassoc : L * (G⁻¹ * Lᴴ * pinv (cfGram_isHermitian hG L) * L)
      = (L * G⁻¹ * Lᴴ) * pinv (cfGram_isHermitian hG L) * L := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, cfGram_range hG L, sub_self]

/-- The projector fixes the constraint kernel. -/
theorem cfProjector_fixes (hG : G.PosDef) (L : Matrix Z E ℂ) {x : E → ℂ}
    (hx : L *ᵥ x = 0) : cfProjector hG L *ᵥ x = x := by
  unfold cfProjector
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hx, mulVec_zero, sub_zero]

/-- The projector is idempotent. -/
theorem cfProjector_idem (hG : G.PosDef) (L : Matrix Z E ℂ) :
    cfProjector hG L * cfProjector hG L = cfProjector hG L := by
  have hLQ := cfProjector_kills hG L
  calc cfProjector hG L * cfProjector hG L
      = (1 - G⁻¹ * Lᴴ * pinv (cfGram_isHermitian hG L) * L) * cfProjector hG L := rfl
    _ = cfProjector hG L
        - G⁻¹ * (Lᴴ * (pinv (cfGram_isHermitian hG L) * (L * cfProjector hG L))) := by
        rw [Matrix.sub_mul, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
    _ = cfProjector hG L := by
        rw [hLQ]
        simp only [Matrix.mul_zero, sub_zero]

/-- `G Q_{G,L} = G - L^* A^† L`. -/
theorem cfProjector_G_eq (hG : G.PosDef) (L : Matrix Z E ℂ) :
    G * cfProjector hG L = G - Lᴴ * pinv (cfGram_isHermitian hG L) * L := by
  unfold cfProjector
  rw [Matrix.mul_sub, Matrix.mul_one]
  congr 1
  simp only [← Matrix.mul_assoc]
  rw [posDef_mul_inv_cancel hG, Matrix.one_mul]

/-- The projector is `G`-self-adjoint: `(GQ)^* = GQ`. -/
theorem cfProjector_G_symm (hG : G.PosDef) (L : Matrix Z E ℂ) :
    (G * cfProjector hG L)ᴴ = G * cfProjector hG L := by
  rw [cfProjector_G_eq, conjTranspose_sub, hG.1.eq, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, (pinv_isHermitian (cfGram_isHermitian hG L)).eq]
  congr 1
  simp only [Matrix.mul_assoc]

/-- Adjoint exchange: `Q^* G = G Q`. -/
theorem cfProjector_adjoint_G (hG : G.PosDef) (L : Matrix Z E ℂ) :
    (cfProjector hG L)ᴴ * G = G * cfProjector hG L := by
  have h := cfProjector_G_symm hG L
  rwa [conjTranspose_mul, hG.1.eq] at h

/-- The Riesz vector lies in the constraint kernel. -/
theorem cfRiesz_mem_ker (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ) :
    L *ᵥ cfRiesz hG L t = 0 := by
  unfold cfRiesz
  rw [mulVec_mulVec, cfProjector_kills hG L, zero_mulVec]

/-- **(representation)** `⟨t, x⟩ = ⟨r, Gx⟩` for every `x ∈ Ker L`. -/
theorem cf_representation (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ) {x : E → ℂ}
    (hx : L *ᵥ x = 0) : star t ⬝ᵥ x = star (cfRiesz hG L t) ⬝ᵥ (G *ᵥ x) := by
  unfold cfRiesz
  calc star t ⬝ᵥ x
      = star t ⬝ᵥ ((G⁻¹ * G) *ᵥ x) := by rw [posDef_inv_mul_cancel hG, one_mulVec]
    _ = star t ⬝ᵥ (G⁻¹ *ᵥ (G *ᵥ x)) := by rw [← mulVec_mulVec]
    _ = star (G⁻¹ *ᵥ t) ⬝ᵥ (G *ᵥ x) := by
        rw [star_mulVec, ← dotProduct_mulVec, hG.inv.1.eq]
    _ = star (G⁻¹ *ᵥ t) ⬝ᵥ (G *ᵥ (cfProjector hG L *ᵥ x)) := by
        rw [cfProjector_fixes hG L hx]
    _ = star (G⁻¹ *ᵥ t) ⬝ᵥ ((G * cfProjector hG L) *ᵥ x) := by rw [← mulVec_mulVec]
    _ = star (G⁻¹ *ᵥ t) ⬝ᵥ (((cfProjector hG L)ᴴ * G) *ᵥ x) := by
        rw [cfProjector_adjoint_G]
    _ = star (cfProjector hG L *ᵥ (G⁻¹ *ᵥ t)) ⬝ᵥ (G *ᵥ x) := by
        rw [← mulVec_mulVec, adjoint_dot, conjTranspose_conjTranspose]

/-- The self-pairing of the Riesz vector against `t` is the action `d`. -/
theorem cf_riesz_pairing (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ) :
    star t ⬝ᵥ cfRiesz hG L t = ((cfAction hG L t : ℝ) : ℂ) := by
  rw [cf_representation hG L t (cfRiesz_mem_ker hG L t)]
  exact hermitian_form_ofReal hG.1 _

/-- The `G`-self-pairing of the Riesz vector is the action `d`. -/
theorem cf_riesz_G_pairing (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ) :
    star (cfRiesz hG L t) ⬝ᵥ (G *ᵥ cfRiesz hG L t) = ((cfAction hG L t : ℝ) : ℂ) :=
  hermitian_form_ofReal hG.1 _

/-- **(infeasibility)** If `d = 0`, a nonzero target value is infeasible:
the target functional vanishes on all of `Ker L`. -/
theorem cf_infeasible (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ)
    (hd : cfAction hG L t = 0) : ∀ x, L *ᵥ x = 0 → star t ⬝ᵥ x = 0 := by
  intro x hx
  have hGr : G *ᵥ cfRiesz hG L t = 0 := by
    have hzero : star (cfRiesz hG L t) ⬝ᵥ (G *ᵥ cfRiesz hG L t) = 0 := by
      rw [cf_riesz_G_pairing hG L t, hd, Complex.ofReal_zero]
    exact (hG.posSemidef.dotProduct_mulVec_zero_iff _).mp hzero
  have hr0 : cfRiesz hG L t = 0 := by
    calc cfRiesz hG L t = (G⁻¹ * G) *ᵥ cfRiesz hG L t := by
          rw [posDef_inv_mul_cancel hG, one_mulVec]
      _ = G⁻¹ *ᵥ (G *ᵥ cfRiesz hG L t) := by rw [← mulVec_mulVec]
      _ = 0 := by rw [hGr, mulVec_zero]
  rw [cf_representation hG L t hx, hr0, star_zero, zero_dotProduct]

/-- The minimum-action candidate `x_q = (q/d) r` (PSR.11). -/
noncomputable def cfSolution (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ) (q : ℂ) :
    E → ℂ :=
  (q / ((cfAction hG L t : ℝ) : ℂ)) • cfRiesz hG L t

/-- **(PSR.11, feasibility)** On the branch `d > 0`, the candidate
satisfies both constraints: `L x_q = 0` and `⟨t, x_q⟩ = q`. -/
theorem cf_solution_feasible (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ)
    (hd : 0 < cfAction hG L t) (q : ℂ) :
    L *ᵥ cfSolution hG L t q = 0 ∧ star t ⬝ᵥ cfSolution hG L t q = q := by
  have hdc : ((cfAction hG L t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  constructor
  · unfold cfSolution
    rw [mulVec_smul, cfRiesz_mem_ker hG L t, smul_zero]
  · unfold cfSolution
    rw [dotProduct_smul, cf_riesz_pairing hG L t, smul_eq_mul, div_mul_cancel₀ q hdc]

/-- **(PSR.11, action value)** The candidate has action `|q|²/d`. -/
theorem cf_solution_energy (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ)
    (hd : 0 < cfAction hG L t) (q : ℂ) :
    star (cfSolution hG L t q) ⬝ᵥ (G *ᵥ cfSolution hG L t q)
      = ((‖q‖ ^ 2 / cfAction hG L t : ℝ) : ℂ) := by
  have hdc : ((cfAction hG L t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  unfold cfSolution
  rw [star_smul, smul_dotProduct, mulVec_smul, dotProduct_smul, cf_riesz_G_pairing hG L t]
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, Complex.star_def, Complex.conj_mul']
  rw [Complex.ofReal_div, Complex.ofReal_pow]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  push_cast
  field_simp

/-- **(PSR.11, minimality and uniqueness)** Every feasible `x` has action
at least `|q|²/d`, with equality exactly at `x = x_q`. -/
theorem cf_minimum (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ)
    (hd : 0 < cfAction hG L t) (q : ℂ) (x : E → ℂ)
    (hxL : L *ᵥ x = 0) (hxt : star t ⬝ᵥ x = q) :
    ‖q‖ ^ 2 / cfAction hG L t ≤ (star x ⬝ᵥ (G *ᵥ x)).re ∧
    ((star x ⬝ᵥ (G *ᵥ x)).re = ‖q‖ ^ 2 / cfAction hG L t ↔ x = cfSolution hG L t q) := by
  have hfeas := cf_solution_feasible hG L t hd q
  have hwL : L *ᵥ (x - cfSolution hG L t q) = 0 := by
    rw [mulVec_sub, hxL, hfeas.1, sub_self]
  have hwt : star t ⬝ᵥ (x - cfSolution hG L t q) = 0 := by
    rw [dotProduct_sub, hxt, hfeas.2, sub_self]
  have hcrossgen : ∀ w : E → ℂ, L *ᵥ w = 0 → star t ⬝ᵥ w = 0 →
      star (cfSolution hG L t q) ⬝ᵥ (G *ᵥ w) = 0 := by
    intro w hwL' hwt'
    have hrep := cf_representation hG L t hwL'
    unfold cfSolution
    rw [star_smul, smul_dotProduct, ← hrep, hwt', smul_zero]
  have hcross : star (cfSolution hG L t q) ⬝ᵥ (G *ᵥ (x - cfSolution hG L t q)) = 0 :=
    hcrossgen _ hwL hwt
  have hcross2 : star (x - cfSolution hG L t q) ⬝ᵥ (G *ᵥ cfSolution hG L t q) = 0 := by
    rw [hermitian_form_conj_symm hG.1, hcross, star_zero]
  have hexp := form_add_of_cross_zero (M := G) (cfSolution hG L t q)
    (x - cfSolution hG L t q) hcross hcross2
  have hxsum : cfSolution hG L t q + (x - cfSolution hG L t q) = x := by abel
  rw [hxsum, cf_solution_energy hG L t hd q] at hexp
  have hre := congrArg Complex.re hexp
  rw [Complex.add_re, Complex.ofReal_re] at hre
  have hw_nonneg := re_form_nonneg hG.posSemidef (x - cfSolution hG L t q)
  constructor
  · rw [hre]
    linarith
  · constructor
    · intro heq
      have hwzero : (star (x - cfSolution hG L t q)
          ⬝ᵥ (G *ᵥ (x - cfSolution hG L t q))).re = 0 := by
        rw [hre] at heq
        linarith
      by_contra hne
      have hwne : x - cfSolution hG L t q ≠ 0 := fun h => hne (by
        have := sub_eq_zero.mp h
        exact this)
      exact (re_form_pos hG hwne).ne' hwzero
    · rintro rfl
      have := cf_solution_energy hG L t hd q
      have hre2 := congrArg Complex.re this
      rw [Complex.ofReal_re] at hre2
      exact hre2

/-- The ambient minimum-action candidate `x_q^amb = (q/d₀) G⁻¹ t`
(PSR.12). -/
noncomputable def cfAmbient (hG : G.PosDef) (t : E → ℂ) (q : ℂ) : E → ℂ :=
  (q / ((cfAmbientAction hG t : ℝ) : ℂ)) • (G⁻¹ *ᵥ t)

/-- On the branch `d > 0` the target is nonzero and the ambient action is
positive. -/
theorem cf_ambient_action_pos (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ)
    (hd : 0 < cfAction hG L t) : 0 < cfAmbientAction hG t := by
  have ht : t ≠ 0 := by
    rintro rfl
    have hr0 : cfRiesz hG L 0 = 0 := by
      unfold cfRiesz
      rw [mulVec_zero, mulVec_zero]
    have : cfAction hG L 0 = 0 := by
      unfold cfAction
      rw [hr0, mulVec_zero, dotProduct_zero, Complex.zero_re]
    exact hd.ne' this
  exact re_form_pos hG.inv ht

/-- `G`-pairing of the ambient direction: `⟨G⁻¹t, G G⁻¹ t⟩ = d₀`. -/
theorem cf_ambient_pairing (hG : G.PosDef) (t : E → ℂ) :
    star (G⁻¹ *ᵥ t) ⬝ᵥ (G *ᵥ (G⁻¹ *ᵥ t)) = ((cfAmbientAction hG t : ℝ) : ℂ) := by
  have hcancel : G *ᵥ (G⁻¹ *ᵥ t) = t := by
    rw [mulVec_mulVec, posDef_mul_inv_cancel hG, one_mulVec]
  rw [hcancel]
  have hsymm : star (G⁻¹ *ᵥ t) ⬝ᵥ t = star (star t ⬝ᵥ (G⁻¹ *ᵥ t)) :=
    star_dotProduct _ _
  rw [hsymm, hermitian_form_ofReal hG.inv.1 t]
  rw [Complex.star_def, Complex.conj_ofReal]
  rfl

/-- The pairing `⟨r, t⟩ = d`. -/
theorem cf_riesz_t_pairing (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ) :
    star (cfRiesz hG L t) ⬝ᵥ t = ((cfAction hG L t : ℝ) : ℂ) := by
  have h := star_dotProduct (cfRiesz hG L t) t
  rw [h, cf_riesz_pairing hG L t, Complex.star_def, Complex.conj_ofReal]

/-- **(PSR.12)** The Pythagoras split of the constrained solution over the
ambient solution: `‖x_q‖_G² = ‖x_q^amb‖_G² + ‖x_q - x_q^amb‖_G²`. -/
theorem cf_pythagoras (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ)
    (hd : 0 < cfAction hG L t) (q : ℂ) :
    star (cfSolution hG L t q) ⬝ᵥ (G *ᵥ cfSolution hG L t q)
      = star (cfAmbient hG t q) ⬝ᵥ (G *ᵥ cfAmbient hG t q)
        + star (cfSolution hG L t q - cfAmbient hG t q)
            ⬝ᵥ (G *ᵥ (cfSolution hG L t q - cfAmbient hG t q)) := by
  have hd0 := cf_ambient_action_pos hG L t hd
  have hdc : ((cfAction hG L t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hd0c : ((cfAmbientAction hG t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd0.ne'
  have hGamb : G *ᵥ (G⁻¹ *ᵥ t) = t := by
    rw [mulVec_mulVec, posDef_mul_inv_cancel hG, one_mulVec]
  -- the cross pairing equals the ambient energy
  have hcross : star (cfSolution hG L t q) ⬝ᵥ (G *ᵥ cfAmbient hG t q)
      = ((‖q‖ ^ 2 / cfAmbientAction hG t : ℝ) : ℂ) := by
    unfold cfSolution cfAmbient
    rw [star_smul, smul_dotProduct, mulVec_smul, dotProduct_smul, hGamb,
      cf_riesz_t_pairing hG L t]
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, Complex.star_def]
    rw [map_div₀, Complex.conj_ofReal]
    rw [Complex.ofReal_div, Complex.ofReal_pow]
    field_simp
    exact Complex.conj_mul' q
  have hamb : star (cfAmbient hG t q) ⬝ᵥ (G *ᵥ cfAmbient hG t q)
      = ((‖q‖ ^ 2 / cfAmbientAction hG t : ℝ) : ℂ) := by
    unfold cfAmbient
    rw [star_smul, smul_dotProduct, mulVec_smul, dotProduct_smul, cf_ambient_pairing hG t]
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, Complex.star_def]
    rw [map_div₀, Complex.conj_ofReal]
    rw [Complex.ofReal_div, Complex.ofReal_pow]
    field_simp
    exact Complex.conj_mul' q
  have hcross2 : star (cfAmbient hG t q) ⬝ᵥ (G *ᵥ cfSolution hG L t q)
      = ((‖q‖ ^ 2 / cfAmbientAction hG t : ℝ) : ℂ) := by
    rw [hermitian_form_conj_symm hG.1, hcross, Complex.star_def, Complex.conj_ofReal]
  rw [form_sub_expand G (cfSolution hG L t q) (cfAmbient hG t q), hcross, hcross2, hamb]
  ring

/-- **(PSR.12, comparison)** The constrained action never exceeds the
ambient action: `d ≤ d₀`. -/
theorem cf_action_le_ambient (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ) :
    cfAction hG L t ≤ cfAmbientAction hG t := by
  have hQfix : cfProjector hG L *ᵥ cfRiesz hG L t = cfRiesz hG L t := by
    unfold cfRiesz
    rw [mulVec_mulVec, cfProjector_idem hG L]
  have hQdiff : cfProjector hG L *ᵥ ((G⁻¹ *ᵥ t) - cfRiesz hG L t) = 0 := by
    rw [mulVec_sub, hQfix]
    unfold cfRiesz
    exact sub_self _
  have hcross1 : star (cfRiesz hG L t) ⬝ᵥ (G *ᵥ ((G⁻¹ *ᵥ t) - cfRiesz hG L t)) = 0 := by
    have hstar : star (cfRiesz hG L t) = star (G⁻¹ *ᵥ t) ᵥ* (cfProjector hG L)ᴴ := by
      unfold cfRiesz
      rw [star_mulVec]
    rw [hstar, ← dotProduct_mulVec]
    have hstep : (cfProjector hG L)ᴴ *ᵥ (G *ᵥ ((G⁻¹ *ᵥ t) - cfRiesz hG L t))
        = G *ᵥ (cfProjector hG L *ᵥ ((G⁻¹ *ᵥ t) - cfRiesz hG L t)) := by
      rw [mulVec_mulVec, mulVec_mulVec, cfProjector_adjoint_G hG L]
    rw [hstep, hQdiff, mulVec_zero, dotProduct_zero]
  have hcross2 : star ((G⁻¹ *ᵥ t) - cfRiesz hG L t) ⬝ᵥ (G *ᵥ cfRiesz hG L t) = 0 := by
    rw [hermitian_form_conj_symm hG.1, hcross1, star_zero]
  have hsplit := form_add_of_cross_zero (M := G) (cfRiesz hG L t)
    ((G⁻¹ *ᵥ t) - cfRiesz hG L t) hcross1 hcross2
  have hsum : cfRiesz hG L t + ((G⁻¹ *ᵥ t) - cfRiesz hG L t) = G⁻¹ *ᵥ t := by abel
  rw [hsum] at hsplit
  have hd0eq : (star (G⁻¹ *ᵥ t) ⬝ᵥ (G *ᵥ (G⁻¹ *ᵥ t))).re = cfAmbientAction hG t := by
    have := congrArg Complex.re (cf_ambient_pairing hG t)
    rwa [Complex.ofReal_re] at this
  have hre := congrArg Complex.re hsplit
  rw [Complex.add_re, hd0eq] at hre
  have hnn := re_form_nonneg hG.posSemidef ((G⁻¹ *ᵥ t) - cfRiesz hG L t)
  unfold cfAction
  linarith

/-- **(action ratio)** For a feasible nonzero target value the
constrained-to-ambient action ratio is `d₀/d ≥ 1`. -/
theorem cf_action_ratio (hG : G.PosDef) (L : Matrix Z E ℂ) (t : E → ℂ)
    (hd : 0 < cfAction hG L t) :
    1 ≤ cfAmbientAction hG t / cfAction hG L t :=
  (one_le_div hd).mpr (cf_action_le_ambient hG L t)

end ConstraintFirst

/-! ### `thm:GT-Feshbach-source-debit`

The fine determining quotient splits as `𝓗₊ = 𝓗 ⊕ Y` with
`A₊ = [[A₀₀, L^*], [L, C]]`, `C ≻ 0`, coarse form `A ≻ 0`, source
analysis `T : 𝓗 → E`, and a positive debit `D`.  We prove the exact
characterization (ST.9): the debit inequality holds for all `(x, y)` iff
`A₀₀ - L^*C⁻¹L ⪰ A - T^*DT`, by completing the square in the hidden
block.  The two sufficiency clauses follow: `D = D^old + D^ret` is
admissible when the two displayed Loewner bounds hold, and under
`C ⪰ κI`, `L^*L ⪯ T^*XT` one may take `D^ret = κ⁻¹X`. -/

section FeshbachDebit

variable {h y e : Type*} [Fintype h] [Fintype y] [Fintype e] [DecidableEq y]

/-- Completed-square identity for the fine block form over the hidden
block `C ≻ 0`. -/
theorem feshbach_square (A00 : Matrix h h ℂ) (L : Matrix y h ℂ) {C : Matrix y y ℂ}
    (hC : C.PosDef) (x : h → ℂ) (yv : y → ℂ) :
    star (Sum.elim x yv) ⬝ᵥ (fromBlocks A00 Lᴴ L C *ᵥ Sum.elim x yv)
      = star ((C⁻¹ * L) *ᵥ x + yv) ⬝ᵥ (C *ᵥ ((C⁻¹ * L) *ᵥ x + yv))
        + star x ⬝ᵥ ((A00 - Lᴴ * C⁻¹ * L) *ᵥ x) := by
  have := C.invertibleOfIsUnitDet ((Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit)
  have hkey := schur_complement_eq₂₂ A00 Lᴴ x yv hC.1
  rw [conjTranspose_conjTranspose] at hkey
  simpa only [← dotProduct_mulVec] using hkey

/-- Moving a conjugated quadratic form onto the analysed vector. -/
theorem conj_form_move {m k : Type*} [Fintype m] [Fintype k] (T : Matrix k m ℂ)
    (D : Matrix k k ℂ) (x : m → ℂ) :
    star x ⬝ᵥ ((Tᴴ * D * T) *ᵥ x) = star (T *ᵥ x) ⬝ᵥ (D *ᵥ (T *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, adjoint_dot, conjTranspose_conjTranspose]

/-- Expansion of the (ST.9) comparison form. -/
theorem feshbach_expand (A00 : Matrix h h ℂ) (L : Matrix y h ℂ) (C : Matrix y y ℂ)
    (A : Matrix h h ℂ) (T : Matrix e h ℂ) (D : Matrix e e ℂ) (x : h → ℂ) :
    (star x ⬝ᵥ ((A00 - Lᴴ * C⁻¹ * L - (A - Tᴴ * D * T)) *ᵥ x)).re
      = (star x ⬝ᵥ (A00 *ᵥ x)).re - (star x ⬝ᵥ ((Lᴴ * C⁻¹ * L) *ᵥ x)).re
        - (star x ⬝ᵥ (A *ᵥ x)).re + (star (T *ᵥ x) ⬝ᵥ (D *ᵥ (T *ᵥ x))).re := by
  rw [sub_mulVec, sub_mulVec, sub_mulVec, dotProduct_sub, dotProduct_sub, dotProduct_sub,
    conj_form_move T D x]
  simp only [Complex.sub_re]
  ring

/-- **(ST.9)** Feshbach characterization of the returning-memory debit:
the pointwise debit inequality holds iff `A₀₀ - L^*C⁻¹L ⪰ A - T^*DT`. -/
theorem feshbach_debit_iff (A00 : Matrix h h ℂ) (L : Matrix y h ℂ) {C : Matrix y y ℂ}
    {A : Matrix h h ℂ} (T : Matrix e h ℂ) {D : Matrix e e ℂ}
    (hA00 : A00.IsHermitian) (hC : C.PosDef) (hA : A.PosDef) (hD : D.PosSemidef) :
    (∀ (x : h → ℂ) (yv : y → ℂ),
      (star x ⬝ᵥ (A *ᵥ x)).re
        ≤ (star (Sum.elim x yv) ⬝ᵥ (fromBlocks A00 Lᴴ L C *ᵥ Sum.elim x yv)).re
          + (star (T *ᵥ x) ⬝ᵥ (D *ᵥ (T *ᵥ x))).re)
      ↔ (A00 - Lᴴ * C⁻¹ * L - (A - Tᴴ * D * T)).PosSemidef := by
  constructor
  · intro hineq
    refine posSemidef_of_re_form ?_ fun x => ?_
    · have h1 : (Lᴴ * C⁻¹ * L).IsHermitian := isHermitian_conjTranspose_mul_mul L hC.inv.1
      have h2 : (Tᴴ * D * T).IsHermitian := isHermitian_conjTranspose_mul_mul T hD.1
      exact (hA00.sub h1).sub (hA.1.sub h2)
    · have hx := hineq x (-((C⁻¹ * L) *ᵥ x))
      rw [feshbach_square A00 L hC x _] at hx
      have hzero : (C⁻¹ * L) *ᵥ x + -((C⁻¹ * L) *ᵥ x) = 0 := add_neg_cancel _
      rw [hzero, mulVec_zero, dotProduct_zero, zero_add] at hx
      rw [feshbach_expand A00 L C A T D x]
      rw [sub_mulVec, dotProduct_sub] at hx
      simp only [Complex.sub_re] at hx
      linarith
  · intro hpsd x yv
    have hform := re_form_nonneg hpsd x
    have hC0 := re_form_nonneg hC.posSemidef ((C⁻¹ * L) *ᵥ x + yv)
    rw [feshbach_square A00 L hC x yv]
    rw [feshbach_expand A00 L C A T D x] at hform
    simp only [Complex.add_re]
    rw [sub_mulVec, dotProduct_sub]
    simp only [Complex.sub_re]
    linarith

omit [Fintype h] in
/-- **(ST.9, additivity)** If `A₀₀ ⪰ A - T^*D^old T` and
`L^*C⁻¹L ⪯ T^*D^ret T`, then `D = D^old + D^ret` satisfies the Loewner
characterization. -/
theorem feshbach_debit_add {C : Matrix y y ℂ} (A00 : Matrix h h ℂ) (L : Matrix y h ℂ)
    (A : Matrix h h ℂ) (T : Matrix e h ℂ) (Dold Dret : Matrix e e ℂ)
    (h1 : (A00 - (A - Tᴴ * Dold * T)).PosSemidef)
    (h2 : (Tᴴ * Dret * T - Lᴴ * C⁻¹ * L).PosSemidef) :
    (A00 - Lᴴ * C⁻¹ * L - (A - Tᴴ * (Dold + Dret) * T)).PosSemidef := by
  have hsum := h1.add h2
  have heq : A00 - (A - Tᴴ * Dold * T) + (Tᴴ * Dret * T - Lᴴ * C⁻¹ * L)
      = A00 - Lᴴ * C⁻¹ * L - (A - Tᴴ * (Dold + Dret) * T) := by
    rw [Matrix.mul_add, Matrix.add_mul]
    abel
  rwa [heq] at hsum

/-- **(ST.9, admissibility)** Under the two Loewner bounds the summed
debit `D = D^old + D^ret` is admissible: the pointwise debit inequality
holds. -/
theorem feshbach_debit_admissible (A00 : Matrix h h ℂ) (L : Matrix y h ℂ)
    {C : Matrix y y ℂ} {A : Matrix h h ℂ} (T : Matrix e h ℂ) {Dold Dret : Matrix e e ℂ}
    (hA00 : A00.IsHermitian) (hC : C.PosDef) (hA : A.PosDef)
    (hDold : Dold.PosSemidef) (hDret : Dret.PosSemidef)
    (h1 : (A00 - (A - Tᴴ * Dold * T)).PosSemidef)
    (h2 : (Tᴴ * Dret * T - Lᴴ * C⁻¹ * L).PosSemidef) :
    ∀ (x : h → ℂ) (yv : y → ℂ),
      (star x ⬝ᵥ (A *ᵥ x)).re
        ≤ (star (Sum.elim x yv) ⬝ᵥ (fromBlocks A00 Lᴴ L C *ᵥ Sum.elim x yv)).re
          + (star (T *ᵥ x) ⬝ᵥ ((Dold + Dret) *ᵥ (T *ᵥ x))).re :=
  (feshbach_debit_iff A00 L T hA00 hC hA (hDold.add hDret)).mpr
    (feshbach_debit_add A00 L A T Dold Dret h1 h2)

/-- **(ST.9, high-shell debit)** If `C ⪰ κI` with `κ > 0` and
`L^*L ⪯ T^*XT`, then `D^ret = κ⁻¹X` bounds the returning-memory term:
`L^*C⁻¹L ⪯ T^*(κ⁻¹X)T`. -/
theorem feshbach_kappa_debit (L : Matrix y h ℂ) {C : Matrix y y ℂ} (T : Matrix e h ℂ)
    {X : Matrix e e ℂ} (hC : C.PosDef) {κ : ℝ} (hκ : 0 < κ)
    (hCfloor : (C - (κ : ℂ) • 1).PosSemidef) (hX : X.IsHermitian)
    (hLX : (Tᴴ * X * T - Lᴴ * L).PosSemidef) :
    (Tᴴ * (((κ⁻¹ : ℝ) : ℂ) • X) * T - Lᴴ * C⁻¹ * L).PosSemidef := by
  have hev := le_eigenvalues_of_loewner hC.1 hCfloor
  have hCinv : (((κ⁻¹ : ℝ) : ℂ) • 1 - C⁻¹).PosSemidef := by
    rw [posDef_inv_eq_spectral hC, ← spectralFunction_const hC.1 κ⁻¹,
      ← spectralFunction_sub hC.1]
    refine spectralFunction_posSemidef hC.1 _ fun i => ?_
    have h1 := hev i
    have hpos : 0 < hC.1.eigenvalues i := lt_of_lt_of_le hκ h1
    have hinv : (hC.1.eigenvalues i)⁻¹ ≤ κ⁻¹ := by
      rw [inv_le_inv₀ hpos hκ]
      exact h1
    linarith
  have hsmul : Tᴴ * (((κ⁻¹ : ℝ) : ℂ) • X) * T = ((κ⁻¹ : ℝ) : ℂ) • (Tᴴ * X * T) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hXherm : (((κ⁻¹ : ℝ) : ℂ) • X).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_smul, hX.eq, Complex.star_def, Complex.conj_ofReal]
  refine posSemidef_of_re_form ?_ fun x => ?_
  · exact (isHermitian_conjTranspose_mul_mul T hXherm).sub
      (isHermitian_conjTranspose_mul_mul L hC.inv.1)
  · have hCform := re_form_nonneg hCinv (L *ᵥ x)
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
      smul_eq_mul] at hCform
    simp only [Complex.sub_re, Complex.re_ofReal_mul] at hCform
    have hLform := re_form_nonneg hLX x
    rw [sub_mulVec, dotProduct_sub] at hLform
    simp only [Complex.sub_re] at hLform
    have hLL : star x ⬝ᵥ ((Lᴴ * L) *ᵥ x) = star (L *ᵥ x) ⬝ᵥ (L *ᵥ x) := by
      rw [← mulVec_mulVec, adjoint_dot, conjTranspose_conjTranspose]
    rw [conj_form_move T X x, hLL] at hLform
    rw [sub_mulVec, dotProduct_sub]
    simp only [Complex.sub_re]
    rw [hsmul, smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [Complex.re_ofReal_mul, conj_form_move T X x]
    have hmove1 : (star x ⬝ᵥ ((Lᴴ * C⁻¹ * L) *ᵥ x)).re
        = (star (L *ᵥ x) ⬝ᵥ (C⁻¹ *ᵥ (L *ᵥ x))).re := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, adjoint_dot, conjTranspose_conjTranspose]
    rw [hmove1]
    have hκinv : (0 : ℝ) ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
    have hprod : 0 ≤ κ⁻¹ * ((star (T *ᵥ x) ⬝ᵥ (X *ᵥ (T *ᵥ x))).re
        - (star (L *ᵥ x) ⬝ᵥ (L *ᵥ x)).re) := mul_nonneg hκinv hLform
    rw [mul_sub] at hprod
    linarith

end FeshbachDebit

/-! ### `thm:GT-source-short-cutoff-transport`

The variational source short (ST.1) is the attained least fine energy
over each source fibre; `short_exists` constructs it (as
`(T A⁻¹ T^*)⁻¹`) for every positive fine form and onto source analysis,
so the variational hypothesis `hKvar` below is inhabited, never vacuous.
The determining quotients `𝓗_n` vary along the chain; the source
coefficient spaces, which the packet's unitaries `U_n` identify, are
rendered on one finite carrier `ι` with `U n` square unitary.  We prove
the one-step Loewner recursion (ST.5), the telescoped comparison (ST.6)
with `U_{N:m} =` `shortUprod U m (N - m)`, and the uniform reserve
(ST.7), with `λ_min`/`‖·‖` rendered as the extreme eigenvalues
`hermLamMin`/`hermLamMax` of the Hermitian matrices involved.  No lower
bound on `A_N` outside the determining quotient is used anywhere. -/

section ShortTransport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **(ST.1, existence)** The variational source short exists: for
`A ≻ 0` and onto `T` there is a Hermitian `K` whose quadratic form is
the attained least fine energy on every source fibre. -/
theorem short_exists {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℂ}
    (hA : A.PosDef) (T : Matrix ι m ℂ) (hT : Function.Surjective (T.mulVec)) :
    ∃ K : Matrix ι ι ℂ, K.IsHermitian ∧ ∀ s : ι → ℂ,
      IsLeast {r : ℝ | ∃ u, T *ᵥ u = s ∧ r = (star u ⬝ᵥ (A *ᵥ u)).re}
        ((star s ⬝ᵥ (K *ᵥ s)).re) := by
  have hAinv := hA.inv
  have hMH : (T * A⁻¹ * Tᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose T hAinv.1
  have hTHinj : ∀ x : ι → ℂ, Tᴴ *ᵥ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨u, hu⟩ := hT x
    have hdot : star x ⬝ᵥ x = 0 := by
      have h1 : star x ⬝ᵥ (T *ᵥ u) = 0 := by
        rw [adjoint_dot, hx, star_zero, zero_dotProduct]
      rwa [hu] at h1
    exact dotProduct_star_self_eq_zero.mp hdot
  have hMpd : (T * A⁻¹ * Tᴴ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hMH fun x hx => ?_
    have hmove : star x ⬝ᵥ ((T * A⁻¹ * Tᴴ) *ᵥ x)
        = star (Tᴴ *ᵥ x) ⬝ᵥ (A⁻¹ *ᵥ (Tᴴ *ᵥ x)) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, adjoint_dot]
    rw [hmove]
    exact hAinv.dotProduct_mulVec_pos fun h => hx (hTHinj x h)
  refine ⟨(T * A⁻¹ * Tᴴ)⁻¹, hMpd.inv.1, fun s => ?_⟩
  have hcancelA : ∀ w : m → ℂ, A *ᵥ (A⁻¹ *ᵥ w) = w := by
    intro w
    rw [mulVec_mulVec, posDef_mul_inv_cancel hA, one_mulVec]
  set u0 : m → ℂ := A⁻¹ *ᵥ (Tᴴ *ᵥ ((T * A⁻¹ * Tᴴ)⁻¹ *ᵥ s)) with hu0
  have hTu0 : T *ᵥ u0 = s := by
    rw [hu0, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec,
      posDef_mul_inv_cancel hMpd, one_mulVec]
  have hAu0 : A *ᵥ u0 = Tᴴ *ᵥ ((T * A⁻¹ * Tᴴ)⁻¹ *ᵥ s) := by
    rw [hu0, hcancelA]
  have henergy : star u0 ⬝ᵥ (A *ᵥ u0) = star s ⬝ᵥ ((T * A⁻¹ * Tᴴ)⁻¹ *ᵥ s) := by
    rw [hAu0, adjoint_dot, conjTranspose_conjTranspose, hTu0]
  constructor
  · exact ⟨u0, hTu0, by rw [henergy]⟩
  · rintro r ⟨u, hu, rfl⟩
    have hTw : T *ᵥ (u - u0) = 0 := by
      rw [mulVec_sub, hu, hTu0, sub_self]
    have hcross1 : star u0 ⬝ᵥ (A *ᵥ (u - u0)) = 0 := by
      rw [hermitian_form_conj_symm hA.1, hAu0, adjoint_dot, conjTranspose_conjTranspose,
        hTw, star_zero, zero_dotProduct, star_zero]
    have hcross2 : star (u - u0) ⬝ᵥ (A *ᵥ u0) = 0 := by
      rw [hAu0, adjoint_dot, conjTranspose_conjTranspose, hTw, star_zero,
        zero_dotProduct]
    have hexp := form_add_of_cross_zero (M := A) u0 (u - u0) hcross1 hcross2
    have hsum : u0 + (u - u0) = u := by abel
    rw [hsum, henergy] at hexp
    have hre := congrArg Complex.re hexp
    rw [Complex.add_re] at hre
    have hnn := re_form_nonneg hA.posSemidef (u - u0)
    linarith

omit [DecidableEq ι] in
/-- **(ST.5)** One-step Loewner transport of the variational source
short: `K_{n+1} ⪰ U_n K_n U_n^* - D_n` for every source-compatible
retraction packet (ST.3–ST.4). -/
theorem short_transport_step {Hsp : ℕ → Type*} [∀ n, Fintype (Hsp n)]
    (A : ∀ n, Matrix (Hsp n) (Hsp n) ℂ) (T : ∀ n, Matrix ι (Hsp n) ℂ)
    (K : ℕ → Matrix ι ι ℂ) (R : ∀ n, Matrix (Hsp n) (Hsp (n + 1)) ℂ)
    (U D : ℕ → Matrix ι ι ℂ) (n : ℕ)
    (hKh : ∀ q, (K q).IsHermitian) (hDh : (D n).IsHermitian)
    (hKvar : ∀ q (s : ι → ℂ),
      IsLeast {r : ℝ | ∃ u, T q *ᵥ u = s ∧ r = (star u ⬝ᵥ (A q *ᵥ u)).re}
        ((star s ⬝ᵥ (K q *ᵥ s)).re))
    (hRT : T n * R n = (U n)ᴴ * T (n + 1))
    (hdebit : (A (n + 1) + (T (n + 1))ᴴ * D n * T (n + 1)
      - (R n)ᴴ * A n * R n).PosSemidef) :
    (K (n + 1) - (U n * K n * (U n)ᴴ - D n)).PosSemidef := by
  refine posSemidef_of_re_form ?_ fun s => ?_
  · exact (hKh (n + 1)).sub ((isHermitian_mul_mul_conjTranspose (U n) (hKh n)).sub hDh)
  · obtain ⟨⟨u, hu, hval⟩, -⟩ := hKvar (n + 1) s
    -- the debit inequality (ST.4) at the minimizer u
    have hdeb := re_form_nonneg hdebit u
    rw [sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add,
      conj_form_move (T (n + 1)) (D n) u, conj_form_move (R n) (A n) u, hu] at hdeb
    simp only [Complex.add_re, Complex.sub_re] at hdeb
    -- level-n lower bound at the retracted vector
    have hmem : (star (R n *ᵥ u) ⬝ᵥ (A n *ᵥ (R n *ᵥ u))).re
        ∈ {r : ℝ | ∃ v, T n *ᵥ v = (U n)ᴴ *ᵥ s ∧ r = (star v ⬝ᵥ (A n *ᵥ v)).re} := by
      refine ⟨R n *ᵥ u, ?_, rfl⟩
      rw [mulVec_mulVec, hRT, ← mulVec_mulVec, hu]
    have hlow := (hKvar n ((U n)ᴴ *ᵥ s)).2 hmem
    -- rewrite the conjugated block form
    have hUform : star s ⬝ᵥ ((U n * K n * (U n)ᴴ) *ᵥ s)
        = star ((U n)ᴴ *ᵥ s) ⬝ᵥ (K n *ᵥ ((U n)ᴴ *ᵥ s)) := by
      have hUU : U n * K n * (U n)ᴴ = ((U n)ᴴ)ᴴ * K n * (U n)ᴴ := by
        rw [conjTranspose_conjTranspose]
      rw [hUU, conj_form_move ((U n)ᴴ) (K n) s]
    rw [sub_mulVec, sub_mulVec, dotProduct_sub, dotProduct_sub, hUform]
    simp only [Complex.sub_re]
    linarith

/-- The transported unitary chain `U_{m+k-1} ⋯ U_m`; the manuscript
`U_{N:m}` is `shortUprod U m (N - m)`. -/
def shortUprod (U : ℕ → Matrix ι ι ℂ) (m : ℕ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | k + 1 => U (m + k) * shortUprod U m k

/-- The unitary chain is co-isometric when each `U_n` is unitary. -/
theorem shortUprod_mul_conjTranspose (U : ℕ → Matrix ι ι ℂ)
    (hU : ∀ n, U n * (U n)ᴴ = 1) (m k : ℕ) :
    shortUprod U m k * (shortUprod U m k)ᴴ = 1 := by
  induction k with
  | zero => simp [shortUprod]
  | succ k ih =>
    rw [shortUprod, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (shortUprod U m k), ih, Matrix.one_mul, hU (m + k)]

/-- **(ST.6)** The telescoped source-short comparison:
`K_N ⪰ U_{N:0} K_0 U_{N:0}^* - ∑_{j<N} U_{N:j+1} D_j U_{N:j+1}^*`. -/
theorem short_transport_telescope {Hsp : ℕ → Type*} [∀ n, Fintype (Hsp n)]
    (A : ∀ n, Matrix (Hsp n) (Hsp n) ℂ) (T : ∀ n, Matrix ι (Hsp n) ℂ)
    (K : ℕ → Matrix ι ι ℂ) (R : ∀ n, Matrix (Hsp n) (Hsp (n + 1)) ℂ)
    (U D : ℕ → Matrix ι ι ℂ)
    (hKh : ∀ q, (K q).IsHermitian) (hDh : ∀ q, (D q).IsHermitian)
    (hKvar : ∀ q (s : ι → ℂ),
      IsLeast {r : ℝ | ∃ u, T q *ᵥ u = s ∧ r = (star u ⬝ᵥ (A q *ᵥ u)).re}
        ((star s ⬝ᵥ (K q *ᵥ s)).re))
    (hRT : ∀ n, T n * R n = (U n)ᴴ * T (n + 1))
    (hdebit : ∀ n, (A (n + 1) + (T (n + 1))ᴴ * D n * T (n + 1)
      - (R n)ᴴ * A n * R n).PosSemidef) (N : ℕ) :
    (K N - (shortUprod U 0 N * K 0 * (shortUprod U 0 N)ᴴ
      - ∑ j ∈ Finset.range N, shortUprod U (j + 1) (N - (j + 1)) * D j
        * (shortUprod U (j + 1) (N - (j + 1)))ᴴ)).PosSemidef := by
  induction N with
  | zero =>
    simp only [shortUprod, Finset.range_zero, Finset.sum_empty, sub_zero,
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, sub_self]
    exact Matrix.PosSemidef.zero
  | succ N ih =>
    have hstep := short_transport_step A T K R U D N hKh (hDh N) hKvar (hRT N) (hdebit N)
    have hconj := ih.mul_mul_conjTranspose_same (U N)
    have hsum := hstep.add hconj
    have hP : shortUprod U 0 (N + 1) = U N * shortUprod U 0 N := by
      rw [shortUprod, Nat.zero_add]
    have hV : ∀ j, j < N → shortUprod U (j + 1) (N + 1 - (j + 1))
        = U N * shortUprod U (j + 1) (N - (j + 1)) := by
      intro j hj
      have h1 : N + 1 - (j + 1) = (N - (j + 1)) + 1 := by omega
      have h2 : (j + 1) + (N - (j + 1)) = N := by omega
      rw [h1, shortUprod, h2]
    have hsumeq : ∑ j ∈ Finset.range (N + 1),
        shortUprod U (j + 1) (N + 1 - (j + 1)) * D j
          * (shortUprod U (j + 1) (N + 1 - (j + 1)))ᴴ
      = U N * (∑ j ∈ Finset.range N, shortUprod U (j + 1) (N - (j + 1)) * D j
          * (shortUprod U (j + 1) (N - (j + 1)))ᴴ) * (U N)ᴴ + D N := by
      rw [Finset.sum_range_succ]
      congr 1
      · rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hV j (Finset.mem_range.mp hj), conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      · have h0 : N + 1 - (N + 1) = 0 := by omega
        rw [h0]
        simp [shortUprod]
    have hexpand : K (N + 1) - (U N * K N * (U N)ᴴ - D N)
        + U N * (K N - (shortUprod U 0 N * K 0 * (shortUprod U 0 N)ᴴ
            - ∑ j ∈ Finset.range N, shortUprod U (j + 1) (N - (j + 1)) * D j
              * (shortUprod U (j + 1) (N - (j + 1)))ᴴ)) * (U N)ᴴ
        = K (N + 1) - (shortUprod U 0 (N + 1) * K 0 * (shortUprod U 0 (N + 1))ᴴ
            - ∑ j ∈ Finset.range (N + 1), shortUprod U (j + 1) (N + 1 - (j + 1)) * D j
              * (shortUprod U (j + 1) (N + 1 - (j + 1)))ᴴ) := by
      rw [hsumeq, hP, conjTranspose_mul]
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_assoc]
      abel
    rwa [hexpand] at hsum

/-- **(ST.7)** Uniform source reserve: if the summed debit norms stay
below the least eigenvalue of `K_0`, every transported short keeps the
uniform floor `λ_min(K_N) ≥ λ_min(K_0) - ∑_j ‖D_j‖ > 0`. -/
theorem short_transport_uniform_reserve {Hsp : ℕ → Type*} [∀ n, Fintype (Hsp n)]
    [Nonempty ι]
    (A : ∀ n, Matrix (Hsp n) (Hsp n) ℂ) (T : ∀ n, Matrix ι (Hsp n) ℂ)
    (K : ℕ → Matrix ι ι ℂ) (R : ∀ n, Matrix (Hsp n) (Hsp (n + 1)) ℂ)
    (U D : ℕ → Matrix ι ι ℂ)
    (hKh : ∀ q, (K q).IsHermitian) (hDpsd : ∀ q, (D q).PosSemidef)
    (hKvar : ∀ q (s : ι → ℂ),
      IsLeast {r : ℝ | ∃ u, T q *ᵥ u = s ∧ r = (star u ⬝ᵥ (A q *ᵥ u)).re}
        ((star s ⬝ᵥ (K q *ᵥ s)).re))
    (hRT : ∀ n, T n * R n = (U n)ᴴ * T (n + 1))
    (hdebit : ∀ n, (A (n + 1) + (T (n + 1))ᴴ * D n * T (n + 1)
      - (R n)ᴴ * A n * R n).PosSemidef)
    (hUu : ∀ n, U n * (U n)ᴴ = 1)
    (hsum : Summable fun j => hermLamMax (hDpsd j).1)
    (hlt : ∑' j, hermLamMax (hDpsd j).1 < hermLamMin (hKh 0)) :
    0 < hermLamMin (hKh 0) - ∑' j, hermLamMax (hDpsd j).1 ∧
    ∀ N, hermLamMin (hKh 0) - ∑' j, hermLamMax (hDpsd j).1 ≤ hermLamMin (hKh N) := by
  refine ⟨sub_pos.mpr hlt, fun N => ?_⟩
  set c0 : ℝ := hermLamMin (hKh 0) with hc0
  set cN : ℝ := ∑ j ∈ Finset.range N, hermLamMax (hDpsd j).1 with hcN
  -- the transported head keeps the floor `c0`
  have hfloor0 := (hermLamMin_floor (hKh 0)).mul_mul_conjTranspose_same (shortUprod U 0 N)
  have hPP := shortUprod_mul_conjTranspose U hUu 0 N
  have hfloor1 : (shortUprod U 0 N * K 0 * (shortUprod U 0 N)ᴴ
      - (c0 : ℂ) • 1).PosSemidef := by
    have heq : shortUprod U 0 N * (K 0 - (c0 : ℂ) • 1) * (shortUprod U 0 N)ᴴ
        = shortUprod U 0 N * K 0 * (shortUprod U 0 N)ᴴ - (c0 : ℂ) • 1 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hPP]
    rwa [heq] at hfloor0
  -- each transported debit keeps the norm ceiling
  have hceil : ∀ j, ((hermLamMax (hDpsd j).1 : ℂ) • 1
      - shortUprod U (j + 1) (N - (j + 1)) * D j
        * (shortUprod U (j + 1) (N - (j + 1)))ᴴ).PosSemidef := by
    intro j
    have h1 := (hermLamMax_ceiling (hDpsd j).1).mul_mul_conjTranspose_same
      (shortUprod U (j + 1) (N - (j + 1)))
    have hVV := shortUprod_mul_conjTranspose U hUu (j + 1) (N - (j + 1))
    have heq : shortUprod U (j + 1) (N - (j + 1))
          * ((hermLamMax (hDpsd j).1 : ℂ) • 1 - D j)
          * (shortUprod U (j + 1) (N - (j + 1)))ᴴ
        = (hermLamMax (hDpsd j).1 : ℂ) • 1
          - shortUprod U (j + 1) (N - (j + 1)) * D j
            * (shortUprod U (j + 1) (N - (j + 1)))ᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hVV]
    rwa [heq] at h1
  have hceilsum : ((cN : ℂ) • 1
      - ∑ j ∈ Finset.range N, shortUprod U (j + 1) (N - (j + 1)) * D j
        * (shortUprod U (j + 1) (N - (j + 1)))ᴴ).PosSemidef := by
    have hpsd := Matrix.posSemidef_sum (Finset.range N) (fun j _ => hceil j)
    have heq : ∑ j ∈ Finset.range N, ((hermLamMax (hDpsd j).1 : ℂ) • 1
        - shortUprod U (j + 1) (N - (j + 1)) * D j
          * (shortUprod U (j + 1) (N - (j + 1)))ᴴ)
        = (cN : ℂ) • 1 - ∑ j ∈ Finset.range N, shortUprod U (j + 1) (N - (j + 1)) * D j
          * (shortUprod U (j + 1) (N - (j + 1)))ᴴ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hcN]
      congr 2
      rw [Complex.ofReal_sum]
    rwa [heq] at hpsd
  -- combine with the telescoped comparison
  have htel := short_transport_telescope A T K R U D hKh (fun q => (hDpsd q).1)
    hKvar hRT hdebit N
  have hcomb := (htel.add hfloor1).add hceilsum
  have heq2 : K N - (shortUprod U 0 N * K 0 * (shortUprod U 0 N)ᴴ
        - ∑ j ∈ Finset.range N, shortUprod U (j + 1) (N - (j + 1)) * D j
          * (shortUprod U (j + 1) (N - (j + 1)))ᴴ)
      + (shortUprod U 0 N * K 0 * (shortUprod U 0 N)ᴴ - (c0 : ℂ) • 1)
      + ((cN : ℂ) • 1 - ∑ j ∈ Finset.range N, shortUprod U (j + 1) (N - (j + 1)) * D j
          * (shortUprod U (j + 1) (N - (j + 1)))ᴴ)
      = K N - ((c0 - cN : ℝ) : ℂ) • 1 := by
    rw [Complex.ofReal_sub, sub_smul]
    abel
  rw [heq2] at hcomb
  have hbound := le_hermLamMin_of_loewner (hKh N) hcomb
  have hpartial : cN ≤ ∑' j, hermLamMax (hDpsd j).1 :=
    Summable.sum_le_tsum (Finset.range N) (fun j _ => hermLamMax_nonneg (hDpsd j)) hsum
  linarith

end ShortTransport

/-! ### `thm:GT-exact-trace-dynamic-memory`

The local clock generator `𝓛 = [[A, B^*], [B, C]] ⪰ ρI` (ρ > 0) on the
retained/hidden split.  We prove: the traced form is the attained
infimum over hidden completions and equals the Schur form
`𝓢 = A - B^*C⁻¹B` (ET.15, `dyn_traced_isLeast`); `𝓢 ⪰ ρI` (ET.16); the
exact Green identity `⟨f, 𝓛⁻¹ f⟩ = ⟨f, 𝓢⁻¹ f⟩` (ET.17, `dyn_green`);
associativity of nested tracing (`dyn_nested_trace_assoc`): tracing the
outer hidden block and then the inner one equals the one-shot trace of
the reassociated operator; the four-fold reducing equivalence (ET.18);
and the dynamic-memory angle bound (ET.19–ET.20) with
`Θ_dyn = A^{-1/2} B^*C⁻¹B A^{-1/2}` built from the spectral square root,
including the noncollapse consequence of `θ* < 1`.  The closing remark
that a summable memory stock may replace the angle bound in the
source-short recursion is a pointer to
`thm:GT-source-short-cutoff-transport` and carries no separate claim. -/

section DynamicMemory

variable {h y : Type*} [Fintype h] [Fintype y] [DecidableEq h] [DecidableEq y]

/-- A window `M ⪰ ρI` forces `M` Hermitian. -/
theorem window_isHermitian {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    {ρ : ℝ} (hwin : (M - (ρ : ℂ) • 1).PosSemidef) : M.IsHermitian := by
  have hherm := hwin.1
  rw [Matrix.IsHermitian, conjTranspose_sub, conjTranspose_smul, conjTranspose_one] at hherm
  rw [Complex.star_def, Complex.conj_ofReal] at hherm
  exact sub_left_inj.mp hherm

/-- A window `M ⪰ ρI` bounds the quadratic form below by `ρ‖z‖²`. -/
theorem window_floor_bound {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    {ρ : ℝ} (hwin : (M - (ρ : ℂ) • 1).PosSemidef) (z : n → ℂ) :
    ρ * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re := by
  have hform := re_form_nonneg hwin z
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    star_dot_self_eq_sum_sq] at hform
  simp only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hform
  linarith

/-- A window `M ⪰ ρI` with `ρ > 0` forces `M ≻ 0`. -/
theorem window_posDef {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    {ρ : ℝ} (hρ : 0 < ρ) (hwin : (M - (ρ : ℂ) • 1).PosSemidef) : M.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (window_isHermitian hwin) fun z hz => ?_
  have hbound := window_floor_bound hwin z
  have hnorm : 0 < ∑ i, ‖z i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ i, ?_⟩
    have : z i ≠ 0 := hi
    positivity
  have hre : 0 < (star z ⬝ᵥ (M *ᵥ z)).re := lt_of_lt_of_le (by positivity) hbound
  rw [hermitian_form_ofReal (window_isHermitian hwin) z]
  exact_mod_cast Complex.zero_lt_real.mpr hre

omit [DecidableEq h] [DecidableEq y] in
/-- Quadratic form of the clock on a purely hidden vector. -/
theorem dyn_corner_bottom (A : Matrix h h ℂ) (B : Matrix y h ℂ) (C : Matrix y y ℂ)
    (yv : y → ℂ) :
    star (Sum.elim (0 : h → ℂ) yv) ⬝ᵥ (fromBlocks A Bᴴ B C *ᵥ Sum.elim (0 : h → ℂ) yv)
      = star yv ⬝ᵥ (C *ᵥ yv) := by
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, zero_add]
  rw [star_sum_elim, dotProduct_sum_elim, star_zero, zero_dotProduct, zero_add]

/-- The hidden block of a windowed clock is positive definite. -/
theorem dyn_hidden_posDef {A : Matrix h h ℂ} {B : Matrix y h ℂ} {C : Matrix y y ℂ}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hwin : (fromBlocks A Bᴴ B C - (ρ : ℂ) • 1).PosSemidef) : C.PosDef := by
  have hMh := window_isHermitian hwin
  have hCh : C.IsHermitian := (isHermitian_fromBlocks_iff.mp hMh).2.2.2
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hCh fun yv hyv => ?_
  have hz : (Sum.elim (0 : h → ℂ) yv) ≠ 0 := by
    intro hcon
    apply hyv
    funext i
    have := congrFun hcon (Sum.inr i)
    simpa using this
  have := (window_posDef hρ hwin).dotProduct_mulVec_pos hz
  rwa [dyn_corner_bottom A B C yv] at this

/-- The traced Schur response `𝓢 = A - B^*C⁻¹B` (ET.16). -/
noncomputable def dynSchur (A : Matrix h h ℂ) (B : Matrix y h ℂ) (C : Matrix y y ℂ) :
    Matrix h h ℂ :=
  A - Bᴴ * C⁻¹ * B

omit [DecidableEq h] in
/-- **(ET.15)** The terminal traced form: the attained least clock energy
over hidden completions of a retained writer `f` is the Schur form
`⟨f, 𝓢 f⟩`. -/
theorem dyn_traced_isLeast {A : Matrix h h ℂ} {B : Matrix y h ℂ} {C : Matrix y y ℂ}
    (hC : C.PosDef) (f : h → ℂ) :
    IsLeast {r : ℝ | ∃ hid : y → ℂ, r = (star (Sum.elim f hid)
        ⬝ᵥ (fromBlocks A Bᴴ B C *ᵥ Sum.elim f hid)).re}
      ((star f ⬝ᵥ (dynSchur A B C *ᵥ f)).re) := by
  constructor
  · refine ⟨-((C⁻¹ * B) *ᵥ f), ?_⟩
    rw [feshbach_square A B hC f _]
    have hzero : (C⁻¹ * B) *ᵥ f + -((C⁻¹ * B) *ᵥ f) = 0 := add_neg_cancel _
    rw [hzero, mulVec_zero, dotProduct_zero, zero_add]
    rfl
  · rintro r ⟨hid, rfl⟩
    rw [feshbach_square A B hC f hid]
    have hC0 := re_form_nonneg hC.posSemidef ((C⁻¹ * B) *ᵥ f + hid)
    simp only [Complex.add_re]
    have hS : (star f ⬝ᵥ (dynSchur A B C *ᵥ f)).re
        = (star f ⬝ᵥ ((A - Bᴴ * C⁻¹ * B) *ᵥ f)).re := rfl
    rw [hS]
    linarith

/-- **(ET.16)** The traced response keeps the clock window:
`𝓢 ⪰ ρI` (and is Hermitian). -/
theorem dyn_schur_floor {A : Matrix h h ℂ} {B : Matrix y h ℂ} {C : Matrix y y ℂ}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hwin : (fromBlocks A Bᴴ B C - (ρ : ℂ) • 1).PosSemidef) :
    (dynSchur A B C - (ρ : ℂ) • 1).PosSemidef := by
  have hC := dyn_hidden_posDef hρ hwin
  have hMh := window_isHermitian hwin
  have hAh : A.IsHermitian := (isHermitian_fromBlocks_iff.mp hMh).1
  have hSh : (dynSchur A B C).IsHermitian :=
    hAh.sub (isHermitian_conjTranspose_mul_mul B hC.inv.1)
  refine posSemidef_of_re_form (hSh.sub ?_) fun f => ?_
  · rw [Matrix.IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  · have hval : (star f ⬝ᵥ (dynSchur A B C *ᵥ f)).re
        = (star (Sum.elim f (-((C⁻¹ * B) *ᵥ f)))
            ⬝ᵥ (fromBlocks A Bᴴ B C *ᵥ Sum.elim f (-((C⁻¹ * B) *ᵥ f)))).re := by
      rw [feshbach_square A B hC f _]
      have hzero : (C⁻¹ * B) *ᵥ f + -((C⁻¹ * B) *ᵥ f) = 0 := add_neg_cancel _
      rw [hzero, mulVec_zero, dotProduct_zero, zero_add]
      rfl
    have hbound := window_floor_bound hwin (Sum.elim f (-((C⁻¹ * B) *ᵥ f)))
    have hsplit : ∑ i : h ⊕ y, ‖(Sum.elim f (-((C⁻¹ * B) *ᵥ f))) i‖ ^ 2
        = ∑ i : h, ‖f i‖ ^ 2 + ∑ i : y, ‖(-((C⁻¹ * B) *ᵥ f)) i‖ ^ 2 := by
      rw [Fintype.sum_sum_type]
      rfl
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
      star_dot_self_eq_sum_sq]
    simp only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    rw [hval]
    rw [hsplit] at hbound
    have hyn : 0 ≤ ∑ i : y, ‖(-((C⁻¹ * B) *ᵥ f)) i‖ ^ 2 := by positivity
    nlinarith [hbound, mul_nonneg hρ.le hyn]

/-- The traced response of a windowed clock is positive definite. -/
theorem dyn_schur_posDef {A : Matrix h h ℂ} {B : Matrix y h ℂ} {C : Matrix y y ℂ}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hwin : (fromBlocks A Bᴴ B C - (ρ : ℂ) • 1).PosSemidef) :
    (dynSchur A B C).PosDef :=
  window_posDef hρ (dyn_schur_floor hρ hwin)

/-- **(ET.17)** The exact Green identity
`⟨f ⊕ 0, 𝓛⁻¹ (f ⊕ 0)⟩ = ⟨f, 𝓢⁻¹ f⟩`. -/
theorem dyn_green {A : Matrix h h ℂ} {B : Matrix y h ℂ} {C : Matrix y y ℂ}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hwin : (fromBlocks A Bᴴ B C - (ρ : ℂ) • 1).PosSemidef) (f : h → ℂ) :
    star (Sum.elim f (0 : y → ℂ)) ⬝ᵥ ((fromBlocks A Bᴴ B C)⁻¹ *ᵥ Sum.elim f (0 : y → ℂ))
      = star f ⬝ᵥ ((dynSchur A B C)⁻¹ *ᵥ f) := by
  have hC := dyn_hidden_posDef hρ hwin
  have hS := dyn_schur_posDef hρ hwin
  have hM := window_posDef hρ hwin
  have htop : A * (dynSchur A B C)⁻¹ - Bᴴ * (C⁻¹ * B * (dynSchur A B C)⁻¹) = 1 := by
    have h1 : Bᴴ * (C⁻¹ * B * (dynSchur A B C)⁻¹)
        = Bᴴ * C⁻¹ * B * (dynSchur A B C)⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [h1, ← Matrix.sub_mul]
    exact posDef_mul_inv_cancel hS
  have hbot : B * (dynSchur A B C)⁻¹ - C * (C⁻¹ * B * (dynSchur A B C)⁻¹) = 0 := by
    simp only [← Matrix.mul_assoc]
    rw [posDef_mul_inv_cancel hC, Matrix.one_mul, sub_self]
  have hLz : fromBlocks A Bᴴ B C
      *ᵥ Sum.elim ((dynSchur A B C)⁻¹ *ᵥ f) (-((C⁻¹ * B * (dynSchur A B C)⁻¹) *ᵥ f))
      = Sum.elim f (0 : y → ℂ) := by
    rw [fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    congr 1
    · rw [Matrix.mulVec_neg, mulVec_mulVec, mulVec_mulVec, ← sub_eq_add_neg, ← sub_mulVec,
        htop, one_mulVec]
    · rw [Matrix.mulVec_neg, mulVec_mulVec, mulVec_mulVec, ← sub_eq_add_neg, ← sub_mulVec,
        hbot, zero_mulVec]
  have hinv : (fromBlocks A Bᴴ B C)⁻¹ *ᵥ Sum.elim f (0 : y → ℂ)
      = Sum.elim ((dynSchur A B C)⁻¹ *ᵥ f) (-((C⁻¹ * B * (dynSchur A B C)⁻¹) *ᵥ f)) := by
    rw [← hLz, mulVec_mulVec, posDef_inv_mul_cancel hM, one_mulVec]
  rw [hinv, star_sum_elim, dotProduct_sum_elim, star_zero, zero_dotProduct, add_zero]

omit [DecidableEq h] in
/-- **(ET.18)** The dynamic-memory alternative: the retained subspace is
invariant under the clock iff `B = 0` iff `B^*C⁻¹B = 0` iff `𝓢 = A`. -/
theorem dyn_reducing_iff {A : Matrix h h ℂ} {B : Matrix y h ℂ} {C : Matrix y y ℂ}
    (hC : C.PosDef) :
    ((∀ x : h → ℂ, (fromBlocks A Bᴴ B C *ᵥ Sum.elim x (0 : y → ℂ)) ∘ Sum.inr = 0)
        ↔ B = 0) ∧
    (B = 0 ↔ Bᴴ * C⁻¹ * B = 0) ∧
    (Bᴴ * C⁻¹ * B = 0 ↔ dynSchur A B C = A) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hinv
      rw [ext_iff_mulVec]
      intro x
      have := hinv x
      rw [fromBlocks_mulVec] at this
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, add_zero] at this
      rw [zero_mulVec]
      exact this
    · intro hB x
      rw [hB]
      funext i
      rw [fromBlocks_mulVec]
      simp
  · constructor
    · intro hB
      rw [hB, conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
    · intro hzero
      rw [ext_iff_mulVec]
      intro x
      rw [zero_mulVec]
      have hform : star x ⬝ᵥ ((Bᴴ * C⁻¹ * B) *ᵥ x) = 0 := by
        rw [hzero, zero_mulVec, dotProduct_zero]
      have hmove : star x ⬝ᵥ ((Bᴴ * C⁻¹ * B) *ᵥ x)
          = star (B *ᵥ x) ⬝ᵥ (C⁻¹ *ᵥ (B *ᵥ x)) := by
        rw [← mulVec_mulVec, ← mulVec_mulVec, adjoint_dot, conjTranspose_conjTranspose]
      rw [hmove] at hform
      by_contra hBx
      exact (hC.inv.dotProduct_mulVec_pos hBx).ne' hform
  · constructor
    · intro hzero
      rw [dynSchur, hzero, sub_zero]
    · intro hS
      have := sub_eq_self.mp hS
      exact this

omit [DecidableEq h] [DecidableEq y] in
/-- **(ET.18, complement half)** The hidden subspace is invariant iff
`B = 0`: with `dyn_reducing_iff` this makes the retained subspace
genuinely reducing, not merely invariant, exactly when `B = 0`. -/
theorem dyn_reducing_compl_iff {A : Matrix h h ℂ} {B : Matrix y h ℂ} {C : Matrix y y ℂ} :
    (∀ yv : y → ℂ,
      (fromBlocks A Bᴴ B C *ᵥ Sum.elim (0 : h → ℂ) yv) ∘ Sum.inl = 0) ↔ B = 0 := by
  constructor
  · intro hinv
    have hBH : Bᴴ = 0 := by
      rw [ext_iff_mulVec]
      intro yv
      have hcomp := hinv yv
      rw [fromBlocks_mulVec] at hcomp
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, zero_add] at hcomp
      rw [zero_mulVec]
      exact hcomp
    calc B = Bᴴᴴ := (conjTranspose_conjTranspose B).symm
      _ = 0 := by rw [hBH, conjTranspose_zero]
  · intro hB yv
    rw [hB]
    funext i
    rw [fromBlocks_mulVec]
    simp

/-- The dynamic-memory operator
`Θ_dyn = A^{-1/2} B^*C⁻¹B A^{-1/2}` (ET.19). -/
noncomputable def dynTheta {A : Matrix h h ℂ} (hA : A.IsHermitian) (B : Matrix y h ℂ)
    (C : Matrix y y ℂ) : Matrix h h ℂ :=
  psdInvSqrt hA * (Bᴴ * C⁻¹ * B) * psdInvSqrt hA

/-- Undressing the dynamic-memory operator:
`A^{1/2} Θ_dyn A^{1/2} = B^*C⁻¹B`. -/
theorem dynTheta_conj {A : Matrix h h ℂ} (hA : A.PosDef) (B : Matrix y h ℂ)
    (C : Matrix y y ℂ) :
    psdSqrt hA.1 * dynTheta hA.1 B C * psdSqrt hA.1 = Bᴴ * C⁻¹ * B := by
  unfold dynTheta
  calc psdSqrt hA.1 * (psdInvSqrt hA.1 * (Bᴴ * C⁻¹ * B) * psdInvSqrt hA.1) * psdSqrt hA.1
      = (psdSqrt hA.1 * psdInvSqrt hA.1) * (Bᴴ * C⁻¹ * B)
          * (psdInvSqrt hA.1 * psdSqrt hA.1) := by
        simp only [Matrix.mul_assoc]
    _ = Bᴴ * C⁻¹ * B := by
        rw [psdSqrt_mul_psdInvSqrt hA, psdInvSqrt_mul_psdSqrt hA, Matrix.one_mul,
          Matrix.mul_one]

/-- **(ET.19–ET.20)** The dynamic-memory angle bound: if the normalized
memory operator satisfies `⟨w, Θ w⟩ ≤ θ⋆ ⟨w, w⟩` on the lifted source
range `A^{1/2} Ran J` with `θ⋆ < 1`, then on `Ran J` the traced response
dominates `(1-θ⋆) A`, and it is strictly positive wherever the `A`-form
is. -/
theorem dyn_angle_bound {A : Matrix h h ℂ} {B : Matrix y h ℂ} {C : Matrix y y ℂ}
    {w : Type*} [Fintype w] (hA : A.PosDef) (J : Matrix h w ℂ) {θ : ℝ} (hθ : θ < 1)
    (hang : ∀ v : w → ℂ,
      (star (psdSqrt hA.1 *ᵥ (J *ᵥ v))
        ⬝ᵥ (dynTheta hA.1 B C *ᵥ (psdSqrt hA.1 *ᵥ (J *ᵥ v)))).re
      ≤ θ * (star (psdSqrt hA.1 *ᵥ (J *ᵥ v)) ⬝ᵥ (psdSqrt hA.1 *ᵥ (J *ᵥ v))).re) :
    ∀ v : w → ℂ,
      (1 - θ) * (star (J *ᵥ v) ⬝ᵥ (A *ᵥ (J *ᵥ v))).re
        ≤ (star (J *ᵥ v) ⬝ᵥ (dynSchur A B C *ᵥ (J *ᵥ v))).re ∧
      (0 < (star (J *ᵥ v) ⬝ᵥ (A *ᵥ (J *ᵥ v))).re
        → 0 < (star (J *ᵥ v) ⬝ᵥ (dynSchur A B C *ᵥ (J *ᵥ v))).re) := by
  intro v
  have hsqh : (psdSqrt hA.1)ᴴ = psdSqrt hA.1 := (psdSqrt_posSemidef hA.1).1
  have hmove : ∀ M : Matrix h h ℂ,
      star (psdSqrt hA.1 *ᵥ (J *ᵥ v)) ⬝ᵥ (M *ᵥ (psdSqrt hA.1 *ᵥ (J *ᵥ v)))
        = star (J *ᵥ v) ⬝ᵥ ((psdSqrt hA.1 * M * psdSqrt hA.1) *ᵥ (J *ᵥ v)) := by
    intro M
    rw [← conj_form_move (psdSqrt hA.1) M (J *ᵥ v), hsqh]
  have hang' := hang v
  rw [hmove (dynTheta hA.1 B C), dynTheta_conj hA B C] at hang'
  have hnorm : (star (psdSqrt hA.1 *ᵥ (J *ᵥ v)) ⬝ᵥ (psdSqrt hA.1 *ᵥ (J *ᵥ v))).re
      = (star (J *ᵥ v) ⬝ᵥ (A *ᵥ (J *ᵥ v))).re := by
    have h1 : star (J *ᵥ v) ⬝ᵥ ((psdSqrt hA.1 * psdSqrt hA.1) *ᵥ (J *ᵥ v))
        = star (psdSqrt hA.1 *ᵥ (J *ᵥ v)) ⬝ᵥ (psdSqrt hA.1 *ᵥ (J *ᵥ v)) := by
      rw [← mulVec_mulVec, adjoint_dot, hsqh]
    rw [← h1, psdSqrt_mul_self hA.posSemidef]
  rw [hnorm] at hang'
  have hSform : (star (J *ᵥ v) ⬝ᵥ (dynSchur A B C *ᵥ (J *ᵥ v))).re
      = (star (J *ᵥ v) ⬝ᵥ (A *ᵥ (J *ᵥ v))).re
        - (star (J *ᵥ v) ⬝ᵥ ((Bᴴ * C⁻¹ * B) *ᵥ (J *ᵥ v))).re := by
    rw [dynSchur, sub_mulVec, dotProduct_sub, Complex.sub_re]
  constructor
  · rw [hSform]
    nlinarith [hang']
  · intro hpos
    rw [hSform]
    nlinarith [hang', mul_lt_mul_of_pos_right hθ hpos]

/-- The upper-right block of a Hermitian operator is the adjoint of the
lower-left one. -/
theorem toBlocks_conj {n1 n2 : Type*} (M : Matrix (n1 ⊕ n2) (n1 ⊕ n2) ℂ)
    (hM : M.IsHermitian) : M.toBlocks₁₂ = (M.toBlocks₂₁)ᴴ := by
  ext i j
  have := congrFun (congrFun hM.eq (Sum.inl i)) (Sum.inr j)
  simp only [Matrix.conjTranspose_apply] at this
  simpa [Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.conjTranspose_apply] using this.symm

/-- Decomposition of a Hermitian operator into its retained/hidden
blocks. -/
theorem herm_block_decompose {n1 n2 : Type*} (M : Matrix (n1 ⊕ n2) (n1 ⊕ n2) ℂ)
    (hM : M.IsHermitian) :
    M = fromBlocks M.toBlocks₁₁ (M.toBlocks₂₁)ᴴ M.toBlocks₂₁ M.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [toBlocks_conj M hM]

/-- Reassociation of a doubly split writer. -/
theorem elim_comp_sumAssoc {α h' y1 y2 : Type*} (f : h' → α) (w : y1 ⊕ y2 → α) :
    Sum.elim f w ∘ (Equiv.sumAssoc h' y1 y2)
      = Sum.elim (Sum.elim f (w ∘ Sum.inl)) (w ∘ Sum.inr) := by
  funext z
  rcases z with (z | z) | z <;> rfl

/-- **(ET.17, associativity of nested tracing)** Tracing the outer hidden
block `y₂` and then the inner one `y₁` gives exactly the one-shot traced
response over `y₁ ⊕ y₂` of the reassociated clock. -/
theorem dyn_nested_trace_assoc {y1 y2 : Type*} [Fintype y1] [Fintype y2]
    [DecidableEq y1] [DecidableEq y2]
    (A : Matrix h h ℂ) (B1 : Matrix y1 h ℂ) (C1 : Matrix y1 y1 ℂ)
    (B2 : Matrix y2 (h ⊕ y1) ℂ) (C2 : Matrix y2 y2 ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hwin : (fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2
      - (ρ : ℂ) • 1).PosSemidef) :
    dynSchur (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₁₁
        (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₂₁
        (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₂₂
      = dynSchur
          (((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
            (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm).toBlocks₁₁)
          (((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
            (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm).toBlocks₂₁)
          (((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
            (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm).toBlocks₂₂) := by
  have hC2 : C2.PosDef := dyn_hidden_posDef hρ hwin
  -- stage-one traced response and its window
  have hS1win := dyn_schur_floor hρ hwin
  have hS1h := window_isHermitian hS1win
  have hS1dec := herm_block_decompose _ hS1h
  have hS1win' : (fromBlocks (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₁₁
      ((dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₂₁)ᴴ
      (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₂₁
      (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₂₂
      - (ρ : ℂ) • 1).PosSemidef := by
    rw [← hS1dec]
    exact hS1win
  have hC1' := dyn_hidden_posDef hρ hS1win'
  -- the reassociated clock and its window
  have hMwin' : ((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
      (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm
      - (ρ : ℂ) • 1).PosSemidef := by
    have hsub := (posSemidef_submatrix_equiv (Equiv.sumAssoc h y1 y2).symm).mpr hwin
    have heq : (fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2
        - (ρ : ℂ) • 1).submatrix (Equiv.sumAssoc h y1 y2).symm
          (Equiv.sumAssoc h y1 y2).symm
        = (fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
            (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm
          - (ρ : ℂ) • 1 := by
      have h1 : ((ρ : ℂ) • (1 : Matrix ((h ⊕ y1) ⊕ y2) ((h ⊕ y1) ⊕ y2) ℂ)).submatrix
          (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm
          = (ρ : ℂ) • 1 := by
        have h2 : ((1 : Matrix ((h ⊕ y1) ⊕ y2) ((h ⊕ y1) ⊕ y2) ℂ)).submatrix
            (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm = 1 :=
          Matrix.submatrix_one_equiv _
        rw [← h2]
        rfl
      rw [← h1]
      rfl
    rwa [heq] at hsub
  have hM'h := window_isHermitian hMwin'
  have hM'dec := herm_block_decompose _ hM'h
  have hM'win' : (fromBlocks
      (((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
        (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm).toBlocks₁₁)
      ((((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
        (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm).toBlocks₂₁)ᴴ)
      (((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
        (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm).toBlocks₂₁)
      (((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
        (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm).toBlocks₂₂)
      - (ρ : ℂ) • 1).PosSemidef := by
    rw [← hM'dec]
    exact hMwin'
  have hC2' := dyn_hidden_posDef hρ hM'win'
  -- both traced responses are Hermitian
  have hS2h := window_isHermitian (dyn_schur_floor hρ hS1win')
  have hSosh := window_isHermitian (dyn_schur_floor hρ hM'win')
  refine hermitian_eq_of_re_forms hS2h hSosh fun f => ?_
  -- the nested least value
  have h2 := dyn_traced_isLeast
    (A := (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₁₁)
    (B := (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₂₁) hC1' f
  rw [← hS1dec] at h2
  -- the one-shot least value
  have hos := dyn_traced_isLeast
    (A := ((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
      (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm).toBlocks₁₁)
    (B := ((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
      (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm).toBlocks₂₁) hC2' f
  rw [← hM'dec] at hos
  -- the inner-stage least value at each partially completed writer
  have h1 : ∀ g : (h ⊕ y1) → ℂ,
      IsLeast {r : ℝ | ∃ hid : y2 → ℂ, r = (star (Sum.elim g hid)
          ⬝ᵥ (fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2 *ᵥ Sum.elim g hid)).re}
        ((star g ⬝ᵥ (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2 *ᵥ g)).re) :=
    fun g => dyn_traced_isLeast hC2 g
  -- transport of forms along the reassociation
  have htrans : ∀ w : (y1 ⊕ y2) → ℂ,
      star (Sum.elim f w) ⬝ᵥ ((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
          (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm
        *ᵥ Sum.elim f w)
      = star (Sum.elim (Sum.elim f (w ∘ Sum.inl)) (w ∘ Sum.inr))
          ⬝ᵥ (fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2
            *ᵥ Sum.elim (Sum.elim f (w ∘ Sum.inl)) (w ∘ Sum.inr)) := by
    intro w
    rw [form_submatrix_equiv _ (Equiv.sumAssoc h y1 y2).symm (Sum.elim f w)]
    rw [Equiv.symm_symm, elim_comp_sumAssoc]
  -- the nested least value is also the least of the one-shot set
  have hos2 : IsLeast {r : ℝ | ∃ w : (y1 ⊕ y2) → ℂ,
      r = (star (Sum.elim f w) ⬝ᵥ ((fromBlocks (fromBlocks A B1ᴴ B1 C1) B2ᴴ B2 C2).submatrix
          (Equiv.sumAssoc h y1 y2).symm (Equiv.sumAssoc h y1 y2).symm
        *ᵥ Sum.elim f w)).re}
      ((star f ⬝ᵥ (dynSchur (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₁₁
          (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₂₁
          (dynSchur (fromBlocks A B1ᴴ B1 C1) B2 C2).toBlocks₂₂ *ᵥ f)).re) := by
    constructor
    · obtain ⟨h1v, hh1⟩ := h2.1
      obtain ⟨h2v, hh2⟩ := (h1 (Sum.elim f h1v)).1
      refine ⟨Sum.elim h1v h2v, ?_⟩
      have ht := htrans (Sum.elim h1v h2v)
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at ht
      rw [hh1, hh2]
      exact (congrArg Complex.re ht).symm
    · rintro r ⟨w, rfl⟩
      have ht := htrans w
      have hlow1 := (h1 (Sum.elim f (w ∘ Sum.inl))).2 ⟨w ∘ Sum.inr, rfl⟩
      have hlow2 := h2.2 ⟨w ∘ Sum.inl, rfl⟩
      rw [congrArg Complex.re ht]
      exact le_trans hlow2 hlow1
  exact IsLeast.unique hos2 hos

end DynamicMemory

end NCG

