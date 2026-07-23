/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix

/-!
# The primitive transfer selects a unique faithful stationary weight

Covers `thm:primitive-stationary-weight` from
`manuscripts/renewal_emergence/renewal_emergence.tex`: a
trace-preserving, positivity-preserving, star-preserving linear map
`T` on `M_n(𝕜)` that is *primitive* (some power `T^m` sends every
nonzero positive-semidefinite matrix to a positive-definite one) has

* a stationary density matrix `ρ⋆` (existence via Cesàro averages and
  compactness of the density simplex),
* which is faithful (`ρ⋆ > 0`, via primitivity),
* and unique, and moreover
* `T` mixes at an exponential rate in the Hermitian trace norm:
  there is `c < 1` with `‖T^{km} ρ − ρ⋆‖₁ ≤ c^k ‖ρ − ρ⋆‖₁` for every
  density `ρ` and every `k`.

The trace norm of a Hermitian matrix is implemented as the sum of the
absolute values of its eigenvalues, and the required Jordan
decomposition `X = X₊ − X₋`, the sign operator, and square roots are
all built from the bare functional calculus
`Matrix.IsHermitian.cfc` (conjugation of a diagonal by the
eigenvector unitary), for which we prove a small toolkit
(multiplicativity, positivity, traces, entry bounds).
-/

namespace NCG.Upstream.PrimitiveWeight

open Matrix Unitary Filter Finset
open scoped ComplexOrder

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ## A toolkit for the bare Hermitian functional calculus -/

section Cfc

variable {X : Matrix (Fin n) (Fin n) 𝕜} (hX : X.IsHermitian)

theorem cfc_mul (f g : ℝ → ℝ) :
    hX.cfc f * hX.cfc g = hX.cfc fun x => f x * g x := by
  simp only [Matrix.IsHermitian.cfc]
  rw [← map_mul, diagonal_mul_diagonal]
  congr 1
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [Function.comp]
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem cfc_add (f g : ℝ → ℝ) :
    hX.cfc f + hX.cfc g = hX.cfc fun x => f x + g x := by
  simp only [Matrix.IsHermitian.cfc]
  rw [← map_add, diagonal_add]
  congr 1
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [Function.comp]
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem cfc_sub (f g : ℝ → ℝ) :
    hX.cfc f - hX.cfc g = hX.cfc fun x => f x - g x := by
  simp only [Matrix.IsHermitian.cfc]
  rw [← map_sub, diagonal_sub]
  congr 1
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [Function.comp]
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem cfc_id' : hX.cfc id = X := by
  conv_rhs => rw [hX.spectral_theorem]
  simp only [Matrix.IsHermitian.cfc, Function.id_comp]

theorem cfc_congr {f g : ℝ → ℝ}
    (h : ∀ i, f (hX.eigenvalues i) = g (hX.eigenvalues i)) :
    hX.cfc f = hX.cfc g := by
  simp only [Matrix.IsHermitian.cfc]
  congr 1
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [Function.comp, h i]
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem cfc_const (c : ℝ) :
    hX.cfc (fun _ => c) = (c : 𝕜) • 1 := by
  simp only [Matrix.IsHermitian.cfc]
  have hdiag : (diagonal (RCLike.ofReal ∘ (fun _ => c) ∘ hX.eigenvalues)
      : Matrix (Fin n) (Fin n) 𝕜) = (c : 𝕜) • 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Function.comp]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  rw [hdiag, map_smul, map_one]

theorem cfc_isHermitian (f : ℝ → ℝ) : (hX.cfc f).IsHermitian := by
  change (hX.cfc f)ᴴ = hX.cfc f
  simp only [Matrix.IsHermitian.cfc]
  rw [← star_eq_conjTranspose, ← map_star]
  congr 1
  rw [star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1
  funext i
  simp [Function.comp, RCLike.conj_ofReal]

theorem cfc_posSemidef {f : ℝ → ℝ}
    (hf : ∀ i, 0 ≤ f (hX.eigenvalues i)) :
    (hX.cfc f).PosSemidef := by
  simp only [Matrix.IsHermitian.cfc, conjStarAlgAut_apply]
  have hu : IsUnit
      (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) :=
    isUnit_coe
  refine (hu.posSemidef_star_right_conjugate_iff).mpr ?_
  refine posSemidef_diagonal_iff.mpr fun i => ?_
  simpa [Function.comp] using
    (RCLike.ofReal_nonneg (K := 𝕜)).mpr (hf i)

theorem cfc_trace (f : ℝ → ℝ) :
    (hX.cfc f).trace = ((∑ i, f (hX.eigenvalues i) : ℝ) : 𝕜) := by
  simp only [Matrix.IsHermitian.cfc, conjStarAlgAut_apply]
  rw [trace_mul_cycle]
  have hu : star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜)
      * (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2
  rw [hu, one_mul, trace_diagonal, RCLike.ofReal_sum]
  simp [Function.comp]

/-- Multiplying a functional-calculus element by the matrix itself. -/
theorem cfc_mul_self (f : ℝ → ℝ) :
    hX.cfc f * X = hX.cfc fun x => f x * x := by
  have h1 := cfc_mul hX f id
  rw [cfc_id' hX] at h1
  exact h1

/-! ### Entry bounds via the eigenvector unitary -/

theorem unitary_entry_norm_le (u : Matrix.unitaryGroup (Fin n) 𝕜)
    (i k : Fin n) : ‖(u : Matrix (Fin n) (Fin n) 𝕜) i k‖ ≤ 1 := by
  have hmem : (u : Matrix (Fin n) (Fin n) 𝕜)
      * star (u : Matrix (Fin n) (Fin n) 𝕜) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp u.2
  have h1 : ((u : Matrix (Fin n) (Fin n) 𝕜)
      * star (u : Matrix (Fin n) (Fin n) 𝕜)) i i = 1 := by
    rw [hmem]
    simp
  rw [Matrix.mul_apply] at h1
  have h2 : ∀ l, (u : Matrix (Fin n) (Fin n) 𝕜) i l
      * star (u : Matrix (Fin n) (Fin n) 𝕜) l i
      = ((‖(u : Matrix (Fin n) (Fin n) 𝕜) i l‖ ^ 2 : ℝ) : 𝕜) := by
    intro l
    rw [Matrix.star_apply, RCLike.star_def, RCLike.mul_conj]
    norm_cast
  rw [Finset.sum_congr rfl fun l _ => h2 l, ← RCLike.ofReal_sum] at h1
  have h3 : (∑ l, ‖(u : Matrix (Fin n) (Fin n) 𝕜) i l‖ ^ 2) = 1 := by
    have := congrArg RCLike.re h1
    simpa using this
  have h4 : ‖(u : Matrix (Fin n) (Fin n) 𝕜) i k‖ ^ 2 ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum
      (fun l _ => sq_nonneg ‖(u : Matrix (Fin n) (Fin n) 𝕜) i l‖)
      (Finset.mem_univ k)
  nlinarith [norm_nonneg ((u : Matrix (Fin n) (Fin n) 𝕜) i k)]

theorem cfc_entry_norm_le (f : ℝ → ℝ) (i j : Fin n) :
    ‖hX.cfc f i j‖ ≤ ∑ k, |f (hX.eigenvalues k)| := by
  have hentry : hX.cfc f i j
      = ∑ k, (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) i k
          * ((f (hX.eigenvalues k) : ℝ) : 𝕜)
          * star ((hX.eigenvectorUnitary
              : Matrix (Fin n) (Fin n) 𝕜) j k) := by
    simp only [Matrix.IsHermitian.cfc, conjStarAlgAut_apply]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.star_apply]
    simp [Function.comp]
  rw [hentry]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, norm_mul, norm_star, RCLike.norm_ofReal]
  have h1 := unitary_entry_norm_le hX.eigenvectorUnitary i k
  have h2 := unitary_entry_norm_le hX.eigenvectorUnitary j k
  have h3 := abs_nonneg (f (hX.eigenvalues k))
  have h4 := norm_nonneg
    ((hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) i k)
  have hb1 : ‖(hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) i k‖
      * |f (hX.eigenvalues k)| ≤ |f (hX.eigenvalues k)| :=
    mul_le_of_le_one_left h3 h1
  have hb2 : ‖(hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) i k‖
      * |f (hX.eigenvalues k)|
      * ‖(hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) j k‖
      ≤ ‖(hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) i k‖
        * |f (hX.eigenvalues k)| :=
    mul_le_of_le_one_right (mul_nonneg h4 h3) h2
  exact le_trans hb2 hb1

end Cfc

/-! ## Jordan decomposition and the sign operator -/

section Jordan

variable {X : Matrix (Fin n) (Fin n) 𝕜}

/-- Positive part `X₊` of a Hermitian matrix. -/
noncomputable def posPart (hX : X.IsHermitian) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  hX.cfc fun x => max x 0

/-- Negative part `X₋` of a Hermitian matrix. -/
noncomputable def negPart (hX : X.IsHermitian) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  hX.cfc fun x => max (-x) 0

/-- The sign operator `sgn(X)` (with `sgn 0 = −1`, which is
harmless: it is a self-adjoint `±1`-contraction achieving the trace
norm). -/
noncomputable def signOp (hX : X.IsHermitian) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  hX.cfc fun x => if 0 < x then 1 else -1

theorem posPart_posSemidef (hX : X.IsHermitian) :
    (posPart hX).PosSemidef :=
  cfc_posSemidef hX fun _ => le_max_right _ _

theorem negPart_posSemidef (hX : X.IsHermitian) :
    (negPart hX).PosSemidef :=
  cfc_posSemidef hX fun _ => le_max_right _ _

theorem posPart_sub_negPart (hX : X.IsHermitian) :
    posPart hX - negPart hX = X := by
  unfold posPart negPart
  rw [cfc_sub]
  have hfun : (fun x : ℝ => max x 0 - max (-x) 0) = id := by
    funext x
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      simp
    · rw [max_eq_right h, max_eq_left (by linarith)]
      simp
  rw [hfun, cfc_id']

theorem trace_posPart (hX : X.IsHermitian) :
    (posPart hX).trace
      = ((∑ i, max (hX.eigenvalues i) 0 : ℝ) : 𝕜) :=
  cfc_trace hX _

theorem trace_negPart (hX : X.IsHermitian) :
    (negPart hX).trace
      = ((∑ i, max (-hX.eigenvalues i) 0 : ℝ) : 𝕜) :=
  cfc_trace hX _

theorem one_sub_signOp_posSemidef (hX : X.IsHermitian) :
    ((1 : Matrix (Fin n) (Fin n) 𝕜) - signOp hX).PosSemidef := by
  unfold signOp
  have h1 : (1 : Matrix (Fin n) (Fin n) 𝕜)
      = hX.cfc fun _ => (1 : ℝ) := by
    rw [cfc_const]
    simp
  rw [h1, cfc_sub]
  refine cfc_posSemidef hX fun i => ?_
  by_cases h : 0 < hX.eigenvalues i <;> simp [h]

theorem one_add_signOp_posSemidef (hX : X.IsHermitian) :
    ((1 : Matrix (Fin n) (Fin n) 𝕜) + signOp hX).PosSemidef := by
  unfold signOp
  have h1 : (1 : Matrix (Fin n) (Fin n) 𝕜)
      = hX.cfc fun _ => (1 : ℝ) := by
    rw [cfc_const]
    simp
  rw [h1, cfc_add]
  refine cfc_posSemidef hX fun i => ?_
  by_cases h : 0 < hX.eigenvalues i <;> simp [h]

theorem signOp_mul_self (hX : X.IsHermitian) :
    signOp hX * X = hX.cfc fun x => |x| := by
  unfold signOp
  rw [cfc_mul_self]
  refine cfc_congr hX fun i => ?_
  set x := hX.eigenvalues i
  by_cases h : 0 < x
  · rw [if_pos h, one_mul, abs_of_pos h]
  · rw [if_neg h, abs_of_nonpos (by linarith [not_lt.mp h])]
    ring

end Jordan

/-! ## The Hermitian trace norm -/

section TrNorm

/-- The trace norm of a Hermitian matrix: the sum of the absolute
values of its eigenvalues (defined as `0` on non-Hermitian input). -/
noncomputable def trNorm (X : Matrix (Fin n) (Fin n) 𝕜) : ℝ :=
  if h : X.IsHermitian then ∑ i, |h.eigenvalues i| else 0

variable {X : Matrix (Fin n) (Fin n) 𝕜}

theorem trNorm_def (hX : X.IsHermitian) :
    trNorm X = ∑ i, |hX.eigenvalues i| := dif_pos hX

theorem trNorm_nonneg (X : Matrix (Fin n) (Fin n) 𝕜) :
    0 ≤ trNorm X := by
  unfold trNorm
  split
  · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · exact le_refl 0

theorem trNorm_eq_zero_iff (hX : X.IsHermitian) :
    trNorm X = 0 ↔ X = 0 := by
  rw [trNorm_def hX]
  constructor
  · intro h
    have h1 : ∀ i ∈ Finset.univ, |hX.eigenvalues i| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        fun i _ => abs_nonneg _).mp h
    have h2 : hX.eigenvalues = 0 := by
      funext i
      exact abs_eq_zero.mp (h1 i (Finset.mem_univ i))
    exact hX.eigenvalues_eq_zero_iff.mp h2
  · intro h
    have h2 : hX.eigenvalues = 0 := hX.eigenvalues_eq_zero_iff.mpr h
    simp [h2]

/-- The trace-norm of a Hermitian matrix splits as
`tr X₊ + tr X₋`. -/
theorem trNorm_eq_re_trace_parts (hX : X.IsHermitian) :
    trNorm X = RCLike.re ((posPart hX).trace)
      + RCLike.re ((negPart hX).trace) := by
  rw [trace_posPart, trace_negPart, RCLike.ofReal_re,
    RCLike.ofReal_re, trNorm_def hX, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases le_total 0 (hX.eigenvalues i) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith),
      abs_of_nonneg h, add_zero]
  · rw [max_eq_right h, max_eq_left (by linarith),
      abs_of_nonpos h, zero_add]

/-- The trace of a positive-semidefinite matrix is nonnegative in
the `ComplexOrder` (proved through the eigenvalue sum to avoid any
ordered-algebra instances on `𝕜`). -/
theorem psd_trace_nonneg {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosSemidef) : 0 ≤ A.trace := by
  have h1 := cfc_trace hA.1 id
  rw [cfc_id'] at h1
  rw [h1]
  exact RCLike.ofReal_nonneg.mpr
    (Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i)

/-- The trace of a product of positive-semidefinite matrices is
nonnegative (in the `ComplexOrder`). -/
theorem trace_mul_psd_nonneg {P Q : Matrix (Fin n) (Fin n) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (P * Q).trace := by
  set S := hP.1.cfc Real.sqrt with hSdef
  have hSS : S * S = P := by
    rw [hSdef, cfc_mul]
    have h1 : hP.1.cfc (fun x => Real.sqrt x * Real.sqrt x)
        = hP.1.cfc id := by
      refine cfc_congr hP.1 fun i => ?_
      exact Real.mul_self_sqrt (hP.eigenvalues_nonneg i)
    rw [h1, cfc_id']
  have hSherm : S.IsHermitian := cfc_isHermitian hP.1 _
  have hcycle : (P * Q).trace = (S * Q * S).trace := by
    rw [← hSS, mul_assoc, trace_mul_comm]
  rw [hcycle]
  have hpsd : (S * Q * S).PosSemidef := by
    have h2 := hQ.mul_mul_conjTranspose_same S
    rwa [hSherm.eq] at h2
  exact psd_trace_nonneg hpsd

/-- **Dual bound**: testing a Hermitian matrix against any
self-adjoint `±1`-contraction is dominated by the trace norm. -/
theorem re_trace_mul_le_trNorm (hX : X.IsHermitian)
    {C : Matrix (Fin n) (Fin n) 𝕜}
    (hC1 : ((1 : Matrix (Fin n) (Fin n) 𝕜) - C).PosSemidef)
    (hC2 : ((1 : Matrix (Fin n) (Fin n) 𝕜) + C).PosSemidef) :
    RCLike.re ((C * X).trace) ≤ trNorm X := by
  have hPQ : C * X = C * posPart hX - C * negPart hX := by
    rw [← mul_sub, posPart_sub_negPart]
  -- tr((1−C) X₊) ≥ 0 gives re tr(C X₊) ≤ re tr X₊
  have h1 : 0 ≤ (((1 : Matrix (Fin n) (Fin n) 𝕜) - C)
      * posPart hX).trace :=
    trace_mul_psd_nonneg hC1 (posPart_posSemidef hX)
  have h1' : RCLike.re ((C * posPart hX).trace)
      ≤ RCLike.re ((posPart hX).trace) := by
    rw [sub_mul, one_mul, trace_sub] at h1
    have h2 := (RCLike.nonneg_iff.mp h1).1
    rw [map_sub] at h2
    linarith
  -- tr((1+C) X₋) ≥ 0 gives −re tr(C X₋) ≤ re tr X₋
  have h3 : 0 ≤ (((1 : Matrix (Fin n) (Fin n) 𝕜) + C)
      * negPart hX).trace :=
    trace_mul_psd_nonneg hC2 (negPart_posSemidef hX)
  have h3' : -RCLike.re ((C * negPart hX).trace)
      ≤ RCLike.re ((negPart hX).trace) := by
    rw [add_mul, one_mul, trace_add] at h3
    have h4 := (RCLike.nonneg_iff.mp h3).1
    rw [map_add] at h4
    linarith
  rw [hPQ, trace_sub, map_sub, trNorm_eq_re_trace_parts hX]
  linarith

/-- The sign operator achieves the trace norm. -/
theorem trace_signOp_mul (hX : X.IsHermitian) :
    ((signOp hX * X)).trace = ((trNorm X : ℝ) : 𝕜) := by
  rw [signOp_mul_self hX, cfc_trace, trNorm_def hX]

theorem re_trace_signOp_mul (hX : X.IsHermitian) :
    RCLike.re ((signOp hX * X).trace) = trNorm X := by
  rw [trace_signOp_mul hX, RCLike.ofReal_re]

/-- **Key decomposition bound**: if a Hermitian matrix is written as
any difference `P − Q` of positive-semidefinite matrices, its trace
norm is at most `re tr P + re tr Q`. -/
theorem trNorm_le_of_sub (hX : X.IsHermitian)
    {P Q : Matrix (Fin n) (Fin n) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hdec : X = P - Q) :
    trNorm X ≤ RCLike.re (P.trace) + RCLike.re (Q.trace) := by
  have hC1 := one_sub_signOp_posSemidef hX
  have hC2 := one_add_signOp_posSemidef hX
  -- re tr(sgn(X) P) ≤ re tr P
  have h1 : 0 ≤ (((1 : Matrix (Fin n) (Fin n) 𝕜) - signOp hX)
      * P).trace := trace_mul_psd_nonneg hC1 hP
  have h1' : RCLike.re ((signOp hX * P).trace)
      ≤ RCLike.re (P.trace) := by
    rw [sub_mul, one_mul, trace_sub] at h1
    have h2 := (RCLike.nonneg_iff.mp h1).1
    rw [map_sub] at h2
    linarith
  have h3 : 0 ≤ (((1 : Matrix (Fin n) (Fin n) 𝕜) + signOp hX)
      * Q).trace := trace_mul_psd_nonneg hC2 hQ
  have h3' : -RCLike.re ((signOp hX * Q).trace)
      ≤ RCLike.re (Q.trace) := by
    rw [add_mul, one_mul, trace_add] at h3
    have h4 := (RCLike.nonneg_iff.mp h3).1
    rw [map_add] at h4
    linarith
  have h5 : (signOp hX * P).trace - (signOp hX * Q).trace
      = ((trNorm X : ℝ) : 𝕜) := by
    rw [← trace_sub, ← mul_sub, ← hdec, trace_signOp_mul hX]
  have h6 : RCLike.re ((signOp hX * P).trace)
      - RCLike.re ((signOp hX * Q).trace) = trNorm X := by
    have h7 := congrArg RCLike.re h5
    rw [map_sub, RCLike.ofReal_re] at h7
    exact h7
  linarith

end TrNorm

/-! ## Density matrices: entry bounds, closedness, compactness -/

section Density

/-- Real-scalar rescaling of a positive-semidefinite matrix. -/
theorem posSemidef_real_smul {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (((c : ℝ) : 𝕜) • A).PosSemidef := by
  set S := hA.1.cfc Real.sqrt with hSdef
  have hSS : S * S = A := by
    rw [hSdef, cfc_mul]
    have h1 : hA.1.cfc (fun x => Real.sqrt x * Real.sqrt x)
        = hA.1.cfc id := by
      refine cfc_congr hA.1 fun i => ?_
      exact Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
    rw [h1, cfc_id']
  have hSherm : S.IsHermitian := cfc_isHermitian hA.1 _
  set B := ((Real.sqrt c : ℝ) : 𝕜) • S with hBdef
  have hBH : Bᴴ = B := by
    rw [hBdef, conjTranspose_smul, hSherm.eq]
    congr 1
    rw [RCLike.star_def, RCLike.conj_ofReal]
  have hBB : B * Bᴴ = ((c : ℝ) : 𝕜) • A := by
    rw [hBH, hBdef, smul_mul_smul_comm, hSS, ← RCLike.ofReal_mul,
      Real.mul_self_sqrt hc]
  rw [← hBB]
  exact posSemidef_self_mul_conjTranspose B

theorem entry_norm_le_trNorm {X : Matrix (Fin n) (Fin n) 𝕜}
    (hX : X.IsHermitian) (i j : Fin n) :
    ‖X i j‖ ≤ trNorm X := by
  have h := cfc_entry_norm_le hX id i j
  rw [cfc_id'] at h
  rw [trNorm_def hX]
  simpa using h

/-- The eigenvalues of a density matrix sum to `1`. -/
theorem density_sum_eigenvalues {ρ : Matrix (Fin n) (Fin n) 𝕜}
    (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∑ k, hpsd.1.eigenvalues k = 1 := by
  have h4 := cfc_trace hpsd.1 id
  rw [cfc_id', htr] at h4
  have h5 : ((∑ k, id (hpsd.1.eigenvalues k) : ℝ) : 𝕜)
      = ((1 : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_one, ← h4]
  simpa using RCLike.ofReal_inj.mp h5

theorem density_trNorm_eq_one {ρ : Matrix (Fin n) (Fin n) 𝕜}
    (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) :
    trNorm ρ = 1 := by
  rw [trNorm_def hpsd.1]
  rw [Finset.sum_congr rfl fun k _ =>
    abs_of_nonneg (hpsd.eigenvalues_nonneg k)]
  exact density_sum_eigenvalues hpsd htr

theorem density_entry_le {ρ : Matrix (Fin n) (Fin n) 𝕜}
    (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) (i j : Fin n) :
    ‖ρ i j‖ ≤ 1 := by
  have h := entry_norm_le_trNorm hpsd.1 i j
  rwa [density_trNorm_eq_one hpsd htr] at h

/-- The set of density matrices. -/
def densitySet (n : ℕ) (𝕜 : Type*) [RCLike 𝕜] :
    Set (Matrix (Fin n) (Fin n) 𝕜) :=
  {ρ | ρ.PosSemidef ∧ ρ.trace = 1}

theorem continuous_entry (i j : Fin n) :
    Continuous fun A : Matrix (Fin n) (Fin n) 𝕜 => A i j :=
  (continuous_apply j).comp (continuous_apply i)

theorem continuous_matrix_trace :
    Continuous fun A : Matrix (Fin n) (Fin n) 𝕜 => A.trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact continuous_finsetSum _ fun i _ => continuous_entry i i

theorem continuous_quadForm (x : Fin n → 𝕜) :
    Continuous fun A : Matrix (Fin n) (Fin n) 𝕜 =>
      star x ⬝ᵥ (A *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  refine continuous_finsetSum _ fun i _ =>
    Continuous.mul continuous_const ?_
  exact continuous_finsetSum _ fun j _ =>
    Continuous.mul (continuous_entry i j) continuous_const

theorem isClosed_posSemidef :
    IsClosed {A : Matrix (Fin n) (Fin n) 𝕜 | A.PosSemidef} := by
  have heq : {A : Matrix (Fin n) (Fin n) 𝕜 | A.PosSemidef}
      = {A : Matrix (Fin n) (Fin n) 𝕜 | A.IsHermitian}
        ∩ ⋂ x : Fin n → 𝕜,
          {A : Matrix (Fin n) (Fin n) 𝕜 | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq]
    exact posSemidef_iff_dotProduct_mulVec
  rw [heq]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => ?_)
  · have h2 : {A : Matrix (Fin n) (Fin n) 𝕜 | A.IsHermitian}
        = {A : Matrix (Fin n) (Fin n) 𝕜 | Aᴴ = A} := rfl
    rw [h2]
    refine isClosed_eq ?_ continuous_id
    refine continuous_matrix fun i j => ?_
    exact Continuous.star (continuous_entry j i)
  · have h3 : {A : Matrix (Fin n) (Fin n) 𝕜 | 0 ≤ star x ⬝ᵥ (A *ᵥ x)}
        = (fun A : Matrix (Fin n) (Fin n) 𝕜 => star x ⬝ᵥ (A *ᵥ x))
          ⁻¹' {z : 𝕜 | 0 ≤ z} := rfl
    rw [h3]
    refine IsClosed.preimage (continuous_quadForm x) ?_
    have h4 : {z : 𝕜 | 0 ≤ z}
        = {z : 𝕜 | 0 ≤ RCLike.re z} ∩ {z : 𝕜 | RCLike.im z = 0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      exact RCLike.nonneg_iff
    rw [h4]
    exact (isClosed_le continuous_const RCLike.continuous_re).inter
      (isClosed_eq RCLike.continuous_im continuous_const)

theorem isClosed_densitySet :
    IsClosed (densitySet n 𝕜) := by
  have heq : densitySet n 𝕜
      = {A : Matrix (Fin n) (Fin n) 𝕜 | A.PosSemidef}
        ∩ ((fun A : Matrix (Fin n) (Fin n) 𝕜 => A.trace)
          ⁻¹' {(1 : 𝕜)}) := by
    ext A
    simp [densitySet, Set.mem_inter_iff]
  rw [heq]
  exact isClosed_posSemidef.inter
    (IsClosed.preimage continuous_matrix_trace isClosed_singleton)

theorem isCompact_densitySet :
    IsCompact (densitySet n 𝕜) := by
  have hsub : densitySet n 𝕜
      ⊆ Set.univ.pi (fun _ : Fin n =>
          Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : 𝕜) 1) := by
    intro ρ hρ
    refine Set.mem_pi.mpr fun i _ => Set.mem_pi.mpr fun j _ => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact density_entry_le hρ.1 hρ.2 i j
  refine IsCompact.of_isClosed_subset ?_ isClosed_densitySet hsub
  exact isCompact_univ_pi fun i =>
    isCompact_univ_pi fun j => isCompact_closedBall _ _

end Density

/-! ## Iterates of a trace-preserving positive map -/

section Iterates

variable {T : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin n) (Fin n) 𝕜}

theorem pow_trace (htr : ∀ A, (T A).trace = A.trace) (m : ℕ)
    (A : Matrix (Fin n) (Fin n) 𝕜) :
    ((T ^ m) A).trace = A.trace := by
  induction m generalizing A with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih (T A), htr A]

theorem pow_posSemidef
    (hpsd : ∀ A : Matrix (Fin n) (Fin n) 𝕜,
      A.PosSemidef → (T A).PosSemidef)
    (m : ℕ) {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef) :
    ((T ^ m) A).PosSemidef := by
  induction m generalizing A with
  | zero => simpa using hA
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih (hpsd A hA)

theorem pow_fixed {ρ : Matrix (Fin n) (Fin n) 𝕜} (hfix : T ρ = ρ)
    (m : ℕ) : (T ^ m) ρ = ρ := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, hfix, ih]

end Iterates

/-! ## Existence of a stationary density (Cesàro + compactness) -/

section Existence

/-- The matrix space carries the (first-countable) product
topology. -/
instance : FirstCountableTopology (Matrix (Fin n) (Fin n) 𝕜) :=
  inferInstanceAs (FirstCountableTopology (Fin n → Fin n → 𝕜))

variable {T : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin n) (Fin n) 𝕜}

/-- **Existence**: a trace-preserving positivity-preserving linear
map on `M_n(𝕜)`, `n ≥ 1`, has a stationary density matrix.  Proved
by Cesàro averaging the orbit of the maximally mixed state and
extracting a convergent subsequence in the compact density
simplex. -/
theorem exists_stationary_density (hn : 0 < n)
    (htr : ∀ A, (T A).trace = A.trace)
    (hpsd : ∀ A : Matrix (Fin n) (Fin n) 𝕜,
      A.PosSemidef → (T A).PosSemidef) :
    ∃ ρ ∈ densitySet n 𝕜, T ρ = ρ := by
  classical
  have hn' : ((n : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  -- the maximally mixed initial state
  set ρ₀ : Matrix (Fin n) (Fin n) 𝕜
    := (((n : ℝ)⁻¹ : ℝ) : 𝕜) • 1 with hρ₀def
  have hρ₀psd : ρ₀.PosSemidef :=
    posSemidef_real_smul PosSemidef.one
      (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hρ₀tr : ρ₀.trace = 1 := by
    rw [hρ₀def, trace_smul, trace_one, smul_eq_mul]
    have hcast : ((Fintype.card (Fin n) : ℕ) : 𝕜) = ((n : ℝ) : 𝕜) := by
      simp
    rw [hcast, ← RCLike.ofReal_mul, inv_mul_cancel₀ hn',
      RCLike.ofReal_one]
  -- the orbit stays in the density simplex
  have horbit : ∀ k : ℕ, (T ^ k) ρ₀ ∈ densitySet n 𝕜 := by
    intro k
    exact ⟨pow_posSemidef hpsd k hρ₀psd,
      by rw [pow_trace htr k, hρ₀tr]⟩
  -- Cesàro averages
  set Ces : ℕ → Matrix (Fin n) (Fin n) 𝕜 := fun q =>
    ((((q : ℝ) + 1)⁻¹ : ℝ) : 𝕜)
      • ∑ k ∈ Finset.range (q + 1), (T ^ k) ρ₀ with hCes
  have hq1 : ∀ q : ℕ, ((q : ℝ) + 1) ≠ 0 := by
    intro q
    positivity
  have hCesMem : ∀ q, Ces q ∈ densitySet n 𝕜 := by
    intro q
    constructor
    · refine posSemidef_real_smul ?_
        (inv_nonneg.mpr (by positivity))
      refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb)
        PosSemidef.zero fun k _ => (horbit k).1
    · rw [hCes]
      simp only [trace_smul, trace_sum]
      rw [Finset.sum_congr rfl fun k _ => (horbit k).2]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one, smul_eq_mul]
      rw [show (((q : ℕ) + 1 : ℕ) : 𝕜) = (((q : ℝ) + 1 : ℝ) : 𝕜) by
        push_cast; ring]
      rw [← RCLike.ofReal_mul, inv_mul_cancel₀ (hq1 q),
        RCLike.ofReal_one]
  -- a convergent subsequence
  obtain ⟨ρ, hρmem, φ, hφmono, hφlim⟩ :=
    isCompact_densitySet.tendsto_subseq hCesMem
  -- powers commute with one application
  have hcomm : ∀ (k : ℕ) (A : Matrix (Fin n) (Fin n) 𝕜),
      (T ^ k) (T A) = T ((T ^ k) A) := by
    intro k
    induction k with
    | zero => intro A; simp
    | succ l ih =>
      intro A
      simp only [pow_succ, Module.End.mul_apply]
      exact ih (T A)
  -- the Cesàro defect tends to zero
  have hdefect : ∀ q, T (Ces q) - Ces q
      = ((((q : ℝ) + 1)⁻¹ : ℝ) : 𝕜)
        • ((T ^ (q + 1)) ρ₀ - ρ₀) := by
    intro q
    rw [hCes]
    simp only [map_smul, map_sum, ← smul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ k ∈ Finset.range (q + 1),
        T ((T ^ k) ρ₀) - (T ^ k) ρ₀
        = (T ^ (k + 1)) ρ₀ - (T ^ k) ρ₀ := by
      intro k _
      rw [pow_succ, Module.End.mul_apply, hcomm k ρ₀]
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub
      (fun k => (T ^ k) ρ₀)]
    simp
  have hdef0 : Tendsto (fun q => T (Ces q) - Ces q) atTop
      (nhds (0 : Matrix (Fin n) (Fin n) 𝕜)) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    have hbound : ∀ q : ℕ,
        ‖(T (Ces q) - Ces q) i j‖ ≤ 2 / ((q : ℝ) + 1) := by
      intro q
      rw [hdefect q]
      rw [Matrix.smul_apply, Matrix.sub_apply]
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg
        (inv_nonneg.mpr (by positivity : (0:ℝ) ≤ (q : ℝ) + 1))]
      have hb : ‖(T ^ (q + 1)) ρ₀ i j - ρ₀ i j‖ ≤ 2 := by
        refine le_trans (norm_sub_le _ _) ?_
        have hb1 := density_entry_le (horbit (q + 1)).1
          (horbit (q + 1)).2 i j
        have hb2 := density_entry_le hρ₀psd hρ₀tr i j
        linarith
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hb
        (inv_nonneg.mpr (by positivity))
    have hto0 : Tendsto (fun q : ℕ => 2 / ((q : ℝ) + 1)) atTop
        (nhds 0) := by
      refine Tendsto.div_atTop tendsto_const_nhds ?_
      exact tendsto_atTop_add_const_right _ 1
        tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun q => (T (Ces q) - Ces q) i j) atTop
        (nhds 0) := squeeze_zero_norm hbound hto0
    simpa using h0
  -- continuity of T and passage to the limit
  have hTcont : Continuous T := T.continuous_of_finiteDimensional
  have h1 : Tendsto (fun s => T (Ces (φ s))) atTop (nhds (T ρ)) :=
    (hTcont.tendsto ρ).comp hφlim
  have h2 : Tendsto (fun s => T (Ces (φ s))) atTop (nhds (0 + ρ)) := by
    have h3 : Tendsto (fun s => T (Ces (φ s)) - Ces (φ s)) atTop
        (nhds 0) := hdef0.comp (hφmono.tendsto_atTop)
    have h4 := h3.add hφlim
    refine h4.congr fun s => ?_
    simp only [Function.comp_apply]
    abel
  have h5 : T ρ = 0 + ρ := tendsto_nhds_unique h1 h2
  exact ⟨ρ, hρmem, by rw [h5, zero_add]⟩

end Existence

/-! ## Faithfulness and uniqueness of the stationary density -/

section Uniqueness

variable {T : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin n) (Fin n) 𝕜}

/-- **Faithfulness**: primitivity makes any stationary density
positive definite. -/
theorem stationary_posDef {m : ℕ}
    (hprim : ∀ A : Matrix (Fin n) (Fin n) 𝕜,
      A.PosSemidef → A ≠ 0 → ((T ^ m) A).PosDef)
    {ρ : Matrix (Fin n) (Fin n) 𝕜}
    (hρ : ρ ∈ densitySet n 𝕜) (hfix : T ρ = ρ) : ρ.PosDef := by
  have hne : ρ ≠ 0 := by
    intro h
    have h2 := hρ.2
    rw [h, trace_zero] at h2
    exact one_ne_zero h2.symm
  have h3 := hprim ρ hρ.1 hne
  rwa [pow_fixed hfix m] at h3

/-- Positive-definite matrices dominate a positive multiple of the
identity: the minimal-eigenvalue shift stays positive
semidefinite. -/
theorem posDef_exists_smul_one_le {A : Matrix (Fin n) (Fin n) 𝕜}
    (hn : 0 < n) (hA : A.PosDef) :
    ∃ ε : ℝ, 0 < ε ∧ (A - ((ε : ℝ) : 𝕜) • 1).PosSemidef := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    refine ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i0, _, hi0⟩ :=
    Finset.exists_min_image Finset.univ hA.1.eigenvalues hne
  refine ⟨hA.1.eigenvalues i0, hA.eigenvalues_pos i0, ?_⟩
  have hshift : A - ((hA.1.eigenvalues i0 : ℝ) : 𝕜) • 1
      = hA.1.cfc fun x => x - hA.1.eigenvalues i0 := by
    have h1 := cfc_sub hA.1 id (fun _ => hA.1.eigenvalues i0)
    rw [cfc_id', cfc_const] at h1
    exact h1
  rw [hshift]
  refine cfc_posSemidef hA.1 fun i => ?_
  have h2 := hi0 i (Finset.mem_univ i)
  linarith

/-- Lowering the identity shift preserves positive
semidefiniteness. -/
theorem shift_mono {A : Matrix (Fin n) (Fin n) 𝕜} {a : ℝ}
    (hA : (A - ((a : ℝ) : 𝕜) • 1).PosSemidef) {e : ℝ}
    (_he : 0 ≤ e) (hea : e ≤ a) :
    (A - ((e : ℝ) : 𝕜) • 1).PosSemidef := by
  have h1 : A - ((e : ℝ) : 𝕜) • 1
      = (A - ((a : ℝ) : 𝕜) • 1) + ((a - e : ℝ) : 𝕜) • 1 := by
    rw [RCLike.ofReal_sub, sub_smul]
    abel
  rw [h1]
  exact hA.add
    (posSemidef_real_smul PosSemidef.one (by linarith))

/-- The strict trace-norm contraction estimate on a traceless
Hermitian matrix through the primitive power. -/
theorem primitive_contraction_strict (hn : 0 < n) {m : ℕ}
    (htr : ∀ A, (T A).trace = A.trace)
    (hprim : ∀ A : Matrix (Fin n) (Fin n) 𝕜,
      A.PosSemidef → A ≠ 0 → ((T ^ m) A).PosDef)
    {Y : Matrix (Fin n) (Fin n) 𝕜} (hY : Y.IsHermitian)
    (hYtr : Y.trace = 0) (hYne : Y ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      trNorm ((T ^ m) Y) ≤ trNorm Y - 2 * ε * n := by
  classical
  -- Jordan parts of Y are both nonzero positive semidefinite
  have hPpsd := posPart_posSemidef hY
  have hQpsd := negPart_posSemidef hY
  have hPQ := posPart_sub_negPart hY
  have htrEq : RCLike.re ((posPart hY).trace)
      = RCLike.re ((negPart hY).trace) := by
    have h1 : (posPart hY).trace - (negPart hY).trace = 0 := by
      rw [← trace_sub, hPQ, hYtr]
    have h2 := congrArg RCLike.re h1
    rw [map_sub] at h2
    simp only [map_zero] at h2
    linarith
  have htrN : trNorm Y = RCLike.re ((posPart hY).trace)
      + RCLike.re ((negPart hY).trace) :=
    trNorm_eq_re_trace_parts hY
  have hpos : 0 < trNorm Y := by
    rcases lt_or_eq_of_le (trNorm_nonneg Y) with h | h
    · exact h
    · exact absurd ((trNorm_eq_zero_iff hY).mp h.symm) hYne
  have hPtr : 0 < RCLike.re ((posPart hY).trace) := by
    have h0 := (RCLike.nonneg_iff.mp (psd_trace_nonneg hPpsd)).1
    rcases lt_or_eq_of_le h0 with h | h
    · exact h
    · exfalso
      linarith
  have hPne : posPart hY ≠ 0 := by
    intro h
    rw [h, trace_zero] at hPtr
    simp at hPtr
  have hQtr : 0 < RCLike.re ((negPart hY).trace) := by
    linarith
  have hQne : negPart hY ≠ 0 := by
    intro h
    rw [h, trace_zero] at hQtr
    simp at hQtr
  -- push the parts through the primitive power
  have hApd := hprim _ hPpsd hPne
  have hBpd := hprim _ hQpsd hQne
  obtain ⟨εA, hεA, hApsd⟩ := posDef_exists_smul_one_le hn hApd
  obtain ⟨εB, hεB, hBpsd⟩ := posDef_exists_smul_one_le hn hBpd
  refine ⟨min εA εB, lt_min hεA hεB, ?_⟩
  have hε : 0 < min εA εB := lt_min hεA hεB
  -- (T^m) Y is Hermitian, being a difference of positive parts
  have hsplit : (T ^ m) Y
      = (T ^ m) (posPart hY) - (T ^ m) (negPart hY) := by
    rw [← map_sub, hPQ]
  have hTYherm : ((T ^ m) Y).IsHermitian := by
    rw [hsplit]
    exact hApd.isHermitian.sub hBpd.isHermitian
  -- the shifted decomposition
  have hA' : ((T ^ m) (posPart hY)
      - ((min εA εB : ℝ) : 𝕜) • 1).PosSemidef :=
    shift_mono hApsd hε.le (min_le_left _ _)
  have hB' : ((T ^ m) (negPart hY)
      - ((min εA εB : ℝ) : 𝕜) • 1).PosSemidef :=
    shift_mono hBpsd hε.le (min_le_right _ _)
  have hdec : (T ^ m) Y
      = ((T ^ m) (posPart hY) - ((min εA εB : ℝ) : 𝕜) • 1)
        - ((T ^ m) (negPart hY) - ((min εA εB : ℝ) : 𝕜) • 1) := by
    rw [sub_sub_sub_cancel_right, ← map_sub, hPQ]
  have hbound := trNorm_le_of_sub hTYherm hA' hB' hdec
  -- evaluate the two shifted traces
  have hεtr : ((((min εA εB : ℝ)) : 𝕜)
      • (1 : Matrix (Fin n) (Fin n) 𝕜)).trace
      = (((min εA εB) * n : ℝ) : 𝕜) := by
    rw [trace_smul, trace_one, smul_eq_mul, Fintype.card_fin]
    rw [show ((n : ℕ) : 𝕜) = ((n : ℝ) : 𝕜) by push_cast; ring]
    rw [← RCLike.ofReal_mul]
  have hre1 : RCLike.re (((T ^ m) (posPart hY)
      - ((min εA εB : ℝ) : 𝕜) • 1).trace)
      = RCLike.re ((posPart hY).trace) - (min εA εB) * n := by
    rw [trace_sub, map_sub, pow_trace htr m, hεtr, RCLike.ofReal_re]
  have hre2 : RCLike.re (((T ^ m) (negPart hY)
      - ((min εA εB : ℝ) : 𝕜) • 1).trace)
      = RCLike.re ((negPart hY).trace) - (min εA εB) * n := by
    rw [trace_sub, map_sub, pow_trace htr m, hεtr, RCLike.ofReal_re]
  rw [hre1, hre2] at hbound
  rw [htrN]
  linarith

/-- **Uniqueness** of the stationary density under primitivity. -/
theorem stationary_unique (hn : 0 < n) {m : ℕ}
    (htr : ∀ A, (T A).trace = A.trace)
    (hprim : ∀ A : Matrix (Fin n) (Fin n) 𝕜,
      A.PosSemidef → A ≠ 0 → ((T ^ m) A).PosDef)
    {ρ₁ ρ₂ : Matrix (Fin n) (Fin n) 𝕜}
    (h1 : ρ₁ ∈ densitySet n 𝕜) (h2 : ρ₂ ∈ densitySet n 𝕜)
    (hfix1 : T ρ₁ = ρ₁) (hfix2 : T ρ₂ = ρ₂) : ρ₁ = ρ₂ := by
  by_contra hne
  have hYherm : (ρ₁ - ρ₂).IsHermitian := h1.1.1.sub h2.1.1
  have hYtr : (ρ₁ - ρ₂).trace = 0 := by
    rw [trace_sub, h1.2, h2.2, sub_self]
  have hYne : ρ₁ - ρ₂ ≠ 0 := sub_ne_zero_of_ne hne
  obtain ⟨ε, hε, hcontr⟩ := primitive_contraction_strict hn htr
    hprim hYherm hYtr hYne
  have hfixY : (T ^ m) (ρ₁ - ρ₂) = ρ₁ - ρ₂ := by
    rw [map_sub, pow_fixed hfix1, pow_fixed hfix2]
  rw [hfixY] at hcontr
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith [mul_pos hε hn0]

end Uniqueness

/-! ## The uniform exponential trace-norm contraction -/

section Contraction

theorem isClosed_isHermitian :
    IsClosed {A : Matrix (Fin n) (Fin n) 𝕜 | A.IsHermitian} := by
  have h2 : {A : Matrix (Fin n) (Fin n) 𝕜 | A.IsHermitian}
      = {A : Matrix (Fin n) (Fin n) 𝕜 | Aᴴ = A} := rfl
  rw [h2]
  refine isClosed_eq ?_ continuous_id
  refine continuous_matrix fun i j => ?_
  exact Continuous.star (continuous_entry j i)

theorem isHermitian_real_smul {Y : Matrix (Fin n) (Fin n) 𝕜}
    (hY : Y.IsHermitian) (c : ℝ) :
    (((c : ℝ) : 𝕜) • Y).IsHermitian := by
  change _ᴴ = _
  rw [conjTranspose_smul, hY.eq, RCLike.star_def, RCLike.conj_ofReal]

/-- Positive homogeneity of the Hermitian trace norm, proved through
the duality bound (no eigenvalue rescaling needed). -/
theorem trNorm_smul_pos {X : Matrix (Fin n) (Fin n) 𝕜}
    (hX : X.IsHermitian) {c : ℝ} (hc : 0 < c) :
    trNorm (((c : ℝ) : 𝕜) • X) = c * trNorm X := by
  have hcX : (((c : ℝ) : 𝕜) • X).IsHermitian :=
    isHermitian_real_smul hX c
  have hkey : ∀ C : Matrix (Fin n) (Fin n) 𝕜,
      RCLike.re ((C * (((c : ℝ) : 𝕜) • X)).trace)
      = c * RCLike.re ((C * X).trace) := by
    intro C
    rw [mul_smul_comm, trace_smul, smul_eq_mul,
      ← RCLike.real_smul_eq_coe_mul, RCLike.smul_re]
  apply le_antisymm
  · have h1 := re_trace_signOp_mul hcX
    rw [← h1, hkey (signOp hcX)]
    have h2 := re_trace_mul_le_trNorm hX
      (one_sub_signOp_posSemidef hcX) (one_add_signOp_posSemidef hcX)
    exact mul_le_mul_of_nonneg_left h2 hc.le
  · have h3 := re_trace_signOp_mul hX
    have h4 := re_trace_mul_le_trNorm hcX
      (one_sub_signOp_posSemidef hX) (one_add_signOp_posSemidef hX)
    rw [hkey (signOp hX), h3] at h4
    exact h4

theorem signOp_entry_le {X : Matrix (Fin n) (Fin n) 𝕜}
    (hX : X.IsHermitian) (i j : Fin n) :
    ‖signOp hX i j‖ ≤ (n : ℝ) := by
  refine le_trans (cfc_entry_norm_le hX _ i j) ?_
  have habs : ∀ k : Fin n,
      |(if 0 < hX.eigenvalues k then (1 : ℝ) else -1)| = 1 := by
    intro k
    by_cases h : 0 < hX.eigenvalues k <;> simp [h]
  rw [Finset.sum_congr rfl fun k _ => habs k]
  simp

/-- Testing against a matrix with entries bounded by `n` is
controlled by the entry sum. -/
theorem re_trace_mul_le_entry_sum {C W : Matrix (Fin n) (Fin n) 𝕜}
    (hC : ∀ i j, ‖C i j‖ ≤ (n : ℝ)) :
    RCLike.re ((C * W).trace) ≤ (n : ℝ) * ∑ i, ∑ j, ‖W i j‖ := by
  have h1 : RCLike.re ((C * W).trace) ≤ ‖(C * W).trace‖ :=
    RCLike.re_le_norm _
  refine le_trans h1 ?_
  have h2 : ‖(C * W).trace‖ ≤ ∑ i, ‖(C * W) i i‖ := by
    simp only [Matrix.trace, Matrix.diag]
    exact norm_sum_le _ _
  refine le_trans h2 ?_
  have h3 : ∀ i : Fin n, ‖(C * W) i i‖
      ≤ ∑ j, (n : ℝ) * ‖W j i‖ := by
    intro i
    rw [Matrix.mul_apply]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC i j) (norm_nonneg _)
  refine le_trans (Finset.sum_le_sum fun i _ => h3 i) ?_
  rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [Finset.mul_sum]

/-- Lipschitz-type bound: the Hermitian trace norm varies by at most
`n` times the entrywise `ℓ¹`-distance. -/
theorem trNorm_diff_le {X Z : Matrix (Fin n) (Fin n) 𝕜}
    (hX : X.IsHermitian) (hZ : Z.IsHermitian) :
    |trNorm X - trNorm Z| ≤ (n : ℝ) * ∑ i, ∑ j, ‖(X - Z) i j‖ := by
  have hone : ∀ {W : Matrix (Fin n) (Fin n) 𝕜},
      W.IsHermitian → ∀ (hV : W.IsHermitian) (V : Matrix (Fin n) (Fin n) 𝕜),
      True := fun _ _ _ => trivial
  have hdir : ∀ (U V : Matrix (Fin n) (Fin n) 𝕜),
      U.IsHermitian → V.IsHermitian →
      trNorm U - trNorm V ≤ (n : ℝ) * ∑ i, ∑ j, ‖(U - V) i j‖ := by
    intro U V hU hV
    have e1 : RCLike.re ((signOp hU * U).trace)
        = RCLike.re ((signOp hU * V).trace)
          + RCLike.re ((signOp hU * (U - V)).trace) := by
      rw [← map_add, ← trace_add, ← mul_add, add_sub_cancel]
    have e2 := re_trace_mul_le_trNorm hV
      (one_sub_signOp_posSemidef hU) (one_add_signOp_posSemidef hU)
    have e3 := re_trace_mul_le_entry_sum
      (C := signOp hU) (W := U - V) (fun i j => signOp_entry_le hU i j)
    have e4 := re_trace_signOp_mul hU
    linarith
  have h1 := hdir X Z hX hZ
  have h2 := hdir Z X hZ hX
  have hsym : (∑ i, ∑ j, ‖(Z - X) i j‖)
      = ∑ i, ∑ j, ‖(X - Z) i j‖ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.sub_apply, Matrix.sub_apply, norm_sub_rev]
  rw [hsym] at h2
  rw [abs_le]
  constructor
  · linarith
  · exact h1

/-- The Hermitian trace norm is continuous on the closed set of
Hermitian matrices. -/
theorem continuousOn_trNorm :
    ContinuousOn trNorm
      {A : Matrix (Fin n) (Fin n) 𝕜 | A.IsHermitian} := by
  intro X hX
  have hgcont : Continuous fun Z : Matrix (Fin n) (Fin n) 𝕜 =>
      (n : ℝ) * ∑ i, ∑ j, ‖(Z - X) i j‖ := by
    refine Continuous.mul continuous_const ?_
    refine continuous_finsetSum _ fun i _ => ?_
    refine continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_entry i j).sub continuous_const).norm
  have hg0 : Tendsto
      (fun Z : Matrix (Fin n) (Fin n) 𝕜 =>
        (n : ℝ) * ∑ i, ∑ j, ‖(Z - X) i j‖)
      (nhdsWithin X {A : Matrix (Fin n) (Fin n) 𝕜 | A.IsHermitian})
      (nhds 0) := by
    have h1 := (hgcont.tendsto X).mono_left
      (nhdsWithin_le_nhds
        (s := {A : Matrix (Fin n) (Fin n) 𝕜 | A.IsHermitian}))
    simpa using h1
  have hlow : Tendsto
      (fun Z : Matrix (Fin n) (Fin n) 𝕜 =>
        trNorm X - (n : ℝ) * ∑ i, ∑ j, ‖(Z - X) i j‖)
      (nhdsWithin X {A : Matrix (Fin n) (Fin n) 𝕜 | A.IsHermitian})
      (nhds (trNorm X)) := by
    have h2 := (tendsto_const_nhds
      (x := trNorm X)
      (f := nhdsWithin X
        {A : Matrix (Fin n) (Fin n) 𝕜 | A.IsHermitian})).sub hg0
    simpa using h2
  have hhigh : Tendsto
      (fun Z : Matrix (Fin n) (Fin n) 𝕜 =>
        trNorm X + (n : ℝ) * ∑ i, ∑ j, ‖(Z - X) i j‖)
      (nhdsWithin X {A : Matrix (Fin n) (Fin n) 𝕜 | A.IsHermitian})
      (nhds (trNorm X)) := by
    have h2 := (tendsto_const_nhds
      (x := trNorm X)
      (f := nhdsWithin X
        {A : Matrix (Fin n) (Fin n) 𝕜 | A.IsHermitian})).add hg0
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · refine eventually_mem_nhdsWithin.mono fun Z hZ => ?_
    have h3 := trNorm_diff_le hZ hX
    have h4 := abs_le.mp h3
    have hsym : (∑ i, ∑ j, ‖(Z - X) i j‖)
        = ∑ i, ∑ j, ‖(Z - X) i j‖ := rfl
    linarith [h4.1]
  · refine eventually_mem_nhdsWithin.mono fun Z hZ => ?_
    have h3 := trNorm_diff_le hZ hX
    have h4 := abs_le.mp h3
    linarith [h4.2]

variable {T : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin n) (Fin n) 𝕜}

/-- A positivity-preserving map preserves hermiticity (through the
Jordan decomposition). -/
theorem pow_isHermitian
    (hpsd : ∀ A : Matrix (Fin n) (Fin n) 𝕜,
      A.PosSemidef → (T A).PosSemidef) (m : ℕ)
    {Y : Matrix (Fin n) (Fin n) 𝕜} (hY : Y.IsHermitian) :
    ((T ^ m) Y).IsHermitian := by
  have hsplit : (T ^ m) Y
      = (T ^ m) (posPart hY) - (T ^ m) (negPart hY) := by
    rw [← map_sub, posPart_sub_negPart]
  rw [hsplit]
  exact (pow_posSemidef hpsd m (posPart_posSemidef hY)).1.sub
    (pow_posSemidef hpsd m (negPart_posSemidef hY)).1

/-- **Uniform strict contraction** of the primitive power on the
traceless Hermitian subspace, obtained by maximizing over the
compact trace-norm sphere. -/
theorem exists_uniform_contraction (hn : 0 < n) {m : ℕ}
    (htr : ∀ A, (T A).trace = A.trace)
    (hpsd : ∀ A : Matrix (Fin n) (Fin n) 𝕜,
      A.PosSemidef → (T A).PosSemidef)
    (hprim : ∀ A : Matrix (Fin n) (Fin n) 𝕜,
      A.PosSemidef → A ≠ 0 → ((T ^ m) A).PosDef) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ Y : Matrix (Fin n) (Fin n) 𝕜, Y.IsHermitian → Y.trace = 0 →
        trNorm ((T ^ m) Y) ≤ c * trNorm Y := by
  classical
  set K : Set (Matrix (Fin n) (Fin n) 𝕜)
    := {X | X.IsHermitian ∧ X.trace = 0 ∧ trNorm X = 1} with hKdef
  -- scaling any nonzero traceless Hermitian matrix into K
  have hscale : ∀ Y : Matrix (Fin n) (Fin n) 𝕜, Y.IsHermitian →
      Y.trace = 0 → Y ≠ 0 →
      (((trNorm Y)⁻¹ : ℝ) : 𝕜) • Y ∈ K ∧ 0 < trNorm Y := by
    intro Y hY hYtr hYne
    have ht : 0 < trNorm Y := by
      rcases lt_or_eq_of_le (trNorm_nonneg Y) with h | h
      · exact h
      · exact absurd ((trNorm_eq_zero_iff hY).mp h.symm) hYne
    refine ⟨⟨isHermitian_real_smul hY _, ?_, ?_⟩, ht⟩
    · rw [trace_smul, hYtr, smul_zero]
    · rw [trNorm_smul_pos hY (inv_pos.mpr ht), inv_mul_cancel₀ ht.ne']
  rcases Set.eq_empty_or_nonempty K with hK | hK
  · -- degenerate case: there is no traceless Hermitian direction
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro Y hY hYtr
    by_cases hY0 : Y = 0
    · subst hY0
      rw [map_zero]
      rw [(trNorm_eq_zero_iff isHermitian_zero).mpr rfl]
      simp
    · exfalso
      obtain ⟨hZK, _⟩ := hscale Y hY hYtr hY0
      rw [hK] at hZK
      simp at hZK
  · -- compactness of the sphere
    have hKclosed : IsClosed K := by
      refine IsSeqClosed.isClosed ?_
      intro x X hx hlim
      have hXherm : X.IsHermitian :=
        isClosed_isHermitian.isSeqClosed (fun k => (hx k).1) hlim
      have hXtr : X.trace = 0 := by
        have h1 : Tendsto (fun k => (x k).trace) atTop
            (nhds X.trace) :=
          (continuous_matrix_trace.tendsto X).comp hlim
        have h2 : (fun k => (x k).trace) = fun _ => (0 : 𝕜) :=
          funext fun k => (hx k).2.1
        rw [h2] at h1
        exact (tendsto_nhds_unique h1 tendsto_const_nhds)
      refine ⟨hXherm, hXtr, ?_⟩
      -- trace norms converge by the Lipschitz bound
      have hg : Tendsto (fun k => trNorm (x k)) atTop
          (nhds (trNorm X)) := by
        have hgcont : Continuous fun Z : Matrix (Fin n) (Fin n) 𝕜 =>
            (n : ℝ) * ∑ i, ∑ j, ‖(Z - X) i j‖ := by
          refine Continuous.mul continuous_const ?_
          refine continuous_finsetSum _ fun i _ => ?_
          refine continuous_finsetSum _ fun j _ => ?_
          exact ((continuous_entry i j).sub continuous_const).norm
        have hg0 : Tendsto
            (fun k => (n : ℝ) * ∑ i, ∑ j, ‖(x k - X) i j‖) atTop
            (nhds 0) := by
          have h3 := (hgcont.tendsto X).comp hlim
          simpa [Function.comp_def] using h3
        have hb : ∀ k, ‖trNorm (x k) - trNorm X‖
            ≤ (n : ℝ) * ∑ i, ∑ j, ‖(x k - X) i j‖ := by
          intro k
          rw [Real.norm_eq_abs]
          exact trNorm_diff_le (hx k).1 hXherm
        have h5 := squeeze_zero_norm hb hg0
        have h6 := h5.add
          (tendsto_const_nhds (x := trNorm X) (f := atTop))
        rw [zero_add] at h6
        refine h6.congr fun k => ?_
        ring
      have h7 : (fun k => trNorm (x k)) = fun _ => (1 : ℝ) :=
        funext fun k => (hx k).2.2
      rw [h7] at hg
      exact tendsto_nhds_unique hg tendsto_const_nhds
    have hKcomp : IsCompact K := by
      refine IsCompact.of_isClosed_subset
        (isCompact_univ_pi fun _ : Fin n =>
          isCompact_univ_pi fun _ : Fin n =>
            isCompact_closedBall (0 : 𝕜) 1) hKclosed ?_
      intro X hX
      refine Set.mem_pi.mpr fun i _ => Set.mem_pi.mpr fun j _ => ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      have h := entry_norm_le_trNorm hX.1 i j
      rwa [hX.2.2] at h
    -- the maximized contraction factor
    have hFcont : ContinuousOn
        (fun X : Matrix (Fin n) (Fin n) 𝕜 => trNorm ((T ^ m) X)) K := by
      refine ContinuousOn.comp continuousOn_trNorm
        ((T ^ m).continuous_of_finiteDimensional.continuousOn) ?_
      intro X hXK
      exact pow_isHermitian hpsd m hXK.1
    obtain ⟨X₀, hX₀K, hX₀max⟩ :=
      hKcomp.exists_isMaxOn hK hFcont
    set c : ℝ := trNorm ((T ^ m) X₀) with hcdef
    have hc0 : 0 ≤ c := trNorm_nonneg _
    have hX₀ne : X₀ ≠ 0 := by
      intro h
      have h2 := hX₀K.2.2
      rw [h, (trNorm_eq_zero_iff isHermitian_zero).mpr rfl] at h2
      exact one_ne_zero h2.symm
    have hc1 : c < 1 := by
      obtain ⟨ε, hε, hcontr⟩ := primitive_contraction_strict hn htr
        hprim hX₀K.1 hX₀K.2.1 hX₀ne
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have h8 : 0 < ε * n := mul_pos hε hn0
      rw [hcdef]
      rw [hX₀K.2.2] at hcontr
      nlinarith
    refine ⟨c, hc0, hc1, ?_⟩
    intro Y hY hYtr
    by_cases hY0 : Y = 0
    · subst hY0
      rw [map_zero]
      rw [(trNorm_eq_zero_iff isHermitian_zero).mpr rfl]
      simp
    · obtain ⟨hZK, ht⟩ := hscale Y hY hYtr hY0
      have h9 := hX₀max hZK
      simp only [Set.mem_setOf_eq] at h9
      -- h9 : trNorm ((T^m) Z) ≤ c
      have hTmY : ((T ^ m) Y).IsHermitian := pow_isHermitian hpsd m hY
      have hFZ : trNorm ((T ^ m) ((((trNorm Y)⁻¹ : ℝ) : 𝕜) • Y))
          = (trNorm Y)⁻¹ * trNorm ((T ^ m) Y) := by
        rw [map_smul]
        exact trNorm_smul_pos hTmY (inv_pos.mpr ht)
      rw [hFZ] at h9
      have h10 : trNorm Y * ((trNorm Y)⁻¹ * trNorm ((T ^ m) Y))
          ≤ trNorm Y * c := mul_le_mul_of_nonneg_left h9 ht.le
      rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at h10
      linarith [h10]

/-- **Theorem `thm:primitive-stationary-weight`**: a trace-preserving
positivity-preserving linear map on `M_n(𝕜)` (`n ≥ 1`) that is
primitive at exponent `m` has a unique stationary density matrix; it
is faithful (positive definite), and the `m`-step dynamics contracts
towards it exponentially fast in the Hermitian trace norm. -/
theorem primitive_stationary_weight (hn : 0 < n) (m : ℕ)
    (T : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin n) (Fin n) 𝕜)
    (htr : ∀ A, (T A).trace = A.trace)
    (hpsd : ∀ A : Matrix (Fin n) (Fin n) 𝕜,
      A.PosSemidef → (T A).PosSemidef)
    (hprim : ∀ A : Matrix (Fin n) (Fin n) 𝕜,
      A.PosSemidef → A ≠ 0 → ((T ^ m) A).PosDef) :
    ∃ ρstar : Matrix (Fin n) (Fin n) 𝕜,
      ρstar.PosDef ∧ ρstar.trace = 1 ∧ T ρstar = ρstar
      ∧ (∀ ρ : Matrix (Fin n) (Fin n) 𝕜,
          ρ.PosSemidef → ρ.trace = 1 → T ρ = ρ → ρ = ρstar)
      ∧ ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
          ∀ ρ : Matrix (Fin n) (Fin n) 𝕜,
            ρ.PosSemidef → ρ.trace = 1 → ∀ k : ℕ,
            trNorm ((T ^ (k * m)) ρ - ρstar)
              ≤ c ^ k * trNorm (ρ - ρstar) := by
  obtain ⟨ρstar, hmem, hfix⟩ := exists_stationary_density hn htr hpsd
  have hpd : ρstar.PosDef := stationary_posDef hprim hmem hfix
  obtain ⟨c, hc0, hc1, hcontr⟩ :=
    exists_uniform_contraction hn htr hpsd hprim
  refine ⟨ρstar, hpd, hmem.2, hfix, ?_, c, hc0, hc1, ?_⟩
  · intro ρ hρpsd hρtr hρfix
    exact stationary_unique hn htr hprim ⟨hρpsd, hρtr⟩ hmem hρfix hfix
  · intro ρ hρpsd hρtr k
    induction k with
    | zero =>
      simp only [Nat.zero_mul, pow_zero, Module.End.one_apply,
        one_mul]
      exact le_refl _
    | succ k ih =>
      have hstep : (T ^ ((k + 1) * m)) ρ - ρstar
          = (T ^ m) ((T ^ (k * m)) ρ - ρstar) := by
        rw [map_sub, pow_fixed hfix m, ← Module.End.mul_apply,
          ← pow_add]
        rw [show m + k * m = (k + 1) * m by ring]
      rw [hstep]
      have hherm : ((T ^ (k * m)) ρ - ρstar).IsHermitian :=
        (pow_posSemidef hpsd _ hρpsd).1.sub hpd.1
      have htr0 : ((T ^ (k * m)) ρ - ρstar).trace = 0 := by
        rw [trace_sub, pow_trace htr, hρtr, hmem.2, sub_self]
      have h1 := hcontr _ hherm htr0
      calc trNorm ((T ^ m) ((T ^ (k * m)) ρ - ρstar))
          ≤ c * trNorm ((T ^ (k * m)) ρ - ρstar) := h1
        _ ≤ c * (c ^ k * trNorm (ρ - ρstar)) :=
            mul_le_mul_of_nonneg_left ih hc0
        _ = c ^ (k + 1) * trNorm (ρ - ρstar) := by ring

end Contraction

end NCG.Upstream.PrimitiveWeight
