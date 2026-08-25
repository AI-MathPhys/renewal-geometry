/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.QuantumRelativeEntropyExact

/-!
# The Petz recovery map and the recovery-error Gram

Layer QS.1 and QS.4 of `thm:accepted-Petz-sufficiency`: for a finite CPTP
map presented by its Kraus family `K` and a faithful reference state `σ`
with faithful output `σ̄ = Φ_*(σ)`:

* `petz`: the Petz map
  `R(y) = σ^{1/2} Φ†(σ̄^{-1/2} y σ̄^{-1/2}) σ^{1/2}` (QS.1);
* `petz_eq_kraus`: `R` has the explicit Kraus family
  `L_i = σ^{1/2} K_i^* σ̄^{-1/2}` — the Choi–Kraus certificate of complete
  positivity;
* `petz_kraus_sum`, `petz_trace`: `∑ L_i^* L_i = 1`, so `R` is trace
  preserving;
* `petz_recovers_reference`: `R(σ̄) = σ`;
* `recGram_posSemidef` (QS.4): the Gram `[𝔾_rec]_{ab} = Tr(e_a^* e_b)` of
  the recovery errors is positive semidefinite;
* `recGram_eq_zero_iff`: `𝔾_rec = 0` exactly when the channel is recovered
  on the complete declared family;
* `petz_recovers_mixture`: a channel recovered on every family member is
  recovered on every mixture.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace Petz

open NCG.QRE

variable {n m κ : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype κ]
variable {S σ : Matrix n n ℂ}

/-! ### Square roots through the spectral calculus -/

/-- The positive square root through the spectrum. -/
noncomputable def sqrtMat (hS : S.IsHermitian) : Matrix n n ℂ :=
  matFun hS Real.sqrt

/-- The inverse square root through the spectrum. -/
noncomputable def invSqrtMat (hS : S.IsHermitian) : Matrix n n ℂ :=
  matFun hS fun x => (Real.sqrt x)⁻¹

theorem matFun_id (hS : S.IsHermitian) : matFun hS id = S := by
  unfold matFun
  exact hS.spectral_theorem.symm

theorem matFun_one (hS : S.IsHermitian) :
    matFun hS (fun _ => 1) = 1 := by
  unfold matFun
  have h1 : diagonal (RCLike.ofReal ∘ fun _ : n =>
      (1 : ℝ)) = (1 : Matrix n n ℂ) := by
    rw [← Matrix.diagonal_one]
    rfl
  rw [h1, map_one]

theorem matFun_congr (hS : S.IsHermitian) (f g : ℝ → ℝ)
    (h : ∀ i, f (hS.eigenvalues i) = g (hS.eigenvalues i)) :
    matFun hS f = matFun hS g := by
  unfold matFun
  have harg : (RCLike.ofReal (K := ℂ) ∘ fun i => f (hS.eigenvalues i)) =
      RCLike.ofReal (K := ℂ) ∘ fun i => g (hS.eigenvalues i) := by
    funext i
    simp [Function.comp, h i]
  rw [harg]

theorem matFun_isHermitian (hS : S.IsHermitian) (f : ℝ → ℝ) :
    (matFun hS f).IsHermitian := by
  unfold matFun
  rw [conjStarAlgAut_apply]
  have hd : (diagonal (RCLike.ofReal ∘ fun i =>
      f (hS.eigenvalues i)) : Matrix n n ℂ)ᴴ =
      diagonal (RCLike.ofReal ∘ fun i => f (hS.eigenvalues i)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [Function.comp, Complex.conj_ofReal]
  change (_ * _ * _)ᴴ = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hd,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
    ← Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

theorem sqrtMat_mul_self (hp : S.PosSemidef) :
    sqrtMat hp.1 * sqrtMat hp.1 = S := by
  unfold sqrtMat
  rw [matFun_mul]
  rw [matFun_congr hp.1 _ id fun i =>
    Real.mul_self_sqrt (hp.eigenvalues_nonneg i)]
  exact matFun_id hp.1

theorem invSqrt_conj_self (hd : S.PosDef) :
    invSqrtMat hd.1 * S * invSqrtMat hd.1 = 1 := by
  unfold invSqrtMat
  have h1 := matFun_mul hd.1 (fun x => (Real.sqrt x)⁻¹) id
  rw [matFun_id] at h1
  have h2 := matFun_mul hd.1 (fun x => (Real.sqrt x)⁻¹ * id x)
    (fun x => (Real.sqrt x)⁻¹)
  rw [h1, h2]
  rw [matFun_congr hd.1 _ (fun _ => 1) fun i => ?_]
  · exact matFun_one hd.1
  · have hpos := hd.eigenvalues_pos i
    have hs : Real.sqrt (hd.1.eigenvalues i) ≠ 0 :=
      (Real.sqrt_pos.mpr hpos).ne'
    simp only [id_eq]
    field_simp
    rw [Real.sq_sqrt hpos.le]

theorem sqrtMat_isHermitian (hS : S.IsHermitian) :
    (sqrtMat hS).IsHermitian := matFun_isHermitian hS _

theorem invSqrtMat_isHermitian (hS : S.IsHermitian) :
    (invSqrtMat hS).IsHermitian := matFun_isHermitian hS _

/-! ### Kraus channels -/

/-- The Schrödinger-picture channel of a Kraus family. -/
noncomputable def kraus (K : κ → Matrix m n ℂ) (ρ : Matrix n n ℂ) :
    Matrix m m ℂ :=
  ∑ i, K i * ρ * (K i)ᴴ

set_option linter.unusedFintypeInType false in
omit [DecidableEq n] [DecidableEq m] in
theorem kraus_posSemidef (K : κ → Matrix m n ℂ) {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) : (kraus K ρ).PosSemidef := by
  unfold kraus
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb)
    Matrix.PosSemidef.zero fun i _ => ?_
  exact hρ.mul_mul_conjTranspose_same (K i)

omit [DecidableEq m] in
theorem kraus_trace (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (ρ : Matrix n n ℂ) :
    (kraus K ρ).trace = ρ.trace := by
  unfold kraus
  rw [Matrix.trace_sum]
  have hterm : ∀ i, (K i * ρ * (K i)ᴴ).trace =
      (ρ * ((K i)ᴴ * K i)).trace := by
    intro i
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  simp only [hterm]
  rw [← Matrix.trace_sum]
  have hsum : ∑ i, ρ * ((K i)ᴴ * K i) = ρ * ∑ i, (K i)ᴴ * K i := by
    rw [Matrix.mul_sum]
  rw [hsum, hK, Matrix.mul_one]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem kraus_add (K : κ → Matrix m n ℂ) (ρ₁ ρ₂ : Matrix n n ℂ) :
    kraus K (ρ₁ + ρ₂) = kraus K ρ₁ + kraus K ρ₂ := by
  unfold kraus
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_add, Matrix.add_mul]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem kraus_smul (K : κ → Matrix m n ℂ) (c : ℂ) (ρ : Matrix n n ℂ) :
    kraus K (c • ρ) = c • kraus K ρ := by
  unfold kraus
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-! ### The Petz map (QS.1) -/

/-- **The Petz recovery map**
`R(y) = σ^{1/2} Φ†(σ̄^{-1/2} y σ̄^{-1/2}) σ^{1/2}` (QS.1). -/
noncomputable def petz (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (y : Matrix m m ℂ) : Matrix n n ℂ :=
  sqrtMat hσ.1 *
    (∑ i, (K i)ᴴ *
      (invSqrtMat hbar.1 * y * invSqrtMat hbar.1) * K i) *
    sqrtMat hσ.1

/-- The explicit Kraus operators of the Petz map. -/
noncomputable def petzKraus (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (i : κ) : Matrix n m ℂ :=
  sqrtMat hσ.1 * (K i)ᴴ * invSqrtMat hbar.1

theorem petzKraus_conjTranspose (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (i : κ) :
    (petzKraus K hσ hbar i)ᴴ =
      invSqrtMat hbar.1 * K i * sqrtMat hσ.1 := by
  unfold petzKraus
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    invSqrtMat_isHermitian hbar.1, sqrtMat_isHermitian hσ.1,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- **The Petz map in explicit Kraus form** — its Choi–Kraus complete
positivity certificate. -/
theorem petz_eq_kraus (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (y : Matrix m m ℂ) :
    petz K hσ hbar y =
      ∑ i, petzKraus K hσ hbar i * y * (petzKraus K hσ hbar i)ᴴ := by
  unfold petz
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [petzKraus_conjTranspose]
  unfold petzKraus
  simp only [Matrix.mul_assoc]

/-- The Petz map preserves positivity. -/
theorem petz_posSemidef (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) {y : Matrix m m ℂ}
    (hy : y.PosSemidef) : (petz K hσ hbar y).PosSemidef := by
  rw [petz_eq_kraus]
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb)
    Matrix.PosSemidef.zero fun i _ => ?_
  exact hy.mul_mul_conjTranspose_same (petzKraus K hσ hbar i)

/-- `∑ L_i^* L_i = 1`: the Petz map is trace preserving. -/
theorem petz_kraus_sum (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) :
    ∑ i, (petzKraus K hσ hbar i)ᴴ * petzKraus K hσ hbar i = 1 := by
  have hterm : ∀ i, (petzKraus K hσ hbar i)ᴴ * petzKraus K hσ hbar i =
      invSqrtMat hbar.1 * (K i * σ * (K i)ᴴ) * invSqrtMat hbar.1 := by
    intro i
    rw [petzKraus_conjTranspose]
    unfold petzKraus
    have hmid : sqrtMat hσ.1 * sqrtMat hσ.1 = σ :=
      sqrtMat_mul_self hσ.posSemidef
    calc invSqrtMat hbar.1 * K i * sqrtMat hσ.1 *
          (sqrtMat hσ.1 * (K i)ᴴ * invSqrtMat hbar.1)
        = invSqrtMat hbar.1 * (K i * (sqrtMat hσ.1 * sqrtMat hσ.1) *
            (K i)ᴴ) * invSqrtMat hbar.1 := by
          simp only [Matrix.mul_assoc]
      _ = invSqrtMat hbar.1 * (K i * σ * (K i)ᴴ) * invSqrtMat hbar.1 := by
          rw [hmid]
  simp only [hterm]
  have hsum : ∑ i, invSqrtMat hbar.1 * (K i * σ * (K i)ᴴ) *
      invSqrtMat hbar.1 =
      invSqrtMat hbar.1 * kraus K σ * invSqrtMat hbar.1 := by
    unfold kraus
    rw [Matrix.mul_sum, Matrix.sum_mul]
  rw [hsum, invSqrt_conj_self hbar]

/-- The Petz map is trace preserving. -/
theorem petz_trace (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (y : Matrix m m ℂ) :
    (petz K hσ hbar y).trace = y.trace := by
  rw [petz_eq_kraus]
  exact kraus_trace _ (petz_kraus_sum K hσ hbar) y

/-- **The Petz map recovers the reference state**: `R(σ̄) = σ`. -/
theorem petz_recovers_reference (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef)
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    petz K hσ hbar (kraus K σ) = σ := by
  unfold petz
  rw [invSqrt_conj_self hbar]
  have hmid : ∀ i, (K i)ᴴ * (1 : Matrix m m ℂ) * K i = (K i)ᴴ * K i := by
    intro i
    rw [Matrix.mul_one]
  simp only [hmid]
  rw [hK, Matrix.mul_one]
  exact sqrtMat_mul_self hσ.posSemidef

theorem petz_add (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (y₁ y₂ : Matrix m m ℂ) :
    petz K hσ hbar (y₁ + y₂) =
      petz K hσ hbar y₁ + petz K hσ hbar y₂ := by
  simp only [petz_eq_kraus]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_add, Matrix.add_mul]

theorem petz_smul (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (c : ℂ) (y : Matrix m m ℂ) :
    petz K hσ hbar (c • y) = c • petz K hσ hbar y := by
  simp only [petz_eq_kraus]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem petz_zero (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) : petz K hσ hbar 0 = 0 := by
  rw [petz_eq_kraus]
  simp

theorem petz_sum (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) {ι : Type*} {s : Finset ι}
    {f : ι → Matrix m m ℂ} :
    petz K hσ hbar (∑ x ∈ s, f x) = ∑ x ∈ s, petz K hσ hbar (f x) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using petz_zero K hσ hbar
  | cons x s hx ih =>
      rw [Finset.sum_cons, Finset.sum_cons, petz_add, ih]

/-! ### The recovery-error Gram (QS.4) -/

omit [DecidableEq n] [DecidableEq m] in
/-- Hilbert–Schmidt norm-square of a matrix as a trace. -/
theorem trace_conjTranspose_mul_self (M : Matrix n m ℂ) :
    (Mᴴ * M).trace = ((∑ i, ∑ j, Complex.normSq (M i j) : ℝ) : ℂ) := by
  have hentry : ∀ j, (Mᴴ * M) j j =
      ∑ i, ((Complex.normSq (M i j) : ℝ) : ℂ) := by
    intro j
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, mul_comm, Complex.star_def,
      Complex.mul_conj]
  simp only [Matrix.trace, Matrix.diag, hentry]
  rw [Finset.sum_comm]
  push_cast
  rfl

omit [DecidableEq n] [DecidableEq m] in
theorem trace_conjTranspose_mul_self_eq_zero_iff (M : Matrix n m ℂ) :
    (Mᴴ * M).trace = 0 ↔ M = 0 := by
  rw [trace_conjTranspose_mul_self]
  constructor
  · intro h
    have hr : (∑ i, ∑ j, Complex.normSq (M i j) : ℝ) = 0 := by
      exact_mod_cast h
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (M i j)).mp hr
    ext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      Complex.normSq_nonneg (M i j)).mp (hterm i (Finset.mem_univ i))
      j (Finset.mem_univ j)
    simpa using Complex.normSq_eq_zero.mp hj
  · intro h
    subst h
    simp

/-- The recovery error of one declared family member. -/
noncomputable def recoveryError (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (ρa : Matrix n n ℂ) : Matrix n n ℂ :=
  ρa - petz K hσ hbar (kraus K ρa)

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- **The recovery-error Gram** `[𝔾_rec]_{ab} = Tr(e_a^* e_b)` (QS.4). -/
noncomputable def recGram (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (ρfam : A → Matrix n n ℂ) :
    Matrix A A ℂ :=
  Matrix.of fun a b =>
    ((recoveryError K hσ hbar (ρfam a))ᴴ *
      recoveryError K hσ hbar (ρfam b)).trace

set_option linter.unusedFintypeInType false in
omit [DecidableEq n] [DecidableEq A] in
/-- A Gram matrix of Hilbert–Schmidt vectors is positive semidefinite. -/
theorem gram_posSemidef (e : A → Matrix n n ℂ) :
    (Matrix.of fun a b => ((e a)ᴴ * e b).trace : Matrix A A ℂ).PosSemidef := by
  have hherm : (Matrix.of fun a b =>
      ((e a)ᴴ * e b).trace : Matrix A A ℂ).IsHermitian := by
    ext a b
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply]
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  have hquad : star x ⬝ᵥ ((Matrix.of fun a b =>
      ((e a)ᴴ * e b).trace : Matrix A A ℂ) *ᵥ x) =
      ((∑ a, x a • e a)ᴴ * ∑ b, x b • e b).trace := by
    rw [Matrix.conjTranspose_sum, Matrix.sum_mul]
    rw [Matrix.trace_sum]
    simp only [Matrix.conjTranspose_smul, Matrix.mul_sum,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, dotProduct, Matrix.mulVec, Matrix.of_apply,
      Pi.star_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hquad, trace_conjTranspose_mul_self]
  rw [Complex.le_def]
  constructor
  · simp only [Complex.zero_re, Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  · simp

set_option linter.unusedFintypeInType false in
omit [DecidableEq A] in
/-- **(QS.4) positivity**: `𝔾_rec ⪰ 0`. -/
theorem recGram_posSemidef (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (ρfam : A → Matrix n n ℂ) :
    (recGram K hσ hbar ρfam).PosSemidef :=
  gram_posSemidef fun a => recoveryError K hσ hbar (ρfam a)

omit [Fintype A] [DecidableEq A] in
/-- **(QS.4) sufficiency criterion**: the Gram vanishes exactly when the
channel is recovered on the complete declared family. -/
theorem recGram_eq_zero_iff (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (ρfam : A → Matrix n n ℂ) :
    recGram K hσ hbar ρfam = 0 ↔
      ∀ a, petz K hσ hbar (kraus K (ρfam a)) = ρfam a := by
  constructor
  · intro h a
    have hdiag := congrArg (fun M : Matrix A A ℂ => M a a) h
    simp only [recGram, Matrix.of_apply, Matrix.zero_apply] at hdiag
    have hzero := (trace_conjTranspose_mul_self_eq_zero_iff
      (recoveryError K hσ hbar (ρfam a))).mp hdiag
    unfold recoveryError at hzero
    rw [sub_eq_zero] at hzero
    exact hzero.symm
  · intro h
    ext a b
    have hzero : recoveryError K hσ hbar (ρfam a) = 0 := by
      unfold recoveryError
      rw [sub_eq_zero]
      exact (h a).symm
    simp [recGram, hzero]

omit [DecidableEq A] in
/-- **(QS.4) mixture transport**: a channel recovered on every member of
the family is recovered on every mixture. -/
theorem petz_recovers_mixture (K : κ → Matrix m n ℂ) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (ρfam : A → Matrix n n ℂ)
    (h : ∀ a, petz K hσ hbar (kraus K (ρfam a)) = ρfam a)
    (w : A → ℂ) :
    petz K hσ hbar (kraus K (∑ a, w a • ρfam a)) =
      ∑ a, w a • ρfam a := by
  have hkraus : kraus K (∑ a, w a • ρfam a) =
      ∑ a, w a • kraus K (ρfam a) := by
    unfold kraus
    have hper : ∀ i, K i * (∑ a, w a • ρfam a) * (K i)ᴴ =
        ∑ a, w a • (K i * ρfam a * (K i)ᴴ) := by
      intro i
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
    simp only [hper]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.smul_sum]
  rw [hkraus, petz_sum, Finset.sum_congr rfl fun a _ => ?_]
  rw [petz_smul, h a]

end Petz
end NCG
