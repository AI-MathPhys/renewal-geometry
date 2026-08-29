/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PsdBlockSchurExact
import NCG.Grand.SqrtPolar

/-!
# Protected-observable Riesz theorem with the Moore--Penrose inverse

This supplies the singular, multi-column form of `thm:GT-protected-Riesz`.
The protected influence is the genuine spectral Moore--Penrose compression
`Eᴴ L† E`.  Its square-root factorization gives the sharp Riesz bound, and
every positive unit eigenvector gives the displayed normalized witness.
-/

open Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG
namespace ProtectedObservableRiesz

open GeometricThresholdBank SourceCoercivityInfluence PsdBlockSchur

variable {n k : Type*} [Fintype n] [Fintype k]
  [DecidableEq n] [DecidableEq k]

/-- The exact protected influence `Eᴴ L† E`. -/
noncomputable def influence (L : Matrix n n ℂ) (hL : L.PosSemidef)
    (E : Matrix n k ℂ) : Matrix k k ℂ :=
  Eᴴ * pinv hL.1 * E

/-- The whitening factor `L^{1/2} L† E`. -/
noncomputable def factor (L : Matrix n n ℂ) (hL : L.PosSemidef)
    (E : Matrix n k ℂ) : Matrix n k ℂ :=
  CFC.sqrt L * (pinv hL.1 * E)

/-- A vector's Hermitian self-pairing is its Euclidean norm square. -/
theorem star_dot_self_eq_norm_sq {p : Type*} [Fintype p] (v : p → ℂ) :
    star v ⬝ᵥ v =
      ((‖(WithLp.toLp 2 v : EuclideanSpace ℂ p)‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp,
    inner_self_eq_norm_sq_to_K]
  norm_num

/-- The protected influence is the Gram of the whitening factor. -/
theorem factor_gram (L : Matrix n n ℂ) (hL : L.PosSemidef)
    (E : Matrix n k ℂ) :
    (factor L hL E)ᴴ * factor L hL E = influence L hL E := by
  have hsqrtH : (CFC.sqrt L)ᴴ = CFC.sqrt L := sqrt_isHermitian L
  have hpinvH : (pinv hL.1)ᴴ = pinv hL.1 := (pinv_isHermitian hL.1).eq
  calc
    (factor L hL E)ᴴ * factor L hL E =
        Eᴴ * (pinv hL.1 * (CFC.sqrt L * CFC.sqrt L) *
          pinv hL.1) * E := by
      unfold factor
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hsqrtH, hpinvH]
      simp only [Matrix.mul_assoc]
    _ = Eᴴ * (pinv hL.1 * L * pinv hL.1) * E := by
      rw [sqrt_mul_self_eq L hL]
    _ = influence L hL E := by
      rw [pinv_mul_self_mul_pinv hL.1]
      rfl

/-- Hence the protected influence is positive semidefinite. -/
theorem influence_posSemidef (L : Matrix n n ℂ) (hL : L.PosSemidef)
    (E : Matrix n k ℂ) : (influence L hL E).PosSemidef := by
  rw [← factor_gram L hL E]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The range hypothesis `Ran E ⊆ Ran L`, in matrix form. -/
def RangeSupported (L : Matrix n n ℂ) (hL : L.PosSemidef)
    (E : Matrix n k ℂ) : Prop :=
  L * pinv hL.1 * E = E

/-- On the supported range, the factor adjoint followed by `L^{1/2}` is
exactly `Eᴴ`. -/
theorem factor_conjTranspose_mul_sqrt
    (L : Matrix n n ℂ) (hL : L.PosSemidef) (E : Matrix n k ℂ)
    (hE : RangeSupported L hL E) :
    (factor L hL E)ᴴ * CFC.sqrt L = Eᴴ := by
  have hsqrtH : (CFC.sqrt L)ᴴ = CFC.sqrt L := sqrt_isHermitian L
  have hpinvH : (pinv hL.1)ᴴ = pinv hL.1 := (pinv_isHermitian hL.1).eq
  have hPE : supportProj hL.1 * E = E := by
    rw [← mul_pinv_eq_supportProj hL.1]
    exact hE
  have hEP : Eᴴ * supportProj hL.1 = Eᴴ := by
    have h := congrArg Matrix.conjTranspose hPE
    simpa [Matrix.conjTranspose_mul,
      (supportProj_posSemidef hL.1).1.eq] using h
  unfold factor
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hsqrtH, hpinvH]
  simp only [Matrix.mul_assoc]
  rw [sqrt_mul_self_eq L hL, ← supportProj_eq_pinv_mul hL.1, hEP]

/-- The `L`-energy is the squared Euclidean norm after applying `L^{1/2}`. -/
theorem sqrt_energy (L : Matrix n n ℂ) (hL : L.PosSemidef) (v : n → ℂ) :
    ‖(WithLp.toLp 2 (CFC.sqrt L *ᵥ v) : EuclideanSpace ℂ n)‖ ^ 2 =
      rayleigh L v := by
  have hgram := gram_realization_inner (CFC.sqrt L) v v
  rw [sqrt_isHermitian L, sqrt_mul_self_eq L hL] at hgram
  rw [star_dot_self_eq_norm_sq] at hgram
  have hr := SourceCoercivityInfluence.dotProduct_eq_rayleigh hL v
  rw [hr] at hgram
  exact_mod_cast hgram

/-- The exact multi-column Riesz bound.  The orthogonality hypothesis records
the manuscript's supported reading; the estimate in fact holds for every
`v` once `E` is range-supported. -/
theorem protected_riesz_bound
    (L : Matrix n n ℂ) (hL : L.PosSemidef) (E : Matrix n k ℂ)
    (hE : RangeSupported L hL E) (v : n → ℂ)
    (_hv : ∀ x : n → ℂ, L *ᵥ x = 0 → star x ⬝ᵥ v = 0) :
    ‖(WithLp.toLp 2 (Eᴴ *ᵥ v) : EuclideanSpace ℂ k)‖ ^ 2 ≤
      ‖influence L hL E‖ * rayleigh L v := by
  let B := factor L hL E
  let y := CFC.sqrt L *ᵥ v
  have hEy : Eᴴ *ᵥ v = Bᴴ *ᵥ y := by
    symm
    calc
      Bᴴ *ᵥ y = (Bᴴ * CFC.sqrt L) *ᵥ v := by
        change Bᴴ *ᵥ (CFC.sqrt L *ᵥ v) =
          (Bᴴ * CFC.sqrt L) *ᵥ v
        rw [Matrix.mulVec_mulVec]
      _ = Eᴴ *ᵥ v := by
        rw [show Bᴴ * CFC.sqrt L = Eᴴ by
          simpa [B] using factor_conjTranspose_mul_sqrt L hL E hE]
  have hb := Matrix.l2_opNorm_mulVec Bᴴ
    (WithLp.toLp 2 y : EuclideanSpace ℂ n)
  have hb' : ‖(WithLp.toLp 2 (Bᴴ *ᵥ y) : EuclideanSpace ℂ k)‖ ≤
      ‖B‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ n)‖ := by
    simpa [Matrix.l2_opNorm_conjTranspose B] using hb
  have hsquare :
      ‖(WithLp.toLp 2 (Bᴴ *ᵥ y) : EuclideanSpace ℂ k)‖ ^ 2 ≤
        (‖B‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ n)‖) ^ 2 := by
    nlinarith [norm_nonneg
      (WithLp.toLp 2 (Bᴴ *ᵥ y) : EuclideanSpace ℂ k),
      norm_nonneg (WithLp.toLp 2 y : EuclideanSpace ℂ n),
      norm_nonneg B]
  have hBnorm : ‖B‖ ^ 2 = ‖influence L hL E‖ := by
    have hgram := Matrix.l2_opNorm_conjTranspose_mul_self B
    rw [show Bᴴ * B = influence L hL E by
      simpa [B] using factor_gram L hL E] at hgram
    nlinarith
  rw [hEy]
  calc
    ‖(WithLp.toLp 2 (Bᴴ *ᵥ y) : EuclideanSpace ℂ k)‖ ^ 2
        ≤ (‖B‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ n)‖) ^ 2 := hsquare
    _ = ‖influence L hL E‖ * rayleigh L v := by
      rw [mul_pow, hBnorm]
      rw [sqrt_energy L hL v]

/-- A positive influence eigenvector gives the exact normalized protected
output and reciprocal action displayed in the manuscript. -/
theorem protected_riesz_eigen_witness
    (L : Matrix n n ℂ) (hL : L.PosSemidef) (E : Matrix n k ℂ)
    (hE : RangeSupported L hL E) (c : k → ℂ) (lam : ℝ)
    (hlam : 0 < lam)
    (hc : ‖(WithLp.toLp 2 c : EuclideanSpace ℂ k)‖ = 1)
    (heig : influence L hL E *ᵥ c = (lam : ℂ) • c) :
    let z := (lam : ℂ)⁻¹ • (pinv hL.1 *ᵥ (E *ᵥ c))
    Eᴴ *ᵥ z = c ∧ rayleigh L z = lam⁻¹ := by
  dsimp only
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  let u := pinv hL.1 *ᵥ (E *ᵥ c)
  have hEu : Eᴴ *ᵥ u = (lam : ℂ) • c := by
    calc
      Eᴴ *ᵥ u = (Eᴴ * pinv hL.1 * E) *ᵥ c := by
        simp [u, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = influence L hL E *ᵥ c := rfl
      _ = (lam : ℂ) • c := heig
  have hLu : L *ᵥ u = E *ᵥ c := by
    calc
      L *ᵥ u = (L * pinv hL.1 * E) *ᵥ c := by
        simp [u, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = E *ᵥ c := congrArg (fun M : Matrix n k ℂ => M *ᵥ c) hE
  have hcc : star c ⬝ᵥ c = 1 := by
    rw [star_dot_self_eq_norm_sq, hc]
    norm_num
  have huu : star u ⬝ᵥ (L *ᵥ u) = (lam : ℂ) := by
    rw [hLu, PsdBlockSchur.adjoint_dot E u c, hEu, star_smul,
      smul_dotProduct, hcc]
    simp [Complex.star_def]
  constructor
  · rw [Matrix.mulVec_smul, hEu, smul_smul,
      inv_mul_cancel₀ hlamC, one_smul]
  · have henergy :
        star ((lam : ℂ)⁻¹ • u) ⬝ᵥ
            (L *ᵥ ((lam : ℂ)⁻¹ • u)) = ((lam⁻¹ : ℝ) : ℂ) := by
      rw [Matrix.mulVec_smul, star_smul, smul_dotProduct,
        dotProduct_smul, huu]
      simp only [smul_eq_mul]
      rw [show star ((lam : ℂ)⁻¹) = (lam : ℂ)⁻¹ by
        simp [Complex.star_def]]
      push_cast
      field_simp
    have hr := SourceCoercivityInfluence.dotProduct_eq_rayleigh hL
      ((lam : ℂ)⁻¹ • u)
    rw [hr] at henergy
    exact_mod_cast henergy

/-- Along a diverging positive influence sequence, the reciprocal witness
actions tend to zero. -/
theorem influence_atTop_implies_witness_action_zero
    (lam : ℕ → ℝ) (h : Tendsto lam atTop atTop) :
    Tendsto (fun j => (lam j)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp h

/-- For positive influences the preceding implication is an equivalence:
diverging influence is exactly vanishing reciprocal witness action. -/
theorem influence_atTop_iff_witness_action_zero
    (lam : ℕ → ℝ) (hpos : ∀ j, 0 < lam j) :
    Tendsto lam atTop atTop ↔
      Tendsto (fun j => (lam j)⁻¹) atTop (nhds 0) := by
  constructor
  · exact influence_atTop_implies_witness_action_zero lam
  · intro hzero
    have hwithin : Tendsto (fun j => (lam j)⁻¹) atTop
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
      rw [nhdsWithin]
      refine le_inf hzero ?_
      exact tendsto_principal.2 (Filter.Eventually.of_forall fun j =>
        inv_pos.mpr (hpos j))
    have hinv := hwithin.inv_tendsto_nhdsGT_zero
    change Tendsto (fun j => ((lam j)⁻¹)⁻¹) atTop atTop at hinv
    simpa only [inv_inv] using hinv

end ProtectedObservableRiesz
end NCG
