/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.RelativeMetricDensity
import NCG.Grand.PositiveHeadTailEnclosure
import NCG.Grand.SchurRedheffer
import NCG.Grand.ExactSourceSchurResidual

/-!
# Relative metric density on a singular support

The support projection, positive square root, and Moore--Penrose inverse square
root are recorded through their exact Penrose identities.  This permits the
kernel-defect, reconstruction, domination, and sharp norm arguments to be
carried out without assuming that the source form is faithful.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Norms.L2Operator

namespace NCG
namespace RelativeMetricSupportDensity

/-- Exact support data for a positive source form.  `A` is its positive square
root and `R` its Moore--Penrose inverse square root. -/
structure SupportData {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) where
  Q : Matrix n n ℂ
  A : Matrix n n ℂ
  R : Matrix n n ℂ
  Q_star : Qᴴ = Q
  Q_idem : Q * Q = Q
  A_star : Aᴴ = A
  A_sq : A * A = M
  Q_mul_A : Q * A = A
  A_mul_Q : A * Q = A
  R_star : Rᴴ = R
  A_mul_R : A * R = Q
  R_mul_A : R * A = Q
  Q_mul_R : Q * R = R
  R_mul_Q : R * Q = R

/-- The manuscript's kernel defect. -/
def kernelDefect {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (D : SupportData M) (E : Matrix n n ℂ) : ℂ :=
  Matrix.trace ((1 - D.Q) * E)

/-- The support-relative density `M^{dagger/2} E M^{dagger/2}`. -/
def relativeDensity {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (D : SupportData M) (E : Matrix n n ℂ) :
    Matrix n n ℂ :=
  D.R * E * D.R

lemma complement_star {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (D : SupportData M) :
    (1 - D.Q)ᴴ = 1 - D.Q := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, D.Q_star]

lemma complement_idem {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (D : SupportData M) :
    (1 - D.Q) * (1 - D.Q) = 1 - D.Q := by
  calc
    (1 - D.Q) * (1 - D.Q) = 1 - D.Q - D.Q + D.Q * D.Q := by
      noncomm_ring
    _ = 1 - D.Q := by rw [D.Q_idem]; abel

lemma support_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (D : SupportData M) : D.Q.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self D.Q
  rwa [D.Q_star, D.Q_idem] at h

lemma complement_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (D : SupportData M) : (1 - D.Q).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - D.Q)
  rwa [complement_star D, complement_idem D] at h

private theorem hermitian_quadratic_im_zero {n : Type*} [Fintype n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (x : n → ℂ) :
    (star x ⬝ᵥ (H *ᵥ x)).im = 0 := by
  have hreal : star (star x ⬝ᵥ (H *ᵥ x)) = star x ⬝ᵥ (H *ᵥ x) := by
    calc
      star (star x ⬝ᵥ (H *ᵥ x)) = star (H *ᵥ x) ⬝ᵥ x := by
        rw [star_dotProduct]
        simp
      _ = (star x ᵥ* Hᴴ) ⬝ᵥ x := by rw [star_mulVec]
      _ = star x ⬝ᵥ (Hᴴ *ᵥ x) := by rw [dotProduct_mulVec]
      _ = star x ⬝ᵥ (H *ᵥ x) := by rw [hH.eq]
  have him := congrArg Complex.im hreal
  change -(star x ⬝ᵥ (H *ᵥ x)).im = (star x ⬝ᵥ (H *ᵥ x)).im at him
  linarith

/-- For a positive form, zero kernel trace defect is exactly support inside
the source support projection. -/
theorem kernelDefect_eq_zero_iff_supported {n : Type*}
    [Fintype n] [DecidableEq n] {M E : Matrix n n ℂ}
    (D : SupportData M) (hE : E.PosSemidef) :
    kernelDefect D E = 0 ↔ E = D.Q * E * D.Q := by
  let K : Matrix n n ℂ := 1 - D.Q
  have hKstar : Kᴴ = K := complement_star D
  have hKid : K * K = K := complement_idem D
  have hcomp : (K * E * K).PosSemidef := by
    have h := hE.mul_mul_conjTranspose_same K
    rwa [hKstar] at h
  have htrace : Matrix.trace (K * E * K) = kernelDefect D E := by
    rw [Matrix.trace_mul_cycle, hKid]
    rfl
  constructor
  · intro hdef
    have hcomp0 : K * E * K = 0 :=
      hcomp.trace_eq_zero_iff.mp (htrace.trans hdef)
    let B : Matrix n n ℂ := CFC.sqrt E
    have hBstar : Bᴴ = B := sqrt_isHermitian E
    have hBsq : B * B = E := sqrt_mul_self_eq E hE
    have hgram : (B * K)ᴴ * (B * K) = K * E * K := by
      rw [Matrix.conjTranspose_mul, hKstar, hBstar]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B B K, hBsq]
    have hBK : B * K = 0 := by
      apply Matrix.conjTranspose_mul_self_eq_zero.mp
      rw [hgram, hcomp0]
    have hEK : E * K = 0 := by
      rw [← hBsq, Matrix.mul_assoc, hBK, Matrix.mul_zero]
    have hKE : K * E = 0 := by
      have h := congrArg Matrix.conjTranspose hEK
      simpa only [Matrix.conjTranspose_mul, hKstar, hE.isHermitian.eq,
        Matrix.conjTranspose_zero] using h
    dsimp only [K] at hEK hKE
    rw [Matrix.mul_sub, Matrix.mul_one] at hEK
    rw [Matrix.sub_mul, Matrix.one_mul] at hKE
    have hEQ : E * D.Q = E := (sub_eq_zero.mp hEK).symm
    have hQE : D.Q * E = E := (sub_eq_zero.mp hKE).symm
    calc
      E = D.Q * E := hQE.symm
      _ = D.Q * E * D.Q := by rw [Matrix.mul_assoc, hEQ]
  · intro hsupp
    rw [hsupp]
    have hKQ : (1 - D.Q) * D.Q = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, D.Q_idem, sub_self]
    simp only [kernelDefect, ← Matrix.mul_assoc, hKQ, Matrix.zero_mul,
      Matrix.trace_zero]

/-- A positive matrix is bounded above by a scalar identity exactly when its
L2 operator norm is bounded by that scalar. -/
theorem posSemidef_norm_le_iff_scalar_deficit {n : Type*}
    [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hH : H.PosSemidef) (lam : ℝ) (hlam : 0 ≤ lam) :
    ‖H‖ ≤ lam ↔
      (((lam : ℂ) • (1 : Matrix n n ℂ)) - H).PosSemidef := by
  constructor
  · intro hnorm
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · change ((((lam : ℂ) • (1 : Matrix n n ℂ)) - H)ᴴ) =
        (lam : ℂ) • 1 - H
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, hH.isHermitian.eq]
      simp
    · intro x
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, star_dot_self, Complex.nonneg_iff]
      constructor
      · norm_num
        calc
          (star x ⬝ᵥ (H *ᵥ x)).re
              ≤ |(star x ⬝ᵥ (H *ᵥ x)).re| := le_abs_self _
          _ ≤ ‖H‖ * ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 x‖ :=
            abs_re_star_dot_mulVec_le H x x
          _ ≤ lam * ‖WithLp.toLp 2 x‖ ^ 2 := by
            nlinarith [norm_nonneg (WithLp.toLp 2 x)]
          _ = lam * ∑ i, Complex.normSq (x i) := by
            rw [EuclideanSpace.norm_sq_eq]
            simp only [Complex.sq_norm]
      · norm_num
        exact hermitian_quadratic_im_zero H hH.isHermitian x
  · intro hdef
    let T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
      Matrix.toEuclideanCLM (𝕜 := ℂ) H
    have hTpos : T.IsPositive := by
      rw [← ContinuousLinearMap.isPositive_toLinearMap_iff]
      change (Matrix.toEuclideanLin H).IsPositive
      exact Matrix.isPositive_toEuclideanLin_iff.mpr hH
    have hquad : ∀ z, T.reApplyInnerSelf z ≤ lam * ‖z‖ ^ 2 := by
      intro z
      let x : n → ℂ := WithLp.ofLp z
      have hz := hdef.re_dotProduct_nonneg x
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, star_dot_self] at hz
      have henergy : (∑ i, Complex.normSq (x i)) = ‖z‖ ^ 2 := by
        simpa only [Complex.sq_norm] using (EuclideanSpace.norm_sq_eq z).symm
      have hTform : T.reApplyInnerSelf z =
          (star x ⬝ᵥ (H *ᵥ x)).re := by
        dsimp only [T]
        rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
        simp only [EuclideanSpace.inner_eq_star_dotProduct,
          Matrix.ofLp_toEuclideanCLM]
        rw [dotProduct_comm]
        rfl
      rw [hTform, ← henergy]
      norm_num at hz
      exact hz
    have hray : ∀ z, T.rayleighQuotient z ≤ lam := by
      intro z
      by_cases hz : z = 0
      · subst z
        simpa using hlam
      · change T.reApplyInnerSelf z / ‖z‖ ^ 2 ≤ lam
        rw [div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hz))]
        exact hquad z
    change ‖H‖ ≤ lam
    rw [Matrix.cstar_norm_def]
    change ‖T‖ ≤ lam
    rw [T.norm_eq_iSup_rayleighQuotient hTpos.isSymmetric]
    apply ciSup_le
    intro z
    rw [abs_of_nonneg]
    · exact hray z
    · by_cases hz : z = 0
      · subst z
        simp
      · change 0 ≤ T.reApplyInnerSelf z / ‖z‖ ^ 2
        exact div_nonneg (hTpos.2 z) (sq_nonneg _)

/-- For an operator supported on a projection `Q`, the sharp norm deficit is
`lam Q - H`, with no artificial contribution on the kernel complement. -/
theorem supported_posSemidef_norm_le_iff_deficit {n : Type*}
    [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (D : SupportData M) (H : Matrix n n ℂ) (hH : H.PosSemidef)
    (hHQ : D.Q * H * D.Q = H) (lam : ℝ) (hlam : 0 ≤ lam) :
    ‖H‖ ≤ lam ↔ (((lam : ℂ) • D.Q) - H).PosSemidef := by
  have hscalar : (0 : ℂ) ≤ (lam : ℂ) := by
    rw [Complex.nonneg_iff]
    exact ⟨hlam, rfl⟩
  constructor
  · intro hnorm
    have hfull :=
      (posSemidef_norm_le_iff_scalar_deficit H hH lam hlam).mp hnorm
    have h := hfull.mul_mul_conjTranspose_same D.Q
    rw [D.Q_star] at h
    have heq : D.Q * (((lam : ℂ) • (1 : Matrix n n ℂ)) - H) * D.Q =
        ((lam : ℂ) • D.Q) - H := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, D.Q_idem, hHQ]
    rwa [heq] at h
  · intro hsuppdef
    have hkernel : ((lam : ℂ) • (1 - D.Q)).PosSemidef :=
      (complement_posSemidef D).smul hscalar
    have hfull : (((lam : ℂ) • (1 : Matrix n n ℂ)) - H).PosSemidef := by
      have hadd := hsuppdef.add hkernel
      have heq : (((lam : ℂ) • D.Q) - H) +
            (lam : ℂ) • (1 - D.Q) =
          ((lam : ℂ) • (1 : Matrix n n ℂ)) - H := by
        module
      rwa [heq] at hadd
    exact (posSemidef_norm_le_iff_scalar_deficit H hH lam hlam).mpr hfull

lemma source_supported {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (D : SupportData M) :
    D.Q * M = M ∧ M * D.Q = M := by
  constructor
  · calc
      D.Q * M = D.Q * (D.A * D.A) :=
        congrArg (fun X => D.Q * X) D.A_sq.symm
      _ = (D.Q * D.A) * D.A := by rw [Matrix.mul_assoc]
      _ = D.A * D.A := by rw [D.Q_mul_A]
      _ = M := D.A_sq
  · calc
      M * D.Q = (D.A * D.A) * D.Q :=
        congrArg (fun X => X * D.Q) D.A_sq.symm
      _ = D.A * (D.A * D.Q) := by rw [Matrix.mul_assoc]
      _ = D.A * D.A := by rw [D.A_mul_Q]
      _ = M := D.A_sq

lemma relativeDensity_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {M E : Matrix n n ℂ} (D : SupportData M) (hE : E.PosSemidef) :
    (relativeDensity D E).PosSemidef := by
  have h := hE.mul_mul_conjTranspose_same D.R
  rwa [D.R_star] at h

lemma relativeDensity_supported {n : Type*} [Fintype n] [DecidableEq n]
    {M E : Matrix n n ℂ} (D : SupportData M) :
    D.Q * relativeDensity D E * D.Q = relativeDensity D E := by
  rw [relativeDensity]
  calc
    D.Q * (D.R * E * D.R) * D.Q =
        (D.Q * D.R) * E * (D.R * D.Q) := by
      simp only [Matrix.mul_assoc]
    _ = D.R * E * D.R := by rw [D.Q_mul_R, D.R_mul_Q]

/-- On the zero-defect branch, the original form is reconstructed exactly
from its support-relative density. -/
theorem reconstruct_from_relativeDensity {n : Type*}
    [Fintype n] [DecidableEq n] {M E : Matrix n n ℂ}
    (D : SupportData M) (hsupp : E = D.Q * E * D.Q) :
    E = D.A * relativeDensity D E * D.A := by
  calc
    E = D.Q * E * D.Q := hsupp
    _ = (D.A * D.R) * E * (D.R * D.A) := by
      rw [D.A_mul_R, D.R_mul_A]
    _ = D.A * relativeDensity D E * D.A := by
      simp only [relativeDensity, Matrix.mul_assoc]

/-- On the supported branch, domination by the source form is equivalent to
the same scalar domination of the relative density on `Q`. -/
theorem domination_iff_relativeDensity_deficit {n : Type*}
    [Fintype n] [DecidableEq n] {M E : Matrix n n ℂ}
    (D : SupportData M) (hsupp : E = D.Q * E * D.Q)
    (lam : ℝ) :
    (((lam : ℂ) • M) - E).PosSemidef ↔
      (((lam : ℂ) • D.Q) - relativeDensity D E).PosSemidef := by
  have hRMR : D.R * M * D.R = D.Q := by
    calc
      D.R * M * D.R = D.R * (D.A * D.A) * D.R :=
        congrArg (fun X => D.R * X * D.R) D.A_sq.symm
      _ = (D.R * D.A) * (D.A * D.R) := by
        simp only [Matrix.mul_assoc]
      _ = D.Q := by rw [D.R_mul_A, D.A_mul_R, D.Q_idem]
  have hAQA : D.A * D.Q * D.A = M := by
    calc
      D.A * D.Q * D.A = D.A * D.A := by rw [D.A_mul_Q]
      _ = M := D.A_sq
  have hrec := reconstruct_from_relativeDensity D hsupp
  constructor
  · intro hdom
    have h := hdom.mul_mul_conjTranspose_same D.R
    rw [D.R_star] at h
    have heq : D.R * (((lam : ℂ) • M) - E) * D.R =
        ((lam : ℂ) • D.Q) - relativeDensity D E := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, hRMR]
      rfl
    rwa [heq] at h
  · intro hrel
    have h := hrel.mul_mul_conjTranspose_same D.A
    rw [D.A_star] at h
    have heq : D.A * (((lam : ℂ) • D.Q) - relativeDensity D E) * D.A =
        ((lam : ℂ) • M) - E := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, hAQA, ← hrec]
    rwa [heq] at h

/-- Any finite Loewner domination forces the second form to be supported on
the support of the first. -/
theorem domination_implies_supported {n : Type*}
    [Fintype n] [DecidableEq n] {M E : Matrix n n ℂ}
    (D : SupportData M) (hE : E.PosSemidef) (lam : ℝ)
    (hdom : (((lam : ℂ) • M) - E).PosSemidef) :
    E = D.Q * E * D.Q := by
  let K : Matrix n n ℂ := 1 - D.Q
  have hKstar : Kᴴ = K := complement_star D
  have hKM : K * M = 0 := by
    obtain ⟨hQM, -⟩ := source_supported D
    dsimp only [K]
    rw [Matrix.sub_mul, Matrix.one_mul, hQM, sub_self]
  have hcomp : (K * E * K).PosSemidef := by
    have h := hE.mul_mul_conjTranspose_same K
    rwa [hKstar] at h
  have hneg : (-(K * E * K)).PosSemidef := by
    have h := hdom.mul_mul_conjTranspose_same K
    rw [hKstar] at h
    have hleft : K * (((lam : ℂ) • M) - E) = -(K * E) := by
      rw [Matrix.mul_sub, Matrix.mul_smul, hKM]
      simp
    have heq : K * (((lam : ℂ) • M) - E) * K = -(K * E * K) := by
      calc
        K * (((lam : ℂ) • M) - E) * K = (-(K * E)) * K :=
          congrArg (fun X => X * K) hleft
        _ = -(K * E * K) := by simp
    rwa [heq] at h
  have hcomp0 : K * E * K = 0 := by
    apply le_antisymm
    · rw [← neg_nonneg]
      exact Matrix.nonneg_iff_posSemidef.mpr hneg
    · exact Matrix.nonneg_iff_posSemidef.mpr hcomp
  apply (kernelDefect_eq_zero_iff_supported D hE).mp
  have htrace : Matrix.trace (K * E * K) = kernelDefect D E := by
    have hKid : K * K = K := complement_idem D
    rw [Matrix.trace_mul_cycle, hKid]
    rfl
  calc
    kernelDefect D E = Matrix.trace (K * E * K) := htrace.symm
    _ = 0 := by rw [hcomp0, Matrix.trace_zero]

theorem exists_domination_iff_kernelDefect_zero {n : Type*}
    [Fintype n] [DecidableEq n] {M E : Matrix n n ℂ}
    (D : SupportData M) (hE : E.PosSemidef) :
    (∃ lam : ℝ, 0 ≤ lam ∧ (((lam : ℂ) • M) - E).PosSemidef) ↔
      kernelDefect D E = 0 := by
  have hH : (relativeDensity D E).PosSemidef := relativeDensity_posSemidef D hE
  have hHQ := relativeDensity_supported (D := D) (E := E)
  constructor
  · rintro ⟨lam, -, hdom⟩
    exact (kernelDefect_eq_zero_iff_supported D hE).mpr
      (domination_implies_supported D hE lam hdom)
  · intro hdef
    have hsupp := (kernelDefect_eq_zero_iff_supported D hE).mp hdef
    refine ⟨‖relativeDensity D E‖, norm_nonneg _, ?_⟩
    exact (domination_iff_relativeDensity_deficit D hsupp _).mpr
      ((supported_posSemidef_norm_le_iff_deficit D _ hH hHQ _ (norm_nonneg _)).mp le_rfl)

theorem sharp_domination_on_zero_defect {n : Type*}
    [Fintype n] [DecidableEq n] {M E : Matrix n n ℂ}
    (D : SupportData M) (hE : E.PosSemidef)
    (hdef : kernelDefect D E = 0) :
    E = D.A * relativeDensity D E * D.A
      ∧ ∀ lam : ℝ, 0 ≤ lam →
        ((((lam : ℂ) • M) - E).PosSemidef ↔
          ‖relativeDensity D E‖ ≤ lam) := by
  have hsupp := (kernelDefect_eq_zero_iff_supported D hE).mp hdef
  have hH : (relativeDensity D E).PosSemidef := relativeDensity_posSemidef D hE
  have hHQ := relativeDensity_supported (D := D) (E := E)
  refine ⟨reconstruct_from_relativeDensity D hsupp, ?_⟩
  intro lam hlam
  exact (domination_iff_relativeDensity_deficit D hsupp lam).trans
    (supported_posSemidef_norm_le_iff_deficit D _ hH hHQ lam hlam).symm

theorem unit_domination_iff_kernelDefect_and_norm {n : Type*}
    [Fintype n] [DecidableEq n] {M E : Matrix n n ℂ}
    (D : SupportData M) (hE : E.PosSemidef) :
    (((1 : ℂ) • M) - E).PosSemidef ↔
      kernelDefect D E = 0 ∧ ‖relativeDensity D E‖ ≤ 1 := by
  have hH : (relativeDensity D E).PosSemidef := relativeDensity_posSemidef D hE
  have hHQ := relativeDensity_supported (D := D) (E := E)
  constructor
  · intro hdom
    have hsupp := domination_implies_supported D hE 1 hdom
    have hdef := (kernelDefect_eq_zero_iff_supported D hE).mpr hsupp
    refine ⟨hdef, ?_⟩
    have hrel := (domination_iff_relativeDensity_deficit D hsupp 1).mp hdom
    exact (supported_posSemidef_norm_le_iff_deficit D _ hH hHQ 1 zero_le_one).mpr hrel
  · rintro ⟨hdef, hnorm⟩
    have hsupp := (kernelDefect_eq_zero_iff_supported D hE).mp hdef
    apply (domination_iff_relativeDensity_deficit D hsupp 1).mpr
    exact (supported_posSemidef_norm_le_iff_deficit D _ hH hHQ 1 zero_le_one).mp hnorm

/-- Full singular-support relative-metric theorem, including existence of a
finite domination constant, the sharp constant, and the unit-order test. -/
theorem relativeMetricDensity_singular_exact {n : Type*}
    [Fintype n] [DecidableEq n] {M E : Matrix n n ℂ}
    (D : SupportData M) (hE : E.PosSemidef) :
    let H := relativeDensity D E
    H.PosSemidef
      ∧ ((∃ lam : ℝ, 0 ≤ lam ∧ (((lam : ℂ) • M) - E).PosSemidef) ↔
          kernelDefect D E = 0)
      ∧ (kernelDefect D E = 0 →
          E = D.A * H * D.A
            ∧ ∀ lam : ℝ, 0 ≤ lam →
              ((((lam : ℂ) • M) - E).PosSemidef ↔ ‖H‖ ≤ lam))
      ∧ ((((1 : ℂ) • M) - E).PosSemidef ↔
          kernelDefect D E = 0 ∧ ‖H‖ ≤ 1) := by
  dsimp only
  exact ⟨relativeDensity_posSemidef D hE,
    exists_domination_iff_kernelDefect_zero D hE,
    sharp_domination_on_zero_defect D hE,
    unit_domination_iff_kernelDefect_and_norm D hE⟩

/-- Positive rescaling of a source map preserves its physical range and hence
has zero Schur residual relative to the original source. -/
theorem scalar_rescaling_has_zero_sourceSchurResidual {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ) (a : ℂ) :
    sourceSchurResidual S (a • S) = 0 := by
  apply (sourceSchurResidual_eq_zero_iff_rangeIncluded S (a • S)).mpr
  refine ⟨a • (1 : Matrix (Fin e) (Fin e) ℂ), ?_⟩
  rw [Matrix.mul_smul, Matrix.mul_one]

/-- A one-dimensional witness that source-range/Schur inclusion does not
imply coefficient-form metric domination: scaling a nonzero source by two
keeps the Schur residual zero but multiplies its Gram form by four. -/
theorem zero_sourceSchurResidual_but_metric_order_fails :
    let S : Matrix (Fin 1) (Fin 1) ℂ := 1
    sourceSchurResidual S ((2 : ℂ) • S) = 0
      ∧ ¬ (Sᴴ * S - (((2 : ℂ) • S)ᴴ * ((2 : ℂ) • S))).PosSemidef := by
  dsimp only
  constructor
  · exact scalar_rescaling_has_zero_sourceSchurResidual 1 (2 : ℂ)
  · intro hpos
    have h := hpos.dotProduct_mulVec_nonneg (fun _ : Fin 1 => (1 : ℂ))
    norm_num [Matrix.mulVec, dotProduct] at h

end RelativeMetricSupportDensity
end NCG
