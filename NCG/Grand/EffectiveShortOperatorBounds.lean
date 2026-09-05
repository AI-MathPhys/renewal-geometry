/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.SchurCluster
import NCG.Grand.BrandNewEasy02
import NCG.Grand.GTEffectiveShort
import NCG.Grand.SourceCoercivityInfluenceExact

/-!
# Operator bounds for effective shorts

This file closes the operator-level clauses of the Gran--Tensor records
`cor:GT-effective-corrector`, `thm:GT-occurrence-Feshbach`, and
`thm:GT-connected-load`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Norms.L2Operator

namespace NCG

set_option maxHeartbeats 1000000

/-- `cor:GT-effective-corrector`, full operator form.  If the tail block has
floor `γ`, the corrected short has floor `δ`, and the corrector residual has
operator norm at most `ε`, then the exact short has floor
`δ - ε² / γ`. -/
theorem gt_effective_corrector_operator {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin q) ℂ) (K : Matrix (Fin q) (Fin p) ℂ)
    [Invertible C] {δ ε γ : ℝ} (hγ : 0 < γ) (hC : C.PosDef)
    (hCfloor : (C - (γ : ℂ) • 1).PosSemidef)
    (hcorrected :
      ((A - B * K - Kᴴ * Bᴴ + Kᴴ * (C * K)) - (δ : ℂ) • 1).PosSemidef)
    (hresidual : ‖C * K - Bᴴ‖ ≤ ε) :
    ((A - B * C⁻¹ * Bᴴ) - ((δ - ε ^ 2 / γ : ℝ) : ℂ) • 1).PosSemidef := by
  have hnorm :
      (((ε ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ)
        - (C * K - Bᴴ)ᴴ * (C * K - Bᴴ)).PosSemidef :=
    posSemidef_smul_one_sub_gram (C * K - Bᴴ) ε hresidual
  have hnorm' :
      (((ε : ℂ) ^ 2) • (1 : Matrix (Fin p) (Fin p) ℂ)
        - (C * K - Bᴴ)ᴴ * (C * K - Bᴴ)).PosSemidef := by
    simpa only [Complex.ofReal_pow] using hnorm
  have hupper := (cluster_feshbach_bound (δ := γ) (β := ε) (C * K - Bᴴ) C 0 hγ
    (by simpa using hC) (by simpa using hCfloor) hnorm').2
  simp only [zero_smul, sub_zero] at hupper
  have hexact := (gt_effective_corrector A B C K hC.1.eq).1
  have hsum := hcorrected.add hupper
  rw [hexact] at hsum
  have hrearrange :
      ((A - B * C⁻¹ * Bᴴ + (C * K - Bᴴ)ᴴ * (C⁻¹ * (C * K - Bᴴ)))
          - (δ : ℂ) • 1)
        + (((ε ^ 2 / γ : ℝ) : ℂ) • 1
          - (C * K - Bᴴ)ᴴ * C⁻¹ * (C * K - Bᴴ))
      = (A - B * C⁻¹ * Bᴴ) - ((δ - ε ^ 2 / γ : ℝ) : ℂ) • 1 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.mul_assoc]
    push_cast
    ring
  rwa [hrearrange] at hsum

/-- `thm:GT-occurrence-Feshbach`, positivity clause.  A positive block action
with an invertible positive occurrence block has a positive effective Schur
action. -/
theorem gt_occurrence_feshbach_posSemidef {P Q : Type*} [Fintype P]
    [Fintype Q] [DecidableEq Q]
    (A : Matrix P P ℂ) (B : Matrix P Q ℂ) (C : Matrix Q Q ℂ)
    [Invertible C] (hC : C.PosDef)
    (hblock : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    (A - B * C⁻¹ * Bᴴ).PosSemidef := by
  have hZ : C * (C⁻¹ * Bᴴ) = Bᴴ := by
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  have hshort := (schur_short A B C (C⁻¹ * Bᴴ) hZ hblock).1
  have hsimp : (C⁻¹ * Bᴴ)ᴴ * C * (C⁻¹ * Bᴴ) = B * C⁻¹ * Bᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hC.1.eq]
    simp only [Matrix.mul_assoc]
    rw [hZ]
  rwa [hsimp] at hshort

/-- `thm:GT-connected-load`, operator assembly.  A pointwise relative load
bound assembles into the two advertised Loewner floors. -/
theorem gt_connected_load_operator {p : Type*} [Fintype p] [DecidableEq p]
    (S L₀ V R : Matrix p p ℂ) (hS : S.IsHermitian) (hL₀ : L₀.IsHermitian)
    (hV : V.IsHermitian) (hR : R.PosSemidef) {α γ : ℝ} (hα : α < 1)
    (hdecomp : S = L₀ + V - R)
    (hload : ∀ x : p → ℂ,
      |(star x ⬝ᵥ (V *ᵥ x)).re| + (star x ⬝ᵥ (R *ᵥ x)).re
        ≤ α * (star x ⬝ᵥ (L₀ *ᵥ x)).re)
    (hfloor : (L₀ - (γ : ℂ) • 1).PosSemidef) :
    (S - ((1 - α : ℝ) : ℂ) • L₀).PosSemidef ∧
      (((1 - α : ℝ) : ℂ) • L₀
        - (((1 - α) * γ : ℝ) : ℂ) • 1).PosSemidef := by
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · change (S - ((1 - α : ℝ) : ℂ) • L₀)ᴴ = _
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hS.eq, hL₀.eq,
        Complex.star_def, Complex.conj_ofReal]
    · have hdecomp' :
          (star x ⬝ᵥ (S *ᵥ x)).re = (star x ⬝ᵥ (L₀ *ᵥ x)).re
            + (star x ⬝ᵥ (V *ᵥ x)).re - (star x ⬝ᵥ (R *ᵥ x)).re := by
        rw [hdecomp, Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub,
          dotProduct_add, Complex.sub_re, Complex.add_re]
      have hfloor' : γ * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (L₀ *ᵥ x)).re := by
        have hx := hfloor.dotProduct_mulVec_nonneg x
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
          dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.le_def] at hx
        simpa [Complex.mul_re, Complex.mul_im] using hx.1
      have hscalar := gt_connected_load
        (star x ⬝ᵥ (S *ᵥ x)).re
        (star x ⬝ᵥ (L₀ *ᵥ x)).re
        (star x ⬝ᵥ (V *ᵥ x)).re
        (star x ⬝ᵥ (R *ᵥ x)).re α γ
        (star x ⬝ᵥ x).re
        (Complex.le_def.mp (star_dot_self_nonneg x)).1 hα hdecomp' (hload x) hfloor'
      rw [Complex.le_def]
      constructor
      · simp only [Complex.zero_re, Matrix.sub_mulVec, Matrix.smul_mulVec,
          dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.sub_re,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact sub_nonneg.mpr hscalar.2
      · let q := star x ⬝ᵥ ((S - ((1 - α : ℝ) : ℂ) • L₀) *ᵥ x)
        have htarget : (S - ((1 - α : ℝ) : ℂ) • L₀).IsHermitian := by
          change (S - ((1 - α : ℝ) : ℂ) • L₀)ᴴ = _
          rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hS.eq, hL₀.eq,
            Complex.star_def, Complex.conj_ofReal]
        have hself : star q = q := by
          dsimp [q]
          calc
            star (star x ⬝ᵥ ((S - ((1 - α : ℝ) : ℂ) • L₀) *ᵥ x)) =
                star ((S - ((1 - α : ℝ) : ℂ) • L₀) *ᵥ x) ⬝ᵥ x := by
              rw [star_dotProduct, star_star]
            _ = star x ⬝ᵥ ((S - ((1 - α : ℝ) : ℂ) • L₀) *ᵥ x) :=
              (SourceCoercivityInfluence.dotProduct_mulVec_hermitian htarget x x).symm
        have him : -q.im = q.im := by
          simpa using congrArg Complex.im hself
        have himzero : q.im = 0 := by linarith
        simpa [q] using himzero.symm
  · have hsmul := hfloor.smul (Complex.zero_le_real.mpr (by linarith : 0 ≤ 1 - α))
    have hrearrange :
        ((1 - α : ℝ) : ℂ) • (L₀ - (γ : ℂ) • 1)
          = ((1 - α : ℝ) : ℂ) • L₀
            - (((1 - α) * γ : ℝ) : ℂ) • 1 := by
      ext i j
      simp [Matrix.smul_apply]
      ring
    rwa [hrearrange] at hsmul

end NCG
