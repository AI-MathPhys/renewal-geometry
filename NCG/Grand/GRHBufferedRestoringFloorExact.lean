/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SampledVersusKilledExact

/-!
# Buffered rowwise lower bound for the restoring short

Exact encoding of `thm:GRH-buffered-restoring-floor` (GRH.14) in the sector coordinates
of `GRHRestoringShortExact`: with `D = C₁ + C₂ + C₃` (translated-test, taper-boundary,
stable-return rows, each `C_j ⪰ 0` with blocks `[[C_j^HH, C_j^HL], [C_j^HL^*, C_j^LL]]`),
weights `α_j > 0` summing to one, `γ_θ = (θ - 1) h` and `M_j ≥ ‖H C_j H‖` (encoded as
`C_j^HH ⪯ M_j I`),

`𝓡_θ ⪰ ∑_j (α_j γ_θ) / (M_j + α_j γ_θ) · C_j^LL`.

The proof splits the high buffer `γ_θ H` among the rows (`G ⪰ ∑_j G_j`,
`G_j = C_j^HH + α_j γ_θ I`), uses Loewner inversion and the parallel-sum block inequality
`X^* (∑ G_j)⁻¹ X ⪯ ∑ X_j^* G_j⁻¹ X_j`, the spectral comparison
`(C_j^HH + a I)⁻¹ ⪯ M_j/(M_j + a) · (C_j^HH)^†` on the supported range, and the Schur
positivity `X_j^* (C_j^HH)^† X_j ⪯ C_j^LL`.
-/

open Matrix Finset NCG.GeometricThresholdBank NCG.SourceCoercivityInfluence NCG.PsdBlockSchur
  NCG.LocalizerExtensionFloor NCG.GRHRestoringShort NCG.SampledVersusKilled
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace GRHBufferedRestoringFloor

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

variable {m p : ℕ}

/-! ### Spectral comparison on the supported range -/

/-- `(C + a I)⁻¹` through the spectral calculus of `C ⪰ 0`. -/
theorem shift_inv_spectral {C : Matrix (Fin m) (Fin m) ℂ} (hC : C.PosSemidef) {a : ℝ}
    (ha : 0 < a) : (C + (a : ℂ) • 1)⁻¹ = spectralFunction hC.1 (fun l => (l + a)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  have e : C + (a : ℂ) • 1 = spectralFunction hC.1 (fun l => id l + a) := by
    rw [spectralFunction_add, spectralFunction_id, spectralFunction_const]
  rw [e, spectralFunction_mul]
  have : spectralFunction hC.1 (fun l => (l + a)⁻¹ * (id l + a))
      = spectralFunction hC.1 (fun _ => 1) := by
    refine spectralFunction_congr hC.1 fun i => ?_
    have := hC.eigenvalues_nonneg i
    simp only [id]
    exact inv_mul_cancel₀ (by positivity)
  rw [this, spectralFunction_const]
  simp

theorem shift_posDef {C : Matrix (Fin m) (Fin m) ℂ} (hC : C.PosSemidef) {a : ℝ} (ha : 0 < a) :
    (C + (a : ℂ) • 1).PosDef := by
  refine posDef_of_floor (γ := a) ?_ ha
  rw [add_sub_cancel_right]
  exact hC

/-- `C ⪯ M I` bounds the eigenvalues of `C`. -/
theorem eigenvalues_le_of_le {C : Matrix (Fin m) (Fin m) ℂ} (hC : C.PosSemidef) {M : ℝ}
    (hM : ((M : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) - C).PosSemidef) (i : Fin m) :
    hC.1.eigenvalues i ≤ M := by
  have e : (M : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) - C
      = spectralFunction hC.1 (fun l => M - id l) := by
    rw [spectralFunction_sub, spectralFunction_const, spectralFunction_id]
  rw [e] at hM
  have := nonneg_of_spectralFunction_posSemidef hC.1 _ hM i
  simp only [id] at this
  linarith

/-- **Local spectral comparison**: on the supported range of `C ⪰ 0` with `C ⪯ M I`,
`(C + a I)⁻¹ ⪯ M/(M + a) · C^†`. -/
theorem local_comparison {C : Matrix (Fin m) (Fin m) ℂ} (hC : C.PosSemidef) {M a : ℝ}
    (hM : ((M : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) - C).PosSemidef) (ha : 0 < a) :
    (supportProj hC.1 * (((M / (M + a) : ℝ) : ℂ) • pinv hC.1 - (C + (a : ℂ) • 1)⁻¹)
      * supportProj hC.1).PosSemidef := by
  rw [shift_inv_spectral hC ha]
  have e : ((M / (M + a) : ℝ) : ℂ) • pinv hC.1
      = spectralFunction hC.1 (fun l => M / (M + a) * (if 0 < l then l⁻¹ else 0)) := by
    unfold pinv
    rw [spectralFunction_smul]
  rw [e, ← spectralFunction_sub]
  unfold supportProj
  rw [spectralFunction_mul, spectralFunction_mul]
  refine spectralFunction_posSemidef hC.1 _ fun i => ?_
  have h0 := hC.eigenvalues_nonneg i
  have hle := eigenvalues_le_of_le hC hM i
  split_ifs with hl
  · have h1 : 0 < hC.1.eigenvalues i + a := by linarith
    have h2 : 0 < M + a := by linarith
    have key : (hC.1.eigenvalues i + a)⁻¹ ≤ M / (M + a) * (hC.1.eigenvalues i)⁻¹ := by
      rw [show M / (M + a) * (hC.1.eigenvalues i)⁻¹ = M / ((M + a) * hC.1.eigenvalues i) by
        field_simp]
      rw [le_div_iff₀ (by positivity), inv_mul_le_iff₀ h1]
      nlinarith [mul_le_mul_of_nonneg_left hle ha.le]
    simp only [one_mul, mul_one]
    linarith
  · simp

/-! ### Block sums -/

theorem fromBlocks_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin m) (Fin m) ℂ)
    (B : ι → Matrix (Fin m) (Fin p) ℂ) (C : ι → Matrix (Fin p) (Fin m) ℂ)
    (D : ι → Matrix (Fin p) (Fin p) ℂ) :
    fromBlocks (∑ i ∈ s, A i) (∑ i ∈ s, B i) (∑ i ∈ s, C i) (∑ i ∈ s, D i)
      = ∑ i ∈ s, fromBlocks (A i) (B i) (C i) (D i) := by
  ext (i | i) (j | j) <;> simp [Matrix.sum_apply]

/-! ### The buffered floor -/

variable (AH : Matrix (Fin m) (Fin m) ℂ) (CH : Fin 3 → Matrix (Fin m) (Fin m) ℂ)
  (CX : Fin 3 → Matrix (Fin m) (Fin p) ℂ) (CL : Fin 3 → Matrix (Fin p) (Fin p) ℂ) (h θ : ℝ)
  (α M : Fin 3 → ℝ)

/-- **(GRH.14)**: the buffered rowwise lower bound
`𝓡_θ ⪰ ∑_j α_j γ_θ / (M_j + α_j γ_θ) · C_j^LL`. -/
theorem buffered_restoring_floor (hθ : 1 < θ) (hh : 0 < h)
    (hAH : (AH - ((θ * h : ℝ) : ℂ) • 1).PosSemidef)
    (hC : ∀ j, (fromBlocks (CH j) (CX j) (CX j)ᴴ (CL j)).PosSemidef)
    (hα : ∀ j, 0 < α j) (hα1 : ∑ j, α j = 1) (hM0 : ∀ j, 0 ≤ M j)
    (hM : ∀ j, ((M j : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) - CH j).PosSemidef)
    (hG : (highBlock AH (∑ j, CH j) h).PosDef) :
    (restoringShort AH (∑ j, CH j) (∑ j, CX j) (∑ j, CL j) h hG.1
      - ∑ j, (((α j * ((θ - 1) * h)) / (M j + α j * ((θ - 1) * h)) : ℝ) : ℂ)
        • CL j).PosSemidef := by
  -- notation
  set γ : ℝ := (θ - 1) * h with hγ
  have hγpos : 0 < γ := mul_pos (by linarith) hh
  set a : Fin 3 → ℝ := fun j => α j * γ with ha
  have hapos : ∀ j, 0 < a j := fun j => mul_pos (hα j) hγpos
  have hCH : ∀ j, (CH j).PosSemidef := fun j => posSemidef_left_of_fromBlocks (hC j)
  have hGjPD : ∀ j, (CH j + ((a j : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)).PosDef :=
    fun j => shift_posDef (hCH j) (hapos j)
  set S : Matrix (Fin m) (Fin m) ℂ := ∑ j, (CH j + ((a j : ℝ) : ℂ) • 1) with hS
  set X : Matrix (Fin m) (Fin p) ℂ := ∑ j, CX j with hX
  set G : Matrix (Fin m) (Fin m) ℂ := highBlock AH (∑ j, CH j) h with hGdef
  -- `∑ a_j = γ`
  have hsum_a : ∑ j, ((a j : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) = ((γ : ℝ) : ℂ) • 1 := by
    rw [← Finset.sum_smul]
    congr 1
    rw [← Complex.ofReal_sum]
    congr 1
    simp only [ha]
    rw [← Finset.sum_mul, hα1, one_mul]
  -- `S ≻ 0` and `G ⪰ S`
  have hSPD : S.PosDef := by
    refine posDef_of_floor (γ := γ) ?_ hγpos
    have e : S - ((γ : ℝ) : ℂ) • 1 = ∑ j, CH j := by
      rw [hS, ← hsum_a, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [add_sub_cancel_right]
    rw [e]
    exact Matrix.posSemidef_sum _ fun j _ => hCH j
  have hGS : (G - S).PosSemidef := by
    have e : G - S = AH - ((θ * h : ℝ) : ℂ) • 1 := by
      rw [hGdef, hS]
      unfold highBlock
      have e2 : ∑ j, (CH j + ((a j : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))
          = ∑ j, CH j + ((γ : ℝ) : ℂ) • 1 := by
        rw [← hsum_a, ← Finset.sum_add_distrib]
      rw [e2]
      have e3 : ((θ * h : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)
          = (h : ℂ) • 1 + ((γ : ℝ) : ℂ) • 1 := by
        rw [← add_smul, hγ]
        congr 1
        push_cast
        ring
      rw [e3]
      abel
    rw [e]
    exact hAH
  -- Loewner inversion: `S⁻¹ - G⁻¹ ⪰ 0`
  have hLoe := inv_le_inv_of_le hSPD hG hGS
  -- the parallel-sum block inequality
  have hNj : ∀ j, (fromBlocks (CH j + ((a j : ℝ) : ℂ) • 1) (CX j) (CX j)ᴴ
      ((CX j)ᴴ * (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹ * CX j)).PosSemidef := by
    intro j
    have hherm : ((CX j)ᴴ * (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹ * CX j).IsHermitian := by
      rw [← pinv_eq_inv (hGjPD j)]
      exact ((pinv_posSemidef _).conjTranspose_mul_mul_same (CX j)).1
    refine (posSemidef_block_iff (hGjPD j).posSemidef (CX j) _ hherm).mpr
      ⟨range_condition_of_posDef (hGjPD j) (CX j), ?_⟩
    rw [pinv_eq_inv (hGjPD j), sub_self]
    exact PosSemidef.zero
  have hN : (fromBlocks S X Xᴴ
      (∑ j, (CX j)ᴴ * (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹ * CX j)).PosSemidef := by
    have e : fromBlocks S X Xᴴ (∑ j, (CX j)ᴴ * (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹ * CX j)
        = ∑ j, fromBlocks (CH j + ((a j : ℝ) : ℂ) • 1) (CX j) (CX j)ᴴ
          ((CX j)ᴴ * (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹ * CX j) := by
      rw [hS, hX, conjTranspose_sum, fromBlocks_sum]
    rw [e]
    exact Matrix.posSemidef_sum _ fun j _ => hNj j
  have hpar := schur_posSemidef hSPD.posSemidef X _ hN
  rw [pinv_eq_inv hSPD] at hpar
  -- congruence of Loewner inversion
  have hcong := hLoe.conjTranspose_mul_mul_same X
  rw [Matrix.mul_sub, Matrix.sub_mul] at hcong
  -- local comparisons
  have hloc : ∀ j, ((((M j / (M j + a j) : ℝ) : ℂ) • ((CX j)ᴴ * pinv (hCH j).1 * CX j))
      - (CX j)ᴴ * (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹ * CX j).PosSemidef := by
    intro j
    have hQB : supportProj (hCH j).1 * CX j = CX j := by
      rw [← mul_pinv_eq_supportProj]
      exact range_condition_of_posSemidef (hCH j) (CX j) (CL j) (hC j)
    have hBQ : (CX j)ᴴ * supportProj (hCH j).1 = (CX j)ᴴ := by
      have := congrArg conjTranspose hQB
      rwa [conjTranspose_mul, (supportProj_posSemidef (hCH j).1).1.eq] at this
    have hsand := (local_comparison (hCH j) (hM j) (hapos j)).conjTranspose_mul_mul_same (CX j)
    have e : (CX j)ᴴ * (supportProj (hCH j).1
          * (((M j / (M j + a j) : ℝ) : ℂ) • pinv (hCH j).1
            - (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹) * supportProj (hCH j).1) * CX j
        = (((M j / (M j + a j) : ℝ) : ℂ) • ((CX j)ᴴ * pinv (hCH j).1 * CX j))
          - (CX j)ᴴ * (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹ * CX j := by
      have e1 : (CX j)ᴴ * (supportProj (hCH j).1
          * (((M j / (M j + a j) : ℝ) : ℂ) • pinv (hCH j).1
            - (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹) * supportProj (hCH j).1) * CX j
          = ((CX j)ᴴ * supportProj (hCH j).1)
            * (((M j / (M j + a j) : ℝ) : ℂ) • pinv (hCH j).1
              - (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹) * (supportProj (hCH j).1 * CX j) := by
        simp only [Matrix.mul_assoc]
      rw [e1, hBQ, hQB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [e] at hsand
    exact hsand
  -- Schur positivity of each row
  have hsch : ∀ j, (CL j - (CX j)ᴴ * pinv (hCH j).1 * CX j).PosSemidef :=
    fun j => schur_posSemidef (hCH j) (CX j) (CL j) (hC j)
  have hcoef : ∀ j, 0 ≤ M j / (M j + a j) := fun j =>
    div_nonneg (hM0 j) (by linarith [hM0 j, hapos j])
  have hd : ∀ j, (((α j * ((θ - 1) * h)) / (M j + α j * ((θ - 1) * h)) : ℝ) : ℂ)
      = 1 - ((M j / (M j + a j) : ℝ) : ℂ) := by
    intro j
    have h1 : M j + a j ≠ 0 := by linarith [hM0 j, hapos j]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    congr 1
    simp only [ha, hγ] at h1 ⊢
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq h1]
    ring
  -- assembly
  have key : restoringShort AH (∑ j, CH j) (∑ j, CX j) (∑ j, CL j) h hG.1
      - ∑ j, (((α j * ((θ - 1) * h)) / (M j + α j * ((θ - 1) * h)) : ℝ) : ℂ) • CL j
      = (Xᴴ * S⁻¹ * X - Xᴴ * G⁻¹ * X)
        + ((∑ j, (CX j)ᴴ * (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹ * CX j) - Xᴴ * S⁻¹ * X)
        + ∑ j, ((M j / (M j + a j) : ℝ) : ℂ) • (CL j - (CX j)ᴴ * pinv (hCH j).1 * CX j)
        + ∑ j, ((((M j / (M j + a j) : ℝ) : ℂ) • ((CX j)ᴴ * pinv (hCH j).1 * CX j))
          - (CX j)ᴴ * (CH j + ((a j : ℝ) : ℂ) • 1)⁻¹ * CX j) := by
    unfold restoringShort
    rw [pinv_eq_inv hG]
    simp only [hd, sub_smul, one_smul, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [key]
  exact ((hcong.add hpar).add (Matrix.posSemidef_sum _ fun j _ =>
    (hsch j).smul (Complex.zero_le_real.mpr (hcoef j)))).add
    (Matrix.posSemidef_sum _ fun j _ => hloc j)

end GRHBufferedRestoringFloor
end NCG
