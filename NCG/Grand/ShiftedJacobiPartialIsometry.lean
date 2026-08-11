/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ArJacobiEdge
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Shifted Jacobi partial isometry

The shifted nonzero-field translation is constructed as an explicit partial
permutation matrix.  Its exact Gram projection gives partial isometry, rank,
and operator norm before Fourier transformation to multiplicative characters.
-/

open Matrix
open scoped ComplexOrder Norms.L2Operator

namespace NCG
namespace ShiftedJacobiPartialIsometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Matrix of `f(x) ↦ 1_{Fˣ}(x-h) f(x-h)` on the nonzero field elements. -/
noncomputable def shiftedTranslationMatrix (h : Fˣ) : Matrix Fˣ Fˣ ℂ :=
  fun x y => if (x : F) - (h : F) = (y : F) then 1 else 0

noncomputable def shiftedRangeWeight (h : Fˣ) (x : Fˣ) : ℂ :=
  if x = h then 0 else 1

theorem shiftedTranslationMatrix_row_at_shift_zero (h : Fˣ) (y : Fˣ) :
    shiftedTranslationMatrix h h y = 0 := by
  unfold shiftedTranslationMatrix
  have hy : (y : F) ≠ 0 := Units.ne_zero y
  have hy' : ¬(0 : F) = (y : F) := fun he => hy he.symm
  simp [hy']

theorem shiftedTranslationMatrix_mul_conjTranspose
    (h : Fˣ) :
    shiftedTranslationMatrix h * (shiftedTranslationMatrix h)ᴴ =
      Matrix.diagonal (shiftedRangeWeight h) := by
  ext x z
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hx : x = h
  · subst x
    simp [shiftedTranslationMatrix_row_at_shift_zero, shiftedRangeWeight]
  · have hxcoe : (x : F) ≠ (h : F) := fun he => hx (Units.ext he)
    let y0 : Fˣ := Units.mk0 ((x : F) - (h : F)) (sub_ne_zero.mpr hxcoe)
    by_cases hxz : x = z
    · subst z
      rw [Finset.sum_eq_single y0]
      · simp [shiftedTranslationMatrix, shiftedRangeWeight, hx, y0]
      · intro y _ hy
        have hne : (x : F) - (h : F) ≠ (y : F) := by
          intro heq
          apply hy
          apply Units.ext
          exact heq.symm
        simp [shiftedTranslationMatrix, hne]
      · simp
    · have hdisjoint : ∀ y : Fˣ,
          shiftedTranslationMatrix h x y *
            (shiftedTranslationMatrix h)ᴴ y z = 0 := by
        intro y
        rw [Matrix.conjTranspose_apply]
        unfold shiftedTranslationMatrix
        by_cases hxy : (x : F) - (h : F) = (y : F)
        · have hzy : (z : F) - (h : F) ≠ (y : F) := by
            intro hzy
            apply hxz
            apply Units.ext
            exact sub_left_inj.mp (hxy.trans hzy.symm)
          simp [hxy, hzy]
        · simp [hxy]
      rw [Finset.sum_eq_zero fun y _ => hdisjoint y]
      simp [hxz]

theorem shiftedTranslationMatrix_partialIsometry (h : Fˣ) :
    shiftedTranslationMatrix h * (shiftedTranslationMatrix h)ᴴ *
      shiftedTranslationMatrix h = shiftedTranslationMatrix h := by
  rw [shiftedTranslationMatrix_mul_conjTranspose]
  ext x y
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single x]
  · by_cases hx : x = h
    · subst x
      simp [shiftedRangeWeight, shiftedTranslationMatrix_row_at_shift_zero]
    · simp [Matrix.diagonal_apply, shiftedRangeWeight, hx]
  · intro z _ hzx
    have hxz : x ≠ z := Ne.symm hzx
    simp [Matrix.diagonal_apply, hxz]
  · simp

theorem shiftedTranslationMatrix_rank (h : Fˣ) :
    (shiftedTranslationMatrix h).rank = Fintype.card F - 2 := by
  rw [← Matrix.rank_self_mul_conjTranspose,
    shiftedTranslationMatrix_mul_conjTranspose, Matrix.rank_diagonal]
  have hcard : Fintype.card {x : Fˣ // shiftedRangeWeight h x ≠ 0} =
      Fintype.card Fˣ - 1 := by
    have hequiv : {x : Fˣ // shiftedRangeWeight h x ≠ 0} ≃
        {x : Fˣ // x ≠ h} :=
      Equiv.subtypeEquiv (Equiv.refl Fˣ) (by
        intro x
        simp [shiftedRangeWeight])
    rw [Fintype.card_congr hequiv]
    exact Set.card_ne_eq h
  rw [hcard, Fintype.card_units]
  omega

theorem shiftedRangeWeight_norm (h : Fˣ) (hq : 3 ≤ Fintype.card F) :
    ‖shiftedRangeWeight h‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro x
    by_cases hx : x = h <;> simp [shiftedRangeWeight, hx]
  · have hunits : 1 < Fintype.card Fˣ := by
      rw [Fintype.card_units]
      omega
    have hnonempty : ∃ x : Fˣ, x ≠ h :=
      Fintype.exists_ne_of_one_lt_card hunits h
    obtain ⟨x, hx⟩ := hnonempty
    have hle : ‖shiftedRangeWeight h x‖₊ ≤
        Finset.univ.sup fun b => ‖shiftedRangeWeight h b‖₊ :=
      Finset.le_sup (f := fun b => ‖shiftedRangeWeight h b‖₊)
        (Finset.mem_univ x)
    calc
      (1 : ℝ) = ‖shiftedRangeWeight h x‖ := by
        simp [shiftedRangeWeight, hx]
      _ ≤ ‖shiftedRangeWeight h‖ := by
        rw [Pi.norm_def]
        exact_mod_cast hle

theorem shiftedTranslationMatrix_norm (h : Fˣ) (hq : 3 ≤ Fintype.card F) :
    ‖shiftedTranslationMatrix h‖ = 1 := by
  have hgramNorm :
      ‖shiftedTranslationMatrix h * (shiftedTranslationMatrix h)ᴴ‖ = 1 := by
    rw [shiftedTranslationMatrix_mul_conjTranspose,
      Matrix.l2_opNorm_diagonal, shiftedRangeWeight_norm h hq]
  have hcstar := Matrix.l2_opNorm_conjTranspose_mul_self
    ((shiftedTranslationMatrix h)ᴴ)
  simp only [Matrix.conjTranspose_conjTranspose,
    Matrix.l2_opNorm_conjTranspose] at hcstar
  rw [hgramNorm] at hcstar
  nlinarith [norm_nonneg (shiftedTranslationMatrix h)]

/-- Scaling of the additive field by a nonzero element. -/
def unitScaleEquiv (h : Fˣ) : F ≃ F where
  toFun x := (h : F) * x
  invFun x := ((h⁻¹ : Fˣ) : F) * x
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]

/-- Character coefficient after extending multiplicative characters by zero
to the whole field.  The inverse character is the algebraic conjugate on the
unit circle. -/
noncomputable def shiftedCharacterCoefficient
    (h : Fˣ) (χ ψ : MulChar F ℂ) : ℂ :=
  ((Fintype.card F - 1 : ℕ) : ℂ)⁻¹ *
    ∑ x : F, χ⁻¹ x * ψ (x - (h : F))

/-- Exact substitution `x=h t` converting the shifted coefficient into the
Jacobi sum displayed in the manuscript. -/
theorem shiftedCharacterCoefficient_eq_jacobiSum
    (h : Fˣ) (χ ψ : MulChar F ℂ) :
    shiftedCharacterCoefficient h χ ψ =
      ((Fintype.card F - 1 : ℕ) : ℂ)⁻¹ *
        (χ⁻¹ (h : F) * ψ (h : F) * ψ (-1) * jacobiSum χ⁻¹ ψ) := by
  unfold shiftedCharacterCoefficient jacobiSum
  congr 1
  rw [← (unitScaleEquiv h).sum_comp
    (fun x : F => χ⁻¹ x * ψ (x - (h : F)))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  change χ⁻¹ ((h : F) * t) * ψ ((h : F) * t - (h : F)) = _
  have hsub : (h : F) * t - (h : F) = (h : F) * (-1) * (1 - t) := by
    ring
  rw [hsub]
  simp only [map_mul]
  ring

private theorem sum_units_eq_sum_field_of_zero
    (f : F → ℂ) (hf : f 0 = 0) :
    (∑ u : Fˣ, f u) = ∑ x : F, f x := by
  calc
    (∑ u : Fˣ, f u) = ∑ z : {x : F // x ≠ 0}, f z := by
      exact Fintype.sum_equiv unitsEquivNeZero _ _ fun _ => rfl
    _ = ∑ x ∈ Finset.univ.filter (fun x : F => x ≠ 0), f x := by
      rw [Finset.sum_subtype
        (p := fun x : F => x ≠ 0)
        (Finset.univ.filter fun x : F => x ≠ 0) (by simp) f]
    _ = ∑ x : F, f x := by
      exact Finset.sum_subset (Finset.filter_subset _ _) (by
        intro x _ hx
        have hx0 : x = 0 := by simpa using hx
        simpa [hx0] using hf)

theorem shiftedTranslationMatrix_mulVec_character
    (h : Fˣ) (ψ : MulChar F ℂ) (x : Fˣ) :
    Matrix.mulVec (shiftedTranslationMatrix h)
        (fun y : Fˣ => ψ (y : F)) x = ψ ((x : F) - (h : F)) := by
  change (∑ y, shiftedTranslationMatrix h x y * ψ (y : F)) = _
  by_cases hx : x = h
  · subst x
    unfold shiftedTranslationMatrix
    have hy : ∀ y : Fˣ, ¬(0 : F) = (y : F) :=
      fun y he => Units.ne_zero y he.symm
    simp [hy]
    exact (MulChar.map_zero ψ).symm
  · have hxcoe : (x : F) ≠ (h : F) := fun he => hx (Units.ext he)
    let y0 : Fˣ := Units.mk0 ((x : F) - (h : F)) (sub_ne_zero.mpr hxcoe)
    rw [Finset.sum_eq_single y0]
    · simp [shiftedTranslationMatrix, y0]
    · intro y _ hy
      have hne : (x : F) - (h : F) ≠ (y : F) := by
        intro heq
        apply hy
        apply Units.ext
        exact heq.symm
      simp [shiftedTranslationMatrix, hne]
    · simp

/-- The algebraic normalized matrix coefficient in the multiplicative-
character basis equals the field-sum coefficient above. -/
theorem normalizedCharacterMatrixEntry_eq_shiftedCharacterCoefficient
    (h : Fˣ) (χ ψ : MulChar F ℂ) :
    ((Fintype.card F - 1 : ℕ) : ℂ)⁻¹ *
        ∑ x : Fˣ, χ⁻¹ (x : F) *
          Matrix.mulVec (shiftedTranslationMatrix h)
            (fun y : Fˣ => ψ (y : F)) x =
      shiftedCharacterCoefficient h χ ψ := by
  unfold shiftedCharacterCoefficient
  congr 1
  simp_rw [shiftedTranslationMatrix_mulVec_character]
  exact sum_units_eq_sum_field_of_zero
    (fun z : F => χ⁻¹ z * ψ (z - (h : F))) (by
      rw [MulChar.map_zero, zero_mul])

theorem star_jacobiSum (χ ψ : MulChar F ℂ) :
    star (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
  unfold jacobiSum
  change (starRingEnd ℂ) (∑ x : F, χ x * ψ (1 - x)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul]
  change star (χ x) * star (ψ (1 - x)) =
    χ⁻¹ x * ψ⁻¹ (1 - x)
  rw [MulChar.star_apply', MulChar.star_apply']

theorem jacobiSum_norm_eq_sqrt_card
    (χ ψ : MulChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ * ψ ≠ 1) :
    ‖jacobiSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  have hprod := jacobiSum_mul_jacobiSum_inv
    (F := F) (F' := ℂ)
      (by simpa only [ringChar.eq_zero] using
        (CharP.ringChar_ne_zero_of_finite F).symm)
      hχ hψ hχψ
  rw [← star_jacobiSum χ ψ] at hprod
  have hnorm := congrArg norm hprod
  rw [norm_mul, norm_star, norm_natCast] at hnorm
  have hsq : ‖jacobiSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    nlinarith
  have hsqrt : Real.sqrt (Fintype.card F) ^ 2 = (Fintype.card F : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith [norm_nonneg (jacobiSum χ ψ), Real.sqrt_nonneg (Fintype.card F)]

theorem mulChar_apply_unit_norm (χ : MulChar F ℂ) (u : Fˣ) :
    ‖χ (u : F)‖ = 1 := by
  simpa only [MulChar.coe_equivToUnitHom] using
    (Complex.norm_eq_one_of_mem_rootsOfUnity
      (χ.apply_mem_rootsOfUnity u))

theorem jacobiSum_norm_le_sqrt_card
    (χ ψ : MulChar F ℂ) (hq : 3 ≤ Fintype.card F)
    (hother : ¬(χ = 1 ∧ ψ = 1)) :
    ‖jacobiSum χ ψ‖ ≤ Real.sqrt (Fintype.card F) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
    have hcard : (3 : ℝ) ≤ Fintype.card F := by
      exact_mod_cast hq
    have hsq : Real.sqrt (Fintype.card F) ^ 2 =
        (Fintype.card F : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (Fintype.card F)]
  by_cases hχ : χ = 1
  · subst χ
    have hψ : ψ ≠ 1 := fun h => hother ⟨rfl, h⟩
    rw [jacobiSum_one_nontrivial hψ, norm_neg, norm_one]
    exact hsqrt
  · by_cases hψ : ψ = 1
    · subst ψ
      rw [jacobiSum_comm, jacobiSum_one_nontrivial hχ, norm_neg, norm_one]
      exact hsqrt
    · by_cases hχψ : χ * ψ = 1
      · have hψinv : ψ = χ⁻¹ := eq_inv_of_mul_eq_one_right hχψ
        rw [hψinv, jacobiSum_nontrivial_inv hχ, norm_neg]
        let minusOneUnit : Fˣ :=
          Units.mk0 (-1 : F) (neg_ne_zero.mpr one_ne_zero)
        have hphase := mulChar_apply_unit_norm χ minusOneUnit
        simpa [minusOneUnit] using hphase.trans_le hsqrt
      · rw [jacobiSum_norm_eq_sqrt_card χ ψ hχ hψ hχψ]

theorem shiftedCharacterCoefficient_principal
    (h : Fˣ) :
    shiftedCharacterCoefficient h 1 1 =
      ((Fintype.card F - 2 : ℕ) : ℂ) /
        ((Fintype.card F - 1 : ℕ) : ℂ) := by
  have htwo : 2 ≤ Fintype.card F :=
    Nat.add_one_le_of_lt Fintype.one_lt_card
  rw [shiftedCharacterCoefficient_eq_jacobiSum]
  simp only [inv_one]
  rw [jacobiSum_one_one]
  rw [Nat.cast_sub htwo]
  have hminusOne : (1 : MulChar F ℂ) (-1) = 1 := by
    exact MulChar.one_apply
      (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))
  have hshift : (1 : MulChar F ℂ) (h : F) = 1 :=
    MulChar.one_apply_coe h
  rw [hminusOne, hshift]
  simp only [mul_one, div_eq_mul_inv]
  ring

theorem shiftedCharacterCoefficient_norm_le
    (h : Fˣ) (χ ψ : MulChar F ℂ)
    (hq : 3 ≤ Fintype.card F)
    (hother : ¬(χ = 1 ∧ ψ = 1)) :
    ‖shiftedCharacterCoefficient h χ ψ‖ ≤
      Real.sqrt (Fintype.card F) /
        (Fintype.card F - 1 : ℕ) := by
  have hother' : ¬(χ⁻¹ = 1 ∧ ψ = 1) := by
    rintro ⟨hχ, hψ⟩
    exact hother ⟨inv_eq_one.mp hχ, hψ⟩
  have hJ := jacobiSum_norm_le_sqrt_card χ⁻¹ ψ hq hother'
  have hχphase : ‖χ⁻¹ (h : F)‖ = 1 :=
    mulChar_apply_unit_norm χ⁻¹ h
  have hψphase : ‖ψ (h : F)‖ = 1 :=
    mulChar_apply_unit_norm ψ h
  let minusOneUnit : Fˣ :=
    Units.mk0 (-1 : F) (neg_ne_zero.mpr one_ne_zero)
  have hminusOne : ‖ψ (-1 : F)‖ = 1 := by
    simpa [minusOneUnit] using
      (mulChar_apply_unit_norm ψ minusOneUnit)
  have hphase :
      ‖χ⁻¹ (h : F) * ψ (h : F) * ψ (-1)‖ = 1 := by
    rw [norm_mul, norm_mul, hχphase, hψphase, hminusOne]
    norm_num
  rw [shiftedCharacterCoefficient_eq_jacobiSum]
  rw [norm_mul, norm_inv, norm_natCast, norm_mul, hphase, one_mul]
  calc
    ((Fintype.card F - 1 : ℕ) : ℝ)⁻¹ *
          ‖jacobiSum χ⁻¹ ψ‖
        ≤ ((Fintype.card F - 1 : ℕ) : ℝ)⁻¹ *
            Real.sqrt (Fintype.card F) :=
      mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr (by positivity))
    _ = Real.sqrt (Fintype.card F) /
          (Fintype.card F - 1 : ℕ) := by
      rw [div_eq_mul_inv]
      ring

/-- Full form of the shifted Jacobi-edge theorem: the shifted translation is
a rank-q-minus-two norm-one partial isometry, and every normalized
multiplicative-character matrix entry has the stated Jacobi-sum formula and
sharp principal/non-principal estimates. -/
theorem shiftedJacobiPartialIsometry
    (h : Fˣ) (hq : 3 ≤ Fintype.card F) :
    shiftedTranslationMatrix h * (shiftedTranslationMatrix h)ᴴ *
        shiftedTranslationMatrix h = shiftedTranslationMatrix h
    ∧ (shiftedTranslationMatrix h).rank = Fintype.card F - 2
    ∧ ‖shiftedTranslationMatrix h‖ = 1
    ∧ (∀ χ ψ : MulChar F ℂ,
        ((Fintype.card F - 1 : ℕ) : ℂ)⁻¹ *
            ∑ x : Fˣ, χ⁻¹ (x : F) *
              Matrix.mulVec (shiftedTranslationMatrix h)
                (fun y : Fˣ => ψ (y : F)) x =
          ((Fintype.card F - 1 : ℕ) : ℂ)⁻¹ *
            (χ⁻¹ (h : F) * ψ (h : F) * ψ (-1) *
              jacobiSum χ⁻¹ ψ))
    ∧ shiftedCharacterCoefficient h 1 1 =
        ((Fintype.card F - 2 : ℕ) : ℂ) /
          ((Fintype.card F - 1 : ℕ) : ℂ)
    ∧ (∀ χ ψ : MulChar F ℂ, ¬(χ = 1 ∧ ψ = 1) →
        ‖shiftedCharacterCoefficient h χ ψ‖ ≤
          Real.sqrt (Fintype.card F) /
            (Fintype.card F - 1 : ℕ)) := by
  refine ⟨shiftedTranslationMatrix_partialIsometry h,
    shiftedTranslationMatrix_rank h,
    shiftedTranslationMatrix_norm h hq, ?_,
    shiftedCharacterCoefficient_principal h, ?_⟩
  · intro χ ψ
    exact (normalizedCharacterMatrixEntry_eq_shiftedCharacterCoefficient
      h χ ψ).trans (shiftedCharacterCoefficient_eq_jacobiSum h χ ψ)
  · intro χ ψ hother
    exact shiftedCharacterCoefficient_norm_le h χ ψ hq hother

end ShiftedJacobiPartialIsometry
end NCG
