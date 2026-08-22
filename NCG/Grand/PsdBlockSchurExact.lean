/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SourceCoercivityInfluenceExact

/-!
# Positive block matrices and the Moore–Penrose Schur criterion

Toolkit for the pseudo-inverse Schur complements used by
`thm:GT-localizer-extension-floor`, `thm:GT-target-short-influence` and
`thm:GT-sampled-versus-killed`.

For the Hermitian block matrix `M = [[A, B], [B^*, D]]` with `A ⪰ 0` and the
spectral pseudo-inverse `A^†` (`SourceCoercivityInfluence.pinv`):

* `block_form`: the quadratic form of `M` on a block vector;
* `completion_of_square`: under the range condition `A A^† B = B`,
  `⟪(x,y), M (x,y)⟫ = ⟪x + A^†By, A (x + A^†By)⟫ + ⟪y, S y⟫` with the Schur
  complement `S = D - B^* A^† B`;
* `range_obstruction_witness` / `range_condition_of_posSemidef`: `M ⪰ 0`
  forces `Ran B ⊆ Ran A` (`A A^† B = B`), with an explicit negative block
  direction otherwise;
* `schur_posSemidef`: `M ⪰ 0 ⇒ S ⪰ 0`, and `negative_witness`: a negative
  direction `y` of `S` gives the explicit block witness `(-A^†By, y)`;
* `posSemidef_of_schur` / `posSemidef_block_iff`: conversely `A ⪰ 0`,
  `A A^† B = B`, `S ⪰ 0` give `M ⪰ 0` — the Moore–Penrose Schur criterion.
-/

open Matrix Finset NCG.GeometricThresholdBank NCG.SourceCoercivityInfluence
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace PsdBlockSchur

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]

/-! ### Pseudo-inverse facts -/

theorem pinv_posSemidef {A : Matrix m m ℂ} (hA : A.IsHermitian) : (pinv hA).PosSemidef :=
  spectralFunction_posSemidef hA _ fun i => by
    split_ifs with h
    · exact (inv_pos.mpr h).le
    · exact le_rfl

theorem pinv_isHermitian {A : Matrix m m ℂ} (hA : A.IsHermitian) : (pinv hA).IsHermitian :=
  (pinv_posSemidef hA).1

theorem mul_pinv_eq_supportProj {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    A * pinv hA = supportProj hA := by
  have hid := spectralFunction_id hA
  calc A * pinv hA
      = spectralFunction hA id * spectralFunction hA (fun l => if 0 < l then l⁻¹ else 0) := by
        unfold pinv; rw [hid]
    _ = spectralFunction hA (fun l => id l * if 0 < l then l⁻¹ else 0) :=
        spectralFunction_mul hA _ _
    _ = supportProj hA := by
        unfold supportProj
        refine spectralFunction_congr hA fun i => ?_
        simp only [id]
        split_ifs with h
        · field_simp
        · ring

theorem pinv_mul_self_mul_pinv {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    pinv hA * A * pinv hA = pinv hA := by
  have hid := spectralFunction_id hA
  calc pinv hA * A * pinv hA
      = spectralFunction hA (fun l => if 0 < l then l⁻¹ else 0) * spectralFunction hA id
        * spectralFunction hA (fun l => if 0 < l then l⁻¹ else 0) := by unfold pinv; rw [hid]
    _ = spectralFunction hA (fun l => (if 0 < l then l⁻¹ else 0) * id l
          * (if 0 < l then l⁻¹ else 0)) := by
        rw [spectralFunction_mul, spectralFunction_mul]
    _ = pinv hA := by
        unfold pinv
        refine spectralFunction_congr hA fun i => ?_
        simp only [id]
        split_ifs with h
        · field_simp
        · ring

/-- `A (I - Q) = 0`. -/
theorem mul_one_sub_supportProj {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    A * (1 - supportProj hA.1) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, mul_supportProj hA, sub_self]

/-! ### Block quadratic forms -/

omit [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p] in
theorem star_sum_elim (u : m → ℂ) (x : p → ℂ) :
    star (Sum.elim u x) = Sum.elim (star u) (star x) := by
  funext i; cases i <;> rfl

omit [DecidableEq m] [DecidableEq p] in
theorem dotProduct_sum_elim (u v : m → ℂ) (x y : p → ℂ) :
    Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- `star v ⬝ᵥ M w = star (M^* v) ⬝ᵥ w`. -/
theorem adjoint_dot {k l : Type*} [Fintype k] [Fintype l] (M : Matrix k l ℂ) (v : k → ℂ)
    (w : l → ℂ) : star v ⬝ᵥ (M *ᵥ w) = star (Mᴴ *ᵥ v) ⬝ᵥ w := by
  rw [dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

omit [DecidableEq m] [DecidableEq p] in
/-- The quadratic form of the Hermitian block matrix on a block vector. -/
theorem block_form (A : Matrix m m ℂ) (B : Matrix m p ℂ) (D : Matrix p p ℂ) (x : m → ℂ)
    (y : p → ℂ) :
    star (Sum.elim x y) ⬝ᵥ (fromBlocks A B Bᴴ D *ᵥ Sum.elim x y)
      = star x ⬝ᵥ (A *ᵥ x) + star x ⬝ᵥ (B *ᵥ y) + star y ⬝ᵥ (Bᴴ *ᵥ x)
        + star y ⬝ᵥ (D *ᵥ y) := by
  rw [fromBlocks_mulVec, star_sum_elim, dotProduct_sum_elim, dotProduct_add, dotProduct_add]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  ring

omit [DecidableEq p] in
/-- **Completion of the square** under the range condition `A A^† B = B`. -/
theorem completion_of_square {A : Matrix m m ℂ} (hA : A.PosSemidef) (B : Matrix m p ℂ)
    (D : Matrix p p ℂ) (hrange : A * pinv hA.1 * B = B) (x : m → ℂ) (y : p → ℂ) :
    star (Sum.elim x y) ⬝ᵥ (fromBlocks A B Bᴴ D *ᵥ Sum.elim x y)
      = star (x + pinv hA.1 *ᵥ (B *ᵥ y)) ⬝ᵥ (A *ᵥ (x + pinv hA.1 *ᵥ (B *ᵥ y)))
        + star y ⬝ᵥ ((D - Bᴴ * pinv hA.1 * B) *ᵥ y) := by
  have hP := pinv_isHermitian hA.1
  have hrange' : Bᴴ * pinv hA.1 * A = Bᴴ := by
    have := congrArg conjTranspose hrange
    rwa [conjTranspose_mul, conjTranspose_mul, hP.eq, hA.1.eq, ← Matrix.mul_assoc] at this
  set w := pinv hA.1 *ᵥ (B *ᵥ y) with hw
  have t2 : star x ⬝ᵥ (A *ᵥ w) = star x ⬝ᵥ (B *ᵥ y) := by
    rw [hw, mulVec_mulVec, mulVec_mulVec, hrange]
  have t3 : star w ⬝ᵥ (A *ᵥ x) = star y ⬝ᵥ (Bᴴ *ᵥ x) := by
    calc star w ⬝ᵥ (A *ᵥ x) = star (B *ᵥ y) ⬝ᵥ (pinv hA.1 *ᵥ (A *ᵥ x)) := by
          rw [hw, adjoint_dot (pinv hA.1) (B *ᵥ y) (A *ᵥ x), hP.eq]
      _ = star y ⬝ᵥ (Bᴴ *ᵥ (pinv hA.1 *ᵥ (A *ᵥ x))) := by
          rw [adjoint_dot Bᴴ y, conjTranspose_conjTranspose]
      _ = star y ⬝ᵥ (Bᴴ *ᵥ x) := by
          rw [mulVec_mulVec, mulVec_mulVec, hrange']
  have t4 : star w ⬝ᵥ (A *ᵥ w) = star y ⬝ᵥ ((Bᴴ * pinv hA.1 * B) *ᵥ y) := by
    calc star w ⬝ᵥ (A *ᵥ w) = star w ⬝ᵥ (B *ᵥ y) := by
          have : A *ᵥ w = B *ᵥ y := by
            rw [hw, mulVec_mulVec, mulVec_mulVec, hrange]
          rw [this]
      _ = star (B *ᵥ y) ⬝ᵥ (pinv hA.1 *ᵥ (B *ᵥ y)) := by
          rw [hw, adjoint_dot (pinv hA.1) (B *ᵥ y) (B *ᵥ y), hP.eq]
      _ = star y ⬝ᵥ (Bᴴ *ᵥ (pinv hA.1 *ᵥ (B *ᵥ y))) := by
          rw [adjoint_dot Bᴴ y, conjTranspose_conjTranspose]
      _ = star y ⬝ᵥ ((Bᴴ * pinv hA.1 * B) *ᵥ y) := by
          rw [mulVec_mulVec, mulVec_mulVec]
  rw [block_form, mulVec_add, dotProduct_add, star_add, add_dotProduct, add_dotProduct, t2, t3,
    t4, sub_mulVec, dotProduct_sub]
  ring

omit [DecidableEq p] in
/-- **Obstruction witness**: if `Ran B ⊄ Ran A`, some block direction has
negative energy. -/
theorem range_obstruction_witness {A : Matrix m m ℂ} (hA : A.PosSemidef) (B : Matrix m p ℂ)
    (D : Matrix p p ℂ) (hfail : A * pinv hA.1 * B ≠ B) :
    ∃ z : m ⊕ p → ℂ, (star z ⬝ᵥ (fromBlocks A B Bᴴ D *ᵥ z)).re < 0 := by
  have hQ : supportProj hA.1 * B ≠ B := by rwa [← mul_pinv_eq_supportProj]
  obtain ⟨y, hy⟩ : ∃ y, (1 - supportProj hA.1) *ᵥ (B *ᵥ y) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hQ
    rw [ext_iff_mulVec]
    intro y
    have := hcon y
    rw [sub_mulVec, one_mulVec, sub_eq_zero, mulVec_mulVec] at this
    exact this.symm
  set u := (1 - supportProj hA.1) *ᵥ (B *ᵥ y) with hu
  have hAu : A *ᵥ u = 0 := by
    rw [hu, mulVec_mulVec, mul_one_sub_supportProj hA, zero_mulVec]
  have hQu : supportProj hA.1 *ᵥ u = 0 := by
    rw [hu, mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, supportProj_idem, sub_self,
      zero_mulVec]
  set nu := ∑ j, ‖u j‖ ^ 2 with hnu
  -- `star u ⬝ᵥ B y = ‖u‖²`
  have hnorm : star u ⬝ᵥ (B *ᵥ y) = (nu : ℂ) := by
    have hsplit : B *ᵥ y = supportProj hA.1 *ᵥ (B *ᵥ y) + u := by
      rw [hu, sub_mulVec, one_mulVec]; abel
    rw [hsplit, dotProduct_add, adjoint_dot, (supportProj_posSemidef hA.1).1.eq, hQu, star_zero,
      zero_dotProduct, zero_add, hnu, dotProduct, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  have hnorm' : star (B *ᵥ y) ⬝ᵥ u = (nu : ℂ) := by
    rw [← star_star (star (B *ᵥ y) ⬝ᵥ u), star_dotProduct, star_star, hnorm, Complex.star_def,
      Complex.conj_ofReal]
  have hupos : 0 < nu := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg fun j _ => sq_nonneg ‖u j‖) with h | h
    · exact h
    · exfalso
      apply hy
      funext j
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖u j‖).mp h.symm j
        (Finset.mem_univ j)
      rw [sq_eq_zero_iff, norm_eq_zero] at this
      simpa using this
  set d := (star y ⬝ᵥ (D *ᵥ y)).re with hd
  set t : ℝ := (|d| + 1) / nu with ht
  have htnu : t * nu = |d| + 1 := by rw [ht]; field_simp
  refine ⟨Sum.elim (((-t : ℝ) : ℂ) • u) y, ?_⟩
  rw [block_form]
  have e1 : star (((-t : ℝ) : ℂ) • u) ⬝ᵥ (A *ᵥ (((-t : ℝ) : ℂ) • u)) = 0 := by
    rw [mulVec_smul, hAu, smul_zero, dotProduct_zero]
  have e2 : star (((-t : ℝ) : ℂ) • u) ⬝ᵥ (B *ᵥ y) = ((-t * nu : ℝ) : ℂ) := by
    rw [star_smul, smul_dotProduct, hnorm, smul_eq_mul, Complex.star_def, Complex.conj_ofReal,
      Complex.ofReal_mul]
  have e3 : star y ⬝ᵥ (Bᴴ *ᵥ (((-t : ℝ) : ℂ) • u)) = ((-t * nu : ℝ) : ℂ) := by
    rw [mulVec_smul, dotProduct_smul, adjoint_dot Bᴴ y, conjTranspose_conjTranspose, hnorm',
      smul_eq_mul, Complex.ofReal_mul]
  rw [e1, e2, e3]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re]
  have : -t * nu = -(|d| + 1) := by rw [neg_mul, htnu]
  clear_value t nu d
  have hkey : (0 : ℝ) + -t * nu + -t * nu + (star y ⬝ᵥ (D *ᵥ y)).re = d - 2 * (|d| + 1) := by
    rw [this, hd]; ring
  rw [hkey]
  linarith [le_abs_self d, abs_nonneg d]

omit [DecidableEq p] in
/-- **Range condition**: a positive block matrix has `Ran B ⊆ Ran A`. -/
theorem range_condition_of_posSemidef {A : Matrix m m ℂ} (hA : A.PosSemidef) (B : Matrix m p ℂ)
    (D : Matrix p p ℂ) (hM : (fromBlocks A B Bᴴ D).PosSemidef) : A * pinv hA.1 * B = B := by
  by_contra h
  obtain ⟨z, hz⟩ := range_obstruction_witness hA B D h
  have h0 := (Complex.le_def.mp (hM.dotProduct_mulVec_nonneg z)).1
  rw [Complex.zero_re] at h0
  linarith

omit [DecidableEq p] in
/-- **Schur complement positivity**: `M ⪰ 0 ⇒ S = D - B^* A^† B ⪰ 0`. -/
theorem schur_posSemidef {A : Matrix m m ℂ} (hA : A.PosSemidef) (B : Matrix m p ℂ)
    (D : Matrix p p ℂ) (hM : (fromBlocks A B Bᴴ D).PosSemidef) :
    (D - Bᴴ * pinv hA.1 * B).PosSemidef := by
  have hrange := range_condition_of_posSemidef hA B D hM
  have hD : D.IsHermitian := (isHermitian_fromBlocks_iff.mp hM.1).2.2.2
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun y => ?_⟩
  · change (D - Bᴴ * pinv hA.1 * B)ᴴ = D - Bᴴ * pinv hA.1 * B
    rw [conjTranspose_sub, hD.eq, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, (pinv_isHermitian hA.1).eq, Matrix.mul_assoc]
  · have := hM.dotProduct_mulVec_nonneg (Sum.elim (-(pinv hA.1 *ᵥ (B *ᵥ y))) y)
    rw [completion_of_square hA B D hrange, neg_add_cancel, mulVec_zero, dotProduct_zero,
      zero_add] at this
    exact this

omit [DecidableEq p] in
/-- **Explicit soft witness**: a negative direction of the Schur complement
lifts to the negative block direction `(-A^†By, y)`. -/
theorem negative_witness {A : Matrix m m ℂ} (hA : A.PosSemidef) (B : Matrix m p ℂ)
    (D : Matrix p p ℂ) (hrange : A * pinv hA.1 * B = B) (y : p → ℂ)
    (hneg : (star y ⬝ᵥ ((D - Bᴴ * pinv hA.1 * B) *ᵥ y)).re < 0) :
    (star (Sum.elim (-(pinv hA.1 *ᵥ (B *ᵥ y))) y)
      ⬝ᵥ (fromBlocks A B Bᴴ D *ᵥ Sum.elim (-(pinv hA.1 *ᵥ (B *ᵥ y))) y)).re < 0 := by
  rw [completion_of_square hA B D hrange, neg_add_cancel, mulVec_zero, dotProduct_zero, zero_add]
  exact hneg

omit [DecidableEq p] in
/-- **Converse**: `A ⪰ 0`, the range condition and `S ⪰ 0` give `M ⪰ 0`. -/
theorem posSemidef_of_schur {A : Matrix m m ℂ} (hA : A.PosSemidef) (B : Matrix m p ℂ)
    (D : Matrix p p ℂ) (hD : D.IsHermitian) (hrange : A * pinv hA.1 * B = B)
    (hS : (D - Bᴴ * pinv hA.1 * B).PosSemidef) : (fromBlocks A B Bᴴ D).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨IsHermitian.fromBlocks hA.1 rfl hD, fun z => ?_⟩
  rw [← Sum.elim_comp_inl_inr z, completion_of_square hA B D hrange]
  exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hS.dotProduct_mulVec_nonneg _)

omit [DecidableEq p] in
/-- **Moore–Penrose Schur criterion** for a Hermitian block matrix with
positive source block: `M ⪰ 0 ⇔ Ran B ⊆ Ran A ∧ S ⪰ 0`. -/
theorem posSemidef_block_iff {A : Matrix m m ℂ} (hA : A.PosSemidef) (B : Matrix m p ℂ)
    (D : Matrix p p ℂ) (hD : D.IsHermitian) :
    (fromBlocks A B Bᴴ D).PosSemidef ↔
      A * pinv hA.1 * B = B ∧ (D - Bᴴ * pinv hA.1 * B).PosSemidef :=
  ⟨fun hM => ⟨range_condition_of_posSemidef hA B D hM, schur_posSemidef hA B D hM⟩,
    fun ⟨hrange, hS⟩ => posSemidef_of_schur hA B D hD hrange hS⟩

end PsdBlockSchur
end NCG
