/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.IncidenceDeterminantCoefficients

/-!
# Rectangular Cauchy–Binet for Gram determinants

Infrastructure for `thm:howe-discriminant` (`eq:howe-minor-sos`) of the spacetime–gauge duality
paper: for a rectangular complex matrix `A` with `r` columns,

`det (Aᴴ A) = ∑_{|I| = r} |det A_I|²`,

the sum running over the `r`-element sets `I` of rows and `A_I` denoting the `r × r` submatrix
on those rows (any enumeration of `I`; the squared modulus does not depend on it).

* `factorial_mul_det_conjTranspose_mul`: the symmetrised form
  `r! · det (Aᴴ A) = ∑_{p : Fin r → rows} |det A_p|²` over *all* row choices, specialised from
  `IncidencePolymatroid.factorial_mul_det_eq_sum`;
* `det_submatrix_eq_zero_of_not_injective`: non-injective row choices contribute nothing;
* `sum_fiber_eq_factorial_mul`: the `r!` injective row choices with a given image `I` all
  contribute `|det A_I|²`;
* `det_conjTranspose_mul_eq_sum_minors`: **rectangular Cauchy–Binet**, with the squared moduli
  written as `star (det) * det`;
* `det_conjTranspose_mul_eq_sum_normSq_minors`: the same with `‖det A_I‖²`.
-/

open Matrix Finset

namespace RenewalGeometry
namespace CauchyBinet

variable {m : Type*} [Fintype m] [DecidableEq m] {r : ℕ}

/-- The symmetrised Cauchy–Binet identity for the Gram determinant:
`r! · det (Aᴴ A) = ∑_{p : Fin r → m} |det A_p|²` over all row choices `p`. -/
theorem factorial_mul_det_conjTranspose_mul (A : Matrix m (Fin r) ℂ) :
    (r.factorial : ℂ) * (Aᴴ * A).det =
      ∑ p : Fin r → m, star (A.submatrix p id).det * (A.submatrix p id).det := by
  have h := IncidencePolymatroid.factorial_mul_det_eq_sum A (fun _ => (1 : ℂ)) (RingHom.id ℂ)
  simp only [one_mul, Finset.prod_const_one, RingHom.id_apply, Fintype.card_fin] at h
  have hG : (Matrix.of fun i j => ∑ x, star (A x i) * A x j) = Aᴴ * A := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hG] at h
  exact h

/-- Non-injective row choices have vanishing minors. -/
theorem det_submatrix_eq_zero_of_not_injective (A : Matrix m (Fin r) ℂ) {p : Fin r → m}
    (hp : ¬ Function.Injective p) : (A.submatrix p id).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
    by_contra h
    push_neg at h
    exact hp fun i j hij => h i j hij
  exact Matrix.det_zero_of_row_eq hne (by ext k; simp [Matrix.submatrix_apply, hij])

/-- Permuting the rows does not change the squared modulus of the minor. -/
theorem star_det_mul_det_submatrix_comp (A : Matrix m (Fin r) ℂ) (p : Fin r → m)
    (σ : Equiv.Perm (Fin r)) :
    star (A.submatrix (p ∘ σ) id).det * (A.submatrix (p ∘ σ) id).det =
      star (A.submatrix p id).det * (A.submatrix p id).det := by
  have h : A.submatrix (p ∘ σ) id = (A.submatrix p id).submatrix σ id := by
    ext i j
    rfl
  rw [h, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

/-- **The fiber over an `r`-set.**  If `enum : Fin r → m` is an injective enumeration of the
`r`-element set `I`, the row choices with image `I` are exactly the `r!` reorderings
`enum ∘ σ`, and they all contribute `|det A_enum|²`. -/
theorem sum_fiber_eq_factorial_mul (A : Matrix m (Fin r) ℂ) (I : Finset m) (hI : I.card = r)
    (enum : Fin r → m) (hinj : Function.Injective enum) (hmem : ∀ j, enum j ∈ I) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin r → m => Finset.image p Finset.univ = I),
        star (A.submatrix p id).det * (A.submatrix p id).det =
      (r.factorial : ℂ) * (star (A.submatrix enum id).det * (A.submatrix enum id).det) := by
  -- the image of the enumeration is `I`
  have himage : Finset.image enum Finset.univ = I := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact hmem j
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hI]
  have hconst : (r.factorial : ℂ) * (star (A.submatrix enum id).det * (A.submatrix enum id).det) =
      ∑ _σ : Equiv.Perm (Fin r), star (A.submatrix enum id).det * (A.submatrix enum id).det := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst]
  symm
  refine Finset.sum_bij (fun σ _ => enum ∘ σ) ?_ ?_ ?_ ?_
  · intro σ _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← Finset.image_image, Finset.image_univ_of_surjective σ.surjective, himage]
  · intro σ _ τ _ h
    exact Equiv.ext fun j => hinj (congrFun h j)
  · intro p hp
    rw [Finset.mem_filter] at hp
    have hpinj : Function.Injective p := by
      have hcard : (Finset.image p Finset.univ).card = (Finset.univ : Finset (Fin r)).card := by
        rw [hp.2, hI, Finset.card_univ, Fintype.card_fin]
      have := Finset.injOn_of_card_image_eq hcard
      exact fun a b hab => this (Finset.mem_univ a) (Finset.mem_univ b) hab
    have hchoice : ∀ j, ∃ k, enum k = p j := by
      intro j
      have hj : p j ∈ Finset.image p Finset.univ := Finset.mem_image_of_mem p (Finset.mem_univ j)
      rw [hp.2, ← himage] at hj
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hj
      exact ⟨k, hk⟩
    choose σ hσ using hchoice
    have hσinj : Function.Injective σ := by
      intro a b hab
      apply hpinj
      rw [← hσ a, ← hσ b, hab]
    refine ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσinj), Finset.mem_univ _, ?_⟩
    funext j
    exact hσ j
  · intro σ _
    exact (star_det_mul_det_submatrix_comp A enum σ).symm

/-- **Rectangular Cauchy–Binet for Gram determinants** (`eq:howe-minor-sos`).  For a complex
matrix `A` with `r` columns and any enumeration `enum I : Fin r → m` of each `r`-element row set
`I` (injective, with values in `I`),
`det (Aᴴ A) = ∑_{|I| = r} |det A_I|²`, the squared modulus written as `star (det A_I) * det A_I`. -/
theorem det_conjTranspose_mul_eq_sum_minors (A : Matrix m (Fin r) ℂ)
    (enum : Finset m → Fin r → m)
    (henum : ∀ I : Finset m, I.card = r → Function.Injective (enum I) ∧ ∀ j, enum I j ∈ I) :
    (Aᴴ * A).det = ∑ I ∈ Finset.univ.powersetCard r,
      star (A.submatrix (enum I) id).det * (A.submatrix (enum I) id).det := by
  have hfac : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  apply mul_left_cancel₀ hfac
  rw [factorial_mul_det_conjTranspose_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := (Finset.univ : Finset (Finset m)))
    (g := fun p : Fin r → m => Finset.image p Finset.univ) (fun _ _ => Finset.mem_univ _)
    (fun p : Fin r → m => star (A.submatrix p id).det * (A.submatrix p id).det)]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun I : Finset m => I.card = r)]
  have hzero : ∑ I ∈ Finset.univ.filter (fun I : Finset m => ¬ I.card = r),
      ∑ p ∈ Finset.univ.filter (fun p : Fin r → m => Finset.image p Finset.univ = I),
        star (A.submatrix p id).det * (A.submatrix p id).det = 0 := by
    apply Finset.sum_eq_zero
    intro I hI
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hI hp
    have hpn : ¬ Function.Injective p := by
      intro hinj
      apply hI.2
      rw [← hp.2, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    rw [det_submatrix_eq_zero_of_not_injective A hpn, mul_zero]
  rw [hzero, add_zero, Finset.mul_sum, Finset.powersetCard_eq_filter, Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mem_filter] at hI
  exact sum_fiber_eq_factorial_mul A I hI.2 (enum I) (henum I hI.2).1 (henum I hI.2).2

/-- Rectangular Cauchy–Binet with the squared moduli written as `‖det A_I‖²`. -/
theorem det_conjTranspose_mul_eq_sum_normSq_minors (A : Matrix m (Fin r) ℂ)
    (enum : Finset m → Fin r → m)
    (henum : ∀ I : Finset m, I.card = r → Function.Injective (enum I) ∧ ∀ j, enum I j ∈ I) :
    (Aᴴ * A).det = ∑ I ∈ Finset.univ.powersetCard r,
      ((‖(A.submatrix (enum I) id).det‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_conjTranspose_mul_eq_sum_minors A enum henum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

end CauchyBinet
end RenewalGeometry
