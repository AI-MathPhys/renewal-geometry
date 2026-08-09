/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ArAddMult

/-!
# Exact EASY 45: the boxed additive--multiplicative transform

`ArAddMult` proves the scalar orthogonality, coordinate factorization,
character-transform, and Gauss-sum engines.  Here they are assembled into the
boxed constrained finite-field Fourier identity from the manuscript.
-/

open AddChar

namespace NCG

variable {F r t : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

/-- Finite dot product over the row carrier. -/
def arDot (u v : r -> F) : F := ∑ i, u i * v i

/-- The matrix-vector constraint map. -/
def arMatVec (A : r -> t -> F) (x : t -> F) : r -> F :=
  fun i => ∑ j, A i j * x j

/-- Pairing of a Fourier row with a column of `A`. -/
def arColDot (A : r -> t -> F) (xi : r -> F) (j : t) : F :=
  ∑ i, xi i * A i j

/-- The unnormalized additive Fourier transform used in the manuscript. -/
def arFourier (psi : AddChar F Complex) (f : F -> Complex) (y : F) :
    Complex := ∑ x, f x * psi (y * x)

lemma addChar_finset_sum_eq_prod (psi : AddChar F Complex)
    {s : Finset t} (g : t -> F) :
    psi (∑ i ∈ s, g i) = ∏ i ∈ s, psi (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [map_zero_eq_one]
  | @insert a s ha ih =>
      simp [ha, ih, AddChar.map_add_eq_mul]

lemma ar_vector_orthogonality
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (chi : MulChar F Complex) (hchi : chi ≠ 1) (v : r -> F) :
    ∑ xi : r -> F, psi (arDot xi v)
      = if v = 0 then
          (Fintype.card F : Complex) ^ Fintype.card r else 0 := by
  have hscalar := (ar_add_mult (F := F) psi hpsi chi hchi).1
  have hfactor := (ar_add_mult (F := F) psi hpsi chi hchi).2.1
  calc
    ∑ xi : r -> F, psi (arDot xi v)
        = ∑ xi : r -> F, ∏ i, psi (xi i * v i) := by
            apply Finset.sum_congr rfl
            intro xi _
            exact addChar_finset_sum_eq_prod psi
              (s := Finset.univ) (fun i => xi i * v i)
    _ = ∏ i : r, ∑ x : F, psi (x * v i) :=
          hfactor r (fun i x => psi (x * v i))
    _ = ∏ i : r,
          if v i = 0 then (Fintype.card F : Complex) else 0 := by
            apply Finset.prod_congr rfl
            intro i _
            exact hscalar (v i)
    _ = if v = 0 then
          (Fintype.card F : Complex) ^ Fintype.card r else 0 := by
            classical
            by_cases hv : v = 0
            · subst v
              simp
            · rw [if_neg hv]
              obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
                by_contra h
                push_neg at h
                apply hv
                funext j
                exact h j
              exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma ar_phase_bilinear (A : r -> t -> F) (b : r -> F)
    (x : t -> F) (xi : r -> F) :
    arDot xi (arMatVec A x - b)
      = -arDot xi b + ∑ j, arColDot A xi j * x j := by
  classical
  simp only [arDot, arMatVec, arColDot, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  ring_nf

lemma ar_phase_factorization (psi : AddChar F Complex)
    (A : r -> t -> F) (b : r -> F) (x : t -> F) (xi : r -> F) :
    psi (arDot xi (arMatVec A x - b))
      = psi (-arDot xi b) * ∏ j, psi (arColDot A xi j * x j) := by
  rw [ar_phase_bilinear A b x xi, AddChar.map_add_eq_mul]
  congr 1
  exact addChar_finset_sum_eq_prod psi
    (s := Finset.univ) (fun j => arColDot A xi j * x j)

/-- Unnormalized form of the manuscript's boxed transform. -/
theorem ar_add_mult_boxed_unnormalized
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (chi : MulChar F Complex) (hchi : chi ≠ 1)
    (A : r -> t -> F) (b : r -> F) (f : t -> F -> Complex) :
    (∑ xi : r -> F, psi (-arDot xi b) *
        ∏ j, arFourier psi (f j) (arColDot A xi j))
      = (Fintype.card F : Complex) ^ Fintype.card r *
        ∑ x : t -> F,
          if arMatVec A x = b then ∏ j, f j (x j) else 0 := by
  have hfactor := (ar_add_mult (F := F) psi hpsi chi hchi).2.1
  calc
    (∑ xi : r -> F, psi (-arDot xi b) *
        ∏ j, arFourier psi (f j) (arColDot A xi j))
        = ∑ xi : r -> F, psi (-arDot xi b) *
            ∑ x : t -> F,
              ∏ j, (f j (x j) *
                psi (arColDot A xi j * x j)) := by
                  apply Finset.sum_congr rfl
                  intro xi _
                  simp only [arFourier]
                  rw [← hfactor t (fun j x =>
                    f j x * psi (arColDot A xi j * x))]
    _ = ∑ xi : r -> F, ∑ x : t -> F,
          psi (-arDot xi b) *
            ∏ j, (f j (x j) *
              psi (arColDot A xi j * x j)) := by
                apply Finset.sum_congr rfl
                intro xi _
                rw [Finset.mul_sum]
    _ = ∑ x : t -> F, ∑ xi : r -> F,
          psi (-arDot xi b) *
            ∏ j, (f j (x j) *
              psi (arColDot A xi j * x j)) := by
                rw [Finset.sum_comm]
    _ = ∑ x : t -> F,
          (∑ xi : r -> F,
            psi (arDot xi (arMatVec A x - b))) *
            ∏ j, f j (x j) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro xi _
              rw [ar_phase_factorization psi A b x xi]
              rw [Finset.prod_mul_distrib]
              ring
    _ = ∑ x : t -> F,
          (if arMatVec A x - b = 0 then
              (Fintype.card F : Complex) ^ Fintype.card r else 0) *
            ∏ j, f j (x j) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [ar_vector_orthogonality psi hpsi chi hchi]
    _ = (Fintype.card F : Complex) ^ Fintype.card r *
        ∑ x : t -> F,
          if arMatVec A x = b then ∏ j, f j (x j) else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : arMatVec A x = b
            · rw [if_pos hx]
              have hz : arMatVec A x - b = 0 := sub_eq_zero.mpr hx
              rw [if_pos hz]
            · rw [if_neg hx]
              have hz : arMatVec A x - b ≠ 0 := by
                exact fun h => hx (sub_eq_zero.mp h)
              rw [if_neg hz]
              ring

/-- The exact normalized boxed transform, with `q^{-r}` represented by the
inverse of the finite-field cardinality power. -/
theorem ar_add_mult_boxed
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (chi : MulChar F Complex) (hchi : chi ≠ 1)
    (A : r -> t -> F) (b : r -> F) (f : t -> F -> Complex) :
    (∑ x : t -> F,
        if arMatVec A x = b then ∏ j, f j (x j) else 0)
      = ((Fintype.card F : Complex) ^ Fintype.card r)⁻¹ *
        ∑ xi : r -> F, psi (-arDot xi b) *
          ∏ j, arFourier psi (f j) (arColDot A xi j) := by
  rw [ar_add_mult_boxed_unnormalized psi hpsi chi hchi A b f]
  have hcard : (Fintype.card F : Complex) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hcard]

/-- The Gauss sum has squared complex modulus equal to the field cardinality. -/
theorem gaussSum_norm_sq_eq_card
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (chi : MulChar F Complex) (hchi : chi ≠ 1) :
    ‖gaussSum chi psi‖ ^ 2 = (Fintype.card F : Real) := by
  have hprod := gaussSum_mul_gaussSum_eq_card hchi hpsi
  have hz : (Complex.normSq (gaussSum chi psi) : Complex)
      = (Fintype.card F : Complex) := by
    rw [Complex.normSq_eq_conj_mul_self]
    change star (gaussSum chi psi) * gaussSum chi psi
      = (Fintype.card F : Complex)
    rw [mul_comm, star_gaussSum_eq]
    exact hprod
  rw [Complex.sq_norm]
  exact_mod_cast hz

/-- The manuscript's `|tau| = sqrt q` normalization. -/
theorem gaussSum_norm_eq_sqrt_card
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (chi : MulChar F Complex) (hchi : chi ≠ 1) :
    ‖gaussSum chi psi‖ = Real.sqrt (Fintype.card F : Real) := by
  rw [← Real.sqrt_sq (norm_nonneg (gaussSum chi psi)),
    gaussSum_norm_sq_eq_card psi hpsi chi hchi]

/-- The character transform and Gauss-modulus clauses, exported beside the
boxed constrained transform in one exact packet. -/
theorem ar_add_mult_exact_packet
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (chi : MulChar F Complex) (hchi : chi ≠ 1)
    (A : r -> t -> F) (b : r -> F) (f : t -> F -> Complex) :
    ((∑ x : t -> F,
        if arMatVec A x = b then ∏ j, f j (x j) else 0)
      = ((Fintype.card F : Complex) ^ Fintype.card r)⁻¹ *
        ∑ xi : r -> F, psi (-arDot xi b) *
          ∏ j, arFourier psi (f j) (arColDot A xi j))
    ∧ (∀ a : Fˣ, gaussSum chi (psi.mulShift a)
        = chi⁻¹ a * gaussSum chi psi)
    ∧ (∑ x : F, chi x * psi (0 * x) = 0)
    ∧ (gaussSum chi psi * gaussSum chi⁻¹ psi⁻¹
        = (Fintype.card F : Complex))
    ∧ (‖gaussSum chi psi‖ =
        Real.sqrt (Fintype.card F : Real)) := by
  exact ⟨ar_add_mult_boxed psi hpsi chi hchi A b f,
    (ar_add_mult (F := F) psi hpsi chi hchi).2.2.1,
    (ar_add_mult (F := F) psi hpsi chi hchi).2.2.2.1,
    (ar_add_mult (F := F) psi hpsi chi hchi).2.2.2.2,
    gaussSum_norm_eq_sqrt_card psi hpsi chi hchi⟩

end NCG
