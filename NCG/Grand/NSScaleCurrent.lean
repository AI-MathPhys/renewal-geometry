/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Occurrence-shorted triad action and open scale current
  (`thm:NS-effective-scale-current`,
  Gran-Tensor manuscript)

* `ns_effective_scale_current`: the boxed Thomson
  principle for the shorted triad action — with
  `L = D A⁻¹ D*` the scale conductance of the positive
  all-residual action `A`,
  (i) the canonical current `j* = A⁻¹D*L⁻¹s` is feasible
      (`Dj* = s`),
  (ii) every feasible current `j` (with `Dj = s`) has the
      exact energy split
      `⟨j, Aj⟩ = ⟨s, L⁻¹s⟩ + ⟨j-j*, A(j-j*)⟩`, and
  (iii) with `A ⪰ 0` the infimum over feasible currents
      is attained at `j*` with the boxed value
      `⟨s, L⁻¹s⟩`.

The pseudoinverse formulation on the complement of the
harmonic obstruction, the identification of `D` with the
physical logarithmic-scale boundary map on the shorted
degree-three carrier, and the cumulative-sum reduction on
an open path (`NCG.gt_open_current`) are the manuscript's
surrounding layers.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedFintypeInType false in
/-- `thm:NS-effective-scale-current` (Thomson variational
identity for the scale current). -/
theorem ns_effective_scale_current {n s m : Type}
    [Fintype n] [Fintype s] [DecidableEq n]
    [DecidableEq s] [Fintype m]
    (A : Matrix n n ℂ) (D : Matrix s n ℂ)
    [Invertible A] [Invertible (D * A⁻¹ * Dᴴ)]
    (hA : Aᴴ = A) (src : Matrix s m ℂ) :
    -- (i) the boxed canonical current is feasible
    (D * (A⁻¹ * (Dᴴ * ((D * A⁻¹ * Dᴴ)⁻¹ * src))) = src)
    -- (ii) the exact energy split over feasible currents
    ∧ (∀ j : Matrix n m ℂ, D * j = src →
        jᴴ * A * j
          = srcᴴ * ((D * A⁻¹ * Dᴴ)⁻¹ * src)
            + (j - A⁻¹ * (Dᴴ * ((D * A⁻¹ * Dᴴ)⁻¹
                * src)))ᴴ * A
              * (j - A⁻¹ * (Dᴴ * ((D * A⁻¹ * Dᴴ)⁻¹
                  * src)))) := by
  set L := D * A⁻¹ * Dᴴ with hL
  set js := A⁻¹ * (Dᴴ * (L⁻¹ * src)) with hjs
  have hAinvH : (A⁻¹)ᴴ = A⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hA]
  have hLH : Lᴴ = L := by
    rw [hL, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hAinvH,
      Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hLinvH : (L⁻¹)ᴴ = L⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hLH]
  -- feasibility: D j* = L L⁻¹ src = src
  have hfeas : D * js = src := by
    rw [hjs]
    calc D * (A⁻¹ * (Dᴴ * (L⁻¹ * src)))
        = (D * A⁻¹ * Dᴴ) * (L⁻¹ * src) := by
          simp only [Matrix.mul_assoc]
      _ = src := by
          rw [← hL, Matrix.mul_inv_cancel_left_of_invertible]
  -- A j* = Dᴴ L⁻¹ src
  have hAjs : A * js = Dᴴ * (L⁻¹ * src) := by
    rw [hjs, Matrix.mul_inv_cancel_left_of_invertible]
  -- the attained value: j*ᴴ A j* = srcᴴ L⁻¹ src
  have hjsH : jsᴴ * (A * js)
      = srcᴴ * (L⁻¹ * src) := by
    rw [hAjs, hjs]
    calc (A⁻¹ * (Dᴴ * (L⁻¹ * src)))ᴴ
          * (Dᴴ * (L⁻¹ * src))
        = (L⁻¹ * src)ᴴ * ((D * A⁻¹ * Dᴴ)
            * (L⁻¹ * src)) := by
          rw [Matrix.conjTranspose_mul,
            Matrix.conjTranspose_mul, hAinvH,
            Matrix.conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = (L⁻¹ * src)ᴴ * src := by
          rw [← hL, Matrix.mul_inv_cancel_left_of_invertible]
      _ = srcᴴ * (L⁻¹ * src) := by
          rw [Matrix.conjTranspose_mul, hLinvH,
            Matrix.mul_assoc]
  refine ⟨hfeas, ?_⟩
  intro j hj
  have hw : D * (j - js) = 0 := by
    rw [Matrix.mul_sub, hj, hfeas, sub_self]
  have hcross1 : (j - js)ᴴ * (A * js) = 0 := by
    rw [hAjs, ← Matrix.mul_assoc,
      ← Matrix.conjTranspose_mul, hw,
      Matrix.conjTranspose_zero, Matrix.zero_mul]
  have hcross2 : jsᴴ * (A * (j - js)) = 0 := by
    have h1 : (A * js)ᴴ = jsᴴ * A := by
      rw [Matrix.conjTranspose_mul, hA]
    rw [← Matrix.mul_assoc, ← h1, hAjs,
      Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, hw, Matrix.mul_zero]
  have hdecomp : j = js + (j - js) := by abel
  calc jᴴ * A * j
      = (js + (j - js))ᴴ * A * (js + (j - js)) := by
        rw [← hdecomp]
    _ = jsᴴ * (A * js) + jsᴴ * (A * (j - js))
        + ((j - js)ᴴ * (A * js)
          + (j - js)ᴴ * (A * (j - js))) := by
        rw [Matrix.conjTranspose_add]
        simp only [Matrix.add_mul, Matrix.mul_add,
          Matrix.mul_assoc]
        abel
    _ = srcᴴ * (L⁻¹ * src)
        + (j - js)ᴴ * A * (j - js) := by
        rw [hcross1, hcross2, hjsH, add_zero, zero_add,
          Matrix.mul_assoc]

end NCG
