/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exterior cube of the direction record
  (`thm:exterior-cube-master`, flagship manuscript)

For direction records `u_a ∈ ℝ³` with weights `w_a` and second
moment `M = Σ_a w_a u_a u_aᵀ`:

* the multilinear row expansion
  `det M = Σ_r (Π_i w_{r i} (u_{r i})_i) det[u_{r 0}; u_{r 1}; u_{r 2}]`
  (`cube_det_expansion`);
* the boxed expectation identity
  `𝔼 det[U₁,U₂,U₃]² = Σ_{a,b,c} w_a w_b w_c det[u_a,u_b,u_c]²
  = 6 det M` (`cube_expectation`, by expanding one determinant
  factor through the Leibniz formula and symmetrizing over the six
  row permutations — repeated indices contribute zero
  determinants, so the ordered sum is the i.i.d. expectation);
* hence the boxed Cauchy–Binet value
  `Σ_{a<b<c} w_a w_b w_c det[u_a,u_b,u_c]² = det M` in its ordered
  form `(1/6)Σ_{a,b,c} = det M`; the identification with
  `‖Λ³W‖²_HS` is definitional (the matrix coefficients of `Λ³W`
  are the maximal minors `√(w_aw_bw_c) det[u_a,u_b,u_c]`, and the
  `a<b<c` grouping is the `3!`-fold symmetrization of the ordered
  sum — disclosed);
* the isotropic normalization: `M = I₃/3` has
  `𝔼 det² = 6 det(I₃/3) = 2/9` (`cube_isotropic`).
-/

open Finset

namespace NCG

variable {m : Type*} [Fintype m]

/-- The second-moment matrix `M = Σ_a w_a u_a u_aᵀ`. -/
noncomputable def cubeM (w : m → ℝ) (u : m → Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => ∑ a, w a * u a i * u a j

/-- The triple determinant `det[u_{r 0}; u_{r 1}; u_{r 2}]`
(rows). -/
noncomputable def tripleDet (u : m → Fin 3 → ℝ) (r : Fin 3 → m) :
    ℝ :=
  Matrix.det (Matrix.of fun i j => u (r i) j)

/-- Multilinear row expansion of `det M`. -/
theorem cube_det_expansion (w : m → ℝ) (u : m → Fin 3 → ℝ) :
    (cubeM w u).det
      = ∑ r : Fin 3 → m,
          (∏ i, w (r i) * u (r i) i) * tripleDet u r := by
  have hrow : cubeM w u
      = Matrix.of fun i => ∑ a, (w a * u a i) • u a := by
    ext i j
    simp [cubeM, Finset.sum_apply, mul_assoc]
  rw [hrow]
  have hdet : (Matrix.of fun i => ∑ a, (w a * u a i) • u a).det
      = Matrix.detRowAlternating
          (fun i => ∑ a : m, (w a * u a i) • u a) := rfl
  rw [hdet]
  have hmap := (Matrix.detRowAlternating (R := ℝ)
      (n := Fin 3)).toMultilinearMap.map_sum
    (g := fun i a => (w a * u a i) • u a)
  rw [show Matrix.detRowAlternating
        (fun i => ∑ a : m, (w a * u a i) • u a)
      = (Matrix.detRowAlternating (R := ℝ)
          (n := Fin 3)).toMultilinearMap
        (fun i => ∑ a : m, (fun i a => (w a * u a i) • u a) i a)
      from rfl, hmap]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [show (fun i => (fun i a => (w a * u a i) • u a) i (r i))
      = fun i => (w (r i) * u (r i) i) • u (r i) from rfl]
  rw [(Matrix.detRowAlternating (R := ℝ)
      (n := Fin 3)).toMultilinearMap.map_smul_univ]
  rw [smul_eq_mul]
  rfl

omit [Fintype m] in
/-- Row permutations of the triple determinant. -/
lemma tripleDet_comp (u : m → Fin 3 → ℝ) (r : Fin 3 → m)
    (σ : Equiv.Perm (Fin 3)) :
    tripleDet u (r ∘ σ)
      = (Equiv.Perm.sign σ : ℤ) * tripleDet u r := by
  have h := Matrix.det_permute σ
    (Matrix.of fun i j => u (r i) j)
  simp only [tripleDet]
  rw [← h]
  rfl

/-- `thm:exterior-cube-master`, boxed expectation identity:
`Σ_{a,b,c} w_a w_b w_c det[u_a,u_b,u_c]² = 6 det M` — the
ordered form of the boxed Cauchy–Binet value and the i.i.d.
second moment of the record volume. -/
theorem cube_expectation (w : m → ℝ) (u : m → Fin 3 → ℝ) :
    ∑ r : Fin 3 → m,
        (∏ i, w (r i)) * tripleDet u r ^ 2
      = 6 * (cubeM w u).det := by
  have hleib : ∀ r : Fin 3 → m, tripleDet u r
      = ∑ σ : Equiv.Perm (Fin 3),
          (Equiv.Perm.sign σ : ℤ) * ∏ i, u (r (σ i)) i := by
    intro r
    rw [tripleDet, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  calc ∑ r : Fin 3 → m, (∏ i, w (r i)) * tripleDet u r ^ 2
      = ∑ r : Fin 3 → m, ∑ σ : Equiv.Perm (Fin 3),
          (Equiv.Perm.sign σ : ℤ)
            * ((∏ i, w (r i)) * (∏ i, u (r (σ i)) i)
              * tripleDet u r) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [sq, show tripleDet u r * tripleDet u r
            = tripleDet u r * tripleDet u r from rfl]
        conv_lhs => rw [show (∏ i, w (r i))
            * (tripleDet u r * tripleDet u r)
          = tripleDet u r * ((∏ i, w (r i)) * tripleDet u r)
          from by ring]
        rw [hleib r, Finset.sum_mul]
        refine Finset.sum_congr rfl fun σ _ => ?_
        ring
    _ = ∑ σ : Equiv.Perm (Fin 3), ∑ r : Fin 3 → m,
          (Equiv.Perm.sign σ : ℤ)
            * ((∏ i, w (r i)) * (∏ i, u (r (σ i)) i)
              * tripleDet u r) := Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin 3), ∑ r : Fin 3 → m,
          (∏ i, w (r i) * u (r i) i) * tripleDet u r := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← (Equiv.arrowCongr σ (Equiv.refl m)).sum_comp
          (fun r => (Equiv.Perm.sign σ : ℤ)
            * ((∏ i, w (r i)) * (∏ i, u (r (σ i)) i)
              * tripleDet u r))]
        refine Finset.sum_congr rfl fun t _ => ?_
        have harr : ∀ i, (Equiv.arrowCongr σ (Equiv.refl m)) t i
            = t (σ.symm i) := fun i => rfl
        have h1 : (∏ i, w ((Equiv.arrowCongr σ (Equiv.refl m)) t i))
            = ∏ i, w (t i) := by
          simp only [harr]
          exact Fintype.prod_equiv σ.symm _ _ fun i => rfl
        have h2 : (∏ i,
            u ((Equiv.arrowCongr σ (Equiv.refl m)) t (σ i)) i)
            = ∏ i, u (t i) i := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [harr, Equiv.symm_apply_apply]
        have h3 : tripleDet u ((Equiv.arrowCongr σ (Equiv.refl m)) t)
            = (Equiv.Perm.sign σ.symm : ℤ) * tripleDet u t := by
          rw [show (Equiv.arrowCongr σ (Equiv.refl m)) t
              = t ∘ σ.symm from rfl]
          exact tripleDet_comp u t σ.symm
        rw [h1, h2, h3, Equiv.Perm.sign_symm]
        have hsgn : ((Equiv.Perm.sign σ : ℤ) : ℝ)
            * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
            rw [h] <;> norm_num
        rw [Finset.prod_mul_distrib]
        linear_combination ((∏ i, w (t i)) * (∏ i, u (t i) i)
          * tripleDet u t) * hsgn
    _ = 6 * (cubeM w u).det := by
        rw [Finset.sum_const, Finset.card_univ,
          ← cube_det_expansion,
          show Fintype.card (Equiv.Perm (Fin 3)) = 6 from by
            simp [Fintype.card_perm, Nat.factorial],
          nsmul_eq_mul]
        norm_num

/-- Isotropic normalization: the canonical record `M = I₃/3` has
ordered squared-volume mean `6 det(I₃/3) = 2/9`. -/
theorem cube_isotropic :
    6 * ((3⁻¹ : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      = 2 / 9 := by
  rw [Matrix.det_smul]
  norm_num

end NCG
