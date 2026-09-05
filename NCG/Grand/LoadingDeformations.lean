/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PeanoLadder

/-!
# Loading deformations of the Peano histories
  (`thm:ar-loading-deformations`, Gran-Tensor manuscript)

* `loading_deformation`: the boxed rigidity — any operator with
  the deformed covariance `M S = S^a M` and deformed anchor
  `M η = c·S^{a-1}η` is exactly `M = c·L_a`, so relaxed natural
  loadings are scalar deformations of the Peano histories;
* `affine_count_rigidity`: the boxed count deformation — any
  `D` with `Dη = αη` and `[D, S] = βS` is the affine diagonal
  `D = diag(α + (n-1)β)`.

Rendering disclosed: the multiplicativity `c_{ab} = c_a c_b`
below cutoff and the zeta-history Euler product for a
completely multiplicative family read off the rigidity clause
composed with the proved `peano_product`, and are the
manuscript's remaining bookkeeping (the Euler product is the
separate finite-Euler record).
-/

open Matrix

namespace NCG

private lemma pow_mulVec_single0 {X : ℕ} (hX : 0 < X) (k : ℕ)
    (j : Fin X) :
    ((recS X) ^ k *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j
      = if (j : ℕ) = k then 1 else 0 := by
  rw [recS_pow, mulVec_single_col, Matrix.of_apply]
  have hval : ((⟨0, hX⟩ : Fin X) : ℕ) = 0 := rfl
  rw [hval, zero_add]

/-- `thm:ar-loading-deformations`, boxed rigidity: a deformed
covariant loading is a scalar multiple of the Peano history. -/
theorem loading_deformation {X : ℕ} (hX : 0 < X) (a : ℕ)
    (ha : 1 ≤ a) (M : Matrix (Fin X) (Fin X) ℂ) (c : ℂ)
    (hMS : M * recS X = (recS X) ^ a * M)
    (hMη : M *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
      = c • ((recS X) ^ (a - 1)
        *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1)) :
    M = c • peanoL X a := by
  have hcols : ∀ (m : ℕ) (hm : m < X),
      M *ᵥ Pi.single (⟨m, hm⟩ : Fin X) 1
        = c • ((recS X) ^ (a * (m + 1) - 1)
          *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) := by
    intro m
    induction m with
    | zero =>
      intro hm
      rw [show a * (0 + 1) - 1 = a - 1 from by omega]
      exact hMη
    | succ m ih =>
      intro hm1
      have hm : m < X := Nat.lt_of_succ_lt hm1
      have hstep : (M * recS X)
            *ᵥ Pi.single (⟨m, hm⟩ : Fin X) (1 : ℂ)
          = ((recS X) ^ a * M)
            *ᵥ Pi.single (⟨m, hm⟩ : Fin X) 1 := by
        rw [hMS]
      rw [← Matrix.mulVec_mulVec, recS_mulVec_single hm hm1,
        ← Matrix.mulVec_mulVec, ih hm, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, ← pow_add] at hstep
      rw [hstep, show a + (a * (m + 1) - 1)
          = a * (m + 1 + 1) - 1 from by
        have hp : 0 < a * (m + 1) :=
          Nat.mul_pos (by omega) (Nat.succ_pos _)
        have hd : a * (m + 1 + 1) = a * (m + 1) + a := by ring
        omega]
  ext j i
  have hc := hcols (i : ℕ) i.isLt
  rw [Fin.eta] at hc
  have hji := congrFun hc j
  rw [mulVec_single_col] at hji
  rw [hji, Pi.smul_apply, pow_mulVec_single0 hX, smul_eq_mul,
    Matrix.smul_apply, peanoL, Matrix.of_apply, smul_eq_mul]
  have hp : 0 < a * ((i : ℕ) + 1) :=
    Nat.mul_pos (by omega) (Nat.succ_pos _)
  by_cases hcond : (j : ℕ) = a * ((i : ℕ) + 1) - 1
  · rw [if_pos hcond, if_pos (by omega), mul_one]
  · rw [if_neg hcond, if_neg (fun h => hcond (by omega)),
      mul_zero]

/-- `thm:ar-loading-deformations`, count clause: an affinely
deformed count is the affine diagonal. -/
theorem affine_count_rigidity {X : ℕ} (hX : 0 < X)
    (D : Matrix (Fin X) (Fin X) ℂ) (α β : ℂ)
    (hanchor : D *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
      = α • Pi.single (⟨0, hX⟩ : Fin X) 1)
    (hcomm : D * recS X - recS X * D = β • recS X) :
    D = Matrix.diagonal
      (fun i : Fin X => α + (i : ℕ) * β) := by
  have hDS : D * recS X = recS X * D + β • recS X := by
    rw [sub_eq_iff_eq_add] at hcomm
    rw [hcomm]
    abel
  have hcols : ∀ (m : ℕ) (hm : m < X),
      D *ᵥ Pi.single (⟨m, hm⟩ : Fin X) 1
        = (α + (m : ℂ) * β)
          • Pi.single (⟨m, hm⟩ : Fin X) 1 := by
    intro m
    induction m with
    | zero =>
      intro hm
      rw [show α + ((0 : ℕ) : ℂ) * β = α from by
        push_cast; ring]
      exact hanchor
    | succ m ih =>
      intro hm1
      have hm : m < X := Nat.lt_of_succ_lt hm1
      have hstep : (D * recS X)
            *ᵥ Pi.single (⟨m, hm⟩ : Fin X) (1 : ℂ)
          = (recS X * D + β • recS X)
            *ᵥ Pi.single (⟨m, hm⟩ : Fin X) 1 := by
        rw [hDS]
      rw [← Matrix.mulVec_mulVec, recS_mulVec_single hm hm1,
        Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ih hm,
        Matrix.mulVec_smul, recS_mulVec_single hm hm1,
        Matrix.smul_mulVec, recS_mulVec_single hm hm1]
        at hstep
      rw [hstep]
      push_cast
      module
  ext j i
  have hc := hcols (i : ℕ) i.isLt
  rw [Fin.eta] at hc
  have hji := congrFun hc j
  rw [mulVec_single_col] at hji
  rw [hji, Matrix.diagonal_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  by_cases hd : j = i
  · rw [if_pos hd, if_pos hd, mul_one, hd]
  · rw [if_neg hd, if_neg hd, mul_zero]

end NCG
