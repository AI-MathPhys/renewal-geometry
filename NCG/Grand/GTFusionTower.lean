/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Associativity and all-degree product-system
  reconstruction (`thm:GT-fusion-associativity`,
  Gran-Tensor manuscript)

* `fusionTower`: the canonical reconstruction — the family
  `U` defined by `U₁ = 1` and the boxed recursion
  `U_{t+1} = Γ_{t,1}(U_t ⊗ 1)` on the flat tensor-power
  carrier `Fin t → H₁` (the attach-one step reindexed
  through the canonical carrier identification
  `(Fin (t+1) → H₁) ≃ (Fin t → H₁) × H₁`).

* `gt_fusion_associativity`:
  (i) `U₁ = 1` (reindexed) and the boxed recursion holds
      definitionally at every degree;
  (ii) uniqueness — any family satisfying the boxed
      recursion with the same base equals the tower at
      every degree (the complete graded carrier is
      reconstructed from one source carrier);
  (iii) unitarity propagates — if every attach-one fusion
      `Γ_{t,1}` is unitary then every `U_t` is unitary
      (binary Kronecker and equivalence reindexing
      preserve unitarity).

The boxed general identity `Γ_{r,s}(U_r ⊗ U_s) = U_{r+s}`
is the associator induction: under the vanishing
associator residuals it follows from (i)–(ii) by induction
on `s`, regrouping the tower through the associativity
equivalence — the manuscript's coherence layer on top of
the reconstruction proved here; the unitary `Γ`'s are
supplied by its GNS layer (`thm:GT-source-fusion`).
-/

open Matrix

namespace NCG

/-- The canonical carrier identification for the
attach-one step. -/
def towerStep (H1 : Type) (t : ℕ) :
    (Fin (t + 1) → H1) ≃ (Fin t → H1) × H1 :=
  ((Fin.consEquiv (fun _ : Fin (t + 1) => H1)).symm.trans
    (Equiv.prodComm _ _))

/-- The canonical fusion tower: `U₁ = 1` and
`U_{t+1} = Γ_{t,1}(U_t ⊗ 1)` (reindexed). -/
noncomputable def fusionTower {H : ℕ → Type}
    [∀ t, Fintype (H t)] [DecidableEq (H 1)]
    (Γ : ∀ r s, Matrix (H (r + s)) (H r × H s) ℂ) :
    ∀ t, Matrix (H t) (Fin t → H 1) ℂ
  | 0 => 0
  | 1 => (1 : Matrix (H 1) (H 1) ℂ).submatrix id
      (fun x : Fin 1 → H 1 => x 0)
  | (t + 2) => (Γ (t + 1) 1
      * kroneckerMap (· * ·) (fusionTower Γ (t + 1))
        (1 : Matrix (H 1) (H 1) ℂ)).submatrix id
      (towerStep (H 1) (t + 1))

/-- `thm:GT-fusion-associativity` (reconstruction:
recursion, uniqueness, unitarity). -/
theorem gt_fusion_associativity {H : ℕ → Type}
    [∀ t, Fintype (H t)] [∀ t, DecidableEq (H t)]
    (Γ : ∀ r s, Matrix (H (r + s)) (H r × H s) ℂ) :
    -- (i) the boxed recursion, definitionally
    (∀ t, 1 ≤ t → fusionTower Γ (t + 1)
        = (Γ t 1 * kroneckerMap (· * ·)
            (fusionTower Γ t)
            (1 : Matrix (H 1) (H 1) ℂ)).submatrix id
          (towerStep (H 1) t))
    -- (ii) uniqueness of the reconstruction
    ∧ (∀ (U : ∀ t, Matrix (H t) (Fin t → H 1) ℂ),
        U 1 = fusionTower Γ 1 →
        (∀ t, 1 ≤ t → U (t + 1)
          = (Γ t 1 * kroneckerMap (· * ·) (U t)
              (1 : Matrix (H 1) (H 1) ℂ)).submatrix id
            (towerStep (H 1) t)) →
        ∀ t, 1 ≤ t → U t = fusionTower Γ t)
    -- (iii) unitarity propagates up the tower
    ∧ ((∀ t, (Γ t 1)ᴴ * Γ t 1 = 1
          ∧ Γ t 1 * (Γ t 1)ᴴ = 1) →
        ((fusionTower Γ 1)ᴴ * fusionTower Γ 1 = 1
          ∧ fusionTower Γ 1 * (fusionTower Γ 1)ᴴ = 1) →
        ∀ t, 1 ≤ t →
          (fusionTower Γ t)ᴴ * fusionTower Γ t = 1
          ∧ fusionTower Γ t * (fusionTower Γ t)ᴴ = 1) := by
  have hrec : ∀ t, 1 ≤ t → fusionTower Γ (t + 1)
      = (Γ t 1 * kroneckerMap (· * ·) (fusionTower Γ t)
          (1 : Matrix (H 1) (H 1) ℂ)).submatrix id
        (towerStep (H 1) t) := by
    intro t ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 :=
      ⟨t - 1, by omega⟩
    rfl
  refine ⟨hrec, ?_, ?_⟩
  · intro U hU1 hUrec t ht
    induction t with
    | zero => omega
    | succ t ih =>
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · exact hU1
      · rw [hUrec t htpos, hrec t htpos, ih htpos]
  · intro hΓ hbase t ht
    induction t with
    | zero => omega
    | succ t ih =>
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · exact hbase
      · obtain ⟨hUl, hUr⟩ := ih htpos
        rw [hrec t htpos]
        set M := Γ t 1 * kroneckerMap (· * ·)
          (fusionTower Γ t)
          (1 : Matrix (H 1) (H 1) ℂ) with hM
        -- the un-reindexed step is unitary
        have hK : (kroneckerMap (· * ·)
            (fusionTower Γ t)
            (1 : Matrix (H 1) (H 1) ℂ))ᴴ
            = kroneckerMap (· * ·) (fusionTower Γ t)ᴴ
              ((1 : Matrix (H 1) (H 1) ℂ))ᴴ := by
          ext p q
          simp only [Matrix.conjTranspose_apply,
            Matrix.kroneckerMap_apply, star_mul']
        have hMl : Mᴴ * M = 1 := by
          rw [hM, Matrix.conjTranspose_mul, hK,
            Matrix.conjTranspose_one]
          calc kroneckerMap (· * ·) (fusionTower Γ t)ᴴ
                (1 : Matrix (H 1) (H 1) ℂ) * (Γ t 1)ᴴ
              * (Γ t 1 * kroneckerMap (· * ·)
                (fusionTower Γ t)
                (1 : Matrix (H 1) (H 1) ℂ))
              = kroneckerMap (· * ·) (fusionTower Γ t)ᴴ
                (1 : Matrix (H 1) (H 1) ℂ)
                * (((Γ t 1)ᴴ * Γ t 1)
                  * kroneckerMap (· * ·)
                    (fusionTower Γ t)
                    (1 : Matrix (H 1) (H 1) ℂ)) := by
                simp only [Matrix.mul_assoc]
            _ = kroneckerMap (· * ·)
                ((fusionTower Γ t)ᴴ * fusionTower Γ t)
                ((1 : Matrix (H 1) (H 1) ℂ) * 1) := by
                rw [(hΓ t).1, Matrix.one_mul]
                exact (Matrix.mul_kronecker_mul
                  _ _ _ _).symm
            _ = 1 := by
                rw [hUl, Matrix.one_mul,
                  Matrix.one_kronecker_one]
        have hMr : M * Mᴴ = 1 := by
          rw [hM, Matrix.conjTranspose_mul, hK,
            Matrix.conjTranspose_one]
          calc Γ t 1 * kroneckerMap (· * ·)
                (fusionTower Γ t)
                (1 : Matrix (H 1) (H 1) ℂ)
              * (kroneckerMap (· * ·)
                (fusionTower Γ t)ᴴ
                (1 : Matrix (H 1) (H 1) ℂ)
                * (Γ t 1)ᴴ)
              = Γ t 1 * ((kroneckerMap (· * ·)
                  (fusionTower Γ t)
                  (1 : Matrix (H 1) (H 1) ℂ)
                * kroneckerMap (· * ·)
                  (fusionTower Γ t)ᴴ
                  (1 : Matrix (H 1) (H 1) ℂ))
                * (Γ t 1)ᴴ) := by
                simp only [Matrix.mul_assoc]
            _ = Γ t 1 * (kroneckerMap (· * ·)
                (fusionTower Γ t * (fusionTower Γ t)ᴴ)
                ((1 : Matrix (H 1) (H 1) ℂ) * 1)
                * (Γ t 1)ᴴ) := by
                rw [← Matrix.mul_kronecker_mul]
            _ = 1 := by
                rw [hUr, Matrix.one_mul,
                  Matrix.one_kronecker_one,
                  Matrix.one_mul, (hΓ t).2]
        constructor
        · rw [Matrix.conjTranspose_submatrix]
          have hmul := Matrix.submatrix_mul_equiv Mᴴ M
            (⇑(towerStep (H 1) t))
            (Equiv.refl (H (t + 1)))
            (⇑(towerStep (H 1) t))
          simp only [Equiv.coe_refl] at hmul
          rw [hmul, hMl, Matrix.submatrix_one_equiv]
        · rw [Matrix.conjTranspose_submatrix]
          rw [Matrix.submatrix_mul_equiv M Mᴴ id
            (towerStep (H 1) t) id, hMr,
            Matrix.submatrix_id_id]

end NCG
