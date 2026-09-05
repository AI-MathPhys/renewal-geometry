/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointSourceUniversality

/-!
# Common-action Hessian, Schur residual, and Ward router
  (`thm:common-action-router`, Gran-Tensor manuscript)

* `common_action_router`: with Gram-factor data
  `G = B_Γᴴ B_Γ ≻ 0`, `C = B_Γᴴ B_E`, `G_E = B_Eᴴ B_E`,
  `K = G⁻¹ C`, `S_E = G_E − Cᴴ G⁻¹ C`, and the range
  projection `P = B_Γ G⁻¹ B_Γᴴ`:
  (1) `P` is a hermitian idempotent with `B_Γᴴ(I−P) = 0`;
  (2) the boxed compression `S_E = B_Eᴴ (I−P) B_E ⪰ 0`;
  (3) the boxed variational identity as an exact Pythagoras:
      `‖B_Γx + B_Ey‖² = ‖B_Γ(x+Ky)‖² + ⟨y, S_E y⟩`, so the
      infimum over `x` is attained at `x = −Ky` with value the
      Schur-residual form;
  (4) the boxed equivalences
      `S_E = 0 ⟺ B_E = B_Γ K ⟺ G_E = Kᴴ G K`;
  (5) the Ward router: if the symmetry direction satisfies the
      two block rows of `H𝓡_W = 0` (`C = G W`, `G_E = Cᴴ W`),
      then `K = W`, `G_E = Wᴴ G W`, and `S_E = 0`.

Rendering disclosed: the `C²`-functional origin of the Hessian
and the closed-range/pseudo-inverse formulation are rendered by
the declared Gram factors with faithful `G ≻ 0` (on the closed
range the compression is positive definite — the manuscript's
own support reduction); the infimum is rendered by the exact
attained Pythagoras identity.
-/

open Matrix
open scoped ComplexOrder

-- the `show` tactics below unfold the statement's `let`
-- abbreviations (defeq) for readability; the style linter
-- cannot distinguish this from goal rewriting.
set_option linter.style.show false

namespace NCG

/-- `thm:common-action-router`. -/
theorem common_action_router {h g e : Type*} [Fintype h]
    [Fintype g] [Fintype e] [DecidableEq h] [DecidableEq g]
    (BΓ : Matrix h g ℂ) (BE : Matrix h e ℂ)
    (hG : (BΓᴴ * BΓ).PosDef) :
    let G : Matrix g g ℂ := BΓᴴ * BΓ
    let C : Matrix g e ℂ := BΓᴴ * BE
    let GE : Matrix e e ℂ := BEᴴ * BE
    let K : Matrix g e ℂ := G⁻¹ * C
    let SE : Matrix e e ℂ := GE - Cᴴ * G⁻¹ * C
    let P : Matrix h h ℂ := BΓ * G⁻¹ * BΓᴴ
    -- (1) hermitian idempotent annihilating the source rows
    (Pᴴ = P ∧ P * P = P ∧ BΓᴴ * ((1 : Matrix h h ℂ) - P) = 0)
    -- (2) the boxed Schur-residual compression and positivity
    ∧ SE = BEᴴ * ((1 : Matrix h h ℂ) - P) * BE
    ∧ SE.PosSemidef
    -- (3) the boxed exact variational (Pythagoras) identity
    ∧ (∀ (x : g → ℂ) (y : e → ℂ),
        star (BΓ *ᵥ x + BE *ᵥ y)
            ⬝ᵥ (BΓ *ᵥ x + BE *ᵥ y)
          = star (BΓ *ᵥ (x + K *ᵥ y))
              ⬝ᵥ (BΓ *ᵥ (x + K *ᵥ y))
            + star y ⬝ᵥ (SE *ᵥ y))
    -- (4) the boxed vanishing equivalences
    ∧ (SE = 0 ↔ BE = BΓ * K)
    ∧ (SE = 0 ↔ GE = Kᴴ * G * K)
    -- (5) the Ward router
    ∧ (∀ W : Matrix g e ℂ, C = G * W → GE = Cᴴ * W →
        K = W ∧ GE = Wᴴ * G * W ∧ SE = 0) := by
  haveI := hG.isUnit.invertible
  intro G C GE K SE P
  have hGH : Gᴴ = G := hG.1
  have hGiH : (G⁻¹)ᴴ = G⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hGH]
  have hPH : Pᴴ = P := by
    show (BΓ * G⁻¹ * BΓᴴ)ᴴ = BΓ * G⁻¹ * BΓᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hGiH, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hann : BΓᴴ * ((1 : Matrix h h ℂ) - P) = 0 := by
    show BΓᴴ * ((1 : Matrix h h ℂ) - BΓ * G⁻¹ * BΓᴴ) = 0
    rw [Matrix.mul_sub, Matrix.mul_one]
    rw [show BΓᴴ * (BΓ * G⁻¹ * BΓᴴ)
        = (BΓᴴ * BΓ) * G⁻¹ * BΓᴴ from by
      simp only [Matrix.mul_assoc]]
    rw [show (BΓᴴ * BΓ) * G⁻¹ = 1 from
      Matrix.mul_inv_of_invertible G]
    rw [Matrix.one_mul, sub_self]
  have hannT : ((1 : Matrix h h ℂ) - P) * BΓ = 0 := by
    have hh := congrArg Matrix.conjTranspose hann
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      hPH, Matrix.conjTranspose_conjTranspose] at hh
  have hP2 : P * P = P := by
    show BΓ * G⁻¹ * BΓᴴ * (BΓ * G⁻¹ * BΓᴴ)
      = BΓ * G⁻¹ * BΓᴴ
    rw [show BΓ * G⁻¹ * BΓᴴ * (BΓ * G⁻¹ * BΓᴴ)
        = BΓ * G⁻¹ * ((BΓᴴ * BΓ) * G⁻¹) * BΓᴴ from by
      simp only [Matrix.mul_assoc]]
    rw [show (BΓᴴ * BΓ) * G⁻¹ = 1 from
      Matrix.mul_inv_of_invertible G]
    rw [Matrix.mul_one]
  have hCH : Cᴴ = BEᴴ * BΓ := by
    show (BΓᴴ * BE)ᴴ = BEᴴ * BΓ
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hSE : SE = BEᴴ * ((1 : Matrix h h ℂ) - P) * BE := by
    show GE - Cᴴ * G⁻¹ * C
      = BEᴴ * ((1 : Matrix h h ℂ) - P) * BE
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    congr 1
    rw [hCH]
    show BEᴴ * BΓ * G⁻¹ * C
      = BEᴴ * (BΓ * G⁻¹ * BΓᴴ) * BE
    show BEᴴ * BΓ * G⁻¹ * (BΓᴴ * BE)
      = BEᴴ * (BΓ * G⁻¹ * BΓᴴ) * BE
    simp only [Matrix.mul_assoc]
  have hQH : ((1 : Matrix h h ℂ) - P)ᴴ
      = (1 : Matrix h h ℂ) - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hPH]
  have hQ2 : ((1 : Matrix h h ℂ) - P)
      * ((1 : Matrix h h ℂ) - P)
      = (1 : Matrix h h ℂ) - P := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Matrix.one_mul, hP2, sub_self, sub_zero]
  have hSEgram : SE
      = (((1 : Matrix h h ℂ) - P) * BE)ᴴ
          * (((1 : Matrix h h ℂ) - P) * BE) := by
    rw [hSE, Matrix.conjTranspose_mul, hQH]
    rw [show BEᴴ * ((1 : Matrix h h ℂ) - P)
        * (((1 : Matrix h h ℂ) - P) * BE)
        = BEᴴ * (((1 : Matrix h h ℂ) - P)
            * ((1 : Matrix h h ℂ) - P)) * BE from by
      simp only [Matrix.mul_assoc]]
    rw [hQ2]
  have hPB : P * BE = BΓ * K := by
    show BΓ * G⁻¹ * BΓᴴ * BE = BΓ * (G⁻¹ * (BΓᴴ * BE))
    simp only [Matrix.mul_assoc]
  refine ⟨⟨hPH, hP2, hann⟩, hSE, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSEgram]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · -- Pythagoras
    intro x y
    have hcross : BΓᴴ * (((1 : Matrix h h ℂ) - P) * BE)
        = 0 := by
      rw [← Matrix.mul_assoc, hann, Matrix.zero_mul]
    have hcross' : (((1 : Matrix h h ℂ) - P) * BE)ᴴ * BΓ
        = 0 := by
      rw [Matrix.conjTranspose_mul, hQH, Matrix.mul_assoc,
        hannT, Matrix.mul_zero]
    have hdec : BΓ *ᵥ x + BE *ᵥ y
        = BΓ *ᵥ (x + K *ᵥ y)
          + (((1 : Matrix h h ℂ) - P) * BE) *ᵥ y := by
      rw [Matrix.mulVec_add,
        show BΓ *ᵥ (K *ᵥ y) = (BΓ * K) *ᵥ y from
          Matrix.mulVec_mulVec _ _ _,
        Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec,
        hPB]
      abel
    have hmix : ∀ (u : g → ℂ) (v : e → ℂ),
        star (BΓ *ᵥ u)
            ⬝ᵥ ((((1 : Matrix h h ℂ) - P) * BE) *ᵥ v)
          = star u
            ⬝ᵥ ((BΓᴴ * (((1 : Matrix h h ℂ) - P) * BE))
                *ᵥ v) := by
      intro u v
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
        Matrix.mulVec_mulVec]
    have hmix' : ∀ (v : e → ℂ) (u : g → ℂ),
        star ((((1 : Matrix h h ℂ) - P) * BE) *ᵥ v)
            ⬝ᵥ (BΓ *ᵥ u)
          = star v
            ⬝ᵥ (((((1 : Matrix h h ℂ) - P) * BE)ᴴ * BΓ)
                *ᵥ u) := by
      intro v u
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
        Matrix.mulVec_mulVec]
    rw [hdec,
      show ∀ u v : h → ℂ, star (u + v) ⬝ᵥ (u + v)
          = star u ⬝ᵥ u + star u ⬝ᵥ v + star v ⬝ᵥ u
            + star v ⬝ᵥ v from fun u v => by
        rw [star_add, add_dotProduct, dotProduct_add,
          dotProduct_add]
        ring,
      hmix, hcross, Matrix.zero_mulVec, dotProduct_zero,
      hmix', hcross', Matrix.zero_mulVec, dotProduct_zero,
      add_zero, add_zero]
    congr 1
    rw [gram_realization_inner, ← hSEgram]
  · constructor
    · intro h0
      have hz : ((1 : Matrix h h ℂ) - P) * BE = 0 :=
        Matrix.conjTranspose_mul_self_eq_zero.mp
          (hSEgram ▸ h0)
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero,
        hPB] at hz
      exact hz
    · intro hBE
      rw [hSEgram]
      have hz : ((1 : Matrix h h ℂ) - P) * BE = 0 := by
        rw [Matrix.sub_mul, Matrix.one_mul, hPB, ← hBE,
          sub_self]
      rw [hz, Matrix.conjTranspose_zero, Matrix.zero_mul]
  · have harith : Kᴴ * G * K = Cᴴ * G⁻¹ * C := by
      show (G⁻¹ * C)ᴴ * G * (G⁻¹ * C) = Cᴴ * G⁻¹ * C
      rw [Matrix.conjTranspose_mul, hGiH]
      rw [show Cᴴ * G⁻¹ * G * (G⁻¹ * C)
          = Cᴴ * (G⁻¹ * G) * (G⁻¹ * C) from by
        simp only [Matrix.mul_assoc]]
      rw [Matrix.inv_mul_of_invertible, Matrix.mul_one,
        ← Matrix.mul_assoc]
    constructor
    · intro h0
      rw [harith]
      exact sub_eq_zero.mp h0
    · intro hGE
      show GE - Cᴴ * G⁻¹ * C = 0
      rw [hGE, harith, sub_self]
  · intro W hC hGE
    have hCGC : Cᴴ * G⁻¹ * C = Wᴴ * G * W := by
      rw [hC, Matrix.conjTranspose_mul, hGH]
      calc Wᴴ * G * G⁻¹ * (G * W)
          = Wᴴ * ((G * G⁻¹) * (G * W)) := by
            simp only [Matrix.mul_assoc]
        _ = Wᴴ * (G * W) := by
            rw [Matrix.mul_inv_of_invertible,
              Matrix.one_mul]
        _ = Wᴴ * G * W := by rw [← Matrix.mul_assoc]
    have hGEW : GE = Wᴴ * G * W := by
      rw [hGE, hC, Matrix.conjTranspose_mul, hGH]
    refine ⟨?_, hGEW, ?_⟩
    · show G⁻¹ * C = W
      rw [hC, ← Matrix.mul_assoc,
        Matrix.inv_mul_of_invertible, Matrix.one_mul]
    · show GE - Cᴴ * G⁻¹ * C = 0
      rw [hCGC, hGEW, sub_self]

end NCG
