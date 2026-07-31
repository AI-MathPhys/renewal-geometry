/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Schur shorting and the cluster–Feshbach reduction
  (`thm:schur`, `thm:v002-cluster`, arithmetic monograph)

* `schur_short` — the Schur-short variational principle: for a PSD
  block Gram matrix `[[A,B],[Bᴴ,C]]` with `Ran Bᴴ ⊆ Ran C`
  (witnessed by a solution `Z` of `CZ = Bᴴ`), the short
  `A - ZᴴCZ = A - BC†Bᴴ` is PSD, is the infimum of the joint
  quadratic form over the nuisance component, and the minimizer is
  `y = -Zx`;
* `inv_shift_posSemidef` — inverse monotonicity `N ⪰ δ·1 > 0 ⇒
  N⁻¹ ⪯ δ⁻¹·1` (via the spectral theorem);
* `cluster_feshbach_det` — the Feshbach–Schur determinant
  factorization `det(Q-z) = det(C-z)·det(A-z-Bᴴ(C-z)⁻¹B)`;
* `cluster_feshbach_bound` — the self-energy sandwich
  `0 ⪯ Bᴴ(C-z)⁻¹B ⪯ (β²/δ)·1`.

The sin-Θ spectral-projection clause of `thm:v002-cluster` is the
declared analytic input (contour perturbation theory).
-/

namespace NCG

open Matrix

open scoped ComplexOrder

section Schur

variable {s n : Type*} [Fintype s] [Fintype n]

omit [Fintype s] [Fintype n] in
private lemma star_sum_elim (x : s → ℂ) (y : n → ℂ) :
    star (Sum.elim x y) = Sum.elim (star x) (star y) := by
  funext i
  cases i <;> rfl

/-- `thm:schur`: the Schur-short variational principle. With a
solvability witness `CZ = Bᴴ` for the range condition, the short
`A - ZᴴCZ` is PSD, bounds the joint form from below, and is
attained at the least-norm minimizer `y = -Zx`. -/
theorem schur_short (A : Matrix s s ℂ) (B : Matrix s n ℂ)
    (C : Matrix n n ℂ) (Z : Matrix n s ℂ) (hZ : C * Z = Bᴴ)
    (hPSD : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    (A - Zᴴ * C * Z).PosSemidef
      ∧ (∀ (x : s → ℂ) (y : n → ℂ),
          star x ⬝ᵥ ((A - Zᴴ * C * Z) *ᵥ x)
            ≤ star (Sum.elim x y)
                ⬝ᵥ ((Matrix.fromBlocks A B Bᴴ C)
                  *ᵥ Sum.elim x y))
      ∧ (∀ x : s → ℂ,
          star (Sum.elim x (-(Z *ᵥ x)))
              ⬝ᵥ ((Matrix.fromBlocks A B Bᴴ C)
                *ᵥ Sum.elim x (-(Z *ᵥ x)))
            = star x ⬝ᵥ ((A - Zᴴ * C * Z) *ᵥ x)) := by
  have hCH : Cᴴ = C := by
    have h := hPSD.1
    have := congrArg Matrix.toBlocks₂₂ h
    simpa [Matrix.fromBlocks_conjTranspose] using this
  have hB : Zᴴ * C = B := by
    have h := congrArg Matrix.conjTranspose hZ
    rw [Matrix.conjTranspose_mul, hCH,
      Matrix.conjTranspose_conjTranspose] at h
    exact h
  have hCpsd : C.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hCH ?_
    intro y
    have h := hPSD.dotProduct_mulVec_nonneg (Sum.elim 0 y)
    rw [Matrix.fromBlocks_mulVec, star_sum_elim,
      sumElim_dotProduct_sumElim] at h
    simpa using h
  -- the exact completion-of-squares identity
  have key : ∀ (x : s → ℂ) (y : n → ℂ),
      star (Sum.elim x y)
          ⬝ᵥ ((Matrix.fromBlocks A B Bᴴ C) *ᵥ Sum.elim x y)
        = star x ⬝ᵥ ((A - Zᴴ * C * Z) *ᵥ x)
          + star (y + Z *ᵥ x) ⬝ᵥ (C *ᵥ (y + Z *ᵥ x)) := by
    intro x y
    rw [Matrix.fromBlocks_mulVec, star_sum_elim,
      sumElim_dotProduct_sumElim]
    have e1 : (Sum.elim x y ∘ Sum.inl) = x := rfl
    have e2 : (Sum.elim x y ∘ Sum.inr) = y := rfl
    rw [e1, e2]
    -- rewrite B and Bᴴ through Z
    rw [← hB, Matrix.conjTranspose_mul, hCH,
      Matrix.conjTranspose_conjTranspose]
    have hadj : ∀ w : n → ℂ,
        star x ⬝ᵥ (Zᴴ *ᵥ w) = star (Z *ᵥ x) ⬝ᵥ w := by
      intro w
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]
    simp only [Matrix.sub_mulVec, Matrix.mulVec_add, star_add,
      add_dotProduct, dotProduct_add, dotProduct_sub,
      ← Matrix.mulVec_mulVec, hadj]
    ring
  refine ⟨?_, ?_, ?_⟩
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · have hAH : Aᴴ = A := by
        have h := hPSD.1
        have := congrArg Matrix.toBlocks₁₁ h
        simpa [Matrix.fromBlocks_conjTranspose] using this
      change (A - Zᴴ * C * Z)ᴴ = A - Zᴴ * C * Z
      rw [Matrix.conjTranspose_sub, hAH,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hCH, Matrix.conjTranspose_conjTranspose]
      rw [Matrix.mul_assoc]
    · intro x
      have h := hPSD.dotProduct_mulVec_nonneg
        (Sum.elim x (-(Z *ᵥ x)))
      rw [key x (-(Z *ᵥ x))] at h
      rw [neg_add_cancel] at h
      simpa using h
  · intro x y
    rw [key x y]
    have hpos := hCpsd.dotProduct_mulVec_nonneg (y + Z *ᵥ x)
    exact le_add_of_nonneg_right hpos
  · intro x
    rw [key x (-(Z *ᵥ x)), neg_add_cancel]
    simp

end Schur

section Cluster

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Inverse monotonicity: `N ⪰ δ·1 > 0` implies `N⁻¹ ⪯ δ⁻¹·1`
(spectral theorem). -/
theorem inv_shift_posSemidef {N : Matrix n n ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hN : N.PosDef)
    (hgap : (N - (δ : ℂ) • 1).PosSemidef) :
    (((δ : ℂ)⁻¹ • 1 : Matrix n n ℂ) - N⁻¹).PosSemidef := by
  classical
  have hH := hN.1
  have heig : ∀ i, δ ≤ hH.eigenvalues i := by
    intro i
    have hv := hH.mulVec_eigenvectorBasis i
    have h := hgap.dotProduct_mulVec_nonneg
      ⇑(hH.eigenvectorBasis i)
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hv, dotProduct_sub, dotProduct_smul, dotProduct_smul] at h
    have hv0 : ⇑(hH.eigenvectorBasis i) ≠ 0 := by
      intro hc
      apply hH.eigenvectorBasis.orthonormal.ne_zero i
      ext j
      exact congrFun hc j
    have hS := dotProduct_star_self_pos_iff.mpr hv0
    rw [RCLike.pos_iff] at hS
    rw [RCLike.nonneg_iff] at h
    obtain ⟨hSre, hSim⟩ := hS
    obtain ⟨hre, him⟩ := h
    simp only [Complex.real_smul, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, RCLike.re_to_complex,
      RCLike.im_to_complex, smul_eq_mul] at hre him hSre hSim
    nlinarith
  have hpos : ∀ i, 0 < hH.eigenvalues i :=
    fun i => lt_of_lt_of_le hδ (heig i)
  set U := hH.eigenvectorUnitary with hU
  set D : Matrix n n ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) with hD
  have hNU : N = Unitary.conjStarAlgAut ℂ _ U D := hH.spectral_theorem
  have hDdet : IsUnit D.det := by
    rw [hD, Matrix.det_diagonal]
    apply isUnit_iff_ne_zero.mpr
    rw [Finset.prod_ne_zero_iff]
    intro i _
    simp only [Function.comp_apply, RCLike.ofReal_ne_zero]
    exact (hpos i).ne'
  have hinv : N⁻¹ = Unitary.conjStarAlgAut ℂ _ U D⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [hNU, ← map_mul, Matrix.nonsing_inv_mul _ hDdet, map_one]
  have hone : ((δ : ℂ)⁻¹ • 1 : Matrix n n ℂ)
      = Unitary.conjStarAlgAut ℂ _ U ((δ : ℂ)⁻¹ • 1) := by
    rw [map_smul, map_one]
  rw [hone, hinv, ← map_sub]
  have hDinvEq : D⁻¹
      = Matrix.diagonal
          (fun i => (RCLike.ofReal (hH.eigenvalues i) : ℂ)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [hD, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => (RCLike.ofReal (hH.eigenvalues i) : ℂ)⁻¹
          * (RCLike.ofReal ∘ hH.eigenvalues) i)
        = fun _ => (1 : ℂ) from funext fun i =>
          inv_mul_cancel₀ (by
            simp only [RCLike.ofReal_ne_zero]
            exact (hpos i).ne'), Matrix.diagonal_one]
  have hdiag : ((δ : ℂ)⁻¹ • 1 : Matrix n n ℂ) - D⁻¹
      = Matrix.diagonal
          (fun i => ((δ⁻¹ - (hH.eigenvalues i)⁻¹ : ℝ) : ℂ)) := by
    rw [hDinvEq]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
        smul_eq_mul, mul_one]
      push_cast
      rfl
    · simp [Matrix.sub_apply, Matrix.smul_apply,
        Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [hdiag, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose]
  refine (Matrix.posSemidef_diagonal_iff.mpr
    ?_).mul_mul_conjTranspose_same _
  intro i
  apply Complex.zero_le_real.mpr
  rw [sub_nonneg]
  exact (inv_le_inv₀ (hpos i) hδ).mpr (heig i)

/-- `thm:v002-cluster` (Feshbach determinant): the Schur
factorization `det(Q-z) = det(C-z)·det(A-z-Bᴴ(C-z)⁻¹B)`. -/
theorem cluster_feshbach_det {s' n' : Type*} [Fintype s']
    [Fintype n'] [DecidableEq s'] [DecidableEq n']
    (A : Matrix s' s' ℂ) (B : Matrix n' s' ℂ)
    (C : Matrix n' n' ℂ) (z : ℂ)
    (hCz : IsUnit (C - z • 1).det) :
    ((Matrix.fromBlocks A Bᴴ B C)
        - z • (1 : Matrix (s' ⊕ n') (s' ⊕ n') ℂ)).det
      = (C - z • 1).det
        * ((A - z • 1) - Bᴴ * (C - z • 1)⁻¹ * B).det := by
  have hsplit : (Matrix.fromBlocks A Bᴴ B C)
        - z • (1 : Matrix (s' ⊕ n') (s' ⊕ n') ℂ)
      = Matrix.fromBlocks (A - z • 1) Bᴴ B (C - z • 1) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq]
  rw [hsplit]
  letI := Matrix.invertibleOfIsUnitDet _ hCz
  rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]

/-- `thm:v002-cluster` (self-energy sandwich):
`0 ⪯ Bᴴ(C-z)⁻¹B ⪯ (β²/δ)·1` below the gap. -/
theorem cluster_feshbach_bound {s' n' : Type*} [Finite s']
    [Fintype n'] [DecidableEq s'] [DecidableEq n']
    (B : Matrix n' s' ℂ) (C : Matrix n' n' ℂ) (z : ℂ) {δ β : ℝ}
    (hδ : 0 < δ) (hCz : (C - z • 1).PosDef)
    (hgap : ((C - z • 1) - (δ : ℂ) • 1).PosSemidef)
    (hβ : ((β ^ 2 : ℂ) • 1 - Bᴴ * B).PosSemidef) :
    (Bᴴ * (C - z • 1)⁻¹ * B).PosSemidef
    ∧ (((β ^ 2 / δ : ℝ) : ℂ) • (1 : Matrix s' s' ℂ)
        - Bᴴ * (C - z • 1)⁻¹ * B).PosSemidef := by
  haveI := Fintype.ofFinite s'
  constructor
  · exact (hCz.posSemidef.inv).conjTranspose_mul_mul_same B
  · have h1 := (inv_shift_posSemidef hδ hCz
      hgap).conjTranspose_mul_mul_same B
    have h2 : (((δ⁻¹ : ℝ) : ℂ)
        • ((β ^ 2 : ℂ) • 1 - Bᴴ * B)).PosSemidef := by
      apply hβ.smul
      exact Complex.zero_le_real.mpr (by positivity)
    have hsum := h1.add h2
    have hexpand : Bᴴ * (((δ : ℂ)⁻¹ • 1) - (C - z • 1)⁻¹) * B
          + ((δ⁻¹ : ℝ) : ℂ) • ((β ^ 2 : ℂ) • 1 - Bᴴ * B)
        = ((β ^ 2 / δ : ℝ) : ℂ) • (1 : Matrix s' s' ℂ)
          - Bᴴ * (C - z • 1)⁻¹ * B := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one]
      push_cast
      match_scalars <;> ring
    rwa [hexpand] at hsum

end Cluster

end NCG
