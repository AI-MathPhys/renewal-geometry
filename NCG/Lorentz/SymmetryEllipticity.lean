/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.SecondMoment

/-!
# Symmetry forces ellipticity (`prop:symmetry-ellipticity`)

If a family of orthogonal matrices acts **irreducibly** on `ℝ^d` and
a real symmetric matrix `M` is invariant under the action
(`R M Rᵀ = M`), then `M` is a scalar multiple of the identity: any
eigenspace of `M` is invariant, so by irreducibility it is
everything.  Applied to the second moment
`M = Σ w_i v_i v_iᵀ` of a finite positive invariant direction law
not supported at the origin, the scalar is **positive** — symmetry
forces the elliptic spatial phase.

The invariant measure is realized in its finite-atomic form
(weights `w_i ≥ 0` on directions `v_i`), which is the form consumed
by the renewal construction; the eigenvalue machinery is the real
(`RCLike ℝ`) spectral theorem through the functional-calculus
toolkit.
-/

namespace NCG

open Matrix

variable {d : ℕ}

/-- Invariant symmetric matrices under an irreducible orthogonal
family are scalar. -/
theorem invariant_symm_eq_smul_one [NeZero d]
    (S : Set (Matrix (Fin d) (Fin d) ℝ))
    (horth : ∀ R ∈ S, R * Rᵀ = 1)
    (hirr : ∀ W : Submodule ℝ (Fin d → ℝ),
      (∀ R ∈ S, ∀ v ∈ W, R.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    (hinv : ∀ R ∈ S, R * M * Rᵀ = M) :
    ∃ c : ℝ, M = c • 1 := by
  classical
  -- the action commutes with M
  have hcomm : ∀ R ∈ S, R * M = M * R := by
    intro R hR
    have h1 := hinv R hR
    have h2 : R * M * Rᵀ * R = M * R := by rw [h1]
    have h3 : Rᵀ * R = 1 := by
      have h4 := horth R hR
      rwa [mul_eq_one_comm] at h4
    calc R * M = R * M * 1 := by rw [mul_one]
      _ = R * M * (Rᵀ * R) := by rw [h3]
      _ = R * M * Rᵀ * R := by rw [← Matrix.mul_assoc]
      _ = M * R := h2
  -- an eigenvalue of the symmetric matrix M
  set μ : ℝ := hM.eigenvalues ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    with hμdef
  -- its eigenspace is a nonzero invariant subspace
  set W : Submodule ℝ (Fin d → ℝ) :=
    LinearMap.ker (Matrix.mulVecLin (M - μ • 1)) with hWdef
  have hWne : W ≠ ⊥ := by
    -- the eigenvector of the spectral basis lies in W
    have h6 := hM.mulVec_eigenvectorBasis
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    intro hbot
    have h7 : (⇑(hM.eigenvectorBasis ⟨0, Nat.pos_of_ne_zero
        (NeZero.ne d)⟩) : Fin d → ℝ) ∈ W := by
      rw [hWdef]
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      rw [Matrix.sub_mulVec, h6, hμdef]
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    rw [hbot] at h7
    have h8 := Submodule.mem_bot (R := ℝ) |>.mp h7
    have h9 := (hM.eigenvectorBasis).orthonormal.ne_zero
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    apply h9
    ext i
    exact congrFun h8 i
  have hWinv : ∀ R ∈ S, ∀ v ∈ W, R.mulVec v ∈ W := by
    intro R hR v hv
    rw [hWdef, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec]
    have h10 : (M - μ • 1) * R = R * (M - μ • 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, hcomm R hR]
      congr 1
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
    rw [h10, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rcases hirr W hWinv with h | h
  · exact absurd h hWne
  · -- the eigenspace is everything: M = μ•1
    refine ⟨μ, ?_⟩
    have h11 : ∀ v : Fin d → ℝ, (M - μ • 1).mulVec v = 0 := by
      intro v
      have h12 : v ∈ W := by
        rw [h]
        exact Submodule.mem_top
      rw [hWdef, LinearMap.mem_ker, Matrix.mulVecLin_apply] at h12
      exact h12
    have h13 : M - μ • 1 = 0 := by
      ext i j
      have h14 := congrFun (h11 (Pi.single j 1)) i
      rw [Matrix.mulVec_single] at h14
      simpa using h14
    have h15 := sub_eq_zero.mp h13
    exact h15

/-- **Proposition `prop:symmetry-ellipticity`**: the second moment of
a finite positive invariant direction law, not supported at the
origin, is a positive multiple of the identity under an irreducible
orthogonal symmetry. -/
theorem symmetry_ellipticity [NeZero d] {ι : Type*} [Fintype ι]
    (S : Set (Matrix (Fin d) (Fin d) ℝ))
    (horth : ∀ R ∈ S, R * Rᵀ = 1)
    (hirr : ∀ W : Submodule ℝ (Fin d → ℝ),
      (∀ R ∈ S, ∀ v ∈ W, R.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (w : ι → ℝ) (v : ι → (Fin d → ℝ)) (hw : ∀ i, 0 ≤ w i)
    (hM : (∑ i, w i • vecMulVec (v i) (v i)).IsHermitian)
    (hinv : ∀ R ∈ S,
      R * (∑ i, w i • vecMulVec (v i) (v i)) * Rᵀ
        = ∑ i, w i • vecMulVec (v i) (v i))
    (hne : ∃ i, 0 < w i ∧ v i ≠ 0) :
    ∃ c : ℝ, 0 < c
      ∧ (∑ i, w i • vecMulVec (v i) (v i)) = c • 1 := by
  classical
  obtain ⟨c, hc⟩ := invariant_symm_eq_smul_one S horth hirr hM hinv
  refine ⟨c, ?_, hc⟩
  -- positivity: pair against a nonvanishing coordinate of an atom
  obtain ⟨i₀, hw₀, hv₀⟩ := hne
  obtain ⟨j₀, hj₀⟩ : ∃ j, v i₀ j ≠ 0 := by
    by_contra hall
    refine hv₀ (funext fun j => ?_)
    by_contra hj
    exact hall ⟨j, hj⟩
  -- the (j₀,j₀) entry of M is positive and equals c
  have h1 : (∑ i, w i • vecMulVec (v i) (v i)) j₀ j₀
      = ∑ i, w i * (v i j₀)^2 := by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    ring
  have h2 : 0 < ∑ i, w i * (v i j₀)^2 := by
    refine Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
      ⟨i₀, Finset.mem_univ i₀, ?_⟩
    exact mul_pos hw₀ (by positivity)
  have h3 : (∑ i, w i • vecMulVec (v i) (v i)) j₀ j₀ = c := by
    rw [hc, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one]
  rw [h1] at h3
  linarith [h2, h3.symm.le, h3.le]

end NCG
