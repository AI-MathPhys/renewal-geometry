/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Sector resolutions of a source Gram: the six-term
  source-word–transport–Hodge identity and the parallel
  signed certificate (`thm:GT-source-word-Hodge` and
  `thm:GRH-parallel-signed-certificate`,
  Gran-Tensor manuscript)

* `gt_sector_resolution`: for any finite resolution of the
  identity by pairwise-orthogonal hermitian idempotents
  `E_j` (`∑E_j = 1`), a source synthesis `W` splits
  exactly: the boxed
  `𝕂 = W*W = ∑_j W*E_jW` with every sector term PSD
  (`W*E_jW = (E_jW)*(E_jW)`), vanishing exactly when the
  sector annihilates the source.  With six sectors this is
  the boxed SC.4
  `𝕂_r = 𝕀_alg + 𝕀_hid + 𝕀_tr + G_dem + G_open + G_cyc`;
  with four it is the boxed GRH.3
  `N*N = 𝕀_{pair|R} + G_dem + G_open + G_cyc`.

* `gt_sector_domination_kernel`: the easy half of the
  domination criterion — if the last sectors are dominated
  by the physical action (`x*Ax ≤ c·x*Bx`), every kernel
  direction of `B` is a kernel direction of `A`
  (via the square-root support identification), which is
  the necessity of the boxed kernel-inclusion condition.

The identification of the six (resp. four) sectors with
the algebraic-word, hidden-record, transport, demand,
open-current and cycle projections (via the conditional
variance SK.3, `NCG.gt_source_record_variance`) is the
manuscript's construction; the sharp constant as the
largest generalized eigenvalue is its spectral layer.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedFintypeInType false in
/-- Exact sector resolution of a source Gram. -/
theorem gt_sector_resolution {n m : Type} [Fintype n]
    [Fintype m] [DecidableEq n] {k : ℕ}
    (E : Fin k → Matrix n n ℂ) (W : Matrix n m ℂ)
    (hres : ∑ j, E j = 1)
    (hH : ∀ j, (E j)ᴴ = E j)
    (hidem : ∀ j, E j * E j = E j) :
    -- the boxed exact decomposition
    (Wᴴ * W = ∑ j, Wᴴ * E j * W)
    -- every sector term is a PSD Gram
    ∧ (∀ j, Wᴴ * E j * W
        = (E j * W)ᴴ * (E j * W))
    ∧ (∀ j, (Wᴴ * E j * W).PosSemidef)
    -- a sector vanishes exactly when it annihilates the
    -- source
    ∧ (∀ j, Wᴴ * E j * W = 0 ↔ E j * W = 0) := by
  have hfact : ∀ j, Wᴴ * E j * W
      = (E j * W)ᴴ * (E j * W) := by
    intro j
    calc Wᴴ * E j * W
        = Wᴴ * ((E j * E j) * W) := by
          rw [hidem j, Matrix.mul_assoc]
      _ = (Wᴴ * (E j)ᴴ) * (E j * W) := by
          rw [hH j]
          simp only [Matrix.mul_assoc]
      _ = (E j * W)ᴴ * (E j * W) := by
          rw [Matrix.conjTranspose_mul]
  refine ⟨?_, hfact, ?_, ?_⟩
  · calc Wᴴ * W
        = Wᴴ * ((∑ j, E j) * W) := by
          rw [hres, Matrix.one_mul]
      _ = ∑ j, Wᴴ * E j * W := by
          rw [Matrix.sum_mul, Matrix.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by
            rw [Matrix.mul_assoc]
  · intro j
    rw [hfact j]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · intro j
    rw [hfact j]
    exact Matrix.conjTranspose_mul_self_eq_zero

set_option linter.unusedDecidableInType false in
/-- Domination forces kernel inclusion (the necessity half
of the boxed generalized-eigenvalue criterion). -/
theorem gt_sector_domination_kernel {n : Type} [Fintype n]
    [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (c : ℝ)
    (hdom : ∀ x : n → ℂ,
      (star x ⬝ᵥ (A *ᵥ x)).re
        ≤ c * (star x ⬝ᵥ (B *ᵥ x)).re) :
    ∀ x : n → ℂ, B *ᵥ x = 0 → A *ᵥ x = 0 := by
  intro x hx
  have hzero : (star x ⬝ᵥ (A *ᵥ x)).re = 0 := by
    have h1 := hdom x
    rw [hx] at h1
    simp only [dotProduct_zero, Complex.zero_re,
      mul_zero] at h1
    have h2 := hA.dotProduct_mulVec_nonneg x
    rw [Complex.le_def] at h2
    have h2re : (0:ℝ) ≤ (star x ⬝ᵥ (A *ᵥ x)).re := by
      simpa using h2.1
    exact le_antisymm h1 h2re
  -- PSD quadratic vanishing forces the kernel
  have hsq : CFC.sqrt A *ᵥ x = 0 := by
    have hAs : A = CFC.sqrt A * CFC.sqrt A :=
      (sqrt_mul_self_eq A hA).symm
    have hnorm : (star x ⬝ᵥ (A *ᵥ x)).re
        = ∑ i, Complex.normSq ((CFC.sqrt A *ᵥ x) i) := by
      conv_lhs => rw [hAs]
      rw [← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec,
        show star x ᵥ* CFC.sqrt A
          = star (CFC.sqrt A *ᵥ x) from by
        rw [Matrix.star_mulVec, sqrt_isHermitian]]
      rw [show star (CFC.sqrt A *ᵥ x)
          ⬝ᵥ (CFC.sqrt A *ᵥ x)
          = ∑ i, star ((CFC.sqrt A *ᵥ x) i)
            * (CFC.sqrt A *ᵥ x) i from rfl]
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, Complex.star_def, Complex.mul_conj]
      simp
    rw [hnorm] at hzero
    have hall : ∀ i, Complex.normSq
        ((CFC.sqrt A *ᵥ x) i) = 0 := by
      intro i
      have := Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Complex.normSq_nonneg _)
        |>.mp hzero i (Finset.mem_univ i)
      exact this
    funext i
    exact Complex.normSq_eq_zero.mp (hall i)
  have hAs : A = CFC.sqrt A * CFC.sqrt A :=
    (sqrt_mul_self_eq A hA).symm
  rw [hAs, ← Matrix.mulVec_mulVec, hsq,
    Matrix.mulVec_zero]

end NCG
