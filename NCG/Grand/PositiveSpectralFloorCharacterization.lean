/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpacetimeFrame
import NCG.Grand.FiniteCommutantPoincareGap

/-!
# Positive spectral floors and source-frame noncollapse

This file completes the spectral interpretation of
`thm:SMST-spacetime-frame`.  For a finite positive semidefinite block, the
order-theoretic certificate `A² - cA ⪰ 0` is proved equivalent to saying that
every positive eigenvalue of `A` is at least `c`.  Thus the floor hypothesis
used by `smst_spacetime_frame` is exactly the manuscript's
least-positive-eigenvalue hypothesis.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

open Upstream.PrimitiveWeight

/-- The order certificate `A²-cA ⪰ 0` is exactly a lower bound `c` on every
nonzero eigenvalue of a positive semidefinite Hermitian matrix. -/
theorem positiveSpectralFloor_iff
    {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ)
    (c : ℝ) (hA : A.PosSemidef) :
    (A * A - (c : ℂ) • A).PosSemidef ↔
      ∀ i : Fin r, hA.1.eigenvalues i = 0 ∨ c ≤ hA.1.eigenvalues i := by
  constructor
  · intro hfloor i
    let v : Fin r → ℂ := ⇑(hA.1.eigenvectorBasis i)
    have hv := hA.1.mulVec_eigenvectorBasis i
    have hnon := hfloor.re_dotProduct_nonneg v
    have hvnorm : star v ⬝ᵥ v = 1 := by
      dsimp [v]
      rw [dotProduct_comm,
        ← EuclideanSpace.inner_eq_star_dotProduct,
        @inner_self_eq_norm_sq_to_K ℂ,
        hA.1.eigenvectorBasis.orthonormal.1 i]
      norm_num
    have hMv : (A * A - (c : ℂ) • A) *ᵥ v =
        ((hA.1.eigenvalues i * hA.1.eigenvalues i -
          c * hA.1.eigenvalues i : ℝ) • v) := by
      rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_smul, hv, Matrix.smul_mulVec, hv]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
        smul_smul, sub_smul, map_mul, map_sub]
      rfl
    rw [hMv, dotProduct_smul, hvnorm] at hnon
    have hnonReal : 0 ≤ hA.1.eigenvalues i * hA.1.eigenvalues i -
        c * hA.1.eigenvalues i := by
      simpa using hnon
    have hlam : 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg i
    by_cases hz : hA.1.eigenvalues i = 0
    · exact Or.inl hz
    · right
      have hpos : 0 < hA.1.eigenvalues i := lt_of_le_of_ne hlam (Ne.symm hz)
      nlinarith [hnonReal, hpos]
  · intro hspec
    have heq : A * A - (c : ℂ) • A =
        hA.1.cfc (fun x : ℝ => x * x - c * x) := by
      calc
        A * A - (c : ℂ) • A =
            hA.1.cfc id * hA.1.cfc id -
              hA.1.cfc (fun _ : ℝ => c) * hA.1.cfc id := by
                rw [cfc_id' hA.1, cfc_const hA.1,
                  Matrix.smul_mul, Matrix.one_mul]
                rfl
        _ = hA.1.cfc (fun x : ℝ => x * x) -
              hA.1.cfc (fun x : ℝ => c * x) := by
                rw [cfc_mul hA.1, cfc_mul hA.1]
                rfl
        _ = hA.1.cfc (fun x : ℝ => x * x - c * x) := by
                rw [cfc_sub hA.1]
    rw [heq]
    refine cfc_posSemidef hA.1 fun i => ?_
    rcases hspec i with hz | hci
    · rw [hz]
      simp
    · nlinarith [hA.eigenvalues_nonneg i]

/-- Exact bridge used by the structured spacetime frame theorem: a uniform
least-positive-eigenvalue bound supplies precisely its order-theoretic floor
hypothesis. -/
theorem leastPositiveEigenvalueBound_implies_sourceFrameFloor
    {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ)
    (c : ℝ) (hA : A.PosSemidef)
    (hspec : ∀ i : Fin r,
      hA.1.eigenvalues i = 0 ∨ c ≤ hA.1.eigenvalues i) :
    (A * A - (c : ℂ) • A).PosSemidef :=
  (positiveSpectralFloor_iff A c hA).2 hspec

end NCG
