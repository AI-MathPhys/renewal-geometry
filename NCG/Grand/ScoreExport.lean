/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Operational score export and the unread-refinement law
  (`thm:operational-score-export`, Gran-Tensor manuscript)

* `fisherBlock`: the weighted score Gram
  `𝕀_{ij} = Σ_x p(x)·conj(s_i(x))·s_j(x)`.
* `fisher_posSemidef`: the joint Fisher block is positive
  semidefinite (it is the Gram of the score syntheses).
* `operational_score_export`: for a coarse-graining
  `c : Ω → Ω_c` with conditional-expectation scores
  `s_c = 𝔼[s_f | R_c]`, the boxed covariance Pythagoras
  `𝕀_f = 𝕀_c + 𝔼[(s_f - s_c)(s_f - s_c)*]` holds, both blocks
  and the innovation block are positive, and genuinely unread
  refinements contribute zero innovation.

Rendering disclosed: the score families are rendered as declared
finite families with the conditional-expectation identity as the
coarse-score hypothesis (it follows from differentiating the
fibre-summed probability in the manuscript's smooth-model layer);
the nuisance-projection clause is
`thm:simultaneous-nuisance-short`.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- The weighted score Gram (joint Fisher block). -/
noncomputable def fisherBlock {Om idx : Type*} [Fintype Om]
    (p : Om → ℝ) (s : idx → Om → ℂ) : Matrix idx idx ℂ :=
  Matrix.of fun i j =>
    ∑ x, (p x : ℂ) * (starRingEnd ℂ) (s i x) * s j x

/-- The Fisher block is the Gram of the score syntheses, hence
positive semidefinite. -/
theorem fisher_posSemidef {Om idx : Type*} [Fintype Om]
    [Finite idx] (p : Om → ℝ) (s : idx → Om → ℂ)
    (hp : ∀ x, 0 ≤ p x) : (fisherBlock p s).PosSemidef := by
  classical
  have hDA : Matrix.diagonal (fun x => (p x : ℂ))
      * Matrix.of (fun (x : Om) (i : idx) => s i x)
      = Matrix.of fun (x : Om) (i : idx) =>
          (p x : ℂ) * s i x := by
    ext x i
    rw [Matrix.diagonal_mul, Matrix.of_apply, Matrix.of_apply]
  have hfact : fisherBlock p s
      = (Matrix.of fun (x : Om) (i : idx) => s i x)ᴴ
        * (Matrix.diagonal (fun x => (p x : ℂ))
          * Matrix.of fun (x : Om) (i : idx) => s i x) := by
    rw [hDA]
    ext i j
    simp only [fisherBlock, Matrix.of_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.star_def]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hfact, ← Matrix.mul_assoc]
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same
    (Matrix.posSemidef_diagonal_iff.mpr fun x => by
      exact_mod_cast hp x) _

/-- `thm:operational-score-export`: Fisher positivity, the
coarse/innovation Pythagoras, innovation positivity, and the
unread-refinement law. -/
theorem operational_score_export {Om Omc idx : Type*}
    [Fintype Om] [Fintype Omc] [DecidableEq Omc] [Finite idx]
    (p : Om → ℝ) (hp : ∀ x, 0 ≤ p x)
    (s : idx → Om → ℂ) (c : Om → Omc)
    (pc : Omc → ℝ)
    (hpc : ∀ y, pc y
      = ∑ x ∈ Finset.univ.filter (fun x => c x = y), p x)
    (hpcpos : ∀ y, pc y ≠ 0)
    (sc : idx → Omc → ℂ)
    (hsc : ∀ i y, sc i y = (pc y : ℂ)⁻¹
      * ∑ x ∈ Finset.univ.filter (fun x => c x = y),
          (p x : ℂ) * s i x) :
    (fisherBlock p s).PosSemidef
    ∧ (fisherBlock pc sc).PosSemidef
    ∧ (fisherBlock p s = fisherBlock pc sc
        + fisherBlock p (fun i x => s i x - sc i (c x)))
    ∧ (fisherBlock p (fun i x => s i x - sc i (c x))).PosSemidef
    ∧ ((∀ i x, s i x = sc i (c x)) →
        fisherBlock p s = fisherBlock pc sc) := by
  have hpcnn : ∀ y, 0 ≤ pc y := by
    intro y
    rw [hpc]
    exact Finset.sum_nonneg fun x _ => hp x
  have hfib : ∀ (i : idx) (y : Omc),
      ∑ x ∈ Finset.univ.filter (fun x => c x = y),
        (p x : ℂ) * s i x = (pc y : ℂ) * sc i y := by
    intro i y
    have hpcy : (pc y : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hpcpos y)
    rw [hsc]
    field_simp
  have hfibconj : ∀ (i : idx) (y : Omc),
      ∑ x ∈ Finset.univ.filter (fun x => c x = y),
        (p x : ℂ) * (starRingEnd ℂ) (s i x)
      = (pc y : ℂ) * (starRingEnd ℂ) (sc i y) := by
    intro i y
    have h := congrArg (starRingEnd ℂ) (hfib i y)
    simpa [map_sum, map_mul, Complex.conj_ofReal] using h
  have hfibconst : ∀ y : Omc,
      ∑ x ∈ Finset.univ.filter (fun x => c x = y), (p x : ℂ)
      = (pc y : ℂ) := by
    intro y
    rw [hpc]
    norm_cast
  have hkey : ∀ i j : idx,
      ∑ x, (p x : ℂ)
          * (starRingEnd ℂ) (s i x - sc i (c x))
          * (s j x - sc j (c x))
      = (∑ x, (p x : ℂ) * (starRingEnd ℂ) (s i x) * s j x)
        - ∑ y, (pc y : ℂ) * (starRingEnd ℂ) (sc i y)
            * sc j y := by
    intro i j
    rw [← Finset.sum_fiberwise Finset.univ c
      (fun x => (p x : ℂ) * (starRingEnd ℂ) (s i x) * s j x)]
    rw [← Finset.sum_fiberwise Finset.univ c
      (fun x => (p x : ℂ)
        * (starRingEnd ℂ) (s i x - sc i (c x))
        * (s j x - sc j (c x)))]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hrw : ∀ x ∈ Finset.univ.filter (fun x => c x = y),
        (p x : ℂ) * (starRingEnd ℂ) (s i x - sc i (c x))
          * (s j x - sc j (c x))
        = (p x : ℂ) * (starRingEnd ℂ) (s i x) * s j x
          - ((p x : ℂ) * (starRingEnd ℂ) (s i x)) * sc j y
          - ((p x : ℂ) * s j x) * (starRingEnd ℂ) (sc i y)
          + (p x : ℂ)
            * ((starRingEnd ℂ) (sc i y) * sc j y) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hx.2, map_sub]
      ring
    rw [Finset.sum_congr rfl hrw]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hfibconj i y]
    rw [show (∑ x ∈ Finset.univ.filter (fun x => c x = y),
        ((p x : ℂ) * s j x) * (starRingEnd ℂ) (sc i y))
        = (∑ x ∈ Finset.univ.filter (fun x => c x = y),
            (p x : ℂ) * s j x) * (starRingEnd ℂ) (sc i y) from
      (Finset.sum_mul _ _ _).symm]
    rw [hfib j y]
    rw [← Finset.sum_mul, hfibconst y]
    ring
  have hpyth : fisherBlock p s = fisherBlock pc sc
      + fisherBlock p (fun i x => s i x - sc i (c x)) := by
    ext i j
    have h := hkey i j
    simp only [fisherBlock, Matrix.of_apply, Matrix.add_apply]
    linear_combination -h
  refine ⟨fisher_posSemidef p s hp,
    fisher_posSemidef pc sc hpcnn, hpyth,
    fisher_posSemidef p _ hp, ?_⟩
  intro hconst
  have h0 : fisherBlock p (fun i x => s i x - sc i (c x))
      = 0 := by
    ext i j
    simp [fisherBlock, hconst]
  rw [hpyth, h0, add_zero]

end NCG
