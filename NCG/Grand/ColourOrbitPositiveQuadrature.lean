/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ColourOrbitHaarExact
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Explicit positive colour-orbit quadrature

This file strengthens the finite clause of `thm:SM-colour-orbit`.  It constructs
five mutually unbiased bases in dimension four (the coordinate basis and four
Gaussian-integer phase bases), proves their projective second-moment identity,
and realizes every resulting colour matrix as an `SU(4)` conjugate of the seed.
The result is an equal-weight positive exact quadrature with 20 orbit points,
well below the manuscript's bound of 257.
-/

open Matrix Finset

namespace NCG.ColourOrbitPositiveQuadrature

abbrev GI := GaussianInt

def giI : GI := ⟨0, 1⟩
def signG : Fin 2 → GI := ![1, -1]

@[simp] theorem giI_toComplex : (giI : ℂ) = Complex.I := by
  apply Complex.ext <;> norm_num [giI, GaussianInt.toComplex_def₂]

def mubG (q : Fin 4) (s t : Fin 2) : Fin 4 → GI :=
  ![
    ![1, signG t, signG s, signG s * signG t],
    ![1, giI * signG t, giI * signG s, -(signG s * signG t)],
    ![1, giI * signG t, signG s, -(giI * signG s * signG t)],
    ![1, signG s, giI * signG t, -(giI * signG s * signG t)]
  ] q

def basisG (r : Fin 4) : Fin 4 → GI := fun i => if i = r then 1 else 0

theorem mubG_fourth_moment (i j k l : Fin 4) :
    (16 : GI) * (∑ r : Fin 4,
        star (basisG r i) * basisG r j * basisG r k * star (basisG r l))
      + (∑ q : Fin 4, ∑ s : Fin 2, ∑ t : Fin 2,
        star (mubG q s t i) * mubG q s t j *
          mubG q s t k * star (mubG q s t l))
      = (16 : GI) * ((if i = j ∧ k = l then (1 : GI) else 0)
          + (if i = k ∧ j = l then (1 : GI) else 0)) := by
  decide +revert

noncomputable def mubVector (q : Fin 4) (s t : Fin 2) : Fin 4 → ℂ :=
  fun i => (mubG q s t i : ℂ) / 2

def basisVector (r : Fin 4) : Fin 4 → ℂ :=
  fun i => (basisG r i : ℂ)

theorem mub_term_eq (q : Fin 4) (s t : Fin 2) (i j k l : Fin 4) :
    star (mubVector q s t i) * mubVector q s t j *
        mubVector q s t k * star (mubVector q s t l)
      = ((star (mubG q s t i) * mubG q s t j *
          mubG q s t k * star (mubG q s t l) : GI) : ℂ) / 16 := by
  simp [mubVector, GaussianInt.toComplex_mul, GaussianInt.toComplex_star]
  ring

theorem basis_term_eq (r : Fin 4) (i j k l : Fin 4) :
    star (basisVector r i) * basisVector r j *
        basisVector r k * star (basisVector r l)
      = ((star (basisG r i) * basisG r j *
          basisG r k * star (basisG r l) : GI) : ℂ) := by
  simp [basisVector, GaussianInt.toComplex_mul, GaussianInt.toComplex_star]

theorem mub_fourth_moment (i j k l : Fin 4) :
    (∑ r : Fin 4,
        star (basisVector r i) * basisVector r j *
          basisVector r k * star (basisVector r l))
      + (∑ q : Fin 4, ∑ s : Fin 2, ∑ t : Fin 2,
        star (mubVector q s t i) * mubVector q s t j *
          mubVector q s t k * star (mubVector q s t l))
      = (if i = j ∧ k = l then (1 : ℂ) else 0)
          + (if i = k ∧ j = l then (1 : ℂ) else 0) := by
  simp_rw [mub_term_eq, basis_term_eq]
  have h := congrArg (fun z : GI => (z : ℂ)) (mubG_fourth_moment i j k l)
  simp only [GaussianInt.toComplex_add, GaussianInt.toComplex_mul,
    map_sum] at h
  norm_num only [map_ofNat, map_one, map_zero] at h
  have hdiv :
      (∑ q : Fin 4, ∑ s : Fin 2, ∑ t : Fin 2,
        ((star (mubG q s t i) * mubG q s t j *
          mubG q s t k * star (mubG q s t l) : GI) : ℂ)) / 16
        = ∑ q : Fin 4, ∑ s : Fin 2, ∑ t : Fin 2,
          ((star (mubG q s t i) * mubG q s t j *
            mubG q s t k * star (mubG q s t l) : GI) : ℂ) / 16 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _hs
    rw [Finset.sum_div]
  rw [← hdiv]
  simp only [GaussianInt.toComplex_mul, GaussianInt.toComplex_star] at h ⊢
  split_ifs at h ⊢ <;> norm_num at h ⊢ <;> linear_combination h / 16

abbrev M4 := Matrix (Fin 4) (Fin 4) ℂ

def pureProjection (v : Fin 4 → ℂ) : M4 := fun i j => v i * star (v j)

noncomputable def rawMoment (i j k l : Fin 4) : ℂ :=
  (∑ r : Fin 4,
      star (basisVector r i) * basisVector r j *
        basisVector r k * star (basisVector r l))
    + (∑ q : Fin 4, ∑ s : Fin 2, ∑ t : Fin 2,
      star (mubVector q s t i) * mubVector q s t j *
        mubVector q s t k * star (mubVector q s t l))

theorem rawMoment_exact (i j k l : Fin 4) :
    rawMoment i j k l =
      (if i = j ∧ k = l then (1 : ℂ) else 0)
        + (if i = k ∧ j = l then (1 : ℂ) else 0) :=
  mub_fourth_moment i j k l

noncomputable def projectionMomentAverage (A : M4) : M4 := fun k l =>
  (1 / 20 : ℂ) * ∑ i : Fin 4, ∑ j : Fin 4, A j i * rawMoment j i k l

theorem projectionMomentAverage_exact (A : M4) :
    projectionMomentAverage A = (1 / 20 : ℂ) • (A + Matrix.trace A • 1) := by
  ext k l
  rw [projectionMomentAverage]
  simp_rw [rawMoment_exact]
  fin_cases k <;> fin_cases l <;>
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ] <;> ring

noncomputable def projectionOrbitAverage (A : M4) : M4 :=
  (1 / 20 : ℂ) •
    ((∑ r : Fin 4,
        Matrix.trace (pureProjection (basisVector r) * A) •
          pureProjection (basisVector r))
      + (∑ q : Fin 4, ∑ s : Fin 2, ∑ t : Fin 2,
        Matrix.trace (pureProjection (mubVector q s t) * A) •
          pureProjection (mubVector q s t)))

set_option maxHeartbeats 1000000 in
-- Expanding the fixed twenty-vector moment requires a large finite normalization.
theorem projectionOrbitAverage_eq_moment (A : M4) :
    projectionOrbitAverage A = projectionMomentAverage A := by
  ext k l
  simp only [projectionOrbitAverage, projectionMomentAverage, Matrix.smul_apply,
    Matrix.add_apply, Matrix.sum_apply, smul_eq_mul, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, pureProjection, rawMoment]
  simp (config := { maxSteps := 1000000 }) only [Fin.sum_univ_succ]
  ring

theorem projectionOrbitAverage_exact (A : M4) :
    projectionOrbitAverage A = (1 / 20 : ℂ) • (A + Matrix.trace A • 1) := by
  rw [projectionOrbitAverage_eq_moment, projectionMomentAverage_exact]

theorem pureProjection_star (v : Fin 4 → ℂ) :
    star (pureProjection v) = pureProjection v := by
  ext i j
  simp [pureProjection, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, mul_comm]

theorem basisProjection_trace (r : Fin 4) :
    Matrix.trace (pureProjection (basisVector r)) = 1 := by
  fin_cases r <;>
    simp [Matrix.trace, Matrix.diag_apply, pureProjection, basisVector,
      basisG, Fin.sum_univ_succ]

theorem mubProjection_trace (q : Fin 4) (s t : Fin 2) :
    Matrix.trace (pureProjection (mubVector q s t)) = 1 := by
  fin_cases q <;> fin_cases s <;> fin_cases t <;>
    simp [Matrix.trace, Matrix.diag_apply, pureProjection, mubVector,
      mubG, signG, Fin.sum_univ_succ] <;>
    apply Complex.ext <;> norm_num

noncomputable def projectionMean : M4 :=
  (1 / 20 : ℂ) •
    ((∑ r : Fin 4, pureProjection (basisVector r))
      + ∑ q : Fin 4, ∑ s : Fin 2, ∑ t : Fin 2,
        pureProjection (mubVector q s t))

theorem projectionMean_eq : projectionMean = (1 / 4 : ℂ) • (1 : M4) := by
  calc
    projectionMean = projectionOrbitAverage (1 : M4) := by
      ext i j
      simp only [projectionMean, projectionOrbitAverage, Matrix.smul_apply,
        Matrix.add_apply, Matrix.sum_apply]
      simp_rw [Matrix.mul_one, basisProjection_trace, mubProjection_trace,
        one_smul]
    _ = (1 / 20 : ℂ) • ((1 : M4) + Matrix.trace (1 : M4) • 1) :=
      projectionOrbitAverage_exact 1
    _ = (1 / 4 : ℂ) • (1 : M4) := by
      rw [Matrix.trace_one]
      norm_num
      module

noncomputable def projectionCoefficientAverage (A : M4) : ℂ :=
  (1 / 20 : ℂ) *
    ((∑ r : Fin 4, Matrix.trace (pureProjection (basisVector r) * A))
      + ∑ q : Fin 4, ∑ s : Fin 2, ∑ t : Fin 2,
        Matrix.trace (pureProjection (mubVector q s t) * A))

theorem projectionCoefficientAverage_eq (A : M4) :
    projectionCoefficientAverage A = Matrix.trace A / 4 := by
  have ht := congrArg Matrix.trace (projectionOrbitAverage_exact A)
  simp only [projectionOrbitAverage, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, basisProjection_trace,
    mubProjection_trace, mul_one] at ht
  rw [projectionCoefficientAverage]
  rw [Matrix.trace_one] at ht
  norm_num at ht ⊢
  linear_combination ht / 20

def colourFromProjection (P : M4) : M4 := (2 : ℂ) • P - 1

noncomputable def colourOrbitAverage (A : M4) : M4 :=
  (1 / 20 : ℂ) •
    ((∑ r : Fin 4,
        Matrix.trace (star (colourFromProjection (pureProjection (basisVector r))) * A) •
          colourFromProjection (pureProjection (basisVector r)))
      + ∑ q : Fin 4, ∑ s : Fin 2, ∑ t : Fin 2,
        Matrix.trace (star (colourFromProjection (pureProjection (mubVector q s t))) * A) •
          colourFromProjection (pureProjection (mubVector q s t)))

set_option maxHeartbeats 1000000 in
-- This expands the finite projective moment identity entry by entry.
theorem colourOrbitAverage_expand (A : M4) :
    colourOrbitAverage A =
      (4 : ℂ) • projectionOrbitAverage A
        - (2 * Matrix.trace A) • projectionMean
        - (2 * projectionCoefficientAverage A) • (1 : M4)
        + Matrix.trace A • (1 : M4) := by
  ext i j
  simp only [colourOrbitAverage, colourFromProjection, pureProjection_star,
    star_sub, star_smul, star_one, map_ofNat, projectionOrbitAverage,
    projectionMean, projectionCoefficientAverage, Matrix.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply, smul_eq_mul,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.one_mul]
  simp (config := { maxSteps := 1000000 }) only [Fin.sum_univ_succ]
  simp only [star_ofNat]
  ring

theorem colourOrbitAverage_exact (A : M4) :
    colourOrbitAverage A = (Matrix.trace A / 4) • 1
      + (5⁻¹ : ℂ) • (A - (Matrix.trace A / 4) • 1) := by
  rw [colourOrbitAverage_expand, projectionOrbitAverage_exact,
    projectionMean_eq, projectionCoefficientAverage_eq]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    smul_eq_mul]
  ring

def pairFirst : Fin 4 → Fin 2 := ![0, 0, 1, 1]
def pairSecond : Fin 4 → Fin 2 := ![0, 1, 0, 1]
def pairIndex (s t : Fin 2) : Fin 4 := ![![0, 1], ![2, 3]] s t

/-- The four MUB vectors in family `q`, placed as the columns of a matrix. -/
noncomputable def mubUnitary (q : Fin 4) : M4 := fun i r =>
  mubVector q (pairFirst r) (pairSecond r) i

set_option maxHeartbeats 1000000 in
-- The four explicit Gaussian phase matrices are checked entrywise.
theorem mubUnitary_mem (q : Fin 4) :
    mubUnitary q ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases q <;> fin_cases i <;> fin_cases j <;>
    simp [mubUnitary, mubVector, mubG, pairFirst, pairSecond, signG,
      Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;>
    apply Complex.ext <;> norm_num

theorem basisProjection_eq_swap_conjugate (r : Fin 4) :
    pureProjection (basisVector r) =
      Matrix.swap ℂ 0 r * NCG.lepP * star (Matrix.swap ℂ 0 r) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_swap]
  ext i j
  rw [NCG.ConjIrreducible.swap_conj_apply]
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    simp [pureProjection, basisVector, basisG, NCG.lepP,
      Equiv.swap_apply_def]

set_option maxHeartbeats 1000000 in
-- The rank-one conjugation identity is a fixed four-by-four calculation.
theorem mubProjection_eq_conjugate (q : Fin 4) (s t : Fin 2) :
    pureProjection (mubVector q s t) =
      mubUnitary q * pureProjection
        (basisVector (pairIndex s t)) *
          star (mubUnitary q) := by
  ext i j
  fin_cases q <;> fin_cases s <;> fin_cases t <;>
    fin_cases i <;> fin_cases j <;>
    simp [pureProjection, basisVector, basisG, mubUnitary, mubVector,
      mubG, pairFirst, pairSecond, pairIndex, signG, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
    apply Complex.ext <;> norm_num

theorem conjugate_colourFromProjection (U P : M4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    U * colourFromProjection P * star U =
      colourFromProjection (U * P * star U) := by
  simp [colourFromProjection, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mem_unitaryGroup_iff.mp hU]

theorem basisColour_unitary_conjugate (r : Fin 4) :
    Matrix.swap ℂ 0 r * NCG.colourR * star (Matrix.swap ℂ 0 r) =
      colourFromProjection (pureProjection (basisVector r)) := by
  have hU := NCG.ConjIrreducible.swap_mem (n := Fin 4) 0 r
  rw [NCG.colourR_from_projection]
  change Matrix.swap ℂ 0 r * colourFromProjection NCG.lepP *
    star (Matrix.swap ℂ 0 r) = _
  rw [conjugate_colourFromProjection _ _ hU,
    ← basisProjection_eq_swap_conjugate]

theorem basisColour_orbit (r : Fin 4) :
    ∃ V : NCG.CompactHaarRankOneAverage.SU4,
      V.1 * NCG.colourR * star V.1 =
        colourFromProjection (pureProjection (basisVector r)) := by
  let U : M4 := Matrix.swap ℂ 0 r
  have hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    NCG.ConjIrreducible.swap_mem 0 r
  obtain ⟨V, hV⟩ :=
    NCG.ColourOrbitHaarExact.unitary_conjugation_represented_in_SU4 U hU
  refine ⟨V, (hV NCG.colourR).trans ?_⟩
  exact basisColour_unitary_conjugate r

theorem mubColour_orbit (q : Fin 4) (s t : Fin 2) :
    ∃ V : NCG.CompactHaarRankOneAverage.SU4,
      V.1 * NCG.colourR * star V.1 =
        colourFromProjection (pureProjection (mubVector q s t)) := by
  let S : M4 := Matrix.swap ℂ 0 (pairIndex s t)
  let U : M4 := mubUnitary q * S
  have hS : S ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    NCG.ConjIrreducible.swap_mem 0 (pairIndex s t)
  have hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    (Matrix.unitaryGroup (Fin 4) ℂ).mul_mem (mubUnitary_mem q) hS
  have hconj : U * NCG.colourR * star U =
      colourFromProjection (pureProjection (mubVector q s t)) := by
    rw [show U * NCG.colourR * star U =
        mubUnitary q * (S * NCG.colourR * star S) * star (mubUnitary q) by
      simp only [U, star_mul]
      noncomm_ring]
    rw [show S * NCG.colourR * star S =
        colourFromProjection (pureProjection (basisVector (pairIndex s t))) by
      exact basisColour_unitary_conjugate (pairIndex s t)]
    rw [conjugate_colourFromProjection _ _ (mubUnitary_mem q),
      ← mubProjection_eq_conjugate]
  obtain ⟨V, hV⟩ :=
    NCG.ColourOrbitHaarExact.unitary_conjugation_represented_in_SU4 U hU
  exact ⟨V, (hV NCG.colourR).trans hconj⟩

noncomputable def basisSU (r : Fin 4) :
    NCG.CompactHaarRankOneAverage.SU4 := (basisColour_orbit r).choose

theorem basisSU_spec (r : Fin 4) :
    (basisSU r).1 * NCG.colourR * star (basisSU r).1 =
      colourFromProjection (pureProjection (basisVector r)) :=
  (basisColour_orbit r).choose_spec

noncomputable def mubSU (q : Fin 4) (s t : Fin 2) :
    NCG.CompactHaarRankOneAverage.SU4 := (mubColour_orbit q s t).choose

theorem mubSU_spec (q : Fin 4) (s t : Fin 2) :
    (mubSU q s t).1 * NCG.colourR * star (mubSU q s t).1 =
      colourFromProjection (pureProjection (mubVector q s t)) :=
  (mubColour_orbit q s t).choose_spec

/-- A 20-point equal-weight exact positive `SU(4)` orbit quadrature for the
actual colour Haar covariance. -/
theorem colourHaar_twenty_point_quadrature (A : M4) :
    NCG.ColourOrbitHaarExact.colourHaarMatrix A =
      (1 / 20 : ℂ) •
        ((∑ r : Fin 4,
            Matrix.trace
                (star ((basisSU r).1 * NCG.colourR * star (basisSU r).1) * A) •
              ((basisSU r).1 * NCG.colourR * star (basisSU r).1))
          + ∑ q : Fin 4, ∑ s : Fin 2, ∑ t : Fin 2,
            Matrix.trace
                (star ((mubSU q s t).1 * NCG.colourR * star (mubSU q s t).1) * A) •
              ((mubSU q s t).1 * NCG.colourR * star (mubSU q s t).1)) := by
  rw [NCG.ColourOrbitHaarExact.colourHaarMatrix_exact,
    ← colourOrbitAverage_exact]
  simp_rw [basisSU_spec, mubSU_spec]
  rfl

theorem twenty_point_weights_positive : (0 : ℝ) < 1 / 20 := by norm_num

theorem twenty_point_weights_sum_one :
    (∑ _r : Fin 4, (1 / 20 : ℝ))
      + (∑ _q : Fin 4, ∑ _s : Fin 2, ∑ _t : Fin 2, (1 / 20 : ℝ)) = 1 := by
  norm_num

theorem twenty_points_le_manuscript_bound : 4 + 4 * 2 * 2 ≤ 257 := by norm_num

end NCG.ColourOrbitPositiveQuadrature
