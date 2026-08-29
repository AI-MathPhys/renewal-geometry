/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExteriorPowerOperatorNormBoundsExact
import NCG.Upstream.PrimitiveWeight

/-!
# Robust reflected positivity from an approximate covariance

This module formalizes the four alternatives of
thm:SMQG-robust-positivity: a strict approximate spectral floor certifies
positive definiteness, a sufficiently negative bottom eigenvalue supplies an
explicit negative grade-one word, the unresolved interval supplies a soft
eigenvector, and every exterior grade inherits the sharp perturbation bound.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG
namespace RobustReflectedPositivity

open ExteriorPowerOperatorNormBounds
open FiniteCompoundMatrixExteriorPower

variable {d : ℕ}

/-- Subtracting a lower spectral bound from a Hermitian matrix leaves a
positive-semidefinite matrix. -/
theorem sub_spectral_floor_posSemidef
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (a : ℝ)
    (ha : ∀ i, a ≤ hA.eigenvalues i) :
    (A - (a : ℂ) • 1).PosSemidef := by
  have heq : A - (a : ℂ) • 1 =
      hA.cfc fun x => x - a := by
    have h := Upstream.PrimitiveWeight.cfc_sub hA id (fun _ => a)
    rw [Upstream.PrimitiveWeight.cfc_id',
      Upstream.PrimitiveWeight.cfc_const] at h
    exact h
  rw [heq]
  exact Upstream.PrimitiveWeight.cfc_posSemidef hA fun i =>
    sub_nonneg.mpr (ha i)

/-- An operator-norm error bound on a Hermitian perturbation gives both
Loewner bounds -εI ≤ D ≤ εI. -/
theorem hermitian_norm_bound_gives_order_interval
    (D : Matrix (Fin d) (Fin d) ℂ) (hD : D.IsHermitian)
    (ε : ℝ) (hε : 0 ≤ ε) (hDnorm : ‖D‖ ≤ ε) :
    (D + (ε : ℂ) • 1).PosSemidef ∧
      (-D + (ε : ℂ) • 1).PosSemidef := by
  have hlower : ∀ i, -ε ≤ hD.eigenvalues i := by
    intro i
    have habs : |hD.eigenvalues i| ≤ ε := by
      have hspec := hermitian_eigenvalue_norm_le D hD i
      have : |hD.eigenvalues i| ≤ ‖D‖ := by
        simpa [Real.norm_eq_abs] using hspec
      exact this.trans hDnorm
    exact (abs_le.mp habs).1
  have hnegD : (-D).IsHermitian := hD.neg
  have hupper : ∀ i, -ε ≤ hnegD.eigenvalues i := by
    intro i
    have hnegNorm : ‖-D‖ ≤ ε := by simpa using hDnorm
    have hspec := hermitian_eigenvalue_norm_le (-D) hnegD i
    have habs : |hnegD.eigenvalues i| ≤ ε := by
      have : |hnegD.eigenvalues i| ≤ ‖-D‖ := by
        simpa [Real.norm_eq_abs] using hspec
      exact this.trans hnegNorm
    exact (abs_le.mp habs).1
  constructor
  · simpa [sub_eq_add_neg] using
      sub_spectral_floor_posSemidef D hD (-ε) hlower
  · simpa [sub_eq_add_neg] using
      sub_spectral_floor_posSemidef (-D) hnegD (-ε) hupper

/-- A strict spectral floor of the approximation, separated from the
operator-norm error, certifies positive definiteness of the exact covariance.
-/
theorem posDef_of_approximate_min_gt_error
    (P Ptilde : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hPt : Ptilde.IsHermitian)
    (ε lam : ℝ) (hε : 0 ≤ ε)
    (hclose : ‖Ptilde - P‖ ≤ ε)
    (hmin : ∀ i, lam ≤ hPt.eigenvalues i)
    (hgap : ε < lam) :
    P.PosDef := by
  let D := P - Ptilde
  have hD : D.IsHermitian := hP.sub hPt
  have hDnorm : ‖D‖ ≤ ε := by
    simpa [D, norm_sub_rev] using hclose
  have hDlo := (hermitian_norm_bound_gives_order_interval
    D hD ε hε hDnorm).1
  have hPtlo := sub_spectral_floor_posSemidef Ptilde hPt lam hmin
  have hscalar : (((lam - ε : ℝ) : ℂ) •
      (1 : Matrix (Fin d) (Fin d) ℂ)).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one (by
      simpa using
        (RCLike.ofReal_pos (K := ℂ)).mpr (sub_pos.mpr hgap))
  have hsum : (((lam - ε : ℝ) : ℂ) •
        (1 : Matrix (Fin d) (Fin d) ℂ)
      + (Ptilde - (lam : ℂ) • 1)
      + (D + (ε : ℂ) • 1)).PosDef :=
    (hscalar.add_posSemidef hPtlo).add_posSemidef hDlo
  convert hsum using 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [D]
  · simp [D, Matrix.one_apply_ne hij]

/-- A bottom eigenvalue below the negative error threshold gives its normalized
eigenvector as an explicit negative grade-one reflected word for the exact
covariance. -/
theorem bottom_eigenvector_negative_of_lt_neg_error
    (P Ptilde : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hPt : Ptilde.IsHermitian)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hclose : ‖Ptilde - P‖ ≤ ε) (i0 : Fin d)
    (hneg : hPt.eigenvalues i0 < -ε) :
    let v : Fin d → ℂ := ⇑(hPt.eigenvectorBasis i0)
    Ptilde *ᵥ v = (hPt.eigenvalues i0 : ℂ) • v ∧
      star v ⬝ᵥ v = 1 ∧
      (star v ⬝ᵥ (P *ᵥ v)).re < 0 := by
  let v : Fin d → ℂ := ⇑(hPt.eigenvectorBasis i0)
  let D := P - Ptilde
  have hD : D.IsHermitian := hP.sub hPt
  have hDnorm : ‖D‖ ≤ ε := by
    simpa [D, norm_sub_rev] using hclose
  have hDupper := (hermitian_norm_bound_gives_order_interval
    D hD ε hε hDnorm).2
  have hvinner : star v ⬝ᵥ v = 1 := by
    dsimp [v]
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      @inner_self_eq_norm_sq_to_K ℂ,
      hPt.eigenvectorBasis.orthonormal.1 i0]
    norm_num
  have hDquad : (star v ⬝ᵥ (D *ᵥ v)).re ≤ ε := by
    have hq := hDupper.re_dotProduct_nonneg v
    rw [Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_add, dotProduct_neg,
      dotProduct_smul, hvinner] at hq
    norm_num at hq ⊢
    linarith
  have hPquad :
      (star v ⬝ᵥ (P *ᵥ v)).re =
        hPt.eigenvalues i0 + (star v ⬝ᵥ (D *ᵥ v)).re := by
    have heigquad :
        (star v ⬝ᵥ (Ptilde *ᵥ v)).re =
          hPt.eigenvalues i0 := by
      dsimp [v]
      exact (hPt.eigenvalues_eq i0).symm
    have hsplit : P = Ptilde + D := by
      simp [D]
    rw [hsplit, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
    rw [heigquad]
  refine ⟨?_, hvinner, ?_⟩
  · simpa [v] using hPt.mulVec_eigenvectorBasis i0
  · rw [hPquad]
    linarith

/-- If neither strict sign test succeeds, the same normalized bottom
eigenvector is returned with eigenvalue inside the uncertainty window. -/
theorem bottom_eigenvector_soft_of_unresolved
    (Ptilde : Matrix (Fin d) (Fin d) ℂ)
    (hPt : Ptilde.IsHermitian) (ε : ℝ) (i0 : Fin d)
    (hnotPos : ¬ ε < hPt.eigenvalues i0)
    (hnotNeg : ¬ hPt.eigenvalues i0 < -ε) :
    let v : Fin d → ℂ := ⇑(hPt.eigenvectorBasis i0)
    Ptilde *ᵥ v = (hPt.eigenvalues i0 : ℂ) • v ∧
      star v ⬝ᵥ v = 1 ∧
      |hPt.eigenvalues i0| ≤ ε := by
  let v : Fin d → ℂ := ⇑(hPt.eigenvectorBasis i0)
  have hvinner : star v ⬝ᵥ v = 1 := by
    dsimp [v]
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      @inner_self_eq_norm_sq_to_K ℂ,
      hPt.eigenvectorBasis.orthonormal.1 i0]
    norm_num
  refine ⟨?_, hvinner, abs_le.mpr ⟨?_, ?_⟩⟩
  · simpa [v] using hPt.mulVec_eigenvectorBasis i0
  · exact le_of_not_gt hnotNeg
  · exact le_of_not_gt hnotPos

/-- Exact four-branch package for thm:SMQG-robust-positivity. -/
theorem robust_reflected_positivity
    (P Ptilde : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hPt : Ptilde.IsHermitian)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hclose : ‖Ptilde - P‖ ≤ ε)
    (i0 : Fin d)
    (hmin : ∀ i, hPt.eigenvalues i0 ≤ hPt.eigenvalues i) :
    (hPt.eigenvalues i0 > ε → P.PosDef)
    ∧ (hPt.eigenvalues i0 < -ε →
      let v : Fin d → ℂ := ⇑(hPt.eigenvectorBasis i0)
      Ptilde *ᵥ v = (hPt.eigenvalues i0 : ℂ) • v ∧
        star v ⬝ᵥ v = 1 ∧
        (star v ⬝ᵥ (P *ᵥ v)).re < 0)
    ∧ ((¬ hPt.eigenvalues i0 > ε) ∧
        (¬ hPt.eigenvalues i0 < -ε) →
      let v : Fin d → ℂ := ⇑(hPt.eigenvectorBasis i0)
      Ptilde *ᵥ v = (hPt.eigenvalues i0 : ℂ) • v ∧
        star v ⬝ᵥ v = 1 ∧
        |hPt.eigenvalues i0| ≤ ε)
    ∧ (∀ r : ℕ, 1 ≤ r →
      ‖cmpd r Ptilde - cmpd r P‖ ≤
        r * max ‖Ptilde‖ ‖P‖ ^ (r - 1) * ε) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hgap
    exact posDef_of_approximate_min_gt_error P Ptilde hP hPt
      ε (hPt.eigenvalues i0) hε hclose hmin hgap
  · exact bottom_eigenvector_negative_of_lt_neg_error
      P Ptilde hP hPt ε hε hclose i0
  · intro hsoft
    exact bottom_eigenvector_soft_of_unresolved Ptilde hPt ε i0
      hsoft.1 hsoft.2
  · intro r hr
    calc
      ‖cmpd r Ptilde - cmpd r P‖
          ≤ r * max ‖Ptilde‖ ‖P‖ ^ (r - 1) *
              ‖Ptilde - P‖ :=
        exterior_power_perturbation_bound Ptilde P r hr
      _ ≤ r * max ‖Ptilde‖ ‖P‖ ^ (r - 1) * ε := by
        gcongr

end RobustReflectedPositivity
end NCG
