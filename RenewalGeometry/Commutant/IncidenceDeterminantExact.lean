/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.IncidencePolymatroidExact

/-!
# The weighted incidence determinant: face criterion and homogeneity

Towards `thm:incidence-determinant` of the spacetime–gauge duality paper, in the abstract
setting of `IncidencePolymatroidExact.lean` (constraint maps `D e : V →ₗ W e` on a
finite-dimensional complex inner product space, `G_e = D_e^* D_e`).

For nonnegative weights `w = (w_e)` the **weighted incidence Gram operator** is
`G(w) = ∑_e w_e G_e` (`weightedGram`) and `P_E(w) = det G(w)` (`incidenceDet`,
`eq:weighted-incidence-Gram`).

* `weightedGram_isPositive`: `G(w) ≽ 0` for `w ≥ 0`;
* `ker_weightedGram`: on a coordinate face (`w_e > 0` on `S`, `w_e = 0` off `S`)
  `Ker G(w) = ⋂_{e∈S} Ker D_e`;
* `incidenceDet_pos_iff` / `incidenceDet_ne_zero_iff`: the **face criterion**
  `P_E(w) > 0 ⟺ f(S) = n` (`eq:incidence-face-exactness`, first equivalence), and
  `incidenceDet_pos_iff_enlargedCommutant_eq` adds `⟺ M(S) = M(E)` in the commutant
  setting;
* `incidenceDet_smul`: `P_E(t w) = tⁿ P_E(w)` (degree-`n` homogeneity as a function);
* `incidencePoly`, `eval_incidencePoly`, `incidencePoly_isHomogeneous`: `P_E` as an
  element of `ℂ[X_e : e ∈ E]` (the determinant of `∑_e X_e · [G_e]` in an orthonormal
  basis), which evaluates to `incidenceDet` and is homogeneous of degree `n`.

**Not covered here** (the Cauchy–Binet part of the theorem): nonnegativity of the
coefficients of `P_E`, and the clause that the least power of `X_e` in `P_E` is exactly
`κ_e = n − f(E ∖ {e})` (hence `e` essential iff `X_e ∣ P_E`).
-/

open Module Submodule Finset
open scoped ComplexOrder

namespace RenewalGeometry
namespace IncidencePolymatroid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {W : ι → Type*} [∀ e, NormedAddCommGroup (W e)] [∀ e, InnerProductSpace ℂ (W e)]
  [∀ e, FiniteDimensional ℂ (W e)]

/-! ### The weighted Gram operator -/

/-- The single-incidence Gram operator `G_e = D_e^* D_e`. -/
noncomputable def gramTerm (D : ∀ e, V →ₗ[ℂ] W e) (e : ι) : V →ₗ[ℂ] V :=
  (LinearMap.adjoint (D e)) ∘ₗ (D e)

/-- The weighted incidence Gram operator `G(w) = ∑_e w_e G_e` (`eq:weighted-incidence-Gram`). -/
noncomputable def weightedGram (D : ∀ e, V →ₗ[ℂ] W e) (w : ι → ℝ) : V →ₗ[ℂ] V :=
  ∑ e, ((w e : ℝ) : ℂ) • gramTerm D e

/-- The incidence polynomial evaluated at `w`: `P_E(w) = det G(w)`. -/
noncomputable def incidenceDet (D : ∀ e, V →ₗ[ℂ] W e) (w : ι → ℝ) : ℂ :=
  LinearMap.det (weightedGram D w)

theorem inner_gramTerm (D : ∀ e, V →ₗ[ℂ] W e) (e : ι) (x : V) :
    inner ℂ x (gramTerm D e x) = ((‖D e x‖ : ℂ)) ^ 2 := by
  rw [gramTerm, LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  rfl

/-- The quadratic form of `G(w)` is `∑_e w_e ‖D_e x‖²`. -/
theorem inner_weightedGram (D : ∀ e, V →ₗ[ℂ] W e) (w : ι → ℝ) (x : V) :
    inner ℂ x (weightedGram D w x) = ∑ e, ((w e : ℂ)) * ((‖D e x‖ : ℂ)) ^ 2 := by
  unfold weightedGram
  rw [LinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [LinearMap.smul_apply, inner_smul_right, inner_gramTerm]

theorem gramTerm_isPositive (D : ∀ e, V →ₗ[ℂ] W e) (e : ι) : (gramTerm D e).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self (D e)

/-- `G(w) ≽ 0` for nonnegative weights. -/
theorem weightedGram_isPositive (D : ∀ e, V →ₗ[ℂ] W e) {w : ι → ℝ} (hw : ∀ e, 0 ≤ w e) :
    (weightedGram D w).IsPositive :=
  LinearMap.isPositive_sum _ fun e _ =>
    (gramTerm_isPositive D e).smul_of_nonneg (Complex.zero_le_real.mpr (hw e))

/-- On a coordinate face, `Ker G(w) = ⋂_{e ∈ S} Ker D_e`. -/
theorem ker_weightedGram (D : ∀ e, V →ₗ[ℂ] W e) {w : ι → ℝ} {S : Finset ι}
    (hw : ∀ e ∈ S, 0 < w e) (hw0 : ∀ e ∉ S, w e = 0) :
    LinearMap.ker (weightedGram D w) = constraintKer D S := by
  ext x
  rw [LinearMap.mem_ker, mem_constraintKer]
  constructor
  · intro h
    have h1 : inner ℂ x (weightedGram D w x) = 0 := by rw [h, inner_zero_right]
    rw [inner_weightedGram] at h1
    have h2 : ((∑ e, w e * ‖D e x‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [Complex.ofReal_sum]
      simp only [Complex.ofReal_mul, Complex.ofReal_pow]
      exact h1
    have h3 := Complex.ofReal_eq_zero.mp h2
    have hnn : ∀ e ∈ (Finset.univ : Finset ι), 0 ≤ w e * ‖D e x‖ ^ 2 := by
      intro e _
      by_cases he : e ∈ S
      · exact mul_nonneg (hw e he).le (sq_nonneg _)
      · rw [hw0 e he, zero_mul]
    intro e he
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h3 e (Finset.mem_univ e)
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 (hw e he).ne'
    · exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h5)
  · intro h
    unfold weightedGram
    rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases he : e ∈ S
    · rw [LinearMap.smul_apply, gramTerm, LinearMap.comp_apply, h e he, map_zero, smul_zero]
    · rw [hw0 e he, Complex.ofReal_zero, zero_smul, LinearMap.zero_apply]

/-! ### The face criterion -/

/-- `P_E(w) ≠ 0` on a face iff the joint constraint kernel of `S` vanishes iff `f(S) = n`. -/
theorem incidenceDet_ne_zero_iff (D : ∀ e, V →ₗ[ℂ] W e) {w : ι → ℝ} {S : Finset ι}
    (hw : ∀ e ∈ S, 0 < w e) (hw0 : ∀ e ∉ S, w e = 0) :
    incidenceDet D w ≠ 0 ↔ incidenceRank D S = finrank ℂ V := by
  rw [incidenceDet, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, ker_weightedGram D hw hw0,
    constraintKer_eq_bot_iff]

/-- The determinant of a positive operator is positive as soon as it is nonzero (in the
complex order, i.e. real and positive). -/
theorem det_pos_of_isPositive_of_ne_zero {T : V →ₗ[ℂ] V} (hT : T.IsPositive)
    (hne : LinearMap.det T ≠ 0) : 0 < LinearMap.det T := by
  set b := stdOrthonormalBasis ℂ V
  have hM : (LinearMap.toMatrix b.toBasis b.toBasis T).PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff b).mpr hT
  have hdet : (LinearMap.toMatrix b.toBasis b.toBasis T).det = LinearMap.det T :=
    LinearMap.det_toMatrix b.toBasis T
  have hpd : (LinearMap.toMatrix b.toBasis b.toBasis T).PosDef :=
    hM.posDef_iff_det_ne_zero.mpr (by rw [hdet]; exact hne)
  rw [← hdet]
  exact hpd.det_pos

/-- **The face criterion** (`eq:incidence-face-exactness`, rank form): on the coordinate
face `w_e > 0` (`e ∈ S`), `w_e = 0` (`e ∉ S`), `P_E(w) > 0 ⟺ f(S) = n`. -/
theorem incidenceDet_pos_iff (D : ∀ e, V →ₗ[ℂ] W e) {w : ι → ℝ} {S : Finset ι}
    (hw : ∀ e ∈ S, 0 < w e) (hw0 : ∀ e ∉ S, w e = 0) :
    0 < incidenceDet D w ↔ incidenceRank D S = finrank ℂ V := by
  rw [← incidenceDet_ne_zero_iff D hw hw0]
  constructor
  · exact ne_of_gt
  · intro hne
    have hnn : ∀ e, 0 ≤ w e := fun e => by
      by_cases he : e ∈ S
      · exact (hw e he).le
      · rw [hw0 e he]
    exact det_pos_of_isPositive_of_ne_zero (weightedGram_isPositive D hnn) hne

/-! ### Homogeneity -/

theorem weightedGram_smul (D : ∀ e, V →ₗ[ℂ] W e) (t : ℝ) (w : ι → ℝ) :
    weightedGram D (t • w) = (t : ℂ) • weightedGram D w := by
  unfold weightedGram
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, smul_smul]

/-- **Degree-`n` homogeneity**: `P_E(t w) = tⁿ P_E(w)`. -/
theorem incidenceDet_smul (D : ∀ e, V →ₗ[ℂ] W e) (t : ℝ) (w : ι → ℝ) :
    incidenceDet D (t • w) = (t : ℂ) ^ finrank ℂ V * incidenceDet D w := by
  rw [incidenceDet, incidenceDet, weightedGram_smul, LinearMap.det_smul]

/-! ### The incidence polynomial -/

/-- The matrix of `G_e` in the standard orthonormal basis of `V`. -/
noncomputable def gramMatrix (D : ∀ e, V →ₗ[ℂ] W e) (e : ι) :
    Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ :=
  LinearMap.toMatrix (stdOrthonormalBasis ℂ V).toBasis (stdOrthonormalBasis ℂ V).toBasis
    (gramTerm D e)

/-- The polynomial matrix `∑_e X_e [G_e]`. -/
noncomputable def gramPolyMatrix (D : ∀ e, V →ₗ[ℂ] W e) :
    Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) (MvPolynomial ι ℂ) :=
  ∑ e, (MvPolynomial.X e : MvPolynomial ι ℂ) •
    (gramMatrix D e).map (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)

/-- **The incidence polynomial** `P_E ∈ ℂ[X_e : e ∈ E]`, `P_E = det (∑_e X_e G_e)`. -/
noncomputable def incidencePoly (D : ∀ e, V →ₗ[ℂ] W e) : MvPolynomial ι ℂ :=
  Matrix.det (gramPolyMatrix D)

theorem gramPolyMatrix_apply (D : ∀ e, V →ₗ[ℂ] W e) (i j : Fin (finrank ℂ V)) :
    gramPolyMatrix D i j =
      ∑ e, (MvPolynomial.X e : MvPolynomial ι ℂ) * MvPolynomial.C (gramMatrix D e i j) := by
  simp only [gramPolyMatrix, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]

/-- Evaluating `P_E` at real weights gives `det G(w)`. -/
theorem eval_incidencePoly (D : ∀ e, V →ₗ[ℂ] W e) (w : ι → ℝ) :
    MvPolynomial.eval (fun e => (w e : ℂ)) (incidencePoly D) = incidenceDet D w := by
  rw [incidencePoly, RingHom.map_det, incidenceDet,
    ← LinearMap.det_toMatrix (stdOrthonormalBasis ℂ V).toBasis]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, gramPolyMatrix_apply, map_sum]
  unfold weightedGram
  rw [map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, map_smul, Matrix.smul_apply, smul_eq_mul]
  rfl

/-- **`P_E` is homogeneous of degree `n = dim V`.** -/
theorem incidencePoly_isHomogeneous (D : ∀ e, V →ₗ[ℂ] W e) :
    (incidencePoly D).IsHomogeneous (finrank ℂ V) := by
  rw [incidencePoly, Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have hentry : ∀ i, (gramPolyMatrix D (σ i) i).IsHomogeneous 1 := by
    intro i
    rw [gramPolyMatrix_apply]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun e _ => ?_
    simpa using (MvPolynomial.isHomogeneous_X ℂ e).mul
      (MvPolynomial.isHomogeneous_C ι (gramMatrix D e (σ i) i))
  have hprod : (∏ i, gramPolyMatrix D (σ i) i).IsHomogeneous (finrank ℂ V) := by
    have := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => gramPolyMatrix D (σ i) i)
      (fun _ => 1) fun i _ => hentry i
    simpa using this
  have hsign : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial ι ℂ).IsHomogeneous 0 := by
    rw [← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)]
    exact MvPolynomial.isHomogeneous_C _ _
  simpa using hsign.mul hprod

/-! ### The commutant setting -/

section Commutant

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- **`eq:incidence-face-exactness`** in the commutant setting of
`thm:incidence-polymatroid`: on the face of `S`, `P_E(w) > 0 ⟺ f(S) = n ⟺ M(S) = M(E)`. -/
theorem incidenceDet_pos_iff_enlargedCommutant_eq (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e)
    {w : ι → ℝ} {S : Finset ι} (hw : ∀ e ∈ S, 0 < w e) (hw0 : ∀ e ∉ S, w e = 0) :
    (0 < incidenceDet (residualMap M₀ D) w
        ↔ incidenceRank (residualMap M₀ D) S = finrank ℂ (residualSpace M₀ D)) ∧
    (0 < incidenceDet (residualMap M₀ D) w
        ↔ enlargedCommutant M₀ D S = fullCommutant M₀ D) := by
  refine ⟨incidenceDet_pos_iff _ hw hw0, ?_⟩
  rw [incidenceDet_pos_iff _ hw hw0, enlargedCommutant_eq_full_iff]

end Commutant

end IncidencePolymatroid
end RenewalGeometry
