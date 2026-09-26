/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.IncidenceDeterminantExact

/-!
# The incidence determinant: symmetrised Cauchy–Binet, nonnegative coefficients, least power

Completes `thm:incidence-determinant` of the spacetime–gauge duality paper on top of
`IncidenceDeterminantExact` (face criterion, homogeneity, the polynomial `P_E`).

The Cauchy–Binet step of the manuscript is formalised in a **symmetrised** form that avoids
grouping row choices by their image: for a rectangular matrix `A : Matrix R n ℂ`, weights
`t : R → S` in a commutative ring `S` and a ring homomorphism `C : ℂ →+* S`,
```
  n! · det (∑_r t_r · C(conj A_{r i}) C(A_{r j}))_{ij}
    = ∑_{p : n → R} (∏_i t_{p i}) · C(|det A_p|²),      A_p = rows p(0), …, p(n−1) of A
```
(`factorial_mul_det_eq_sum`; the non-injective `p` contribute `0`).  Applied to the stacked
constraint matrix (rows indexed by `Σ e, Fin (dim W e)`: the coordinates of the constraint
vectors `v_{(e,k)} = D_e^* b_{e,k}` in orthonormal bases, `stackedMatrix`) with
`t_{(e,k)} = X_e`, this gives `n! · P_E = ∑_p (∏_i X_{e(p i)}) · C(|det A_p|²)`
(`factorial_mul_incidencePoly`, `factorial_mul_coeff`), hence

* `incidencePoly_coeff_nonneg`: **every coefficient of `P_E` is a nonnegative real**
  (`0 ≤ coeff α P_E` in the complex order);
* `incidencePoly_least_power`: when `f(E) = n` (so `P_E ≠ 0`), **the least power of `X_e` in
  `P_E` is exactly `κ_e = n − f(E ∖ {e})`**: `κ_e ≤ α(e)` for every monomial `X^α` of `P_E`
  (`kappa_le_rowExponent`: a row basis uses at most `f(E ∖ {e})` rows from the other blocks),
  and some monomial attains `α(e) = κ_e` (`exists_det_ne_zero_rowExponent_eq`: extend a row
  basis of `R(E ∖ {e})` by rows of the block `e`);
* `essential_iff_X_dvd`: `e` is essential (`f(E ∖ {e}) < n`) iff every monomial of `P_E`
  contains `X_e`;
* `incidence_determinant`: the assembled theorem.

Disclosure: the "least power" clause is stated under the hypothesis `f(E) = n` (the manuscript
assumes `G_E ≻ 0`; without it `P_E = 0` and the least power is undefined), and "`w_e ∣ P_E`"
is rendered as "every monomial with nonzero coefficient contains `X_e`".
-/

open Module Finset Matrix
open scoped ComplexOrder

namespace RenewalGeometry
namespace IncidencePolymatroid

/-! ### Symmetrised Cauchy–Binet -/

section CauchyBinet

variable {n R S : Type*} [Fintype n] [DecidableEq n] [Fintype R] [CommRing S]

/-- The `p`-th term of the row expansion: `(∏ t_{p i}) · (∏_i C(A_{p i, i})) · C(conj det A_p)`. -/
def rowTerm (A : Matrix R n ℂ) (t : R → S) (C : ℂ →+* S) (p : n → R) : S :=
  (∏ i, t (p i)) * ((∏ i, C (A (p i) i)) * C (star (A.submatrix p id).det))

/-- The signed sum `∑_σ ε σ ∏_i C(conj A_{p i, σ i})` is `C(conj det A_p)`. -/
theorem sum_sign_prod_star (A : Matrix R n ℂ) (C : ℂ →+* S) (p : n → R) :
    (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : S) * ∏ i, C (star (A (p i) (σ i)))) =
      C (star (A.submatrix p id).det) := by
  have h : (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : S) * ∏ i, C (star (A (p i) (σ i)))) =
      (((A.submatrix p id)ᴴ).map C).det := by
    rw [Matrix.det_apply']
    rfl
  rw [h, ← Matrix.det_conjTranspose, RingHom.map_det]
  rfl

/-- The signed sum `∑_τ ε τ ∏_i C(A_{p (τ i), i})` is `C(det A_p)`. -/
theorem sum_sign_prod (A : Matrix R n ℂ) (C : ℂ →+* S) (p : n → R) :
    (∑ τ : Equiv.Perm n, ((Equiv.Perm.sign τ : ℤ) : S) * ∏ i, C (A (p (τ i)) i)) =
      C (A.submatrix p id).det := by
  rw [RingHom.map_det, Matrix.det_apply']
  rfl

/-- Row expansion of the determinant of `∑_r t_r C(conj A_{r i}) C(A_{r j})`. -/
theorem det_eq_sum_rowTerm (A : Matrix R n ℂ) (t : R → S) (C : ℂ →+* S) :
    Matrix.det (Matrix.of fun i j => ∑ r, t r * (C (star (A r i)) * C (A r j))) =
      ∑ p : n → R, rowTerm A t C p := by
  rw [Matrix.det_apply']
  simp only [Matrix.of_apply, Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Finset.prod_mul_distrib]
  rw [rowTerm, ← sum_sign_prod_star A C p, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- Symmetrisation: `rowTerm (p ∘ τ)` summed over `τ` gives `(∏ t_{p i}) · C(|det A_p|²)`. -/
theorem sum_rowTerm_comp (A : Matrix R n ℂ) (t : R → S) (C : ℂ →+* S) (p : n → R) :
    (∑ τ : Equiv.Perm n, rowTerm A t C (p ∘ τ)) =
      (∏ i, t (p i)) * C (star (A.submatrix p id).det * (A.submatrix p id).det) := by
  have hdet : ∀ τ : Equiv.Perm n,
      (A.submatrix (p ∘ τ) id).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (A.submatrix p id).det := by
    intro τ
    rw [← Matrix.det_permute τ (A.submatrix p id), Matrix.submatrix_submatrix]
    rfl
  have hprod : ∀ τ : Equiv.Perm n, (∏ i, t ((p ∘ τ) i)) = ∏ i, t (p i) := fun τ =>
    Equiv.prod_comp τ (fun i => t (p i))
  have hterm : ∀ τ : Equiv.Perm n, rowTerm A t C (p ∘ τ) =
      (∏ i, t (p i)) * C (star (A.submatrix p id).det) *
        (((Equiv.Perm.sign τ : ℤ) : S) * ∏ i, C (A (p (τ i)) i)) := by
    intro τ
    rw [rowTerm, hdet τ, hprod τ, star_mul', star_intCast, map_mul, map_intCast]
    simp only [Function.comp_apply]
    ring
  rw [Finset.sum_congr rfl (fun τ _ => hterm τ), ← Finset.mul_sum, sum_sign_prod A C p, map_mul]
  ring

/-- **Symmetrised Cauchy–Binet**: `n! · det (∑_r t_r C(conj A_{r i}) C(A_{r j}))
= ∑_{p : n → R} (∏_i t_{p i}) · C(|det A_p|²)`. -/
theorem factorial_mul_det_eq_sum (A : Matrix R n ℂ) (t : R → S) (C : ℂ →+* S) :
    ((Fintype.card n).factorial : S) *
      Matrix.det (Matrix.of fun i j => ∑ r, t r * (C (star (A r i)) * C (A r j))) =
      ∑ p : n → R, (∏ i, t (p i)) * C (star (A.submatrix p id).det * (A.submatrix p id).det) := by
  rw [det_eq_sum_rowTerm]
  have hcard : ((Fintype.card n).factorial : S) * ∑ p : n → R, rowTerm A t C p =
      ∑ τ : Equiv.Perm n, ∑ p : n → R, rowTerm A t C p := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
  rw [hcard]
  have hre : ∀ τ : Equiv.Perm n,
      (∑ p : n → R, rowTerm A t C p) = ∑ p : n → R, rowTerm A t C (p ∘ τ) := by
    intro τ
    rw [← Equiv.sum_comp (Equiv.arrowCongr τ.symm (Equiv.refl R)) (rowTerm A t C)]
    rfl
  rw [Finset.sum_congr rfl (fun τ _ => hre τ), Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => sum_rowTerm_comp A t C p

end CauchyBinet

/-! ### The stacked constraint matrix and `P_E` -/

section Incidence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {W : ι → Type*} [∀ e, NormedAddCommGroup (W e)] [∀ e, InnerProductSpace ℂ (W e)]
  [∀ e, FiniteDimensional ℂ (W e)]

/-- The row index set of the stacked constraint matrix: `(e, k)`, `k < dim W_e`. -/
abbrev RowIdx (W : ι → Type*) [∀ e, NormedAddCommGroup (W e)] [∀ e, InnerProductSpace ℂ (W e)]
    [∀ e, FiniteDimensional ℂ (W e)] : Type _ :=
  Σ e : ι, Fin (finrank ℂ (W e))

/-- The constraint vectors `v_{(e,k)} = D_e^* b_{e,k}` (`b_e` the standard orthonormal basis
of `W_e`); they span `R(S) = ∑_{e∈S} Ran D_e^*`. -/
noncomputable def constraintVec (D : ∀ e, V →ₗ[ℂ] W e) (r : RowIdx W) : V :=
  LinearMap.adjoint (D r.1) (stdOrthonormalBasis ℂ (W r.1) r.2)

/-- The stacked constraint matrix: row `r` holds the coordinates of `v_r` in the standard
orthonormal basis of `V`. -/
noncomputable def stackedMatrix (D : ∀ e, V →ₗ[ℂ] W e) :
    Matrix (RowIdx W) (Fin (finrank ℂ V)) ℂ :=
  fun r j => (stdOrthonormalBasis ℂ V).repr (constraintVec D r) j

theorem gramMatrix_apply (D : ∀ e, V →ₗ[ℂ] W e) (e : ι) (i j : Fin (finrank ℂ V)) :
    gramMatrix D e i j =
      ∑ k, stackedMatrix D ⟨e, k⟩ i * star (stackedMatrix D ⟨e, k⟩ j) := by
  have h2 : LinearMap.toMatrix (stdOrthonormalBasis ℂ V).toBasis
      (stdOrthonormalBasis ℂ (W e)).toBasis (D e) =
      (LinearMap.toMatrix (stdOrthonormalBasis ℂ (W e)).toBasis (stdOrthonormalBasis ℂ V).toBasis
        (LinearMap.adjoint (D e)))ᴴ := by
    rw [LinearMap.toMatrix_adjoint, Matrix.conjTranspose_conjTranspose]
  rw [gramMatrix, gramTerm, LinearMap.toMatrix_comp _ (stdOrthonormalBasis ℂ (W e)).toBasis, h2,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp only [stackedMatrix, constraintVec, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply]

theorem gramPolyMatrix_transpose_eq (D : ∀ e, V →ₗ[ℂ] W e) :
    (gramPolyMatrix D)ᵀ = Matrix.of fun i j => ∑ r : RowIdx W,
      (MvPolynomial.X r.1 : MvPolynomial ι ℂ) *
        (MvPolynomial.C (star (stackedMatrix D r i)) * MvPolynomial.C (stackedMatrix D r j)) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.transpose_apply, Matrix.of_apply, gramPolyMatrix_apply]
  rw [Fintype.sum_sigma (fun r : RowIdx W => (MvPolynomial.X r.1 : MvPolynomial ι ℂ) *
    (MvPolynomial.C (star (stackedMatrix D r i)) * MvPolynomial.C (stackedMatrix D r j)))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [gramMatrix_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, mul_comm (MvPolynomial.C (stackedMatrix D ⟨e, k⟩ j))]

/-- **Symmetrised Cauchy–Binet for `P_E`**:
`n! · P_E = ∑_{p : Fin n → R} (∏_i X_{e(p i)}) · C(|det A_p|²)`. -/
theorem factorial_mul_incidencePoly (D : ∀ e, V →ₗ[ℂ] W e) :
    ((finrank ℂ V).factorial : MvPolynomial ι ℂ) * incidencePoly D =
      ∑ p : Fin (finrank ℂ V) → RowIdx W,
        (∏ i, (MvPolynomial.X (p i).1 : MvPolynomial ι ℂ)) *
          MvPolynomial.C (star ((stackedMatrix D).submatrix p id).det *
            ((stackedMatrix D).submatrix p id).det) := by
  rw [incidencePoly, ← Matrix.det_transpose, gramPolyMatrix_transpose_eq]
  have := factorial_mul_det_eq_sum (stackedMatrix D)
    (fun r : RowIdx W => (MvPolynomial.X r.1 : MvPolynomial ι ℂ)) MvPolynomial.C
  rwa [Fintype.card_fin] at this

/-- The exponent vector of a row choice: `α_p(e) = #{i : e(p i) = e}`. -/
noncomputable def rowExponent {m : ℕ} (p : Fin m → RowIdx W) : ι →₀ ℕ :=
  ∑ i, Finsupp.single (p i).1 1

theorem prod_X_eq_monomial {m : ℕ} (p : Fin m → RowIdx W) :
    (∏ i, (MvPolynomial.X (p i).1 : MvPolynomial ι ℂ)) =
      MvPolynomial.monomial (rowExponent p) 1 := by
  rw [rowExponent, MvPolynomial.monomial_sum_one]
  rfl

theorem rowExponent_apply {m : ℕ} (p : Fin m → RowIdx W) (e : ι) :
    rowExponent p e = (Finset.univ.filter fun i => (p i).1 = e).card := by
  rw [rowExponent, Finsupp.finsetSum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.single_apply]

/-- `n! · coeff_α P_E = ∑_{p : α_p = α} |det A_p|²`. -/
theorem factorial_mul_coeff (D : ∀ e, V →ₗ[ℂ] W e) (α : ι →₀ ℕ) :
    ((finrank ℂ V).factorial : ℂ) * MvPolynomial.coeff α (incidencePoly D) =
      ∑ p : Fin (finrank ℂ V) → RowIdx W,
        (if rowExponent p = α then 1 else 0) *
          (star ((stackedMatrix D).submatrix p id).det * ((stackedMatrix D).submatrix p id).det) := by
  have h := congrArg (MvPolynomial.coeff α) (factorial_mul_incidencePoly D)
  rw [← map_natCast MvPolynomial.C, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum] at h
  rw [h]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_comm, MvPolynomial.coeff_C_mul, prod_X_eq_monomial, MvPolynomial.coeff_monomial,
    mul_comm]

/-- **Nonnegative coefficients**: every coefficient of `P_E` is `≥ 0` in the complex order
(i.e. a nonnegative real number). -/
theorem incidencePoly_coeff_nonneg (D : ∀ e, V →ₗ[ℂ] W e) (α : ι →₀ ℕ) :
    0 ≤ MvPolynomial.coeff α (incidencePoly D) := by
  have hnn : 0 ≤ ((finrank ℂ V).factorial : ℂ) * MvPolynomial.coeff α (incidencePoly D) := by
    rw [factorial_mul_coeff]
    refine Finset.sum_nonneg fun p _ => mul_nonneg ?_ (star_mul_self_nonneg _)
    split_ifs <;> simp
  have hpos : (0 : ℂ) < (finrank ℂ V).factorial := by exact_mod_cast Nat.factorial_pos _
  exact le_of_mul_le_mul_left (by rwa [mul_zero]) hpos

theorem incidencePoly_coeff_im (D : ∀ e, V →ₗ[ℂ] W e) (α : ι →₀ ℕ) :
    (MvPolynomial.coeff α (incidencePoly D)).im = 0 :=
  (Complex.nonneg_iff.mp (incidencePoly_coeff_nonneg D α)).2.symm

theorem incidencePoly_coeff_re_nonneg (D : ∀ e, V →ₗ[ℂ] W e) (α : ι →₀ ℕ) :
    0 ≤ (MvPolynomial.coeff α (incidencePoly D)).re :=
  (Complex.nonneg_iff.mp (incidencePoly_coeff_nonneg D α)).1

/-! ### The least power of `X_e`: `κ_e = n − f(E ∖ {e})` -/

/-- `v_r ∈ R(S)` whenever `r.1 ∈ S`. -/
theorem constraintVec_mem (D : ∀ e, V →ₗ[ℂ] W e) {S : Finset ι} {r : RowIdx W} (hr : r.1 ∈ S) :
    constraintVec D r ∈ constraintRange D S :=
  Finset.le_sup (f := fun e => LinearMap.range (LinearMap.adjoint (D e))) hr
    (LinearMap.mem_range_self _ _)

/-- `R(S) = span {v_r : r.1 ∈ S}`. -/
theorem constraintRange_eq_span (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) :
    constraintRange D S =
      Submodule.span ℂ (constraintVec D '' {r : RowIdx W | r.1 ∈ S}) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · rw [constraintRange]
    refine Finset.sup_le fun e he => ?_
    rw [LinearMap.range_eq_map, ← (stdOrthonormalBasis ℂ (W e)).toBasis.span_eq,
      Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨⟨e, k⟩, he, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact constraintVec_mem D hr

/-- The rows of `A_p` are the coordinate vectors of `v_{p i}`; if they are linearly
independent, so are the `v_{p i}`. -/
theorem linearIndependent_constraintVec_of_det_ne_zero (D : ∀ e, V →ₗ[ℂ] W e)
    (p : Fin (finrank ℂ V) → RowIdx W) (hp : ((stackedMatrix D).submatrix p id).det ≠ 0) :
    LinearIndependent ℂ (fun i => constraintVec D (p i)) := by
  have hrows : LinearIndependent ℂ ((stackedMatrix D).submatrix p id).row :=
    Matrix.linearIndependent_rows_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp))
  exact LinearIndependent.of_comp
    ((WithLp.linearEquiv 2 ℂ (Fin (finrank ℂ V) → ℂ)).toLinearMap ∘ₗ
      (stdOrthonormalBasis ℂ V).repr.toLinearEquiv.toLinearMap) hrows

/-- Conversely, if the `v_{p i}` are linearly independent then `det A_p ≠ 0`. -/
theorem det_ne_zero_of_linearIndependent (D : ∀ e, V →ₗ[ℂ] W e)
    (p : Fin (finrank ℂ V) → RowIdx W)
    (hv : LinearIndependent ℂ (fun i => constraintVec D (p i))) :
    ((stackedMatrix D).submatrix p id).det ≠ 0 := by
  let φ : V ≃ₗ[ℂ] (Fin (finrank ℂ V) → ℂ) :=
    (stdOrthonormalBasis ℂ V).repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℂ _)
  have hrows : LinearIndependent ℂ ((stackedMatrix D).submatrix p id).row :=
    hv.map' φ.toLinearMap (LinearMap.ker_eq_bot.mpr φ.injective)
  have := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
  exact this

/-- **Lower bound**: every row choice with `det A_p ≠ 0` uses at least
`κ_e = n − f(E ∖ {e})` rows from the block `e`. -/
theorem kappa_le_rowExponent (D : ∀ e, V →ₗ[ℂ] W e) (e : ι)
    (p : Fin (finrank ℂ V) → RowIdx W) (hp : ((stackedMatrix D).submatrix p id).det ≠ 0) :
    finrank ℂ V - incidenceRank D (Finset.univ.erase e) ≤ rowExponent p e := by
  have hv := linearIndependent_constraintVec_of_det_ne_zero D p hp
  -- the rows from the other blocks are independent inside `R(E ∖ {e})`
  let I := {i : Fin (finrank ℂ V) // (p i).1 ≠ e}
  let w : I → constraintRange D (Finset.univ.erase e) := fun i =>
    ⟨constraintVec D (p i.1), constraintVec_mem D (Finset.mem_erase.mpr ⟨i.2, Finset.mem_univ _⟩)⟩
  have hw : LinearIndependent ℂ w :=
    LinearIndependent.of_comp (constraintRange D (Finset.univ.erase e)).subtype
      (hv.comp (Subtype.val : I → Fin (finrank ℂ V)) Subtype.val_injective)
  have hcard : Fintype.card I ≤ incidenceRank D (Finset.univ.erase e) :=
    hw.fintype_card_le_finrank
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin (finrank ℂ V) => (p i).1 = e)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hI : Fintype.card I = (Finset.univ.filter fun i : Fin (finrank ℂ V) => ¬ (p i).1 = e).card :=
    Fintype.card_subtype _
  rw [rowExponent_apply]
  omega

/-- **Attainment**: if `f(E) = n`, some row choice with `det A_p ≠ 0` uses exactly
`κ_e = n − f(E ∖ {e})` rows from the block `e` (extend a row basis of `R(E ∖ {e})` by rows
of the block `e`). -/
theorem exists_det_ne_zero_rowExponent_eq (D : ∀ e, V →ₗ[ℂ] W e) (e : ι)
    (hfull : incidenceRank D Finset.univ = finrank ℂ V) :
    ∃ p : Fin (finrank ℂ V) → RowIdx W, ((stackedMatrix D).submatrix p id).det ≠ 0 ∧
      rowExponent p e = finrank ℂ V - incidenceRank D (Finset.univ.erase e) := by
  classical
  set v := constraintVec D with hv_def
  set t : Set (RowIdx W) := {r | r.1 ≠ e} with ht
  obtain ⟨b₁, hb₁t, -, hspan₁, hind₁⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty (R := ℂ) (v := v)) (Set.empty_subset t)
  obtain ⟨b₂, -, hb₁₂, hspan₂, hind₂⟩ :=
    exists_linearIndepOn_extension hind₁ (Set.subset_univ b₁)
  -- `span (v '' b₂) = ⊤`
  have htop : Submodule.span ℂ (v '' b₂) = ⊤ := by
    have h1 : constraintRange D Finset.univ = ⊤ := Submodule.eq_top_of_finrank_eq hfull
    rw [constraintRange_eq_span] at h1
    refine top_le_iff.mp ?_
    rw [← h1]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, -, rfl⟩
    exact hspan₂ ⟨r, Set.mem_univ r, rfl⟩
  -- `span (v '' b₁) = R(E ∖ {e})`
  have hspan₁' : Submodule.span ℂ (v '' b₁) = constraintRange D (Finset.univ.erase e) := by
    rw [constraintRange_eq_span]
    refine le_antisymm (Submodule.span_mono (Set.image_mono ?_)) (Submodule.span_le.mpr ?_)
    · intro r hr
      exact Finset.mem_erase.mpr ⟨hb₁t hr, Finset.mem_univ _⟩
    · rintro _ ⟨r, hr, rfl⟩
      exact hspan₁ ⟨r, (Finset.mem_erase.mp hr).1, rfl⟩
  -- cardinalities
  have hcard₂ : Fintype.card b₂ = finrank ℂ V := by
    have := finrank_span_eq_card (R := ℂ) hind₂.linearIndependent
    rw [← Set.image_eq_range, htop, finrank_top] at this
    exact this.symm
  have hcard₁ : Fintype.card b₁ = incidenceRank D (Finset.univ.erase e) := by
    have := finrank_span_eq_card (R := ℂ) hind₁.linearIndependent
    rw [← Set.image_eq_range, hspan₁'] at this
    exact this.symm
  -- `b₂ ∩ t ⊆ b₁`
  have hinter : ∀ r ∈ b₂, r ∈ t → r ∈ b₁ := by
    intro r hr₂ hrt
    by_contra hr₁
    have hmem : v r ∈ Submodule.span ℂ (v '' b₁) := hspan₁ ⟨r, hrt, rfl⟩
    have hnot := hind₂.linearIndependent.notMem_span_image
      (s := {x : b₂ | (x : RowIdx W) ∈ b₁}) (x := ⟨r, hr₂⟩) hr₁
    have hset : (fun x : b₂ => v x) '' {x : b₂ | (x : RowIdx W) ∈ b₁} = v '' b₁ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.1, hx, rfl⟩
      · rintro ⟨r', hr', rfl⟩
        exact ⟨⟨r', hb₁₂ hr'⟩, hr', rfl⟩
    rw [hset] at hnot
    exact hnot hmem
  -- the row choice
  let eqv : b₂ ≃ Fin (finrank ℂ V) := Fintype.equivFinOfCardEq hcard₂
  let p : Fin (finrank ℂ V) → RowIdx W := fun i => (eqv.symm i).1
  refine ⟨p, ?_, ?_⟩
  · exact det_ne_zero_of_linearIndependent D p
      (hind₂.linearIndependent.comp eqv.symm eqv.symm.injective)
  · rw [rowExponent_apply]
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin (finrank ℂ V) => (p i).1 = e)
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    have hinj : Function.Injective p := fun i j h => eqv.symm.injective (Subtype.ext h)
    have hne : (Finset.univ.filter fun i : Fin (finrank ℂ V) => ¬ (p i).1 = e).card =
        Fintype.card b₁ := by
      rw [← Finset.card_image_of_injective
        (Finset.univ.filter fun i : Fin (finrank ℂ V) => ¬ (p i).1 = e) hinj,
        ← Set.toFinset_card]
      congr 1
      ext r
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_toFinset]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hinter _ (eqv.symm i).2 hi
      · intro hr
        refine ⟨eqv ⟨r, hb₁₂ hr⟩, ?_, ?_⟩
        · show ¬ ((eqv.symm (eqv ⟨r, hb₁₂ hr⟩)).1).1 = e
          rw [Equiv.symm_apply_apply]
          exact hb₁t hr
        · show (eqv.symm (eqv ⟨r, hb₁₂ hr⟩)).1 = r
          rw [Equiv.symm_apply_apply]
    omega

/-- A nonzero coefficient comes from a row choice with `det A_p ≠ 0` and `α_p = α`. -/
theorem exists_rowExponent_eq_of_coeff_ne_zero (D : ∀ e, V →ₗ[ℂ] W e) {α : ι →₀ ℕ}
    (hα : MvPolynomial.coeff α (incidencePoly D) ≠ 0) :
    ∃ p : Fin (finrank ℂ V) → RowIdx W, ((stackedMatrix D).submatrix p id).det ≠ 0 ∧
      rowExponent p = α := by
  have h : ((finrank ℂ V).factorial : ℂ) * MvPolynomial.coeff α (incidencePoly D) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne') hα
  rw [factorial_mul_coeff] at h
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨p, fun hd => hp ?_, ?_⟩
  · rw [hd, mul_zero, mul_zero]
  · by_contra hne
    rw [if_neg hne, zero_mul] at hp
    exact hp rfl

/-- A row choice with `det A_p ≠ 0` makes the coefficient of `X^{α_p}` nonzero. -/
theorem coeff_ne_zero_of_det_ne_zero (D : ∀ e, V →ₗ[ℂ] W e)
    (p : Fin (finrank ℂ V) → RowIdx W) (hp : ((stackedMatrix D).submatrix p id).det ≠ 0) :
    MvPolynomial.coeff (rowExponent p) (incidencePoly D) ≠ 0 := by
  intro h0
  have h := factorial_mul_coeff D (rowExponent p)
  rw [h0, mul_zero] at h
  have hnn : ∀ q ∈ (Finset.univ : Finset (Fin (finrank ℂ V) → RowIdx W)), (0 : ℂ) ≤
      (if rowExponent q = rowExponent p then 1 else 0) *
        (star ((stackedMatrix D).submatrix q id).det * ((stackedMatrix D).submatrix q id).det) := by
    intro q _
    refine mul_nonneg ?_ (star_mul_self_nonneg _)
    split_ifs <;> simp
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h.symm p (Finset.mem_univ p)
  rw [if_pos rfl, one_mul, mul_eq_zero, star_eq_zero, or_self] at hterm
  exact hp hterm

/-- **The least power of `X_e` in `P_E` is exactly `κ_e = n − f(E ∖ {e})`** (assuming
`f(E) = n`, i.e. `P_E ≠ 0`): every monomial of `P_E` has `X_e`-exponent `≥ κ_e`, and some
monomial has exponent exactly `κ_e`. -/
theorem incidencePoly_least_power (D : ∀ e, V →ₗ[ℂ] W e) (e : ι)
    (hfull : incidenceRank D Finset.univ = finrank ℂ V) :
    (∀ α : ι →₀ ℕ, MvPolynomial.coeff α (incidencePoly D) ≠ 0 →
        finrank ℂ V - incidenceRank D (Finset.univ.erase e) ≤ α e) ∧
    ∃ α : ι →₀ ℕ, MvPolynomial.coeff α (incidencePoly D) ≠ 0 ∧
        α e = finrank ℂ V - incidenceRank D (Finset.univ.erase e) := by
  refine ⟨fun α hα => ?_, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := exists_rowExponent_eq_of_coeff_ne_zero D hα
    exact kappa_le_rowExponent D e p hp
  · obtain ⟨p, hp, hpe⟩ := exists_det_ne_zero_rowExponent_eq D e hfull
    exact ⟨rowExponent p, coeff_ne_zero_of_det_ne_zero D p hp, hpe⟩

/-- **Essential edges**: `e` is essential (`f(E ∖ {e}) < f(E) = n`, i.e. `κ_e ≥ 1`) iff every
monomial of `P_E` contains `X_e` (i.e. iff `X_e` divides `P_E`). -/
theorem essential_iff_X_dvd (D : ∀ e, V →ₗ[ℂ] W e) (e : ι)
    (hfull : incidenceRank D Finset.univ = finrank ℂ V) :
    incidenceRank D (Finset.univ.erase e) < finrank ℂ V ↔
      ∀ α : ι →₀ ℕ, MvPolynomial.coeff α (incidencePoly D) ≠ 0 → 1 ≤ α e := by
  obtain ⟨h1, α₀, hα₀, hα₀e⟩ := incidencePoly_least_power D e hfull
  constructor
  · intro hlt α hα
    have := h1 α hα
    omega
  · intro h
    have := h α₀ hα₀
    omega

/-- **`thm:incidence-determinant`** (assembled): `P_E` is homogeneous of degree `n` with
nonnegative real coefficients and evaluates to `det G(w)`; on every coordinate face
`P_E(w) > 0 ⟺ f(S) = n`; and when `f(E) = n` the least power of `X_e` in `P_E` is exactly
`κ_e = n − f(E ∖ {e})`, so `e` is essential iff every monomial of `P_E` contains `X_e`. -/
theorem incidence_determinant (D : ∀ e, V →ₗ[ℂ] W e) :
    (incidencePoly D).IsHomogeneous (finrank ℂ V) ∧
    (∀ α : ι →₀ ℕ, 0 ≤ MvPolynomial.coeff α (incidencePoly D)) ∧
    (∀ (w : ι → ℝ) (S : Finset ι), (∀ e ∈ S, 0 < w e) → (∀ e ∉ S, w e = 0) →
      (0 < incidenceDet D w ↔ incidenceRank D S = finrank ℂ V)) ∧
    (∀ w : ι → ℝ, MvPolynomial.eval (fun e => (w e : ℂ)) (incidencePoly D) = incidenceDet D w) ∧
    (incidenceRank D Finset.univ = finrank ℂ V → ∀ e : ι,
      ((∀ α : ι →₀ ℕ, MvPolynomial.coeff α (incidencePoly D) ≠ 0 →
          finrank ℂ V - incidenceRank D (Finset.univ.erase e) ≤ α e) ∧
        ∃ α : ι →₀ ℕ, MvPolynomial.coeff α (incidencePoly D) ≠ 0 ∧
          α e = finrank ℂ V - incidenceRank D (Finset.univ.erase e)) ∧
      (incidenceRank D (Finset.univ.erase e) < finrank ℂ V ↔
        ∀ α : ι →₀ ℕ, MvPolynomial.coeff α (incidencePoly D) ≠ 0 → 1 ≤ α e)) :=
  ⟨incidencePoly_isHomogeneous D, incidencePoly_coeff_nonneg D,
    fun _ _ hw hw0 => incidenceDet_pos_iff D hw hw0, eval_incidencePoly D,
    fun hfull e => ⟨incidencePoly_least_power D e hfull, essential_iff_X_dvd D e hfull⟩⟩

end Incidence

end IncidencePolymatroid
end RenewalGeometry
