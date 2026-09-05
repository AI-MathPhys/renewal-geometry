/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHeatBathDobrushin
import NCG.Grand.DrivenProcessExact
import NCG.Lorentz.PerronExistence

/-!
# Positivity of finite Metzler exponential kernels

A real matrix with nonnegative off-diagonal entries becomes entrywise
nonnegative after adding a sufficiently large scalar identity.  Since scalar
identity commutes with the shifted matrix, its exponential factors off as a
strictly positive scalar.  The remaining exponential has a termwise
nonnegative series.  This proves positivity of the concrete tilted
Feynman--Kac semigroup without assuming it as an abstract kernel property.
-/

open Matrix Finset
open scoped BigOperators

namespace NCG
namespace MetzlerExponentialPositivity

open FiniteHeatBathDobrushin

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Add a scalar diagonal shift to a finite matrix. -/
def diagonalShift (A : Matrix S S ℝ) (c : ℝ) : Matrix S S ℝ :=
  A + c • (1 : Matrix S S ℝ)

/-- Off-diagonal nonnegativity and nonnegative shifted diagonal entries make
the shifted matrix entrywise nonnegative. -/
theorem diagonalShift_entrywiseNonnegative
    (A : Matrix S S ℝ) (c : ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hdiag : ∀ i, 0 ≤ A i i + c) :
    Matrix.EntrywiseNonnegative (diagonalShift A c) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [diagonalShift] using hdiag i
  · simpa [diagonalShift, Matrix.one_apply, hij] using hoff i j hij

/-- The sum of absolute diagonal entries is a canonical nonnegative shift. -/
noncomputable def canonicalDiagonalShift (A : Matrix S S ℝ) : ℝ :=
  ∑ i, |A i i|

theorem diagonal_add_canonicalDiagonalShift_nonnegative
    (A : Matrix S S ℝ) (i : S) :
    0 ≤ A i i + canonicalDiagonalShift A := by
  have hone : |A i i| ≤ canonicalDiagonalShift A := by
    exact Finset.single_le_sum (fun j _ => abs_nonneg (A j j))
      (Finset.mem_univ i)
  have hneg : -A i i ≤ |A i i| := neg_le_abs (A i i)
  linarith

/-- Every finite Metzler matrix has a canonical entrywise-nonnegative scalar
shift. -/
theorem canonicalDiagonalShift_entrywiseNonnegative
    (A : Matrix S S ℝ) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) :
    Matrix.EntrywiseNonnegative
      (diagonalShift A (canonicalDiagonalShift A)) :=
  diagonalShift_entrywiseNonnegative A (canonicalDiagonalShift A) hoff
    (diagonal_add_canonicalDiagonalShift_nonnegative A)

/-- Exact scalar-shift factorization of the matrix exponential kernel. -/
theorem exponentialEntry_eq_shift
    (A : Matrix S S ℝ) (c t : ℝ) :
    Matrix.exponentialEntry (t • A) =
      Real.exp (-(t * c)) •
        Matrix.exponentialEntry (t • diagonalShift A c) := by
  have hdecomp :
      t • A = (-(t * c)) • (1 : Matrix S S ℝ) +
        t • diagonalShift A c := by
    simp only [diagonalShift]
    module
  have hcomm : Commute
      ((-(t * c)) • (1 : Matrix S S ℝ))
      (t • diagonalShift A c) :=
    (Commute.one_left (t • diagonalShift A c)).smul_left (-(t * c))
  have hexp :
      NormedSpace.exp (t • A) =
        Real.exp (-(t * c)) •
          NormedSpace.exp (t • diagonalShift A c) := by
    rw [hdecomp, Matrix.exp_add_of_commute _ _ hcomm,
      exp_smul_matrix_one, smul_mul_assoc, one_mul]
  have hA : Matrix.exponentialEntry (t • A) =
      NormedSpace.exp (t • A) := by
    ext i j
    exact exponentialEntry_eq_exp_apply (t • A) i j
  have hshift :
      Matrix.exponentialEntry (t • diagonalShift A c) =
        NormedSpace.exp (t • diagonalShift A c) := by
    ext i j
    exact exponentialEntry_eq_exp_apply (t • diagonalShift A c) i j
  rw [hA, hshift]
  exact hexp

/-- The exponential kernel of any finite Metzler matrix is entrywise
nonnegative at every nonnegative time. -/
theorem exponentialEntry_smul_entrywiseNonnegative_of_offDiag
    (A : Matrix S S ℝ) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (t : ℝ) (ht : 0 ≤ t) :
    Matrix.EntrywiseNonnegative (Matrix.exponentialEntry (t • A)) := by
  rw [exponentialEntry_eq_shift A (canonicalDiagonalShift A) t]
  have hshift := canonicalDiagonalShift_entrywiseNonnegative A hoff
  have hexp : Matrix.EntrywiseNonnegative
      (Matrix.exponentialEntry
        (t • diagonalShift A (canonicalDiagonalShift A))) :=
    Matrix.exponentialEntry_nonnegative (hshift.smul ht)
  intro i j
  exact mul_nonneg (Real.exp_nonneg _) (hexp i j)

/-- In particular, the protected jump/state tilt of a finite Markov generator
has a nonnegative Feynman--Kac exponential kernel. -/
theorem tiltedGenerator_exponentialEntry_nonnegative
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (v : S → ℝ) (g : S → S → ℝ) (k t : ℝ) (ht : 0 ≤ t) :
    Matrix.EntrywiseNonnegative
      (Matrix.exponentialEntry (t • DrivenProcess.tilt L v g k)) := by
  apply exponentialEntry_smul_entrywiseNonnegative_of_offDiag
    (DrivenProcess.tilt L v g k) _ t ht
  intro i j hij
  rw [DrivenProcess.tilt_apply_ne L v g k hij]
  exact mul_nonneg (hL.offDiag_nonneg i j hij) (Real.exp_nonneg _)

/-! ## Irreducible Metzler kernels and Perron eigenpairs -/

/-- The canonical irreducibility predicate for a finite Metzler matrix: its
canonical nonnegative scalar shift is irreducible.  Scalar diagonal shifts do
not alter the off-diagonal communication graph. -/
def IsIrreducibleMetzler (A : Matrix S S ℝ) : Prop :=
  (diagonalShift A (canonicalDiagonalShift A)).IsIrreducible

/-- Matrix--vector action of a scalar diagonal shift. -/
theorem diagonalShift_mulVec (A : Matrix S S ℝ) (c : ℝ) (x : S → ℝ) :
    (diagonalShift A c).mulVec x = A.mulVec x + c • x := by
  rw [diagonalShift, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]

open scoped Matrix.Norms.Operator in
set_option backward.isDefEq.respectTransparency false in
/-- A positive power coefficient contributes a strictly positive term to the
matrix exponential series. -/
theorem exponentialEntry_pos_of_power_pos
    (A : Matrix S S ℝ) (hA : Matrix.EntrywiseNonnegative A)
    (i j : S) (n : ℕ) (hn : 0 < (A ^ n) i j) :
    0 < Matrix.exponentialEntry A i j := by
  unfold Matrix.exponentialEntry
  have hmatrix : Summable
      (fun m : ℕ => ((m.factorial : ℝ)⁻¹) • A ^ m) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) A
  have hrow := (Pi.summable.mp hmatrix) i
  have hentry := (Pi.summable.mp hrow) j
  have hsummable : Summable
      (fun m : ℕ => (1 / m.factorial : ℝ) * (A ^ m) i j) := by
    simpa [one_div] using hentry
  exact hsummable.tsum_pos
    (fun m => mul_nonneg (by positivity) (hA.pow m i j)) n
    (mul_pos (by positivity) hn)

/-- At every positive time, the exponential of an irreducible nonnegative
finite matrix is entrywise strictly positive. -/
theorem exponentialEntry_smul_pos_of_irreducible
    (B : Matrix S S ℝ) (hB : B.IsIrreducible)
    (t : ℝ) (ht : 0 < t) :
    ∀ i j, 0 < Matrix.exponentialEntry (t • B) i j := by
  intro i j
  obtain ⟨n, _hn0, hn⟩ :=
    ((Matrix.isIrreducible_iff_exists_pow_pos hB.nonneg).1 hB) i j
  have hscaled : Matrix.EntrywiseNonnegative (t • B) := by
    intro a b
    exact mul_nonneg ht.le (hB.nonneg a b)
  apply exponentialEntry_pos_of_power_pos (t • B) hscaled i j n
  rw [smul_pow]
  exact mul_pos (pow_pos ht n) hn

/-- At every positive time, an irreducible Metzler matrix has a strictly
positive exponential kernel. -/
theorem exponentialEntry_smul_pos_of_irreducibleMetzler
    (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A)
    (t : ℝ) (ht : 0 < t) :
    ∀ i j, 0 < Matrix.exponentialEntry (t • A) i j := by
  rw [exponentialEntry_eq_shift A (canonicalDiagonalShift A) t]
  intro i j
  exact mul_pos (Real.exp_pos _)
    (exponentialEntry_smul_pos_of_irreducible
      (diagonalShift A (canonicalDiagonalShift A)) hA t ht i j)

/-- Perron--Frobenius existence for a finite irreducible Metzler matrix,
obtained from the canonical nonnegative scalar shift and transported back to
the original generator. -/
theorem IsIrreducibleMetzler.exists_pos_eigenvector
    [Nonempty S] (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A) :
    ∃ (psi : ℝ) (r : S → ℝ), (∀ i, 0 < r i) ∧
      A.mulVec r = psi • r := by
  let c := canonicalDiagonalShift A
  have hAI : (diagonalShift A c).IsIrreducible := by
    simpa [c, IsIrreducibleMetzler] using hA
  obtain ⟨rho, r, _hrho, hr, heig⟩ :=
    Matrix.IsIrreducible.exists_pos_eigenvector hAI
  refine ⟨rho - c, r, hr, ?_⟩
  rw [diagonalShift_mulVec] at heig
  funext i
  have hi := congrFun heig i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  linarith

/-- The Metzler Perron exponent is the unique exponent admitting a strictly
positive right eigenvector. -/
theorem IsIrreducibleMetzler.eigenvalue_eq_of_pos_eigenvectors
    [Nonempty S] (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A)
    {psi psi' : ℝ} {r r' : S → ℝ}
    (hr : ∀ i, 0 < r i) (hr' : ∀ i, 0 < r' i)
    (heig : A.mulVec r = psi • r)
    (heig' : A.mulVec r' = psi' • r') : psi = psi' := by
  let c := canonicalDiagonalShift A
  have hAI : (diagonalShift A c).IsIrreducible := by
    simpa [c, IsIrreducibleMetzler] using hA
  have hshift : (diagonalShift A c).mulVec r = (psi + c) • r := by
    rw [diagonalShift_mulVec, heig]
    module
  have hshift' : (diagonalShift A c).mulVec r' = (psi' + c) • r' := by
    rw [diagonalShift_mulVec, heig']
    module
  have heq := Matrix.IsIrreducible.eigenvalue_eq_of_pos_eigenvectors
    hAI hr hr' hshift hshift'
  linarith

/-- The eigenspace at a Metzler Perron exponent is one-dimensional. -/
theorem IsIrreducibleMetzler.exists_eq_smul_of_mulVec_eq_smul
    [Nonempty S] (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A)
    {psi : ℝ} {r y : S → ℝ} (hr : ∀ i, 0 < r i)
    (hrEig : A.mulVec r = psi • r)
    (hyEig : A.mulVec y = psi • y) : ∃ a : ℝ, y = a • r := by
  let c := canonicalDiagonalShift A
  have hAI : (diagonalShift A c).IsIrreducible := by
    simpa [c, IsIrreducibleMetzler] using hA
  have hshiftR :
      (diagonalShift A c).mulVec r = (psi + c) • r := by
    rw [diagonalShift_mulVec, hrEig]
    module
  have hshiftY :
      (diagonalShift A c).mulVec y = (psi + c) • y := by
    rw [diagonalShift_mulVec, hyEig]
    module
  exact Matrix.IsIrreducible.exists_eq_smul_of_mulVec_eq_smul
    (r := psi + c) (x := r) (y := y) hAI hr hshiftR hshiftY

/-- The protected finite Markov tilt inherits the complete strict-kernel and
Perron package as soon as its canonical nonnegative shift is irreducible. -/
theorem tiltedGenerator_strictKernel_and_perron
    [Nonempty S] (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hirr : IsIrreducibleMetzler (DrivenProcess.tilt L v g k)) :
    (∀ t : ℝ, 0 < t → ∀ i j,
      0 < Matrix.exponentialEntry
        (t • DrivenProcess.tilt L v g k) i j) ∧
      ∃ (psi : ℝ) (r : S → ℝ), (∀ i, 0 < r i) ∧
        (DrivenProcess.tilt L v g k).mulVec r = psi • r := by
  constructor
  · intro t ht
    exact exponentialEntry_smul_pos_of_irreducibleMetzler
      (DrivenProcess.tilt L v g k) hirr t ht
  · exact hirr.exists_pos_eigenvector (DrivenProcess.tilt L v g k)

end MetzlerExponentialPositivity
end NCG
