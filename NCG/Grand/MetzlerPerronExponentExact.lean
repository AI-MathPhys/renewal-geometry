/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.IrreducibleMetzlerSCGFExact
import NCG.Lorentz.PerronPressure

/-!
# Exact Perron exponent of an irreducible Metzler matrix

The repository implements the spectral radius of a nonnegative matrix by the
Gelfand--Fekete growth rate `NCG.pRad`.  A Metzler matrix becomes nonnegative
after its canonical scalar diagonal shift.  This file therefore gives a
canonical, non-circular formula for its Perron exponent and identifies the
automatic finite-state SCGF limit with that formula.
-/

open Matrix Finset Filter Topology
open scoped BigOperators

noncomputable section

namespace NCG.MetzlerPerronExponent

variable {S : Type*} [Fintype S] [DecidableEq S]

open MetzlerExponentialPositivity PerronSCGFSandwich

/-- The Perron exponent of a Metzler matrix, defined as the Perron radius of
its canonical nonnegative shift, translated back by that scalar shift. -/
def exponent (A : Matrix S S ℝ) : ℝ :=
  NCG.pRad (diagonalShift A (canonicalDiagonalShift A)) -
    canonicalDiagonalShift A

/-- The canonical scalar shift is unchanged by transposition. -/
@[simp] theorem canonicalDiagonalShift_transpose (A : Matrix S S ℝ) :
    canonicalDiagonalShift Aᵀ = canonicalDiagonalShift A := by
  simp [canonicalDiagonalShift]

/-- Scalar diagonal shifting commutes with transposition. -/
@[simp] theorem diagonalShift_transpose (A : Matrix S S ℝ) (c : ℝ) :
    (diagonalShift A c)ᵀ = diagonalShift Aᵀ c := by
  ext i j
  simp [diagonalShift, Matrix.one_apply, eq_comm]

/-- Canonical Metzler irreducibility is invariant under transposition. -/
theorem isIrreducibleMetzler_transpose (A : Matrix S S ℝ)
    (hA : IsIrreducibleMetzler A) : IsIrreducibleMetzler Aᵀ := by
  unfold IsIrreducibleMetzler at hA ⊢
  simpa using hA.transpose

/-- The shifted Gelfand--Fekete radius supplies a strictly positive right
eigenvector at the canonical Metzler exponent. -/
theorem exists_positive_eigenvector
    [Nonempty S] (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A) :
    ∃ r : S → ℝ, (∀ i, 0 < r i) ∧ A.mulVec r = exponent A • r := by
  let c := canonicalDiagonalShift A
  have hshift : (diagonalShift A c).IsIrreducible := by
    simpa [c, IsIrreducibleMetzler] using hA
  obtain ⟨r, hr, heig⟩ :=
    NCG.exists_pRad_eigenvector_of_isIrreducible hshift
  refine ⟨r, hr, ?_⟩
  rw [diagonalShift_mulVec] at heig
  funext i
  have hi := congrFun heig i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  unfold exponent
  change A.mulVec r i =
    (NCG.pRad (diagonalShift A c) - c) * r i
  linarith

/-- Every strictly positive right eigenvector has the canonical shifted-radius
exponent.  This is the exact spectral identification used by the SCGF. -/
theorem eigenvalue_eq_exponent
    [Nonempty S] (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A)
    {psi : ℝ} {r : S → ℝ} (hr : ∀ i, 0 < r i)
    (heig : A.mulVec r = psi • r) : psi = exponent A := by
  let c := canonicalDiagonalShift A
  have hshift : (diagonalShift A c).IsIrreducible := by
    simpa [c, IsIrreducibleMetzler] using hA
  have hshiftEig :
      (diagonalShift A c).mulVec r = (psi + c) • r := by
    rw [diagonalShift_mulVec, heig]
    module
  have hpRad := NCG.eigenvalue_eq_pRad_of_isIrreducible
    hshift hr hshiftEig
  unfold exponent
  change psi = NCG.pRad (diagonalShift A c) - c
  linarith

/-- The eigenspace at the canonical Metzler exponent is one-dimensional. -/
theorem eigenspace_is_one_dimensional
    [Nonempty S] (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A)
    {r y : S → ℝ} (hr : ∀ i, 0 < r i)
    (hrEig : A.mulVec r = exponent A • r)
    (hyEig : A.mulVec y = exponent A • y) :
    ∃ a : ℝ, y = a • r :=
  hA.exists_eq_smul_of_mulVec_eq_smul A hr hrEig hyEig

/-- An irreducible Metzler matrix has strictly positive right and left Perron
vectors which can be normalized to have pairing one. -/
theorem exists_normalized_positive_left_right_eigenvectors
    [Nonempty S] (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A) :
    ∃ (r ell : S → ℝ),
      (∀ i, 0 < r i) ∧ (∀ i, 0 < ell i) ∧
      A.mulVec r = exponent A • r ∧
      A.vecMul ell = exponent A • ell ∧ ell ⬝ᵥ r = 1 := by
  obtain ⟨r, hr, hrEig⟩ := exists_positive_eigenvector A hA
  have hAT := isIrreducibleMetzler_transpose A hA
  obtain ⟨ell, hell, hellEigT⟩ := exists_positive_eigenvector Aᵀ hAT
  have hellEig : A.vecMul ell = exponent Aᵀ • ell := by
    have hconvert : Aᵀ.mulVec ell = A.vecMul ell := by
      ext j
      simp [Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
    rw [hconvert] at hellEigT
    exact hellEigT
  have hq : 0 < ell ⬝ᵥ r := by
    exact Finset.sum_pos (fun i _ => mul_pos (hell i) (hr i))
      (Finset.univ_nonempty)
  have hexponents : exponent Aᵀ = exponent A := by
    have hpair : exponent A * (ell ⬝ᵥ r) =
        exponent Aᵀ * (ell ⬝ᵥ r) := by
      calc
        exponent A * (ell ⬝ᵥ r) = ell ⬝ᵥ A.mulVec r := by
          rw [hrEig]
          simp
        _ = A.vecMul ell ⬝ᵥ r := Matrix.dotProduct_mulVec ell A r
        _ = exponent Aᵀ * (ell ⬝ᵥ r) := by
          rw [hellEig]
          simp
    exact (mul_right_cancel₀ hq.ne' hpair.symm)
  have hellEigA : A.vecMul ell = exponent A • ell := by
    simpa [hexponents] using hellEig
  let q := ell ⬝ᵥ r
  let ellN : S → ℝ := q⁻¹ • ell
  refine ⟨r, ellN, hr, ?_, hrEig, ?_, ?_⟩
  · intro i
    exact mul_pos (inv_pos.mpr hq) (hell i)
  · change A.vecMul (q⁻¹ • ell) = exponent A • (q⁻¹ • ell)
    rw [Matrix.smul_vecMul, hellEigA]
    module
  · change (q⁻¹ • ell) ⬝ᵥ r = 1
    rw [smul_dotProduct]
    simp [q, hq.ne']

/-- The automatic finite-state logarithmic moment limit is exactly the
canonical shifted Gelfand--Fekete Perron exponent. -/
theorem tendsto_scaled_log_moment_exponent
    [Nonempty S] (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A)
    (p : S → ℝ) (hp : ∀ i, 0 ≤ p i) (hpne : ∃ i, 0 < p i) :
    Tendsto
      (fun T : ℝ => Real.log
        (perronMoment
          (fun t => Matrix.exponentialEntry (t • A)) p (fun _ => 1) T) / T)
      atTop (𝓝 (exponent A)) := by
  obtain ⟨psi, r, hr, heig, hlim⟩ :=
    IrreducibleMetzlerSCGF.exists_perronExponent_and_tendsto_scaled_log
      A hA p hp hpne
  have hpsi : psi = exponent A := eigenvalue_eq_exponent A hA hr heig
  simpa [hpsi] using hlim

/-- Protected state/jump tilts inherit the explicit shifted-radius SCGF. -/
theorem tiltedGenerator_SCGLimit_eq_exponent
    [Nonempty S] (L : Matrix S S ℝ) (_hL : DrivenProcess.IsGenerator L)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hirr : IsIrreducibleMetzler (DrivenProcess.tilt L v g k))
    (p : S → ℝ) (hp : ∀ i, 0 ≤ p i) (hpne : ∃ i, 0 < p i) :
    Tendsto
      (fun T : ℝ => Real.log
        (perronMoment
          (fun t => Matrix.exponentialEntry
            (t • DrivenProcess.tilt L v g k))
          p (fun _ => 1) T) / T)
      atTop (𝓝 (exponent (DrivenProcess.tilt L v g k))) :=
  tendsto_scaled_log_moment_exponent
    (DrivenProcess.tilt L v g k) hirr p hp hpne

end NCG.MetzlerPerronExponent
