/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MetzlerExponentialPositivityExact
import NCG.Grand.PerronSCGFSandwichExact

/-!
# Automatic SCGF limit for finite irreducible Metzler tilts

This file composes the finite Metzler Perron--Frobenius compiler with the
two-sided Perron sandwich.  No Perron eigenvalue or eigenvector is supplied by
the caller: canonical-shift irreducibility constructs them, strict positivity
of the exponential kernel supplies monotonicity, and the matrix exponential
series propagates the generator eigen-equation.
-/

open Matrix Finset Filter Topology
open scoped BigOperators

noncomputable section

namespace NCG.IrreducibleMetzlerSCGF

variable {S : Type*} [Fintype S] [DecidableEq S]

open MetzlerExponentialPositivity PerronSCGFSandwich

open scoped Matrix.Norms.Operator in
set_option backward.isDefEq.respectTransparency false in
/-- The coordinatewise matrix exponential propagates an arbitrary finite
matrix eigenvector.  Absolute summability comes from the Banach-algebra
exponential series, so no stochastic normalization is needed. -/
theorem exponentialEntry_smul_mulVec_eigenvector
    (A : Matrix S S ℝ) (r : S → ℝ) (psi t : ℝ)
    (heig : A.mulVec r = psi • r) :
    Matrix.mulVec (Matrix.exponentialEntry (t • A)) r =
      Real.exp (t * psi) • r := by
  ext i
  unfold Matrix.mulVec Matrix.exponentialEntry
  have hsummable (j : S) : Summable (fun n : ℕ =>
      ((1 / n.factorial : ℝ) * ((t • A) ^ n) i j) * r j) := by
    have hmatrix : Summable
        (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • A) ^ n) :=
      NormedSpace.expSeries_summable' (𝕂 := ℝ) (t • A)
    have hrow := (Pi.summable.mp hmatrix) i
    have hentry := (Pi.summable.mp hrow) j
    have hscalar : Summable (fun n : ℕ =>
        (1 / n.factorial : ℝ) * ((t • A) ^ n) i j) := by
      simpa [one_div] using hentry
    exact hscalar.mul_right (r j)
  change (∑ j, (∑' n : ℕ,
      (1 / n.factorial : ℝ) * ((t • A) ^ n) i j) * r j) =
        Real.exp (t * psi) * r i
  have htsum (j : S) :
      (∑' n : ℕ, (1 / n.factorial : ℝ) * ((t • A) ^ n) i j) * r j =
        ∑' n : ℕ,
          ((1 / n.factorial : ℝ) * ((t • A) ^ n) i j) * r j := by
    exact (tsum_mul_right).symm
  simp_rw [htsum]
  rw [(Summable.tsum_finsetSum (fun j _ => hsummable j)).symm]
  have hpow (n : ℕ) :
      Matrix.mulVec ((t • A) ^ n) r = (t * psi) ^ n • r := by
    rw [smul_pow, Matrix.smul_mulVec,
      Matrix.pow_mulVec_eigenvector A r psi heig n]
    ext v
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_pow]
    ring
  calc
    (∑' n : ℕ, ∑ j,
        ((1 / n.factorial : ℝ) * ((t • A) ^ n) i j) * r j) =
        ∑' n : ℕ, (1 / n.factorial : ℝ) * (t * psi) ^ n * r i := by
          apply tsum_congr
          intro n
          have hn := congrFun (hpow n) i
          simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hn
          calc
            (∑ j, (1 / ↑n.factorial * ((t • A) ^ n) i j) * r j) =
                (1 / ↑n.factorial) *
                  ∑ j, ((t • A) ^ n) i j * r j := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
            _ = (1 / ↑n.factorial) * ((t * psi) ^ n * r i) := by
                  have hn' :
                      (∑ j, ((t • A) ^ n) i j * r j) =
                        (t * psi) ^ n * r i := hn
                  rw [hn']
            _ = (1 / ↑n.factorial) * (t * psi) ^ n * r i := by ring
    _ = (∑' n : ℕ, (1 / n.factorial : ℝ) * (t * psi) ^ n) * r i := by
          rw [tsum_mul_right]
    _ = Real.exp (t * psi) * r i := by
          rw [Real.exp_eq_exp_ℝ,
            congrFun (NormedSpace.exp_eq_tsum ℝ) (t * psi)]
          congr 1
          apply tsum_congr
          intro n
          simp only [smul_eq_mul, one_div]

/-- A nonzero nonnegative initial weight pairs strictly positively with every
strictly positive Perron vector. -/
theorem positive_pairing_of_nonzero
    [Nonempty S] (p r : S → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpne : ∃ i, 0 < p i)
    (hr : ∀ i, 0 < r i) : 0 < ∑ i, p i * r i := by
  obtain ⟨i, hi⟩ := hpne
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hp j) (hr j).le)
    ⟨i, Finset.mem_univ i, mul_pos hi (hr i)⟩

/-- Automatic finite-state SCGF limit for an irreducible Metzler matrix.
The Perron exponent and vector are outputs rather than hypotheses. -/
theorem exists_perronExponent_and_tendsto_scaled_log
    [Nonempty S] (A : Matrix S S ℝ)
    (hirr : IsIrreducibleMetzler A)
    (p : S → ℝ) (hp : ∀ i, 0 ≤ p i) (hpne : ∃ i, 0 < p i) :
    ∃ (psi : ℝ) (r : S → ℝ),
      (∀ i, 0 < r i) ∧ A.mulVec r = psi • r ∧
      Tendsto
        (fun T : ℝ => Real.log
          (perronMoment
            (fun t => Matrix.exponentialEntry (t • A)) p (fun _ => 1) T) / T)
        atTop (𝓝 psi) := by
  obtain ⟨psi, r, hr, heig⟩ := hirr.exists_pos_eigenvector A
  refine ⟨psi, r, hr, heig, ?_⟩
  apply tendsto_scaled_log_perronMoment_one
    (fun t => Matrix.exponentialEntry (t • A)) p r psi hp hr
  · intro T hT i j
    exact (exponentialEntry_smul_pos_of_irreducibleMetzler
      A hirr T hT i j).le
  · intro T _hT
    exact exponentialEntry_smul_mulVec_eigenvector A r psi T heig
  · exact positive_pairing_of_nonzero p r hp hpne hr

/-- The manuscript's protected state/jump tilt is an immediate specialization
of the automatic finite irreducible-Metzler SCGF theorem. -/
theorem tiltedGenerator_exists_perronExponent_and_SCGLimit
    [Nonempty S] (L : Matrix S S ℝ) (_hL : DrivenProcess.IsGenerator L)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hirr : IsIrreducibleMetzler (DrivenProcess.tilt L v g k))
    (p : S → ℝ) (hp : ∀ i, 0 ≤ p i) (hpne : ∃ i, 0 < p i) :
    ∃ (psi : ℝ) (r : S → ℝ),
      (∀ i, 0 < r i) ∧
      (DrivenProcess.tilt L v g k).mulVec r = psi • r ∧
      Tendsto
        (fun T : ℝ => Real.log
          (perronMoment
            (fun t => Matrix.exponentialEntry
              (t • DrivenProcess.tilt L v g k))
            p (fun _ => 1) T) / T)
        atTop (𝓝 psi) :=
  exists_perronExponent_and_tendsto_scaled_log
    (DrivenProcess.tilt L v g k) hirr p hp hpne

end NCG.IrreducibleMetzlerSCGF
