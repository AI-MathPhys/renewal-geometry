/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DrivenProcessExact
import NCG.Grand.FiniteHeatBathDobrushin

/-!
# Poisson uniformization of finite Metzler semigroups

This file isolates the uniformization mechanism needed by the finite
Feynman--Kac and large-deviation compiler. If `A` is Metzler and `rho > 0`
dominates every negative diagonal entry, then `K = I + rho⁻¹ A` is
entrywise nonnegative. Its Poissonized discrete evolution is exactly the
continuous semigroup:

`exp (-rho*t) * exp ((rho*t) K) = exp (t A)`.

The result applies directly to the protected tilted generator `B_k`, which is
Metzler even though it need not have zero row sums. This is the algebraic core
of uniformized finite-state Feynman--Kac and the source of the Poisson
jump-count domination used for exponential tightness.
-/

open Matrix Finset
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

namespace NCG.FiniteMetzlerUniformization

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The discrete kernel obtained by shifting and rescaling a matrix. -/
def uniformizedKernel (A : Matrix S S ℝ) (rho : ℝ) : Matrix S S ℝ :=
  1 + rho⁻¹ • A

/-- A canonical strictly positive rate dominating every negative diagonal
entry. The finite sum is deliberately simple and requires no chosen maximizer. -/
def dominatingRate (A : Matrix S S ℝ) : ℝ :=
  1 + ∑ i, |A i i|

theorem dominatingRate_pos (A : Matrix S S ℝ) :
    0 < dominatingRate A := by
  unfold dominatingRate
  have hsum : 0 ≤ ∑ i, |A i i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

theorem neg_diagonal_le_dominatingRate (A : Matrix S S ℝ) (i : S) :
    -A i i ≤ dominatingRate A := by
  have habs : -A i i ≤ |A i i| := neg_le_abs _
  have hsingle : |A i i| ≤ ∑ j, |A j j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (A j j)) (Finset.mem_univ i)
  unfold dominatingRate
  linarith

theorem uniformizedKernel_apply (A : Matrix S S ℝ) (rho : ℝ) (i j : S) :
    uniformizedKernel A rho i j =
      (if i = j then 1 else 0) + rho⁻¹ * A i j := by
  simp [uniformizedKernel, Matrix.one_apply]

/-- A positive shift dominating the negative diagonal makes the entire
uniformized kernel nonnegative. -/
theorem uniformizedKernel_nonnegative
    (A : Matrix S S ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hdiag : ∀ i, -A i i ≤ rho) :
    Matrix.EntrywiseNonnegative (uniformizedKernel A rho) := by
  intro i j
  rw [uniformizedKernel_apply]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have h := hdiag i
    have hinv : 0 < rho⁻¹ := inv_pos.mpr hrho
    have hscaled := mul_le_mul_of_nonneg_left h hinv.le
    field_simp [hrho.ne'] at hscaled ⊢
    linarith
  · rw [if_neg hij]
    simpa using mul_nonneg (inv_nonneg.mpr hrho.le) (hoff i j hij)

/-- If `A` has zero row sums, its uniformization is row-stochastic. -/
theorem uniformizedKernel_rowStochastic
    (A : Matrix S S ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hA : NCG.DrivenProcess.IsGenerator A)
    (hdiag : ∀ i, -A i i ≤ rho) :
    Matrix.RowStochastic (uniformizedKernel A rho) := by
  refine ⟨uniformizedKernel_nonnegative A rho hrho hA.offDiag_nonneg hdiag, ?_⟩
  intro i
  change ∑ j, ((if i = j then 1 else 0) + rho⁻¹ * A i j) = 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [hA.row_sum i]

/-- Canonical automatic nonnegative uniformization of any finite Metzler
matrix. -/
theorem canonicalUniformizedKernel_nonnegative
    (A : Matrix S S ℝ) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) :
    Matrix.EntrywiseNonnegative
      (uniformizedKernel A (dominatingRate A)) :=
  uniformizedKernel_nonnegative A (dominatingRate A)
    (dominatingRate_pos A) hoff (neg_diagonal_le_dominatingRate A)

/-- Canonical automatic stochastic uniformization of a finite generator. -/
theorem canonicalUniformizedKernel_rowStochastic
    (A : Matrix S S ℝ) (hA : NCG.DrivenProcess.IsGenerator A) :
    Matrix.RowStochastic (uniformizedKernel A (dominatingRate A)) :=
  uniformizedKernel_rowStochastic A (dominatingRate A)
    (dominatingRate_pos A) hA (neg_diagonal_le_dominatingRate A)

/-- Poissonization of a discrete matrix kernel. -/
def poissonizedMatrix (K : Matrix S S ℝ) (s : ℝ) : Matrix S S ℝ :=
  Real.exp (-s) • Matrix.exponentialEntry (s • K)

/-- Backward value of an `n`-step discrete path with terminal payoff `f`.
This recursive form avoids choosing coordinates for the intermediate path. -/
def terminalPathValue (K : Matrix S S ℝ) (f : S → ℝ) : ℕ → S → ℝ
  | 0, x => f x
  | n + 1, x => ∑ y, K x y * terminalPathValue K f n y

/-- The backward discrete path recursion is exactly the action of a matrix
power on the terminal payoff. -/
theorem terminalPathValue_eq_pow_mulVec
    (K : Matrix S S ℝ) (f : S → ℝ) :
    ∀ n : ℕ, terminalPathValue K f n = (K ^ n).mulVec f := by
  intro n
  induction n with
  | zero =>
      funext x
      simp [terminalPathValue]
  | succ n ih =>
      funext x
      change (K.mulVec (terminalPathValue K f n)) x =
        ((K ^ (n + 1)).mulVec f) x
      rw [ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- Choosing a point-mass terminal payoff selects the corresponding endpoint
entry of the matrix power. -/
theorem terminalPathValue_indicator_eq_pow_apply
    (K : Matrix S S ℝ) (n : ℕ) (i j : S) :
    terminalPathValue K (fun x => if x = j then 1 else 0) n i =
      (K ^ n) i j := by
  rw [terminalPathValue_eq_pow_mulVec]
  simp [Matrix.mulVec, dotProduct]

/-- The Poissonized matrix is literally its factorially weighted power
series, entry by entry. -/
theorem poissonizedMatrix_apply
    (K : Matrix S S ℝ) (s : ℝ) (i j : S) :
    poissonizedMatrix K s i j =
      ∑' n : ℕ, Real.exp (-s) * (s ^ n / n.factorial) * (K ^ n) i j := by
  unfold poissonizedMatrix Matrix.exponentialEntry
  change Real.exp (-s) *
      (∑' n : ℕ, (1 / (n.factorial : ℝ)) * ((s • K) ^ n) i j) = _
  simp only [smul_pow, Matrix.smul_apply, smul_eq_mul]
  calc
    Real.exp (-s) *
        (∑' n : ℕ, (1 / (n.factorial : ℝ)) *
          (s ^ n * (K ^ n) i j)) =
      Real.exp (-s) *
        (∑' n : ℕ, (s ^ n / n.factorial) * (K ^ n) i j) := by
          congr 1
          apply tsum_congr
          intro n
          ring
    _ = ∑' n : ℕ, Real.exp (-s) *
        ((s ^ n / n.factorial) * (K ^ n) i j) := tsum_mul_left.symm
    _ = ∑' n : ℕ, Real.exp (-s) * (s ^ n / n.factorial) *
        (K ^ n) i j := by
          apply tsum_congr
          intro n
          ring

/-- Exact uniformization identity for an arbitrary finite matrix. Positivity
is not needed for this algebraic equality. -/
theorem poissonized_uniformizedKernel_eq_exponentialEntry
    (A : Matrix S S ℝ) (rho t : ℝ) (hrho : rho ≠ 0) :
    poissonizedMatrix (uniformizedKernel A rho) (rho * t) =
      Matrix.exponentialEntry (t • A) := by
  have hsplit :
      (rho * t) • uniformizedKernel A rho =
        (rho * t) • (1 : Matrix S S ℝ) + t • A := by
    rw [uniformizedKernel, smul_add, smul_smul]
    congr 1
    field_simp [hrho]
  have hcomm : Commute ((rho * t) • (1 : Matrix S S ℝ)) (t • A) :=
    (Commute.one_left (t • A)).smul_left (rho * t)
  have hexponentialEntry (X : Matrix S S ℝ) :
      Matrix.exponentialEntry X = NormedSpace.exp X := by
    ext i j
    exact FiniteHeatBathDobrushin.exponentialEntry_eq_exp_apply X i j
  unfold poissonizedMatrix
  rw [hexponentialEntry, hexponentialEntry, hsplit,
    Matrix.exp_add_of_commute _ _ hcomm,
    FiniteHeatBathDobrushin.exp_smul_matrix_one]
  have hscalar : Real.exp (-(rho * t)) * Real.exp (rho * t) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [smul_mul_assoc, Matrix.one_mul]
  ext i j
  change Real.exp (-(rho * t)) *
      (Real.exp (rho * t) * NormedSpace.exp (t • A) i j) =
    NormedSpace.exp (t • A) i j
  rw [← mul_assoc, hscalar, one_mul]

/-- The exact factorially weighted power expansion of the continuous
semigroup after uniformization. -/
theorem exponentialEntry_eq_poisson_power_sum
    (A : Matrix S S ℝ) (rho t : ℝ) (hrho : rho ≠ 0)
    (i j : S) :
    Matrix.exponentialEntry (t • A) i j =
      ∑' n : ℕ, Real.exp (-(rho * t)) *
        ((rho * t) ^ n / n.factorial) *
        (uniformizedKernel A rho ^ n) i j := by
  rw [← poissonized_uniformizedKernel_eq_exponentialEntry A rho t hrho,
    poissonizedMatrix_apply]

/-- Endpoint version of exact Poisson uniformization. The `n`th summand is
the backward value of the uniformized `n`-step path with endpoint fixed at
`j`. -/
theorem exponentialEntry_eq_poisson_endpoint_value
    (A : Matrix S S ℝ) (rho t : ℝ) (hrho : rho ≠ 0)
    (i j : S) :
    Matrix.exponentialEntry (t • A) i j =
      ∑' n : ℕ, Real.exp (-(rho * t)) *
        ((rho * t) ^ n / n.factorial) *
        terminalPathValue (uniformizedKernel A rho)
          (fun x => if x = j then 1 else 0) n i := by
  rw [exponentialEntry_eq_poisson_power_sum A rho t hrho i j]
  apply tsum_congr
  intro n
  rw [terminalPathValue_indicator_eq_pow_apply]

/-- Arbitrary terminal payoffs are reconstructed from the endpoint path
values. This is the finite-state terminal-function form used by
Feynman--Kac. -/
theorem exponentialEntry_mulVec_eq_poisson_endpoint_sum
    (A : Matrix S S ℝ) (rho t : ℝ) (hrho : rho ≠ 0)
    (f : S → ℝ) (i : S) :
    Matrix.mulVec (Matrix.exponentialEntry (t • A)) f i =
      ∑ j, (∑' n : ℕ, Real.exp (-(rho * t)) *
        ((rho * t) ^ n / n.factorial) *
        terminalPathValue (uniformizedKernel A rho)
          (fun x => if x = j then 1 else 0) n i) * f j := by
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [exponentialEntry_eq_poisson_endpoint_value A rho t hrho i j]

/-- Every protected tilted generator is Metzler. -/
theorem tiltedGenerator_offDiagonal_nonnegative
    (L : Matrix S S ℝ) (hL : NCG.DrivenProcess.IsGenerator L)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    ∀ i j, i ≠ j → 0 ≤ NCG.DrivenProcess.tilt L v g k i j := by
  intro i j hij
  rw [NCG.DrivenProcess.tilt_apply_ne L v g k hij]
  exact mul_nonneg (hL.offDiag_nonneg i j hij) (Real.exp_pos _).le

/-- Exact Poisson uniformization of the protected tilted semigroup. -/
theorem tiltedGenerator_poissonization
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (k rho t : ℝ) (hrho : rho ≠ 0) :
    poissonizedMatrix
        (uniformizedKernel (NCG.DrivenProcess.tilt L v g k) rho)
        (rho * t) =
      Matrix.exponentialEntry (t • NCG.DrivenProcess.tilt L v g k) :=
  poissonized_uniformizedKernel_eq_exponentialEntry
    (NCG.DrivenProcess.tilt L v g k) rho t hrho

/-- The canonical shifted kernel of a protected tilt is automatically
entrywise nonnegative. -/
theorem canonicalTiltedKernel_nonnegative
    (L : Matrix S S ℝ) (hL : NCG.DrivenProcess.IsGenerator L)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    Matrix.EntrywiseNonnegative
      (uniformizedKernel (NCG.DrivenProcess.tilt L v g k)
        (dominatingRate (NCG.DrivenProcess.tilt L v g k))) :=
  canonicalUniformizedKernel_nonnegative _
    (tiltedGenerator_offDiagonal_nonnegative L hL v g k)

/-- Premise-free Poisson uniformization of a protected tilt using its
canonical dominating rate. -/
theorem tiltedGenerator_canonical_poissonization
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (k t : ℝ) :
    poissonizedMatrix
        (uniformizedKernel (NCG.DrivenProcess.tilt L v g k)
          (dominatingRate (NCG.DrivenProcess.tilt L v g k)))
        (dominatingRate (NCG.DrivenProcess.tilt L v g k) * t) =
      Matrix.exponentialEntry (t • NCG.DrivenProcess.tilt L v g k) :=
  tiltedGenerator_poissonization L v g k
    (dominatingRate (NCG.DrivenProcess.tilt L v g k)) t
    (dominatingRate_pos _).ne'

end NCG.FiniteMetzlerUniformization
