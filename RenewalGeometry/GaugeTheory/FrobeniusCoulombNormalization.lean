/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.FiniteCoulombNormalization

/-!
# The Frobenius metric and finite Coulomb normalization for `U(N)`
  (instantiation and non-vacuity of `thm:finite-Coulomb-normalization`)

For complex matrices with the operator norm (a C*-algebra, gauge group `U(N)`), the Frobenius
identification `frobE : Matrix m m ℂ ≃L[ℝ] EuclideanSpace ℂ (m × m)` carries the invariant
Lie-algebra metric `⟪X, Y⟫ = Re tr(X^* Y)` (`inner_frobE`).  It is invariant under unitary
conjugation (`frobE_conj_unitary`) and infinitesimally invariant on skew-Hermitian matrices
(`inner_frobE_commutator`), i.e. it satisfies the metric hypotheses of
`FiniteCoulomb.finite_coulomb_normalization`, which is therefore instantiated for `U(N)`
(`finite_coulomb_normalization_unitary`).  The hypotheses of the theorem are satisfiable
(the zero seed, `exists_coulomb_zero_seed`).
-/

open NormedSpace Finset

namespace RenewalGeometry.FrobeniusCoulomb

open scoped Matrix.Norms.L2Operator
open FiniteCoulomb CoulombApriori

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The Frobenius identification of matrices with `ℂ^{m × m}` as a real linear equivalence. -/
def frobLin : Matrix m m ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (m × m) :=
  ((Matrix.ofLinearEquiv ℝ).symm.trans (LinearEquiv.curry ℝ ℂ m m).symm).trans
    (WithLp.linearEquiv 2 ℝ (m × m → ℂ)).symm

/-- The Frobenius identification `Matrix m m ℂ ≃L[ℝ] EuclideanSpace ℂ (m × m)`. -/
def frobE : Matrix m m ℂ ≃L[ℝ] EuclideanSpace ℂ (m × m) :=
  (frobLin (m := m)).toContinuousLinearEquiv

omit [DecidableEq m] in
theorem frobE_apply (X : Matrix m m ℂ) (p : m × m) : (frobE X) p = X p.1 p.2 := rfl

/-- `⟪frobE X, frobE Y⟫ = Re tr(X^* Y)`. -/
theorem inner_frobE (X Y : Matrix m m ℂ) :
    inner ℝ (frobE X) (frobE Y) = (Matrix.trace (X.conjTranspose * Y)).re := by
  simp only [PiLp.inner_apply, frobE_apply]
  simp [Complex.inner, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Complex.re_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem norm_frobE_sq (X : Matrix m m ℂ) :
    ‖frobE X‖ ^ 2 = (Matrix.trace (X.conjTranspose * X)).re := by
  rw [← real_inner_self_eq_norm_sq, inner_frobE]

/-- **Unitary invariance of the Frobenius metric**: `‖U X U^*‖_F = ‖X‖_F`. -/
theorem frobE_conj_unitary (U : Matrix m m ℂ) (hU : U ∈ unitary (Matrix m m ℂ))
    (X : Matrix m m ℂ) : ‖frobE (U * X * star U)‖ = ‖frobE X‖ := by
  have h1 : star U * U = 1 := Unitary.star_mul_self_of_mem hU
  have e : (U * X * star U).conjTranspose * (U * X * star U) =
      U * (X.conjTranspose * X) * star U := by
    rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose]
    simp only [star_mul, star_star, mul_assoc]
    rw [← mul_assoc (star U) U, h1, one_mul]
  have htr : Matrix.trace (U * (X.conjTranspose * X) * star U) =
      Matrix.trace (X.conjTranspose * X) := by
    rw [Matrix.trace_mul_comm, ← mul_assoc, h1, one_mul]
  have hsq : ‖frobE (U * X * star U)‖ ^ 2 = ‖frobE X‖ ^ 2 := by
    rw [norm_frobE_sq, norm_frobE_sq, e, htr]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- **Infinitesimal invariance**: `⟪a, [a, u]⟫_F = 0` for skew-Hermitian `a`. -/
theorem inner_frobE_commutator (a : Matrix m m ℂ) (ha : star a = -a) (u : Matrix m m ℂ) :
    inner ℝ (frobE a) (frobE (a * u - u * a)) = 0 := by
  rw [inner_frobE, ← Matrix.star_eq_conjTranspose, ha, mul_sub, Matrix.trace_sub]
  have : Matrix.trace (-a * (u * a)) = Matrix.trace (-a * (a * u)) := by
    rw [← mul_assoc, Matrix.trace_mul_comm (-a * u) a]
    congr 1
    noncomm_ring
  rw [this, sub_self, Complex.zero_re]

/-- `frobE` as a continuous linear map. -/
abbrev frobT (m : Type*) [Fintype m] [DecidableEq m] :
    Matrix m m ℂ →L[ℝ] EuclideanSpace ℂ (m × m) := (frobE (m := m) : _)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- **`thm:finite-Coulomb-normalization` for the gauge group `U(N)`** with the Frobenius metric:
the metric hypotheses of `FiniteCoulomb.finite_coulomb_normalization` hold, so for every
`ε_* > 0` there are `ε_c, C_c > 0` independent of the number of sites and of the mesh (at fixed
side `L`) such that every small skew-Hermitian seed admits a unitary site gauge in exact discrete
Coulomb gauge with the estimate `eq:native-Coulomb-estimate`. -/
theorem finite_coulomb_normalization_unitary (N : ℕ) [NeZero N] (hι : Fintype.card ι = 4)
    {L : ℝ} (hL : 0 < L) {εstar : ℝ} (hεstar : 0 < εstar) :
    type_of% (finite_coulomb_normalization (ι := ι) (frobE (m := Fin N)) hι
      (fun U hU X => frobE_conj_unitary U hU X) (fun a ha u => inner_frobE_commutator a ha u)
      hL hεstar) :=
  finite_coulomb_normalization (ι := ι) (frobE (m := Fin N)) hι
    (fun U hU X => frobE_conj_unitary U hU X) (fun a ha u => inner_frobE_commutator a ha u) hL
    hεstar

theorem oneL4_zero {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T] {n : ℕ} [NeZero n] (h : ℝ) :
    oneL4 h (frobT T) (0 : Fin 4 → (Fin 4 → ZMod n) → Matrix T T ℂ) = 0 := by
  have hb : ∀ μ, bar (frobT T) (0 : Fin 4 → (Fin 4 → ZMod n) → Matrix T T ℂ) μ = 0 := by
    intro μ; funext x; simp [bar]
  simp only [oneL4, hb]
  simp [GridSobolev.gridL4Norm]

theorem curvL2_zero {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T] {n : ℕ} [NeZero n] (h : ℝ) :
    curvL2 h (frobT T) (0 : Fin 4 → (Fin 4 → ZMod n) → Matrix T T ℂ) = 0 := by
  have hc : ∀ μ ν x, CurvatureSplit.curvature h
      (0 : Fin 4 → (Fin 4 → ZMod n) → Matrix T T ℂ) μ ν x = 0 := by
    intro μ ν x
    simp only [CurvatureSplit.curvature, CurvatureSplit.plaquette, Pi.zero_apply, smul_zero,
      neg_zero, NormedSpace.exp_zero, mul_one, SeriesLogChart.logChart_one]
  simp only [curvL2, packetL2, hc, map_zero]
  simp [GridSobolev.gridL2Norm, periodicHodgeNormSq]

/-- Non-vacuity: the zero seed satisfies the smallness hypothesis, so the theorem produces a
Coulomb representative (here for `U(1)`, four directions, any grid). -/
theorem exists_coulomb_zero_seed (n : ℕ) [NeZero n] {h : ℝ} (hh : 0 < h) :
    ∃ q : (Fin 4 → ZMod n) → Matrix (Fin 1) (Fin 1) ℂ, (∀ x, q x ∈ unitary _) ∧
      periodicHodgeCodiff h GridSobolev.gridStep (bar (frobT (Fin 1))
        (linkA h (0 : Fin 4 → (Fin 4 → ZMod n) → Matrix (Fin 1) (Fin 1) ℂ) 1 q)) = 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨εc, Cc, hεc, -, H⟩ := finite_coulomb_normalization_unitary (ι := Fin 4) 1 (by simp)
    (L := n * h) (by positivity) one_pos
  obtain ⟨q, hq, -, -, hcod, -, -, -⟩ := H n h hh rfl 0 (fun μ x => by simp)
    (by rw [oneL4_zero, curvL2_zero, add_zero]; exact hεc.le)
  exact ⟨q, hq, hcod⟩

end

end RenewalGeometry.FrobeniusCoulomb
