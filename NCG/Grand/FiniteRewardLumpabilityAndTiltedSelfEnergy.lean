/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CoarseAndHiddenEntropyProduction
import NCG.Gravity.RateFunction
import NCG.Lorentz.PerronExistence
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Finite reward lumpability and tilted self-energy

Coefficient extraction for a finite exponential tilt family, universal tilted
closure through a quotient projection, the complementary Schur self-energy,
and the exact cross-block residual criterion.
-/

open Finset Matrix

namespace NCG
namespace FiniteRewardLumpabilityAndTiltedSelfEnergy

theorem exponential_second_difference (gamma : ℝ) (n : ℕ) :
    Real.exp (((n + 2 : ℕ) : ℝ) * gamma) -
        2 * Real.exp (((n + 1 : ℕ) : ℝ) * gamma) +
        Real.exp ((n : ℝ) * gamma) =
      (Real.exp gamma - 1) ^ 2 * (Real.exp gamma) ^ n := by
  rw [show ((n + 2 : ℕ) : ℝ) * gamma = (n : ℝ) * gamma + gamma + gamma by
      push_cast; ring,
    show ((n + 1 : ℕ) : ℝ) * gamma = (n : ℝ) * gamma + gamma by
      push_cast; ring,
    ]
  simp only [Real.exp_add]
  rw [Real.exp_nat_mul]
  ring

/-- The functions `1`, `k`, and `exp(k gamma_j)-1` are linearly independent
for distinct nonzero real rewards.  The proof restricts to integer tilts,
takes a second finite difference to remove the affine part, and applies the
ordinary Vandermonde theorem to the distinct nodes `exp gamma_j`. -/
theorem exponential_affine_coefficients_unique
    {s : ℕ} (gamma : Fin s → ℝ)
    (hgamma : Function.Injective gamma) (hgamma0 : ∀ j, gamma j ≠ 0)
    (a0 a1 : ℝ) (a : Fin s → ℝ)
    (hzero : ∀ k : ℝ,
      a0 + k * a1 + ∑ j, (Real.exp (k * gamma j) - 1) * a j = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a = 0 := by
  let x : Fin s → ℝ := fun j => Real.exp (gamma j)
  have hxinj : Function.Injective x := by
    intro i j hij
    apply hgamma
    exact Real.exp_injective hij
  let v : Fin s → ℝ := fun j => (x j - 1) ^ 2 * a j
  have hvMoments : ∀ n : Fin s, ∑ j, v j * x j ^ (n : ℕ) = 0 := by
    intro n
    have h0 := hzero ((n : ℕ) : ℝ)
    have h1 := hzero (((n : ℕ) : ℝ) + 1)
    have h2 := hzero (((n : ℕ) : ℝ) + 2)
    have hdiffRaw :
        (∑ j, (Real.exp ((((n : ℕ) : ℝ) + 2) * gamma j) - 1) * a j) -
          2 * (∑ j, (Real.exp ((((n : ℕ) : ℝ) + 1) * gamma j) - 1) * a j) +
          ∑ j, (Real.exp (((n : ℕ) : ℝ) * gamma j) - 1) * a j = 0 := by
      linarith
    have hdiff :
        ∑ j, (Real.exp (((n : ℕ) : ℝ) * gamma j + gamma j + gamma j) -
              2 * Real.exp (((n : ℕ) : ℝ) * gamma j + gamma j) +
              Real.exp (((n : ℕ) : ℝ) * gamma j)) * a j = 0 := by
      calc
        _ = ∑ j, ((Real.exp ((((n : ℕ) : ℝ) + 2) * gamma j) - 1) * a j -
              2 * ((Real.exp ((((n : ℕ) : ℝ) + 1) * gamma j) - 1) * a j) +
              (Real.exp (((n : ℕ) : ℝ) * gamma j) - 1) * a j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show (((n : ℕ) : ℝ) + 2) * gamma j =
              ((n : ℕ) : ℝ) * gamma j + gamma j + gamma j by ring,
            show (((n : ℕ) : ℝ) + 1) * gamma j =
              ((n : ℕ) : ℝ) * gamma j + gamma j by ring]
          ring
        _ = (∑ j, (Real.exp ((((n : ℕ) : ℝ) + 2) * gamma j) - 1) * a j) -
            2 * (∑ j, (Real.exp ((((n : ℕ) : ℝ) + 1) * gamma j) - 1) * a j) +
            ∑ j, (Real.exp (((n : ℕ) : ℝ) * gamma j) - 1) * a j := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum]
        _ = 0 := hdiffRaw
    have hsecond (j : Fin s) :
        Real.exp (((n : ℕ) : ℝ) * gamma j + gamma j + gamma j) -
            2 * Real.exp (((n : ℕ) : ℝ) * gamma j + gamma j) +
            Real.exp (((n : ℕ) : ℝ) * gamma j) =
          (Real.exp (gamma j) - 1) ^ 2 * Real.exp (gamma j) ^ (n : ℕ) := by
      have h := exponential_second_difference (gamma j) (n : ℕ)
      rw [show ((((n : ℕ) + 2 : ℕ) : ℝ) * gamma j) =
          ((n : ℕ) : ℝ) * gamma j + gamma j + gamma j by
            push_cast; ring,
        show ((((n : ℕ) + 1 : ℕ) : ℝ) * gamma j) =
          ((n : ℕ) : ℝ) * gamma j + gamma j by
            push_cast; ring] at h
      exact h
    simp_rw [hsecond] at hdiff
    simpa [v, x, mul_assoc, mul_comm, mul_left_comm] using hdiff
  have hvzero : v = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hxinj hvMoments
  have hazero : a = 0 := by
    funext j
    have hvj : (x j - 1) ^ 2 * a j = 0 := by
      simpa [v] using congrFun hvzero j
    have hxone : x j - 1 ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      apply hgamma0 j
      apply Real.exp_injective
      simpa [x] using h
    exact (mul_eq_zero.mp hvj).resolve_left (pow_ne_zero 2 hxone)
  have ha0 : a0 = 0 := by
    simpa [hazero] using hzero 0
  have ha1 : a1 = 0 := by
    simpa [ha0, hazero] using hzero 1
  exact ⟨ha0, ha1, hazero⟩

/-- Algebraic matrix commutator. -/
def matrixCommutator {n : Type*} [Fintype n]
    (E T : Matrix n n ℝ) : Matrix n n ℝ := E * T - T * E

theorem matrixCommutator_add {n : Type*} [Fintype n]
    (E S T : Matrix n n ℝ) :
    matrixCommutator E (S + T) =
      matrixCommutator E S + matrixCommutator E T := by
  unfold matrixCommutator
  rw [Matrix.mul_add, Matrix.add_mul]
  abel

theorem matrixCommutator_smul {n : Type*} [Fintype n]
    (E T : Matrix n n ℝ) (a : ℝ) :
    matrixCommutator E (a • T) = a • matrixCommutator E T := by
  unfold matrixCommutator
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

theorem matrixCommutator_sum {n I : Type*} [Fintype n]
    (E : Matrix n n ℝ) (s : Finset I) (T : I → Matrix n n ℝ) :
    matrixCommutator E (∑ i ∈ s, T i) =
      ∑ i ∈ s, matrixCommutator E (T i) := by
  unfold matrixCommutator
  rw [Matrix.mul_sum, Matrix.sum_mul]
  exact (Finset.sum_sub_distrib (s := s)
    (f := fun i => E * T i) (g := fun i => T i * E)).symm

/-- Finite reward-tilted matrix in coefficient-bank form. -/
noncomputable def tiltedMatrix
    {n : Type*} [Fintype n] {s : ℕ}
    (L V : Matrix n n ℝ) (J : Fin s → Matrix n n ℝ)
    (gamma : Fin s → ℝ) (k : ℝ) : Matrix n n ℝ :=
  L + k • V + ∑ j, (Real.exp (k * gamma j) - 1) • J j

theorem matrixCommutator_tiltedMatrix
    {n : Type*} [Fintype n] {s : ℕ}
    (E L V : Matrix n n ℝ) (J : Fin s → Matrix n n ℝ)
    (gamma : Fin s → ℝ) (k : ℝ) :
    matrixCommutator E (tiltedMatrix L V J gamma k) =
      matrixCommutator E L + k • matrixCommutator E V +
        ∑ j, (Real.exp (k * gamma j) - 1) • matrixCommutator E (J j) := by
  unfold tiltedMatrix
  rw [matrixCommutator_add, matrixCommutator_add,
    matrixCommutator_smul,
    matrixCommutator_sum E Finset.univ]
  apply congrArg (fun X => matrixCommutator E L + k • matrixCommutator E V + X)
  apply Finset.sum_congr rfl
  intro j _
  rw [matrixCommutator_smul]

/-- Universal tilted closure is equivalent to the finite coefficient bank.
This is the exact matrix version of the manuscript's reward-lumpability
criterion. -/
theorem commutes_with_every_tilt_iff_coefficients
    {n : Type*} [Fintype n] {s : ℕ}
    (E L V : Matrix n n ℝ) (J : Fin s → Matrix n n ℝ)
    (gamma : Fin s → ℝ)
    (hgamma : Function.Injective gamma) (hgamma0 : ∀ j, gamma j ≠ 0) :
    (∀ k : ℝ, E * tiltedMatrix L V J gamma k =
        tiltedMatrix L V J gamma k * E) ↔
      E * L = L * E ∧ E * V = V * E ∧
        ∀ j, E * J j = J j * E := by
  constructor
  · intro htilt
    have hentry (p q : n) :
        matrixCommutator E L p q = 0 ∧
          matrixCommutator E V p q = 0 ∧
          (fun j => matrixCommutator E (J j) p q) = 0 := by
      apply exponential_affine_coefficients_unique gamma hgamma hgamma0
      intro k
      have hk : matrixCommutator E (tiltedMatrix L V J gamma k) = 0 := by
        unfold matrixCommutator
        rw [htilt k, sub_self]
      rw [matrixCommutator_tiltedMatrix] at hk
      have hpq := congrFun (congrFun hk p) q
      simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.sum_apply, Matrix.zero_apply] using hpq
    constructor
    · apply sub_eq_zero.mp
      ext p q
      exact (hentry p q).1
    constructor
    · apply sub_eq_zero.mp
      ext p q
      exact (hentry p q).2.1
    · intro j
      apply sub_eq_zero.mp
      ext p q
      have hj := congrFun (hentry p q).2.2 j
      simpa [matrixCommutator] using hj
  · rintro ⟨hL, hV, hJ⟩ k
    apply sub_eq_zero.mp
    change matrixCommutator E (tiltedMatrix L V J gamma k) = 0
    rw [matrixCommutator_tiltedMatrix]
    have hcL : matrixCommutator E L = 0 := sub_eq_zero.mpr hL
    have hcV : matrixCommutator E V = 0 := sub_eq_zero.mpr hV
    have hcJ : ∀ j, matrixCommutator E (J j) = 0 :=
      fun j => sub_eq_zero.mpr (hJ j)
    rw [hcL, hcV]
    simp [hcJ]

/-! ## The exact Hilbert--Schmidt cross-block residual -/

/-- Squared Hilbert--Schmidt norm of a real finite matrix, written entrywise. -/
def hilbertSchmidtSquare {m n : Type*} [Fintype m] [Fintype n]
    (T : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, (T i j) ^ 2

theorem hilbertSchmidtSquare_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (T : Matrix m n ℝ) : 0 ≤ hilbertSchmidtSquare T := by
  unfold hilbertSchmidtSquare
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (T i j)

theorem hilbertSchmidtSquare_eq_zero_iff
    {m n : Type*} [Fintype m] [Fintype n]
    (T : Matrix m n ℝ) : hilbertSchmidtSquare T = 0 ↔ T = 0 := by
  constructor
  · intro h
    ext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (T i j))).mp h
      i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (T i j))).mp hi j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hij
  · rintro rfl
    simp [hilbertSchmidtSquare]

/-- The sum of the squared Hilbert--Schmidt norms of the two off-diagonal
blocks cut out by `E` and its algebraic complement. -/
def crossBlockResidual {n : Type*} [Fintype n] [DecidableEq n]
    (E T : Matrix n n ℝ) : ℝ :=
  hilbertSchmidtSquare (E * T * (1 - E)) +
    hilbertSchmidtSquare ((1 - E) * T * E)

theorem crossBlockResidual_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (E T : Matrix n n ℝ) : 0 ≤ crossBlockResidual E T := by
  exact add_nonneg (hilbertSchmidtSquare_nonneg _)
    (hilbertSchmidtSquare_nonneg _)

theorem crossBlockResidual_eq_zero_iff_commutes
    {n : Type*} [Fintype n] [DecidableEq n]
    (E T : Matrix n n ℝ) (hE : E * E = E) :
    crossBlockResidual E T = 0 ↔ E * T = T * E := by
  let Q : Matrix n n ℝ := 1 - E
  have hEQ : E * Q = 0 := by
    rw [show Q = 1 - E by rfl, Matrix.mul_sub, Matrix.mul_one, hE, sub_self]
  have hQE : Q * E = 0 := by
    rw [show Q = 1 - E by rfl, Matrix.sub_mul, Matrix.one_mul, hE, sub_self]
  have hsplit : E + Q = 1 := by simp [Q]
  have hres : crossBlockResidual E T =
      hilbertSchmidtSquare (E * T * Q) +
        hilbertSchmidtSquare (Q * T * E) := by
    simp only [crossBlockResidual, Q]
  rw [hres]
  constructor
  · intro hzero
    have hleft0 : hilbertSchmidtSquare (E * T * Q) = 0 := by
      have h1 := hilbertSchmidtSquare_nonneg (E * T * Q)
      have h2 := hilbertSchmidtSquare_nonneg (Q * T * E)
      linarith
    have hright0 : hilbertSchmidtSquare (Q * T * E) = 0 := by
      have h1 := hilbertSchmidtSquare_nonneg (E * T * Q)
      have h2 := hilbertSchmidtSquare_nonneg (Q * T * E)
      linarith
    have hleft : E * T * Q = 0 :=
      (hilbertSchmidtSquare_eq_zero_iff _).mp hleft0
    have hright : Q * T * E = 0 :=
      (hilbertSchmidtSquare_eq_zero_iff _).mp hright0
    calc
      E * T = E * T * (E + Q) := by rw [hsplit, Matrix.mul_one]
      _ = E * T * E + E * T * Q := by rw [Matrix.mul_add]
      _ = E * T * E := by rw [hleft, add_zero]
      _ = (E + Q) * T * E := by
        rw [Matrix.add_mul, Matrix.add_mul, hright, add_zero]
      _ = T * E := by rw [hsplit, Matrix.one_mul]
  · intro hcomm
    have hleft : E * T * Q = 0 := by
      rw [hcomm, Matrix.mul_assoc, hEQ, Matrix.mul_zero]
    have hright : Q * T * E = 0 := by
      rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hQE,
        Matrix.zero_mul]
    rw [hleft, hright]
    simp [hilbertSchmidtSquare]

/-- Quantitative coefficient-bank defect: drift, potential, and every jump
coefficient contribute their two cross blocks. -/
def tiltedCoefficientResidual
    {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}
    (E L V : Matrix n n ℝ) (J : Fin s → Matrix n n ℝ) : ℝ :=
  crossBlockResidual E L + crossBlockResidual E V +
    ∑ j, crossBlockResidual E (J j)

theorem tiltedCoefficientResidual_nonneg
    {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}
    (E L V : Matrix n n ℝ) (J : Fin s → Matrix n n ℝ) :
    0 ≤ tiltedCoefficientResidual E L V J := by
  unfold tiltedCoefficientResidual
  exact add_nonneg
    (add_nonneg (crossBlockResidual_nonneg E L)
      (crossBlockResidual_nonneg E V))
    (Finset.sum_nonneg fun j _ => crossBlockResidual_nonneg E (J j))

/-- The coefficient residual vanishes exactly when every real tilt closes.
Thus the scalar residual is an exact, not merely sufficient, diagnostic. -/
theorem tiltedCoefficientResidual_eq_zero_iff_universal_closure
    {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}
    (E L V : Matrix n n ℝ) (J : Fin s → Matrix n n ℝ)
    (gamma : Fin s → ℝ)
    (hE : E * E = E)
    (hgamma : Function.Injective gamma) (hgamma0 : ∀ j, gamma j ≠ 0) :
    tiltedCoefficientResidual E L V J = 0 ↔
      ∀ k : ℝ, E * tiltedMatrix L V J gamma k =
        tiltedMatrix L V J gamma k * E := by
  rw [commutes_with_every_tilt_iff_coefficients E L V J gamma hgamma hgamma0]
  unfold tiltedCoefficientResidual
  constructor
  · intro hzero
    have hL0 : crossBlockResidual E L = 0 := by
      have hL := crossBlockResidual_nonneg E L
      have hV := crossBlockResidual_nonneg E V
      have hJ : 0 ≤ ∑ j, crossBlockResidual E (J j) :=
        Finset.sum_nonneg fun j _ => crossBlockResidual_nonneg E (J j)
      linarith
    have hV0 : crossBlockResidual E V = 0 := by
      have hL := crossBlockResidual_nonneg E L
      have hV := crossBlockResidual_nonneg E V
      have hJ : 0 ≤ ∑ j, crossBlockResidual E (J j) :=
        Finset.sum_nonneg fun j _ => crossBlockResidual_nonneg E (J j)
      linarith
    have hsum0 : ∑ j, crossBlockResidual E (J j) = 0 := by
      have hL := crossBlockResidual_nonneg E L
      have hV := crossBlockResidual_nonneg E V
      have hJ : 0 ≤ ∑ j, crossBlockResidual E (J j) :=
        Finset.sum_nonneg fun j _ => crossBlockResidual_nonneg E (J j)
      linarith
    refine ⟨(crossBlockResidual_eq_zero_iff_commutes E L hE).mp hL0,
      (crossBlockResidual_eq_zero_iff_commutes E V hE).mp hV0, ?_⟩
    intro j
    apply (crossBlockResidual_eq_zero_iff_commutes E (J j) hE).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => crossBlockResidual_nonneg E (J i))).mp hsum0
      j (Finset.mem_univ j)
  · rintro ⟨hL, hV, hJ⟩
    rw [(crossBlockResidual_eq_zero_iff_commutes E L hE).mpr hL,
      (crossBlockResidual_eq_zero_iff_commutes E V hE).mpr hV]
    simp only [zero_add]
    apply Finset.sum_eq_zero
    intro j _
    exact (crossBlockResidual_eq_zero_iff_commutes E (J j) hE).mpr (hJ j)

/-! ## Complementary Schur self-energy -/

/-- The hidden-block self-energy seen by the visible projection.  The matrix
`H` is the inverse of the hidden corner on the range of `1 - E`. -/
def tiltedSelfEnergy {n : Type*} [Fintype n] [DecidableEq n]
    (E B H : Matrix n n ℝ) : Matrix n n ℝ :=
  E * B * (1 - E) * H * (1 - E) * B * E

/-- The effective visible spectral matrix after eliminating the hidden
corner. -/
def visibleSchurMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℝ) (E B H : Matrix n n ℝ) : Matrix n n ℝ :=
  z • E - E * B * E - tiltedSelfEnergy E B H

/-- Exact Schur resolvent identity in corner form.  `hvisible` and `hhidden`
are precisely the two block rows of `(zI-B)G=I` after right multiplication
by `E`; `H` is a left inverse of the hidden corner; and `K` is a left inverse
of the visible Schur matrix.  The conclusion is the manuscript identity
`E G E = [zE-EBE-Σ(z)]⁻¹` without pretending that corner inverses are
ordinary full-space inverses. -/
theorem visible_resolvent_eq_schur_inverse
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℝ) (E B G H K : Matrix n n ℝ)
    (hE : E * E = E)
    (hvisible :
      (z • E - E * B * E) * (E * G * E) -
          E * B * (1 - E) * ((1 - E) * G * E) = E)
    (hhidden :
      (z • (1 - E) - (1 - E) * B * (1 - E)) *
          ((1 - E) * G * E) =
        (1 - E) * B * E * (E * G * E))
    (hHleft : H *
      (z • (1 - E) - (1 - E) * B * (1 - E)) = 1 - E)
    (hHcorner : H * (1 - E) = H)
    (hKleft : K * visibleSchurMatrix z E B H = E)
    (hKcorner : K * E = K) :
    E * G * E = K := by
  let Q : Matrix n n ℝ := 1 - E
  let D : Matrix n n ℝ := z • Q - Q * B * Q
  have hQ : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hE]
    abel
  have hhidden' : D * (Q * G * E) = Q * B * E * (E * G * E) := by
    simpa only [D, Q] using hhidden
  have hHleft' : H * D = Q := by simpa only [D, Q] using hHleft
  have hHcorner' : H * Q = H := by simpa only [Q] using hHcorner
  have hqge : Q * G * E = H * Q * B * E * (E * G * E) := by
    calc
      Q * G * E = (Q * Q) * G * E := by rw [hQ]
      _ = Q * (Q * G * E) := by simp only [Matrix.mul_assoc]
      _ = (H * D) * (Q * G * E) := by rw [hHleft']
      _ = H * (D * (Q * G * E)) := by rw [Matrix.mul_assoc]
      _ = H * (Q * B * E * (E * G * E)) := by rw [hhidden']
      _ = H * Q * B * E * (E * G * E) := by
        simp only [Matrix.mul_assoc]
  have hschur : visibleSchurMatrix z E B H * (E * G * E) = E := by
    rw [visibleSchurMatrix, tiltedSelfEnergy]
    rw [show (1 - E : Matrix n n ℝ) = Q by rfl] at hvisible ⊢
    rw [hqge] at hvisible
    simpa only [Matrix.sub_mul, Matrix.mul_assoc] using hvisible
  calc
    E * G * E = (E * E) * G * E := by rw [hE]
    _ = E * (E * G * E) := by simp only [Matrix.mul_assoc]
    _ = (K * visibleSchurMatrix z E B H) * (E * G * E) := by rw [hKleft]
    _ = K * (visibleSchurMatrix z E B H * (E * G * E)) := by
      rw [Matrix.mul_assoc]
    _ = K * E := by rw [hschur]
    _ = K := hKcorner

/-! ## Closure branch: quotient intertwining and Perron transport -/

/-- If `R C = I`, `E = C R`, and `B` commutes with `E`, then the fine
operator intertwines with the compressed operator `A = R B C`. -/
theorem fine_to_coarse_intertwining
    {u x : Type*} [Fintype u] [Fintype x]
    [DecidableEq u] [DecidableEq x]
    (B : Matrix x x ℝ) (C : Matrix x u ℝ) (R : Matrix u x ℝ)
    (hRC : R * C = 1) (hcomm : (C * R) * B = B * (C * R)) :
    B * C = C * (R * B * C) := by
  have hCRC : (C * R) * C = C := by
    rw [Matrix.mul_assoc, hRC, Matrix.mul_one]
  calc
    B * C = B * ((C * R) * C) := congrArg (fun T => B * T) hCRC.symm
    _ = (B * (C * R)) * C := (Matrix.mul_assoc B (C * R) C).symm
    _ = ((C * R) * B) * C := by rw [hcomm]
    _ = C * (R * B * C) := by simp only [Matrix.mul_assoc]

/-- The same hypotheses give the reverse intertwining through the decoder. -/
theorem coarse_to_fine_intertwining
    {u x : Type*} [Fintype u] [Fintype x]
    [DecidableEq u] [DecidableEq x]
    (B : Matrix x x ℝ) (C : Matrix x u ℝ) (R : Matrix u x ℝ)
    (hRC : R * C = 1) (hcomm : (C * R) * B = B * (C * R)) :
    R * B = (R * B * C) * R := by
  calc
    R * B = (R * C) * (R * B) := by rw [hRC, Matrix.one_mul]
    _ = R * ((C * R) * B) := by simp only [Matrix.mul_assoc]
    _ = R * (B * (C * R)) := by rw [hcomm]
    _ = (R * B * C) * R := by simp only [Matrix.mul_assoc]

/-- A coarse eigenvector lifts through `C` to a fine eigenvector on the
universal-closure branch. -/
theorem lift_compressed_eigenvector
    {u x : Type*} [Fintype u] [Fintype x]
    [DecidableEq u] [DecidableEq x]
    (B : Matrix x x ℝ) (C : Matrix x u ℝ) (R : Matrix u x ℝ)
    (hRC : R * C = 1) (hcomm : (C * R) * B = B * (C * R))
    (r : u → ℝ) (psi : ℝ)
    (hr : (R * B * C).mulVec r = psi • r) :
    B.mulVec (C.mulVec r) = psi • C.mulVec r := by
  rw [Matrix.mulVec_mulVec,
    fine_to_coarse_intertwining B C R hRC hcomm,
    ← Matrix.mulVec_mulVec, hr, Matrix.mulVec_smul]

/-- Under the standard Perron hypotheses, compression preserves the Perron
exponent.  Positivity of `C r` records that the coarse Perron mode lifts into
the positive fine cone; irreducibility makes that positive eigenvalue unique. -/
theorem compressed_perron_exponent_eq
    {u x : Type*} [Fintype u] [Fintype x] [Nonempty x]
    [DecidableEq u] [DecidableEq x]
    (B : Matrix x x ℝ) (C : Matrix x u ℝ) (R : Matrix u x ℝ)
    (hRC : R * C = 1) (hcomm : (C * R) * B = B * (C * R))
    (hBirr : B.IsIrreducible)
    (r : u → ℝ) (finePerronVector : x → ℝ)
    (coarseExponent fineExponent : ℝ)
    (hCr : ∀ i, 0 < C.mulVec r i)
    (hfinePos : ∀ i, 0 < finePerronVector i)
    (hcoarse : (R * B * C).mulVec r = coarseExponent • r)
    (hfine : B.mulVec finePerronVector =
      fineExponent • finePerronVector) :
    coarseExponent = fineExponent := by
  apply hBirr.eigenvalue_eq_of_pos_eigenvectors hCr hfinePos
  · exact lift_compressed_eigenvector B C R hRC hcomm r coarseExponent hcoarse
  · exact hfine

/-- Pointwise equality of fine and compressed Perron exponents on the closure
branch implies equality of their Legendre--Fenchel rate functions. -/
theorem perron_pressure_and_rate_function_coincide
    (fineExponent coarseExponent : ℝ → ℝ)
    (hexponent : ∀ k, fineExponent k = coarseExponent k) :
    fineExponent = coarseExponent ∧
      ∀ a, rateFunction fineExponent a = rateFunction coarseExponent a := by
  have hfun : fineExponent = coarseExponent := funext hexponent
  subst coarseExponent
  exact ⟨rfl, fun _ => rfl⟩

/-- Family form of the closure branch: for `Aₖ = R Bₖ C`, universal
commutation and the finite Perron hypotheses identify the fine and coarse
scaled cumulant generating functions, hence their rate functions. -/
theorem compressed_perron_pressures_and_rate_functions_coincide
    {u x : Type*} [Fintype u] [Fintype x] [Nonempty x]
    [DecidableEq u] [DecidableEq x]
    (B : ℝ → Matrix x x ℝ) (C : Matrix x u ℝ) (R : Matrix u x ℝ)
    (coarseVector : ℝ → u → ℝ) (fineVector : ℝ → x → ℝ)
    (coarseExponent fineExponent : ℝ → ℝ)
    (hRC : R * C = 1)
    (hcomm : ∀ k, (C * R) * B k = B k * (C * R))
    (hirr : ∀ k, (B k).IsIrreducible)
    (hCpos : ∀ k i, 0 < C.mulVec (coarseVector k) i)
    (hfinePos : ∀ k i, 0 < fineVector k i)
    (hcoarse : ∀ k, (R * B k * C).mulVec (coarseVector k) =
      coarseExponent k • coarseVector k)
    (hfine : ∀ k, (B k).mulVec (fineVector k) =
      fineExponent k • fineVector k) :
    fineExponent = coarseExponent ∧
      ∀ a, rateFunction fineExponent a = rateFunction coarseExponent a := by
  apply perron_pressure_and_rate_function_coincide
  intro k
  exact (compressed_perron_exponent_eq (B k) C R hRC (hcomm k) (hirr k)
    (coarseVector k) (fineVector k) (coarseExponent k) (fineExponent k)
    (hCpos k) (hfinePos k) (hcoarse k) (hfine k)).symm

end FiniteRewardLumpabilityAndTiltedSelfEnergy
end NCG
