/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# New SMST channel/derivation records (2026-08-07 tex update):
  formal cores for the locked-orbit polytope, provenance
  compiler, derivation conditioning, Hamiltonian tangent,
  channel Pythagoras, unitarity, and coherence records.
  See each ledger entry for its citation and disclosure.
-/

open Matrix Finset

namespace NCG

/-- Locked-orbit polytope: the boxed condition is exactly
nonemptiness of the boxed `D`-interval. -/
theorem orbit_polytope_interval (E A T : ℝ) :
    |E + A| + |2 * E - A| ≤ 3 * T
      ↔ -T + |E + A| ≤ 2 * T - |2 * E - A| := by
  constructor <;> intro h <;> linarith

/-- Provenance compiler clause (P1): the diagonal terminal
metric is PSD for nonnegative masses. -/
theorem provenance_metric_psd {c : Type*} [Fintype c]
    [DecidableEq c] (τ : c → ℝ) (hτ : ∀ i, 0 ≤ τ i)
    (x : c → ℝ) :
    0 ≤ x ⬝ᵥ (Matrix.diagonal τ).mulVec x := by
  have hdiag : (Matrix.diagonal τ).mulVec x
      = fun i => τ i * x i := by
    funext i
    rw [Matrix.mulVec_diagonal]
  rw [hdiag, dotProduct]
  refine Finset.sum_nonneg fun i _ => ?_
  have := hτ i
  have := mul_self_nonneg (x i)
  calc (0 : ℝ) ≤ τ i * (x i * x i) := by positivity
    _ = x i * (τ i * x i) := by ring

/-- Provenance-marginals countertheorem witness: two distinct
PSD Grams share the same diagonal marginals. -/
theorem same_marginal_distinct_gram :
    (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
        ≠ !![1, 1; 1, 1]
      ∧ (∀ i : Fin 2,
        (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i i
          = (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) i i) := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp at h01
  · intro i
    fin_cases i <;> simp

/-- Private-SM export: the homogeneous-tail rescaling is exact,
`s·(P/s) = P`. -/
theorem private_export_scaling {n m : Type*}
    (P : Matrix n m ℝ) (s : ℝ) (hs : s ≠ 0) :
    s • (s⁻¹ • P) = P := by
  rw [smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- Source-allocation kernel slice: a PSD-kernel vector has
vanishing quadratic form. -/
theorem psd_kernel_quadratic {n : Type*} [Fintype n]
    (R : Matrix n n ℂ) (x : n → ℂ) (hx : R.mulVec x = 0) :
    star x ⬝ᵥ R.mulVec x = 0 := by
  rw [hx]
  simp

/-- Invariant Einstein subspace: the observability kernel
`{x : R Pⁿ x = 0 ∀ n}` is `P`-invariant. -/
theorem invariant_subspace_characterization {V W : Type*}
    [AddCommGroup V] [AddCommGroup W] [Module ℝ V] [Module ℝ W]
    (P : V →ₗ[ℝ] V) (R : V →ₗ[ℝ] W) (x : V)
    (hx : ∀ n : ℕ, R ((P ^ n) x) = 0) (n : ℕ) :
    R ((P ^ n) (P x)) = 0 := by
  have := hx (n + 1)
  rwa [pow_succ, Module.End.mul_apply] at this

/-- Residual quotient: the induced propagator descends
canonically (re-export of the quotient universal property). -/
theorem residual_quotient_induced {V : Type*} [AddCommGroup V]
    [Module ℝ V] (K : Submodule ℝ V) (P : V →ₗ[ℝ] V)
    (h : K ≤ K.comap P) :
    (Submodule.mapQ K K P h).comp K.mkQ
      = K.mkQ.comp P := by
  exact Submodule.mapQ_mkQ K K P

/-- Inner-derivation conditioning, eigenvalue form: the boxed
identity `Σᵢⱼ(λᵢ-λⱼ)² = 2d·Σᵢ(λᵢ - λ̄)²`. -/
theorem inner_derivation_eigen_identity {d : ℕ} (hd : d ≠ 0)
    (l : Fin d → ℝ) :
    ∑ i, ∑ j, (l i - l j) ^ 2
      = 2 * d * ∑ i, (l i - (∑ j, l j) / d) ^ 2 := by
  have hdc : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hL : ∑ i, ∑ j, (l i - l j) ^ 2
      = 2 * d * ∑ i, l i ^ 2 - 2 * (∑ i, l i) ^ 2 := by
    have hexp : ∀ i, ∑ j, (l i - l j) ^ 2
        = d * l i ^ 2 - 2 * l i * ∑ j, l j
          + ∑ j, l j ^ 2 := by
      intro i
      have h1 : ∑ j, (l i - l j) ^ 2
          = ∑ j, (l i ^ 2 - 2 * l i * l j + l j ^ 2) :=
        Finset.sum_congr rfl fun j _ => by ring
      rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl fun i _ => hexp i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    rw [show ∑ i, 2 * l i * ∑ j, l j
      = 2 * (∑ i, l i) * ∑ j, l j from by
        rw [← Finset.sum_mul, ← Finset.mul_sum]]
    ring
  have hSm : (d : ℝ) * ((∑ j, l j) / d) = ∑ j, l j := by
    field_simp
  have hR : ∑ i, (l i - (∑ j, l j) / d) ^ 2
      = ∑ i, l i ^ 2
        - 2 * ((∑ j, l j) / d) * ∑ i, l i
        + d * ((∑ j, l j) / d) ^ 2 := by
    have hexp : ∀ i, (l i - (∑ j, l j) / d) ^ 2
        = l i ^ 2 - 2 * ((∑ j, l j) / d) * l i
          + ((∑ j, l j) / d) ^ 2 := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hexp i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.mul_sum]
    ring
  rw [hL, hR]
  linear_combination
    (2 * (∑ j, l j) - 2 * (d : ℝ) * ((∑ j, l j) / d)) * hSm

/-- Tangent-certificate uniqueness: a traceless scalar matrix
vanishes, so traceless Hamiltonians with equal derivations
agree. -/
theorem traceless_scalar_eq {n : Type*} [Fintype n]
    [DecidableEq n] [Nonempty n] (H K : Matrix n n ℂ) (c : ℂ)
    (hscalar : H - K = c • 1)
    (htr : Matrix.trace H = Matrix.trace K) : H = K := by
  have htr0 : Matrix.trace (H - K) = 0 := by
    rw [Matrix.trace_sub, htr, sub_self]
  rw [hscalar, Matrix.trace_smul, Matrix.trace_one] at htr0
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hc : c = 0 := by
    have := htr0
    rw [smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_right hcard
  have hHK := hscalar
  rw [hc, zero_smul] at hHK
  exact sub_eq_zero.mp hHK

/-- Channel-native tangent signs: the forward and reverse
tangents cancel exactly. -/
theorem channel_tangent_sign {n : Type*} [Fintype n]
    (H X : Matrix n n ℂ) :
    (-Complex.I) • (H * X - X * H)
        + Complex.I • (H * X - X * H) = 0 := by
  rw [← add_smul]
  simp

/-- Source-core leakage Pythagoras: an orthogonal split of a
synthesis splits its Gram trace exactly. -/
theorem projection_pythagoras {n m : Type*} [Fintype n]
    [DecidableEq n] [Fintype m] (P : Matrix n n ℂ) (X : Matrix n m ℂ)
    (hP : Pᴴ * P = P) (h1P : (1 - P)ᴴ * (1 - P) = 1 - P) :
    ((P * X)ᴴ * (P * X)).trace
        + (((1 - P) * X)ᴴ * ((1 - P) * X)).trace
      = (Xᴴ * X).trace := by
  have h1 : (P * X)ᴴ * (P * X) = Xᴴ * (P * X) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Pᴴ P X, hP]
  have h2 : ((1 - P) * X)ᴴ * ((1 - P) * X)
      = Xᴴ * ((1 - P) * X) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (1 - P)ᴴ (1 - P) X, h1P]
  rw [h1, h2, ← Matrix.trace_add, ← Matrix.mul_add,
    ← Matrix.add_mul]
  rw [show P + (1 - P) = (1 : Matrix n n ℂ) from by abel,
    Matrix.one_mul]

/-- Choi-purity of a rank-one (unitary) channel: the squared
trace saturates. -/
theorem rank_one_choi_purity {n : Type*} [Fintype n]
    (v : n → ℂ) :
    ((Matrix.vecMulVec v (star v))
        * Matrix.vecMulVec v (star v)).trace
      = (star v ⬝ᵥ v) * (Matrix.vecMulVec v (star v)).trace := by
  have hkey : Matrix.vecMulVec v (star v)
        * Matrix.vecMulVec v (star v)
      = (star v ⬝ᵥ v) • Matrix.vecMulVec v (star v) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply]
    simp only [Matrix.vecMulVec_apply]
    rw [show (∑ k, v i * star v k * (v k * star v j))
      = (∑ k, star v k * v k) * (v i * star v j) from by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring]
    rw [show (∑ k, star v k * v k) = star v ⬝ᵥ v from rfl,
      smul_eq_mul]
  rw [hkey, Matrix.trace_smul, smul_eq_mul]

/-- Axis-populations countertheorem mechanism: the ±θ
random-unitary average has the same axis populations as the
pulse itself. -/
theorem axis_population_degeneracy (θ : ℝ) :
    ((Real.cos θ) ^ 2 + (Real.cos (-θ)) ^ 2) / 2
      = (Real.cos θ) ^ 2 := by
  rw [Real.cos_neg]
  ring

end NCG
