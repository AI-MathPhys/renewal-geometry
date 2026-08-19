/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianImplicitEulerFamily
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Finite Hermitian heat multipliers are literal exponential semigroups

The canonical heat multiplier used by the finite spectral Euler estimate is identified here with
the Banach-algebra exponential of the Hermitian generator, first for matrices and then for the
corresponding continuous operators on Euclidean space.
-/

open Filter Topology Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.ImplicitEuler

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

local instance : NormedAlgebra ℚ (Matrix ι ι ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℚ
    (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
/-- The diagonal finite heat multiplier is the literal matrix exponential. -/
theorem finiteSpectralHeat_eq_exp_smul_diagonal (ν : ι → ℝ) (t : ℝ) :
    finiteSpectralHeat ν t =
      NormedSpace.exp (((-(t : ℂ)) •
        Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ))) : Matrix ι ι ℂ) := by
  have hscale :
      ((-(t : ℂ)) • Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ)) :
          Matrix ι ι ℂ) =
        Matrix.diagonal (fun i ↦ (((-(t * ν i) : ℝ)) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.smul_apply, Matrix.diagonal_apply, if_pos]
      push_cast
      ring
    · simp [Matrix.smul_apply, hij]
  rw [hscale, Matrix.exp_diagonal]
  unfold finiteSpectralHeat
  congr 1
  funext i
  rw [Pi.coe_exp]
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.ofReal_exp_ℝ_ℝ (-(t * ν i))

/-- Unitary spectral transport carries the diagonal heat exponential to the exponential of the
transported generator. -/
theorem finiteUnitarySpectralHeat_eq_exp_smul
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (t : ℝ) :
    finiteUnitarySpectralHeat U ν t =
      NormedSpace.exp (((-(t : ℂ)) •
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ)))) : Matrix ι ι ℂ) := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have henorm : ∀ X : Matrix ι ι ℂ, ‖e X‖ = ‖X‖ := by
    intro X
    change ‖(U : Matrix ι ι ℂ) * X * (star U : Matrix ι ι ℂ)‖ = ‖X‖
    rw [← Unitary.coe_star]
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  have hecont : Continuous e := by
    apply AddMonoidHomClass.continuous_of_bound e 1
    intro X
    rw [henorm]
    simp
  change e (finiteSpectralHeat ν t) =
    NormedSpace.exp ((-(t : ℂ)) • e
      (Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ))))
  rw [finiteSpectralHeat_eq_exp_smul_diagonal]
  rw [NormedSpace.map_exp e hecont]
  congr 1
  exact map_smul e (-(t : ℂ))
    (Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ)))

/-- The canonical spectral heat multiplier of a Hermitian matrix is its literal exponential
semigroup. -/
theorem finiteHermitianHeat_eq_exp_smul
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) :
    finiteHermitianHeat hA t =
      NormedSpace.exp (((-(t : ℂ)) • A) : Matrix ι ι ℂ) := by
  have hspectral :
      Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (Matrix.diagonal (fun i ↦ ((hA.eigenvalues i : ℝ) : ℂ))) = A := by
    calc
      _ = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
        apply congrArg (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary)
        ext i j
        by_cases hij : i = j
        · subst j
          simp only [Matrix.diagonal_apply, if_pos, Function.comp_apply]
          apply Complex.ext <;> simp [RCLike.ofReal]
        · simp [hij]
      _ = A := hA.spectral_theorem.symm
  unfold finiteHermitianHeat
  rw [finiteUnitarySpectralHeat_eq_exp_smul, hspectral]

/-- After bundling matrices as Euclidean continuous operators, the canonical heat multiplier is
still the literal Banach-algebra exponential. -/
theorem finiteHermitianHeatOperator_eq_exp_smul
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) :
    finiteHermitianHeatOperator hA t =
      NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) := by
  have hcont : Continuous (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) := by
    apply AddMonoidHomClass.continuous_of_bound
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) 1
    intro X
    change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) X‖ ≤ 1 * ‖X‖
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    simp
  unfold finiteHermitianHeatOperator
  rw [finiteHermitianHeat_eq_exp_smul]
  calc
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        (NormedSpace.exp ((-(t : ℂ)) • A)) =
      NormedSpace.exp (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        ((-(t : ℂ)) • A)) := NormedSpace.map_exp
          (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) hcont _
    _ = _ := by rw [map_smul]

/-- The literal implicit-Euler resolvent power approximates the literal finite semigroup, with a
dimension-free rate. -/
theorem norm_finiteHermitianEulerResolventOperator_sub_exp_le_inv_sqrt
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hk : 0 < k) :
    ‖finiteHermitianEulerResolventOperator A t k -
        NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)‖ ≤
      (Real.sqrt (k : ℝ))⁻¹ := by
  rw [← finiteHermitianHeatOperator_eq_exp_smul hA.1 t]
  exact norm_finiteHermitianEulerResolventOperator_sub_heat_le_inv_sqrt hA t k ht hk

/-- Zero-indexed semigroup estimate with the convergence-ready error rate. -/
theorem norm_finiteHermitianEulerResolventOperator_succ_sub_exp_le_errorRate
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t : ℝ) (m : ℕ) (ht : 0 ≤ t) :
    ‖finiteHermitianEulerResolventOperator A t (m + 1) -
        NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)‖ ≤ errorRate m := by
  simpa only [errorRate, Nat.cast_add, Nat.cast_one] using
    norm_finiteHermitianEulerResolventOperator_sub_exp_le_inv_sqrt
      hA t (m + 1) ht (Nat.succ_pos m)

end NCG.ImplicitEuler

namespace NCG.VaryingHilbert.System

universe u v

variable {ι : ℕ → Type u}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- For arbitrary changing finite cutoff dimensions, the literal resolvent powers approximate the
literal cutoff exponential semigroups uniformly on every set of nonnegative times. -/
theorem eventually_uniform_finiteHermitianEuler_exp_operatorNorm_error
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (s : Set ℝ) (hs : ∀ t ∈ s, 0 ≤ t) :
    ∀ m, ∀ᶠ n in atTop, ∀ t ∈ s,
      ‖NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n)) -
          NCG.ImplicitEuler.finiteHermitianEulerResolventOperator (A n) t (m + 1)‖ ≤
        NCG.ImplicitEuler.errorRate m := by
  intro m
  filter_upwards [] with n
  intro t ht
  rw [norm_sub_rev]
  exact NCG.ImplicitEuler.norm_finiteHermitianEulerResolventOperator_succ_sub_exp_le_errorRate
    (hA n) t m (hs t ht)

/-- The literal cutoff-semigroup estimate supplies the vectorwise approximation premise directly
for every strongly convergent varying-Hilbert source family. -/
theorem eventually_uniform_finiteHermitianEuler_exp_apply_dist
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (s : Set ℝ) (hs : ∀ t ∈ s, 0 ≤ t)
    (x : ∀ n, EuclideanSpace ℂ (ι n)) (xlim : H)
    (hx : J.StronglyConverges x xlim) :
    ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, ∀ t ∈ s,
      dist
        (J.embedding n
          (NormedSpace.exp ((-(t : ℂ)) •
            Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n)) (x n)))
        (J.embedding n
          (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
            (A n) t (m + 1) (x n))) < ε := by
  exact eventually_uniform_apply_dist_of_operatorNorm_error J
    (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
      Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n)))
    (fun m n (t : ℝ) ↦ NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
      (A n) t (m + 1))
    NCG.ImplicitEuler.errorRate s
    NCG.ImplicitEuler.errorRate_tendsto_zero
    NCG.ImplicitEuler.errorRate_nonneg
    (eventually_uniform_finiteHermitianEuler_exp_operatorNorm_error A hA s hs)
    x xlim hx

end NCG.VaryingHilbert.System
