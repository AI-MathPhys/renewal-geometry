/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import NCG.Grand.ZeroModeSaturationExact
import NCG.Grand.SMQGDivisorSafePositivityOrderExact

/-!
# Invertible and zero-safe chiral source hierarchy

Exact finite-dimensional machinery for `thm:SMQG-zero-safe`.

* the invertible branch is the matrix determinant lemma, with the physical
  covariance in the required order;
* every homogeneous coefficient is identified with the corresponding sum of
  principal minors (the exterior-grade coefficient), and coefficients above
  the source dimension vanish;
* the singular branch reuses the adapted zero-mode saturation theorem: lower
  degree is absent, the first saturated coefficient is the reduced hard
  determinant times the kernel/cokernel source line, and it is nonzero under
  source completeness;
* at a divisor the saturated coefficient cannot be normalized by the
  vanishing vacuum determinant, and its sign is tested directly.
-/

open Matrix Polynomial ExteriorAlgebra

namespace NCG
namespace ZeroSafeSourceHierarchy

variable {R E : Type*} [Fintype R] [Fintype E]
  [DecidableEq R] [DecidableEq E]

/-- The chiral source insertion determinant `Z_S(Q)`. -/
def chiralInsertion
    (S : Matrix R R ℂ) (Jminus Jplus : Matrix R E ℂ)
    (Q : Matrix E E ℂ) : ℂ :=
  (S + Jminus * Q * Jplusᴴ).det

/-- The normalized covariance on the invertible branch. -/
noncomputable def normalizedCovariance
    (S : Matrix R R ℂ) (Jminus Jplus : Matrix R E ℂ) : Matrix E E ℂ :=
  Jplusᴴ * S⁻¹ * Jminus

/-- Clause (i): exact determinant insertion identity on the invertible
branch.  No inverse is used in any singular-branch declaration below. -/
theorem chiralInsertion_factorization
    (S : Matrix R R ℂ) (Jminus Jplus : Matrix R E ℂ)
    (Q : Matrix E E ℂ) (hS : IsUnit S.det) :
    chiralInsertion S Jminus Jplus Q =
      S.det * (1 + Q * normalizedCovariance S Jminus Jplus).det := by
  unfold chiralInsertion normalizedCovariance
  rw [show Jminus * Q * Jplusᴴ = Jminus * (Q * Jplusᴴ) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.det_add_mul Jminus (Q * Jplusᴴ) hS]
  simp only [Matrix.mul_assoc]

/-- The one-parameter insertion polynomial whose coefficient of degree `r`
is the homogeneous degree-`r` source response. -/
noncomputable def covariancePolynomial (P : Matrix E E ℂ) : ℂ[X] :=
  (1 + (X : ℂ[X]) • P.map C).det

/-- Clause (i), coefficient form: the homogeneous degree-`r` coefficient is
the sum of the `r`-dimensional principal exterior minors. -/
theorem covariancePolynomial_coeff (P : Matrix E E ℂ) (r : ℕ) :
    (covariancePolynomial P).coeff r =
      ∑ s ∈ Finset.univ.powersetCard r,
        (P.submatrix (Subtype.val : s → E) (Subtype.val : s → E)).det := by
  exact Matrix.coeff_det_one_add_X_smul_eq_sum_minors P r

/-- Consequently the insertion hierarchy has degree at most the physical
source dimension. -/
theorem covariancePolynomial_coeff_eq_zero_of_card_lt
    (P : Matrix E E ℂ) {r : ℕ} (hr : Fintype.card E < r) :
    (covariancePolynomial P).coeff r = 0 := by
  rw [covariancePolynomial_coeff]
  apply Finset.sum_eq_zero
  intro s hs
  have hs' := (Finset.mem_powersetCard.mp hs).2
  have hcard : s.card ≤ Fintype.card E := by
    simpa using Finset.card_le_univ s
  omega

/-- Every partial source insertion of degree strictly below the kernel
dimension misses the determinant line. -/
theorem below_kernel_degree_vanishes
    {r k e : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (zb z : Fin r → M) (a : Fin e → M)
    (g : (Fin e → ℂ) →ₗ[ℂ] M)
    (Dhard : Matrix (Fin e) (Fin e) ℂ) (hrk : r < k) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i M) (2 * e + 2 * k)
        (ZeroMode.fexp a g Dhard * ZeroMode.insertionK zb z) = 0 := by
  classical
  rw [ZeroMode.fexp, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpe : p ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  rw [smul_mul_assoc, LinearMap.map_smul]
  have hmem : ZeroMode.omegaAct a g Dhard ^ p * ZeroMode.insertionK zb z ∈
      ⋀[ℂ]^(2 * p + 2 * r) M :=
    SetLike.mul_mem_graded (ZeroMode.omega_pow_mem a g Dhard p)
      (ZeroMode.insertionK_mem zb z)
  rw [GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_ne
      (ℳ := fun i : ℕ => ⋀[ℂ]^i M) hmem (by omega), smul_zero]

/-- Exact adapted singular-branch content of clauses (ii) and (iii).  Every
insertion degree below `k` vanishes; after all `k` kernel/cokernel pairs are
inserted, its coefficient is exactly the hard determinant times their line
pairing and is nonzero when the hard block and physical source line are
nonzero. -/
theorem zero_mode_first_saturated_coefficient
    {k e : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (zb z : Fin k → M) (a : Fin e → M)
    (g : (Fin e → ℂ) →ₗ[ℂ] M)
    (Dhard : Matrix (Fin e) (Fin e) ℂ)
    (hDhard : IsUnit Dhard.det)
    (hpair : ZeroMode.unitPairs a g * ZeroMode.insertionK zb z ≠ 0) :
    ‖Dhard.det‖ ≠ 0 ∧
    (∀ r (zbr zr : Fin r → M), r < k →
      GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i M) (2 * e + 2 * k)
          (ZeroMode.fexp a g Dhard * ZeroMode.insertionK zbr zr) = 0) ∧
    GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i M) (2 * e + 2 * k)
        (ZeroMode.fexp a g Dhard * ZeroMode.insertionK zb z) =
      Dhard.det • (ZeroMode.unitPairs a g * ZeroMode.insertionK zb z) ∧
    GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i M) (2 * e + 2 * k)
        (ZeroMode.fexp a g Dhard * ZeroMode.insertionK zb z) ≠ 0 := by
  have hdet : Dhard.det ≠ 0 := hDhard.ne_zero
  have hsat := ZeroMode.saturated_projection zb z a g Dhard
  exact ⟨ZeroMode.reduced_determinant_ne_zero hDhard,
    fun r zbr zr hr => below_kernel_degree_vanishes zbr zr a g Dhard hr,
    hsat, by rw [hsat]; exact smul_ne_zero hdet hpair⟩

/-- Clause (iv), in the explicit one-zero-mode divisor chart: the vacuum
partition is zero, the complete saturated coefficient is nonzero, no
normalized covariance can reconstruct it, and its crossing sign is direct. -/
theorem divisor_zero_safe_replacement {q : ℝ} (hq : q ≠ 0) :
    (SMQGDivisorSafePositivityOrder.saturatedDivisorMatrix 0 q).det = 0 ∧
    (SMQGDivisorSafePositivityOrder.saturatedDivisorMatrix 1 q).det = q ∧
    (SMQGDivisorSafePositivityOrder.saturatedDivisorMatrix 1 q).det ≠ 0 ∧
    (∀ t, 0 < t →
      (0 < (SMQGDivisorSafePositivityOrder.saturatedDivisorMatrix t q).det ↔
        0 < q)) ∧
    ¬∃ normalized : ℝ,
      (SMQGDivisorSafePositivityOrder.saturatedDivisorMatrix 0 q).det * normalized =
        (SMQGDivisorSafePositivityOrder.saturatedDivisorMatrix 1 q).det :=
  SMQGDivisorSafePositivityOrder.divisor_safe_positivity_order hq

/-- Compiled statement of all four branches of
`thm:SMQG-zero-safe`: invertible determinant factorization and exterior
coefficients, singular zero-mode saturation, and forbidden divisor
normalization. -/
theorem invertible_and_zero_safe_source_hierarchy
    (S : Matrix R R ℂ) (Jminus Jplus : Matrix R E ℂ)
    (Q : Matrix E E ℂ) (hS : IsUnit S.det) :
    chiralInsertion S Jminus Jplus Q =
        S.det * (1 + Q * normalizedCovariance S Jminus Jplus).det ∧
    (∀ r, (covariancePolynomial
        (Q * normalizedCovariance S Jminus Jplus)).coeff r =
      ∑ s ∈ Finset.univ.powersetCard r,
        ((Q * normalizedCovariance S Jminus Jplus).submatrix
          (Subtype.val : s → E) (Subtype.val : s → E)).det) ∧
    (∀ r, Fintype.card E < r →
      (covariancePolynomial
        (Q * normalizedCovariance S Jminus Jplus)).coeff r = 0) := by
  refine ⟨chiralInsertion_factorization S Jminus Jplus Q hS, ?_, ?_⟩
  · exact fun r => covariancePolynomial_coeff _ r
  · exact fun _ hr => covariancePolynomial_coeff_eq_zero_of_card_lt _ hr

end ZeroSafeSourceHierarchy
end NCG
