/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Derived common finite CP completion
  (`thm:common-CP-completion`, Gran-Tensor manuscript)

* `common_cp_completion`: for a Stinespring contraction `V`
  (both defect operators `1 - VᴴV` and `1 - VVᴴ` positive):
  (i) the square-root intertwining
      `V·√(1 - VᴴV) = √(1 - VVᴴ)·V` — proved by transporting
      `V·(1 - VᴴV) = (1 - VVᴴ)·V` through powers and
      polynomials, then realizing both CFC square roots as one
      Lagrange interpolation polynomial on the union of the
      two spectra;
  (ii) the **Julia unitary**: the block matrix
      `[[V, √(1-VVᴴ)], [√(1-VᴴV), -Vᴴ]]` is unitary
      (`J·Jᴴ = 1` and `Jᴴ·J = 1`) — the controlled-unitary
      completion of the contraction;
  (iii) finite direct sums of unitaries are unitary — the
      simultaneous finite controlled-unitary completion of a
      finite family.

The remaining finite-family, common Radon–Nikodym/Naimark, and compatible
path-labelled word clauses are proved in the exact companion module
`NCG.Grand.FiniteCommonCPCompletion`.
-/

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- A CFC square root is the Lagrange interpolation polynomial
of `Real.sqrt` evaluated on the matrix, for any node set
containing the spectrum. -/
private lemma sqrt_eq_aeval_of_subset {n : Type*} [Fintype n]
    [DecidableEq n] {M : Matrix n n ℂ} (hM : M.PosSemidef)
    {s : Finset ℝ} (hs : spectrum ℝ M ⊆ (s : Set ℝ)) :
    CFC.sqrt M
      = Polynomial.aeval M
          (Lagrange.interpolate s id Real.sqrt) := by
  rw [CFC.sqrt_eq_real_sqrt M hM.nonneg,
    cfcₙ_eq_cfc Real.continuous_sqrt.continuousOn
      Real.sqrt_zero,
    ← cfc_polynomial (Lagrange.interpolate s id Real.sqrt) M
      hM.1.isSelfAdjoint]
  exact cfc_congr fun x hx =>
    (Lagrange.eval_interpolate_at_node Real.sqrt
      (Set.injOn_id _) (Finset.mem_coe.mp (hs hx))).symm

/-- `thm:common-CP-completion`. -/
theorem common_cp_completion {h k : Type*} [Fintype h]
    [Fintype k] [DecidableEq h] [DecidableEq k]
    (V : Matrix k h ℂ) (hA : (1 - Vᴴ * V).PosSemidef)
    (hB : (1 - V * Vᴴ).PosSemidef) :
    -- (i) square-root intertwining
    V * CFC.sqrt (1 - Vᴴ * V) = CFC.sqrt (1 - V * Vᴴ) * V
    -- (ii) the Julia unitary completion
    ∧ fromBlocks V (CFC.sqrt (1 - V * Vᴴ))
        (CFC.sqrt (1 - Vᴴ * V)) (-Vᴴ)
      * (fromBlocks V (CFC.sqrt (1 - V * Vᴴ))
          (CFC.sqrt (1 - Vᴴ * V)) (-Vᴴ))ᴴ = 1
    ∧ (fromBlocks V (CFC.sqrt (1 - V * Vᴴ))
          (CFC.sqrt (1 - Vᴴ * V)) (-Vᴴ))ᴴ
      * fromBlocks V (CFC.sqrt (1 - V * Vᴴ))
          (CFC.sqrt (1 - Vᴴ * V)) (-Vᴴ) = 1
    -- (iii) simultaneous control: direct sums of unitaries
    ∧ (∀ {p q : Type} [Fintype p] [Fintype q] [DecidableEq p]
        [DecidableEq q] (J₁ : Matrix p p ℂ)
        (J₂ : Matrix q q ℂ),
        J₁ * J₁ᴴ = 1 → J₂ * J₂ᴴ = 1 →
        fromBlocks J₁ 0 0 J₂
          * (fromBlocks J₁ 0 0 J₂)ᴴ = 1) := by
  classical
  set A := 1 - Vᴴ * V with hAdef
  set B := 1 - V * Vᴴ with hBdef
  have hAH : A.IsHermitian := hA.1
  have hBH : B.IsHermitian := hB.1
  -- common interpolation nodes: both spectra
  set s : Finset ℝ :=
    Finset.image hAH.eigenvalues Finset.univ
      ∪ Finset.image hBH.eigenvalues Finset.univ with hsdef
  have hsubA : spectrum ℝ A ⊆ (s : Set ℝ) := by
    rw [hAH.spectrum_real_eq_range_eigenvalues]
    rintro x ⟨i, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hsubB : spectrum ℝ B ⊆ (s : Set ℝ) := by
    rw [hBH.spectrum_real_eq_range_eigenvalues]
    rintro x ⟨i, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hSA := sqrt_eq_aeval_of_subset hA hsubA
  have hSB := sqrt_eq_aeval_of_subset hB hsubB
  -- the defect intertwining and its polynomial transport
  have hVA : V * A = B * V := by
    rw [hAdef, hBdef, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have hpow : ∀ m : ℕ, V * A ^ m = B ^ m * V := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one,
        Matrix.one_mul]
    | succ j ih =>
        rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih,
          Matrix.mul_assoc, hVA, ← Matrix.mul_assoc]
  have htrans : ∀ q : Polynomial ℝ,
      V * Polynomial.aeval A q = Polynomial.aeval B q * V := by
    intro q
    induction q using Polynomial.induction_on' with
    | add u w hu hw =>
        rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul,
          hu, hw]
    | monomial m c =>
        rw [Polynomial.aeval_monomial,
          Polynomial.aeval_monomial,
          Algebra.algebraMap_eq_smul_one,
          Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
          smul_mul_assoc, Matrix.one_mul, Matrix.one_mul,
          Matrix.mul_smul, Matrix.smul_mul, hpow m]
  -- the square-root intertwining and its adjoint
  have hVS : V * CFC.sqrt A = CFC.sqrt B * V := by
    rw [hSA, hSB]
    exact htrans _
  have hSV : CFC.sqrt A * Vᴴ = Vᴴ * CFC.sqrt B := by
    have hc := congrArg conjTranspose hVS
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      sqrt_isHermitian, sqrt_isHermitian] at hc
    exact hc
  refine ⟨hVS, ?_, ?_, ?_⟩
  · -- `J·Jᴴ = 1`
    rw [Matrix.fromBlocks_conjTranspose, sqrt_isHermitian,
      sqrt_isHermitian, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose,
      Matrix.fromBlocks_multiply]
    have h11 : V * Vᴴ + CFC.sqrt B * CFC.sqrt B = 1 := by
      rw [sqrt_mul_self_eq B hB, hBdef]
      abel
    have h12 : V * CFC.sqrt A + CFC.sqrt B * -V = 0 := by
      rw [Matrix.mul_neg, hVS]
      abel
    have h21 : CFC.sqrt A * Vᴴ + -Vᴴ * CFC.sqrt B = 0 := by
      rw [Matrix.neg_mul, hSV]
      abel
    have h22 : CFC.sqrt A * CFC.sqrt A + -Vᴴ * -V = 1 := by
      rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg,
        sqrt_mul_self_eq A hA, hAdef]
      abel
    rw [h11, h12, h21, h22, Matrix.fromBlocks_one]
  · -- `Jᴴ·J = 1`
    rw [Matrix.fromBlocks_conjTranspose, sqrt_isHermitian,
      sqrt_isHermitian, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose,
      Matrix.fromBlocks_multiply]
    have h11 : Vᴴ * V + CFC.sqrt A * CFC.sqrt A = 1 := by
      rw [sqrt_mul_self_eq A hA, hAdef]
      abel
    have h12 : Vᴴ * CFC.sqrt B + CFC.sqrt A * -Vᴴ = 0 := by
      rw [Matrix.mul_neg, hSV]
      abel
    have h21 : CFC.sqrt B * V + -V * CFC.sqrt A = 0 := by
      rw [Matrix.neg_mul, hVS]
      abel
    have h22 : CFC.sqrt B * CFC.sqrt B + -V * -Vᴴ = 1 := by
      rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg,
        sqrt_mul_self_eq B hB, hBdef]
      abel
    rw [h11, h12, h21, h22, Matrix.fromBlocks_one]
  · -- (iii) direct sums
    intro p q _ _ _ _ J₁ J₂ h1 h2
    rw [Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, h1, h2,
      Matrix.fromBlocks_one]

end NCG
