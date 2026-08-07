/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Arbitrary positive factorizations are not interchangeable
  (`cth:nonminimal-factorization`, Gran-Tensor manuscript)

* `nonminimal_factorization`: the reset channel
  `T(X) = Tr(X)·P₀` on `M₂(ℂ)` realizes the trivial scalar table
  (`Tr(Tⁿ P₀) = 1` for all `n`, trace preservation), its
  Hilbert–Schmidt adjoint is `T*(Y) = Tr(P₀Y)·1`, both are
  idempotent, and `T` and `T*` do NOT commute — the ambient
  adjoint algebra of a nonminimal positive realization is
  noncommutative although the minimal realization of the same
  table is one dimensional.

Rendering disclosed: `C*(I,T,T*) ≅ M₂(ℂ) ⊕ ℂ` is rendered by
the verified idempotent/adjoint relations and the
noncommutativity witness; the one-dimensionality of the minimal
predictive realization is the trivial-table clause.
-/

open Matrix

namespace NCG

/-- The rank-one reset target `P₀`. -/
noncomputable def resetP : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, 0]

/-- The reset channel `T(X) = Tr(X)·P₀`. -/
noncomputable def resetT :
    Module.End ℂ (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun X := X.trace • resetP
  map_add' X Y := by rw [Matrix.trace_add, add_smul]
  map_smul' c X := by
    rw [Matrix.trace_smul, smul_eq_mul, RingHom.id_apply,
      mul_smul]

/-- The Hilbert–Schmidt adjoint `T*(Y) = Tr(P₀Y)·1`. -/
noncomputable def resetTstar :
    Module.End ℂ (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun X := (resetP * X).trace • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_add' X Y := by
    rw [Matrix.mul_add, Matrix.trace_add, add_smul]
  map_smul' c X := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      RingHom.id_apply, mul_smul]

/-- `cth:nonminimal-factorization`: trivial table, HS
adjointness, idempotents, and the noncommutativity of the
ambient adjoint pair. -/
theorem nonminimal_factorization :
    (∀ X Y : Matrix (Fin 2) (Fin 2) ℂ,
      (Xᴴ * resetT Y).trace = ((resetTstar X)ᴴ * Y).trace)
    ∧ (∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        (resetT X).trace = X.trace)
    ∧ (resetT * resetT = resetT)
    ∧ (resetTstar * resetTstar = resetTstar)
    ∧ (∀ n : ℕ, ((resetT ^ n) resetP).trace = 1)
    ∧ (resetT * resetTstar ≠ resetTstar * resetT) := by
  have hT : ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
      resetT X = X.trace • resetP := fun _ => rfl
  have hTs : ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
      resetTstar X = (resetP * X).trace • 1 := fun _ => rfl
  have hPtrace : resetP.trace = 1 := by
    simp [resetP, Matrix.trace_fin_two]
  have hPH : resetPᴴ = resetP := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [resetP]
  have hPP : resetP * resetP = resetP := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [resetP, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- HS adjointness
    intro X Y
    rw [hT, hTs]
    rw [Matrix.mul_smul, Matrix.trace_smul,
      Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.trace_smul, Matrix.conjTranspose_one,
      Matrix.one_mul]
    rw [show Xᴴ * resetP = (resetPᴴ * X)ᴴ from by
      rw [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]]
    rw [Matrix.trace_conjTranspose, hPH]
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
  · -- trace preservation
    intro X
    rw [hT, Matrix.trace_smul, hPtrace, smul_eq_mul, mul_one]
  · -- T idempotent
    apply LinearMap.ext
    intro X
    change resetT (resetT X) = resetT X
    rw [hT X, map_smul, hT resetP, hPtrace, one_smul]
  · -- T* idempotent
    apply LinearMap.ext
    intro X
    change resetTstar (resetTstar X) = resetTstar X
    rw [hTs X, map_smul, hTs 1, Matrix.mul_one, hPtrace,
      one_smul]
  · -- trivial table
    intro n
    induction n with
    | zero => rw [pow_zero, Module.End.one_apply, hPtrace]
    | succ k ih =>
        rw [pow_succ, Module.End.mul_apply, hT resetP,
          hPtrace, one_smul, ih]
  · -- noncommutativity of the adjoint pair
    intro h
    have h1 := congrArg
      (fun f : Module.End ℂ (Matrix (Fin 2) (Fin 2) ℂ) =>
        (f (1 : Matrix (Fin 2) (Fin 2) ℂ)) 1 1) h
    simp only [Module.End.mul_apply] at h1
    rw [hTs 1, Matrix.mul_one, hPtrace, one_smul, hT 1,
      Matrix.trace_one, map_smul, hTs resetP, hPP, hPtrace,
      one_smul] at h1
    rw [Matrix.smul_apply, Matrix.smul_apply] at h1
    norm_num [resetP, Matrix.one_apply, Fintype.card_fin] at h1

end NCG
