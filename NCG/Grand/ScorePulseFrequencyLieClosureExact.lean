/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandScoreControl
import NCG.Grand.ControlledCompiler
import NCG.Grand.TwoClockFullMatrixLieGeneration
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Exact frequency-resolved score control

The missing dynamical clause of `thm:canonical-score-control` is a finite
spectral-isolation argument.  In a quotient by the generated Lie subspace,
the frequency blocks are eigenvectors of the double adjoint.  Distinct
squared frequencies make the nonzero quotient blocks linearly independent,
while their sum is zero; hence every block already belongs to the generated
subspace.  Two commutators recover the remaining Pauli axes.
-/

open Matrix Finset

namespace NCG
namespace ScoreFrequencyControl

/-- An invariant subspace containing the sum of eigenvectors with distinct
eigenvalues contains every summand. -/
theorem distinct_eigencomponents_mem
    {s : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (lam : Fin s → ℂ) (hlam : Function.Injective lam)
    (v : Fin s → V) (hv : ∀ j, T (v j) = lam j • v j)
    (S : Submodule ℂ V) (hTS : ∀ x ∈ S, T x ∈ S)
    (hsum : ∑ j, v j ∈ S) :
    ∀ j, v j ∈ S := by
  classical
  have hT : S ≤ S.comap T := by
    intro x hx
    exact hTS x hx
  let Tq : (V ⧸ S) →ₗ[ℂ] (V ⧸ S) := S.mapQ S T hT
  let qv : Fin s → V ⧸ S := fun j => S.mkQ (v j)
  have hqev : ∀ j, Tq (qv j) = lam j • qv j := by
    intro j
    change ((S.mapQ S T hT).comp S.mkQ) (v j) =
      lam j • S.mkQ (v j)
    rw [Submodule.mapQ_mkQ, LinearMap.comp_apply, hv]
    exact S.mkQ.map_smul (lam j) (v j)
  have hqsum : ∑ j, qv j = 0 := by
    change ∑ j, S.mkQ (v j) = 0
    rw [← map_sum]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsum
  let I := {j : Fin s // qv j ≠ 0}
  let w : I → V ⧸ S := fun j => qv j.1
  have hhas : ∀ j : I,
      Module.End.HasEigenvector Tq (lam j.1) (w j) := by
    intro j
    exact ⟨Module.End.mem_eigenspace_iff.mpr (hqev j.1), j.2⟩
  have hli : LinearIndependent ℂ w :=
    Module.End.eigenvectors_linearIndependent' Tq (fun j : I => lam j.1)
      (hlam.comp Subtype.val_injective) w hhas
  have hfalse : ∑ j : {j : Fin s // ¬qv j ≠ 0}, qv j.1 = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact not_ne_iff.mp j.2
  have hIsum : ∑ j : I, w j = 0 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun j : Fin s => qv j ≠ 0) qv
    change (∑ j : I, w j) +
        (∑ j : {j : Fin s // ¬qv j ≠ 0}, qv j.1) = ∑ j, qv j at hsplit
    rw [hfalse, add_zero, hqsum] at hsplit
    exact hsplit
  have hcoeff : ∀ j : I, (1 : ℂ) = 0 := by
    have hzero : ∑ j : I, (1 : ℂ) • w j = 0 := by
      simpa using hIsum
    exact Fintype.linearIndependent_iff.mp hli (fun _ => 1) hzero
  intro j
  rw [← Submodule.Quotient.mk_eq_zero]
  by_contra hj
  exact one_ne_zero (hcoeff ⟨j, hj⟩)

variable {n : Type*} [Fintype n]

/-- Commutation with a fixed generator, as a complex linear endomorphism. -/
def adjointMap (L : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := matrixCommutator L X
  map_add' X Y := by
    unfold matrixCommutator
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c X := by
    unfold matrixCommutator
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
    module

/-- The double adjoint used to separate the squared frequencies. -/
def doubleAdjointMap (L : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  (adjointMap L).comp (adjointMap L)

/-- The span of the three resolved axes on one frequency block. -/
def frequencyBlockSpan (A B K : Fin s → Matrix n n ℂ) (j : Fin s) :
    Submodule ℂ (Matrix n n ℂ) :=
  Submodule.span ℂ ({A j, B j, K j} : Set (Matrix n n ℂ))

/-- Distinct nonzero anticommuting frequency blocks generate their complete
three-axis `su(2)` spans inside any Lie subspace containing `L` and `Z`. -/
theorem score_su2_block_generation
    {s : ℕ} (mu : Fin s → ℝ) (hmu : ∀ j, mu j ≠ 0)
    (hmu2 : Function.Injective fun j => mu j ^ 2)
    (L : Matrix n n ℂ) (A B K : Fin s → Matrix n n ℂ)
    (S : Submodule ℂ (Matrix n n ℂ))
    (hLmem : L ∈ S)
    (hLie : ∀ X ∈ S, ∀ Y ∈ S, matrixCommutator X Y ∈ S)
    (hKsum : ∑ j, K j ∈ S)
    (hdouble : ∀ j, doubleAdjointMap L (K j) =
      (((-4 : ℝ) * mu j ^ 2 : ℝ) : ℂ) • K j)
    (hfirst : ∀ j, matrixCommutator L (K j) =
      (((2 : ℝ) * mu j : ℝ) : ℂ) • A j)
    (hsecond : ∀ j, matrixCommutator (K j) (A j) =
      (2 * Complex.I) • B j) :
    ∀ j, frequencyBlockSpan A B K j ≤ S := by
  have hlam : Function.Injective
      (fun j => (((-4 : ℝ) * mu j ^ 2 : ℝ) : ℂ)) := by
    intro i j hij
    apply hmu2
    have hr : (-4 : ℝ) * mu i ^ 2 = (-4 : ℝ) * mu j ^ 2 :=
      Complex.ofReal_injective hij
    linarith
  have hTmem : ∀ X ∈ S, doubleAdjointMap L X ∈ S := by
    intro X hX
    exact hLie L hLmem _ (hLie L hLmem X hX)
  have hKmem : ∀ j, K j ∈ S :=
    distinct_eigencomponents_mem (doubleAdjointMap L)
      (fun j => (((-4 : ℝ) * mu j ^ 2 : ℝ) : ℂ)) hlam K hdouble S hTmem hKsum
  intro j
  have hcA : ((((2 : ℝ) * mu j : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) (hmu j))
  have hAmem : A j ∈ S := by
    have hc := hLie L hLmem (K j) (hKmem j)
    rw [hfirst j] at hc
    rw [show A j = ((((2 : ℝ) * mu j : ℝ) : ℂ)⁻¹) •
        (((((2 : ℝ) * mu j : ℝ) : ℂ)) • A j) by
          rw [smul_smul, inv_mul_cancel₀ hcA, one_smul]]
    exact S.smul_mem _ hc
  have hcB : (2 * Complex.I : ℂ) ≠ 0 := by norm_num
  have hBmem : B j ∈ S := by
    have hc := hLie (K j) (hKmem j) (A j) hAmem
    rw [hsecond j] at hc
    rw [show B j = (2 * Complex.I : ℂ)⁻¹ • ((2 * Complex.I) • B j) by
      rw [smul_smul, inv_mul_cancel₀ hcB, one_smul]]
    exact S.smul_mem _ hc
  apply Submodule.span_le.mpr
  intro X hX
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with rfl | rfl | rfl
  · exact hAmem
  · exact hBmem
  · exact hKmem j

/-- The exact controlled-Z identity, named for use inside theorem conjunctions. -/
def ControlledZIdentity : Prop :=
  czGate = Complex.exp (-((Real.pi / 4 : ℝ) : ℂ) * Complex.I) •
    ((Matrix.diagonal fun p : Fin 2 × Fin 2 =>
        Complex.exp (-((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I * zSign p.1))
      * (Matrix.diagonal fun p : Fin 2 × Fin 2 =>
          Complex.exp (-((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I * zSign p.2))
      * scorePulse (Real.pi / 4))

theorem controlledZIdentity_proof : ControlledZIdentity := score_control_cz

/-- `thm:canonical-score-control`, exact pulse, kickback, controlled-`Z`,
and resolved dynamical `su(2)` package. -/
theorem canonical_score_control_exact
    {s : ℕ} (mu : Fin s → ℝ) (hmu : ∀ j, mu j ≠ 0)
    (hmu2 : Function.Injective fun j => mu j ^ 2)
    (L : Matrix n n ℂ) (A B K : Fin s → Matrix n n ℂ)
    (S : Submodule ℂ (Matrix n n ℂ))
    (hLmem : L ∈ S)
    (hLie : ∀ X ∈ S, ∀ Y ∈ S, matrixCommutator X Y ∈ S)
    (hKsum : ∑ j, K j ∈ S)
    (hdouble : ∀ j, doubleAdjointMap L (K j) =
      (((-4 : ℝ) * mu j ^ 2 : ℝ) : ℂ) • K j)
    (hfirst : ∀ j, matrixCommutator L (K j) =
      (((2 : ℝ) * mu j : ℝ) : ℂ) • A j)
    (hsecond : ∀ j, matrixCommutator (K j) (A j) =
      (2 * Complex.I) • B j) :
    (∀ theta theta', scorePulse theta * scorePulse theta' =
      scorePulse (theta + theta'))
      ∧ (∀ t, Matrix.kroneckerMap (· * ·) (scorePhase t)
          (1 : Matrix (Fin 2) (Fin 2) ℂ) =
        Matrix.diagonal fun p : Fin 2 × Fin 2 =>
          Complex.exp (-(t : ℂ) * Complex.I * zSign p.1))
      ∧ (∀ t, Matrix.kroneckerMap (· * ·)
          (1 : Matrix (Fin 2) (Fin 2) ℂ) (scorePhase t) =
        Matrix.diagonal fun p : Fin 2 × Fin 2 =>
          Complex.exp (-(t : ℂ) * Complex.I * zSign p.2))
      ∧ ControlledZIdentity
      ∧ ∀ j, frequencyBlockSpan A B K j ≤ S := by
  refine ⟨scorePulse_group, scorePhase_kron_left,
    scorePhase_kron_right, controlledZIdentity_proof, ?_⟩
  exact score_su2_block_generation mu hmu hmu2 L A B K S
    hLmem hLie hKsum hdouble hfirst hsecond

end ScoreFrequencyControl
end NCG
