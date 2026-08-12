/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FullMatrixControl
import NCG.Algebra.CliffordGenerates

/-!
# Lie generation of the two-clock full matrix target

The six local Pauli axes and the entangling `Z ⊗ Z` axis generate, under
complex linear combinations and commutators, all fifteen nonidentity
Pauli--Kronecker axes.  Since the sixteen Pauli words are a basis of `M₄(ℂ)`,
this is the exact complexified `su(4)` generation assertion in
`cor:canonical-full-matrix-control`.
-/

open Matrix Kronecker

namespace NCG

open CommonOrigin

/-- Matrix commutator used for the concrete control Lie algebra. -/
def matrixCommutator {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) : Matrix n n ℂ := A * B - B * A

private lemma pauli13_comm :
    pauli1 * pauli3 - pauli3 * pauli1 =
      (-(2 * Complex.I)) • pauli2 := by
  simpa [pauli1, pauli2, pauli3] using
    (full_matrix_control (d := Fin 2)).2.2.1

private lemma pauli23_comm :
    pauli2 * pauli3 - pauli3 * pauli2 =
      (2 * Complex.I) • pauli1 := by
  simpa [pauli1, pauli2, pauli3] using
    (full_matrix_control (d := Fin 2)).2.2.2.1

private lemma pauli12_comm :
    pauli1 * pauli2 - pauli2 * pauli1 =
      (2 * Complex.I) • pauli3 := by
  simpa [pauli1, pauli2, pauli3] using
    (full_matrix_control (d := Fin 2)).2.2.2.2

private lemma pauli21_comm :
    matrixCommutator pauli2 pauli1 =
      (-(2 * Complex.I)) • pauli3 := by
  unfold matrixCommutator
  calc
    pauli2 * pauli1 - pauli1 * pauli2 =
        -(pauli1 * pauli2 - pauli2 * pauli1) := by abel
    _ = -((2 * Complex.I) • pauli3) := congrArg Neg.neg pauli12_comm
    _ = (-(2 * Complex.I)) • pauli3 := by simp

private lemma comm_k10_k33 :
    matrixCommutator (pauliKron (1, 0)) (pauliKron (3, 3)) =
      (-(2 * Complex.I)) • pauliKron (2, 3) := by
  change matrixCommutator (pauli1 ⊗ₖ 1) (pauli3 ⊗ₖ pauli3) =
    (-(2 * Complex.I)) • (pauli2 ⊗ₖ pauli3)
  unfold matrixCommutator
  rw [(full_matrix_control (d := Fin 2)).1 pauli1 pauli3 pauli3,
    pauli13_comm,
    Matrix.smul_kronecker]

private lemma comm_k20_k33 :
    matrixCommutator (pauliKron (2, 0)) (pauliKron (3, 3)) =
      (2 * Complex.I) • pauliKron (1, 3) := by
  change matrixCommutator (pauli2 ⊗ₖ 1) (pauli3 ⊗ₖ pauli3) =
    (2 * Complex.I) • (pauli1 ⊗ₖ pauli3)
  unfold matrixCommutator
  rw [(full_matrix_control (d := Fin 2)).1 pauli2 pauli3 pauli3,
    pauli23_comm,
    Matrix.smul_kronecker]

private lemma comm_k02_k23 :
    matrixCommutator (pauliKron (0, 2)) (pauliKron (2, 3)) =
      (2 * Complex.I) • pauliKron (2, 1) := by
  change matrixCommutator (1 ⊗ₖ pauli2) (pauli2 ⊗ₖ pauli3) =
    (2 * Complex.I) • (pauli2 ⊗ₖ pauli1)
  unfold matrixCommutator
  rw [(full_matrix_control (d := Fin 2)).2.1 pauli2 pauli2 pauli3,
    pauli23_comm,
    Matrix.kronecker_smul]

private lemma comm_k01_k23 :
    matrixCommutator (pauliKron (0, 1)) (pauliKron (2, 3)) =
      (-(2 * Complex.I)) • pauliKron (2, 2) := by
  change matrixCommutator (1 ⊗ₖ pauli1) (pauli2 ⊗ₖ pauli3) =
    (-(2 * Complex.I)) • (pauli2 ⊗ₖ pauli2)
  unfold matrixCommutator
  rw [(full_matrix_control (d := Fin 2)).2.1 pauli1 pauli2 pauli3,
    pauli13_comm,
    Matrix.kronecker_smul]

private lemma comm_k02_k13 :
    matrixCommutator (pauliKron (0, 2)) (pauliKron (1, 3)) =
      (2 * Complex.I) • pauliKron (1, 1) := by
  change matrixCommutator (1 ⊗ₖ pauli2) (pauli1 ⊗ₖ pauli3) =
    (2 * Complex.I) • (pauli1 ⊗ₖ pauli1)
  unfold matrixCommutator
  rw [(full_matrix_control (d := Fin 2)).2.1 pauli2 pauli1 pauli3,
    pauli23_comm,
    Matrix.kronecker_smul]

private lemma comm_k01_k13 :
    matrixCommutator (pauliKron (0, 1)) (pauliKron (1, 3)) =
      (-(2 * Complex.I)) • pauliKron (1, 2) := by
  change matrixCommutator (1 ⊗ₖ pauli1) (pauli1 ⊗ₖ pauli3) =
    (-(2 * Complex.I)) • (pauli1 ⊗ₖ pauli2)
  unfold matrixCommutator
  rw [(full_matrix_control (d := Fin 2)).2.1 pauli1 pauli1 pauli3,
    pauli13_comm,
    Matrix.kronecker_smul]

private lemma comm_k20_k11 :
    matrixCommutator (pauliKron (2, 0)) (pauliKron (1, 1)) =
      (-(2 * Complex.I)) • pauliKron (3, 1) := by
  change matrixCommutator (pauli2 ⊗ₖ 1) (pauli1 ⊗ₖ pauli1) =
    (-(2 * Complex.I)) • (pauli3 ⊗ₖ pauli1)
  unfold matrixCommutator
  rw [(full_matrix_control (d := Fin 2)).1 pauli2 pauli1 pauli1,
    show pauli2 * pauli1 - pauli1 * pauli2 =
      (-(2 * Complex.I)) • pauli3 by exact pauli21_comm,
    Matrix.smul_kronecker]

private lemma comm_k20_k12 :
    matrixCommutator (pauliKron (2, 0)) (pauliKron (1, 2)) =
      (-(2 * Complex.I)) • pauliKron (3, 2) := by
  change matrixCommutator (pauli2 ⊗ₖ 1) (pauli1 ⊗ₖ pauli2) =
    (-(2 * Complex.I)) • (pauli3 ⊗ₖ pauli2)
  unfold matrixCommutator
  rw [(full_matrix_control (d := Fin 2)).1 pauli2 pauli1 pauli2,
    show pauli2 * pauli1 - pauli1 * pauli2 =
      (-(2 * Complex.I)) • pauli3 by exact pauli21_comm,
    Matrix.smul_kronecker]

/-- Every commutator-closed complex subspace containing the local controls
and `Z ⊗ Z` contains every nonidentity Pauli word. -/
theorem twoClockLocalEntangling_generate_allPauliAxes
    (L : Submodule ℂ
      (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (hcomm : ∀ A ∈ L, ∀ B ∈ L, matrixCommutator A B ∈ L)
    (h10 : pauliKron (1, 0) ∈ L) (h20 : pauliKron (2, 0) ∈ L)
    (h30 : pauliKron (3, 0) ∈ L) (h01 : pauliKron (0, 1) ∈ L)
    (h02 : pauliKron (0, 2) ∈ L) (h03 : pauliKron (0, 3) ∈ L)
    (h33 : pauliKron (3, 3) ∈ L) :
    ∀ p q : Fin 4, (p, q) ≠ (0, 0) → pauliKron (p, q) ∈ L := by
  have solve {A B X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
      {c : ℂ} (hc : c ≠ 0) (hA : A ∈ L) (hB : B ∈ L)
      (heq : matrixCommutator A B = c • X) : X ∈ L := by
    have hm := L.smul_mem c⁻¹ (hcomm A hA B hB)
    rw [heq, smul_smul, inv_mul_cancel₀ hc, one_smul] at hm
    exact hm
  have h23 : pauliKron (2, 3) ∈ L :=
    solve (by norm_num : -(2 * Complex.I) ≠ 0) h10 h33 comm_k10_k33
  have h13 : pauliKron (1, 3) ∈ L :=
    solve (by norm_num : 2 * Complex.I ≠ 0) h20 h33 comm_k20_k33
  have h21 : pauliKron (2, 1) ∈ L :=
    solve (by norm_num : 2 * Complex.I ≠ 0) h02 h23 comm_k02_k23
  have h22 : pauliKron (2, 2) ∈ L :=
    solve (by norm_num : -(2 * Complex.I) ≠ 0) h01 h23 comm_k01_k23
  have h11 : pauliKron (1, 1) ∈ L :=
    solve (by norm_num : 2 * Complex.I ≠ 0) h02 h13 comm_k02_k13
  have h12 : pauliKron (1, 2) ∈ L :=
    solve (by norm_num : -(2 * Complex.I) ≠ 0) h01 h13 comm_k01_k13
  have h31 : pauliKron (3, 1) ∈ L :=
    solve (by norm_num : -(2 * Complex.I) ≠ 0) h20 h11 comm_k20_k11
  have h32 : pauliKron (3, 2) ∈ L :=
    solve (by norm_num : -(2 * Complex.I) ≠ 0) h20 h12 comm_k20_k12
  intro p q hpq
  fin_cases p <;> fin_cases q
  · exact False.elim (hpq rfl)
  · exact h01
  · exact h02
  · exact h03
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h30
  · exact h31
  · exact h32
  · exact h33

/-- The standard Pauli realization of the complexified two-clock special
unitary Lie algebra: the span of the fifteen nonidentity Pauli words. -/
def twoClockSpecialLinear : Submodule ℂ
    (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  Submodule.span ℂ {A | ∃ p q : Fin 4,
    (p, q) ≠ (0, 0) ∧ A = pauliKron (p, q)}

/-- The local-plus-entangling commutator closure contains the entire
complexified `su(4)` realization. -/
theorem twoClockSpecialLinear_le_control
    (L : Submodule ℂ
      (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (haxes : ∀ p q : Fin 4, (p, q) ≠ (0, 0) → pauliKron (p, q) ∈ L) :
    twoClockSpecialLinear ≤ L := by
  rw [twoClockSpecialLinear, Submodule.span_le]
  rintro A ⟨p, q, hpq, rfl⟩
  exact haxes p q hpq

/-- Adding the identity to the generated fifteen axes spans the entire full
matrix algebra; equivalently the generated nonidentity part is the
complexification of `su(4)`. -/
theorem twoClockControl_span_fullMatrix
    (L : Submodule ℂ
      (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (haxes : ∀ p q : Fin 4, (p, q) ≠ (0, 0) → pauliKron (p, q) ∈ L) :
    Submodule.span ℂ (Set.insert (pauliKron (0, 0)) (L : Set _)) = ⊤ := by
  apply le_antisymm le_top
  rw [← pauliKron_span]
  apply Submodule.span_mono
  rintro M ⟨⟨p, q⟩, rfl⟩
  by_cases h : (p, q) = (0, 0)
  · rw [h]
    exact Set.mem_insert _ _
  · exact Set.mem_insert_iff.mpr (Or.inr (haxes p q h))

/-- A resolved target is simple for the commutator action when every
nonzero commutator ideal inside it is the whole target.  This packages the
precise structural hypothesis used in the manuscript's simple-block clause. -/
def IsSimpleCommutatorTarget {n : Type*} [Fintype n]
    (S : Submodule ℂ (Matrix n n ℂ)) : Prop :=
  ∀ L : Submodule ℂ (Matrix n n ℂ), L ≤ S →
    (∀ A ∈ S, ∀ B ∈ L, matrixCommutator A B ∈ L) →
    L = ⊥ ∨ L = S

/-- Lie-ideal propagation on a resolved simple full-matrix target: any
nonzero controlled ideal is the full target. -/
theorem simpleCommutatorTarget_control {n : Type*} [Fintype n]
    (S L : Submodule ℂ (Matrix n n ℂ))
    (hsimple : IsSimpleCommutatorTarget S)
    (hLS : L ≤ S)
    (hideal : ∀ A ∈ S, ∀ B ∈ L, matrixCommutator A B ∈ L)
    {X : Matrix n n ℂ} (hX : X ∈ L) (hX0 : X ≠ 0) :
    L = S := by
  rcases hsimple L hLS hideal with hbot | htop
  · have : X = 0 := by simpa [hbot] using hX
    exact (hX0 this).elim
  · exact htop

end NCG
