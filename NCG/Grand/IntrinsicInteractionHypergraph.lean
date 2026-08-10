/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ExactSourceSchurResidual
import NCG.Grand.SupportPrototype

/-!
# Intrinsic interaction hypergraph from singular nuisance shorts

This module constructs the connected-support Gram with the exact
Moore--Penrose nuisance projector.  It proves its zero test, positivity and
coordinate invariances, identifies the canonical maximal-support hypergraph
and its least two-section graph, and turns every nonzero Gram eigenmode into
an explicit nonzero connected history.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace IntrinsicInteractionHypergraph

/-- The part of a response synthesis unexplained by the full nuisance range. -/
noncomputable def connectedResidual {h k l : ℕ}
    (F : Matrix (Fin h) (Fin k) ℂ) (Z : Matrix (Fin h) (Fin l) ℂ) :
    Matrix (Fin h) (Fin k) ℂ :=
  (1 - sourceRangeProjection Z) * F

/-- The intrinsic connected-support Gram. -/
noncomputable def connectedSupportGram {h k l : ℕ}
    (F : Matrix (Fin h) (Fin k) ℂ) (Z : Matrix (Fin h) (Fin l) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  (connectedResidual F Z)ᴴ * connectedResidual F Z

/-- The Moore--Penrose nuisance short has precisely the advertised positivity
and vanishing criterion, without a linear-independence assumption on `Z`. -/
theorem connectedSupportGram_properties {h k l : ℕ}
    (F : Matrix (Fin h) (Fin k) ℂ) (Z : Matrix (Fin h) (Fin l) ℂ) :
    (connectedSupportGram F Z).PosSemidef ∧
      (connectedSupportGram F Z = 0 ↔ connectedResidual F Z = 0) ∧
      (connectedSupportGram F Z = 0 ↔ SourceRangeIncluded F Z) := by
  have hzero : connectedSupportGram F Z = 0 ↔ connectedResidual F Z = 0 := by
    exact Matrix.conjTranspose_mul_self_eq_zero
  have hres : sourceSchurResidual Z F = connectedSupportGram F Z := by
    rw [sourceSchurResidual_eq_orthogonalResidual]
    let P := sourceRangeProjection Z
    obtain ⟨hPH, hP2, _⟩ :=
      (sourceGramPseudoinverse_projection Z).2.2.2
    change Pᴴ = P at hPH
    change P * P = P at hP2
    have hQH : (1 - P)ᴴ = 1 - P := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
    have hQ2 : (1 - P) * (1 - P) = 1 - P := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hP2]
      abel
    change Fᴴ * (1 - P) * F =
      ((1 - P) * F)ᴴ * ((1 - P) * F)
    rw [Matrix.conjTranspose_mul, hQH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 - P) (1 - P) F, hQ2]
  refine ⟨Matrix.posSemidef_conjTranspose_mul_self _, hzero, ?_⟩
  rw [← hres]
  exact sourceSchurResidual_eq_zero_iff_rangeIncluded Z F

/-- A change of source coordinates acts by congruence on the connected Gram. -/
theorem connectedSupportGram_right_congruence {h k m l : ℕ}
    (F : Matrix (Fin h) (Fin k) ℂ) (Z : Matrix (Fin h) (Fin l) ℂ)
    (U : Matrix (Fin k) (Fin m) ℂ) :
    (connectedResidual F Z * U)ᴴ * (connectedResidual F Z * U) =
      Uᴴ * connectedSupportGram F Z * U := by
  simp only [connectedSupportGram, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Unitary source-coordinate changes preserve zero versus nonzero support. -/
theorem sourceUnitary_preserves_nonvanishing {h k l : ℕ}
    (F : Matrix (Fin h) (Fin k) ℂ) (Z : Matrix (Fin h) (Fin l) ℂ)
    (U : Matrix (Fin k) (Fin k) ℂ) (hUU : U * Uᴴ = 1) :
    ((connectedResidual F Z * U)ᴴ * (connectedResidual F Z * U) = 0 ↔
      connectedSupportGram F Z = 0) := by
  rw [connectedSupportGram_right_congruence]
  constructor
  · intro hz
    have h := congrArg (fun X => U * X * Uᴴ) hz
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc] at h
    simpa only [← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.mul_one] using h
  · intro hC
    rw [hC]
    simp

/-- Any support-minimal invertible source-coordinate change preserves the
zero/nonzero connected-support test. -/
theorem invertibleSourceCoordinates_preserve_nonvanishing {h k l : ℕ}
    (F : Matrix (Fin h) (Fin k) ℂ) (Z : Matrix (Fin h) (Fin l) ℂ)
    (U V : Matrix (Fin k) (Fin k) ℂ) (hUV : U * V = 1) :
    ((connectedResidual F Z * U)ᴴ * (connectedResidual F Z * U) = 0 ↔
      connectedSupportGram F Z = 0) := by
  constructor
  · intro hzero
    have hRU : connectedResidual F Z * U = 0 :=
      Matrix.conjTranspose_mul_self_eq_zero.mp hzero
    have h := congrArg (fun X => X * V) hRU
    simp only [Matrix.zero_mul, Matrix.mul_assoc, hUV, Matrix.mul_one] at h
    exact (connectedSupportGram_properties F Z).2.1.mpr h
  · intro hzero
    have hR := (connectedSupportGram_properties F Z).2.1.mp hzero
    rw [hR, Matrix.zero_mul, Matrix.conjTranspose_zero, Matrix.zero_mul]

/-- Isometric response-frame changes (including genuinely unread row
refinements) leave the connected Gram exactly unchanged. -/
theorem responseIsometry_preserves_gram {h h' k : ℕ}
    (R : Matrix (Fin h) (Fin k) ℂ) (J : Matrix (Fin h') (Fin h) ℂ)
    (hJ : Jᴴ * J = 1) :
    (J * R)ᴴ * (J * R) = Rᴴ * R := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Jᴴ J R, hJ, Matrix.one_mul]

/-- A support is retained exactly when its connected Gram is nonzero. -/
def Retained {α : Type*} {k : ℕ}
    (C : Finset α → Matrix (Fin k) (Fin k) ℂ) (A : Finset α) : Prop :=
  C A ≠ 0

/-- A retained support maximal under inclusion. -/
def MaximalRetained {α : Type*} {k : ℕ}
    (C : Finset α → Matrix (Fin k) (Fin k) ℂ) (A : Finset α) : Prop :=
  Retained C A ∧
    ∀ B : Finset α, Retained C B → A ⊆ B → B = A

/-- A hypergraph covers every retained response support. -/
def CoversRetained {α : Type*} {k : ℕ}
    (C : Finset α → Matrix (Fin k) (Fin k) ℂ)
    (H : Set (Finset α)) : Prop :=
  ∀ A : Finset α, Retained C A → ∃ B, B ∈ H ∧ A ⊆ B

/-- No hyperedge in the family is contained in a distinct hyperedge. -/
def SupportAntichain {α : Type*} (H : Set (Finset α)) : Prop :=
  ∀ A, A ∈ H → ∀ B, B ∈ H → A ⊆ B → A = B

/-- The maximal nonzero supports form the unique retained antichain covering
all retained responses: the canonical edge-minimal interaction hypergraph. -/
theorem maximalSupports_unique_edgeMinimal {α : Type*} {k : ℕ}
    [Finite α]
    (C : Finset α → Matrix (Fin k) (Fin k) ℂ) :
    let Hmin : Set (Finset α) := {A | MaximalRetained C A}
    CoversRetained C Hmin ∧ SupportAntichain Hmin ∧
      ∀ H : Set (Finset α),
        (∀ A, A ∈ H → Retained C A) →
        CoversRetained C H → SupportAntichain H → H = Hmin := by
  classical
  dsimp only
  have hext := (intrinsic_interaction_hypergraph C).1
  have hcover : CoversRetained C {A | MaximalRetained C A} := by
    intro A hA
    obtain ⟨B, hB, hAB, hmax⟩ := hext A hA
    exact ⟨B, ⟨hB, hmax⟩, hAB⟩
  have hanti : SupportAntichain {A | MaximalRetained C A} := by
    intro A hA B hB hAB
    exact (hA.2 B hB.1 hAB).symm
  refine ⟨hcover, hanti, ?_⟩
  intro H hret hcov hHanti
  ext A
  constructor
  · intro hAH
    obtain ⟨B, hBret, hAB, hBmax⟩ := hext A (hret A hAH)
    have hBHmin : MaximalRetained C B := ⟨hBret, hBmax⟩
    obtain ⟨D, hDH, hBD⟩ := hcov B hBret
    have hDB : D = B := hBmax D (hret D hDH) hBD
    have hBH : B ∈ H := hDB ▸ hDH
    have hABeq : A = B := hHanti A hAH B hBH hAB
    exact hABeq ▸ hBHmin
  · intro hAmax
    obtain ⟨B, hBH, hAB⟩ := hcov A hAmax.1
    have hBA : B = A := hAmax.2 B (hret B hBH) hAB
    exact hBA ▸ hBH

/-- The two-section relation of a hypergraph. -/
def TwoSection {α : Type*} (H : Set (Finset α)) (i j : α) : Prop :=
  ∃ A, A ∈ H ∧ i ∈ A ∧ j ∈ A

/-- The two-section is the least graph in which every hyperedge is a clique. -/
theorem twoSection_is_unique_least_cliqueGraph {α : Type*}
    (H : Set (Finset α)) :
    (∀ A, A ∈ H → ∀ i ∈ A, ∀ j ∈ A, TwoSection H i j) ∧
      ∀ E : α → α → Prop,
        (∀ A, A ∈ H → ∀ i ∈ A, ∀ j ∈ A, E i j) →
        ∀ i j, TwoSection H i j → E i j := by
  constructor
  · intro A hA i hi j hj
    exact ⟨A, hA, hi, hj⟩
  · intro E hE i j
    rintro ⟨A, hA, hi, hj⟩
    exact hE A hA i hi j hj

/-- A nonzero eigenmode of the connected Gram synthesizes a concrete nonzero
connected history through the shorted response map. -/
theorem nonzeroGramMode_synthesizes_connectedHistory {h k : ℕ}
    (R : Matrix (Fin h) (Fin k) ℂ) (v : Fin k → ℂ) (mu : ℂ)
    (hv : v ≠ 0) (hmu : mu ≠ 0)
    (heig : (Rᴴ * R) *ᵥ v = mu • v) :
    R *ᵥ v ≠ 0 := by
  intro hRv
  have hleft : (Rᴴ * R) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, hRv, Matrix.mulVec_zero]
  have hzero : mu • v = 0 := heig ▸ hleft
  exact hv ((smul_eq_zero.mp hzero).resolve_left hmu)

end IntrinsicInteractionHypergraph
end NCG
