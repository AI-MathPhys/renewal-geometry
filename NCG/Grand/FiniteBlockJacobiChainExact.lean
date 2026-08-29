/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PositiveGaugeJacobiLayerReconstruction
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Actual finite block-Jacobi resolvents and continued fractions

The earlier reconstruction file starts from a response tower satisfying the
continued-fraction recursion.  Here the tower is derived from an actual finite
self-adjoint block Jacobi matrix.  A chain is built recursively, its global
operator is a genuine `Matrix.fromBlocks`, and repeated use of mathlib's Schur
inverse theorem identifies the visible block of every full tail resolvent with
the inverse recursive response.
-/

open Matrix

namespace NCG.FiniteBlockJacobiChainExact

universe u

variable (b : Type u) [Fintype b] [DecidableEq b]

abbrev Block := Matrix b b ℂ

/-- A finite Jacobi chain, stored from its visible layer toward its terminal
layer. -/
inductive Chain
  | terminal (center : Block b)
  | prepend (center coupling : Block b) (tail : Chain)

namespace Chain

variable {b : Type u} [Fintype b] [DecidableEq b]

/-- The actual carrier of all layers in a chain. -/
abbrev Index : Chain b → Type u
  | .terminal _ => b
  | .prepend _ _ tail => b ⊕ Index tail

noncomputable instance indexFintype : (J : Chain b) → Fintype (Index J)
  | .terminal _ => (inferInstance : Fintype b)
  | .prepend _ _ tail =>
      @instFintypeSum b (Index tail) inferInstance (indexFintype tail)

instance indexDecidableEq : (J : Chain b) → DecidableEq (Index J)
  | .terminal _ => (inferInstance : DecidableEq b)
  | .prepend _ _ tail =>
      @instDecidableEqSum b (Index tail) inferInstance (indexDecidableEq tail)

/-- Embed a coupling into the first block of a tail carrier. -/
def injectHead (J : Chain b) (B : Block b) : Matrix (Index J) b ℂ :=
  match J with
  | .terminal _ => B
  | .prepend _ _ tail => Matrix.fromRows B (0 : Matrix (Index tail) b ℂ)

/-- Visible compression of an operator on a tail carrier. -/
def visibleBlock (J : Chain b) (X : Matrix (Index J) (Index J) ℂ) : Block b :=
  match J with
  | .terminal _ => X
  | .prepend _ _ _ => X.toBlocks₁₁

/-- The actual block-tridiagonal Jacobi operator. -/
noncomputable def operator : (J : Chain b) → Matrix (Index J) (Index J) ℂ
  | .terminal C => C
  | .prepend C B tail =>
      Matrix.fromBlocks C (injectHead tail B)ᴴ (injectHead tail B) (operator tail)

/-- Full resolvent pencil of an actual tail. -/
noncomputable def resolvent (J : Chain b) (z : ℂ) : Matrix (Index J) (Index J) ℂ :=
  z • (1 : Matrix (Index J) (Index J) ℂ) - operator J

/-- The recursive matrix continued fraction associated with the actual chain. -/
noncomputable def response : Chain b → ℂ → Block b
  | .terminal C, z => z • (1 : Block b) - C
  | .prepend C B tail, z =>
      z • (1 : Block b) - C - Bᴴ * (response tail z)⁻¹ * B

/-- Every full tail resolvent and every recursive response is invertible at a
well-posed spectral parameter. -/
def WellPosed : Chain b → ℂ → Prop
  | .terminal C, z => IsUnit (resolvent (.terminal C) z)
  | .prepend C B tail, z =>
      IsUnit (resolvent (.prepend C B tail) z)
        ∧ IsUnit (response (.prepend C B tail) z)
        ∧ WellPosed tail z

theorem wellPosed_resolvent_isUnit :
    ∀ {J : Chain b} {z : ℂ}, WellPosed J z → IsUnit (resolvent J z) := by
  intro J z h
  cases J with
  | terminal => exact h
  | prepend => exact h.1

theorem wellPosed_response_isUnit :
    ∀ {J : Chain b} {z : ℂ}, WellPosed J z → IsUnit (response J z) := by
  intro J z h
  cases J with
  | terminal C => simpa only [WellPosed, response, resolvent, operator] using h
  | prepend => exact h.2.1

theorem wellPosed_tail {C B : Block b} {tail : Chain b} {z : ℂ}
    (h : WellPosed (.prepend C B tail) z) : WellPosed tail z := h.2.2

/-- The terminal response is literally `zI-C_m`. -/
@[simp] theorem response_terminal (C : Block b) (z : ℂ) :
    response (.terminal C) z = z • (1 : Block b) - C := rfl

/-- The full resolvent of a prepended layer has the expected actual block
form; this is an equality of the constructed global matrix, not an axiom. -/
theorem resolvent_prepend (C B : Block b) (tail : Chain b) (z : ℂ) :
    resolvent (.prepend C B tail) z =
      Matrix.fromBlocks (z • (1 : Block b) - C)
        (-(injectHead tail B)ᴴ) (-(injectHead tail B))
        (resolvent tail z) := by
  unfold resolvent operator
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
  rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp [sub_eq_add_neg, resolvent, operator]
  cases tail <;> rfl

/-- Head embeddings turn compression by a full tail inverse into compression
by its visible block. -/
theorem injectHead_compression (J : Chain b) (B : Block b)
    (X : Matrix (Index J) (Index J) ℂ) :
    (injectHead J B)ᴴ * X * injectHead J B =
      Bᴴ * visibleBlock J X * B := by
  classical
  cases J with
  | terminal C =>
      change Bᴴ * X * B = Bᴴ * X * B
      rfl
  | prepend C D tail =>
      change (Matrix.fromRows B 0)ᴴ * X * Matrix.fromRows B 0 =
        Bᴴ * X.toBlocks₁₁ * B
      rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
        ← Matrix.fromBlocks_toBlocks X,
        Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
      simp [Matrix.mul_assoc]

/-- The visible block of the inverse of every actual full tail resolvent is
the inverse continued-fraction response.  This is the missing derivation from
the global Jacobi matrix. -/
theorem visibleBlock_resolvent_inv_eq_response_inv :
    ∀ (J : Chain b) (z : ℂ), WellPosed J z →
      visibleBlock J ((resolvent J z)⁻¹) = (response J z)⁻¹ := by
  intro J
  induction J with
  | terminal C =>
      intro z hz
      change (z • (1 : Block b) - C)⁻¹ = (z • (1 : Block b) - C)⁻¹
      rfl
  | prepend C B tail ih =>
      intro z hz
      classical
      let I := injectHead tail B
      let A : Block b := z • (1 : Block b) - C
      let D := resolvent tail z
      have htail := wellPosed_tail hz
      have hDunit : IsUnit D := wellPosed_resolvent_isUnit htail
      have hRunit : IsUnit (response (.prepend C B tail) z) := hz.2.1
      letI : Invertible D := hDunit.invertible
      have htailInv : visibleBlock tail D⁻¹ = (response tail z)⁻¹ := ih z htail
      have hcompression : Iᴴ * D⁻¹ * I = Bᴴ * (response tail z)⁻¹ * B := by
        rw [injectHead_compression, htailInv]
      have hSchur : A - (-Iᴴ) * D⁻¹ * (-I) = response (.prepend C B tail) z := by
        simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
        rw [hcompression]
        rfl
      have hSchurOf : A - (-Iᴴ) * ⅟D * (-I) =
          response (.prepend C B tail) z := by
        simpa only [Matrix.invOf_eq_nonsing_inv] using hSchur
      letI hResponseInst : Invertible (response (.prepend C B tail) z) :=
        hRunit.invertible
      haveI hSchurInst : Invertible (A - (-Iᴴ) * ⅟D * (-I)) :=
        hRunit.invertible.copy _ (by
          rw [Matrix.invOf_eq_nonsing_inv, hSchur])
      haveI hBlockInst : Invertible (Matrix.fromBlocks A (-Iᴴ) (-I) D) :=
        Matrix.fromBlocks₂₂Invertible A (-Iᴴ) (-I) D
      have hInv := Matrix.invOf_fromBlocks₂₂_eq A (-Iᴴ) (-I) D
      have hres : resolvent (.prepend C B tail) z =
          Matrix.fromBlocks A (-Iᴴ) (-I) D := by
        simpa [A, D, I] using resolvent_prepend C B tail z
      change ((resolvent (.prepend C B tail) z)⁻¹).toBlocks₁₁ =
        (response (.prepend C B tail) z)⁻¹
      have hcorner : ((Matrix.fromBlocks A (-Iᴴ) (-I) D)⁻¹).toBlocks₁₁ =
          (response (.prepend C B tail) z)⁻¹ := by
        rw [← Matrix.invOf_eq_nonsing_inv, hInv,
          Matrix.toBlocks_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv,
          hSchurOf]
      simpa only [hres] using hcorner

/-- The actual response tower obeys both the terminal condition and the
forward Schur recursion, and agrees with the visible inverse corner of the
global block-Jacobi resolvent at every well-posed parameter. -/
theorem actualJacobi_continuedFraction_certificate (J : Chain b) (z : ℂ)
    (hJ : WellPosed J z) :
    visibleBlock J ((resolvent J z)⁻¹) = (response J z)⁻¹
      ∧ (∀ C, response (.terminal C) z = z • (1 : Block b) - C)
      ∧ (∀ C B tail,
          response (.prepend C B tail) z =
            z • (1 : Block b) - C - Bᴴ * (response tail z)⁻¹ * B) := by
  exact ⟨visibleBlock_resolvent_inv_eq_response_inv J z hJ,
    fun _ => rfl, fun _ _ _ => rfl⟩

end Chain

end NCG.FiniteBlockJacobiChainExact
