/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EdgeCommutantReconstruction

/-!
# Graph-wide loaded-edge commutant assembly

The one-edge Kronecker cut and connected-walk propagation were previously
available separately.  This file assembles them into the exact graph-wide
generator commutant used by `thm:SMST-edge-commutant`: commuting with every
loaded incidence generator and its adjoint is equivalent to the two typed
multiplicity intertwining equations on every edge.  It also derives the
common multiplicity dimension from bijectivity of the rectangular links.
-/

open Matrix Kronecker

namespace NCG
namespace GraphLoadedEdgeCommutant

variable {V : Type*} (G : SimpleGraph V)
variable (B M : V → Type*)
variable [∀ v, Fintype (B v)] [∀ v, DecidableEq (B v)]
variable [∀ v, Fintype (M v)] [∀ v, DecidableEq (M v)]

/- A nonzero typed carrier matrix and its multiplicity link on every
oriented graph edge.  Reversing an undirected edge may carry independently
specified data; the theorem is pointwise in the chosen orientation. -/
variable
  (D : ∀ ⦃u v⦄, G.Adj u v → Matrix (B v) (B u) ℂ)
  (F : ∀ ⦃u v⦄, G.Adj u v → Matrix (M v) (M u) ℂ)

/-- The block-diagonal commutant after the external/internal trinity cut is a
family of multiplicity blocks. -/
abbrev MultiplicityBlocks := ∀ v, Matrix (M v) (M v) ℂ

/-- Commutation with every actual loaded edge `D_e ⊗ F_e` and its adjoint. -/
def CommutesWithLoadedEdges (R : MultiplicityBlocks M) : Prop :=
  ∀ ⦃u v⦄ (h : G.Adj u v),
    ((1 : Matrix (B v) (B v) ℂ) ⊗ₖ R v) * (D h ⊗ₖ F h)
        = (D h ⊗ₖ F h) * ((1 : Matrix (B u) (B u) ℂ) ⊗ₖ R u) ∧
    ((1 : Matrix (B u) (B u) ℂ) ⊗ₖ R u) * (D h ⊗ₖ F h)ᴴ
        = (D h ⊗ₖ F h)ᴴ * ((1 : Matrix (B v) (B v) ℂ) ⊗ₖ R v)

/-- The typed multiplicity-graph commutant equations. -/
def TypedMultiplicityCommutant (R : MultiplicityBlocks M) : Prop :=
  ∀ ⦃u v⦄ (h : G.Adj u v),
    R v * F h = F h * R u ∧ R u * (F h)ᴴ = (F h)ᴴ * R v

/-- Cancellation of a nonzero carrier factor in a Kronecker equality. -/
theorem kronecker_left_cancel
    {I J K L : Type*} [Fintype I] [Fintype J]
    [Fintype K] [Fintype L]
    {A : Matrix I J ℂ} (hA : A ≠ 0)
    {P Q : Matrix K L ℂ} (h : A ⊗ₖ P = A ⊗ₖ Q) : P = Q := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra hall
    apply hA
    ext i j
    rw [Matrix.zero_apply]
    by_contra hz
    exact hall ⟨i, j, hz⟩
  ext k l
  have hp := congrFun (congrFun h (i, k)) (j, l)
  simp only [Matrix.kroneckerMap_apply] at hp
  exact mul_left_cancel₀ hij hp

/-- One loaded forward generator cuts exactly to its multiplicity equation. -/
theorem loadedEdge_forward_iff
    {u v : V} (h : G.Adj u v) (hD : D h ≠ 0)
    (Ru : Matrix (M u) (M u) ℂ) (Rv : Matrix (M v) (M v) ℂ) :
    ((1 : Matrix (B v) (B v) ℂ) ⊗ₖ Rv) * (D h ⊗ₖ F h)
        = (D h ⊗ₖ F h) * ((1 : Matrix (B u) (B u) ℂ) ⊗ₖ Ru)
      ↔ Rv * F h = F h * Ru := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  constructor
  · exact kronecker_left_cancel hD
  · intro hmul
    rw [hmul]

/-- One loaded adjoint generator cuts exactly to the reverse multiplicity
equation. -/
theorem loadedEdge_adjoint_iff
    {u v : V} (h : G.Adj u v) (hD : D h ≠ 0)
    (Ru : Matrix (M u) (M u) ℂ) (Rv : Matrix (M v) (M v) ℂ) :
    ((1 : Matrix (B u) (B u) ℂ) ⊗ₖ Ru) * (D h ⊗ₖ F h)ᴴ
        = (D h ⊗ₖ F h)ᴴ * ((1 : Matrix (B v) (B v) ℂ) ⊗ₖ Rv)
      ↔ Ru * (F h)ᴴ = (F h)ᴴ * Rv := by
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  constructor
  · apply kronecker_left_cancel
    intro hzero
    apply hD
    have := congrArg Matrix.conjTranspose hzero
    simpa using this
  · intro hmul
    rw [hmul]

/-- **Graph-wide exact edge-commutant reconstruction.**  Once the trinity
commutant has supplied the block family `R`, commuting with all loaded edge
generators and their adjoints is *equivalent*, without any residual
hypothesis, to membership in the typed multiplicity-graph algebra. -/
theorem loadedEdgeCommutant_iff_typed
    (hD : ∀ ⦃u v⦄ (h : G.Adj u v), D h ≠ 0)
    (R : MultiplicityBlocks M) :
    CommutesWithLoadedEdges G B M D F R ↔
      TypedMultiplicityCommutant G M F R := by
  constructor
  · intro hload u v h
    exact ⟨(loadedEdge_forward_iff G B M D F h (hD h) (R u) (R v)).mp
        (hload h).1,
      (loadedEdge_adjoint_iff G B M D F h (hD h) (R u) (R v)).mp
        (hload h).2⟩
  · intro htyped u v h
    exact ⟨(loadedEdge_forward_iff G B M D F h (hD h) (R u) (R v)).mpr
        (htyped h).1,
      (loadedEdge_adjoint_iff G B M D F h (hD h) (R u) (R v)).mpr
        (htyped h).2⟩

/-- A bijective rectangular multiplicity link forces equality of its endpoint
dimensions. -/
theorem card_eq_of_bijective_link {u v : V} (h : G.Adj u v)
    (hbij : Function.Bijective (Matrix.toLin' (F h))) :
    Fintype.card (M u) = Fintype.card (M v) := by
  let e := LinearEquiv.ofBijective (Matrix.toLin' (F h)) hbij
  have hfin := e.finrank_eq
  simpa using hfin

/-- In a connected incidence graph, bijective links give one common
multiplicity dimension `g`, as asserted by the manuscript. -/
theorem connected_common_multiplicity_dimension
    (hconn : G.Connected)
    (hbij : ∀ ⦃u v⦄ (h : G.Adj u v),
      Function.Bijective (Matrix.toLin' (F h))) :
    ∃ g : ℕ, ∀ v, Fintype.card (M v) = g := by
  apply connected_common_dimension G hconn (fun v => Fintype.card (M v))
  intro u v h
  exact card_eq_of_bijective_link G M F h (hbij h)

/-- Complete graph-level packet for `thm:SMST-edge-commutant`. -/
theorem exact_edge_commutant_reconstruction
    (hD : ∀ ⦃u v⦄ (h : G.Adj u v), D h ≠ 0)
    (hconn : G.Connected)
    (hbij : ∀ ⦃u v⦄ (h : G.Adj u v),
      Function.Bijective (Matrix.toLin' (F h))) :
    (∀ R : MultiplicityBlocks M,
      CommutesWithLoadedEdges G B M D F R ↔
        TypedMultiplicityCommutant G M F R) ∧
    ∃ g : ℕ, ∀ v, Fintype.card (M v) = g :=
  ⟨fun R => loadedEdgeCommutant_iff_typed G B M D F hD R,
    connected_common_multiplicity_dimension G M F hconn hbij⟩

end GraphLoadedEdgeCommutant
end NCG
