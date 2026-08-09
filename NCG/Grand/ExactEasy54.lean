/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.GrandWedderburn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Exact EASY 54: connected edge-commutant reconstruction

`smst_edge_commutant` proves the exact commutant reconstruction across one
nondegenerate incidence edge.  This file supplies the finite-walk iteration
used in the manuscript: invertible edge transport propagates the multiplicity
block by conjugation, and equality of endpoint dimensions propagates through
a connected incidence graph.
-/

open Matrix

namespace NCG

variable {V g : Type*} (G : SimpleGraph V)

/-- Equality of multiplicity dimensions propagates along every incidence
walk. -/
theorem dimension_eq_of_walk (d : V → ℕ)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → d u = d v) :
    ∀ {u v : V}, G.Walk u v → d u = d v := by
  intro u v p
  induction p with
  | nil => rfl
  | cons h p ih => exact (hedge h).trans ih

/-- A connected incidence graph whose edge maps are between equal-dimensional
multiplicity spaces has one common multiplicity dimension. -/
theorem connected_common_dimension (hconn : G.Connected) (d : V → ℕ)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → d u = d v) :
    ∃ n : ℕ, ∀ v : V, d v = n := by
  let v₀ : V := Classical.choice hconn.nonempty
  refine ⟨d v₀, ?_⟩
  intro v
  exact (dimension_eq_of_walk G d hedge (Classical.choice (hconn v v₀)))

/-- Ordered product of the forward link matrices along a walk. -/
def smstWalkForwardTransport [Fintype g] [DecidableEq g]
    (F : ∀ ⦃u v⦄, G.Adj u v → Matrix g g ℂ) :
    ∀ {u v : V}, G.Walk u v → Matrix g g ℂ
  | _, _, .nil => 1
  | _, _, .cons h p => F h * smstWalkForwardTransport F p

/-- Ordered product of the inverse link matrices along a walk. -/
def smstWalkReverseTransport [Fintype g] [DecidableEq g]
    (Finv : ∀ ⦃u v⦄, G.Adj u v → Matrix g g ℂ) :
    ∀ {u v : V}, G.Walk u v → Matrix g g ℂ
  | _, _, .nil => 1
  | _, _, .cons h p => smstWalkReverseTransport Finv p * Finv h

/-- The one-edge commutant equation iterates along every finite incidence
walk.  Thus the endpoint block is conjugate to the starting block by the
ordered product of invertible links. -/
theorem edge_transport_of_walk [Fintype g] [DecidableEq g]
    (R : V → Matrix g g ℂ)
    (F Finv : ∀ ⦃u v⦄, G.Adj u v → Matrix g g ℂ)
    (hedge : ∀ ⦃u v⦄ (h : G.Adj u v),
      R v = Finv h * R u * F h) :
    ∀ {u v : V} (p : G.Walk u v),
      R v = smstWalkReverseTransport G Finv p * R u *
        smstWalkForwardTransport G F p := by
  intro u v p
  induction p with
  | nil => simp [smstWalkForwardTransport, smstWalkReverseTransport]
  | @cons u v w h p ih =>
      rw [ih, hedge h]
      simp only [smstWalkForwardTransport, smstWalkReverseTransport,
        Matrix.mul_assoc]

/-- Connected form of exact edge transport: every multiplicity block is
obtained from one root block by transport along any chosen incidence walk. -/
theorem connected_edge_transport [Fintype g] [DecidableEq g]
    (hconn : G.Connected)
    (R : V → Matrix g g ℂ)
    (F Finv : ∀ ⦃u v⦄, G.Adj u v → Matrix g g ℂ)
    (hedge : ∀ ⦃u v⦄ (h : G.Adj u v),
      R v = Finv h * R u * F h) :
    ∃ v₀ : V, ∀ v : V, ∃ p : G.Walk v₀ v,
      R v = smstWalkReverseTransport G Finv p * R v₀ *
        smstWalkForwardTransport G F p := by
  let v₀ : V := Classical.choice hconn.nonempty
  refine ⟨v₀, ?_⟩
  intro v
  let p : G.Walk v₀ v := Classical.choice (hconn v₀ v)
  exact ⟨p, edge_transport_of_walk G R F Finv hedge p⟩

end NCG
