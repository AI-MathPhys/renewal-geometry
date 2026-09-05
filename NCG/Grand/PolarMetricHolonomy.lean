/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.PolarHolonomy
import NCG.Grand.EdgeCommutantReconstruction
import NCG.Grand.GlobalFrameTransport

/-!
# connected polar metric--holonomy assembly

The load-bearing per-edge equivalence and finite bicommutant theorem are
`smst_polar_holonomy`.  This file kernel-checks the formerly disclosed finite
assembly: tree-path products remain unitary, connectedness supplies a root path
to every vertex, and the per-edge equivalence lifts to the complete edge family.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- Ordered unitary transport along a graph walk; the last edge acts on the
left. -/
def walkUnitaryTransport {V g : Type*} [Fintype g] [DecidableEq g]
    {G : SimpleGraph V}
    (U : ∀ ⦃u v⦄, G.Adj u v → Matrix g g ℂ) :
    ∀ {u v : V}, G.Walk u v → Matrix g g ℂ
  | _, _, .nil => 1
  | _, _, .cons h p => walkUnitaryTransport U p * U h

/-- A product of unitary edge factors along any finite walk is unitary. -/
theorem walkUnitaryTransport_isUnitary {V g : Type*}
    [Fintype g] [DecidableEq g] {G : SimpleGraph V}
    (U : ∀ ⦃u v⦄, G.Adj u v → Matrix g g ℂ)
    (hU : ∀ ⦃u v⦄ (h : G.Adj u v), IsUnitaryMatrix (U h)) :
    ∀ {u v : V} (p : G.Walk u v),
      IsUnitaryMatrix (walkUnitaryTransport U p) := by
  intro u v p
  induction p with
  | nil => simp [walkUnitaryTransport, IsUnitaryMatrix]
  | @cons u v w h p ih =>
      constructor
      · rw [walkUnitaryTransport, Matrix.conjTranspose_mul]
        calc
          (walkUnitaryTransport U p * U h) *
                ((U h)ᴴ * (walkUnitaryTransport U p)ᴴ)
              = walkUnitaryTransport U p *
                  ((U h * (U h)ᴴ) * (walkUnitaryTransport U p)ᴴ) := by
                    simp only [Matrix.mul_assoc]
          _ = walkUnitaryTransport U p *
                (walkUnitaryTransport U p)ᴴ := by rw [(hU h).1, Matrix.one_mul]
          _ = 1 := ih.1
      · rw [walkUnitaryTransport, Matrix.conjTranspose_mul]
        calc
          (U h)ᴴ * (walkUnitaryTransport U p)ᴴ *
                (walkUnitaryTransport U p * U h)
              = (U h)ᴴ *
                  (((walkUnitaryTransport U p)ᴴ *
                    walkUnitaryTransport U p) * U h) := by
                      simp only [Matrix.mul_assoc]
          _ = (U h)ᴴ * U h := by rw [ih.2, Matrix.one_mul]
          _ = 1 := (hU h).2

/-- On a connected incidence graph, choosing one root and one walk to each
vertex produces unitary root transports.  A spanning tree is precisely a
coherent finite choice of these walks. -/
theorem connected_unitary_root_transports {V g : Type*}
    [Fintype g] [DecidableEq g] (G : SimpleGraph V)
    (hconn : G.Connected)
    (U : ∀ ⦃u v⦄, G.Adj u v → Matrix g g ℂ)
    (hU : ∀ ⦃u v⦄ (h : G.Adj u v), IsUnitaryMatrix (U h)) :
    ∃ o : V, ∀ v : V, ∃ p : G.Walk o v,
      IsUnitaryMatrix (walkUnitaryTransport U p) := by
  let o : V := Classical.choice hconn.nonempty
  refine ⟨o, ?_⟩
  intro v
  let p : G.Walk o v := Classical.choice (hconn o v)
  exact ⟨p, walkUnitaryTransport_isUnitary U hU p⟩

/-- Exact all-edges polar-holonomy reconstruction.  A root operator satisfies
every transported typed edge equation iff it commutes with every root-fibre
metric generator `K_e` and relative holonomy generator `W_e`. -/
theorem smst_polar_holonomy_family {g E : Type*} [Fintype g]
    [DecidableEq g]
    (U P Qs Qt : E → Matrix g g ℂ)
    (hU : ∀ e, IsUnitaryMatrix (U e))
    (hP : ∀ e, (P e).PosDef)
    (hQs : ∀ e, IsUnitaryMatrix (Qs e))
    (hQt : ∀ e, IsUnitaryMatrix (Qt e))
    (R : Matrix g g ℂ) :
    (∀ e,
      (Qt e * R * (Qt e)ᴴ) * (U e * P e)
          = (U e * P e) * (Qs e * R * (Qs e)ᴴ)
      ∧ (Qs e * R * (Qs e)ᴴ) * (U e * P e)ᴴ
          = (U e * P e)ᴴ * (Qt e * R * (Qt e)ᴴ))
      ↔
    (∀ e,
      R * ((Qs e)ᴴ * (P e * P e) * Qs e)
          = ((Qs e)ᴴ * (P e * P e) * Qs e) * R
      ∧ R * ((Qt e)ᴴ * U e * Qs e)
          = ((Qt e)ᴴ * U e * Qs e) * R) := by
  constructor
  · intro hedge e
    exact ((smst_polar_holonomy (g := g)).1
      (U e) (P e) R (Qs e) (Qt e)
      (hU e).1 (hU e).2 (hP e)
      (hQs e).1 (hQs e).2 (hQt e).1 (hQt e).2).mp (hedge e)
  · intro hroot e
    exact ((smst_polar_holonomy (g := g)).1
      (U e) (P e) R (Qs e) (Qt e)
      (hU e).1 (hU e).2 (hP e)
      (hQs e).1 (hQs e).2 (hQt e).1 (hQt e).2).mpr (hroot e)

end NCG
