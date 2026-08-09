/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.EfficientConnectedScore

/-!
# Exact EASY 47: visibility and explanation innovations

The existing theorem proves the nuisance-explanation identity.  This file
adds the missing visibility innovation: a refined connected response splits
orthogonally into its embedded old response and the new visible rows.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedDecidableInType false

/-- Pythagoras for a strict response refinement.  `e` embeds the old
connected-response carrier, `j` embeds the old coefficient space, and
`eᴴ Gnew j = Gold` is preservation of the old response. -/
theorem visibility_refinement_innovation
    {Hn Hm kn km : Type*}
    [Fintype Hn] [Fintype Hm] [Fintype kn] [Fintype km]
    [DecidableEq Hn] [DecidableEq Hm]
    (Gnew : Matrix Hn kn Complex) (Gold : Matrix Hm km Complex)
    (e : Matrix Hn Hm Complex) (j : Matrix kn km Complex)
    (he : eᴴ * e = (1 : Matrix Hm Hm Complex))
    (hcompat : eᴴ * Gnew * j = Gold) :
    jᴴ * (Gnewᴴ * Gnew) * j
      = Goldᴴ * Gold
        + jᴴ * Gnewᴴ * ((1 : Matrix Hn Hn Complex) - e * eᴴ)
          * Gnew * j
    ∧ (jᴴ * Gnewᴴ * ((1 : Matrix Hn Hn Complex) - e * eᴴ)
          * Gnew * j).PosSemidef := by
  let Q : Matrix Hn Hn Complex := 1 - e * eᴴ
  have hQH : Qᴴ = Q := by
    simp [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have hEE : (e * eᴴ) * (e * eᴴ) = e * eᴴ := by
    rw [Matrix.mul_assoc e eᴴ (e * eᴴ),
      ← Matrix.mul_assoc eᴴ e eᴴ, he, Matrix.one_mul]
  have hQ2 : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hEE]
    abel
  have hold : Goldᴴ * Gold
      = jᴴ * Gnewᴴ * (e * eᴴ) * Gnew * j := by
    rw [← hcompat]
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hgram : jᴴ * Gnewᴴ * Q * Gnew * j
      = (Q * Gnew * j)ᴴ * (Q * Gnew * j) := by
    calc
      jᴴ * Gnewᴴ * Q * Gnew * j
          = jᴴ * Gnewᴴ * (Q * Q) * Gnew * j := by rw [hQ2]
      _ = (Q * Gnew * j)ᴴ * (Q * Gnew * j) := by
        simp only [Matrix.conjTranspose_mul, hQH, Matrix.mul_assoc]
  constructor
  · rw [hold]
    simp only [Q, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  · change (jᴴ * Gnewᴴ * Q * Gnew * j).PosSemidef
    rw [hgram]
    exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The complete refinement packet: positive visibility innovation together
with the existing positive explanation innovation. -/
theorem interaction_refinement_innovations_exact
    {Hn Hm kn km : Type*}
    [Fintype Hn] [Fintype Hm] [Fintype kn] [Fintype km]
    [DecidableEq Hn] [DecidableEq Hm]
    (Gnew : Matrix Hn kn Complex) (Gold : Matrix Hm km Complex)
    (e : Matrix Hn Hm Complex) (j : Matrix kn km Complex)
    (he : eᴴ * e = (1 : Matrix Hm Hm Complex))
    (hcompat : eᴴ * Gnew * j = Gold) :
    jᴴ * (Gnewᴴ * Gnew) * j
      = Goldᴴ * Gold
        + jᴴ * Gnewᴴ * ((1 : Matrix Hn Hn Complex) - e * eᴴ)
          * Gnew * j
    ∧ (jᴴ * Gnewᴴ * ((1 : Matrix Hn Hn Complex) - e * eᴴ)
          * Gnew * j).PosSemidef :=
  visibility_refinement_innovation Gnew Gold e j he hcompat

end NCG
