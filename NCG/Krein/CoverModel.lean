/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.SignedCover
import NCG.Operator.Diagonal

/-!
# The Krein model on the signed cover

This file realizes the signed sector of the manuscript on the module of
finitely supported vectors over the signed cover `G^χ`
(Definition `def:J-eps`, Proposition `prop:krein-datum`):

* the sheet **sign character** `signValue : ℤ/2 → ℂ`, `η ↦ (-1)^η`;
* the **fundamental symmetry** `kreinJ`, acting diagonally by the sheet
  sign: `J e_{(x,η)} = (-1)^η e_{(x,η)}`;
* the **lifted shifts** `edgeShift e`, with
  `S̃_e e_{(x,η)} = e_{(y, η + χ e)}` for an edge `e : x → y`, and `0` off
  the source fibre.

The operators act on `(G.V × ℤ/2) →₀ ℂ`, the finitely supported vectors on
the vertex set of the signed cover `G^χ` (which is `G.V × ℤ/2` by
Construction `constr:signed-cover`).

## Main results

* `NCG.signValue_add` — multiplicativity of the sheet sign character;
* `NCG.kreinJ_mul_self` — `J² = 1` on basis vectors;
* `NCG.krein_exchange` — the **exchange relation** of Proposition
  `prop:krein-datum`:

  `J_χ ∘ S̃_e = (-1)^{χ e} · (S̃_e ∘ J_χ)`.

  This scalar sign is the algebraic seed of the Lorentzian signature: for a
  nontrivial holonomy class it cannot be gauged away
  (`NCG.Multigraph.isCoboundary_of_holonomy_eq_zero`).
-/

namespace NCG

open Multigraph

/-- The sheet **sign character** `(-1)^η` of the signed cover. -/
def signValue (η : ZMod 2) : ℂ :=
  if η = 0 then 1 else -1

@[simp]
theorem signValue_zero : signValue 0 = 1 := rfl

@[simp]
theorem signValue_one : signValue 1 = -1 := rfl

/-- The sheet sign is multiplicative: `(-1)^{η+η'} = (-1)^η (-1)^{η'}`. -/
theorem signValue_add (η η' : ZMod 2) :
    signValue (η + η') = signValue η * signValue η' := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  rcases h η with hη | hη <;> rcases h η' with hη' | hη' <;>
    subst hη <;> subst hη' <;>
    simp [signValue, h11]

@[simp]
theorem signValue_mul_self (η : ZMod 2) : signValue η * signValue η = 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h η with hη | hη <;> subst hη <;> simp [signValue]

theorem signValue_ne_zero (η : ZMod 2) : signValue η ≠ 0 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h η with hη | hη <;> subst hη <;> simp [signValue]

variable {G : Multigraph}

/-- The **canonical fundamental symmetry** of the signed cover
(Definition `def:J-eps`), acting diagonally by the sheet sign:
`J e_{(x,η)} = (-1)^η e_{(x,η)}`. -/
noncomputable def kreinJ (G : Multigraph) :
    ((G.V × ZMod 2) →₀ ℂ) →ₗ[ℂ] ((G.V × ZMod 2) →₀ ℂ) :=
  diagOp fun p => signValue p.2

@[simp]
theorem kreinJ_single (p : G.V × ZMod 2) (c : ℂ) :
    kreinJ G (Finsupp.single p c) = Finsupp.single p (signValue p.2 * c) := by
  simp [kreinJ]

/-- `J² = 1`: the fundamental symmetry is an involution
(Proposition `prop:krein-datum`). -/
theorem kreinJ_mul_self (G : Multigraph) :
    kreinJ G ∘ₗ kreinJ G = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro p c
  simp only [LinearMap.comp_apply, kreinJ_single, LinearMap.id_apply]
  rw [← mul_assoc, signValue_mul_self, one_mul]

/-- The **lifted shift** `S̃_e` along an edge `e : x → y` of the base graph
(Definition `def:J-eps`): `S̃_e e_{(x,η)} = e_{(y, η + χ e)}` on the source
fibre, `0` elsewhere. -/
noncomputable def edgeShift [DecidableEq G.V] (χ : G.E → ZMod 2) (e : G.E) :
    ((G.V × ZMod 2) →₀ ℂ) →ₗ[ℂ] ((G.V × ZMod 2) →₀ ℂ) :=
  Finsupp.lsum ℂ fun p =>
    if p.1 = G.src e then Finsupp.lsingle (G.tgt e, p.2 + χ e) else 0

@[simp]
theorem edgeShift_single [DecidableEq G.V] (χ : G.E → ZMod 2) (e : G.E)
    (p : G.V × ZMod 2) (c : ℂ) :
    edgeShift χ e (Finsupp.single p c)
      = if p.1 = G.src e then Finsupp.single (G.tgt e, p.2 + χ e) c
        else 0 := by
  by_cases h : p.1 = G.src e <;>
    simp [edgeShift, Finsupp.lsum_single, Finsupp.lsingle_apply,
      LinearMap.zero_apply, h]

/-- **The Krein exchange relation** (Proposition `prop:krein-datum`):

`J_χ ∘ S̃_e = (-1)^{χ e} · (S̃_e ∘ J_χ)`.

The fundamental symmetry commutes with a lifted shift exactly up to the sign
`χ(e)` of the edge; products of these signs around loops are the holonomy
class `[χ] ∈ H¹(G, ℤ/2)`, which is the non-removable content of the signed
sector (Theorem `thm:cover`). -/
theorem krein_exchange [DecidableEq G.V] (χ : G.E → ZMod 2) (e : G.E) :
    kreinJ G ∘ₗ edgeShift χ e
      = signValue (χ e) • (edgeShift χ e ∘ₗ kreinJ G) := by
  apply Finsupp.lhom_ext
  intro p c
  by_cases h : p.1 = G.src e
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, edgeShift_single,
      kreinJ_single, h, if_true, Finsupp.smul_single, smul_eq_mul]
    congr 1
    rw [signValue_add]
    ring
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, edgeShift_single,
      kreinJ_single, h, if_false, map_zero, smul_zero]

end NCG
