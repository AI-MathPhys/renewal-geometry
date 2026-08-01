/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Full-symmetry dark no-go (`cor:v5-s4-dark-nogo`, SM manuscript)

`H¹(K₄;𝔽₂) ≅ 𝔽₂³`: the explicit linear map `qF2` on the six edge
indicators (edge order `01,02,03,12,13,23`) has kernel exactly the
mod-2 coboundaries (`qF2_ker`, by `decide`), so it realizes the
cohomology.  The three adjacent vertex transpositions act on edge
functions by the permutations `edgeS01/S12/S23` and descend through
`qF2` to the matrices `w01/w12/w23` (`qF2_equivariant`).  In this
coordinate system:

* opposite edge classes sum to the `S₄`-fixed triangle class
  `τ = (1,1,1)`: `[e] + [ē] = τ` (`opposite_edge_tau`);
* `⟨τ⟩` is the unique invariant line (`invariant_line_unique`);
* there is **no** `S₄`-invariant plane (`s4_dark_nogo`): an exactly
  `S₄`-covariant charged source cannot have charged rank two, hence
  cannot select one unique dark parity (the dark-parity reading of
  rank two is interpretive prose; the formal content is the
  invariant-subspace classification `0, ⟨τ⟩, H¹`).
-/

namespace NCG

/-- The six edges of `K₄` as ordered vertex pairs. -/
def ends6 : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

/-- The mod-2 coboundary on `K₄`. -/
def cellDF2 (f : Fin 4 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun e => f (ends6 e).1 + f (ends6 e).2

/-- Coordinates of a one-cochain class in the basis
`[χ₀₁], [χ₀₂], [χ₁₂]` of `H¹(K₄;𝔽₂)`. -/
def qF2 (x : Fin 6 → ZMod 2) : Fin 3 → ZMod 2 :=
  ![x 0 + x 2 + x 4, x 1 + x 2 + x 5, x 3 + x 4 + x 5]

/-- Edge action of the vertex transposition `(0 1)`. -/
def edgeS01 : Fin 6 → Fin 6 := ![0, 3, 4, 1, 2, 5]

/-- Edge action of the vertex transposition `(1 2)`. -/
def edgeS12 : Fin 6 → Fin 6 := ![1, 0, 2, 3, 5, 4]

/-- Edge action of the vertex transposition `(2 3)`. -/
def edgeS23 : Fin 6 → Fin 6 := ![0, 2, 1, 4, 3, 5]

/-- Descended action of `(0 1)` on `H¹` coordinates. -/
def w01 (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 := ![v 0, v 2, v 1]

/-- Descended action of `(1 2)` on `H¹` coordinates. -/
def w12 (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 := ![v 1, v 0, v 2]

/-- Descended action of `(2 3)` on `H¹` coordinates. -/
def w23 (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  ![v 0 + v 1 + v 2, v 1, v 2]

/-- The `S₄`-fixed triangle class `τ`. -/
def tauF2 : Fin 3 → ZMod 2 := ![1, 1, 1]

/-- `qF2` realizes `H¹(K₄;𝔽₂)`: its kernel is exactly the mod-2
coboundary space. -/
lemma qF2_ker : ∀ x : Fin 6 → ZMod 2,
    qF2 x = 0 ↔ ∃ f : Fin 4 → ZMod 2, cellDF2 f = x := by decide

/-- The transposition actions descend through `qF2` to
`w01`, `w12`, `w23`. -/
lemma qF2_equivariant : ∀ x : Fin 6 → ZMod 2,
    qF2 (fun e => x (edgeS01 e)) = w01 (qF2 x)
    ∧ qF2 (fun e => x (edgeS12 e)) = w12 (qF2 x)
    ∧ qF2 (fun e => x (edgeS23 e)) = w23 (qF2 x) := by decide

/-- Opposite edge classes sum to the triangle class:
`[e] + [ē] = τ` for the three opposite pairs `(01,23)`, `(02,13)`,
`(03,12)`. -/
lemma opposite_edge_tau :
    (qF2 ![1,0,0,0,0,0] + qF2 ![0,0,0,0,0,1] = tauF2)
    ∧ (qF2 ![0,1,0,0,0,0] + qF2 ![0,0,0,0,1,0] = tauF2)
    ∧ (qF2 ![0,0,1,0,0,0] + qF2 ![0,0,0,1,0,0] = tauF2) := by decide

/-- `⟨τ⟩` is the unique `S₄`-invariant line in `H¹(K₄;𝔽₂)`. -/
lemma invariant_line_unique : ∀ a : Fin 3 → ZMod 2, a ≠ 0 →
    ((w01 a = a ∧ w12 a = a ∧ w23 a = a) ↔ a = tauF2) := by decide

/-- A plane `{0, a, b, a+b}` is preserved by `U` iff it maps both
generators into the plane. -/
def planeInv (U : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))
    (a b : Fin 3 → ZMod 2) : Prop :=
  (U a = 0 ∨ U a = a ∨ U a = b ∨ U a = a + b)
  ∧ (U b = 0 ∨ U b = a ∨ U b = b ∨ U b = a + b)

instance (U : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))
    (a b : Fin 3 → ZMod 2) : Decidable (planeInv U a b) := by
  unfold planeInv
  infer_instance

/-- `cor:v5-s4-dark-nogo`: no plane of `H¹(K₄;𝔽₂)` is invariant
under all of `S₄` — an exactly `S₄`-covariant charged source
cannot have charged rank two. -/
theorem s4_dark_nogo : ∀ a b : Fin 3 → ZMod 2,
    a ≠ 0 → b ≠ 0 → a ≠ b →
    ¬ (planeInv w01 a b ∧ planeInv w12 a b ∧ planeInv w23 a b) := by
  decide

end NCG
