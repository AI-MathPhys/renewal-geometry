/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Gauge normalization indices and the oriented-edge quotient
  (`thm:absolute-gauge-normalization`, `thm:oriented-edge-quotient`,
   SM_emergence)

* `weak_index_one_generation` / `colour_index_one_generation` /
  `hypercharge_index_one_generation` — the one-generation Dynkin
  index sums: the four weak doublets (coloured `Q_L` and `L_L`)
  give `I₂ = 2`, the four colour triplets (`u_L,d_L,u_R,d_R`) give
  `I₃ = 2`, and the hypercharge square sum over the fifteen Weyl
  components gives `I_Y = 10/3`;
* `gauge_coupling_normalization` — the boxed normalization
  `g_a²I_a = 2 ↔ g_a² = 2/I_a`;
* `oriented_edge_separation` / `oriented_edge_quotient` — on `K₄`,
  distinct terminal oriented edges have distinct one-step future
  laws (kernel-checked), so under the last-edge assumption the
  predictive quotient of nontrivial histories is canonically the
  set of oriented edges `E⃗(K₄)`.

The identification of the bosonic action with the extensive
expected odd-record count per normalized lapse (which fixes the
constant `2`) is the declared normalization input.
-/

namespace NCG

open Finset

/-- Weak isospin index: four doublets (three colours of `Q_L` plus
`L_L`), each contributing `1/2`: `I₂⁽¹⁾ = 2`. -/
theorem weak_index_one_generation :
    (3 + 1 : ℚ) * (1 / 2) = 2 := by norm_num

/-- Colour index: four triplets (`u_L, d_L, u_R, d_R`), each
contributing `1/2`: `I₃⁽¹⁾ = 2`. -/
theorem colour_index_one_generation :
    (4 : ℚ) * (1 / 2) = 2 := by norm_num

/-- Hypercharge index: the square sum over one generation of Weyl
components — six `Q_L` at `1/6`, three `u_R` at `2/3`, three `d_R`
at `-1/3`, two `L_L` at `-1/2`, one `e_R` at `-1`:
`I_Y⁽¹⁾ = 10/3`. -/
theorem hypercharge_index_one_generation :
    6 * (1 / 6 : ℚ) ^ 2 + 3 * (2 / 3) ^ 2 + 3 * (-(1 / 3)) ^ 2
      + 2 * (-(1 / 2)) ^ 2 + 1 * (-1) ^ 2 = 10 / 3 := by norm_num

/-- The boxed normalization: `g_a²I_a = 2` iff `g_a² = 2/I_a`. -/
theorem gauge_coupling_normalization (I g2 : ℚ) (hI : I ≠ 0) :
    g2 * I = 2 ↔ g2 = 2 / I := by
  rw [eq_div_iff hI]

/-- The one-step future law of an oriented edge of `K₄`: its
admissible nonbacktracking continuations. -/
def k4NextEdges (e : Fin 4 × Fin 4) : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter
    (fun f => f.1 = e.2 ∧ f.2 ≠ e.1 ∧ f.2 ≠ e.2)

/-- Distinct oriented edges of `K₄` have distinct one-step future
laws — including each reversed pair. -/
theorem oriented_edge_separation :
    ∀ e f : Fin 4 × Fin 4, e.1 ≠ e.2 → f.1 ≠ f.2 → e ≠ f →
      k4NextEdges e ≠ k4NextEdges f := by
  decide

/-- `thm:oriented-edge-quotient`: under the last-edge assumption
(the future law of a nontrivial history is the one-step law of its
terminal oriented edge), two histories have identical future laws
iff they share the terminal oriented edge: the predictive quotient
is canonically `E⃗(K₄)`. -/
theorem oriented_edge_quotient {H : Type*}
    (term : H → Fin 4 × Fin 4)
    (law : H → Finset (Fin 4 × Fin 4))
    (hvalid : ∀ h, (term h).1 ≠ (term h).2)
    (hlaw : ∀ h, law h = k4NextEdges (term h)) (h1 h2 : H) :
    law h1 = law h2 ↔ term h1 = term h2 := by
  rw [hlaw h1, hlaw h2]
  constructor
  · intro heq
    by_contra hne
    exact oriented_edge_separation (term h1) (term h2)
      (hvalid h1) (hvalid h2) hne heq
  · intro heq
    rw [heq]

end NCG
