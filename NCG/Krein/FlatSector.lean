/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Krein.CoverModel

/-!
# The flat sector is abelian: why the Clifford twist must be dynamical

The manuscript separates two roles that are easy to conflate: flat graph
holonomy supplies the *sector labels* `H¹(G, ℤ/2)`, but it cannot supply
the Clifford anticommutation — the flat sector algebra is **commutative**.
This file proves the operator content of that separation in the
finsupp cover model:

* `NCG.shiftOp_comp` — composition of shifts is the shift of the
  composite;
* `NCG.sheetShift_comm` — **Proposition `prop:flat-spatial-block-zero`**:
  sheet translations of the abelian cover commute, so the flat spatial
  commutator block vanishes, `ω|_{H×H} = 0`;
* `NCG.diagOp_comm` (in `NCG.Operator.Diagonal`) together with
  `NCG.sheetShift_add` — **Proposition `prop:flat-holonomy-obstruction`**:
  the flat holonomy sector operators multiply additively in their labels,
  `J_α J_β = J_{α+β} = J_β J_α`; the sector algebra is the commutative
  group algebra, not a Clifford algebra.  The spatial–spatial twist must
  come from modular/internal dynamics
  (`NCG.Algebra.ProjectiveDefect`);
* `NCG.scalar_compression` — **Theorem `thm:exact-bicharacter-stabilisation`**:
  an exact scalar commutator identity survives compression by every
  diagonal (shell) projection, so the finite-shell modular Gram data are
  shell-independent, `ω_N ≡ ω`.
-/

namespace NCG

open Finsupp

variable {ι : Type*}

/-- Composition of shift operators is the shift of the composite map. -/
theorem shiftOp_comp (s t : ι → ι) :
    shiftOp (ι := ι) s ∘ₗ shiftOp t = shiftOp (s ∘ t) := by
  apply Finsupp.lhom_ext
  intro i c
  simp [Function.comp_apply]

/-- Shifts along commuting maps commute. -/
theorem shiftOp_comm_of_comm {s t : ι → ι} (hst : s ∘ t = t ∘ s) :
    shiftOp (ι := ι) s ∘ₗ shiftOp t = shiftOp t ∘ₗ shiftOp s := by
  rw [shiftOp_comp, shiftOp_comp, hst]

variable {V H : Type*} [AddCommGroup H]

/-- The **sheet translation** by a holonomy label `α` on the abelian cover
`V × H`: the undressed flat realization of the revision `R_α`. -/
noncomputable def sheetShift (α : H) :
    ((V × H) →₀ ℂ) →ₗ[ℂ] ((V × H) →₀ ℂ) :=
  shiftOp fun p => (p.1, p.2 + α)

/-- Sheet translations compose additively:
`S_α ∘ S_β = S_{α+β}` — the flat sector operators multiply as the group
algebra of `H` (Proposition `prop:flat-holonomy-obstruction`). -/
theorem sheetShift_add (α β : H) :
    sheetShift (V := V) α ∘ₗ sheetShift β = sheetShift (β + α) := by
  rw [sheetShift, sheetShift, sheetShift, shiftOp_comp]
  congr 1
  funext p
  simp [Function.comp_apply, add_assoc]

/-- **Proposition `prop:flat-spatial-block-zero`** (flat sheet transport
has trivial spatial block): sheet translations commute, so the group
commutator of any two undressed flat revisions is the identity and the
spatial–spatial block of the modular commutator form vanishes,
`ω|_{H×H} = 0`.  Combined with `prop:flat-holonomy-obstruction` this is
why the Clifford twist requires nonabelian internal transport
(`thm:nonabelian-holonomy-necessary`). -/
theorem sheetShift_comm (α β : H) :
    sheetShift (V := V) α ∘ₗ sheetShift β
      = sheetShift β ∘ₗ sheetShift α := by
  rw [sheetShift_add, sheetShift_add, add_comm]

/-- **Theorem `thm:exact-bicharacter-stabilisation`** (exact-bicharacter
stabilisation): an exact scalar operator identity `C = c·1` — such as the
revision commutator `R_α R_β R_α⁻¹ R_β⁻¹ = (−1)^{ω(α,β)}·1` — survives
compression by every diagonal shell projection `P`:
`P C P = c · P²`, and for an idempotent shell symbol `P C P = c · P`.
Hence the finite-shell modular Gram matrices are shell-independent,
`ω_N ≡ ω` on every nonempty shell. -/
theorem scalar_compression (p : ι → ℂ) (hp : ∀ i, p i * p i = p i)
    (c : ℂ) :
    diagOp p ∘ₗ (c • LinearMap.id) ∘ₗ diagOp p = c • diagOp p := by
  apply Finsupp.lhom_ext
  intro i x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    diagOp_single, Finsupp.smul_single, smul_eq_mul]
  congr 1
  linear_combination c * x * hp i

end NCG
