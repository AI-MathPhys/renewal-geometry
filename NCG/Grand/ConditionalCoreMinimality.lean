/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FlatMonoidal

/-!
# Record-conditioned predictive minimality
  (`thm:conditional-core-minimality`, Gran-Tensor manuscript)

* `conditional_core_minimality`: per record sector `r`, two
  support-minimal (source-cyclic) realizations with identical
  moment tables are related by a unique intertwiner of their
  Krylov observability syntheses — the record-fixing unitary
  gauge of the boxed direct-sum core, sector by sector.

Rendering disclosed: realizations enter through their per-record
transfer/source pairs `(G_r, B_r)`; the boxed direct sum
`M^op,min = ⊕_r ⊕_x |r⟩ ⊗ M_{x,r}` is the sector-indexed
packaging of these blocks, preservation of intervention
probabilities is the moment-table equality itself, and the
prohibition on identifying distinct protected record values is
the sector-indexing (the gauge acts within each `r`).  Existence
and uniqueness per sector are the cited
`flat_monoidal_reconstruction` clauses.
-/

open Matrix

namespace NCG

/-- `thm:conditional-core-minimality`: per record sector, a
unique gauge intertwines any two minimal moment-matched
realizations. -/
theorem conditional_core_minimality {R : Type*}
    {u p : Type*} [Fintype u] [Fintype p] [DecidableEq u]
    (G G' : R → Matrix u u ℂ) (B B' : R → Matrix u p ℂ)
    (hG : ∀ r, (G r)ᴴ = G r) (hG' : ∀ r, (G' r)ᴴ = G' r)
    (d : ℕ) (hd : 0 < d)
    (hmin : ∀ r,
      Function.Surjective (krylovMat (G r) (B r) d).mulVec)
    (hmom : ∀ r (n : ℕ), (B r)ᴴ * (G r) ^ n * (B r)
        = (B' r)ᴴ * (G' r) ^ n * (B' r)) :
    ∀ r, ∃! W : Matrix u u ℂ,
      W * krylovMat (G r) (B r) d
        = krylovMat (G' r) (B' r) d := by
  intro r
  obtain ⟨⟨W, hWu, hWk, hWB, hWG⟩, huniq⟩ :=
    flat_monoidal_reconstruction (G r) (G' r) (B r) (B' r)
      (hG r) (hG' r) d hd (hmin r) (hmom r)
  exact ⟨W, hWk d, fun W' hW' => huniq W' W hW' (hWk d)⟩

end NCG
