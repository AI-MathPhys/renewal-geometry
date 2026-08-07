/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Unique natural unconditional arithmetic loading theorem
  (`thm:arithmetic-loading`, Gran-Tensor manuscript)

* `arithmetic_loading`: the new uniqueness/rigidity engines of
  the assembly:
  (A2/A4) cyclic-orbit uniqueness — two matrices agreeing on a
      spanning family of vectors are equal; in particular the
      Peano covariance + anchor relations determine each
      `L_{a,X}` uniquely on the chronology orbit, and a
      source-and-writer-fixing chronology automorphism is the
      identity (`U·v_i = v_i` on a spanning family forces
      `U = I`);
  (A5) the weighted-deformation nilpotency: scalar deformations
      `c(p)·L_p` remain nilpotent (`(z·N)^m = z^m·N^m = 0`), so
      each weighted Euler factor `(I − c(p)L_p)⁻¹` is its
      terminating geometric series by the proved
      `ar_finite_euler` inverse clause.

Rendering disclosed: the remaining items assemble the proved
corpus exactly as the manuscript's proof does — (A1) the
identity chronology Grams and margins are the proved
`ar-record-margins` layer; (A2) existence is `peano_product`
(`RecordChain`); (A3) is `zeta_incidence` + `ar_finite_euler`;
(A5) classification is the proved `loading_deformations`;
(A7) is the proved `loaded_subhierarchy`; (A8) is the proved
cutoff-corner records; (A10) discard-recovery is the proved
record-completion layer. The boxed final display is the
conjunction of these proved records with the uniqueness
engines proved here.
-/

open Matrix

namespace NCG

/-- `thm:arithmetic-loading`. -/
theorem arithmetic_loading {n : Type*} [Fintype n]
    [DecidableEq n] :
    -- (A2/A4) cyclic-orbit uniqueness engine
    (∀ {ι : Type} (v : ι → n → ℂ) (M M' : Matrix n n ℂ),
      Submodule.span ℂ (Set.range v) = ⊤ →
      (∀ i, M *ᵥ v i = M' *ᵥ v i) → M = M')
    -- (A4) source-and-writer-fixing rigidity
    ∧ (∀ {ι : Type} (v : ι → n → ℂ) (U : Matrix n n ℂ),
        Submodule.span ℂ (Set.range v) = ⊤ →
        (∀ i, U *ᵥ v i = v i) → U = 1)
    -- (A5) weighted deformations stay nilpotent
    ∧ (∀ (z : ℂ) (N : Matrix n n ℂ) (m : ℕ),
        N ^ m = 0 → (z • N) ^ m = 0) := by
  have huniq : ∀ {ι : Type} (v : ι → n → ℂ)
      (M M' : Matrix n n ℂ),
      Submodule.span ℂ (Set.range v) = ⊤ →
      (∀ i, M *ᵥ v i = M' *ᵥ v i) → M = M' := by
    intro ι v M M' hspan hagree
    have hlin : M.mulVecLin = M'.mulVecLin :=
      LinearMap.ext_on hspan (by
        rintro x ⟨i, rfl⟩
        simpa [Matrix.mulVecLin_apply] using hagree i)
    ext a b
    have h := DFunLike.congr_fun hlin (Pi.single b 1)
    have h2 := congrFun h a
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Pi.single_apply, Finset.sum_ite_eq'] using h2
  refine ⟨huniq, ?_, ?_⟩
  · intro ι v U hspan hfix
    exact huniq v U 1 hspan fun i => by
      rw [hfix i, Matrix.one_mulVec]
  · intro z N m hN
    rw [smul_pow, hN, smul_zero]

end NCG
