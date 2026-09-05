/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.CylinderDescentPolarExact
import NCG.Grand.ProvenanceInnovationRank

/-!
# Cylinder descent: predictor rank gain and finite stabilization

Second machinery layer for `thm:global-cylinder-descent` (G3)–(G5):

* `rowProj` — the canonical row-space projector `P_H = Q_{H^*H}` of a
  predictor block, with its algebraic characterization (`rowProj_hermitian`,
  `rowProj_idem`, `mul_rowProj`, `rowProj_rank`) — the hypotheses of the
  proved stacked-rank machinery, discharged by spectral calculus;
* `hankel_rank_gain` (G4): the boxed identity
  `rank H_{n∣m} − rank H_m = rank 𝕀^pred` for the stacked refined predictor,
  with `𝕀^pred = S(1 − P_H)S^*` the innovation Gram of the later rows on the
  old kernel — and `hankel_innovation_posSemidef`;
* `submodule_chain_stabilizes` (G5): every monotone chain of subspaces of a
  finite-dimensional space stabilizes at a finite index — the tail ideal is
  already determined at some finite later cutoff;
* `descending_relation_stabilizes` (G3): a descending chain of relations on a
  finite record ledger stabilizes after finitely many refinements;
* `pullback_annihilator` (G5): `α_{n/m}^{-1}(𝒩_n) = ker(C_n α_{n/m})` — the
  contextual ideal pulls back to the annihilator of the transported row span.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace CylinderDescentRank

open NCG.SourceCoercivityInfluence NCG.CylinderDescent

/-! ### The canonical row-space projector -/

variable {a s n : ℕ}

/-- The canonical projector onto the row support of `H`: the support
projection of the Gram `H^* H`. -/
noncomputable def rowProj (H : Matrix (Fin a) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  supportProj (posSemidef_conjTranspose_mul_self H).1

theorem rowProj_hermitian (H : Matrix (Fin a) (Fin n) ℂ) :
    (rowProj H)ᴴ = rowProj H :=
  (supportProj_posSemidef (posSemidef_conjTranspose_mul_self H).1).1

theorem rowProj_idem (H : Matrix (Fin a) (Fin n) ℂ) :
    rowProj H * rowProj H = rowProj H :=
  supportProj_idem (posSemidef_conjTranspose_mul_self H).1

/-- `H` is fixed by its row projector. -/
theorem mul_rowProj (H : Matrix (Fin a) (Fin n) ℂ) : H * rowProj H = H :=
  mul_supportProj_of_gram H (posSemidef_conjTranspose_mul_self H) rfl

/-- The row projector has the rank of `H`. -/
theorem rowProj_rank (H : Matrix (Fin a) (Fin n) ℂ) :
    (rowProj H).rank = H.rank := by
  refine le_antisymm ?_ ?_
  · calc (rowProj H).rank
        = (pinv (posSemidef_conjTranspose_mul_self H).1 * (Hᴴ * H)).rank := by
          rw [rowProj, supportProj_eq_pinv_mul]
      _ ≤ (Hᴴ * H).rank := Matrix.rank_mul_le_right _ _
      _ = H.rank := Matrix.rank_conjTranspose_mul_self H
  · calc H.rank = (H * rowProj H).rank := by rw [mul_rowProj]
      _ ≤ (rowProj H).rank := Matrix.rank_mul_le_right _ _

/-! ### (G4): the predictor rank gain -/

/-- **(G4), the boxed rank identity**: for the stacked refined predictor
`H_{n∣m} = [H_m; S]`, the rank gain over the old predictor is the rank of the
innovation Gram of the later rows on the old kernel:
`rank H_{n∣m} − rank H_m = rank (S (1 − P_H) S^*)`. -/
theorem hankel_rank_gain (H : Matrix (Fin a) (Fin n) ℂ)
    (S : Matrix (Fin s) (Fin n) ℂ) :
    (Matrix.fromRows H S).rank - H.rank
      = (S * (1 - rowProj H) * Sᴴ).rank := by
  obtain ⟨_, _, _, h4⟩ := NCG.provenance_innovation_decomposition_exact H S
    (rowProj H) 1 (rowProj_hermitian H) Matrix.conjTranspose_one
    (rowProj_idem H) (Matrix.one_mul 1) (Matrix.one_mul _) (mul_rowProj H)
    (rowProj_rank H)
  exact h4

/-- **(G4)**: the predictor innovation Gram is positive semidefinite. -/
theorem hankel_innovation_posSemidef (H : Matrix (Fin a) (Fin n) ℂ)
    (S : Matrix (Fin s) (Fin n) ℂ) :
    (S * (1 - rowProj H) * Sᴴ).PosSemidef := by
  obtain ⟨_, h2, _, _⟩ := NCG.provenance_innovation_decomposition_exact H S
    (rowProj H) 1 (rowProj_hermitian H) Matrix.conjTranspose_one
    (rowProj_idem H) (Matrix.one_mul 1) (Matrix.one_mul _) (mul_rowProj H)
    (rowProj_rank H)
  simpa using h2

/-! ### (G3), (G5): finite stabilization -/

/-- **(G5), finite determination of the tail ideal**: every monotone chain of
subspaces of a finite-dimensional coefficient space stabilizes at a finite
index. -/
theorem submodule_chain_stabilizes {d : ℕ}
    (f : ℕ →o Submodule ℂ (Fin d → ℂ)) : ∃ N, ∀ m, N ≤ m → f N = f m :=
  monotone_stabilizes_iff_noetherian.mpr inferInstance f

/-- **(G3), finite stabilization of the record refinements**: a descending
chain of relations on a finite record ledger stabilizes after finitely many
refinements. -/
theorem descending_relation_stabilizes {α : Type*} [Finite α]
    (f : ℕ → Set (α × α)) (hf : ∀ k, f (k + 1) ⊆ f k) :
    ∃ N, ∀ m, N ≤ m → f m = f N := by
  classical
  have hchain : ∀ {k m : ℕ}, k ≤ m → f m ⊆ f k := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => exact subset_rfl
    | succ m _ ih => exact (hf m).trans ih
  obtain ⟨N, hN⟩ := Nat.sInf_mem (Set.range_nonempty fun k => (f k).ncard)
  refine ⟨N, fun m hm => ?_⟩
  have hle : (f N).ncard ≤ (f m).ncard := by
    have hN' : (f N).ncard = sInf (Set.range fun k => (f k).ncard) := hN
    rw [hN']
    exact Nat.sInf_le ⟨m, rfl⟩
  exact Set.eq_of_subset_of_ncard_le (hchain hm) hle (Set.toFinite _)

/-! ### (G5): the contextual annihilator pulls back -/

/-- **(G5), the annihilator identity**: the preimage of the contextual ideal
`𝒩_n = ker C_n` under the connecting map `α_{n/m}` is the annihilator of the
transported row span, `ker (C_n α_{n/m})`. -/
theorem pullback_annihilator {c dn dm : ℕ} (C : Matrix (Fin c) (Fin dn) ℂ)
    (α : Matrix (Fin dn) (Fin dm) ℂ) :
    {x : Fin dm → ℂ | (C * α) *ᵥ x = 0}
      = (fun x => α *ᵥ x) ⁻¹' {y : Fin dn → ℂ | C *ᵥ y = 0} := by
  ext x
  simp [Matrix.mulVec_mulVec]

end CylinderDescentRank
end NCG
