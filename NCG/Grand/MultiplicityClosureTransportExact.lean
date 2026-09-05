/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Multiplicity closure: generation-source transport under cutoff embeddings

Record-local machinery for `thm:SMST-coercive-multiplicity-closure` (whose
nine proof anchors are all proved records): the remaining clause — "the
generation-source lower bound preserves its rank and positive variance under
the cutoff embeddings" — is formalized exactly.

* `isometric_gram_invariant`: an isometric cutoff embedding preserves the
  generation-source Gram exactly;
* `isometric_rank_invariant`: hence the rank-three generation source cannot
  collapse under the embeddings;
* `gram_lower_bound_invariant`: and every uniform positive lower bound on the
  Gram transports verbatim.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace MultiplicityClosure

variable {m n q : Type*} [Fintype m] [Fintype n] [Fintype q] [DecidableEq n]

omit [Fintype q] in
/-- An isometric cutoff embedding preserves the generation-source Gram. -/
theorem isometric_gram_invariant (I : Matrix m n ℂ) (S : Matrix n q ℂ)
    (hI : Iᴴ * I = 1) : (I * S)ᴴ * (I * S) = Sᴴ * S := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Iᴴ I S,
    hI, Matrix.one_mul]

/-- **Rank preservation**: the rank-three generation source cannot collapse
under isometric cutoff embeddings. -/
theorem isometric_rank_invariant (I : Matrix m n ℂ)
    (S : Matrix n q ℂ) (hI : Iᴴ * I = 1) : (I * S).rank = S.rank := by
  refine le_antisymm (Matrix.rank_mul_le_right I S) ?_
  have hS : Iᴴ * (I * S) = S := by
    rw [← Matrix.mul_assoc, hI, Matrix.one_mul]
  calc S.rank = (Iᴴ * (I * S)).rank := by rw [hS]
    _ ≤ (I * S).rank := Matrix.rank_mul_le_right Iᴴ (I * S)

omit [Fintype q] in
/-- **Positive-variance preservation**: every uniform lower bound on the
generation-source Gram transports verbatim through the embeddings. -/
theorem gram_lower_bound_invariant [DecidableEq q] (I : Matrix m n ℂ)
    (S : Matrix n q ℂ) (hI : Iᴴ * I = 1) (c : ℂ)
    (hlow : (Sᴴ * S - c • 1).PosSemidef) :
    ((I * S)ᴴ * (I * S) - c • 1).PosSemidef := by
  rw [isometric_gram_invariant I S hI]
  exact hlow

end MultiplicityClosure
end NCG
