/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CharacterHankelSectorSaturation
import NCG.Grand.FullMatrixAlgebraModuleDecomposition

/-!
# Schur multiplicity from a character Hankel sector

The range of the character-projected Krylov synthesis is the represented
sector.  When its irreducible block action is the full matrix algebra
`Matrix (Fin d) (Fin d) ℂ`, the explicit matrix-unit decomposition identifies
that range with `d` copies of one diagonal corner.  Thus the manuscript's
Hankel multiplicity formula follows from the action itself; no separate rank
or dimension hypothesis is required.
-/

noncomputable section

open Matrix

namespace NCG
namespace CharacterHankelSchurMultiplicity

open CharacterHankelSectorSaturation

/-- The represented character sector at depth `n`: the actual range of the
projected Krylov synthesis. -/
abbrev ProjectedKrylovCarrier
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n : ℕ) :=
  LinearMap.range (characterControllability P T S n).mulVecLin

/-- The diagonal matrix-unit corner of a represented character sector.  This
is its intrinsic Schur multiplicity space. -/
abbrev CharacterMultiplicityCorner
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n d : ℕ)
    [Module (Matrix (Fin d) (Fin d) ℂ)
      (ProjectedKrylovCarrier P T S n)]
    [SMulCommClass ℂ (Matrix (Fin d) (Fin d) ℂ)
      (ProjectedKrylovCarrier P T S n)]
    (i₀ : Fin d) :=
  FullMatrixAlgebraModuleDecomposition.cornerSubspace
    (M := ProjectedKrylovCarrier P T S n) i₀

/-- Schur's matrix-unit decomposition derives the isotypic dimension formula
for the *actual* projected Krylov range. -/
theorem projectedKrylov_finrank_eq_irrep_mul_multiplicity
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n d : ℕ)
    [Module (Matrix (Fin d) (Fin d) ℂ)
      (ProjectedKrylovCarrier P T S n)]
    [SMulCommClass ℂ (Matrix (Fin d) (Fin d) ℂ)
      (ProjectedKrylovCarrier P T S n)]
    (i₀ : Fin d) :
    Module.finrank ℂ (ProjectedKrylovCarrier P T S n) =
      d * Module.finrank ℂ
        (CharacterMultiplicityCorner P T S n d i₀) := by
  have hdim := LinearEquiv.finrank_eq
    (FullMatrixAlgebraModuleDecomposition.fullMatrixModuleEquiv
      (M := ProjectedKrylovCarrier P T S n) i₀)
  simpa [Module.finrank_pi_fintype] using hdim.symm

/-- The character Hankel rank is `dπ` times the Schur multiplicity obtained
from a diagonal matrix-unit corner.  In particular it is divisible by `dπ`,
and quotienting by the nonzero irreducible dimension recovers multiplicity.
Unlike the earlier interface theorem, this result assumes the represented
full-matrix action, not the desired rank equality. -/
theorem characterHankel_rank_eq_irrep_mul_schurMultiplicity
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n d : ℕ)
    [Module (Matrix (Fin d) (Fin d) ℂ)
      (ProjectedKrylovCarrier P T S n)]
    [SMulCommClass ℂ (Matrix (Fin d) (Fin d) ℂ)
      (ProjectedKrylovCarrier P T S n)]
    (i₀ : Fin d)
    (hPstar : Pᴴ = P) (hPid : P * P = P)
    (hTstar : Tᴴ = T) (hcomm : P * T = T * P) :
    (characterHankel P T S n).rank =
        d * Module.finrank ℂ
          (CharacterMultiplicityCorner P T S n d i₀)
      ∧ d ∣ (characterHankel P T S n).rank
      ∧ (characterHankel P T S n).rank / d =
          Module.finrank ℂ
            (CharacterMultiplicityCorner P T S n d i₀) := by
  let m := Module.finrank ℂ
    (CharacterMultiplicityCorner P T S n d i₀)
  have hcontrollability :
      (characterControllability P T S n).rank = d * m := by
    rw [Matrix.rank_eq_finrank_span_cols, ← Matrix.range_mulVecLin]
    exact projectedKrylov_finrank_eq_irrep_mul_multiplicity P T S n d i₀
  have hrank : (characterHankel P T S n).rank = d * m := by
    rw [characterHankel_rank_eq_projectedKrylov_rank P T S n
      hPstar hPid hTstar hcomm, hcontrollability]
  refine ⟨hrank, hrank ▸ dvd_mul_right d m, ?_⟩
  rw [hrank]
  have hd : 0 < d := Fin.pos_iff_nonempty.mpr ⟨i₀⟩
  simpa [Nat.mul_comm] using Nat.mul_div_left m hd

end CharacterHankelSchurMultiplicity
end NCG
