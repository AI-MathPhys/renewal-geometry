/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTAtlasCompleteness
import NCG.Grand.ThreeCylinderActionResponseExact
import NCG.Grand.BrandNewEasy02

/-!
# Source-minimal atlas missing bank

This proves the missing formula (SA.6) in `thm:GT-atlas-completeness` using
the maintained spectral Moore--Penrose inverse square root.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace AtlasMissingBank

open ThreeCylinderActionResponse SourceCoercivityInfluence

/-- The atlas completeness kernel `C = U*(1-P)U`. -/
def completenessKernel {n e : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin e) ℂ) :
    Matrix (Fin e) (Fin e) ℂ :=
  Uᴴ * (1 - P) * U

/-- The source synthesis of the directions missed by `P`. -/
def missingSynthesis {n e : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin e) ℂ) :
    Matrix (Fin n) (Fin e) ℂ :=
  (1 - P) * U

/-- The canonical source-minimal missing bank (SA.6). -/
noncomputable def missingBank {n e : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin e) ℂ) :
    Matrix (Fin n) (Fin e) ℂ :=
  isoSynthesis (missingSynthesis P U)

/-- Exact SA.6 package: the completeness kernel is the Gram of the missing
synthesis; the normalized bank is an isometry on its support, reconstructs
the full missing synthesis after multiplication by the positive square root,
has exactly the missing rank, and every other synthesis of the same kernel
has that rank. -/
theorem atlas_missing_bank_exact {n e : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ)
    (hPH : Pᴴ = P) (hP2 : P * P = P)
    (U : Matrix (Fin n) (Fin e) ℂ) :
    let A := missingSynthesis P U
    let C := completenessKernel P U
    let J := missingBank P U
    C = Aᴴ * A
      ∧ Jᴴ * J = supportProj (gramPsd A).1
      ∧ J * sqrtM (gramPsd A).1 = A
      ∧ J.rank = A.rank
      ∧ (∀ {p : ℕ} (B : Matrix (Fin p) (Fin e) ℂ),
          Bᴴ * B = C → B.rank = A.rank) := by
  dsimp only
  let A := missingSynthesis P U
  let C := completenessKernel P U
  let J := missingBank P U
  have hCA : C = Aᴴ * A := by
    unfold C A completenessKernel missingSynthesis
    exact (orthComplement_gram_synthesis P hPH hP2 U).symm
  have hgram : Jᴴ * J = supportProj (gramPsd A).1 := by
    unfold J missingBank
    exact isoSynthesis_gram A
  have hreconstruct : J * sqrtM (gramPsd A).1 = A := by
    unfold J missingBank isoSynthesis whitener
    rw [Matrix.mul_assoc, invSqrt_mul_sqrtM,
      mul_supportProj_self A]
  have hrank : J.rank = A.rank := by
    apply le_antisymm
    · unfold J missingBank isoSynthesis
      exact Matrix.rank_mul_le_left _ _
    · rw [← hreconstruct]
      exact Matrix.rank_mul_le_left _ _
  refine ⟨hCA, hgram, hreconstruct, hrank, ?_⟩
  intro p B hB
  exact gram_synthesis_rank_eq B A (hB.trans hCA)

end AtlasMissingBank
end NCG
