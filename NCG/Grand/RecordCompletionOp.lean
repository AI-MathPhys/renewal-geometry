/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectatorProduct

/-!
# Operational-record completion theorem
  (`thm:operational-record-completion`, Gran-Tensor manuscript)

* `operational_record_completion`:
  (O1) the completed branch normalization identity:
       `Σ_j (W⊗K_j)ᴴ(W⊗K_j) = (WᴴW) ⊗ (Σ_j K_jᴴK_j)`, so with
       a partial-isometry writer (`WᴴW = P`) and a normalized
       instrument (`ΣK_jᴴK_j = 1`) the completed instrument
       sums to `P ⊗ I ⪯ I` (the manuscript's boxed display);
  (O2) record discard recovers the original branch: the
       partial trace over the record leg of
       `(WρW ᴴ) ⊗ (KσKᴴ)` is `Tr(WρWᴴ)·KσKᴴ`;
  (O3) composition law: completed branches compose as
       `(W₂⊗K₂)(W₁⊗K₁) = (W₂W₁)⊗(K₂K₁)`;
  (O6) point Reads separate: if the read signature separates
       ledger values then every signature class is a singleton.

Rendering disclosed: (O4)/(O5) — unread-refinement invariance
and cutoff functoriality — are the proved `minimal_record` and
`record_refinement_bundle` records applied to the completed
ledger (the manuscript cites exactly those theorems); the
CP property of each completed branch is conjugation positivity
(proved in the generator records).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace NCG

/-- `thm:operational-record-completion`. -/
theorem operational_record_completion
    {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r]
    [DecidableEq c] :
    -- (O1) completed-branch normalization
    (∀ {ι : Type} [Fintype ι] (W : Matrix r r ℂ)
      (K : ι → Matrix c c ℂ),
      ∑ j, (W ⊗ₖ K j)ᴴ * (W ⊗ₖ K j)
        = (Wᴴ * W) ⊗ₖ (∑ j, (K j)ᴴ * K j))
    ∧ (∀ P : Matrix r r ℂ, Pᴴ = P → P * P = P →
        ((1 : Matrix (r × c) (r × c) ℂ)
          - P ⊗ₖ (1 : Matrix c c ℂ)).PosSemidef)
    -- (O2) record discard recovers the branch
    ∧ (∀ (A : Matrix c c ℂ) (B : Matrix r r ℂ),
        partialTraceRight (dA := c) (dK := r) (A ⊗ₖ B)
          = B.trace • A)
    -- (O3) sequential composition of completed branches
    ∧ (∀ (W₁ W₂ : Matrix r r ℂ) (K₁ K₂ : Matrix c c ℂ),
        (W₂ ⊗ₖ K₂) * (W₁ ⊗ₖ K₁) = (W₂ * W₁) ⊗ₖ (K₂ * K₁))
    -- (O6) separating point Reads make classes singletons
    ∧ (∀ {α β : Type} (sig : α → β),
        Function.Injective sig →
        ∀ a b : α, sig a = sig b → a = b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ι _ W K
    have hterm : ∀ j : ι, (W ⊗ₖ K j)ᴴ * (W ⊗ₖ K j)
        = (Wᴴ * W) ⊗ₖ ((K j)ᴴ * K j) := by
      intro j
      rw [Matrix.conjTranspose_kronecker,
        ← Matrix.mul_kronecker_mul]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    ext pq rs
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
      Finset.mul_sum]
  · intro P hPH hP2
    have hQH : ((1 : Matrix r r ℂ) - P)ᴴ
        = (1 : Matrix r r ℂ) - P := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        hPH]
    have hQ2 : ((1 : Matrix r r ℂ) - P)
        * ((1 : Matrix r r ℂ) - P)
        = (1 : Matrix r r ℂ) - P := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
        Matrix.one_mul, hP2, sub_self, sub_zero]
    have hk : (1 : Matrix (r × c) (r × c) ℂ)
        - P ⊗ₖ (1 : Matrix c c ℂ)
        = ((1 : Matrix r r ℂ) - P) ⊗ₖ (1 : Matrix c c ℂ) := by
      ext p q
      simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.sub_apply, Prod.ext_iff]
      by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
        simp [h1, h2]
    rw [hk, show ((1 : Matrix r r ℂ) - P)
          ⊗ₖ (1 : Matrix c c ℂ)
        = (((1 : Matrix r r ℂ) - P) ⊗ₖ (1 : Matrix c c ℂ))ᴴ
          * (((1 : Matrix r r ℂ) - P)
            ⊗ₖ (1 : Matrix c c ℂ)) from by
      rw [Matrix.conjTranspose_kronecker, hQH,
        Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
        hQ2, Matrix.one_mul]]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · intro A B
    ext i j
    simp only [partialTraceRight, Matrix.of_apply,
      Matrix.kroneckerMap_apply, Matrix.smul_apply,
      Matrix.trace, Matrix.diag_apply, smul_eq_mul]
    rw [← Finset.mul_sum, mul_comm]
  · intro W₁ W₂ K₁ K₂
    rw [Matrix.mul_kronecker_mul]
  · intro α β sig hinj a b hab
    exact hinj hab

end NCG
