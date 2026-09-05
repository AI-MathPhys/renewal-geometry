/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SchurJetsExact
import NCG.Grand.LeadingRayExact

/-!
# Constant localizer, nested Schur jets, and the complete leading ray

This module assembles the exact clauses RG.3f--RG.3i of
`thm:SM-localizer-jets`.  In particular, the first Schur jet is used as its
literal continuous `mulVec` action in the marginal recurrence, so the jet and
leading-ray statements share one typed operator rather than separate
interfaces.
-/

open Matrix Filter
open scoped Topology

namespace NCG
namespace ConstantLocalizerSchurJetsLeadingRay

open SchurBlock SchurJets LeadingRay

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The first Schur jet acting on the retained carrier. -/
noncomputable def firstJetAction (K : M m n) :
    (m ⊕ n → ℝ) →L[ℝ] (m ⊕ n → ℝ) :=
  LinearMap.toContinuousLinearMap K.mulVecLin

@[simp]
theorem firstJetAction_apply (K : M m n) (x : m ⊕ n → ℝ) :
    firstJetAction K x = K *ᵥ x := rfl

/-- Exact assembly of RG.3f--RG.3i.  `hphysical` is the manuscript's
positive physical-width block presentation, `hL`/`hL'` are its displayed
two-sided differentiability hypotheses, and `hrec` is the displayed reduced
marginal recurrence. -/
theorem constantLocalizer_nestedSchurJets_completeLeadingRay
    (L L' : ℝ → M m n) (L₂ : M m n)
    (hL : ∀ s, HasDerivAt L (L' s) s)
    (hL' : HasDerivAt L' L₂ 0)
    (hu : ∀ s, IsUnit (P + Q * L s * Q))
    (hP0 : P * L 0 = 0) (h0P : L 0 * P = 0)
    (hphysical : ∀ s, 0 < s →
      ∃ (A : Matrix m m ℝ) (B : Matrix m n ℝ)
        (D : Matrix n n ℝ),
        L s = fromBlocks A B Bᴴ D ∧
          (fromBlocks A B Bᴴ D).PosSemidef ∧ D.PosDef)
    (𝒬 : (m ⊕ n → ℝ) →L[ℝ]
      (m ⊕ n → ℝ) →L[ℝ] (m ⊕ n → ℝ))
    (z : ℝ → (m ⊕ n → ℝ)) (γ : ℝ → ℝ)
    (r z₂ b : m ⊕ n → ℝ) (β : ℝ)
    (hz : (fun s => z s - s • r - s ^ 2 • z₂)
      =o[𝓝 0] fun s : ℝ => s ^ 2)
    (hγ : (fun s => γ s - s - β * s ^ 2)
      =o[𝓝 0] fun s : ℝ => s ^ 2)
    (hrec : (fun s => z (γ s) -
      (z s + s ^ 2 • b + 𝒬 (z s) (z s) -
        s • firstJetAction (P * L' 0 * P) (z s)))
      =o[𝓝 0] fun s : ℝ => s ^ 2) :
    -- RG.3f: exact induced localizer is positive on the physical branch
    (∀ s, 0 < s → (schur (L s)).PosSemidef)
    -- RG.3g: exact first jet and its one-sided positivity
    ∧ HasDerivAt (fun s => schur (L s)) (P * L' 0 * P) 0
    ∧ (∀ x : m ⊕ n → ℝ,
        0 ≤ x ⬝ᵥ ((P * L' 0 * P) *ᵥ x))
    -- RG.3h: exact relaxed second jet, positive on the first-jet kernel
    ∧ HasDerivAt (schurDeriv L L') (secondJet L L' L₂) 0
    ∧ (∀ x : m ⊕ n → ℝ,
        (P * L' 0 * P) *ᵥ x = 0 →
          0 ≤ x ⬝ᵥ (secondJet L L' L₂ *ᵥ x))
    -- RG.3i: complete leading-ray equation with the same first-jet action
    ∧ b + 𝒬 r r - firstJetAction (P * L' 0 * P) r - β • r = 0 := by
  have hpos : ∀ s, 0 < s → (schur (L s)).PosSemidef := by
    intro s hs
    obtain ⟨A, B, D, hLs, hLspos, hD⟩ := hphysical s hs
    rw [hLs]
    exact schur_posSemidef A B D hLspos hD
  refine ⟨hpos,
    hasDerivAt_schur_zero L L' (hL 0) (hu 0) hP0 h0P,
    ?_,
    hasDerivAt_schurDeriv_zero L L' L₂ hL hL' (hu 0) hP0 h0P,
    ?_,
    ?_⟩
  · intro x
    exact quadForm_jet1_nonneg L L' (hL 0) (hu 0) hP0 h0P hpos x
  · intro x hx
    exact quadForm_jet2_nonneg L L' L₂ hL hL' hu hP0 h0P hpos x hx
  · exact leading_ray_eq 𝒬 (firstJetAction (P * L' 0 * P)) z γ
      r z₂ b β hz hγ hrec

end ConstantLocalizerSchurJetsLeadingRay
end NCG
