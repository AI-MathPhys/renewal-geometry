/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Rank and kernel of a block operator vanishing on a translation subspace
  (the "Hence" part of `thm:supp-certified-weak-rank`: `eq:supp-certified-Kblock`,
  `eq:supp-certified-kernel`; emergent-spacetime manuscript)

Let `V = 𝒢 ⊕ ℋ` (complementary subspaces) and let `K : V → V` have the block form
`K = diag(0_ℋ, K_g)`, i.e. `K` kills `ℋ` and takes values in `𝒢`
(`eq:supp-certified-Kblock`, translation invariance of the weak first-Poisson block).  Then
`rank K = rank K_g` and `ker K = ker K_g ⊕ ℋ` (`translationBlock_rank`,
`translationBlock_ker`, `translationBlock_finrank_ker`).

`translationBlock_weak_rank`: in the paper's dimensions (`dim 𝒢 = 26`, `dim ℋ = 3`), the
certified value `rank K_g = 24` gives `rank K_WW = 24`, `dim 𝒵_g = dim ker K_g = 2` and
`ker K_WW = 𝒵_g ⊕ ℋ` of dimension `5` (`eq:supp-certified-rank24`, `eq:supp-certified-kernel`).
The value `rank K_g = 24` itself is the numerical certificate of the paper and is a hypothesis
here.
-/

open Module

namespace RenewalGeometry
namespace TranslationBlock

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (G Hs : Submodule ℝ V) (K : V →ₗ[ℝ] V)

/-- The `𝒢 𝒢` block `K_g = K|_𝒢 : 𝒢 → V` (values in `𝒢`). -/
def gBlock : G →ₗ[ℝ] V := K.domRestrict G

variable {G Hs K}

omit [FiniteDimensional ℝ V] in
/-- `ker K = ker K_g ⊕ ℋ` for `K = diag(0, K_g)`. -/
theorem translationBlock_ker (hc : IsCompl G Hs) (hKH : ∀ h ∈ Hs, K h = 0) :
    LinearMap.ker K = (LinearMap.ker (gBlock G K)).map G.subtype ⊔ Hs := by
  apply le_antisymm
  · intro v hv
    obtain ⟨g, hg, h, hh, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top :
      v ∈ G ⊔ Hs)
    have hKg : K g = 0 := by
      have : K (g + h) = 0 := hv
      rwa [map_add, hKH h hh, add_zero] at this
    exact Submodule.add_mem_sup ⟨⟨g, hg⟩, hKg, rfl⟩ hh
  · rw [sup_le_iff]
    constructor
    · rintro _ ⟨g, hg, rfl⟩
      exact hg
    · intro h hh
      exact hKH h hh

omit [FiniteDimensional ℝ V] in
/-- `rank K = rank K_g`. -/
theorem translationBlock_rank (hc : IsCompl G Hs) (hKH : ∀ h ∈ Hs, K h = 0) :
    LinearMap.range K = LinearMap.range (gBlock G K) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    obtain ⟨g, hg, h, hh, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top :
      v ∈ G ⊔ Hs)
    exact ⟨⟨g, hg⟩, by simp [gBlock, hKH h hh]⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩

/-- `dim ker K = dim ker K_g + dim ℋ = (dim 𝒢 - rank K_g) + dim ℋ`. -/
theorem translationBlock_finrank_ker (hc : IsCompl G Hs) (hKH : ∀ h ∈ Hs, K h = 0) :
    finrank ℝ (LinearMap.ker K) + finrank ℝ (LinearMap.range (gBlock G K))
      = finrank ℝ G + finrank ℝ Hs := by
  have h1 := K.finrank_range_add_finrank_ker
  have h2 := (gBlock G K).finrank_range_add_finrank_ker
  have h3 := Submodule.finrank_add_eq_of_isCompl hc
  rw [translationBlock_rank hc hKH] at h1
  omega

omit [FiniteDimensional ℝ V] in
/-- The `ker K_g` summand `𝒵_g` meets `ℋ` trivially, so `ker K = 𝒵_g ⊕ ℋ` is direct. -/
theorem translationBlock_disjoint (hc : IsCompl G Hs) :
    Disjoint ((LinearMap.ker (gBlock G K)).map G.subtype) Hs := by
  refine Disjoint.mono_left ?_ hc.disjoint
  rintro _ ⟨g, -, rfl⟩
  exact g.2

/-- **The "Hence" of `thm:supp-certified-weak-rank`.** With `dim 𝒢 = 26`, `dim ℋ = 3` and the
certified `rank K_g = 24`: `rank K_WW = 24`, `dim 𝒵_g = 2` (`𝒵_g = ker K_g`),
`ker K_WW = 𝒵_g ⊕ ℋ` (direct) of dimension `5`. -/
theorem translationBlock_weak_rank (hc : IsCompl G Hs) (hKH : ∀ h ∈ Hs, K h = 0)
    (hG : finrank ℝ G = 26) (hH : finrank ℝ Hs = 3)
    (hrank : finrank ℝ (LinearMap.range (gBlock G K)) = 24) :
    finrank ℝ (LinearMap.range K) = 24 ∧
      finrank ℝ (LinearMap.ker (gBlock G K)) = 2 ∧
      LinearMap.ker K = (LinearMap.ker (gBlock G K)).map G.subtype ⊔ Hs ∧
      Disjoint ((LinearMap.ker (gBlock G K)).map G.subtype) Hs ∧
      finrank ℝ (LinearMap.ker K) = 5 := by
  have h2 := (gBlock G K).finrank_range_add_finrank_ker
  have h4 := translationBlock_finrank_ker hc hKH
  refine ⟨by rw [translationBlock_rank hc hKH, hrank], by omega,
    translationBlock_ker hc hKH, translationBlock_disjoint hc, by omega⟩

end TranslationBlock
end RenewalGeometry
