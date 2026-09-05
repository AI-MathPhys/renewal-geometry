/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniversalHankelExhaustion
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Dense Krylov exhaustion of a self-adjoint norm

This module proves the analytic clause of
`thm:universal-Hankel-exhaustion`: Rayleigh radii on a dense union of finite
source/Krylov subspaces exhaust the norm of the selected self-adjoint transfer.
-/

namespace NCG

/-- Rayleigh radius visible on a subspace. -/
noncomputable def subspaceRayleighRadius {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (K : Submodule ℂ E) : ℝ :=
  ⨆ x : K, |T.rayleighQuotient (x : E)|

/-- Every subspace Rayleigh radius is bounded by the ambient operator norm. -/
theorem subspaceRayleighRadius_le_norm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (K : Submodule ℂ E) :
    subspaceRayleighRadius T K ≤ ‖T‖ := by
  apply ciSup_le
  intro x
  exact T.rayleighQuotient_le_norm x

/-- Supremum of the Rayleigh radii over a dense union of subspaces equals the
ambient norm. -/
theorem norm_eq_iSup_subspaceRayleighRadius {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (hT : T.IsSymmetric)
    (K : ι → Submodule ℂ E)
    (hdense : Dense (⋃ i, (K i : Set E))) :
    ‖T‖ = ⨆ i, subspaceRayleighRadius T (K i) := by
  have hι : Nonempty ι := by
    by_contra h
    letI : IsEmpty ι := not_nonempty_iff.mp h
    have hcl := hdense.closure_eq
    simp at hcl
    have hz : (0 : E) ∈ (∅ : Set E) := by
      rw [hcl]
      exact Set.mem_univ _
    simpa using hz
  let i₀ : ι := Classical.choice hι
  let Q : ℝ := ⨆ i, subspaceRayleighRadius T (K i)
  have hbK (i : ι) : BddAbove
      (Set.range fun x : K i => |T.rayleighQuotient (x : E)|) :=
    ⟨‖T‖, fun _ h => by
      obtain ⟨x, rfl⟩ := h
      exact T.rayleighQuotient_le_norm x⟩
  have hbI : BddAbove
      (Set.range fun i => subspaceRayleighRadius T (K i)) :=
    ⟨‖T‖, fun _ h => by
      obtain ⟨i, rfl⟩ := h
      exact subspaceRayleighRadius_le_norm T (K i)⟩
  have hQle : Q ≤ ‖T‖ := by
    dsimp [Q]
    exact ciSup_le fun i => subspaceRayleighRadius_le_norm T (K i)
  have hQnonneg : 0 ≤ Q := by
    have hzero : 0 ≤ subspaceRayleighRadius T (K i₀) := by
      apply le_ciSup_of_le (hbK i₀) (0 : K i₀)
      simp [ContinuousLinearMap.rayleighQuotient]
    exact le_trans hzero (le_ciSup hbI i₀)
  let P : Set E :=
    {x | abs (Complex.re (inner ℂ (T x) x)) ≤ Q * ‖x‖ ^ 2}
  have hPclosed : IsClosed P := by
    apply isClosed_le <;> fun_prop
  have hsub : (⋃ i, (K i : Set E)) ⊆ P := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hxi⟩ := hx
    let y : K i := ⟨x, hxi⟩
    by_cases hzero : x = 0
    · subst x
      simp [P]
    · have hrad : |T.rayleighQuotient x|
          ≤ subspaceRayleighRadius T (K i) := by
        exact le_ciSup
          ⟨‖T‖, fun z hz => by
            obtain ⟨u, rfl⟩ := hz
            exact T.rayleighQuotient_le_norm u⟩ y
      have hiQ : subspaceRayleighRadius T (K i) ≤ Q := by
        exact le_ciSup
          ⟨‖T‖, fun z hz => by
            obtain ⟨j, rfl⟩ := hz
            exact subspaceRayleighRadius_le_norm T (K j)⟩ i
      have hquot : |T.rayleighQuotient x| ≤ Q := hrad.trans hiQ
      change abs (Complex.re (inner ℂ (T x) x)) ≤ Q * ‖x‖ ^ 2
      rw [ContinuousLinearMap.rayleighQuotient, abs_div, abs_sq] at hquot
      exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hzero))).mp hquot
  have hPall : ∀ x : E, x ∈ P := by
    have hclosure := closure_mono hsub
    rw [hdense.closure_eq, hPclosed.closure_eq] at hclosure
    exact fun x => hclosure (Set.mem_univ x)
  have hnormQ : ‖T‖ ≤ Q := by
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro x
    by_cases hzero : x = 0
    · simp [hzero, ContinuousLinearMap.rayleighQuotient, hQnonneg]
    · have hx := hPall x
      change abs (Complex.re (inner ℂ (T x) x)) ≤ Q * ‖x‖ ^ 2 at hx
      rw [ContinuousLinearMap.rayleighQuotient, abs_div, abs_sq]
      exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hzero))).mpr hx
  exact le_antisymm hnormQ hQle

end NCG
