/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProvenanceHankel

/-!
# Exact EASY 83: finite provenance-panel saturation

This supplies the finite-dimensional stabilization step omitted from the
original provenance Hankel file. A word-length filtration that freezes after
its first plateau and exhausts the carrier is already full by the carrier
dimension. Applying this to the reachable-column and observable-row
filtrations gives rank `d` for every panel with `p,q ≥ d`.
-/

namespace NCG

/-- A finite-dimensional increasing filtration with no growth after its first
plateau, and whose union is the full carrier, saturates by `finrank V`. -/
theorem increasing_filtration_saturates_by_finrank
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (K : ℕ → Submodule ℂ V)
    (hstep : ∀ k, K k ≤ K (k + 1))
    (hfreeze : ∀ k, K k = K (k + 1) →
      ∀ j, k ≤ j → K j = K k)
    (hexhaust : (⨆ k, K k) = ⊤) :
    ∀ q, Module.finrank ℂ V ≤ q → K q = ⊤ := by
  let d := Module.finrank ℂ V
  have hmono : Monotone K := monotone_nat_of_le_succ hstep
  have hKd : K d = ⊤ := by
    by_contra hnot
    have hstrict : ∀ k, k < d → K k < K (k + 1) := by
      intro k hk
      refine lt_of_le_of_ne (hstep k) ?_
      intro heq
      have hconst := hfreeze k heq
      have hkTop : K k = ⊤ := by
        apply top_unique
        rw [← hexhaust]
        apply iSup_le
        intro j
        by_cases hj : k ≤ j
        · rw [hconst j hj]
        · exact hmono (Nat.le_of_lt (lt_of_not_ge hj))
      have hle : K k ≤ K d := hmono (Nat.le_of_lt hk)
      rw [hkTop] at hle
      exact hnot (top_unique hle)
    have hrank : ∀ k, k ≤ d →
        k ≤ Module.finrank ℂ (K k) := by
      intro k hk
      induction k with
      | zero => exact Nat.zero_le _
      | succ k ih =>
          have hklt : k < d := by omega
          have hlt := Submodule.finrank_lt_finrank_of_lt (hstrict k hklt)
          exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih (by omega)) hlt)
    have heq : Module.finrank ℂ (K d) = Module.finrank ℂ V :=
      le_antisymm (Submodule.finrank_le _) (hrank d le_rfl)
    exact hnot (Submodule.eq_top_of_finrank_eq heq)
  intro q hq
  apply top_unique
  rw [← hKd]
  exact hmono hq

/-- A surjective column synthesis followed by an injective row analysis has
rank equal to the middle carrier dimension. -/
theorem full_panel_rank {U V W : Type*}
    [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (C : U →ₗ[ℂ] V) (O : V →ₗ[ℂ] W)
    (hC : Function.Surjective C) (hO : Function.Injective O) :
    Module.finrank ℂ (LinearMap.range (O.comp C)) =
      Module.finrank ℂ V := by
  have hrange : LinearMap.range (O.comp C) = LinearMap.range O := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨C x, rfl⟩
    · rintro y ⟨v, rfl⟩
      obtain ⟨x, rfl⟩ := hC v
      exact ⟨x, rfl⟩
  rw [hrange, LinearMap.finrank_range_of_inj hO]

/-- Abstract finite-panel form of provenance-Hankel saturation. The hypotheses
are exactly the reachable-column and observable-row factorizations used in
the manuscript proof. -/
theorem provenance_finite_panel_saturation
    {U V W : Type*}
    [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (K Ospan : ℕ → Submodule ℂ V)
    (C : ℕ → U →ₗ[ℂ] V) (O : ℕ → V →ₗ[ℂ] W)
    (hKstep : ∀ k, K k ≤ K (k + 1))
    (hKfreeze : ∀ k, K k = K (k + 1) →
      ∀ j, k ≤ j → K j = K k)
    (hKexhaust : (⨆ k, K k) = ⊤)
    (hOstep : ∀ k, Ospan k ≤ Ospan (k + 1))
    (hOfreeze : ∀ k, Ospan k = Ospan (k + 1) →
      ∀ j, k ≤ j → Ospan j = Ospan k)
    (hOexhaust : (⨆ k, Ospan k) = ⊤)
    (hCrange : ∀ q, LinearMap.range (C q) = K q)
    (hOinjective : ∀ p, Ospan p = ⊤ → Function.Injective (O p)) :
    ∀ p q, Module.finrank ℂ V ≤ p →
      Module.finrank ℂ V ≤ q →
      Module.finrank ℂ (LinearMap.range ((O p).comp (C q))) =
        Module.finrank ℂ V := by
  intro p q hp hq
  have hKq := increasing_filtration_saturates_by_finrank
    K hKstep hKfreeze hKexhaust q hq
  have hOp := increasing_filtration_saturates_by_finrank
    Ospan hOstep hOfreeze hOexhaust p hp
  apply full_panel_rank (C q) (O p)
  · rw [← LinearMap.range_eq_top, hCrange q, hKq]
  · exact hOinjective p hOp

end NCG
