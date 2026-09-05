/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite common-action exactness and protected coordinate
  integration
  (`thm:common-action-exactness` and
  `thm:protected-coordinate-integration`,
  Gran-Tensor manuscript)

* `common_action_exactness`:
  (i) the boxed exactness criterion `α = d₀𝒮 ⟺ d₁α = 0`:
      a protected increment admits a scalar common action
      exactly when every face/cycle sum closes;
  (ii) path-integration reconstruction from a fixed anchor;
  (iii) uniqueness of `𝒮` after fixing one action anchor;
  (iv) the boxed quantitative Hodge obstruction
      `dist(α, Ran d₀)² ≤ ‖P_har α‖² + σ_coex⁻²‖d₁α‖²`
      (abstract orthogonal form).

* `protected_coordinate_integration`: the boxed vector
  version `ϑ(e) = X(t(e)) - X(s(e))` — a protected
  directional-increment cochain integrates to a coordinate
  writer, uniquely after fixing one endpoint value,
  precisely under the same closure condition, componentwise
  in `ℤ³`.

The identification of the closure hypothesis with vanishing
of the `2`-cell curls and of all periods on an integral
`H₁` basis (equivalently, path independence on a finite
connected complex) is the manuscript's cellular
bookkeeping.
-/

open scoped InnerProductSpace

namespace NCG

/-- `thm:common-action-exactness`. -/
theorem common_action_exactness {ι : Type*} [Nonempty ι]
    (α : ι → ι → ℝ) :
    -- (i) the boxed exactness criterion
    ((∃ S : ι → ℝ, ∀ i j, α i j = S j - S i)
      ↔ (∀ i j k, α i j + α j k = α i k))
    -- (ii) path-integration reconstruction
    ∧ ((∀ i j k, α i j + α j k = α i k) →
        ∀ o i j, α i j = α o j - α o i)
    -- (iii) uniqueness after one anchor
    ∧ (∀ (S T : ι → ℝ) (o : ι),
        (∀ i j, α i j = S j - S i) →
        (∀ i j, α i j = T j - T i) → S o = T o → S = T)
    -- (iv) the boxed quantitative Hodge obstruction
    ∧ (∀ {V : Type} [NormedAddCommGroup V]
        [InnerProductSpace ℝ V] (har coex : V) (σ d : ℝ),
        0 < σ → ⟪har, coex⟫_ℝ = 0 → ‖coex‖ ≤ σ⁻¹ * d →
        ‖har + coex‖ ^ 2 ≤ ‖har‖ ^ 2 + (σ⁻¹ * d) ^ 2) := by
  have hpath : (∀ i j k, α i j + α j k = α i k) →
      ∀ o i j, α i j = α o j - α o i := by
    intro hc o i j
    have h := hc o i j
    linarith
  refine ⟨?_, hpath, ?_, ?_⟩
  · constructor
    · rintro ⟨S, hS⟩ i j k
      rw [hS, hS, hS]
      ring
    · intro hc
      obtain ⟨o⟩ := ‹Nonempty ι›
      exact ⟨fun q => α o q, fun i j => hpath hc o i j⟩
  · intro S T o hS hT hanchor
    funext j
    have h1 := hS o j
    have h2 := hT o j
    rw [h1] at h2
    linarith
  · intro V _ _ har coex σ d hσ horth hbound
    rw [norm_add_sq_real, horth]
    have h1 : ‖coex‖ ^ 2 ≤ (σ⁻¹ * d) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖coex‖ := norm_nonneg _
      nlinarith [hbound, h0]
    linarith

/-- `thm:protected-coordinate-integration`. -/
theorem protected_coordinate_integration {ι : Type*}
    [Nonempty ι] (ϑ : ι → ι → Fin 3 → ℤ) :
    -- the boxed componentwise integration criterion
    ((∃ X : ι → Fin 3 → ℤ, ∀ i j, ϑ i j = X j - X i)
      ↔ (∀ i j k, ϑ i j + ϑ j k = ϑ i k))
    -- uniqueness after fixing one endpoint value
    ∧ (∀ (X Y : ι → Fin 3 → ℤ) (o : ι),
        (∀ i j, ϑ i j = X j - X i) →
        (∀ i j, ϑ i j = Y j - Y i) → X o = Y o → X = Y) := by
  constructor
  · constructor
    · rintro ⟨X, hX⟩ i j k
      rw [hX, hX, hX]
      abel
    · intro hc
      obtain ⟨o⟩ := ‹Nonempty ι›
      refine ⟨fun q => ϑ o q, fun i j => ?_⟩
      have h := hc o i j
      funext a
      have ha := congrFun h a
      simp only [Pi.add_apply, Pi.sub_apply] at ha ⊢
      omega
  · intro X Y o hX hY hanchor
    funext j a
    have h1 := congrFun (hX o j) a
    have h2 := congrFun (hY o j) a
    have h3 := congrFun hanchor a
    simp only [Pi.sub_apply] at h1 h2
    omega

end NCG
