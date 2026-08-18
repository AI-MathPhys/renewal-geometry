/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealOperatorGraphEnergy

/-!
# Graph resolvent equations imply variational minimizers

For a squared operator-graph energy, the weak resolvent equation gives an exact Pythagorean
objective-gap identity.  Positivity of the shift then supplies the minimizer inequality required
by the one-shift Mosco converse.
-/

open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- Weak variational resolvent equation for an operator graph energy. -/
structure OperatorGraphResolventEquation
    (D : Submodule K E) (A : D →ₗ[K] F)
    (lam : ℝ) (f x : E) : Prop where
  mem : x ∈ D
  weakEuler : ∀ z : D,
    RCLike.re (inner K (A ⟨x, mem⟩) (A z)) +
        lam * RCLike.re (inner K x z.1) =
      RCLike.re (inner K z.1 f)

/-- The graph-resolvent objective gap is exactly the sum of the graph and ambient squared
distances. -/
theorem operatorGraph_resolventObjective_sub_eq
    (D : Submodule K E) (A : D →ₗ[K] F)
    (lam : ℝ) (f x : E)
    (h : OperatorGraphResolventEquation D A lam f x)
    (z : E) (hz : z ∈ D) :
    resolventObjective (K := K)
          (fun y ↦ (ennrealOperatorGraphEnergy D A y).toReal) lam f z -
        resolventObjective (K := K)
          (fun y ↦ (ennrealOperatorGraphEnergy D A y).toReal) lam f x =
      ‖A ⟨z, hz⟩ - A ⟨x, h.mem⟩‖ ^ 2 + lam * ‖z - x‖ ^ 2 := by
  let xD : D := ⟨x, h.mem⟩
  let zD : D := ⟨z, hz⟩
  have heuler := h.weakEuler (zD - xD)
  dsimp [xD, zD] at heuler
  simp only [map_sub, inner_sub_right, inner_sub_left, map_sub] at heuler
  rw [← norm_sq_eq_re_inner (𝕜 := K) (A ⟨x, h.mem⟩)] at heuler
  rw [← norm_sq_eq_re_inner (𝕜 := K) x] at heuler
  simp only [resolventObjective]
  rw [ennrealOperatorGraphEnergy_toReal D A z hz,
    ennrealOperatorGraphEnergy_toReal D A x h.mem]
  rw [norm_sub_sq (𝕜 := K), norm_sub_sq (𝕜 := K)]
  rw [inner_re_symm (𝕜 := K) (A ⟨z, hz⟩) (A ⟨x, h.mem⟩),
    inner_re_symm (𝕜 := K) z x]
  nlinarith

/-- A weak graph resolvent at a nonnegative shift minimizes the resolvent objective over the
operator domain. -/
theorem operatorGraph_resolventObjective_minimizer
    (D : Submodule K E) (A : D →ₗ[K] F)
    (lam : ℝ) (hlam : 0 ≤ lam) (f x : E)
    (h : OperatorGraphResolventEquation D A lam f x) :
    ∀ z : E, z ∈ D →
      resolventObjective (K := K)
          (fun y ↦ (ennrealOperatorGraphEnergy D A y).toReal) lam f x ≤
        resolventObjective (K := K)
          (fun y ↦ (ennrealOperatorGraphEnergy D A y).toReal) lam f z := by
  intro z hz
  have hgap := operatorGraph_resolventObjective_sub_eq D A lam f x h z hz
  have hnonneg :
      0 ≤ ‖A ⟨z, hz⟩ - A ⟨x, h.mem⟩‖ ^ 2 + lam * ‖z - x‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg hlam (sq_nonneg _))
  linarith

end NCG.VaryingHilbert
