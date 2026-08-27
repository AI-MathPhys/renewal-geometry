/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineRadicalReflectionExact
import NCG.Grand.AffineEulerExpansionExact

/-!
# Exact radical reflection pencil

Sharp positivity and the exhaustive kernel description for the AFF.6 pencil.
-/

open Matrix Finset

namespace NCG
namespace AffineRadicalReflectionKernelExact

open AffineRadical

variable {Ω : Type*} [Fintype Ω]

/-- The reflection pencil is positive for every doubled-carrier vector exactly
on `|θ| ≤ 1`. -/
theorem pencilForm_nonnegative_iff [Nonempty Ω]
    (U J : Ω → ℝ) (hJ : ∀ ω, J ω = 1 ∨ J ω = -1)
    (hU : ∀ ω, U ω ≠ 0) (θ : ℝ) :
    (∀ x y : Ω → ℝ, 0 ≤ pencilForm U J θ x y) ↔ |θ| ≤ 1 := by
  constructor
  · intro hall
    by_contra hθ
    have hθ' : 1 < |θ| := lt_of_not_ge hθ
    obtain ⟨x, y, hneg⟩ := pencilForm_neg_of_one_lt U J hJ hU hθ' (Classical.choice inferInstance)
    exact (not_lt_of_ge (hall x y)) hneg
  · intro hθ x y
    exact pencilForm_nonneg U J hJ hθ x y

/-- Exhaustive kernel formula at the positive endpoint. -/
theorem pencilForm_kernel_iff
    (U J : Ω → ℝ) (hJ : ∀ ω, J ω = 1 ∨ J ω = -1)
    (hU : ∀ ω, U ω ≠ 0) (x y : Ω → ℝ) :
    pencilForm U J 1 x y = 0 ↔
      ∃ z : Ω → ℝ,
        x = (fun ω => (U ω)⁻¹ * z ω) ∧
        y = (fun ω => -((U ω)⁻¹ * (J ω * z ω))) := by
  have hsum : pencilForm U J 1 x y =
      ∑ ω, (U ω * y ω + J ω * (U ω * x ω)) ^ 2 := by
    rw [pencilForm, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    have hJ2 : J ω * J ω = 1 := by
      rcases hJ ω with h | h <;> rw [h] <;> ring
    nlinarith
  constructor
  · intro hzero
    rw [hsum] at hzero
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun ω (_ : ω ∈ Finset.univ) => sq_nonneg
        (U ω * y ω + J ω * (U ω * x ω)))).mp hzero
    refine ⟨fun ω => U ω * x ω, ?_, ?_⟩
    · funext ω
      rw [← mul_assoc, inv_mul_cancel₀ (hU ω), one_mul]
    · funext ω
      have hsquare := hz ω (Finset.mem_univ ω)
      have hlinear : U ω * y ω + J ω * (U ω * x ω) = 0 :=
        sq_eq_zero_iff.mp hsquare
      apply (mul_left_cancel₀ (hU ω))
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ (hU ω), one_mul]
      linarith
  · rintro ⟨z, rfl, rfl⟩
    exact pencilForm_kernel U J hJ hU z

end AffineRadicalReflectionKernelExact
end NCG
