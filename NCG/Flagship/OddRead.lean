/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Consequential odd-line Read extraction
  (`thm:consequential-odd-read-master`, flagship manuscript)

On the reduced predictive carrier `X` with physical involution `s`
(`s² = id`, unit-preserving `u∘s = u`) and a loaded odd line
`d ≠ 0` (`sd = -d`, `u(d) = 0`), if the admitted effect body is
closed under pullback by `s`, complement `f ↦ u - f`, and binary
convex mixing, and future separation supplies an admitted `e` with
`e(d) ≠ 0`, then the boxed symmetrized pair

  `e₊ = ½(e + u - s*e)`, `e₋ = u - e₊`

is an admitted binary Read with `s*e₊ = e₋` and
`e₊(d) = e(d) = -e₋(d) ≠ 0` (`consequential_odd_read`): the two
outcomes are future distinct and the involution acts by `-1` on
their contrast line.  Future separation enters as the hypothesis
supplying `e` (disclosed interface); the determinant-holonomy
consequence for recurrent loops is prose.
-/

namespace NCG

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- `thm:consequential-odd-read-master`, boxed extraction: the
symmetrized pair `e₊ = ½(e + u - s*e)`, `e₋ = u - e₊` is an
admitted exchange-covariant binary Read on the loaded odd line. -/
theorem consequential_odd_read
    (adm : (X →ₗ[ℝ] ℝ) → Prop) (u : X →ₗ[ℝ] ℝ) (s : X →ₗ[ℝ] X)
    (hss : s ∘ₗ s = LinearMap.id) (hus : u ∘ₗ s = u)
    (d : X) (hsd : s d = -d) (hud : u d = 0)
    (hcompl : ∀ f, adm f → adm (u - f))
    (hpull : ∀ f, adm f → adm (f ∘ₗ s))
    (hmix : ∀ f g, adm f → adm g → adm ((2⁻¹ : ℝ) • (f + g)))
    (e : X →ₗ[ℝ] ℝ) (he : adm e) (hed : e d ≠ 0) :
    adm ((2⁻¹ : ℝ) • (e + (u - e ∘ₗ s)))
    ∧ adm (u - (2⁻¹ : ℝ) • (e + (u - e ∘ₗ s)))
    ∧ ((2⁻¹ : ℝ) • (e + (u - e ∘ₗ s))) ∘ₗ s
        = u - (2⁻¹ : ℝ) • (e + (u - e ∘ₗ s))
    ∧ ((2⁻¹ : ℝ) • (e + (u - e ∘ₗ s))) d = e d
    ∧ (u - (2⁻¹ : ℝ) • (e + (u - e ∘ₗ s))) d = -(e d)
    ∧ ((2⁻¹ : ℝ) • (e + (u - e ∘ₗ s))) d ≠ 0 := by
  have hplus : adm ((2⁻¹ : ℝ) • (e + (u - e ∘ₗ s))) :=
    hmix e (u - e ∘ₗ s) he (hcompl _ (hpull e he))
  have hval : ((2⁻¹ : ℝ) • (e + (u - e ∘ₗ s))) d = e d := by
    simp only [LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, hsd, hud,
      map_neg]
    ring
  refine ⟨hplus, hcompl _ hplus, ?_, hval, ?_, ?_⟩
  · ext x
    have hsx : s (s x) = x := by
      have := congrArg (fun φ : X →ₗ[ℝ] X => φ x) hss
      simpa using this
    have hux : u (s x) = u x := by
      have := congrArg (fun φ : X →ₗ[ℝ] ℝ => φ x) hus
      simpa using this
    simp only [LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.sub_apply, hsx, hux]
    ring
  · rw [LinearMap.sub_apply, hval, hud]
    ring
  · rw [hval]
    exact hed

end NCG
