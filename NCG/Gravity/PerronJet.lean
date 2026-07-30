/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Perron-jet pressure dictionary
  (`thm:matrix-renewal-dictionary`, GR_emergence)

The implicit-function core of the matrix-renewal dictionary: given
the (Kato-analytic, here strictly differentiable) leading-root
function `F(z, y)` of the tilted renewal kernel, with the
nondegenerate depth slope `∂_z F(0) = -τ̄ ≠ 0` and observable slope
`∂_y F(0) = B_step`, there is a physical-depth pressure `P` with

* `F(P y, y) = 0` near the origin and `P 0 = 0` (existence),
* local uniqueness: every nearby root of `F` lies on the graph of
  `P`,
* the boxed first-derivative dictionary
  `B_phys = P'(0) = B_step / τ̄` (and the same statement applied to
  the `ϑ`-direction gives `s_phys = s_step / τ̄`).

The construction inverts `G(z,y) = (F(z,y), y)` by the strict
inverse function theorem; the derivative dictionary is the first
component of the inverse Jacobian.  The Kato analyticity of the
Perron root (which upgrades `P` to an analytic jet of connected
cumulants) is the disclosed interface hypothesis.
-/

namespace NCG

open ContinuousLinearMap

/-- `thm:matrix-renewal-dictionary` (IFT core): a strictly
differentiable root equation `F(z,y) = 0` with `F(0,0) = 0`,
`∂_z F = -τ̄ ≠ 0` and `∂_y F = B_step` admits a locally unique
physical-depth pressure `P` through the origin with
`P'(0) = B_step/τ̄`. -/
theorem matrix_renewal_dictionary {F : ℝ × ℝ → ℝ} {τ Bstep : ℝ}
    (hτ : 0 < τ)
    (hF : HasStrictFDerivAt F
      ((-τ) • fst ℝ ℝ ℝ + Bstep • snd ℝ ℝ ℝ) (0, 0))
    (hF0 : F (0, 0) = 0) :
    ∃ P : ℝ → ℝ, P 0 = 0 ∧
      (∀ᶠ y in nhds (0 : ℝ), F (P y, y) = 0) ∧
      (∀ᶠ p : ℝ × ℝ in nhds (0, 0), F p = 0 → P p.2 = p.1) ∧
      HasStrictDerivAt P (Bstep / τ) 0 := by
  have hτ0 : τ ≠ 0 := hτ.ne'
  -- the Jacobian of G(z,y) = (F(z,y), y) as an explicit equivalence
  set A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((-τ) • fst ℝ ℝ ℝ + Bstep • snd ℝ ℝ ℝ).prod (snd ℝ ℝ ℝ) with hA
  set Ainv : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((-τ⁻¹) • fst ℝ ℝ ℝ + (Bstep / τ) • snd ℝ ℝ ℝ).prod
      (snd ℝ ℝ ℝ) with hAinv
  have hleft : ∀ p : ℝ × ℝ, Ainv (A p) = p := by
    intro p
    simp only [hA, hAinv, ContinuousLinearMap.prod_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul]
    ext
    · field_simp
      ring
    · rfl
  have hright : ∀ p : ℝ × ℝ, A (Ainv p) = p := by
    intro p
    simp only [hA, hAinv, ContinuousLinearMap.prod_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul]
    ext
    · field_simp
      ring
    · rfl
  set E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearEquiv.equivOfInverse A Ainv hleft hright with hE
  -- G and its strict derivative
  set G : ℝ × ℝ → ℝ × ℝ := fun p => (F p, p.2) with hGdef
  have hG : HasStrictFDerivAt G (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (0, 0) := by
    have h2 : HasStrictFDerivAt (fun p : ℝ × ℝ => p.2)
        (snd ℝ ℝ ℝ) (0, 0) := (snd ℝ ℝ ℝ).hasStrictFDerivAt
    exact hF.prodMk h2
  have hG00 : G (0, 0) = (0, 0) := by
    simp [hGdef, hF0]
  -- local inverse
  set H : ℝ × ℝ → ℝ × ℝ := hG.localInverse G E (0, 0) with hH
  refine ⟨fun y => (H (0, y)).1, ?_, ?_, ?_, ?_⟩
  · -- P 0 = 0
    have := hG.localInverse_apply_image (f := G) (f' := E) (a := (0, 0))
    rw [hG00] at this
    simp [hH, this]
  · -- F (P y, y) = 0 eventually
    have hri := hG.eventually_right_inverse (f := G) (f' := E)
      (a := (0, 0))
    rw [hG00] at hri
    have htend : Filter.Tendsto (fun y : ℝ => ((0 : ℝ), y))
        (nhds 0) (nhds ((0 : ℝ), (0 : ℝ))) := by
      exact (Continuous.prodMk continuous_const continuous_id).tendsto' 0
        (0, 0) rfl
    filter_upwards [htend.eventually hri] with y hy
    have h1 : G (H (0, y)) = (0, y) := hy
    have h2 : F (H (0, y)) = 0 := congrArg Prod.fst h1
    have h3 : (H (0, y)).2 = y := congrArg Prod.snd h1
    calc F ((H (0, y)).1, y) = F ((H (0, y)).1, (H (0, y)).2) := by
          rw [h3]
    _ = F (H (0, y)) := by simp
    _ = 0 := h2
  · -- local uniqueness
    have hli := hG.eventually_left_inverse (f := G) (f' := E)
      (a := (0, 0))
    filter_upwards [hli] with p hp hFp
    have h1 : G p = (0, p.2) := by
      simp [hGdef, hFp]
    have h2 : H (0, p.2) = p := by
      rw [← h1]
      exact hp
    rw [h2]
  · -- derivative dictionary
    have hHd : HasStrictFDerivAt H
        ((E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) ((0, 0) : ℝ × ℝ) := by
      have := hG.to_localInverse (f := G) (f' := E) (a := (0, 0))
      rw [hG00] at this
      exact this
    have hinr : HasStrictFDerivAt (fun y : ℝ => ((0 : ℝ), y))
        (inr ℝ ℝ ℝ) 0 := (inr ℝ ℝ ℝ).hasStrictFDerivAt
    have hcomp : HasStrictFDerivAt (fun y : ℝ => H (0, y))
        ((E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).comp (inr ℝ ℝ ℝ)) 0 :=
      hHd.comp 0 hinr
    have hfst : HasStrictFDerivAt (fun y : ℝ => (H (0, y)).1)
        ((fst ℝ ℝ ℝ).comp
          ((E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).comp (inr ℝ ℝ ℝ))) 0 :=
      (fst ℝ ℝ ℝ).hasStrictFDerivAt.comp 0 hcomp
    have hval : ((fst ℝ ℝ ℝ).comp
        ((E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).comp (inr ℝ ℝ ℝ))) 1
        = Bstep / τ := by
      have hsymm : (E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = Ainv := rfl
      simp only [ContinuousLinearMap.comp_apply, hsymm,
        ContinuousLinearMap.inr_apply, hAinv,
        ContinuousLinearMap.prod_apply, add_apply,
        smul_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', smul_eq_mul]
      ring
    have := hfst.hasStrictDerivAt
    rw [hval] at this
    exact this

end NCG
