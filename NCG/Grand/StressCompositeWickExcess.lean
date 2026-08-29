/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Stress--composite Wick excess

This file formalizes `thm:SMOS-stress-excess`.  A stress--composite tensor has
one stress slot and a finite family of represented composite slots.  Direct
and Wick tensors descend through a surjective stress short and a surjective OS
quotient in every composite slot.  Consequently, a nonzero quotient-visible
excess contradicts Gaussian (or quasi-free) Wick determination.

The second half records an admissible finite scheme change by linear
equivalences in the stress, composite, and value spaces.  If the direct and
Wick tensors transform by the same maps, their difference transforms
covariantly and its vanishing is invariant.
-/

namespace NCG.StressCompositeWickExcess

variable {𝕜 : Type*} [Field 𝕜]

/-- A tensor with one stress slot and `k` represented composite slots. -/
abbrev Tensor (k : ℕ) (Stress Composite Value : Type*)
    [AddCommGroup Stress] [Module 𝕜 Stress]
    [AddCommGroup Composite] [Module 𝕜 Composite]
    [AddCommGroup Value] [Module 𝕜 Value] :=
  Stress →ₗ[𝕜] MultilinearMap 𝕜 (fun _ : Fin k => Composite) Value

/-- The same-source direct-minus-Wick tensor. -/
def excess {k : ℕ} {Stress Composite Value : Type*}
    [AddCommGroup Stress] [Module 𝕜 Stress]
    [AddCommGroup Composite] [Module 𝕜 Composite]
    [AddCommGroup Value] [Module 𝕜 Value]
    (direct wick : Tensor (𝕜 := 𝕜) k Stress Composite Value) :
    Tensor (𝕜 := 𝕜) k Stress Composite Value :=
  direct - wick

/-- Gaussian/quasi-free determination on the selected packet means that the
direct tensor is exactly its Wick/Pfaffian prediction from the same primitive
covariance and source frame. -/
def IsGaussianOnPacket {k : ℕ} {Stress Composite Value : Type*}
    [AddCommGroup Stress] [Module 𝕜 Stress]
    [AddCommGroup Composite] [Module 𝕜 Composite]
    [AddCommGroup Value] [Module 𝕜 Value]
    (direct wick : Tensor (𝕜 := 𝕜) k Stress Composite Value) : Prop :=
  direct = wick

/-- Direct and Wick tensors together with their stress-short and multislot OS
descent.  Surjectivity says that these are the actual quotient spaces rather
than an unrelated collection of test vectors. -/
structure QuotientPacket (k : ℕ)
    (Stress Composite StressQ CompositeQ Value : Type*)
    [AddCommGroup Stress] [Module 𝕜 Stress]
    [AddCommGroup Composite] [Module 𝕜 Composite]
    [AddCommGroup StressQ] [Module 𝕜 StressQ]
    [AddCommGroup CompositeQ] [Module 𝕜 CompositeQ]
    [AddCommGroup Value] [Module 𝕜 Value] where
  direct : Tensor (𝕜 := 𝕜) k Stress Composite Value
  wick : Tensor (𝕜 := 𝕜) k Stress Composite Value
  stressShort : Stress →ₗ[𝕜] StressQ
  compositeQuotient : Composite →ₗ[𝕜] CompositeQ
  stressShort_surjective : Function.Surjective stressShort
  compositeQuotient_surjective : Function.Surjective compositeQuotient
  visibleDirect : Tensor (𝕜 := 𝕜) k StressQ CompositeQ Value
  visibleWick : Tensor (𝕜 := 𝕜) k StressQ CompositeQ Value
  direct_descends : ∀ t c,
    visibleDirect (stressShort t) (fun i => compositeQuotient (c i)) = direct t c
  wick_descends : ∀ t c,
    visibleWick (stressShort t) (fun i => compositeQuotient (c i)) = wick t c
  stressCurrentRelation : Prop
  energyHamiltonianIncidence : Prop

section Quotient

variable {k : ℕ}
variable {Stress Composite StressQ CompositeQ Value : Type*}
variable [AddCommGroup Stress] [Module 𝕜 Stress]
variable [AddCommGroup Composite] [Module 𝕜 Composite]
variable [AddCommGroup StressQ] [Module 𝕜 StressQ]
variable [AddCommGroup CompositeQ] [Module 𝕜 CompositeQ]
variable [AddCommGroup Value] [Module 𝕜 Value]

/-- Multislot descent commutes with taking the direct-minus-Wick excess. -/
theorem visible_excess_descends
    (p : QuotientPacket (𝕜 := 𝕜) k Stress Composite StressQ CompositeQ Value)
    (t : Stress) (c : Fin k → Composite) :
    excess p.visibleDirect p.visibleWick (p.stressShort t)
        (fun i => p.compositeQuotient (c i)) =
      excess p.direct p.wick t c := by
  simp only [excess, LinearMap.sub_apply, MultilinearMap.sub_apply]
  rw [p.direct_descends, p.wick_descends]

/-- `thm:SMOS-stress-excess`, non-Gaussianity part: after the relation and
incidence checks have passed, a nonzero quotient-visible excess rules out
Gaussian/quasi-free Wick determination on the selected local packet. -/
theorem not_gaussian_of_visible_excess_ne_zero
    (p : QuotientPacket (𝕜 := 𝕜) k Stress Composite StressQ CompositeQ Value)
    (_hrelation : p.stressCurrentRelation)
    (_hincidence : p.energyHamiltonianIncidence)
    (hvisible : excess p.visibleDirect p.visibleWick ≠ 0) :
    ¬ IsGaussianOnPacket p.direct p.wick := by
  intro hgaussian
  apply hvisible
  ext tq cq
  obtain ⟨t, rfl⟩ := p.stressShort_surjective tq
  choose c hc using fun i => p.compositeQuotient_surjective (cq i)
  have hdesc := visible_excess_descends p t c
  rw [show (fun i => p.compositeQuotient (c i)) = cq by funext i; exact hc i] at hdesc
  change p.direct = p.wick at hgaussian
  rw [show excess p.direct p.wick = 0 by simp [excess, hgaussian]] at hdesc
  simpa using hdesc

end Quotient

section Scheme

variable {k : ℕ}
variable {Stress Composite Value Stress' Composite' Value' : Type*}
variable [AddCommGroup Stress] [Module 𝕜 Stress]
variable [AddCommGroup Composite] [Module 𝕜 Composite]
variable [AddCommGroup Value] [Module 𝕜 Value]
variable [AddCommGroup Stress'] [Module 𝕜 Stress']
variable [AddCommGroup Composite'] [Module 𝕜 Composite']
variable [AddCommGroup Value'] [Module 𝕜 Value']

/-- The finite invertible basis maps of an admissible stress/composite scheme
change.  Nuisance additions have already been annihilated by the stress short,
so only the induced quotient equivalences remain. -/
structure SchemeChange where
  stress : Stress ≃ₗ[𝕜] Stress'
  composite : Composite ≃ₗ[𝕜] Composite'
  value : Value ≃ₗ[𝕜] Value'

/-- Tensor covariance under the common multilinear basis maps. -/
def Covariant (S : SchemeChange (𝕜 := 𝕜) (Stress := Stress)
    (Composite := Composite) (Value := Value) (Stress' := Stress')
    (Composite' := Composite') (Value' := Value'))
    (A : Tensor (𝕜 := 𝕜) k Stress Composite Value)
    (B : Tensor (𝕜 := 𝕜) k Stress' Composite' Value') : Prop :=
  ∀ t c, B (S.stress t) (fun i => S.composite (c i)) = S.value (A t c)

/-- Common covariance of direct and Wick tensors implies covariance of their
excess. -/
theorem excess_covariant
    (S : SchemeChange (𝕜 := 𝕜) (Stress := Stress)
      (Composite := Composite) (Value := Value) (Stress' := Stress')
      (Composite' := Composite') (Value' := Value'))
    (direct wick : Tensor (𝕜 := 𝕜) k Stress Composite Value)
    (direct' wick' : Tensor (𝕜 := 𝕜) k Stress' Composite' Value')
    (hdirect : Covariant S direct direct')
    (hwick : Covariant S wick wick') :
    Covariant S (excess direct wick) (excess direct' wick') := by
  intro t c
  simp only [excess, LinearMap.sub_apply, MultilinearMap.sub_apply]
  rw [hdirect, hwick, map_sub]

/-- A covariantly transformed tensor vanishes exactly when the original one
does. -/
theorem covariant_zero_iff
    (S : SchemeChange (𝕜 := 𝕜) (Stress := Stress)
      (Composite := Composite) (Value := Value) (Stress' := Stress')
      (Composite' := Composite') (Value' := Value'))
    (A : Tensor (𝕜 := 𝕜) k Stress Composite Value)
    (B : Tensor (𝕜 := 𝕜) k Stress' Composite' Value')
    (hcov : Covariant S A B) :
    B = 0 ↔ A = 0 := by
  constructor
  · intro hB
    ext t c
    have h := hcov t c
    rw [hB] at h
    exact S.value.injective (by simpa using h.symm)
  · intro hA
    ext t' c'
    obtain ⟨t, rfl⟩ := S.stress.surjective t'
    choose c hc using fun i => S.composite.surjective (c' i)
    rw [← show (fun i => S.composite (c i)) = c' by funext i; exact hc i]
    have h := hcov t c
    rw [hA] at h
    simpa using h

/-- `thm:SMOS-stress-excess`, scheme part: if direct and Wick tensors use the
same finite admissible scheme maps, vanishing of their excess is invariant. -/
theorem excess_vanishing_scheme_invariant
    (S : SchemeChange (𝕜 := 𝕜) (Stress := Stress)
      (Composite := Composite) (Value := Value) (Stress' := Stress')
      (Composite' := Composite') (Value' := Value'))
    (direct wick : Tensor (𝕜 := 𝕜) k Stress Composite Value)
    (direct' wick' : Tensor (𝕜 := 𝕜) k Stress' Composite' Value')
    (hdirect : Covariant S direct direct')
    (hwick : Covariant S wick wick') :
    excess direct' wick' = 0 ↔ excess direct wick = 0 :=
  covariant_zero_iff S _ _ (excess_covariant S direct wick direct' wick' hdirect hwick)

/-- Bundled exact conclusion of `thm:SMOS-stress-excess`. -/
theorem stress_linked_primitive_non_gaussianity_and_scheme_invariance
    {StressQ CompositeQ : Type*}
    [AddCommGroup StressQ] [Module 𝕜 StressQ]
    [AddCommGroup CompositeQ] [Module 𝕜 CompositeQ]
    (p : QuotientPacket (𝕜 := 𝕜) k Stress Composite StressQ CompositeQ Value)
    (hrelation : p.stressCurrentRelation)
    (hincidence : p.energyHamiltonianIncidence)
    (hvisible : excess p.visibleDirect p.visibleWick ≠ 0)
    (S : SchemeChange (𝕜 := 𝕜) (Stress := StressQ)
      (Composite := CompositeQ) (Value := Value) (Stress' := Stress')
      (Composite' := Composite') (Value' := Value'))
    (direct' wick' : Tensor (𝕜 := 𝕜) k Stress' Composite' Value')
    (hdirect : Covariant S p.visibleDirect direct')
    (hwick : Covariant S p.visibleWick wick') :
    (¬ IsGaussianOnPacket p.direct p.wick) ∧
      (excess direct' wick' = 0 ↔ excess p.visibleDirect p.visibleWick = 0) := by
  exact ⟨not_gaussian_of_visible_excess_ne_zero p hrelation hincidence hvisible,
    excess_vanishing_scheme_invariant S p.visibleDirect p.visibleWick
      direct' wick' hdirect hwick⟩

end Scheme

end NCG.StressCompositeWickExcess
