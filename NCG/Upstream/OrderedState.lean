/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical ordered-state representation of a convex predictive model

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `thm:ordered-state-representation` — under the finite convex
  predictive model (`ass:finite-convex-model`: a convex state space
  `Ω`, a space `A` of affine effects containing the unit and
  separating `Ω`, pullback-stable affine updates), the evaluation
  functionals span an ordered vector space `V` with pointed
  generating cone `V₊`, the unit functional `𝐮` is strictly positive,
  `Ω` is identified with the normalized base `B(V₊, 𝐮)`, every
  affine update extends uniquely to a positive
  normalization-preserving linear map, and the Heisenberg pullback
  is unital and positive;
* `cor:positive-renewal-monoid` — the linearized updates compose,
  giving a monoid of positive normalization-preserving maps on `V`
  (dually, of unital positive maps on `A`).

The state space is modelled as a convex subset `Ω` of a real vector
space and effects as (restrictions of) affine functionals — exactly
the data of the assumption; compactness is not needed by any of the
proofs, as in the notes.
-/

namespace NCG.Upstream

open Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (A : Submodule ℝ (E →ᵃ[ℝ] ℝ)) (Ω : Set E)

/-- Evaluation of effects at a state: `ω̂(a) = a(ω)`. -/
def evalDual (ω : E) : Module.Dual ℝ ↥A where
  toFun a := (a : E →ᵃ[ℝ] ℝ) ω
  map_add' a b := by
    have : ((a + b : ↥A) : E →ᵃ[ℝ] ℝ) = (a : E →ᵃ[ℝ] ℝ) + b := rfl
    simp [this]
  map_smul' c a := by
    have : ((c • a : ↥A) : E →ᵃ[ℝ] ℝ) = c • (a : E →ᵃ[ℝ] ℝ) := rfl
    simp [this]

theorem evalDual_apply (ω : E) (a : ↥A) :
    evalDual A ω a = (a : E →ᵃ[ℝ] ℝ) ω := rfl

/-- The span `V` of the evaluation functionals. -/
def stateSpan : Submodule ℝ (Module.Dual ℝ ↥A) :=
  Submodule.span ℝ (evalDual A '' Ω)

/-- **Theorem `thm:ordered-state-representation` (the cone)**:
`V₊ = cone{ω̂ : ω ∈ Ω}` — nonnegative combinations of evaluation
functionals. -/
def stateCone : Set (Module.Dual ℝ ↥A) :=
  {v | ∃ (n : ℕ) (lam : Fin n → ℝ) (ω : Fin n → E),
    (∀ i, 0 ≤ lam i) ∧ (∀ i, ω i ∈ Ω) ∧
    v = ∑ i, lam i • evalDual A (ω i)}

theorem evalDual_mem_stateCone {ω : E} (hω : ω ∈ Ω) :
    evalDual A ω ∈ stateCone A Ω := by
  refine ⟨1, fun _ => 1, fun _ => ω, fun _ => zero_le_one,
    fun _ => hω, ?_⟩
  simp

/-- An affine functional applied to a convex combination. -/
theorem affineMap_sum {n : ℕ} (f : E →ᵃ[ℝ] ℝ) (lam : Fin n → ℝ)
    (ω : Fin n → E) (hsum : ∑ i, lam i = 1) :
    f (∑ i, lam i • ω i) = ∑ i, lam i • f (ω i) := by
  have happ : ∀ x, f x = f.linear x + f 0 := fun x =>
    congrFun (AffineMap.decomp f) x
  rw [happ, map_sum]
  have hterm : ∑ i, lam i • f (ω i)
      = ∑ i, (lam i • f.linear (ω i) + lam i • f 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [happ (ω i), smul_add]
  rw [hterm, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul]
  simp [map_smul]

section Unit

variable (hu : AffineMap.const ℝ E (1 : ℝ) ∈ A)

include hu

/-- The unit effect as an element of `A`. -/
def unitEffect : ↥A := ⟨AffineMap.const ℝ E (1 : ℝ), hu⟩

/-- The normalization functional `𝐮(v) = v(u)`. -/
def unitFunctional : Module.Dual ℝ (Module.Dual ℝ ↥A) :=
  Module.Dual.eval ℝ ↥A (unitEffect A hu)

theorem unitFunctional_apply (v : Module.Dual ℝ ↥A) :
    unitFunctional A hu v = v (unitEffect A hu) := rfl

theorem unitFunctional_evalDual (ω : E) :
    unitFunctional A hu (evalDual A ω) = 1 := rfl

/-- The total mass of a cone element. -/
theorem unitFunctional_stateCone_repr {n : ℕ} (lam : Fin n → ℝ)
    (ω : Fin n → E) :
    unitFunctional A hu (∑ i, lam i • evalDual A (ω i))
      = ∑ i, lam i := by
  rw [unitFunctional_apply]
  simp [evalDual_apply, unitEffect, AffineMap.const_apply]

/-- **Theorem `thm:ordered-state-representation` (ii,
nonnegativity)**: `𝐮 ≥ 0` on the cone. -/
theorem unitFunctional_nonneg {v : Module.Dual ℝ ↥A}
    (hv : v ∈ stateCone A Ω) : 0 ≤ unitFunctional A hu v := by
  obtain ⟨n, lam, ω, hlam, hω, rfl⟩ := hv
  rw [unitFunctional_stateCone_repr]
  exact Finset.sum_nonneg fun i _ => hlam i

/-- Vanishing total mass forces the zero functional. -/
theorem eq_zero_of_unitFunctional_eq_zero {v : Module.Dual ℝ ↥A}
    (hv : v ∈ stateCone A Ω) (h0 : unitFunctional A hu v = 0) :
    v = 0 := by
  obtain ⟨n, lam, ω, hlam, hω, rfl⟩ := hv
  rw [unitFunctional_stateCone_repr] at h0
  have hall : ∀ i ∈ Finset.univ, lam i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hlam i).mp h0
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hall i (Finset.mem_univ i), zero_smul]

/-- **Theorem `thm:ordered-state-representation` (i, pointedness)**:
`V₊ ∩ (−V₊) = {0}`. -/
theorem stateCone_pointed {v : Module.Dual ℝ ↥A}
    (hv : v ∈ stateCone A Ω) (hv' : -v ∈ stateCone A Ω) : v = 0 := by
  have h1 := unitFunctional_nonneg A Ω hu hv
  have h2 := unitFunctional_nonneg A Ω hu hv'
  rw [map_neg] at h2
  exact eq_zero_of_unitFunctional_eq_zero A Ω hu hv (le_antisymm
    (by linarith) h1)

/-- **Theorem `thm:ordered-state-representation` (i, generating)**:
the cone spans `V`. -/
theorem stateCone_generating :
    Submodule.span ℝ (stateCone A Ω) = stateSpan A Ω := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨n, lam, ω, _, hω, rfl⟩
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨ω i, hω i, rfl⟩)
  · rw [stateSpan, Submodule.span_le]
    rintro v ⟨ω, hω, rfl⟩
    exact Submodule.subset_span (evalDual_mem_stateCone A Ω hω)

/-- **Theorem `thm:ordered-state-representation` (ii, strict
positivity)**: `𝐮 > 0` on `V₊ ∖ {0}`. -/
theorem unitFunctional_pos {v : Module.Dual ℝ ↥A}
    (hv : v ∈ stateCone A Ω) (hne : v ≠ 0) :
    0 < unitFunctional A hu v :=
  lt_of_le_of_ne (unitFunctional_nonneg A Ω hu hv)
    (fun h0 => hne (eq_zero_of_unitFunctional_eq_zero A Ω hu hv h0.symm))

/-- **Theorem `thm:ordered-state-representation` (iii,
injectivity)**: effect separation makes evaluation injective. -/
theorem evalDual_injOn
    (hsep : ∀ ω ∈ Ω, ∀ ω' ∈ Ω,
      (∀ a : ↥A, (a : E →ᵃ[ℝ] ℝ) ω = (a : E →ᵃ[ℝ] ℝ) ω') → ω = ω') :
    Set.InjOn (evalDual A) Ω := by
  intro ω hω ω' hω' h
  exact hsep ω hω ω' hω' fun a => congrFun (congrArg DFunLike.coe h) a

/-- **Theorem `thm:ordered-state-representation` (iii, the base)**:
the normalized cone elements are exactly the evaluations of states —
`Ω ≃ B(V₊, 𝐮)`. -/
theorem stateCone_base (hconv : Convex ℝ Ω) :
    {v | v ∈ stateCone A Ω ∧ unitFunctional A hu v = 1}
      = evalDual A '' Ω := by
  ext v
  constructor
  · rintro ⟨⟨n, lam, ω, hlam, hω, rfl⟩, hmass⟩
    rw [unitFunctional_stateCone_repr] at hmass
    refine ⟨∑ i, lam i • ω i,
      hconv.sum_mem (fun i _ => hlam i) hmass fun i _ => hω i, ?_⟩
    apply LinearMap.ext
    intro a
    rw [evalDual_apply, affineMap_sum _ lam ω hmass]
    simp [evalDual_apply]
  · rintro ⟨ω, hω, rfl⟩
    exact ⟨evalDual_mem_stateCone A Ω hω,
      unitFunctional_evalDual A hu ω⟩

end Unit

section Update

variable (T : E →ᵃ[ℝ] E)
variable (hTA : ∀ a : ↥A, (a : E →ᵃ[ℝ] ℝ).comp T ∈ A)
variable (hTΩ : ∀ ω ∈ Ω, T ω ∈ Ω)

/-- **Theorem `thm:ordered-state-representation` (v, Heisenberg
pullback)**: `Φ_T(a) = a ∘ T` on effects. -/
def pullbackEffect : ↥A →ₗ[ℝ] ↥A where
  toFun a := ⟨(a : E →ᵃ[ℝ] ℝ).comp T, hTA a⟩
  map_add' a b := by
    apply Subtype.ext
    ext x
    have : ((a + b : ↥A) : E →ᵃ[ℝ] ℝ) = (a : E →ᵃ[ℝ] ℝ) + b := rfl
    simp [this, AffineMap.comp_apply]
  map_smul' c a := by
    apply Subtype.ext
    ext x
    have : ((c • a : ↥A) : E →ᵃ[ℝ] ℝ) = c • (a : E →ᵃ[ℝ] ℝ) := rfl
    simp [this, AffineMap.comp_apply]

theorem pullbackEffect_apply (a : ↥A) (x : E) :
    ((pullbackEffect A T hTA a : ↥A) : E →ᵃ[ℝ] ℝ) x
      = (a : E →ᵃ[ℝ] ℝ) (T x) := rfl

/-- **Theorem `thm:ordered-state-representation` (iv, the linear
extension)**: `T̃ = Φ_T^*` on the dual. -/
def stateMap : Module.Dual ℝ ↥A →ₗ[ℝ] Module.Dual ℝ ↥A :=
  (pullbackEffect A T hTA).dualMap

/-- **Theorem `thm:ordered-state-representation` (iv, extension
property)**: `T̃(ω̂) = (Tω)^`. -/
theorem stateMap_evalDual (ω : E) :
    stateMap A T hTA (evalDual A ω) = evalDual A (T ω) := rfl

/-- **Theorem `thm:ordered-state-representation` (iv, uniqueness)**:
any linear map sending `ω̂ ↦ (Tω)^` agrees with `T̃` on `V`. -/
theorem stateMap_unique
    (S : Module.Dual ℝ ↥A →ₗ[ℝ] Module.Dual ℝ ↥A)
    (hS : ∀ ω ∈ Ω, S (evalDual A ω) = evalDual A (T ω))
    {v : Module.Dual ℝ ↥A} (hv : v ∈ stateSpan A Ω) :
    S v = stateMap A T hTA v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, hω, rfl⟩ := hx
    rw [hS ω hω, stateMap_evalDual]
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add, map_add, ihx, ihy]
  | smul c x hx ih => rw [map_smul, map_smul, ih]

include hTΩ in
/-- **Theorem `thm:ordered-state-representation` (iv, positivity)**:
`T̃(V₊) ⊆ V₊`. -/
theorem stateMap_cone {v : Module.Dual ℝ ↥A}
    (hv : v ∈ stateCone A Ω) :
    stateMap A T hTA v ∈ stateCone A Ω := by
  obtain ⟨n, lam, ω, hlam, hω, rfl⟩ := hv
  refine ⟨n, lam, fun i => T (ω i), hlam,
    fun i => hTΩ (ω i) (hω i), ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, stateMap_evalDual]

/-- **Theorem `thm:ordered-state-representation` (iv,
normalization)**: `𝐮 ∘ T̃ = 𝐮` (the unit effect is pullback
invariant). -/
theorem stateMap_unitFunctional
    (hu : AffineMap.const ℝ E (1 : ℝ) ∈ A)
    (v : Module.Dual ℝ ↥A) :
    unitFunctional A hu (stateMap A T hTA v)
      = unitFunctional A hu v := by
  rw [unitFunctional_apply, unitFunctional_apply]
  have hunit : pullbackEffect A T hTA (unitEffect A hu)
      = unitEffect A hu := by
    apply Subtype.ext
    ext x
    rfl
  show v (pullbackEffect A T hTA (unitEffect A hu)) = v (unitEffect A hu)
  rw [hunit]

/-- **Theorem `thm:ordered-state-representation` (v, unitality)**:
`Φ_T(u) = u`. -/
theorem pullbackEffect_unital (hu : AffineMap.const ℝ E (1 : ℝ) ∈ A) :
    pullbackEffect A T hTA (unitEffect A hu) = unitEffect A hu := by
  apply Subtype.ext
  ext x
  rfl

include hTΩ in
/-- **Theorem `thm:ordered-state-representation` (v, positivity)**:
`Φ_T` is positive for the pointwise order of effects on `Ω`. -/
theorem pullbackEffect_positive {a : ↥A}
    (ha : ∀ ω ∈ Ω, 0 ≤ (a : E →ᵃ[ℝ] ℝ) ω) :
    ∀ ω ∈ Ω, 0 ≤ ((pullbackEffect A T hTA a : ↥A) : E →ᵃ[ℝ] ℝ) ω :=
  fun ω hω => ha (T ω) (hTΩ ω hω)

end Update

section Monoid

variable (T T' : E →ᵃ[ℝ] E)
variable (hTA : ∀ a : ↥A, (a : E →ᵃ[ℝ] ℝ).comp T ∈ A)
variable (hTA' : ∀ a : ↥A, (a : E →ᵃ[ℝ] ℝ).comp T' ∈ A)

/-- **Corollary `cor:positive-renewal-monoid` (Heisenberg
composition)**: `Φ_{T∘T'} = Φ_{T'} ∘ Φ_T`. -/
theorem pullbackEffect_comp
    (hTA'' : ∀ a : ↥A, (a : E →ᵃ[ℝ] ℝ).comp (T.comp T') ∈ A)
    (a : ↥A) :
    pullbackEffect A (T.comp T') hTA'' a
      = pullbackEffect A T' hTA' (pullbackEffect A T hTA a) := by
  apply Subtype.ext
  ext x
  rfl

/-- **Corollary `cor:positive-renewal-monoid` (Schrödinger
composition)**: the linearized updates compose,
`(T∘T')~ = T̃ ∘ T̃'`; with `stateMap_cone` and
`stateMap_unitFunctional` this makes the accumulated renewal maps a
monoid of positive normalization-preserving linear maps on `V`,
dually a monoid of unital positive maps on `A`. -/
theorem stateMap_comp (hTA'' :
      ∀ a : ↥A, (a : E →ᵃ[ℝ] ℝ).comp (T.comp T') ∈ A)
    (v : Module.Dual ℝ ↥A) :
    stateMap A (T.comp T') hTA'' v
      = stateMap A T hTA (stateMap A T' hTA' v) := by
  apply LinearMap.ext
  intro a
  show v (pullbackEffect A (T.comp T') hTA'' a) = _
  have hcomp : pullbackEffect A (T.comp T') hTA'' a
      = pullbackEffect A T' hTA' (pullbackEffect A T hTA a) := by
    apply Subtype.ext
    ext x
    rfl
  rw [hcomp]
  rfl

end Monoid

end NCG.Upstream
