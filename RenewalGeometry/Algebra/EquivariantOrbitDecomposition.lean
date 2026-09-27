/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Stratified orbit decomposition along an equivariant map

Let a group `G` act on `X` and `Y` and let `π : X → Y` be `G`-equivariant.  The orbit space of
`X` is stratified over the orbit space of `Y`: choosing a representative `y_ω` of every orbit
`ω ∈ Y/G`,

`X / G ≃ Σ_{ω ∈ Y/G} π⁻¹(y_ω) / Stab_G(y_ω)`   (`EquivariantMap.orbitDecomposition`).

This is the "simultaneous equivalence under the common stabilizer" of the finite stratified
inverse-fibre exhaustion (`thm:supp-finite-exhaustion` of `predictive_spectral_geometry`),
where `Y` is the correlation spectrahedron with the gauge group acting by block congruence,
`X` the set of fully reduced realizations and `π` the joint Gram map.  In general the
quotient is stratified and not a Cartesian product: the fibre quotients depend on the
stabilizer of the representative.

* `EquivariantMap.fibre y` is the fibre `π⁻¹(y)` with its `Stab_G(y)`-action.
* `EquivariantMap.orbitDecomposition` is the bijection above (built from the explicit map
  `fromSigma : ⟨ω, [z]⟩ ↦ [z]`, which is shown bijective).
* `orbitRelQuotientCongr`: an equivariant bijection induces a bijection of orbit spaces.
-/

set_option linter.unusedSectionVars false

namespace RenewalGeometry.EquivariantOrbit

open MulAction

variable {G : Type*} [Group G] {X Y : Type*} [MulAction G X] [MulAction G Y]

/-- A `G`-equivariant map between `G`-sets. -/
structure EquivariantMap (G : Type*) [Group G] (X Y : Type*) [MulAction G X] [MulAction G Y] where
  /-- The underlying map. -/
  toFun : X → Y
  /-- Equivariance. -/
  map_smul : ∀ (g : G) (x : X), toFun (g • x) = g • toFun x

namespace EquivariantMap

variable (E : EquivariantMap G X Y)

/-- The fibre `π⁻¹(y)`. -/
abbrev fibre (y : Y) : Type _ := {x : X // E.toFun x = y}

/-- The stabilizer of `y` acts on the fibre over `y`. -/
instance instMulActionStabilizerFibre (y : Y) : MulAction (stabilizer G y) (E.fibre y) where
  smul g x := ⟨(g : G) • x.1, by rw [E.map_smul, x.2]; exact g.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul (g : G) (h : G) x.1)

theorem smul_fibre_val (y : Y) (g : stabilizer G y) (x : E.fibre y) :
    ((g • x : E.fibre y) : X) = (g : G) • (x : X) := rfl

/-- The map `⟨ω, [z]⟩ ↦ [z]` from the stratified sum to the orbit space of `X`. -/
noncomputable def fromSigma (p : Σ ω : orbitRel.Quotient G Y,
    orbitRel.Quotient (stabilizer G ω.out) (E.fibre ω.out)) : orbitRel.Quotient G X :=
  Quotient.lift (fun z : E.fibre p.1.out => (⟦z.1⟧ : orbitRel.Quotient G X))
    (fun z z' h => by
      obtain ⟨g, hg⟩ := mem_orbit_iff.1 (orbitRel_apply.1 h)
      exact Quotient.sound (orbitRel_apply.2 (mem_orbit_iff.2 ⟨(g : G), congrArg Subtype.val hg⟩)))
    p.2

theorem fromSigma_mk (ω : orbitRel.Quotient G Y) (z : E.fibre ω.out) :
    E.fromSigma ⟨ω, ⟦z⟧⟩ = ⟦z.1⟧ := rfl

theorem fromSigma_injective : Function.Injective E.fromSigma := by
  rintro ⟨ω, c⟩ ⟨ω', c'⟩ h
  revert h
  refine Quotient.inductionOn₂ c c' fun z z' h => ?_
  rw [fromSigma_mk, fromSigma_mk] at h
  obtain ⟨g, hg⟩ := mem_orbit_iff.1 (orbitRel_apply.1 (Quotient.exact h))
  have hy : ω.out = g • ω'.out := by
    rw [← z.2, ← z'.2, ← hg, E.map_smul]
  have hω : ω = ω' := by
    rw [← Quotient.out_eq ω, ← Quotient.out_eq ω']
    exact Quotient.sound (orbitRel_apply.2 (mem_orbit_iff.2 ⟨g, hy.symm⟩))
  subst hω
  have hg' : g ∈ stabilizer G ω.out := by
    rw [mem_stabilizer_iff]
    exact hy.symm
  congr 1
  exact Quotient.sound (orbitRel_apply.2 (mem_orbit_iff.2 ⟨⟨g, hg'⟩, Subtype.ext hg⟩))

theorem fromSigma_surjective : Function.Surjective E.fromSigma := by
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨g, hg⟩ := mem_orbit_iff.1
      (orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (⟦E.toFun x⟧ : orbitRel.Quotient G Y))))
    refine ⟨⟨⟦E.toFun x⟧, ⟦⟨g • x, by rw [E.map_smul]; exact hg⟩⟧⟩, ?_⟩
    rw [fromSigma_mk]
    exact Quotient.sound (orbitRel_apply.2 (mem_orbit_iff.2 ⟨g, rfl⟩))

/-- **Stratified orbit decomposition**: `X/G ≃ Σ_{ω ∈ Y/G} π⁻¹(y_ω)/Stab(y_ω)` for an
equivariant `π : X → Y`, with `y_ω` the chosen representative `ω.out`. -/
noncomputable def orbitDecomposition :
    orbitRel.Quotient G X ≃
      Σ ω : orbitRel.Quotient G Y, orbitRel.Quotient (stabilizer G ω.out) (E.fibre ω.out) :=
  (Equiv.ofBijective E.fromSigma ⟨E.fromSigma_injective, E.fromSigma_surjective⟩).symm

theorem orbitDecomposition_symm_apply (ω : orbitRel.Quotient G Y) (z : E.fibre ω.out) :
    E.orbitDecomposition.symm ⟨ω, ⟦z⟧⟩ = ⟦z.1⟧ := rfl

/-- The stratum of the class of `x` is the orbit of `π x`. -/
theorem orbitDecomposition_fst (x : X) :
    (E.orbitDecomposition ⟦x⟧).1 = ⟦E.toFun x⟧ := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.1
    (orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (⟦E.toFun x⟧ : orbitRel.Quotient G Y))))
  have : (⟦x⟧ : orbitRel.Quotient G X) =
      E.orbitDecomposition.symm ⟨⟦E.toFun x⟧, ⟦⟨g • x, by rw [E.map_smul]; exact hg⟩⟧⟩ := by
    rw [orbitDecomposition_symm_apply]
    exact Quotient.sound (orbitRel_apply.2 (mem_orbit_iff.2 ⟨g⁻¹, by simp⟩))
  rw [this, Equiv.apply_symm_apply]

end EquivariantMap

/-- An equivariant bijection induces a bijection of orbit spaces. -/
def orbitRelQuotientCongr {A B : Type*} [MulAction G A] [MulAction G B] (e : A ≃ B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a) :
    orbitRel.Quotient G A ≃ orbitRel.Quotient G B :=
  Quotient.congr e fun a b => by
    change orbitRel G A a b ↔ orbitRel G B (e a) (e b)
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, by rw [← he, hg]⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, e.injective (by rw [he, hg])⟩

end RenewalGeometry.EquivariantOrbit
