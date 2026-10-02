/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Topology.FiniteInverseSystemPruning
import RenewalGeometry.Spectralization.CompactFiniteStageSystem

/-!
# Inverse limits commute with compact group quotients

Let `G_n` be compact topological groups acting continuously on compact Hausdorff spaces `X_n`,
with continuous homomorphisms `φ_n : G_{n+1} → G_n` and continuous equivariant bonds
`ρ_n : X_{n+1} → X_n` (`ρ_n (g • x) = φ_n g • ρ_n x`).  Then the inverse limit of the orbit
spaces is the orbit space of the inverse limit:

`varprojlim_n (X_n / G_n) ≃ (varprojlim_n X_n) / (varprojlim_n G_n)`
(`EquivariantInverseSystem.limitQuotientEquiv`).

Surjectivity: the orbit fibres over a compatible thread of orbits form an inverse system of
nonempty compact Hausdorff spaces, which has a thread.  Injectivity: the transporter sets
`{g | g • x_n = y_n}` form an inverse system of nonempty compact Hausdorff spaces, whose thread
is an element of the limit group.

This is the "componentwise form before the compatible compact gauge quotient" of
`thm:supp-semifinite-exhaustion` (`predictive_spectral_geometry`); for products of factor
systems the limit is moreover taken factor by factor (`sectionsProdEquiv`).
-/

set_option linter.unusedSectionVars false

open Filter Topology Set MulAction

noncomputable section

namespace RenewalGeometry

universe u

/-- An `ℕ`-indexed equivariant inverse system: groups `G_n`, `G_n`-spaces `X_n`, homomorphisms
`φ_n : G_{n+1} → G_n` and equivariant bonds `ρ_n : X_{n+1} → X_n`. -/
structure EquivariantInverseSystem where
  /-- The groups. -/
  G : ℕ → Type u
  /-- The spaces. -/
  X : ℕ → Type u
  [instGroup : ∀ n, Group (G n)]
  [instAction : ∀ n, MulAction (G n) (X n)]
  /-- The group bonds. -/
  φ : ∀ n, G (n + 1) →* G n
  /-- The space bonds. -/
  ρ : ∀ n, X (n + 1) → X n
  ρ_smul : ∀ n (g : G (n + 1)) (x : X (n + 1)), ρ n (g • x) = φ n g • ρ n x

namespace EquivariantInverseSystem

variable (E : EquivariantInverseSystem.{u})

attribute [instance] instGroup instAction

/-- The inverse system of spaces. -/
abbrev spaceSystem : InverseSystem.{u} := ⟨E.X, E.ρ⟩

/-- The inverse system of groups. -/
abbrev groupSystem : InverseSystem.{u} := ⟨E.G, fun n => E.φ n⟩

/-- The limit group `varprojlim_n G_n` as a subgroup of `Π_n G_n`. -/
def limitGroup : Subgroup (∀ n, E.G n) where
  carrier := {g | ∀ n, E.φ n (g (n + 1)) = g n}
  mul_mem' {a b} ha hb n := by
    simp only [Pi.mul_apply, map_mul, ha n, hb n]
  one_mem' n := by simp
  inv_mem' {a} ha n := by simp [ha n]

/-- The limit group acts on the threads of spaces. -/
instance instMulActionLimit : MulAction E.limitGroup E.spaceSystem.Sections where
  smul g x := ⟨fun n => (g : ∀ n, E.G n) n • x.1 n, fun n => by
    show E.ρ n ((g : ∀ n, E.G n) (n + 1) • x.1 (n + 1)) = _
    have hx : E.ρ n (x.1 (n + 1)) = x.1 n := x.2 n
    rw [E.ρ_smul, g.2 n, hx]⟩
  one_smul x := Subtype.ext (funext fun n => one_smul _ _)
  mul_smul g h x := Subtype.ext (funext fun n => mul_smul _ _ _)

theorem limit_smul_apply (g : E.limitGroup) (x : E.spaceSystem.Sections) (n : ℕ) :
    (g • x).1 n = (g : ∀ n, E.G n) n • x.1 n := rfl

/-- The bond of orbit spaces induced by `ρ_n`. -/
def quotientBond (n : ℕ) :
    orbitRel.Quotient (E.G (n + 1)) (E.X (n + 1)) → orbitRel.Quotient (E.G n) (E.X n) :=
  Quotient.map (E.ρ n) fun x y hxy => by
    have hxy' : x ∈ orbit (E.G (n + 1)) y := hxy
    show E.ρ n x ∈ orbit (E.G n) (E.ρ n y)
    rw [mem_orbit_iff] at hxy' ⊢
    obtain ⟨g, rfl⟩ := hxy'
    exact ⟨E.φ n g, (E.ρ_smul n g y).symm⟩

theorem quotientBond_mk (n : ℕ) (x : E.X (n + 1)) :
    E.quotientBond n (Quotient.mk _ x) = Quotient.mk _ (E.ρ n x) := rfl

/-- The inverse system of orbit spaces. -/
abbrev quotientSystem : InverseSystem.{u} :=
  ⟨fun n => orbitRel.Quotient (E.G n) (E.X n), E.quotientBond⟩

/-- The comparison map `(varprojlim X_n)/(varprojlim G_n) → varprojlim (X_n/G_n)`. -/
def limitQuotientMap :
    orbitRel.Quotient E.limitGroup E.spaceSystem.Sections → E.quotientSystem.Sections :=
  Quotient.lift (fun x : E.spaceSystem.Sections =>
      (⟨fun n => Quotient.mk _ (x.1 n), fun n => by
        show E.quotientBond n (Quotient.mk _ (x.1 (n + 1))) = _
        rw [quotientBond_mk]
        exact congrArg (Quotient.mk _) (x.2 n)⟩ : E.quotientSystem.Sections))
    (fun x y hxy => by
      have hxy' : x ∈ orbit E.limitGroup y := hxy
      rw [mem_orbit_iff] at hxy'
      obtain ⟨g, rfl⟩ := hxy'
      apply Subtype.ext
      funext n
      apply Quotient.sound
      show _ ∈ orbit (E.G n) _
      exact ⟨(g : ∀ n, E.G n) n, rfl⟩)

theorem limitQuotientMap_mk (x : E.spaceSystem.Sections) (n : ℕ) :
    (E.limitQuotientMap (Quotient.mk _ x)).1 n = Quotient.mk _ (x.1 n) := rfl

section Compact

variable [∀ n, TopologicalSpace (E.G n)] [∀ n, IsTopologicalGroup (E.G n)]
  [∀ n, CompactSpace (E.G n)] [∀ n, T2Space (E.G n)]
  [∀ n, TopologicalSpace (E.X n)] [∀ n, CompactSpace (E.X n)] [∀ n, T2Space (E.X n)]
  [∀ n, ContinuousSMul (E.G n) (E.X n)]
  (hφ : ∀ n, Continuous (E.φ n)) (hρ : ∀ n, Continuous (E.ρ n))

include hφ hρ

/-- **Surjectivity**: every compatible thread of orbits lifts to a thread of points. -/
theorem limitQuotientMap_surjective : Function.Surjective E.limitQuotientMap := by
  intro ω
  -- the orbit fibres over `ω`
  let O : InverseSystem.{u} :=
    ⟨fun n => {x : E.X n // (Quotient.mk _ x : orbitRel.Quotient (E.G n) (E.X n)) = ω.1 n},
      fun n x => ⟨E.ρ n x.1, by
        rw [← quotientBond_mk, x.2]
        exact ω.2 n⟩⟩
  have hclosed : ∀ n, IsClosed {x : E.X n |
      (Quotient.mk _ x : orbitRel.Quotient (E.G n) (E.X n)) = ω.1 n} := by
    intro n
    haveI : T2Space (orbitRel.Quotient (E.G n) (E.X n)) :=
      CompactFiniteStage.t2Space_orbitQuotient
    exact isClosed_eq continuous_quotient_mk' continuous_const
  letI : ∀ n, TopologicalSpace (O.fibre n) := fun n => instTopologicalSpaceSubtype
  haveI : ∀ n, CompactSpace (O.fibre n) := fun n =>
    isCompact_iff_compactSpace.mp (hclosed n).isCompact
  haveI : ∀ n, T2Space (O.fibre n) := fun n => inferInstanceAs (T2Space {x : E.X n // _})
  have hOc : ∀ n, Continuous (O.bond n) := fun n =>
    ((hρ n).comp continuous_subtype_val).subtype_mk _
  have hOne : ∀ n, Nonempty (O.fibre n) := by
    intro n
    obtain ⟨x, hx⟩ := Quotient.exists_rep (ω.1 n)
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨t⟩ := (O.nonempty_sections_iff_fibre hOc).mpr hOne
  refine ⟨Quotient.mk _ ⟨fun n => (t.1 n).1, fun n => congrArg Subtype.val (t.2 n)⟩, ?_⟩
  apply Subtype.ext
  funext n
  exact (t.1 n).2

/-- **Injectivity**: threads with the same orbit at every stage are related by an element of
the limit group. -/
theorem limitQuotientMap_injective : Function.Injective E.limitQuotientMap := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h x =>
  induction b using Quotient.inductionOn with
  | h y =>
  have hn : ∀ n, (Quotient.mk _ (x.1 n) : orbitRel.Quotient (E.G n) (E.X n)) =
      Quotient.mk _ (y.1 n) := fun n => congrFun (congrArg Subtype.val hab) n
  -- transporters `g • y_n = x_n`
  let T : InverseSystem.{u} :=
    ⟨fun n => {g : E.G n // g • y.1 n = x.1 n},
      fun n g => ⟨E.φ n g.1, by
        have hx : E.ρ n (x.1 (n + 1)) = x.1 n := x.2 n
        have hy : E.ρ n (y.1 (n + 1)) = y.1 n := y.2 n
        rw [← hy, ← E.ρ_smul, g.2, hx]⟩⟩
  have hclosed : ∀ n, IsClosed {g : E.G n | g • y.1 n = x.1 n} := fun n =>
    isClosed_eq (continuous_id.smul continuous_const) continuous_const
  letI : ∀ n, TopologicalSpace (T.fibre n) := fun n => instTopologicalSpaceSubtype
  haveI : ∀ n, CompactSpace (T.fibre n) := fun n =>
    isCompact_iff_compactSpace.mp (hclosed n).isCompact
  haveI : ∀ n, T2Space (T.fibre n) := fun n => inferInstanceAs (T2Space {g : E.G n // _})
  have hTc : ∀ n, Continuous (T.bond n) := fun n =>
    ((hφ n).comp continuous_subtype_val).subtype_mk _
  have hTne : ∀ n, Nonempty (T.fibre n) := by
    intro n
    have h' : x.1 n ∈ orbit (E.G n) (y.1 n) := Quotient.exact (hn n)
    obtain ⟨g, hg⟩ := h'
    exact ⟨⟨g, hg⟩⟩
  obtain ⟨t⟩ := (T.nonempty_sections_iff_fibre hTc).mpr hTne
  let g : E.limitGroup := ⟨fun n => (t.1 n).1, fun n => congrArg Subtype.val (t.2 n)⟩
  apply Quotient.sound
  show x ∈ orbit E.limitGroup y
  exact ⟨g, Subtype.ext (funext fun n => (t.1 n).2)⟩

/-- **Inverse limits commute with compact group quotients**:
`(varprojlim X_n)/(varprojlim G_n) ≃ varprojlim (X_n/G_n)`. -/
def limitQuotientEquiv :
    orbitRel.Quotient E.limitGroup E.spaceSystem.Sections ≃ E.quotientSystem.Sections :=
  Equiv.ofBijective E.limitQuotientMap
    ⟨E.limitQuotientMap_injective hφ hρ, E.limitQuotientMap_surjective hφ hρ⟩

end Compact

end EquivariantInverseSystem

/-! ### Limits of products are products of limits -/

namespace InverseSystem

/-- The product of two inverse systems. -/
abbrev prod (S T : InverseSystem.{u}) : InverseSystem.{u} :=
  ⟨fun n => S.fibre n × T.fibre n, fun n => Prod.map (S.bond n) (T.bond n)⟩

/-- **Componentwise limits**: `varprojlim (S_n × T_n) ≃ varprojlim S_n × varprojlim T_n`. -/
def sectionsProdEquiv (S T : InverseSystem.{u}) :
    (S.prod T).Sections ≃ S.Sections × T.Sections where
  toFun x := (⟨fun n => (x.1 n).1, fun n => congrArg Prod.fst (x.2 n)⟩,
    ⟨fun n => (x.1 n).2, fun n => congrArg Prod.snd (x.2 n)⟩)
  invFun p := ⟨fun n => (p.1.1 n, p.2.1 n), fun n => Prod.ext (p.1.2 n) (p.2.2 n)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end InverseSystem

end RenewalGeometry
