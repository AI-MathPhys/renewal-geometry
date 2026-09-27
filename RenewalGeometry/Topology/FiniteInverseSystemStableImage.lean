/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Inverse systems over `ℕ`, stable images and the finite-intersection property

An `ℕ`-indexed inverse system (`InverseSystem`: fibres `F n` with bonding maps
`f n : F (n+1) → F n`) has the compatible threads `Sections = {x | f n (x (n+1)) = x n}` as its
projective limit.  The **stable image** of stage `n` is the set of elements that admit
preimage chains of every finite length,
`stableImage n = ⋂_k extendable k n`, `extendable 0 n = univ`,
`extendable (k+1) n = f n '' extendable k (n+1)`.

* every thread lies in the stable images (`mem_stableImage_of_sections`), so the projective
  limit of the system is the projective limit of the stable-image system
  (`sectionsEquivStable`);
* for **compact Hausdorff** fibres and continuous bonding maps the bonding maps map stable
  images *onto* stable images (`exists_mem_stableImage_bond_eq`, the Mittag-Leffler
  stabilisation, proved through the finite-intersection property of a decreasing chain of
  nonempty closed sets in a compact space, `nonempty_iInter_of_antitone_of_isClosed`), and
  the stable images are nonempty as soon as the fibres are (`stableImage_nonempty`);
* hence the projective limit is nonempty exactly when every stable image is nonempty,
  equivalently when every fibre is nonempty (`nonempty_sections_iff_stableImage`,
  `nonempty_sections_iff_fibre`); for finite fibres (discrete topology) this is König's
  lemma (`nonempty_sections_iff_fibre_of_finite`);
* `sectionsEquivOfStageEquiv`: stagewise bijections compatible with the bonding maps
  induce a bijection of projective limits.

This is the abstract projective-limit shell of the completed quasilocal/semifinite
inverse-fibre theorem (`thm:supp-semifinite-exhaustion` of `predictive_spectral_geometry`):
"surjective restriction to stable images makes the inverse system of nonempty compact finite
strata satisfy the finite-intersection property, so compatible threads exist whenever every
stable image is nonempty".
-/

set_option linter.unusedSectionVars false

namespace RenewalGeometry

open Set

/-- A decreasing sequence of nonempty closed subsets of a compact space has nonempty
intersection (the finite-intersection property). -/
theorem nonempty_iInter_of_antitone_of_isClosed {α : Type*} [TopologicalSpace α] [CompactSpace α]
    (A : ℕ → Set α) (hA : ∀ k, A (k + 1) ⊆ A k) (hne : ∀ k, (A k).Nonempty)
    (hcl : ∀ k, IsClosed (A k)) : (⋂ k, A k).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed A hA hne
    (hcl 0).isCompact hcl

universe u

/-- An `ℕ`-indexed inverse system of types. -/
structure InverseSystem where
  /-- The stage fibres. -/
  fibre : ℕ → Type u
  /-- The bonding maps `F (n+1) → F n`. -/
  bond : ∀ n, fibre (n + 1) → fibre n

namespace InverseSystem

variable (S : InverseSystem.{u})

/-- The projective limit: compatible threads. -/
def Sections : Type u := {x : ∀ n, S.fibre n // ∀ n, S.bond n (x (n + 1)) = x n}

/-- `extendable k n`: the elements of stage `n` admitting a preimage chain of length `k`. -/
def extendable : ℕ → ∀ n, Set (S.fibre n)
  | 0, _ => univ
  | k + 1, n => S.bond n '' extendable k (n + 1)

/-- The stable image of stage `n`: elements admitting preimage chains of every length. -/
def stableImage (n : ℕ) : Set (S.fibre n) := ⋂ k, S.extendable k n

theorem extendable_zero (n : ℕ) : S.extendable 0 n = univ := rfl

theorem extendable_succ (k n : ℕ) :
    S.extendable (k + 1) n = S.bond n '' S.extendable k (n + 1) := by
  simp [extendable]

theorem extendable_succ_subset (k : ℕ) : ∀ n, S.extendable (k + 1) n ⊆ S.extendable k n := by
  induction k with
  | zero => intro n; exact subset_univ _
  | succ k ih =>
    intro n
    rw [extendable_succ, extendable_succ]
    exact image_mono (ih (n + 1))

theorem mem_stableImage_iff (n : ℕ) (y : S.fibre n) :
    y ∈ S.stableImage n ↔ ∀ k, y ∈ S.extendable k n := mem_iInter

/-- Bonding maps send stable images into stable images. -/
theorem bond_mem_stableImage (n : ℕ) {y : S.fibre (n + 1)} (hy : y ∈ S.stableImage (n + 1)) :
    S.bond n y ∈ S.stableImage n := by
  rw [mem_stableImage_iff] at hy ⊢
  intro k
  exact S.extendable_succ_subset k n ⟨y, hy k, rfl⟩

/-- Every thread lies in the stable images. -/
theorem mem_stableImage_of_sections (x : S.Sections) (n : ℕ) : x.1 n ∈ S.stableImage n := by
  rw [mem_stableImage_iff]
  intro k
  induction k generalizing n with
  | zero => exact mem_univ _
  | succ k ih =>
    rw [extendable_succ]
    exact ⟨x.1 (n + 1), ih (n + 1), x.2 n⟩

/-- The system of stable images. -/
def stableSystem : InverseSystem.{u} where
  fibre n := S.stableImage n
  bond n y := ⟨S.bond n y.1, S.bond_mem_stableImage n y.2⟩

/-- **The projective limit is the projective limit of the stable-image system.** -/
def sectionsEquivStable : S.Sections ≃ S.stableSystem.Sections where
  toFun x := ⟨fun n => ⟨x.1 n, S.mem_stableImage_of_sections x n⟩, fun n => Subtype.ext (x.2 n)⟩
  invFun x := ⟨fun n => (x.1 n).1, fun n => congrArg Subtype.val (x.2 n)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem extendable_nonempty (hne : ∀ n, Nonempty (S.fibre n)) (k : ℕ) :
    ∀ n, (S.extendable k n).Nonempty := by
  induction k with
  | zero => intro n; exact univ_nonempty
  | succ k ih => intro n; rw [extendable_succ]; exact (ih (n + 1)).image _

section Compact

variable [∀ n, TopologicalSpace (S.fibre n)] [∀ n, CompactSpace (S.fibre n)]
  [∀ n, T2Space (S.fibre n)] (hcont : ∀ n, Continuous (S.bond n))

include hcont

theorem isClosed_extendable (k : ℕ) : ∀ n, IsClosed (S.extendable k n) := by
  induction k with
  | zero => intro n; exact isClosed_univ
  | succ k ih =>
    intro n
    rw [extendable_succ]
    exact ((ih (n + 1)).isCompact.image (hcont n)).isClosed

theorem isClosed_stableImage (n : ℕ) : IsClosed (S.stableImage n) :=
  isClosed_iInter fun k => S.isClosed_extendable hcont k n

/-- **Mittag-Leffler**: for compact Hausdorff fibres and continuous bonding maps, the
bonding maps map stable images onto stable images. -/
theorem exists_mem_stableImage_bond_eq (n : ℕ) {e : S.fibre n} (he : e ∈ S.stableImage n) :
    ∃ y ∈ S.stableImage (n + 1), S.bond n y = e := by
  rw [mem_stableImage_iff] at he
  let A : ℕ → Set (S.fibre (n + 1)) := fun k => S.extendable k (n + 1) ∩ S.bond n ⁻¹' {e}
  have hA : ∀ k, A (k + 1) ⊆ A k := fun k =>
    inter_subset_inter_left _ (S.extendable_succ_subset k (n + 1))
  have hne : ∀ k, (A k).Nonempty := by
    intro k
    obtain ⟨y, hy, hye⟩ := he (k + 1)
    exact ⟨y, hy, hye⟩
  have hcl : ∀ k, IsClosed (A k) := fun k =>
    (S.isClosed_extendable hcont k (n + 1)).inter (isClosed_singleton.preimage (hcont n))
  obtain ⟨y, hy⟩ := nonempty_iInter_of_antitone_of_isClosed A hA hne hcl
  rw [mem_iInter] at hy
  refine ⟨y, ?_, (hy 0).2⟩
  rw [mem_stableImage_iff]
  exact fun k => (hy k).1

/-- For compact Hausdorff nonempty fibres the stable images are nonempty. -/
theorem stableImage_nonempty (hne : ∀ n, Nonempty (S.fibre n)) (n : ℕ) :
    (S.stableImage n).Nonempty :=
  nonempty_iInter_of_antitone_of_isClosed _ (fun k => S.extendable_succ_subset k n)
    (fun k => S.extendable_nonempty hne k n) (fun k => S.isClosed_extendable hcont k n)

/-- A thread through the stable images, built by successive lifting. -/
noncomputable def stableThread (h0 : (S.stableImage 0).Nonempty) :
    ∀ n, {y : S.fibre n // y ∈ S.stableImage n}
  | 0 => ⟨h0.some, h0.some_mem⟩
  | n + 1 => ⟨(S.exists_mem_stableImage_bond_eq hcont n (stableThread h0 n).2).choose,
      (S.exists_mem_stableImage_bond_eq hcont n (stableThread h0 n).2).choose_spec.1⟩

theorem bond_stableThread (h0 : (S.stableImage 0).Nonempty) (n : ℕ) :
    S.bond n (S.stableThread hcont h0 (n + 1)).1 = (S.stableThread hcont h0 n).1 := by
  simp only [stableThread]
  exact (S.exists_mem_stableImage_bond_eq hcont n (S.stableThread hcont h0 n).2).choose_spec.2

/-- **Finite-intersection property**: for compact Hausdorff fibres and continuous bonding maps
the projective limit is nonempty iff every stable image is nonempty. -/
theorem nonempty_sections_iff_stableImage :
    Nonempty S.Sections ↔ ∀ n, (S.stableImage n).Nonempty := by
  constructor
  · rintro ⟨x⟩ n
    exact ⟨x.1 n, S.mem_stableImage_of_sections x n⟩
  · intro h
    exact ⟨⟨fun n => (S.stableThread hcont (h 0) n).1, S.bond_stableThread hcont (h 0)⟩⟩

/-- The projective limit is nonempty iff every fibre is nonempty. -/
theorem nonempty_sections_iff_fibre : Nonempty S.Sections ↔ ∀ n, Nonempty (S.fibre n) := by
  rw [nonempty_sections_iff_stableImage S hcont]
  constructor
  · intro h n
    exact ⟨(h n).some⟩
  · exact S.stableImage_nonempty hcont

end Compact

/-- **König's lemma**: for finite fibres the projective limit is nonempty iff every fibre is
nonempty (the discrete topology is compact Hausdorff and every map is continuous). -/
theorem nonempty_sections_iff_fibre_of_finite [∀ n, Finite (S.fibre n)] :
    Nonempty S.Sections ↔ ∀ n, Nonempty (S.fibre n) := by
  let _ : ∀ n, TopologicalSpace (S.fibre n) := fun _ => ⊥
  have _ : ∀ n, DiscreteTopology (S.fibre n) := fun _ => ⟨rfl⟩
  exact S.nonempty_sections_iff_fibre fun n => continuous_of_discreteTopology

/-- Stagewise bijections compatible with the bonding maps induce a bijection of projective
limits. -/
def sectionsEquivOfStageEquiv (S' : InverseSystem.{u}) (e : ∀ n, S.fibre n ≃ S'.fibre n)
    (he : ∀ n (y : S.fibre (n + 1)), e n (S.bond n y) = S'.bond n (e (n + 1) y)) :
    S.Sections ≃ S'.Sections where
  toFun x := ⟨fun n => e n (x.1 n), fun n => by rw [← he, x.2]⟩
  invFun x := ⟨fun n => (e n).symm (x.1 n), fun n => by
    apply (e n).injective
    rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply, x.2]⟩
  left_inv x := Subtype.ext (funext fun n => (e n).symm_apply_apply _)
  right_inv x := Subtype.ext (funext fun n => (e n).apply_symm_apply _)

/-- The system obtained by transporting the bonding maps along stagewise bijections. -/
def transport (F' : ℕ → Type u) (e : ∀ n, S.fibre n ≃ F' n) : InverseSystem.{u} where
  fibre := F'
  bond n y := e n (S.bond n ((e (n + 1)).symm y))

/-- Transport along stagewise bijections preserves the projective limit. -/
def sectionsEquivTransport (F' : ℕ → Type u) (e : ∀ n, S.fibre n ≃ F' n) :
    S.Sections ≃ (S.transport F' e).Sections :=
  S.sectionsEquivOfStageEquiv (S.transport F' e) e fun n y => by
    show e n (S.bond n y) = e n (S.bond n ((e (n + 1)).symm (e (n + 1) y)))
    rw [Equiv.symm_apply_apply]

end InverseSystem

end RenewalGeometry
