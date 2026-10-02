/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Topology.FiniteInverseSystemStableImage

/-!
# Canonical pruning of compact inverse systems and compactness of the projective limit

This file completes the abstract inverse-system shell of `lem:supp-fibre-pruning` and of the
compactness clause of `thm:supp-semifinite-exhaustion` (`predictive_spectral_geometry`).
For an `ℕ`-indexed inverse system `S` (`InverseSystem`):

* `iterBond k n : F (n + k) → F n` is the composite restriction map `r_{n+k,n}`; its range is
  the `k`-step image (`range_iterBond`), so the stable image is the paper's
  `F_n^∞ = ⋂_{m ≥ n} r_{m,n}(F_m)` (`stableImage_eq_iInter_range_iterBond`);
* `subset_stableImage_of_subset_image` (**maximality**): every subsystem `T` in which every
  point extends one step inside `T` (hence indefinitely) lies in the stable images, and the
  stable images form such a subsystem as soon as the bonds map them onto each other;
* `HasStableLifts` (the bonding maps send stable images onto stable images; true for compact
  Hausdorff fibres and continuous bonds, `hasStableLifts_of_compact`) implies that every point
  of a stable image lies on a thread (`exists_sections_apply_eq`), so the stable image is
  **exactly the level-`n` projection of the projective limit** (`range_sections_apply`);
* `image_bond_stableImage`: `r_{n+1,n}(F_{n+1}^∞) = F_n^∞`;
* `fibre_pruning`: the packaged lemma (nonempty, compact, stable surjectivity, projection,
  maximality);
* the projective limit `Sections` carries the subspace topology of the product
  (`instTopologicalSpaceSections`); for compact Hausdorff fibres and continuous bonds it is
  compact Hausdorff (`compactSpace_sections`, `t2Space_sections`) and nonempty when the fibres
  are (`nonempty_sections_of_compact`).
-/

set_option linter.unusedSectionVars false

namespace RenewalGeometry

open Set

universe u

namespace InverseSystem

variable (S : InverseSystem.{u})

/-! ### Composite restriction maps -/

/-- The composite restriction map `r_{n+k,n} : F (n+k) → F n`. -/
def iterBond : ∀ k n, S.fibre (n + k) → S.fibre n
  | 0, _ => id
  | k + 1, n => fun y => iterBond k n (S.bond (n + k) y)

@[simp] theorem iterBond_zero (n : ℕ) (y : S.fibre n) : S.iterBond 0 n y = y := rfl

theorem iterBond_succ (k n : ℕ) (y : S.fibre (n + (k + 1))) :
    S.iterBond (k + 1) n y = S.iterBond k n (S.bond (n + k) y) := rfl

theorem iterBond_one (n : ℕ) (y : S.fibre (n + 1)) : S.iterBond 1 n y = S.bond n y := rfl

/-- Bonding maps commute with the transport of fibres along an index equality. -/
theorem bond_cast {a b : ℕ} (h : a = b) (y : S.fibre (a + 1)) :
    S.bond b (cast (congrArg S.fibre (congrArg (· + 1) h)) y) =
      cast (congrArg S.fibre h) (S.bond a y) := by
  subst h; rfl

/-- Transitivity of the composite restriction maps: `r_{n+j+k, n} = r_{n+j, n} ∘ r_{n+j+k, n+j}`
(stated with the definitional index `n + (j + k)` replaced by `(n + j) + k`). -/
theorem iterBond_add (j : ℕ) : ∀ (k n : ℕ) (y : S.fibre (n + j + k)),
    S.iterBond (j + k) n (cast (congrArg S.fibre (Nat.add_assoc n j k)) y) =
      S.iterBond j n (S.iterBond k (n + j) y)
  | 0, n, y => rfl
  | k + 1, n, y => by
    rw [S.iterBond_succ k (n + j) y, ← iterBond_add j k n (S.bond (n + j + k) y),
      ← S.bond_cast (Nat.add_assoc n j k)]
    rfl

/-- The image of the `j`-step image at stage `n + k` under `r_{n+k,n}` is the `(j+k)`-step
image at stage `n`. -/
theorem image_iterBond_extendable (j : ℕ) : ∀ k n,
    S.iterBond k n '' S.extendable j (n + k) = S.extendable (j + k) n
  | 0, n => by simp [iterBond]
  | k + 1, n => by
    have h1 : S.iterBond (k + 1) n '' S.extendable j (n + (k + 1)) =
        S.iterBond k n '' (S.bond (n + k) '' S.extendable j (n + k + 1)) := by
      rw [image_image]; rfl
    rw [h1, ← extendable_succ, image_iterBond_extendable (j + 1) k n]
    congr 1
    omega

/-- The range of `r_{n+k,n}` is the `k`-step image `extendable k n`. -/
theorem range_iterBond (k n : ℕ) : range (S.iterBond k n) = S.extendable k n := by
  rw [← image_univ, ← extendable_zero, image_iterBond_extendable, zero_add]

/-- The stable image is the paper's `F_n^∞ = ⋂_{m ≥ n} r_{m,n}(F_m)` (with `m = n + k`). -/
theorem stableImage_eq_iInter_range_iterBond (n : ℕ) :
    S.stableImage n = ⋂ k, range (S.iterBond k n) := by
  simp only [range_iterBond]
  rfl

/-! ### Maximality -/

/-- **Maximality of the stable images**: if a subsystem `T` has the property that every point
of `T n` extends one step inside `T` (hence indefinitely), then `T n ⊆ F_n^∞`. -/
theorem subset_stableImage_of_subset_image (T : ∀ n, Set (S.fibre n))
    (hT : ∀ n, T n ⊆ S.bond n '' T (n + 1)) (n : ℕ) : T n ⊆ S.stableImage n := by
  have key : ∀ k n, T n ⊆ S.extendable k n := by
    intro k
    induction k with
    | zero => intro n; exact subset_univ _
    | succ k ih =>
      intro n y hy
      obtain ⟨z, hz, rfl⟩ := hT n hy
      rw [extendable_succ]
      exact ⟨z, ih (n + 1) hz, rfl⟩
  intro y hy
  rw [mem_stableImage_iff]
  exact fun k => key k n hy

/-! ### Stable lifts and threads through stable points -/

/-- The bonding maps send stable images *onto* stable images. -/
def HasStableLifts : Prop :=
  ∀ n (e : S.fibre n), e ∈ S.stableImage n → ∃ y ∈ S.stableImage (n + 1), S.bond n y = e

/-- For compact Hausdorff fibres and continuous bonds the stable lifting property holds
(Mittag-Leffler, `exists_mem_stableImage_bond_eq`). -/
theorem hasStableLifts_of_compact [∀ n, TopologicalSpace (S.fibre n)]
    [∀ n, CompactSpace (S.fibre n)] [∀ n, T2Space (S.fibre n)]
    (hcont : ∀ n, Continuous (S.bond n)) : S.HasStableLifts :=
  fun n _ he => S.exists_mem_stableImage_bond_eq hcont n he

/-- The bonding maps send stable images onto stable images:
`r_{n+1,n}(F_{n+1}^∞) = F_n^∞` (`eq:supp-stable-surjectivity`). -/
theorem image_bond_stableImage (hS : S.HasStableLifts) (n : ℕ) :
    S.bond n '' S.stableImage (n + 1) = S.stableImage n := by
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact S.bond_mem_stableImage n hy
  · intro e he
    obtain ⟨y, hy, rfl⟩ := hS n e he
    exact ⟨y, hy, rfl⟩

/-- A thread through the stable images starting at a prescribed stable point of stage `0`. -/
noncomputable def liftThread (hS : S.HasStableLifts) (e : S.fibre 0) (he : e ∈ S.stableImage 0) :
    ∀ n, {y : S.fibre n // y ∈ S.stableImage n}
  | 0 => ⟨e, he⟩
  | n + 1 => ⟨(hS n _ (liftThread hS e he n).2).choose,
      (hS n _ (liftThread hS e he n).2).choose_spec.1⟩

theorem bond_liftThread (hS : S.HasStableLifts) (e : S.fibre 0) (he : e ∈ S.stableImage 0)
    (n : ℕ) : S.bond n (S.liftThread hS e he (n + 1)).1 = (S.liftThread hS e he n).1 := by
  simp only [liftThread]
  exact (hS n _ (S.liftThread hS e he n).2).choose_spec.2

/-- The shifted system `n ↦ F (n+1)`. -/
def shift : InverseSystem.{u} where
  fibre n := S.fibre (n + 1)
  bond n := S.bond (n + 1)

theorem shift_extendable (k : ℕ) : ∀ n, S.shift.extendable k n = S.extendable k (n + 1) := by
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    rw [extendable_succ, extendable_succ, ih (n + 1)]
    rfl

theorem shift_stableImage (n : ℕ) : S.shift.stableImage n = S.stableImage (n + 1) := by
  simp only [stableImage, shift_extendable]
  rfl

theorem HasStableLifts.shift {S : InverseSystem.{u}} (hS : S.HasStableLifts) :
    S.shift.HasStableLifts := by
  intro n e he
  rw [shift_stableImage] at he
  obtain ⟨y, hy, hye⟩ := hS (n + 1) e he
  exact ⟨y, by rw [shift_stableImage]; exact hy, hye⟩

/-- **Every stable point lies on a thread**: under the stable lifting property, for every
`e ∈ F_n^∞` there is a compatible thread `x` with `x n = e`. -/
theorem exists_sections_apply_eq (n : ℕ) :
    ∀ (S : InverseSystem.{u}), S.HasStableLifts →
      ∀ e ∈ S.stableImage n, ∃ x : S.Sections, x.1 n = e := by
  induction n with
  | zero =>
    intro S hS e he
    exact ⟨⟨fun m => (S.liftThread hS e he m).1, S.bond_liftThread hS e he⟩, rfl⟩
  | succ n ih =>
    intro S hS e he
    have he' : e ∈ S.shift.stableImage n := by rw [shift_stableImage]; exact he
    obtain ⟨x', hx'⟩ := ih S.shift hS.shift e he'
    let x : ∀ m, S.fibre m := fun m =>
      match m with
      | 0 => S.bond 0 (x'.1 0)
      | m + 1 => x'.1 m
    refine ⟨⟨x, ?_⟩, hx'⟩
    intro m
    cases m with
    | zero => rfl
    | succ m => exact x'.2 m

/-- **`F_n^∞` is exactly the level-`n` projection of the projective limit** (under the stable
lifting property). -/
theorem range_sections_apply (hS : S.HasStableLifts) (n : ℕ) :
    range (fun x : S.Sections => x.1 n) = S.stableImage n := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact S.mem_stableImage_of_sections x n
  · intro e he
    obtain ⟨x, hx⟩ := exists_sections_apply_eq n S hS e he
    exact ⟨x, hx⟩

/-- The stable images form a subsystem in which every point extends one step (under the stable
lifting property); combined with `subset_stableImage_of_subset_image` they are the largest
such subsystem. -/
theorem stableImage_subset_image_bond (hS : S.HasStableLifts) (n : ℕ) :
    S.stableImage n ⊆ S.bond n '' S.stableImage (n + 1) :=
  (S.image_bond_stableImage hS n).ge

/-! ### Topology on the projective limit -/

section Topology

variable [∀ n, TopologicalSpace (S.fibre n)]

/-- The projective limit carries the subspace topology of the product `Π_n F_n`. -/
instance instTopologicalSpaceSections : TopologicalSpace S.Sections :=
  instTopologicalSpaceSubtype

theorem continuous_sections_val : Continuous (fun x : S.Sections => x.1) :=
  continuous_subtype_val

theorem continuous_sections_apply (n : ℕ) : Continuous (fun x : S.Sections => x.1 n) :=
  (continuous_apply n).comp continuous_subtype_val

theorem isEmbedding_sections_val : Topology.IsEmbedding (fun x : S.Sections => x.1) :=
  Topology.IsEmbedding.subtypeVal

instance t2Space_sections [∀ n, T2Space (S.fibre n)] : T2Space S.Sections :=
  inferInstanceAs (T2Space {x : ∀ n, S.fibre n // ∀ n, S.bond n (x (n + 1)) = x n})

/-- The set of compatible threads is closed in the product. -/
theorem isClosed_setOf_compatible [∀ n, T2Space (S.fibre n)] (hcont : ∀ n, Continuous (S.bond n)) :
    IsClosed {x : ∀ n, S.fibre n | ∀ n, S.bond n (x (n + 1)) = x n} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun n =>
    isClosed_eq ((hcont n).comp (continuous_apply (n + 1))) (continuous_apply n)

/-- **Compactness of the projective limit**: for compact Hausdorff fibres and continuous bonds
the projective limit is compact (closed in the Tychonoff product). -/
theorem compactSpace_sections [∀ n, CompactSpace (S.fibre n)] [∀ n, T2Space (S.fibre n)]
    (hcont : ∀ n, Continuous (S.bond n)) : CompactSpace S.Sections := by
  have hc : IsCompact {x : ∀ n, S.fibre n | ∀ n, S.bond n (x (n + 1)) = x n} :=
    (S.isClosed_setOf_compatible hcont).isCompact
  exact isCompact_iff_compactSpace.mp hc

/-- For nonempty compact Hausdorff fibres and continuous bonds the projective limit is
nonempty. -/
theorem nonempty_sections_of_compact [∀ n, CompactSpace (S.fibre n)] [∀ n, T2Space (S.fibre n)]
    (hcont : ∀ n, Continuous (S.bond n)) (hne : ∀ n, Nonempty (S.fibre n)) :
    Nonempty S.Sections :=
  (S.nonempty_sections_iff_fibre hcont).mpr hne

/-- The thread-set topology of the stable-image system agrees with that of the original
system: the canonical bijection `sectionsEquivStable` is a homeomorphism when the stable
images carry the subspace topology. -/
noncomputable def sectionsHomeomorphStable :
    @Homeomorph S.Sections S.stableSystem.Sections _
      (@instTopologicalSpaceSections S.stableSystem
        (fun n => (inferInstance : TopologicalSpace (S.stableImage n)))) := by
  letI : ∀ n, TopologicalSpace (S.stableSystem.fibre n) :=
    fun n => (inferInstance : TopologicalSpace (S.stableImage n))
  exact
  { toEquiv := S.sectionsEquivStable
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_pi fun n =>
        (S.continuous_sections_apply n).subtype_mk _
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact continuous_pi fun n =>
        continuous_subtype_val.comp (S.stableSystem.continuous_sections_apply n) }

end Topology

/-! ### The packaged pruning lemma -/

/-- **`lem:supp-fibre-pruning` (Canonical pruning of compact finite-stage fibres).**  For an
`ℕ`-inverse system of nonempty compact Hausdorff fibres with continuous bonding maps, every
stable image `F_n^∞ = ⋂_{m ≥ n} r_{m,n}(F_m)` is nonempty and compact,
`r_{n+1,n}(F_{n+1}^∞) = F_n^∞`, `F_n^∞` is exactly the level-`n` projection of the
projective limit, and it is the largest subsystem in which every point extends (one step,
hence indefinitely) within the subsystem. -/
theorem fibre_pruning [∀ n, TopologicalSpace (S.fibre n)] [∀ n, CompactSpace (S.fibre n)]
    [∀ n, T2Space (S.fibre n)] (hcont : ∀ n, Continuous (S.bond n))
    (hne : ∀ n, Nonempty (S.fibre n)) :
    (∀ n, S.stableImage n = ⋂ k, range (S.iterBond k n)) ∧
    (∀ n, (S.stableImage n).Nonempty ∧ IsCompact (S.stableImage n)) ∧
    (∀ n, S.bond n '' S.stableImage (n + 1) = S.stableImage n) ∧
    (∀ n, range (fun x : S.Sections => x.1 n) = S.stableImage n) ∧
    (∀ n, S.stableImage n ⊆ S.bond n '' S.stableImage (n + 1)) ∧
    (∀ T : ∀ n, Set (S.fibre n), (∀ n, T n ⊆ S.bond n '' T (n + 1)) →
      ∀ n, T n ⊆ S.stableImage n) := by
  have hS := S.hasStableLifts_of_compact hcont
  exact ⟨S.stableImage_eq_iInter_range_iterBond,
    fun n => ⟨S.stableImage_nonempty hcont hne n, (S.isClosed_stableImage hcont n).isCompact⟩,
    S.image_bond_stableImage hS, S.range_sections_apply hS,
    S.stableImage_subset_image_bond hS, S.subset_stableImage_of_subset_image⟩

end InverseSystem

/-- Non-vacuity witness for `InverseSystem.fibre_pruning`: the constant system of unit
intervals with identity bonds satisfies all hypotheses. -/
example : True := by
  let S : InverseSystem.{0} := ⟨fun _ => unitInterval, fun _ => id⟩
  have : ∀ n, CompactSpace (S.fibre n) := fun _ => inferInstanceAs (CompactSpace unitInterval)
  have := S.fibre_pruning (fun _ => continuous_id) (fun _ => ⟨(0 : unitInterval)⟩)
  trivial

end RenewalGeometry
