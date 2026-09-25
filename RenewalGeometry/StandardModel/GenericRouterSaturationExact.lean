/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.ConnectedRouterExact

/-!
# Generic saturation at fixed multiplicity census

`cor:generic-router-saturation` of the spacetime–gauge duality paper.  Fix the
diagonal minimal projections `p_i = E_ii` on a multiplicity carrier `ℂⁿ`.  In the
affine parameter space `M_n(ℂ)` of internal routers `u`, the routers whose
support graph is **disconnected** are exactly the routers lying in one of the
finitely many **cut spaces**

`cutSpace S = {u | ∀ i ∈ S, ∀ j ∉ S, u i j = 0 ∧ u j i = 0}`, `∅ ≠ S ≠ univ`,

each of which is a proper linear subspace (`cutSpace_ne_top`).  Hence the set of
routers with connected support graph is the complement of a finite union of
proper linear subspaces (`disconnected_eq_iUnion_cutSpace`): it is nonempty
(`exists_connected`) and dense in the entrywise (Euclidean) topology
(`exists_connected_near`); being the complement of a finite union of linear
subspaces it is Zariski open, which is the manuscript's "Zariski open and dense".

The generation statement is then transported through the connected-router
theorem `thm:connected-router` (`C*(𝒟_n, u) = M_n(ℂ) ↔ support graph connected`),
which is proved separately (`RenewalGeometry.StandardModel.ConnectedRouterExact`)
and enters here as an explicit hypothesis `hgen` on the same generating set
`routerGens u = {p_i} ∪ {u, uᴴ}` and the same support graph (`generic_saturation`).
The census `(3,2,1,1)` instance `generic_saturation_census` applies this
independently to the colour carrier `ℂ³` and the weak carrier `ℂ²`: the pairs
`(u, w)` generating `M_3(ℂ) ⊕ M_2(ℂ)` form the complement of a finite union of
proper linear subspaces of `M_3(ℂ) × M_2(ℂ)`, and they are dense.
-/

open Finset Matrix

namespace RenewalGeometry
namespace GenericRouter

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal rank-one projection `p_i = E_ii`. -/
def diagProj (i : n) : Matrix n n ℂ := Matrix.single i i 1

/-- The generating set `𝒟_n ∪ {u, u*}` of `C*(𝒟_n, u)` (as in
`ConnectedRouterExact.routerGens`). -/
def routerGens (u : Matrix n n ℂ) : Set (Matrix n n ℂ) :=
  Set.range diagProj ∪ {u, uᴴ}

/-- The undirected support graph of `u`: an edge `i — j` (for `i ≠ j`) whenever
`u i j ≠ 0` or `u j i ≠ 0` (as in `ConnectedRouterExact.supportGraph`). -/
def supportGraph (u : Matrix n n ℂ) : SimpleGraph n :=
  SimpleGraph.fromRel fun i j => u i j ≠ 0

theorem supportGraph_adj (u : Matrix n n ℂ) (i j : n) :
    (supportGraph u).Adj i j ↔ i ≠ j ∧ (u i j ≠ 0 ∨ u j i ≠ 0) :=
  SimpleGraph.fromRel_adj _ i j

/-- The cut space of a vertex set `S`: routers with no matrix entry across the
partition `S ⊔ Sᶜ` in either direction.  A linear subspace of `M_n(ℂ)`. -/
def cutSpace (S : Set n) : Submodule ℂ (Matrix n n ℂ) where
  carrier := {u | ∀ i ∈ S, ∀ j ∉ S, u i j = 0 ∧ u j i = 0}
  zero_mem' := fun _ _ _ _ => ⟨rfl, rfl⟩
  add_mem' := fun {u v} hu hv i hi j hj => by
    obtain ⟨hu1, hu2⟩ := hu i hi j hj
    obtain ⟨hv1, hv2⟩ := hv i hi j hj
    simp [hu1, hu2, hv1, hv2]
  smul_mem' := fun c {u} hu i hi j hj => by
    obtain ⟨hu1, hu2⟩ := hu i hi j hj
    simp [hu1, hu2]

theorem mem_cutSpace {S : Set n} {u : Matrix n n ℂ} :
    u ∈ cutSpace S ↔ ∀ i ∈ S, ∀ j ∉ S, u i j = 0 ∧ u j i = 0 := Iff.rfl

/-- A cut space of a nontrivial partition is a proper subspace. -/
theorem cutSpace_ne_top {S : Set n} {i j : n} (hi : i ∈ S) (hj : j ∉ S) :
    cutSpace S ≠ ⊤ := by
  intro htop
  have hmem : Matrix.single i j (1 : ℂ) ∈ cutSpace S := htop ▸ Submodule.mem_top
  have := (hmem i hi j hj).1
  rw [Matrix.single_apply_same] at this
  exact one_ne_zero this

/-- Walks of the support graph never leave a set that is closed under adjacency. -/
theorem mem_of_walk {u : Matrix n n ℂ} {S : Set n}
    (hS : ∀ a ∈ S, ∀ b, (supportGraph u).Adj a b → b ∈ S) {i k : n}
    (p : (supportGraph u).Walk i k) (hi : i ∈ S) : k ∈ S := by
  induction p with
  | nil => exact hi
  | cons h _ ih => exact ih (hS _ hi _ h)

/-- A router in a nontrivial cut space has a disconnected support graph. -/
theorem not_connected_of_mem_cutSpace {u : Matrix n n ℂ} {S : Set n} {i j : n}
    (hi : i ∈ S) (hj : j ∉ S) (hu : u ∈ cutSpace S) :
    ¬ (supportGraph u).Connected := by
  intro hconn
  have hS : ∀ a ∈ S, ∀ b, (supportGraph u).Adj a b → b ∈ S := by
    intro a ha b hab
    by_contra hb
    obtain ⟨h1, h2⟩ := hu a ha b hb
    rw [supportGraph_adj] at hab
    rcases hab.2 with h | h
    · exact h h1
    · exact h h2
  obtain ⟨p⟩ := hconn.preconnected i j
  exact hj (mem_of_walk hS p hi)

/-- A disconnected support graph puts the router in a nontrivial cut space
(the reachability set of any vertex). -/
theorem exists_cutSpace_of_not_connected [Nonempty n] {u : Matrix n n ℂ}
    (h : ¬ (supportGraph u).Connected) :
    ∃ S : Set n, S.Nonempty ∧ Sᶜ.Nonempty ∧ u ∈ cutSpace S := by
  obtain ⟨v₀⟩ := ‹Nonempty n›
  set S : Set n := {i | (supportGraph u).Reachable v₀ i} with hSdef
  refine ⟨S, ⟨v₀, SimpleGraph.Reachable.refl v₀⟩, ?_, ?_⟩
  · by_contra hc
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hc
    apply h
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ S := hc ▸ Set.mem_univ a
    have hb : b ∈ S := hc ▸ Set.mem_univ b
    exact (show (supportGraph u).Reachable v₀ a from ha).symm.trans hb
  · intro i hi j hj
    have hadj : ¬ (supportGraph u).Adj i j := fun hij =>
      hj ((show (supportGraph u).Reachable v₀ i from hi).trans hij.reachable)
    simp only [supportGraph_adj, not_and_or, not_or, not_not, ne_eq] at hadj
    rcases hadj with hne | h2
    · exact absurd (hne ▸ hi) hj
    · exact h2

/-- The index set of nontrivial partitions (finite). -/
abbrev Cut (n : Type*) := {S : Set n // S.Nonempty ∧ Sᶜ.Nonempty}

instance : Finite (Cut n) := Subtype.finite

/-- Every cut space over a nontrivial partition is proper. -/
theorem cutSpace_cut_ne_top (S : Cut n) : cutSpace S.1 ≠ ⊤ := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := S.2
  exact cutSpace_ne_top hi hj

/-- **The disconnected locus is a finite union of proper linear subspaces**: the
routers with disconnected support graph are exactly the union of the cut spaces
over nontrivial partitions. -/
theorem disconnected_eq_iUnion_cutSpace [Nonempty n] :
    {u : Matrix n n ℂ | ¬ (supportGraph u).Connected} =
      ⋃ S : Cut n, (cutSpace S.1 : Set (Matrix n n ℂ)) := by
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · intro h
    obtain ⟨S, hS1, hS2, hu⟩ := exists_cutSpace_of_not_connected h
    exact ⟨⟨S, hS1, hS2⟩, hu⟩
  · rintro ⟨⟨S, ⟨i, hi⟩, ⟨j, hj⟩⟩, hu⟩
    exact not_connected_of_mem_cutSpace hi hj hu

/-- The connected locus is nonempty: a finite union of proper subspaces over the
infinite field `ℂ` is not everything. -/
theorem exists_connected [Nonempty n] :
    ∃ u : Matrix n n ℂ, (supportGraph u).Connected := by
  obtain ⟨u, hu⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun S : Cut n => cutSpace S.1) cutSpace_cut_ne_top
  refine ⟨u, ?_⟩
  by_contra h
  obtain ⟨S, hS1, hS2, hmem⟩ := exists_cutSpace_of_not_connected h
  exact hu ⟨S, hS1, hS2⟩ hmem

/-- The connected locus is dense: every router is entrywise within `ε` of a
router with connected (indeed complete) support graph. -/
theorem exists_connected_near [Nonempty n] (u : Matrix n n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u' : Matrix n n ℂ, (∀ i j, ‖u' i j - u i j‖ < ε) ∧ (supportGraph u').Connected := by
  -- choose a real shift `t ∈ (0, ε)` avoiding the finitely many values `-u i j`
  have hinf : (Set.Ioo (0 : ℝ) ε).Infinite := Set.Ioo_infinite hε
  obtain ⟨t, ht, htn⟩ := hinf.exists_notMem_finset
    (Finset.univ.image fun p : n × n => (-(u p.1 p.2)).re)
  have htne : ∀ i j, (t : ℂ) ≠ -(u i j) := by
    intro i j hc
    apply htn
    rw [Finset.mem_image]
    exact ⟨(i, j), Finset.mem_univ _, by rw [← hc, Complex.ofReal_re]⟩
  refine ⟨u + (t : ℂ) • Matrix.of (fun _ _ => (1 : ℂ)), ?_, ?_⟩
  · intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one,
      add_sub_cancel_left, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_pos ht.1]
    exact ht.2
  · refine ⟨fun a b => ?_⟩
    by_cases hab : a = b
    · exact hab ▸ SimpleGraph.Reachable.refl a
    · refine SimpleGraph.Adj.reachable ?_
      rw [supportGraph_adj]
      refine ⟨hab, Or.inl ?_⟩
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one]
      intro hc
      exact htne a b (by rw [← sub_eq_zero]; rw [add_comm] at hc; rwa [sub_neg_eq_add])

/-- **`cor:generic-router-saturation`, general carrier `ℂⁿ`.**  Given the
connected-router theorem (`hgen`, `thm:connected-router`), the routers `u` that
generate `M_n(ℂ)` together with the diagonal projections form the complement of
the finite union of the proper linear cut spaces (Zariski open), and this locus is
nonempty and entrywise dense. -/
theorem generic_saturation [Nonempty n]
    (hgen : ∀ u : Matrix n n ℂ,
      Algebra.adjoin ℂ (routerGens u) = ⊤ ↔ (supportGraph u).Connected) :
    {u : Matrix n n ℂ | Algebra.adjoin ℂ (routerGens u) = ⊤}ᶜ =
        ⋃ S : Cut n, (cutSpace S.1 : Set (Matrix n n ℂ)) ∧
      (∀ S : Cut n, cutSpace S.1 ≠ ⊤) ∧
      (∃ u : Matrix n n ℂ, Algebra.adjoin ℂ (routerGens u) = ⊤) ∧
      (∀ u : Matrix n n ℂ, ∀ ε : ℝ, 0 < ε → ∃ u' : Matrix n n ℂ,
        (∀ i j, ‖u' i j - u i j‖ < ε) ∧ Algebra.adjoin ℂ (routerGens u') = ⊤) := by
  refine ⟨?_, cutSpace_cut_ne_top, ?_, ?_⟩
  · rw [← disconnected_eq_iUnion_cutSpace]
    ext u
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hgen]
  · obtain ⟨u, hu⟩ := exists_connected (n := n)
    exact ⟨u, (hgen u).mpr hu⟩
  · intro u ε hε
    obtain ⟨u', h1, h2⟩ := exists_connected_near u hε
    exact ⟨u', h1, (hgen u').mpr h2⟩

/-- The cut spaces of the product parameter space `M_3(ℂ) × M_2(ℂ)`: a cut on the
colour carrier or a cut on the weak carrier. -/
def censusCutSpace : Cut (Fin 3) ⊕ Cut (Fin 2) →
    Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ)
  | Sum.inl S => (cutSpace S.1).prod ⊤
  | Sum.inr S => (⊤ : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)).prod (cutSpace S.1)

theorem censusCutSpace_ne_top (S : Cut (Fin 3) ⊕ Cut (Fin 2)) : censusCutSpace S ≠ ⊤ := by
  rcases S with S | S
  · intro h
    apply cutSpace_cut_ne_top S
    rw [eq_top_iff]
    intro u _
    have : (u, (0 : Matrix (Fin 2) (Fin 2) ℂ)) ∈ censusCutSpace (Sum.inl S) := by
      rw [h]; exact Submodule.mem_top
    change (u, (0 : Matrix (Fin 2) (Fin 2) ℂ)) ∈ (cutSpace S.1).prod ⊤ at this
    exact (Submodule.mem_prod.mp this).1
  · intro h
    apply cutSpace_cut_ne_top S
    rw [eq_top_iff]
    intro w _
    have : ((0 : Matrix (Fin 3) (Fin 3) ℂ), w) ∈ censusCutSpace (Sum.inr S) := by
      rw [h]; exact Submodule.mem_top
    change ((0 : Matrix (Fin 3) (Fin 3) ℂ), w) ∈
      (⊤ : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)).prod (cutSpace S.1) at this
    exact (Submodule.mem_prod.mp this).2

/-- **`cor:generic-router-saturation` at the census `(3,2,1,1)`.**  Given the
connected-router theorem on both carriers, the router pairs `(u, w)` generating
`M_3(ℂ) ⊕ M_2(ℂ)` (each factor generated by its diagonal projections and its
router) form the complement of a finite union of proper linear subspaces of
`M_3(ℂ) × M_2(ℂ)`, and are entrywise dense. -/
theorem generic_saturation_census
    (hgen3 : ∀ u : Matrix (Fin 3) (Fin 3) ℂ,
      Algebra.adjoin ℂ (routerGens u) = ⊤ ↔ (supportGraph u).Connected)
    (hgen2 : ∀ w : Matrix (Fin 2) (Fin 2) ℂ,
      Algebra.adjoin ℂ (routerGens w) = ⊤ ↔ (supportGraph w).Connected) :
    {p : Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ |
        Algebra.adjoin ℂ (routerGens p.1) = ⊤ ∧ Algebra.adjoin ℂ (routerGens p.2) = ⊤}ᶜ =
        ⋃ S, (censusCutSpace S : Set (Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ)) ∧
      (∀ S, censusCutSpace S ≠ ⊤) ∧
      (∀ (u : Matrix (Fin 3) (Fin 3) ℂ) (w : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ), 0 < ε →
        ∃ (u' : Matrix (Fin 3) (Fin 3) ℂ) (w' : Matrix (Fin 2) (Fin 2) ℂ),
          (∀ i j, ‖u' i j - u i j‖ < ε) ∧ (∀ i j, ‖w' i j - w i j‖ < ε) ∧
          Algebra.adjoin ℂ (routerGens u') = ⊤ ∧ Algebra.adjoin ℂ (routerGens w') = ⊤) := by
  refine ⟨?_, censusCutSpace_ne_top, ?_⟩
  · ext ⟨u, w⟩
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, SetLike.mem_coe, hgen3,
      hgen2, not_and_or]
    have h3 := congrArg (fun T => u ∈ T) (disconnected_eq_iUnion_cutSpace (n := Fin 3))
    have h2 := congrArg (fun T => w ∈ T) (disconnected_eq_iUnion_cutSpace (n := Fin 2))
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, SetLike.mem_coe, eq_iff_iff] at h3 h2
    constructor
    · rintro (h | h)
      · obtain ⟨S, hS⟩ := h3.mp h
        exact ⟨Sum.inl S, Submodule.mem_prod.mpr ⟨hS, Submodule.mem_top⟩⟩
      · obtain ⟨S, hS⟩ := h2.mp h
        exact ⟨Sum.inr S, Submodule.mem_prod.mpr ⟨Submodule.mem_top, hS⟩⟩
    · rintro ⟨S | S, hS⟩
      · exact Or.inl (h3.mpr ⟨S, (Submodule.mem_prod.mp hS).1⟩)
      · exact Or.inr (h2.mpr ⟨S, (Submodule.mem_prod.mp hS).2⟩)
  · intro u w ε hε
    obtain ⟨u', hu1, hu2⟩ := exists_connected_near u hε
    obtain ⟨w', hw1, hw2⟩ := exists_connected_near w hε
    exact ⟨u', w', hu1, hw1, (hgen3 u').mpr hu2, (hgen2 w').mpr hw2⟩


/-! ### Discharging the connected-router hypothesis

`thm:connected-router` is proved in `RenewalGeometry.StandardModel.ConnectedRouterExact`
with the same generating set and the same support graph; the following wrappers make
`cor:generic-router-saturation` unconditional. -/

/-- The generating set of this file is the one of `ConnectedRouterExact`. -/
theorem routerGens_eq_connectedRouter (u : Matrix n n ℂ) :
    routerGens u = ConnectedRouter.routerGens u := rfl

/-- The support graph of this file is the one of `ConnectedRouterExact`. -/
theorem supportGraph_eq_connectedRouter (u : Matrix n n ℂ) :
    supportGraph u = ConnectedRouter.supportGraph u := rfl

/-- **`thm:connected-router`** in the vocabulary of this file (discharged from
`ConnectedRouter.adjoin_eq_top_iff_connected`). -/
theorem adjoin_eq_top_iff_connected [Nonempty n] (u : Matrix n n ℂ) :
    Algebra.adjoin ℂ (routerGens u) = ⊤ ↔ (supportGraph u).Connected :=
  ConnectedRouter.adjoin_eq_top_iff_connected u

/-- **`cor:generic-router-saturation`, general carrier `ℂⁿ`, unconditional.**  The
routers `u` generating `M_n(ℂ)` together with the diagonal projections form the
complement of the finite union of the proper linear cut spaces (Zariski open), and this
locus is nonempty and entrywise dense. -/
theorem generic_saturation_unconditional [Nonempty n] :
    {u : Matrix n n ℂ | Algebra.adjoin ℂ (routerGens u) = ⊤}ᶜ =
        ⋃ S : Cut n, (cutSpace S.1 : Set (Matrix n n ℂ)) ∧
      (∀ S : Cut n, cutSpace S.1 ≠ ⊤) ∧
      (∃ u : Matrix n n ℂ, Algebra.adjoin ℂ (routerGens u) = ⊤) ∧
      (∀ u : Matrix n n ℂ, ∀ ε : ℝ, 0 < ε → ∃ u' : Matrix n n ℂ,
        (∀ i j, ‖u' i j - u i j‖ < ε) ∧ Algebra.adjoin ℂ (routerGens u') = ⊤) :=
  generic_saturation adjoin_eq_top_iff_connected

/-- **`cor:generic-router-saturation` at the census `(3,2,1,1)`, unconditional.** -/
theorem generic_saturation_census_unconditional :
    {p : Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ |
        Algebra.adjoin ℂ (routerGens p.1) = ⊤ ∧ Algebra.adjoin ℂ (routerGens p.2) = ⊤}ᶜ =
        ⋃ S, (censusCutSpace S : Set (Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ)) ∧
      (∀ S, censusCutSpace S ≠ ⊤) ∧
      (∀ (u : Matrix (Fin 3) (Fin 3) ℂ) (w : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ), 0 < ε →
        ∃ (u' : Matrix (Fin 3) (Fin 3) ℂ) (w' : Matrix (Fin 2) (Fin 2) ℂ),
          (∀ i j, ‖u' i j - u i j‖ < ε) ∧ (∀ i j, ‖w' i j - w i j‖ < ε) ∧
          Algebra.adjoin ℂ (routerGens u') = ⊤ ∧ Algebra.adjoin ℂ (routerGens w') = ⊤) :=
  generic_saturation_census adjoin_eq_top_iff_connected adjoin_eq_top_iff_connected

end GenericRouter
end RenewalGeometry
