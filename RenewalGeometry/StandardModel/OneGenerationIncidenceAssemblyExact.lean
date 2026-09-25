/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Incidence reduces the one-generation commutant

`prop:one-gen-incidence` of the spacetime–gauge duality paper.

## General engine

A finite carrier `n` is partitioned into **sectors** by `β : n → B` (the irreducible,
pairwise inequivalent gauge modules), so the gauge-generated algebra is the algebra
spanned by the matrix units `E_ij` with `β i = β j` (`gaugeUnits β`, encoding
`𝒜_gauge = ⊕_b M_{|b|}(ℂ)`).  An incidence bank is a family of matrices `Y e`
(`incidenceGens β Y = gaugeUnits β ∪ {Y_e} ∪ {Y_e^*}`).  The **support graph** on the
carrier joins two vertices when they lie in one sector or some `Y e` has a nonzero
entry between them (`supportGraph β Y`):

* `single_mem_of_reachable`: products along walks give every matrix unit between
  vertices of one connected component (this is the paper's proof: a nonzero block
  between two full matrix summands plus endpoint matrix units generates every
  rank-one map between the summands);
* `adjoin_eq_labelAlgebra`: if a labelling `κ : n → C` is constant on sectors and on
  incidence supports, and vertices with equal label are reachable, then the generated
  algebra is exactly the block algebra `labelAlgebra κ = ⊕_c M_{|κ⁻¹ c|}(ℂ)`;
* `mem_centralizer_labelAlgebra_iff`, `finrank_centralizer_labelAlgebra`: the
  commutant of a block algebra is `{diag(a_c · 1)} ≅ ℂ^{|C|}`;
* `reachable_of_patternGraph`: reachability in the carrier follows from
  reachability in the **sector pattern graph** whose edges are the incidence pairs
  `edge e = (b, b')`, provided each `Y e` is supported on `b × b'` and nonzero
  (`adjoin_eq_labelAlgebra_of_pattern`).

## The one-generation packet

On `𝓕₁₅ = Q ⊕ u ⊕ d ⊕ L ⊕ e` (`Fin 15` with `sector15`, dimensions `6,3,3,2,1`) and the
three nonzero Higgs-contracted incidence histories `Q ↔ u`, `Q ↔ d`, `L ↔ e`:

* `one_gen_incidence`: `𝒜_gauge+inc = M₁₂(ℂ) ⊕ M₃(ℂ)` (the block algebra of the
  quark/lepton labelling, whose fibres have `12` and `3` elements), and its commutant
  is `{diag(a·1₁₂, b·1₃)} ≅ ℂ²`;
* `one_gen_incidence_neutral`: with a neutral singlet `ν` and a nonzero `L ↔ ν`
  incidence (`Fin 16`, `sector16`), the second block becomes `M₄(ℂ)` and the commutant
  stays `ℂ²`.

The incidence matrices are encoded as full `n × n` matrices supported on the
respective sector blocks (`Y e i j ≠ 0 → β i = (edge e).1 ∧ β j = (edge e).2`).
-/

open Finset Matrix

namespace RenewalGeometry
namespace IncidenceAssembly

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Block algebras of a labelling -/

/-- The block algebra `⊕_c M_{κ⁻¹ c}(ℂ)` of a labelling `κ : n → C`: matrices vanishing
between vertices with different labels. -/
def labelAlgebra {C : Type*} (κ : n → C) : Subalgebra ℂ (Matrix n n ℂ) where
  carrier := {X | ∀ i j, κ i ≠ κ j → X i j = 0}
  zero_mem' := fun _ _ _ => rfl
  one_mem' := fun i j hij => by
    rw [Matrix.one_apply_ne]
    rintro rfl
    exact hij rfl
  add_mem' := fun {X Y} hX hY i j hij => by
    rw [Matrix.add_apply, hX i j hij, hY i j hij, add_zero]
  mul_mem' := fun {X Y} hX hY i j hij => by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : κ i = κ m
    · rw [hY m j (fun hc => hij (hm.trans hc)), mul_zero]
    · rw [hX i m hm, zero_mul]
  algebraMap_mem' := fun c i j hij => by
    rw [Matrix.algebraMap_matrix_apply, if_neg]
    rintro rfl
    exact hij rfl

theorem mem_labelAlgebra {C : Type*} {κ : n → C} {X : Matrix n n ℂ} :
    X ∈ labelAlgebra κ ↔ ∀ i j, κ i ≠ κ j → X i j = 0 :=
  Iff.rfl

theorem single_mem_labelAlgebra {C : Type*} {κ : n → C} {i j : n} (h : κ i = κ j) (c : ℂ) :
    Matrix.single i j c ∈ labelAlgebra κ := by
  intro a b hab
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hab h

/-! ### Gauge units, incidence generators and the support graph -/

variable {B ι : Type*}

/-- The gauge matrix units: `E_ij` with `i, j` in one sector. -/
def gaugeUnits (β : n → B) : Set (Matrix n n ℂ) :=
  {X | ∃ i j : n, β i = β j ∧ X = Matrix.single i j 1}

/-- The generating set `𝒜_gauge ∪ {Y_e, Y_e^*}`. -/
def incidenceGens (β : n → B) (Y : ι → Matrix n n ℂ) : Set (Matrix n n ℂ) :=
  gaugeUnits β ∪ Set.range Y ∪ Set.range fun e => (Y e)ᴴ

/-- The support graph on the carrier: `i — j` when `i ≠ j` and either they share a
sector or some incidence has a nonzero entry between them. -/
def supportGraph (β : n → B) (Y : ι → Matrix n n ℂ) : SimpleGraph n :=
  SimpleGraph.fromRel fun i j => β i = β j ∨ ∃ e, Y e i j ≠ 0

theorem supportGraph_adj (β : n → B) (Y : ι → Matrix n n ℂ) (i j : n) :
    (supportGraph β Y).Adj i j ↔
      i ≠ j ∧ ((β i = β j ∨ ∃ e, Y e i j ≠ 0) ∨ (β j = β i ∨ ∃ e, Y e j i ≠ 0)) :=
  SimpleGraph.fromRel_adj _ i j

theorem gaugeUnit_mem {β : n → B} {Y : ι → Matrix n n ℂ} {A : Subalgebra ℂ (Matrix n n ℂ)}
    (hA : incidenceGens β Y ⊆ A) {i j : n} (h : β i = β j) :
    Matrix.single i j (1 : ℂ) ∈ A :=
  hA (Set.mem_union_left _ (Set.mem_union_left _ ⟨i, j, h, rfl⟩))

theorem incidence_mem {β : n → B} {Y : ι → Matrix n n ℂ} {A : Subalgebra ℂ (Matrix n n ℂ)}
    (hA : incidenceGens β Y ⊆ A) (e : ι) : Y e ∈ A :=
  hA (Set.mem_union_left _ (Set.mem_union_right _ ⟨e, rfl⟩))

theorem incidence_star_mem {β : n → B} {Y : ι → Matrix n n ℂ} {A : Subalgebra ℂ (Matrix n n ℂ)}
    (hA : incidenceGens β Y ⊆ A) (e : ι) : (Y e)ᴴ ∈ A :=
  hA (Set.mem_union_right _ ⟨e, rfl⟩)

/-- A support edge produces the matrix unit `E_ij`: a nonzero incidence entry
`Y_e(i,j)`, compressed by the endpoint units, is a nonzero multiple of `E_ij`. -/
theorem single_mem_of_adj {β : n → B} {Y : ι → Matrix n n ℂ} {A : Subalgebra ℂ (Matrix n n ℂ)}
    (hA : incidenceGens β Y ⊆ A) {i j : n} (h : (supportGraph β Y).Adj i j) :
    Matrix.single i j (1 : ℂ) ∈ A := by
  have hii : Matrix.single i i (1 : ℂ) ∈ A := gaugeUnit_mem hA rfl
  have hjj : Matrix.single j j (1 : ℂ) ∈ A := gaugeUnit_mem hA rfl
  rcases (supportGraph_adj β Y i j).mp h with ⟨_, (hb | ⟨e, he⟩) | (hb | ⟨e, he⟩)⟩
  · exact gaugeUnit_mem hA hb
  · have h1 : Matrix.single i i (1 : ℂ) * Y e * Matrix.single j j 1 ∈ A :=
      mul_mem (mul_mem hii (incidence_mem hA e)) hjj
    rw [Matrix.single_mul_mul_single, one_mul, mul_one] at h1
    have h2 := A.smul_mem h1 (Y e i j)⁻¹
    rwa [Matrix.smul_single, smul_eq_mul, inv_mul_cancel₀ he] at h2
  · exact gaugeUnit_mem hA hb.symm
  · have h1 : Matrix.single i i (1 : ℂ) * (Y e)ᴴ * Matrix.single j j 1 ∈ A :=
      mul_mem (mul_mem hii (incidence_star_mem hA e)) hjj
    rw [Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.conjTranspose_apply] at h1
    have hs : star (Y e j i) ≠ 0 := star_ne_zero.mpr he
    have h2 := A.smul_mem h1 (star (Y e j i))⁻¹
    rwa [Matrix.smul_single, smul_eq_mul, inv_mul_cancel₀ hs] at h2

/-- Products along a walk of the support graph generate the matrix unit between its
endpoints. -/
theorem single_mem_of_reachable {β : n → B} {Y : ι → Matrix n n ℂ}
    {A : Subalgebra ℂ (Matrix n n ℂ)} (hA : incidenceGens β Y ⊆ A) {i j : n}
    (h : (supportGraph β Y).Reachable i j) :
    Matrix.single i j (1 : ℂ) ∈ A := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact gaugeUnit_mem hA rfl
  | tail _ hadj ih =>
    have h1 := mul_mem ih (single_mem_of_adj hA hadj)
    rwa [Matrix.single_mul_single_same, one_mul] at h1

/-- The generators lie in the block algebra of a labelling constant on sectors and on
incidence supports. -/
theorem incidenceGens_subset_labelAlgebra {C : Type*} {β : n → B} {Y : ι → Matrix n n ℂ}
    {κ : n → C} (hβ : ∀ i j, β i = β j → κ i = κ j)
    (hY : ∀ e i j, Y e i j ≠ 0 → κ i = κ j) :
    incidenceGens β Y ⊆ (labelAlgebra κ : Set (Matrix n n ℂ)) := by
  rintro X ((⟨i, j, hij, rfl⟩ | ⟨e, rfl⟩) | ⟨e, rfl⟩)
  · exact single_mem_labelAlgebra (hβ i j hij) 1
  · intro a b hab
    by_contra hne
    exact hab (hY e a b hne)
  · intro a b hab
    show (Y e)ᴴ a b = 0
    rw [Matrix.conjTranspose_apply]
    by_contra hne
    exact hab (hY e b a (fun h0 => hne (by rw [h0, star_zero]))).symm

theorem adjoin_le_labelAlgebra {C : Type*} {β : n → B} {Y : ι → Matrix n n ℂ}
    {κ : n → C} (hβ : ∀ i j, β i = β j → κ i = κ j)
    (hY : ∀ e i j, Y e i j ≠ 0 → κ i = κ j) :
    Algebra.adjoin ℂ (incidenceGens β Y) ≤ labelAlgebra κ :=
  Algebra.adjoin_le (incidenceGens_subset_labelAlgebra hβ hY)

theorem labelAlgebra_le_adjoin {C : Type*} {β : n → B} {Y : ι → Matrix n n ℂ}
    {κ : n → C} (hreach : ∀ i j, κ i = κ j → (supportGraph β Y).Reachable i j) :
    labelAlgebra κ ≤ Algebra.adjoin ℂ (incidenceGens β Y) := by
  intro X hX
  set A := Algebra.adjoin ℂ (incidenceGens β Y) with hA
  rw [Matrix.matrix_eq_sum_single X]
  refine A.sum_mem fun i _ => A.sum_mem fun j _ => ?_
  by_cases hij : κ i = κ j
  · rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j 1 from by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]]
    exact A.smul_mem (single_mem_of_reachable Algebra.subset_adjoin (hreach i j hij)) _
  · rw [hX i j hij, Matrix.single_zero]
    exact A.zero_mem

/-- **The generated algebra is the block algebra of the component labelling.** -/
theorem adjoin_eq_labelAlgebra {C : Type*} {β : n → B} {Y : ι → Matrix n n ℂ}
    {κ : n → C} (hβ : ∀ i j, β i = β j → κ i = κ j)
    (hY : ∀ e i j, Y e i j ≠ 0 → κ i = κ j)
    (hreach : ∀ i j, κ i = κ j → (supportGraph β Y).Reachable i j) :
    Algebra.adjoin ℂ (incidenceGens β Y) = labelAlgebra κ :=
  le_antisymm (adjoin_le_labelAlgebra hβ hY) (labelAlgebra_le_adjoin hreach)

/-! ### The commutant of a block algebra -/

/-- **Commutant of a block algebra**: `X` commutes with `⊕_c M_{κ⁻¹ c}` iff
`X = diag(a_{κ i})` is a scalar on every block. -/
theorem mem_centralizer_labelAlgebra_iff {C : Type*} (κ : n → C) (X : Matrix n n ℂ) :
    X ∈ Subalgebra.centralizer ℂ (labelAlgebra κ : Set (Matrix n n ℂ)) ↔
      ∃ a : C → ℂ, X = Matrix.diagonal (a ∘ κ) := by
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro h
    have hoff : ∀ i j, i ≠ j → X i j = 0 := by
      intro i j hij
      have h1 := congrFun (congrFun (h (Matrix.single i i 1) (single_mem_labelAlgebra rfl 1)) i) j
      rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne (hbj := Ne.symm hij),
        one_mul] at h1
      exact h1
    have hdiag : ∀ i j, κ i = κ j → X j j = X i i := by
      intro i j hij
      have h1 := congrFun (congrFun (h (Matrix.single i j 1) (single_mem_labelAlgebra hij 1)) i) j
      rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_same, one_mul, mul_one] at h1
      exact h1
    classical
    refine ⟨fun c => if hc : ∃ i, κ i = c then X (Classical.choose hc) (Classical.choose hc)
      else 0, ?_⟩
    ext i j
    rw [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Function.comp_apply, if_true]
      have hc : ∃ i', κ i' = κ i := ⟨i, rfl⟩
      rw [dif_pos hc]
      exact hdiag _ _ (Classical.choose_spec hc)
    · rw [if_neg hij]
      exact hoff i j hij
  · rintro ⟨a, rfl⟩ g hg
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply, Function.comp_apply]
    by_cases hij : κ i = κ j
    · rw [hij, mul_comm]
    · rw [hg i j hij, zero_mul, mul_zero]

/-- The linear embedding `a ↦ diag(a ∘ κ)` of `ℂ^C` into `M_n(ℂ)`. -/
noncomputable def diagMap {C : Type*} (κ : n → C) : (C → ℂ) →ₗ[ℂ] Matrix n n ℂ :=
  (Matrix.diagonalLinearMap n ℂ ℂ).comp (LinearMap.funLeft ℂ ℂ κ)

theorem diagMap_apply {C : Type*} (κ : n → C) (a : C → ℂ) :
    diagMap κ a = Matrix.diagonal (a ∘ κ) := rfl

theorem diagMap_injective {C : Type*} {κ : n → C} (hκ : Function.Surjective κ) :
    Function.Injective (diagMap κ) :=
  Matrix.diagonal_injective.comp (LinearMap.funLeft_injective_of_surjective _ _ _ hκ)

theorem centralizer_labelAlgebra_toSubmodule {C : Type*} (κ : n → C) :
    Subalgebra.toSubmodule (Subalgebra.centralizer ℂ (labelAlgebra κ : Set (Matrix n n ℂ)))
      = LinearMap.range (diagMap κ) := by
  ext X
  rw [Subalgebra.mem_toSubmodule, mem_centralizer_labelAlgebra_iff, LinearMap.mem_range]
  simp only [diagMap_apply, eq_comm]

/-- **`𝒜' ≅ ℂ^{|C|}`**: the commutant of the block algebra of a surjective labelling
has dimension the number of blocks. -/
theorem finrank_centralizer_labelAlgebra {C : Type*} [Fintype C] {κ : n → C}
    (hκ : Function.Surjective κ) :
    Module.finrank ℂ (Subalgebra.centralizer ℂ (labelAlgebra κ : Set (Matrix n n ℂ)))
      = Fintype.card C := by
  rw [← Subalgebra.finrank_toSubmodule, centralizer_labelAlgebra_toSubmodule,
    LinearMap.finrank_range_of_inj (diagMap_injective hκ), Module.finrank_fintype_fun_eq_card]

/-! ### Transfer from the sector pattern graph -/

/-- The sector pattern graph: sectors `b — b'` when some incidence `e` has
`edge e = (b, b')`. -/
def patternGraph (edge : ι → B × B) : SimpleGraph B :=
  SimpleGraph.fromRel fun b b' => ∃ e, edge e = (b, b')

/-- Vertices in one sector are reachable (equal or adjacent). -/
theorem reachable_of_sector_eq (β : n → B) (Y : ι → Matrix n n ℂ) {i j : n} (h : β i = β j) :
    (supportGraph β Y).Reachable i j := by
  by_cases hij : i = j
  · rw [hij]
  · exact SimpleGraph.Adj.reachable ((supportGraph_adj β Y i j).mpr ⟨hij, Or.inl (Or.inl h)⟩)

/-- A nonzero incidence supported on the sector pair `(b, b')` connects every vertex of
`b` to every vertex of `b'`. -/
theorem reachable_of_incidence {β : n → B} {Y : ι → Matrix n n ℂ} {edge : ι → B × B} (e : ι)
    (hsupp : ∀ i j, Y e i j ≠ 0 → β i = (edge e).1 ∧ β j = (edge e).2) (hne : Y e ≠ 0)
    {i j : n} (hi : β i = (edge e).1) (hj : β j = (edge e).2) (hbb : (edge e).1 ≠ (edge e).2) :
    (supportGraph β Y).Reachable i j := by
  have hex : ∃ i₀ j₀, Y e i₀ j₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (Matrix.ext fun i₀ j₀ => hall i₀ j₀)
  obtain ⟨i₀, j₀, h₀⟩ := hex
  obtain ⟨hi₀, hj₀⟩ := hsupp i₀ j₀ h₀
  have hadj : (supportGraph β Y).Adj i₀ j₀ := by
    refine (supportGraph_adj β Y i₀ j₀).mpr ⟨?_, Or.inl (Or.inr ⟨e, h₀⟩)⟩
    rintro rfl
    exact hbb (hi₀.symm.trans hj₀)
  exact (reachable_of_sector_eq β Y (hi.trans hi₀.symm)).trans
    (hadj.reachable.trans (reachable_of_sector_eq β Y (hj₀.trans hj.symm)))

/-- Reachability in the sector pattern graph lifts to reachability in the carrier
support graph, when every incidence is nonzero and supported on its sector pair. -/
theorem reachable_of_patternGraph {β : n → B} {Y : ι → Matrix n n ℂ} {edge : ι → B × B}
    (hsupp : ∀ e i j, Y e i j ≠ 0 → β i = (edge e).1 ∧ β j = (edge e).2)
    (hne : ∀ e, Y e ≠ 0) {b b' : B} (h : (patternGraph edge).Reachable b b') :
    ∀ i j : n, β i = b → β j = b' → (supportGraph β Y).Reachable i j := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl =>
    intro i j hi hj
    exact reachable_of_sector_eq β Y (hi.trans hj.symm)
  | @tail c d _ hadj ih =>
    intro i j hi hj
    -- an edge `c — d` of the pattern graph is realized by a nonzero incidence
    rcases (SimpleGraph.fromRel_adj _ c d).mp hadj with ⟨hcd, ⟨e, he⟩ | ⟨e, he⟩⟩
    · have hbb : (edge e).1 ≠ (edge e).2 := by rw [he]; exact hcd
      -- pick any vertex of sector `c` via the nonzero incidence
      obtain ⟨k₀, l₀, h₀⟩ : ∃ k₀ l₀, Y e k₀ l₀ ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hne e (Matrix.ext fun a b' => hall a b')
      have hk₀ := (hsupp e k₀ l₀ h₀).1
      rw [he] at hk₀
      exact (ih i k₀ hi hk₀).trans
        (reachable_of_incidence e (hsupp e) (hne e) (by rw [he]; exact hk₀) (by rw [he]; exact hj)
          hbb)
    · have hbb : (edge e).1 ≠ (edge e).2 := by rw [he]; exact hcd.symm
      obtain ⟨k₀, l₀, h₀⟩ : ∃ k₀ l₀, Y e k₀ l₀ ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hne e (Matrix.ext fun a b' => hall a b')
      have hl₀ := (hsupp e k₀ l₀ h₀).2
      rw [he] at hl₀
      exact (ih i l₀ hi hl₀).trans
        (reachable_of_incidence e (hsupp e) (hne e) (by rw [he]; exact hj) (by rw [he]; exact hl₀)
          hbb).symm

/-- **Block algebra from a sector pattern**: with sectors `β`, a component labelling
`κB` of the sectors constant along every incidence pair and connecting every pair of
sectors with equal label through the pattern graph, and nonzero incidences supported on
their sector pairs, the generated algebra is the block algebra of `κB ∘ β`. -/
theorem adjoin_eq_labelAlgebra_of_pattern {C : Type*} {β : n → B} {Y : ι → Matrix n n ℂ}
    {edge : ι → B × B} (κB : B → C)
    (hsupp : ∀ e i j, Y e i j ≠ 0 → β i = (edge e).1 ∧ β j = (edge e).2)
    (hne : ∀ e, Y e ≠ 0) (hcomp : ∀ e, κB (edge e).1 = κB (edge e).2)
    (hconn : ∀ b b', κB b = κB b' → (patternGraph edge).Reachable b b') :
    Algebra.adjoin ℂ (incidenceGens β Y) = labelAlgebra (κB ∘ β) := by
  refine adjoin_eq_labelAlgebra (fun i j h => by simp [h]) ?_ ?_
  · intro e i j h
    obtain ⟨hi, hj⟩ := hsupp e i j h
    simp only [Function.comp_apply, hi, hj, hcomp e]
  · intro i j h
    exact reachable_of_patternGraph hsupp hne (hconn _ _ h) i j rfl rfl

/-! ### The one-generation packet `Q ⊕ u ⊕ d ⊕ L ⊕ e` -/

/-- Sector labels of `𝓕₁₅ = Q ⊕ u ⊕ d ⊕ L ⊕ e` (dimensions `6, 3, 3, 2, 1`):
`Q = 0`, `u = 1`, `d = 2`, `L = 3`, `e = 4`. -/
def sector15 : Fin 15 → Fin 5 :=
  ![0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 4]

/-- The quark/lepton component of each sector. -/
def quarkLepton : Fin 5 → Fin 2 := ![0, 0, 0, 1, 1]

/-- The three Higgs-contracted incidence histories `Q ↔ u`, `Q ↔ d`, `L ↔ e`. -/
def edges3 : Fin 3 → Fin 5 × Fin 5 := ![(0, 1), (0, 2), (3, 4)]

instance : DecidableRel (patternGraph edges3).Adj := fun a b => by
  unfold patternGraph
  rw [SimpleGraph.fromRel_adj]
  infer_instance

theorem quarkLepton_surjective : Function.Surjective quarkLepton := by
  intro c
  fin_cases c
  · exact ⟨0, rfl⟩
  · exact ⟨3, rfl⟩

theorem sector15_surjective : Function.Surjective sector15 := by
  intro b
  fin_cases b
  · exact ⟨0, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨14, rfl⟩

/-- **`prop:one-gen-incidence`**: with nonzero incidences `Q ↔ u`, `Q ↔ d`, `L ↔ e`,
the gauge-plus-incidence algebra is the block algebra `M₁₂(ℂ) ⊕ M₃(ℂ)` of the
quark/lepton labelling (fibres of `12` and `3` vertices), and its commutant is
`{diag(a·1₁₂, b·1₃)} ≅ ℂ²`. -/
theorem one_gen_incidence (Y : Fin 3 → Matrix (Fin 15) (Fin 15) ℂ)
    (hsupp : ∀ e i j, Y e i j ≠ 0 → sector15 i = (edges3 e).1 ∧ sector15 j = (edges3 e).2)
    (hne : ∀ e, Y e ≠ 0) :
    Algebra.adjoin ℂ (incidenceGens sector15 Y) = labelAlgebra (quarkLepton ∘ sector15) ∧
    Fintype.card {i : Fin 15 // quarkLepton (sector15 i) = 0} = 12 ∧
    Fintype.card {i : Fin 15 // quarkLepton (sector15 i) = 1} = 3 ∧
    (∀ X : Matrix (Fin 15) (Fin 15) ℂ,
      X ∈ Subalgebra.centralizer ℂ ((Algebra.adjoin ℂ (incidenceGens sector15 Y) :
          Subalgebra ℂ (Matrix (Fin 15) (Fin 15) ℂ)) : Set (Matrix (Fin 15) (Fin 15) ℂ)) ↔
        ∃ a : Fin 2 → ℂ, X = Matrix.diagonal (a ∘ quarkLepton ∘ sector15)) ∧
    Module.finrank ℂ (Subalgebra.centralizer ℂ ((Algebra.adjoin ℂ (incidenceGens sector15 Y) :
          Subalgebra ℂ (Matrix (Fin 15) (Fin 15) ℂ)) : Set (Matrix (Fin 15) (Fin 15) ℂ))) = 2 := by
  have hcomp : ∀ e, quarkLepton (edges3 e).1 = quarkLepton (edges3 e).2 := by decide
  have hconn : ∀ b b', quarkLepton b = quarkLepton b' → (patternGraph edges3).Reachable b b' := by
    decide
  have heq := adjoin_eq_labelAlgebra_of_pattern quarkLepton hsupp hne hcomp hconn
  refine ⟨heq, by decide, by decide, ?_, ?_⟩
  · intro X
    rw [heq]
    exact mem_centralizer_labelAlgebra_iff _ X
  · rw [heq, finrank_centralizer_labelAlgebra (quarkLepton_surjective.comp sector15_surjective)]
    rfl

/-! ### The neutral-singlet variant `Q ⊕ u ⊕ d ⊕ L ⊕ e ⊕ ν` -/

/-- Sector labels of `𝓕₁₆ = Q ⊕ u ⊕ d ⊕ L ⊕ e ⊕ ν`: `ν = 5`. -/
def sector16 : Fin 16 → Fin 6 :=
  ![0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 4, 5]

/-- The quark/lepton component of each sector, the neutral singlet being leptonic. -/
def quarkLepton6 : Fin 6 → Fin 2 := ![0, 0, 0, 1, 1, 1]

/-- The four incidence histories `Q ↔ u`, `Q ↔ d`, `L ↔ e`, `L ↔ ν`. -/
def edges4 : Fin 4 → Fin 6 × Fin 6 := ![(0, 1), (0, 2), (3, 4), (3, 5)]

instance : DecidableRel (patternGraph edges4).Adj := fun a b => by
  unfold patternGraph
  rw [SimpleGraph.fromRel_adj]
  infer_instance

theorem quarkLepton6_surjective : Function.Surjective quarkLepton6 := by
  intro c
  fin_cases c
  · exact ⟨0, rfl⟩
  · exact ⟨3, rfl⟩

theorem sector16_surjective : Function.Surjective sector16 := by
  intro b
  fin_cases b
  · exact ⟨0, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨14, rfl⟩
  · exact ⟨15, rfl⟩

/-- **`prop:one-gen-incidence`, neutral-singlet clause**: adding a neutral singlet and a
nonzero `L ↔ ν` incidence changes the lepton block to `M₄(ℂ)` (fibre of `4` vertices)
while the commutant remains `ℂ²`. -/
theorem one_gen_incidence_neutral (Y : Fin 4 → Matrix (Fin 16) (Fin 16) ℂ)
    (hsupp : ∀ e i j, Y e i j ≠ 0 → sector16 i = (edges4 e).1 ∧ sector16 j = (edges4 e).2)
    (hne : ∀ e, Y e ≠ 0) :
    Algebra.adjoin ℂ (incidenceGens sector16 Y) = labelAlgebra (quarkLepton6 ∘ sector16) ∧
    Fintype.card {i : Fin 16 // quarkLepton6 (sector16 i) = 0} = 12 ∧
    Fintype.card {i : Fin 16 // quarkLepton6 (sector16 i) = 1} = 4 ∧
    (∀ X : Matrix (Fin 16) (Fin 16) ℂ,
      X ∈ Subalgebra.centralizer ℂ ((Algebra.adjoin ℂ (incidenceGens sector16 Y) :
          Subalgebra ℂ (Matrix (Fin 16) (Fin 16) ℂ)) : Set (Matrix (Fin 16) (Fin 16) ℂ)) ↔
        ∃ a : Fin 2 → ℂ, X = Matrix.diagonal (a ∘ quarkLepton6 ∘ sector16)) ∧
    Module.finrank ℂ (Subalgebra.centralizer ℂ ((Algebra.adjoin ℂ (incidenceGens sector16 Y) :
          Subalgebra ℂ (Matrix (Fin 16) (Fin 16) ℂ)) : Set (Matrix (Fin 16) (Fin 16) ℂ))) = 2 := by
  have hcomp : ∀ e, quarkLepton6 (edges4 e).1 = quarkLepton6 (edges4 e).2 := by decide
  have hconn : ∀ b b', quarkLepton6 b = quarkLepton6 b' →
      (patternGraph edges4).Reachable b b' := by
    decide
  have heq := adjoin_eq_labelAlgebra_of_pattern quarkLepton6 hsupp hne hcomp hconn
  refine ⟨heq, by decide, by decide, ?_, ?_⟩
  · intro X
    rw [heq]
    exact mem_centralizer_labelAlgebra_iff _ X
  · rw [heq, finrank_centralizer_labelAlgebra (quarkLepton6_surjective.comp sector16_surjective)]
    rfl

end IncidenceAssembly
end RenewalGeometry
