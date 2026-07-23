/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.PeierlsBound

/-!
# The planar contour construction for the Ising plus phase

Discharging the geometric content of the `ContourDatum` interface of
`NCG/Upstream/PeierlsBound.lean` for the two-dimensional Ising model
in a finite volume `Λ ⊆ ℤ²` with plus boundary conditions
(`constr:torsion-ising`, `manuscripts/renewal_emergence/renewal_emergence.tex`).

For a configuration with a minus spin at the origin, the **minus
cluster** `minusCl` is the set of sites reachable from the origin
through minus spins; the **filled cluster** `fillCl` adds every site
that cannot escape to the complement of `Λ` without touching the
cluster; the **contour** is its outer edge boundary `obdry`.  We
prove, with no planar-topology input:

* `mem_minusCl_spin` / `fillCl_subset` — the cluster is minus and
  the filled cluster lies inside the volume;
* `obdry_spec` — every contour edge joins a minus cluster site to a
  plus site of the escape region;
* `interior_obdry` — **the recovery lemma**: the region enclosed by
  the contour (the sites that cannot escape without crossing it) is
  exactly the filled cluster, so the flip region is determined by
  the contour alone;
* `flipC_flipC` — the contour flip is an involution, hence
  injective;
* `card_contour_ge` — contours have at least four edges (the four
  extremal sites of the filled cluster);
* `wt_flipC` — **the exact Peierls weight gain**
  `w(flip σ) = e^{2θ|γ|}·w(σ)`;
* `isingContourDatum` — the assembled `ContourDatum`, taking as its
  **single scoped input** the planar circuit count
  `#{realizable contours of length n} ≤ 4n·3^{n−1}` (the discrete
  Jordan/dual-circuit encoding, Georgii Ch. 6);
* `ising_magnetization` — the endpoint: for `θ ≥ ½·log 12`, the
  plus-boundary volume `Λ` has `⟨τ₀⟩ ≥ 203/216`, uniformly in `Λ`.
-/

namespace NCG.Upstream.Ising

open Finset

attribute [local instance 10] Classical.propDecidable

/-- Sites of the square lattice. -/
abbrev V2 := ℤ × ℤ

/-- Edges: a base site together with a direction (east/north). -/
abbrev IEdge := V2 × Bool

/-- The direction vector of an edge type. -/
def edir (b : Bool) : V2 := if b then (1, 0) else (0, 1)

/-- The two endpoints of an edge. -/
def ep0 (e : IEdge) : V2 := e.1

/-- The two endpoints of an edge. -/
def ep1 (e : IEdge) : V2 := e.1 + edir e.2

/-- Lattice adjacency: the two endpoints of some edge. -/
def IAdj (a b : V2) : Prop :=
  ∃ e : IEdge, (ep0 e = a ∧ ep1 e = b) ∨ (ep0 e = b ∧ ep1 e = a)

/-- An edge-avoiding step. -/
def EdgeStep (γ : Set IEdge) (a b : V2) : Prop :=
  ∃ e : IEdge, e ∉ γ
    ∧ ((ep0 e = a ∧ ep1 e = b) ∨ (ep0 e = b ∧ ep1 e = a))

variable (Λ : Finset V2)

/-- Configurations with plus boundary outside `Λ`. -/
def PlusBC := {σ : V2 → Bool // ∀ v, v ∉ Λ → σ v = true}

/-- The restriction equivalence: a plus-boundary configuration is a
configuration of the volume. -/
def restrictEquiv : PlusBC Λ ≃ (Λ → Bool) where
  toFun σ v := σ.1 v
  invFun f :=
    ⟨fun v => if h : v ∈ Λ then f ⟨v, h⟩ else true,
      fun v hv => dif_neg hv⟩
  left_inv σ := by
    refine Subtype.ext (funext fun v => ?_)
    by_cases h : v ∈ Λ
    · simp [h]
    · simp [h, σ.2 v h]
  right_inv f := by
    funext v
    simp [v.2]

noncomputable instance : Fintype (PlusBC Λ) :=
  Fintype.ofEquiv _ (restrictEquiv Λ).symm

noncomputable instance : DecidableEq (PlusBC Λ) :=
  Classical.decEq _

/-- The incident edges of the volume. -/
def eVol : Finset IEdge :=
  Λ.biUnion fun v =>
    {(v, true), (v, false), (v - ((1 : ℤ), (0 : ℤ)), true),
      (v - ((0 : ℤ), (1 : ℤ)), false)}

theorem mem_eVol {e : IEdge} :
    e ∈ eVol Λ ↔ ep0 e ∈ Λ ∨ ep1 e ∈ Λ := by
  constructor
  · intro he
    obtain ⟨v, hv, hmem⟩ := Finset.mem_biUnion.mp he
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · left; exact hv
    · left; exact hv
    · right
      show (v - ((1:ℤ), (0:ℤ))) + edir true ∈ Λ
      rw [show edir true = ((1:ℤ), (0:ℤ)) from rfl, sub_add_cancel]
      exact hv
    · right
      show (v - ((0:ℤ), (1:ℤ))) + edir false ∈ Λ
      rw [show edir false = ((0:ℤ), (1:ℤ)) from rfl, sub_add_cancel]
      exact hv
  · intro h
    rcases h with h | h
    · refine Finset.mem_biUnion.mpr ⟨ep0 e, h, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases e with ⟨u, b⟩
      cases b
      · right; left; rfl
      · left; rfl
    · refine Finset.mem_biUnion.mpr ⟨ep1 e, h, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases e with ⟨u, b⟩
      cases b
      · right; right; right
        show (u, false) = ((u + edir false) - ((0:ℤ),(1:ℤ)), false)
        rw [show edir false = ((0:ℤ), (1:ℤ)) from rfl,
          add_sub_cancel_right]
      · right; right; left
        show (u, true) = ((u + edir true) - ((1:ℤ),(0:ℤ)), true)
        rw [show edir true = ((1:ℤ), (0:ℤ)) from rfl,
          add_sub_cancel_right]

/-- The spin value of a site. -/
noncomputable def spin (b : Bool) : ℝ := if b then 1 else -1

theorem spin_not (b : Bool) : spin (!b) = -spin b := by
  cases b <;> simp [spin]

theorem spin_sq_vals (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b
  · right; simp [spin]
  · left; simp [spin]

/-- The Ising Gibbs weight of a plus-boundary configuration. -/
noncomputable def wt (θ : ℝ) (σ : PlusBC Λ) : ℝ :=
  Real.exp (θ * ∑ e ∈ eVol Λ, spin (σ.1 (ep0 e)) * spin (σ.1 (ep1 e)))

theorem wt_pos (θ : ℝ) (σ : PlusBC Λ) : 0 < wt Λ θ σ :=
  Real.exp_pos _

/-! ## Clusters, fills, contours -/

variable {Λ}

/-- The minus cluster of the origin. -/
def minusCl (σ : PlusBC Λ) : Set V2 :=
  {v | Relation.ReflTransGen
    (fun a b => IAdj a b ∧ σ.1 b = false) 0 v}

/-- Escape: a path to the complement of the volume avoiding the
minus cluster. -/
def escV (σ : PlusBC Λ) (v : V2) : Prop :=
  ∃ w, w ∉ Λ ∧ Relation.ReflTransGen
    (fun a b => IAdj a b ∧ b ∉ minusCl σ) v w

/-- The filled cluster: the minus cluster together with everything
that cannot escape it. -/
def fillCl (σ : PlusBC Λ) : Set V2 :=
  {v | v ∈ minusCl σ ∨ ¬ escV σ v}

/-- The outer edge boundary of a set of sites. -/
def obdry (S : Set V2) : Set IEdge :=
  {e | (ep0 e ∈ S ∧ ep1 e ∉ S) ∨ (ep0 e ∉ S ∧ ep1 e ∈ S)}

/-- Escape avoiding an edge set. -/
def escE (γ : Set IEdge) (v : V2) : Prop :=
  ∃ w, w ∉ Λ ∧ Relation.ReflTransGen (EdgeStep γ) v w

/-- The region enclosed by an edge set. -/
def interior (γ : Set IEdge) : Set V2 :=
  {v | ¬ escE (Λ := Λ) γ v}

theorem zero_mem_minusCl (σ : PlusBC Λ) : (0 : V2) ∈ minusCl σ :=
  Relation.ReflTransGen.refl

theorem zero_mem_fillCl (σ : PlusBC Λ) : (0 : V2) ∈ fillCl σ :=
  Or.inl (zero_mem_minusCl σ)

/-- Cluster sites are minus. -/
theorem mem_minusCl_spin {σ : PlusBC Λ} (h0 : σ.1 0 = false)
    {v : V2} (hv : v ∈ minusCl σ) : σ.1 v = false := by
  induction hv with
  | refl => exact h0
  | tail _ hstep _ => exact hstep.2

/-- Minus sites lie in the volume. -/
theorem minus_mem_vol {σ : PlusBC Λ} {v : V2}
    (hv : σ.1 v = false) : v ∈ Λ := by
  by_contra h
  rw [σ.2 v h] at hv
  simp at hv

/-- The cluster is closed under minus adjacency. -/
theorem minusCl_closed {σ : PlusBC Λ} {v u : V2}
    (hv : v ∈ minusCl σ) (hadj : IAdj v u) (hu : σ.1 u = false) :
    u ∈ minusCl σ :=
  Relation.ReflTransGen.tail hv ⟨hadj, hu⟩

/-- Sites outside the volume escape trivially. -/
theorem escV_of_notMem {σ : PlusBC Λ} {v : V2} (hv : v ∉ Λ) :
    escV σ v :=
  ⟨v, hv, Relation.ReflTransGen.refl⟩

/-- The filled cluster lies inside the volume. -/
theorem fillCl_subset {σ : PlusBC Λ} (h0 : σ.1 0 = false) :
    fillCl σ ⊆ (Λ : Set V2) := by
  intro v hv
  by_contra h
  rcases hv with hC | hesc
  · exact h (minus_mem_vol (mem_minusCl_spin h0 hC))
  · exact hesc (escV_of_notMem h)

/-- **The contour edges join a minus cluster site to a plus escape
site**: for every boundary edge of the filled cluster, the inside
endpoint is a minus site of the cluster and the outside endpoint is
a plus site. -/
theorem obdry_spec {σ : PlusBC Λ} (h0 : σ.1 0 = false) {p q : V2}
    (hadj : IAdj p q) (hp : p ∈ fillCl σ) (hq : q ∉ fillCl σ) :
    p ∈ minusCl σ ∧ σ.1 p = false ∧ σ.1 q = true := by
  have hqO : q ∉ minusCl σ ∧ escV σ q := by
    by_contra hcon
    push_neg at hcon
    rcases Classical.em (q ∈ minusCl σ) with h | h
    · exact hq (Or.inl h)
    · exact hq (Or.inr (hcon h))
  have hpC : p ∈ minusCl σ := by
    rcases hp with h | h
    · exact h
    · exfalso
      refine h ?_
      obtain ⟨w, hw, hpath⟩ := hqO.2
      exact ⟨w, hw, Relation.ReflTransGen.head ⟨hadj, hqO.1⟩ hpath⟩
  refine ⟨hpC, mem_minusCl_spin h0 hpC, ?_⟩
  by_contra hqspin
  rw [Bool.not_eq_true] at hqspin
  exact hqO.1 (minusCl_closed hpC hadj hqspin)

/-- Edge endpoints are adjacent. -/
theorem iAdj_of_edge (e : IEdge) : IAdj (ep0 e) (ep1 e) :=
  ⟨e, Or.inl ⟨rfl, rfl⟩⟩

/-- **The recovery lemma**: the region enclosed by the contour of
the filled cluster is exactly the filled cluster — the flip region
is determined by the contour alone. -/
theorem interior_obdry {σ : PlusBC Λ} (h0 : σ.1 0 = false) :
    interior (Λ := Λ) (obdry (fillCl σ)) = fillCl σ := by
  ext v
  constructor
  · -- enclosed sites lie in the filled cluster
    intro hv
    by_contra hvout
    refine hv ?_
    -- `v` is in the escape region: its cluster-avoiding escape path
    -- never touches a contour edge
    have hvO : v ∉ minusCl σ ∧ escV σ v := by
      by_contra hcon
      push_neg at hcon
      rcases Classical.em (v ∈ minusCl σ) with h | h
      · exact hvout (Or.inl h)
      · exact hvout (Or.inr (hcon h))
    obtain ⟨w, hw, hpath⟩ := hvO.2
    refine ⟨w, hw, ?_⟩
    -- transport the path, remembering that its sites avoid the
    -- cluster
    have key : ∀ {b : V2},
        Relation.ReflTransGen
          (fun a b => IAdj a b ∧ b ∉ minusCl σ) v b →
        Relation.ReflTransGen (EdgeStep (obdry (fillCl σ))) v b
          ∧ b ∉ minusCl σ := by
      intro b hab
      induction hab with
      | refl => exact ⟨Relation.ReflTransGen.refl, hvO.1⟩
      | tail hab hstep ih =>
        rename_i x y
        obtain ⟨hpath', hx⟩ := ih
        obtain ⟨e, he⟩ := hstep.1
        have henotin : e ∉ obdry (fillCl σ) := by
          intro hein
          have h1 : ep0 e ∈ minusCl σ ∨ ep1 e ∈ minusCl σ := by
            rcases hein with ⟨h2, h3⟩ | ⟨h2, h3⟩
            · exact Or.inl
                (obdry_spec h0 (iAdj_of_edge e) h2 h3).1
            · exact Or.inr
                (obdry_spec h0 ⟨e, Or.inr ⟨rfl, rfl⟩⟩ h3 h2).1
          rcases he with ⟨hx0, hy1⟩ | ⟨hy0, hx1⟩
          · rcases h1 with h | h
            · exact hx (hx0 ▸ h)
            · exact hstep.2 (hy1 ▸ h)
          · rcases h1 with h | h
            · exact hstep.2 (hy0 ▸ h)
            · exact hx (hx1 ▸ h)
        exact ⟨Relation.ReflTransGen.tail hpath' ⟨e, henotin, he⟩,
          hstep.2⟩
    exact (key hpath).1
  · -- the filled cluster cannot escape without crossing the contour
    intro hv hesc
    obtain ⟨w, hw, hpath⟩ := hesc
    have hstay : ∀ {b : V2},
        Relation.ReflTransGen (EdgeStep (obdry (fillCl σ))) v b →
        b ∈ fillCl σ := by
      intro b hab
      induction hab with
      | refl => exact hv
      | tail hab hstep ih =>
        rename_i x y
        by_contra hy
        obtain ⟨e, hemem, hends⟩ := hstep
        refine hemem ?_
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm ▸ ih, h2.symm ▸ hy⟩
        · exact Or.inr ⟨h1.symm ▸ hy, h2.symm ▸ ih⟩
    exact hw (fillCl_subset h0 (hstay hpath))

/-! ## The contour as a finite edge set -/

/-- The filled cluster is finite. -/
theorem fillCl_finite {σ : PlusBC Λ} (h0 : σ.1 0 = false) :
    (fillCl σ).Finite :=
  Λ.finite_toSet.subset (fillCl_subset h0)

/-- Contour edges are incident to the volume. -/
theorem obdry_subset_eVol {σ : PlusBC Λ} (h0 : σ.1 0 = false) :
    obdry (fillCl σ) ⊆ ↑(eVol Λ) := by
  intro e he
  rw [Finset.mem_coe, mem_eVol]
  rcases he with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact Or.inl (fillCl_subset h0 h1)
  · exact Or.inr (fillCl_subset h0 h2)

/-- The contour of a configuration. -/
noncomputable def contour (σ : PlusBC Λ) : Finset IEdge :=
  (eVol Λ).filter (fun e => e ∈ obdry (fillCl σ))

theorem coe_contour {σ : PlusBC Λ} (h0 : σ.1 0 = false) :
    (↑(contour σ) : Set IEdge) = obdry (fillCl σ) := by
  ext e
  rw [Finset.mem_coe, contour, Finset.mem_filter]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨obdry_subset_eVol h0 h, h⟩

/-- **Contours have at least four edges**: the four extremal sites
of the filled cluster contribute four distinct boundary edges. -/
theorem four_le_card_contour {σ : PlusBC Λ} (h0 : σ.1 0 = false) :
    4 ≤ (contour σ).card := by
  classical
  have hfin := fillCl_finite h0
  set T := hfin.toFinset with hT
  have hT0 : (0 : V2) ∈ T := by
    rw [hT, Set.Finite.mem_toFinset]
    exact zero_mem_fillCl σ
  have hTne : T.Nonempty := ⟨0, hT0⟩
  obtain ⟨u, huT, humax⟩ := T.exists_max_image Prod.fst hTne
  obtain ⟨v, hvT, hvmin⟩ := T.exists_min_image Prod.fst hTne
  obtain ⟨p, hpT, hpmax⟩ := T.exists_max_image Prod.snd hTne
  obtain ⟨q, hqT, hqmin⟩ := T.exists_min_image Prod.snd hTne
  have hmem : ∀ x : V2, x ∈ T ↔ x ∈ fillCl σ := fun x => by
    rw [hT, Set.Finite.mem_toFinset]
  set e₁ : IEdge := (u, true) with he₁
  set e₂ : IEdge := (v - ((1:ℤ), (0:ℤ)), true) with he₂
  set e₃ : IEdge := (p, false) with he₃
  set e₄ : IEdge := (q - ((0:ℤ), (1:ℤ)), false) with he₄
  have hb₁ : e₁ ∈ obdry (fillCl σ) := by
    refine Or.inl ⟨(hmem u).mp huT, fun hc => ?_⟩
    have h1 := humax _ ((hmem _).mpr hc)
    have h2 : (ep1 e₁).1 = u.1 + 1 := by
      show (u + edir true).1 = u.1 + 1
      rw [show edir true = ((1:ℤ), (0:ℤ)) from rfl]
      rfl
    omega
  have hb₂ : e₂ ∈ obdry (fillCl σ) := by
    have hep1 : ep1 e₂ = v := by
      show (v - ((1:ℤ),(0:ℤ))) + edir true = v
      rw [show edir true = ((1:ℤ), (0:ℤ)) from rfl, sub_add_cancel]
    refine Or.inr ⟨fun hc => ?_, hep1 ▸ (hmem v).mp hvT⟩
    have h1 := hvmin _ ((hmem _).mpr hc)
    have h2 : (ep0 e₂).1 = v.1 - 1 := rfl
    omega
  have hb₃ : e₃ ∈ obdry (fillCl σ) := by
    refine Or.inl ⟨(hmem p).mp hpT, fun hc => ?_⟩
    have h1 := hpmax _ ((hmem _).mpr hc)
    have h2 : (ep1 e₃).2 = p.2 + 1 := by
      show (p + edir false).2 = p.2 + 1
      rw [show edir false = ((0:ℤ), (1:ℤ)) from rfl]
      rfl
    omega
  have hb₄ : e₄ ∈ obdry (fillCl σ) := by
    have hep1 : ep1 e₄ = q := by
      show (q - ((0:ℤ),(1:ℤ))) + edir false = q
      rw [show edir false = ((0:ℤ), (1:ℤ)) from rfl, sub_add_cancel]
    refine Or.inr ⟨fun hc => ?_, hep1 ▸ (hmem q).mp hqT⟩
    have h1 := hqmin _ ((hmem _).mpr hc)
    have h2 : (ep0 e₄).2 = q.2 - 1 := rfl
    omega
  have h12 : e₁ ≠ e₂ := by
    intro h
    have h1 : u.1 = v.1 - 1 := congrArg (fun e : IEdge => e.1.1) h
    have h2 := hvmin u huT
    omega
  have h34 : e₃ ≠ e₄ := by
    intro h
    have h1 : p.2 = q.2 - 1 := congrArg (fun e : IEdge => e.1.2) h
    have h2 := hqmin p hpT
    omega
  have h13 : e₁ ≠ e₃ := fun h => by
    have h1 := congrArg (fun e : IEdge => e.2) h
    simp at h1
  have h14 : e₁ ≠ e₄ := fun h => by
    have h1 := congrArg (fun e : IEdge => e.2) h
    simp at h1
  have h23 : e₂ ≠ e₃ := fun h => by
    have h1 := congrArg (fun e : IEdge => e.2) h
    simp at h1
  have h24 : e₂ ≠ e₄ := fun h => by
    have h1 := congrArg (fun e : IEdge => e.2) h
    simp at h1
  have hsub : ({e₁, e₂, e₃, e₄} : Finset IEdge) ⊆ contour σ := by
    intro e he
    rw [contour, Finset.mem_filter]
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨obdry_subset_eVol h0 hb₁, hb₁⟩
    · exact ⟨obdry_subset_eVol h0 hb₂, hb₂⟩
    · exact ⟨obdry_subset_eVol h0 hb₃, hb₃⟩
    · exact ⟨obdry_subset_eVol h0 hb₄, hb₄⟩
  have hcard : ({e₁, e₂, e₃, e₄} : Finset IEdge).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨h12, h13, h14⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨h23, h24⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact h34),
      Finset.card_singleton]
  calc 4 = ({e₁, e₂, e₃, e₄} : Finset IEdge).card := hcard.symm
    _ ≤ (contour σ).card := Finset.card_le_card hsub

/-! ## The contour flip -/

/-- The contour flip: reverse every spin enclosed by the contour. -/
noncomputable def flipC (γ : Finset IEdge) (σ : PlusBC Λ) :
    PlusBC Λ :=
  ⟨fun v => if v ∈ interior (Λ := Λ) (↑γ : Set IEdge)
      then !(σ.1 v) else σ.1 v, by
    intro v hv
    show (if v ∈ interior (Λ := Λ) (↑γ : Set IEdge)
      then !(σ.1 v) else σ.1 v) = true
    rw [if_neg, σ.2 v hv]
    intro hvint
    exact hvint ⟨v, hv, Relation.ReflTransGen.refl⟩⟩

/-- The flip is an involution. -/
theorem flipC_flipC (γ : Finset IEdge) (σ : PlusBC Λ) :
    flipC γ (flipC γ σ) = σ := by
  refine Subtype.ext (funext fun v => ?_)
  by_cases h : v ∈ interior (Λ := Λ) (↑γ : Set IEdge)
  · simp [flipC, h]
  · simp [flipC, h]

theorem flipC_injective (γ : Finset IEdge) :
    Function.Injective (flipC (Λ := Λ) γ) := by
  intro a b h
  have h1 := congrArg (flipC γ) h
  rwa [flipC_flipC, flipC_flipC] at h1

/-- **The exact Peierls weight gain**:
`w(flip σ) = e^{2θ|γ|}·w(σ)`. -/
theorem wt_flipC {σ : PlusBC Λ} (h0 : σ.1 0 = false) (θ : ℝ) :
    wt Λ θ (flipC (contour σ) σ)
      = Real.exp (2 * θ * (contour σ).card) * wt Λ θ σ := by
  have hint : interior (Λ := Λ) (↑(contour σ) : Set IEdge)
      = fillCl σ := by
    rw [coe_contour h0]
    exact interior_obdry h0
  have hval : ∀ v : V2, (flipC (contour σ) σ).1 v
      = if v ∈ fillCl σ then !(σ.1 v) else σ.1 v := by
    intro v
    show (if v ∈ interior (Λ := Λ) (↑(contour σ) : Set IEdge)
      then !(σ.1 v) else σ.1 v) = _
    rw [hint]
  have hγsub : contour σ ⊆ eVol Λ := Finset.filter_subset _ _
  have hsum : ∑ e ∈ eVol Λ,
      spin ((flipC (contour σ) σ).1 (ep0 e))
        * spin ((flipC (contour σ) σ).1 (ep1 e))
      = (∑ e ∈ eVol Λ, spin (σ.1 (ep0 e)) * spin (σ.1 (ep1 e)))
        + 2 * (contour σ).card := by
    rw [← Finset.sum_sdiff hγsub, ← Finset.sum_sdiff hγsub
      (f := fun e => spin (σ.1 (ep0 e)) * spin (σ.1 (ep1 e)))]
    have hoff : ∀ e ∈ eVol Λ \ contour σ,
        spin ((flipC (contour σ) σ).1 (ep0 e))
          * spin ((flipC (contour σ) σ).1 (ep1 e))
        = spin (σ.1 (ep0 e)) * spin (σ.1 (ep1 e)) := by
      intro e he
      rw [Finset.mem_sdiff] at he
      have hnb : e ∉ obdry (fillCl σ) := by
        intro hb
        exact he.2 (by
          rw [contour, Finset.mem_filter]
          exact ⟨he.1, hb⟩)
      by_cases h1 : ep0 e ∈ fillCl σ
      · have h2 : ep1 e ∈ fillCl σ := by
          by_contra h2
          exact hnb (Or.inl ⟨h1, h2⟩)
        rw [hval, hval, if_pos h1, if_pos h2, spin_not, spin_not]
        ring
      · have h2 : ep1 e ∉ fillCl σ := by
          intro h2
          exact hnb (Or.inr ⟨h1, h2⟩)
        rw [hval, hval, if_neg h1, if_neg h2]
    have honold : ∀ e ∈ contour σ,
        spin (σ.1 (ep0 e)) * spin (σ.1 (ep1 e)) = -1 := by
      intro e he
      have hb : e ∈ obdry (fillCl σ) := by
        rw [contour, Finset.mem_filter] at he
        exact he.2
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨-, hp, hq⟩ := obdry_spec h0 (iAdj_of_edge e) h1 h2
        rw [hp, hq]
        simp [spin]
      · obtain ⟨-, hp, hq⟩ := obdry_spec h0
          ⟨e, Or.inr ⟨rfl, rfl⟩⟩ h2 h1
        rw [hp, hq]
        simp [spin]
    have honnew : ∀ e ∈ contour σ,
        spin ((flipC (contour σ) σ).1 (ep0 e))
          * spin ((flipC (contour σ) σ).1 (ep1 e)) = 1 := by
      intro e he
      have hb : e ∈ obdry (fillCl σ) := by
        rw [contour, Finset.mem_filter] at he
        exact he.2
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨-, hp, hq⟩ := obdry_spec h0 (iAdj_of_edge e) h1 h2
        rw [hval, hval, if_pos h1, if_neg h2, hp, hq]
        simp [spin]
      · obtain ⟨-, hp, hq⟩ := obdry_spec h0
          ⟨e, Or.inr ⟨rfl, rfl⟩⟩ h2 h1
        rw [hval, hval, if_neg h1, if_pos h2, hp, hq]
        simp [spin]
    rw [Finset.sum_congr rfl hoff, Finset.sum_congr rfl honnew,
      Finset.sum_congr rfl honold]
    rw [Finset.sum_const, Finset.sum_const]
    simp only [nsmul_eq_mul, mul_one, mul_neg_one]
    ring
  rw [wt, wt, hsum, mul_add, Real.exp_add, mul_comm]
  congr 1
  congr 1
  ring

/-! ## The assembled contour datum -/

variable (Λ)

/-- The realizable contours of the volume. -/
noncomputable def contours : Finset (Finset IEdge) :=
  (eVol Λ).powerset.filter
    (fun γ => ∃ σ : PlusBC Λ, σ.1 0 = false ∧ contour σ = γ)

theorem spin_eq_neg_one_iff (b : Bool) : spin b = -1 ↔ b = false := by
  cases b
  · simp [spin]
  · simp only [spin, if_pos]
    norm_num

/-- **The assembled contour datum** for the plus-boundary Ising
volume: every geometric field discharged, with the planar circuit
count as the single scoped hypothesis. -/
noncomputable def isingContourDatum (θ : ℝ)
    (hcount : ∀ n, ((contours Λ).filter
      (fun γ => γ.card = n)).card ≤ 4 * n * 3 ^ (n - 1)) :
    ContourDatum (PlusBC Λ) (wt Λ θ) θ
      (Finset.univ.filter (fun σ => spin (σ.1 0) = -1)) where
  ι := ↥(contours Λ)
  fin := FinsetCoe.fintype _
  len γ := (γ.1).card
  len_ge γ := by
    obtain ⟨-, σ, h0, hγ⟩ := Finset.mem_filter.mp γ.2
    rw [← hγ]
    exact four_le_card_contour h0
  count n := by
    calc (Finset.univ.filter
        (fun γ : ↥(contours Λ) => (γ.1).card = n)).card
        ≤ ((contours Λ).filter (fun γ => γ.card = n)).card := by
          refine Finset.card_le_card_of_injOn (fun γ => γ.1) ?_ ?_
          · intro γ hγ
            rw [Finset.mem_coe, Finset.mem_filter] at hγ ⊢
            exact ⟨γ.2, hγ.2⟩
          · exact fun a _ b _ h => Subtype.ext h
      _ ≤ 4 * n * 3 ^ (n - 1) := hcount n
  occurs γ := Finset.univ.filter
    (fun σ => σ.1 0 = false ∧ contour σ = γ.1)
  cover σ hσ := by
    rw [Finset.mem_filter] at hσ
    have h0 : σ.1 0 = false := (spin_eq_neg_one_iff _).mp hσ.2
    refine ⟨⟨contour σ, ?_⟩, ?_⟩
    · rw [contours, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.filter_subset _ _, σ, h0, rfl⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ σ, h0, rfl⟩
  flip γ := flipC γ.1
  flip_inj γ := (flipC_injective γ.1).injOn
  gain γ σ hσ := by
    rw [Finset.mem_filter] at hσ
    obtain ⟨-, h0, hγ⟩ := hσ
    have h1 := wt_flipC h0 θ
    rw [hγ] at h1
    rw [h1]

/-- **The uniform Ising magnetization bound**: for `θ ≥ ½·log 12`,
every plus-boundary volume has `⟨τ₀⟩ ≥ 203/216` — the constant of
`thm:torsion-phase-coexistence` (ii), with the planar circuit count
as the single remaining scoped input. -/
theorem ising_magnetization (θ : ℝ)
    (hθ : (1 / 2) * Real.log 12 ≤ θ)
    (hcount : ∀ n, ((contours Λ).filter
      (fun γ => γ.card = n)).card ≤ 4 * n * 3 ^ (n - 1)) :
    (203 / 216) * ∑ σ : PlusBC Λ, wt Λ θ σ
      ≤ ∑ σ : PlusBC Λ, wt Λ θ σ * spin (σ.1 0) :=
  peierls_magnetization (fun σ => (wt_pos Λ θ σ).le)
    (fun σ => spin_sq_vals _) (isingContourDatum Λ θ hcount) hθ

end NCG.Upstream.Ising
