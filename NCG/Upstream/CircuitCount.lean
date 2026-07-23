/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.IsingContours

/-!
# Toward the planar circuit count: local contour structure

Foundation layers for the last Peierls scoped input — the planar
circuit count `#{realizable contours of length n} ≤ 4n·3^{n−1}`
(the `hcount` hypothesis of `isingContourDatum`).

**Layer A (this file's first section)**: the discrete local Jordan
property — around every dual vertex (plaquette corner), the number of
boundary edges of *any* site set is **even**.  This is the
sign-change parity of a 2-coloring around the 4-cycle of surrounding
sites, a finite Boolean check, and it is what makes the contour
traceable as closed dual circuits.

* `cornerEdges` — the four primal edges incident to the dual corner
  `v + (½,½)`;
* `xor_cycle_even` — sign changes around a 4-cycle are even;
* `cornerDegree_even` — the corner degree of any boundary is even;
* `corner0`/`corner1` — the two dual endpoints of a primal edge, with
  `mem_cornerEdges_iff` identifying incidence.
-/

namespace NCG.Upstream.Ising

open NCG

/-- The four primal edges incident to the dual corner `v + (½,½)`:
south, north, west, east. -/
def cornerEdges (v : V2) : List IEdge :=
  [((v.1, v.2), true), ((v.1, v.2 + 1), true),
   ((v.1, v.2), false), ((v.1 + 1, v.2), false)]

/-- Sign changes of a 2-coloring around a 4-cycle come in pairs. -/
theorem xor_cycle_even (a b c d : Bool) :
    ((xor a b).toNat + (xor c d).toNat + (xor a c).toNat
      + (xor b d).toNat) % 2 = 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

open Classical in
/-- Boundary membership is the xor of the endpoint memberships. -/
theorem decide_obdry (S : Set V2) (e : IEdge) :
    decide (e ∈ obdry S)
      = xor (decide (ep0 e ∈ S)) (decide (ep1 e ∈ S)) := by
  rcases Classical.em (ep0 e ∈ S) with h0 | h0 <;>
    rcases Classical.em (ep1 e ∈ S) with h1 | h1 <;>
      simp [obdry, h0, h1]

open Classical in
/-- The corner degree: the number of boundary edges at a dual
vertex. -/
noncomputable def cornerDegree (S : Set V2) (v : V2) : ℕ :=
  (cornerEdges v).countP (fun e => decide (e ∈ obdry S))

/-- Endpoint computations for the four corner edges. -/
theorem cornerEdges_endpoints (v : V2) :
    ep0 ((v.1, v.2), true) = (v.1, v.2)
    ∧ ep1 ((v.1, v.2), true) = (v.1 + 1, v.2)
    ∧ ep0 ((v.1, v.2 + 1), true) = (v.1, v.2 + 1)
    ∧ ep1 ((v.1, v.2 + 1), true) = (v.1 + 1, v.2 + 1)
    ∧ ep0 ((v.1, v.2), false) = (v.1, v.2)
    ∧ ep1 ((v.1, v.2), false) = (v.1, v.2 + 1)
    ∧ ep0 ((v.1 + 1, v.2), false) = (v.1 + 1, v.2)
    ∧ ep1 ((v.1 + 1, v.2), false) = (v.1 + 1, v.2 + 1) := by
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_⟩
  · show (v.1, v.2) + edir true = (v.1 + 1, v.2)
    rw [show edir true = ((1 : ℤ), (0 : ℤ)) from rfl]
    show (v.1 + 1, v.2 + 0) = (v.1 + 1, v.2)
    rw [add_zero]
  · show (v.1, v.2 + 1) + edir true = (v.1 + 1, v.2 + 1)
    rw [show edir true = ((1 : ℤ), (0 : ℤ)) from rfl]
    show (v.1 + 1, v.2 + 1 + 0) = (v.1 + 1, v.2 + 1)
    rw [add_zero]
  · show (v.1, v.2) + edir false = (v.1, v.2 + 1)
    rw [show edir false = ((0 : ℤ), (1 : ℤ)) from rfl]
    show (v.1 + 0, v.2 + 1) = (v.1, v.2 + 1)
    rw [add_zero]
  · show (v.1 + 1, v.2) + edir false = (v.1 + 1, v.2 + 1)
    rw [show edir false = ((0 : ℤ), (1 : ℤ)) from rfl]
    show (v.1 + 1 + 0, v.2 + 1) = (v.1 + 1, v.2 + 1)
    rw [add_zero]

open Classical in
/-- **Layer A (local Jordan parity)**: the corner degree of the
boundary of *any* site set is even — around every dual vertex the
boundary has 0, 2, or 4 edges. -/
theorem cornerDegree_even (S : Set V2) (v : V2) :
    cornerDegree S v % 2 = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := cornerEdges_endpoints v
  unfold cornerDegree cornerEdges
  rw [List.countP_cons, List.countP_cons, List.countP_cons,
    List.countP_cons, List.countP_nil]
  simp only [decide_obdry]
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  set a := decide ((v.1, v.2) ∈ S)
  set b := decide ((v.1 + 1, v.2) ∈ S)
  set c := decide ((v.1, v.2 + 1) ∈ S)
  set d := decide ((v.1 + 1, v.2 + 1) ∈ S)
  have hcnt : (0 + (if (xor b d) = true then 1 else 0)
      + (if (xor a c) = true then 1 else 0)
      + (if (xor c d) = true then 1 else 0)
      + (if (xor a b) = true then 1 else 0)) % 2 = 0 := by
    have := xor_cycle_even a b c d
    rcases Bool.eq_false_or_eq_true (xor a b) with hab | hab <;>
      rcases Bool.eq_false_or_eq_true (xor c d) with hcd | hcd <;>
        rcases Bool.eq_false_or_eq_true (xor a c) with hac | hac <;>
          rcases Bool.eq_false_or_eq_true (xor b d) with hbd | hbd <;>
            (rw [hab, hcd, hac, hbd] at this ⊢
             first
               | rfl
               | (exfalso
                  simp at this)
               | simp)
  exact hcnt

/-- The two dual endpoints (corners) of a primal edge. -/
def corner0 (e : IEdge) : V2 :=
  if e.2 then (e.1.1, e.1.2 - 1) else (e.1.1 - 1, e.1.2)

/-- The second dual endpoint of a primal edge. -/
def corner1 (e : IEdge) : V2 := e.1

/-- **Dual incidence**: an edge is incident to a corner exactly when
that corner is one of its two dual endpoints. -/
theorem mem_cornerEdges_iff (e : IEdge) (v : V2) :
    e ∈ cornerEdges v ↔ v = corner0 e ∨ v = corner1 e := by
  obtain ⟨⟨x, y⟩, β⟩ := e
  cases β <;>
    simp [cornerEdges, corner0, corner1, Prod.ext_iff] <;>
    omega

/-! ## Layer B: the filled cluster is connected -/

variable {Λ : Finset V2}

/-- Lattice adjacency is symmetric. -/
theorem iAdj_symm {a b : V2} (h : IAdj a b) : IAdj b a := by
  obtain ⟨e, h | h⟩ := h
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

/-- The lattice is connected: any two sites are joined by a path. -/
theorem lattice_connected (a b : V2) :
    Relation.ReflTransGen IAdj a b := by
  have hkey : ∀ n : ℕ, ∀ a b : V2,
      (b.1 - a.1).natAbs + (b.2 - a.2).natAbs = n →
      Relation.ReflTransGen IAdj a b := by
    intro n
    induction n with
    | zero =>
        intro a b h
        have h3 : a = b := by
          rw [Prod.ext_iff]
          omega
        rw [h3]
    | succ n ih =>
        intro a b h
        rcases Nat.eq_zero_or_pos (b.1 - a.1).natAbs with hx | hx
        · rcases lt_or_ge a.2 b.2 with hlt | hle
          · refine Relation.ReflTransGen.head
              (b := (a.1, a.2 + 1)) ⟨((a.1, a.2), false), Or.inl ?_⟩
              (ih (a.1, a.2 + 1) b (by simp; omega))
            constructor
            · rfl
            · show (a.1, a.2) + edir false = (a.1, a.2 + 1)
              rw [show edir false = ((0 : ℤ), (1 : ℤ)) from rfl]
              show (a.1 + 0, a.2 + 1) = (a.1, a.2 + 1)
              rw [add_zero]
          · refine Relation.ReflTransGen.head
              (b := (a.1, a.2 - 1))
              ⟨((a.1, a.2 - 1), false), Or.inr ?_⟩
              (ih (a.1, a.2 - 1) b (by simp; omega))
            constructor
            · rfl
            · show (a.1, a.2 - 1) + edir false = (a.1, a.2)
              rw [show edir false = ((0 : ℤ), (1 : ℤ)) from rfl]
              show (a.1 + 0, a.2 - 1 + 1) = (a.1, a.2)
              rw [add_zero]
              congr 1
              ring
        · rcases lt_or_ge a.1 b.1 with hlt | hle
          · refine Relation.ReflTransGen.head
              (b := (a.1 + 1, a.2)) ⟨((a.1, a.2), true), Or.inl ?_⟩
              (ih (a.1 + 1, a.2) b (by simp; omega))
            constructor
            · rfl
            · show (a.1, a.2) + edir true = (a.1 + 1, a.2)
              rw [show edir true = ((1 : ℤ), (0 : ℤ)) from rfl]
              show (a.1 + 1, a.2 + 0) = (a.1 + 1, a.2)
              rw [add_zero]
          · refine Relation.ReflTransGen.head
              (b := (a.1 - 1, a.2))
              ⟨((a.1 - 1, a.2), true), Or.inr ?_⟩
              (ih (a.1 - 1, a.2) b (by simp; omega))
            constructor
            · rfl
            · show (a.1 - 1, a.2) + edir true = (a.1, a.2)
              rw [show edir true = ((1 : ℤ), (0 : ℤ)) from rfl]
              show (a.1 - 1 + 1, a.2 + 0) = (a.1, a.2)
              rw [add_zero]
              congr 1
              ring
  exact hkey _ a b rfl

/-- First crossing: a path from inside a set to outside contains a
crossing step. -/
theorem first_crossing {r : V2 → V2 → Prop} {P : V2 → Prop}
    {v w : V2} (hpath : Relation.ReflTransGen r v w)
    (hv : P v) (hw : ¬ P w) :
    ∃ x y, P x ∧ ¬ P y ∧ r x y := by
  induction hpath with
  | refl => exact absurd hv hw
  | tail hab hbc ih =>
      rename_i b c
      by_cases hPb : P b
      · exact ⟨b, c, hPb, hw, hbc⟩
      · exact ih hPb

/-- Non-escape propagates along cluster-avoiding walks. -/
theorem reach_not_esc {σ : PlusBC Λ} {v w : V2}
    (hv : ¬ escV σ v)
    (hreach : Relation.ReflTransGen
      (fun a b => IAdj a b ∧ b ∉ minusCl σ) v w) :
    ¬ escV σ w := by
  rintro ⟨u, hu, hp⟩
  exact hv ⟨u, hu, hreach.trans hp⟩

/-- Reversal of paths over a symmetric step relation. -/
theorem reflTransGen_symm {r : V2 → V2 → Prop}
    (hsym : ∀ a b, r a b → r b a) {a b : V2}
    (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      exact Relation.ReflTransGen.head (hsym _ _ hbc) ih

/-- The connectivity step relation of the filled cluster. -/
def FillStep (σ : PlusBC Λ) (a b : V2) : Prop :=
  IAdj a b ∧ a ∈ fillCl σ ∧ b ∈ fillCl σ

theorem fillStep_symm (σ : PlusBC Λ) :
    ∀ a b, FillStep σ a b → FillStep σ b a :=
  fun _ _ ⟨h1, h2, h3⟩ => ⟨iAdj_symm h1, h3, h2⟩

/-- Lifting a minus-cluster path to a filled-cluster path. -/
theorem minus_path_lift {σ : PlusBC Λ} {w : V2}
    (hw : Relation.ReflTransGen
      (fun a b => IAdj a b ∧ σ.1 b = false) 0 w) :
    Relation.ReflTransGen (FillStep σ) 0 w ∧ w ∈ minusCl σ := by
  induction hw with
  | refl =>
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail hab hbc ih =>
      rename_i b c
      obtain ⟨hpath, hbmem⟩ := ih
      have hcmem : c ∈ minusCl σ :=
        Relation.ReflTransGen.tail hbmem hbc
      exact ⟨hpath.tail ⟨hbc.1, Or.inl hbmem, Or.inl hcmem⟩, hcmem⟩

/-- Lifting a cluster-avoiding reach path from a non-escaping point
to a filled-cluster path. -/
theorem avoid_path_lift {σ : PlusBC Λ} {v z : V2}
    (hv : ¬ escV σ v)
    (hz : Relation.ReflTransGen
      (fun a b => IAdj a b ∧ b ∉ minusCl σ) v z) :
    Relation.ReflTransGen (FillStep σ) v z := by
  induction hz with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      rename_i b c
      have hbfill : b ∈ fillCl σ := Or.inr (reach_not_esc hv hab)
      have hcfill : c ∈ fillCl σ :=
        Or.inr (reach_not_esc hv (hab.tail hbc))
      exact ih.tail ⟨hbc.1, hbfill, hcfill⟩

/-- **Layer B (main): the filled cluster is connected** — every site
of `fillCl σ` is joined to the origin within the filled cluster. -/
theorem fillCl_connected {σ : PlusBC Λ} {v : V2}
    (hv : v ∈ fillCl σ) :
    Relation.ReflTransGen (FillStep σ) 0 v := by
  rcases Classical.em (v ∈ minusCl σ) with hm | hm
  · exact (minus_path_lift hm).1
  · have hesc : ¬ escV σ v := by
      rcases hv with h | h
      · exact absurd h hm
      · exact h
    obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset Λ
    have hlat := lattice_connected v w
    set P : V2 → Prop := fun x => Relation.ReflTransGen
      (fun a b => IAdj a b ∧ b ∉ minusCl σ) v x with hP
    have hPv : P v := Relation.ReflTransGen.refl
    have hPw : ¬ P w := fun hp => hesc ⟨w, hw, hp⟩
    obtain ⟨x, y, hPx, hPy, hxy⟩ := first_crossing hlat hPv hPw
    have hymem : y ∈ minusCl σ := by
      by_contra hym
      exact hPy (hPx.tail ⟨hxy, hym⟩)
    have hxfill : x ∈ fillCl σ := Or.inr (reach_not_esc hesc hPx)
    have hpath0y := (minus_path_lift hymem).1
    have hpathvx := avoid_path_lift hesc hPx
    have hpath0x : Relation.ReflTransGen (FillStep σ) 0 x :=
      hpath0y.tail ⟨iAdj_symm hxy, Or.inl hymem, hxfill⟩
    exact hpath0x.trans (reflTransGen_symm (fillStep_symm σ) hpathvx)

/-! ## Layer C0: the column-parity interior (inverse Jordan calculus)

For a finite edge set `C`, `InsideP C x` holds when an odd number of
vertical `C`-edges lies in the column above `x`.  The key facts:

* vertical edges flip the parity by definition;
* **horizontal edges flip the parity iff they belong to `C`**,
  *given* even corner degrees — by the telescoping corner-parity
  induction down the double column (`insideP_horiz`);
* far-above sites are outside (`insideP_far`).

Together these give `∂(Inside C) = C` for every finite
even-corner-degree `C` — a discrete inverse Jordan theorem with no
curves, winding numbers, or connectivity. -/

open Classical in
/-- The number of vertical `C`-edges in the column at and above `x`. -/
noncomputable def colCount (C : Finset IEdge) (x : V2) : ℕ :=
  (C.filter (fun e => e.2 = false ∧ e.1.1 = x.1 ∧ x.2 ≤ e.1.2)).card

/-- The column-parity interior. -/
def InsideP (C : Finset IEdge) (x : V2) : Prop :=
  colCount C x % 2 = 1

open Classical in
/-- Vertical step: crossing the column edge flips the parity. -/
theorem colCount_step (C : Finset IEdge) (x₁ y : ℤ) :
    colCount C (x₁, y)
      = colCount C (x₁, y + 1)
        + (if ((x₁, y), false) ∈ C then 1 else 0) := by
  unfold colCount
  rcases Classical.em ((((x₁, y), false) : IEdge) ∈ C) with hg | hg
  · rw [if_pos hg]
    have hsplit : C.filter (fun e => e.2 = false ∧ e.1.1 = x₁ ∧ y ≤ e.1.2)
        = insert (((x₁, y), false) : IEdge)
            (C.filter (fun e => e.2 = false ∧ e.1.1 = x₁
              ∧ y + 1 ≤ e.1.2)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨heC, h2, h3, h4⟩
        rcases eq_or_lt_of_le h4 with heq | hlt
        · left
          obtain ⟨⟨e1, e2⟩, eb⟩ := e
          simp only [Prod.mk.injEq]
          constructor
          · constructor
            · exact h3
            · exact heq.symm
          · cases eb
            · rfl
            · exact absurd h2 (by simp)
        · right
          exact ⟨heC, h2, h3, by omega⟩
      · rintro (rfl | ⟨heC, h2, h3, h4⟩)
        · exact ⟨hg, rfl, rfl, le_refl y⟩
        · exact ⟨heC, h2, h3, by omega⟩
    rw [hsplit, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_filter]
      rintro ⟨-, -, -, h4⟩
      omega)]
  · rw [if_neg hg, add_zero]
    congr 1
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨heC, h2, h3, h4⟩
      refine ⟨heC, h2, h3, ?_⟩
      rcases eq_or_lt_of_le h4 with heq | hlt
      · exfalso
        apply hg
        obtain ⟨⟨e1, e2⟩, eb⟩ := e
        have hb : eb = false := h2
        have h1' : e1 = x₁ := h3
        have h2' : e2 = y := heq.symm
        rw [hb, h1', h2'] at heC
        exact heC
      · omega
    · rintro ⟨heC, h2, h3, h4⟩
      exact ⟨heC, h2, h3, by omega⟩

open Classical in
/-- Far above every edge of `C`, the parity is off. -/
theorem colCount_far (C : Finset IEdge) (x₁ : ℤ) {y : ℤ}
    (hy : ∀ e ∈ C, e.1.2 < y) :
    colCount C (x₁, y) = 0 := by
  unfold colCount
  rw [Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  rintro e heC ⟨-, -, h3⟩
  exact absurd h3 (by have := hy e heC; omega)

open Classical in
/-- The corner degree of a finite edge set. -/
noncomputable def cornerDegF (C : Finset IEdge) (v : V2) : ℕ :=
  (cornerEdges v).countP (fun e => decide (e ∈ C))

open Classical in
/-- **The telescoping corner-parity theorem**: for an edge set with
even corner degrees, the joint parity of the two columns at `x₁` and
`x₁ + 1` differs exactly by the horizontal edge between them — the
mod-2 sum `colCount(x₁,y) + colCount(x₁+1,y) + [((x₁,y),true) ∈ C]`
vanishes, by downward induction with the corner degree at `(x₁, y)`
as the telescoping term. -/
theorem colCount_horiz (C : Finset IEdge)
    (hev : ∀ v, cornerDegF C v % 2 = 0) (x₁ y : ℤ) :
    (colCount C (x₁, y) + colCount C (x₁ + 1, y)
      + (if ((x₁, y), true) ∈ C then 1 else 0)) % 2 = 0 := by
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ, ∀ e ∈ C, e.1.2 < Y := by
    rcases Finset.eq_empty_or_nonempty C with rfl | hne
    · exact ⟨0, by simp⟩
    · refine ⟨(C.image (fun e => e.1.2)).max' (hne.image _) + 1,
        fun e he => ?_⟩
      have := Finset.le_max' (C.image (fun e => e.1.2)) _
        (Finset.mem_image_of_mem _ he)
      omega
  suffices h : ∀ n : ℕ, ∀ y : ℤ, Y - y ≤ (n : ℤ) →
      (colCount C (x₁, y) + colCount C (x₁ + 1, y)
        + (if ((x₁, y), true) ∈ C then 1 else 0)) % 2 = 0 by
    refine h (Y - y).toNat y ?_
    exact Int.self_le_toNat _
  intro n
  induction n with
  | zero =>
      intro y hy
      have hfar1 : colCount C (x₁, y) = 0 :=
        colCount_far C x₁ (fun e he => by have := hY e he; omega)
      have hfar2 : colCount C (x₁ + 1, y) = 0 :=
        colCount_far C (x₁ + 1) (fun e he => by have := hY e he; omega)
      have hg : (((x₁, y), true) : IEdge) ∉ C := by
        intro hmem
        have := hY _ hmem
        simp at this
        omega
      rw [hfar1, hfar2, if_neg hg]
  | succ n ih =>
      intro y hy
      by_cases hytop : Y ≤ y
      · have hfar1 : colCount C (x₁, y) = 0 :=
          colCount_far C x₁ (fun e he => by have := hY e he; omega)
        have hfar2 : colCount C (x₁ + 1, y) = 0 :=
          colCount_far C (x₁ + 1)
            (fun e he => by have := hY e he; omega)
        have hg : (((x₁, y), true) : IEdge) ∉ C := by
          intro hmem
          have := hY _ hmem
          simp at this
          omega
        rw [hfar1, hfar2, if_neg hg]
      · have hIH := ih (y + 1) (by omega)
        have hstepW := colCount_step C x₁ y
        have hstepE := colCount_step C (x₁ + 1) y
        have hc := hev (x₁, y)
        unfold cornerDegF cornerEdges at hc
        rw [List.countP_cons, List.countP_cons, List.countP_cons,
          List.countP_cons, List.countP_nil] at hc
        rcases Classical.em ((((x₁, y), true) : IEdge) ∈ C)
            with hS | hS <;>
          rcases Classical.em ((((x₁, y + 1), true) : IEdge) ∈ C)
            with hN | hN <;>
          rcases Classical.em ((((x₁, y), false) : IEdge) ∈ C)
            with hW | hW <;>
          rcases Classical.em ((((x₁ + 1, y), false) : IEdge) ∈ C)
            with hE | hE <;>
          simp only [hS, hN, hW, hE, if_pos, if_neg, decide_eq_true_eq,
            not_false_eq_true, decide_true, decide_false,
            if_true, if_false, Bool.false_eq_true]
            at hstepW hstepE hIH hc ⊢ <;>
          omega

open Classical in
/-- **Vertical flip**: interior membership flips across a column edge
exactly when the edge belongs to `C`. -/
theorem insideP_flip_vert (C : Finset IEdge) (x₁ y : ℤ) :
    ((InsideP C (x₁, y)) ↔ ¬ InsideP C (x₁, y + 1))
      ↔ (((x₁, y), false) : IEdge) ∈ C := by
  have h := colCount_step C x₁ y
  unfold InsideP
  rcases Classical.em ((((x₁, y), false) : IEdge) ∈ C) with hg | hg
  · rw [if_pos hg] at h
    simp only [hg, iff_true]
    omega
  · rw [if_neg hg, add_zero] at h
    simp only [hg, iff_false]
    omega

open Classical in
/-- **Horizontal flip**: given even corner degrees, interior
membership flips across a horizontal edge exactly when the edge
belongs to `C` — the telescoping theorem in flip form. -/
theorem insideP_flip_horiz (C : Finset IEdge)
    (hev : ∀ v, cornerDegF C v % 2 = 0) (x₁ y : ℤ) :
    ((InsideP C (x₁, y)) ↔ ¬ InsideP C (x₁ + 1, y))
      ↔ (((x₁, y), true) : IEdge) ∈ C := by
  have h := colCount_horiz C hev x₁ y
  unfold InsideP
  rcases Classical.em ((((x₁, y), true) : IEdge) ∈ C) with hg | hg
  · rw [if_pos hg] at h
    simp only [hg, iff_true]
    omega
  · rw [if_neg hg, add_zero] at h
    simp only [hg, iff_false]
    omega

open Classical in
/-- **The inverse Jordan theorem (edge form)**: for a finite edge set
with even corner degrees, an edge lies in `C` exactly when the
column-parity interior changes across it —
`∂(InsideP C) = C`. -/
theorem insideP_boundary (C : Finset IEdge)
    (hev : ∀ v, cornerDegF C v % 2 = 0) (e : IEdge) :
    ((InsideP C (ep0 e)) ↔ ¬ InsideP C (ep1 e)) ↔ e ∈ C := by
  obtain ⟨⟨x, y⟩, β⟩ := e
  cases β
  · have hp0 : ep0 (((x, y), false) : IEdge) = (x, y) := rfl
    have hp1 : ep1 (((x, y), false) : IEdge) = (x, y + 1) := by
      show (x, y) + edir false = (x, y + 1)
      rw [show edir false = ((0 : ℤ), (1 : ℤ)) from rfl]
      show (x + 0, y + 1) = (x, y + 1)
      rw [add_zero]
    rw [hp0, hp1]
    exact insideP_flip_vert C x y
  · have hp0 : ep0 (((x, y), true) : IEdge) = (x, y) := rfl
    have hp1 : ep1 (((x, y), true) : IEdge) = (x + 1, y) := by
      show (x, y) + edir true = (x + 1, y)
      rw [show edir true = ((1 : ℤ), (0 : ℤ)) from rfl]
      show (x + 1, y + 0) = (x + 1, y)
      rw [add_zero]
    rw [hp0, hp1]
    exact insideP_flip_horiz C hev x y

open Classical in
/-- **The recovery identification**: the column-parity interior of
the contour is exactly the filled cluster — `Inside(∂ fillCl) =
fillCl`, by the single-column downward induction in which parity and
membership flip together across every column edge. -/
theorem insideP_contour {σ : PlusBC Λ} (h0 : σ.1 0 = false)
    (x : V2) : InsideP (contour σ) x ↔ x ∈ fillCl σ := by
  -- a height bound for the volume and the contour
  obtain ⟨Y, hYΛ⟩ : ∃ Y : ℤ, ∀ v ∈ Λ, v.2 < Y := by
    rcases Finset.eq_empty_or_nonempty Λ with rfl | hne
    · exact ⟨0, by simp⟩
    · refine ⟨(Λ.image (fun v => v.2)).max' (hne.image _) + 1,
        fun v hv => ?_⟩
      have := Finset.le_max' (Λ.image (fun v => v.2)) _
        (Finset.mem_image_of_mem _ hv)
      omega
  have hYγ : ∀ e ∈ contour σ, e.1.2 < Y + 1 := by
    intro e he
    have heV : e ∈ eVol Λ := (Finset.mem_filter.mp he).1
    rcases (mem_eVol Λ).mp heV with h | h
    · have := hYΛ _ h
      show e.1.2 < Y + 1
      unfold ep0 at this
      omega
    · have := hYΛ _ h
      obtain ⟨⟨e1, e2⟩, eb⟩ := e
      cases eb
      · have h1 : ep1 (((e1, e2), false) : IEdge) = (e1, e2 + 1) := by
          show (e1, e2) + edir false = (e1, e2 + 1)
          rw [show edir false = ((0 : ℤ), (1 : ℤ)) from rfl]
          show (e1 + 0, e2 + 1) = (e1, e2 + 1)
          rw [add_zero]
        rw [h1] at this
        show e2 < Y + 1
        simp at this
        omega
      · have h1 : ep1 (((e1, e2), true) : IEdge) = (e1 + 1, e2) := by
          show (e1, e2) + edir true = (e1 + 1, e2)
          rw [show edir true = ((1 : ℤ), (0 : ℤ)) from rfl]
          show (e1 + 1, e2 + 0) = (e1 + 1, e2)
          rw [add_zero]
        rw [h1] at this
        show e2 < Y + 1
        simp at this
        omega
  obtain ⟨x₁, y⟩ := x
  -- downward induction on the column
  suffices h : ∀ n : ℕ, ∀ z : ℤ, Y + 1 - z ≤ (n : ℤ) →
      (InsideP (contour σ) (x₁, z) ↔ (x₁, z) ∈ fillCl σ) by
    exact h (Y + 1 - y).toNat y (Int.self_le_toNat _)
  intro n
  induction n with
  | zero =>
      intro z hz
      have hfar : colCount (contour σ) (x₁, z) = 0 :=
        colCount_far _ x₁ (fun e he => by have := hYγ e he; omega)
      have hnot : (x₁, z) ∉ fillCl σ := by
        intro hmem
        have := hYΛ _ (fillCl_subset h0 hmem)
        simp at this
        omega
      unfold InsideP
      rw [hfar]
      simp [hnot]
  | succ n ih =>
      intro z hz
      by_cases hztop : Y + 1 ≤ z
      · have hfar : colCount (contour σ) (x₁, z) = 0 :=
          colCount_far _ x₁ (fun e he => by have := hYγ e he; omega)
        have hnot : (x₁, z) ∉ fillCl σ := by
          intro hmem
          have := hYΛ _ (fillCl_subset h0 hmem)
          simp at this
          omega
        unfold InsideP
        rw [hfar]
        simp [hnot]
      · have hIH := ih (z + 1) (by omega)
        have hflip := insideP_flip_vert (contour σ) x₁ z
        -- the membership flip across the column edge
        have hmemflip :
            ((x₁, z) ∈ fillCl σ ↔ ¬ ((x₁, z + 1) ∈ fillCl σ))
              ↔ (((x₁, z), false) : IEdge) ∈ contour σ := by
          have hcoe := coe_contour h0 (Λ := Λ) (σ := σ)
          have hmem : ((((x₁, z), false) : IEdge) ∈ contour σ)
              ↔ (((x₁, z), false) : IEdge) ∈ obdry (fillCl σ) := by
            constructor
            · intro hm
              have : (((x₁, z), false) : IEdge)
                  ∈ (↑(contour σ) : Set IEdge) := hm
              rwa [hcoe] at this
            · intro hm
              have : (((x₁, z), false) : IEdge)
                  ∈ (↑(contour σ) : Set IEdge) := by
                rw [hcoe]
                exact hm
              exact this
          rw [hmem]
          have hp1 : ep1 (((x₁, z), false) : IEdge) = (x₁, z + 1) := by
            show (x₁, z) + edir false = (x₁, z + 1)
            rw [show edir false = ((0 : ℤ), (1 : ℤ)) from rfl]
            show (x₁ + 0, z + 1) = (x₁, z + 1)
            rw [add_zero]
          constructor
          · intro hiff
            show (((x₁, z), false) : IEdge) ∈ obdry (fillCl σ)
            unfold obdry
            rw [Set.mem_setOf_eq, hp1]
            rcases Classical.em ((x₁, z) ∈ fillCl σ) with h1 | h1
            · exact Or.inl ⟨h1, hiff.mp h1⟩
            · refine Or.inr ⟨h1, ?_⟩
              by_contra h2
              exact h1 (hiff.mpr h2)
          · intro hob
            unfold obdry at hob
            rw [Set.mem_setOf_eq, hp1] at hob
            rcases hob with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨fun _ => h2, fun _ => h1⟩
            · exact ⟨fun h => absurd h h1, fun hn => absurd h2 hn⟩
        rcases Classical.em ((((x₁, z), false) : IEdge) ∈ contour σ)
            with hg | hg
        · have h1 := hflip.mpr hg
          have h2 := hmemflip.mpr hg
          constructor
          · intro hin
            rcases Classical.em ((x₁, z) ∈ fillCl σ) with hf | hf
            · exact hf
            · exfalso
              have h3 : ¬ InsideP (contour σ) (x₁, z + 1) := h1.mp hin
              have h4 : (x₁, z + 1) ∈ fillCl σ := by
                by_contra h5
                exact hf (h2.mpr h5)
              exact h3 (hIH.mpr h4)
          · intro hf
            rcases Classical.em (InsideP (contour σ) (x₁, z))
                with hin | hin
            · exact hin
            · exfalso
              have h3 : ¬ ((x₁, z + 1) ∈ fillCl σ) := h2.mp hf
              have h4 : InsideP (contour σ) (x₁, z + 1) := by
                by_contra h5
                exact hin (h1.mpr h5)
              exact h3 (hIH.mp h4)
        · have h1 : ¬ ((InsideP (contour σ) (x₁, z))
              ↔ ¬ InsideP (contour σ) (x₁, z + 1)) := by
            intro hiff
            exact hg (hflip.mp hiff)
          have h2 : ¬ (((x₁, z) ∈ fillCl σ)
              ↔ ¬ ((x₁, z + 1) ∈ fillCl σ)) := by
            intro hiff
            exact hg (hmemflip.mp hiff)
          constructor
          · intro hin
            by_contra hf
            apply h2
            constructor
            · intro h3
              exact absurd h3 hf
            · intro h3
              exfalso
              rcases Classical.em ((x₁, z + 1) ∈ fillCl σ) with h4 | h4
              · exact h3 h4
              · have h5 : ¬ InsideP (contour σ) (x₁, z + 1) :=
                  fun h6 => h4 (hIH.mp h6)
                exact h1 ⟨fun _ => h5, fun _ => hin⟩
          · intro hf
            by_contra hin
            apply h1
            constructor
            · intro h3
              exact absurd h3 hin
            · intro h3
              exfalso
              rcases Classical.em ((x₁, z + 1) ∈ fillCl σ) with h4 | h4
              · exact h3 (hIH.mpr h4)
              · exact h2 ⟨fun _ => h4, fun _ => hf⟩

/-! ## Layer C1: the contour admits no proper even decomposition -/

open Classical in
/-- No flip across an edge outside `C`. -/
theorem insideP_const_of_notMem (C : Finset IEdge)
    (hev : ∀ v, cornerDegF C v % 2 = 0) {e : IEdge} (he : e ∉ C) :
    (InsideP C (ep0 e) ↔ InsideP C (ep1 e)) := by
  have h := insideP_boundary C hev e
  rcases Classical.em (InsideP C (ep0 e)) with h0 | h0 <;>
    rcases Classical.em (InsideP C (ep1 e)) with h1 | h1
  · exact ⟨fun _ => h1, fun _ => h0⟩
  · exact absurd (h.mp ⟨fun _ => h1, fun _ => h0⟩) he
  · exact absurd (h.mp ⟨fun hh => absurd hh h0,
      fun hn => absurd h1 hn⟩) he
  · exact ⟨fun hh => absurd hh h0, fun hh => absurd hh h1⟩

open Classical in
/-- Constancy across an adjacency step whose realizing edges avoid
`C`. -/
theorem insideP_const_step (C : Finset IEdge)
    (hev : ∀ v, cornerDegF C v % 2 = 0) {a b : V2}
    (hadj : IAdj a b)
    (havoid : ∀ e : IEdge,
      ((ep0 e = a ∧ ep1 e = b) ∨ (ep0 e = b ∧ ep1 e = a)) →
        e ∉ C) :
    (InsideP C a ↔ InsideP C b) := by
  obtain ⟨e, hcase⟩ := hadj
  have hnot := havoid e hcase
  have hconst := insideP_const_of_notMem C hev hnot
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]
    exact hconst
  · rw [← h1, ← h2]
    exact hconst.symm

open Classical in
/-- Corner degrees are additive on a partition of an edge set. -/
theorem cornerDegF_sdiff (C D : Finset IEdge) (hCD : C ⊆ D)
    (v : V2) :
    cornerDegF C v + cornerDegF (D \ C) v = cornerDegF D v := by
  unfold cornerDegF
  induction cornerEdges v with
  | nil => simp
  | cons a l ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons]
      rcases Classical.em (a ∈ C) with haC | haC
      · have haD : a ∈ D := hCD haC
        have haDC : a ∉ D \ C := by
          simp [Finset.mem_sdiff, haC]
        simp only [haC, haD, haDC, decide_true, decide_false,
          if_true, if_false, Bool.false_eq_true, ite_true, ite_false]
        omega
      · rcases Classical.em (a ∈ D) with haD | haD
        · have haDC : a ∈ D \ C := Finset.mem_sdiff.mpr ⟨haD, haC⟩
          simp only [haC, haD, haDC, decide_true, decide_false,
            if_true, if_false, Bool.false_eq_true, ite_true,
            ite_false]
          omega
        · have haDC : a ∉ D \ C := by
            simp [Finset.mem_sdiff, haD]
          simp only [haC, haD, haDC, decide_true, decide_false,
            if_true, if_false, Bool.false_eq_true, ite_true,
            ite_false]
          omega

open Classical in
/-- Column counts are additive on a partition of an edge set. -/
theorem colCount_sdiff (C D : Finset IEdge) (hCD : C ⊆ D) (x : V2) :
    colCount C x + colCount (D \ C) x = colCount D x := by
  unfold colCount
  rw [← Finset.card_union_of_disjoint (by
    refine Finset.disjoint_filter_filter ?_
    exact Finset.disjoint_sdiff)]
  congr 1
  ext e
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨⟨h1, -⟩, h2⟩)
    · exact ⟨hCD h1, h2⟩
    · exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rcases Classical.em (e ∈ C) with hC | hC
    · exact Or.inl ⟨hC, h2⟩
    · exact Or.inr ⟨⟨h1, hC⟩, h2⟩

open Classical in
/-- The contour has even corner degrees (Finset form of Layer A). -/
theorem cornerDegF_contour_even {σ : PlusBC Λ}
    (h0 : σ.1 0 = false) (v : V2) :
    cornerDegF (contour σ) v % 2 = 0 := by
  have h := cornerDegree_even (fillCl σ) v
  have hcong : cornerDegF (contour σ) v
      = cornerDegree (fillCl σ) v := by
    unfold cornerDegF cornerDegree
    refine List.countP_congr fun e he => ?_
    have hcoe := coe_contour h0 (Λ := Λ) (σ := σ)
    rcases Classical.em (e ∈ contour σ) with hm | hm
    · have : e ∈ obdry (fillCl σ) := by
        rw [← hcoe]
        exact hm
      simp [hm, this]
    · have : e ∉ obdry (fillCl σ) := by
        rw [← hcoe]
        exact hm
      simp [hm, this]
  rw [hcong]
  exact h

open Classical in
/-- Strengthened first crossing: the crossing step comes with the
suffix path continuing to the endpoint. -/
theorem first_crossing' {r : V2 → V2 → Prop} {P : V2 → Prop}
    {v w : V2} (hpath : Relation.ReflTransGen r v w)
    (hv : P v) :
    ¬ P w →
    ∃ x y, P x ∧ ¬ P y ∧ r x y ∧ Relation.ReflTransGen r y w := by
  induction hpath with
  | refl => exact fun hw => absurd hv hw
  | tail hab hbc ih =>
      rename_i b c
      intro hw
      by_cases hPb : P b
      · exact ⟨b, c, hPb, hw, hbc, Relation.ReflTransGen.refl⟩
      · obtain ⟨x, y, h1, h2, h3, h4⟩ := ih hPb
        exact ⟨x, y, h1, h2, h3, h4.tail hbc⟩

/-- Off-volume walks stay off the volume. -/
theorem reach_offVol {w z : V2} (hw : w ∉ Λ)
    (h : Relation.ReflTransGen
      (fun a b => IAdj a b ∧ b ∉ Λ) w z) :
    z ∉ Λ := by
  induction h with
  | refl => exact hw
  | tail hab hbc ih => exact hbc.2

open Classical in
/-- Volume edges lie strictly below any level above the volume. -/
theorem eVol_base_lt {Y : ℤ} (hY : ∀ v ∈ Λ, v.2 < Y) :
    ∀ e ∈ eVol Λ, e.1.2 < Y := by
  intro e heV
  rcases (mem_eVol Λ).mp heV with h | h
  · exact hY _ h
  · have := hY _ h
    obtain ⟨⟨e1, e2⟩, eb⟩ := e
    cases eb
    · have h1 : ep1 (((e1, e2), false) : IEdge) = (e1, e2 + 1) := by
        show (e1, e2) + edir false = (e1, e2 + 1)
        rw [show edir false = ((0 : ℤ), (1 : ℤ)) from rfl]
        show (e1 + 0, e2 + 1) = (e1, e2 + 1)
        rw [add_zero]
      rw [h1] at this
      show e2 < Y
      simp at this
      omega
    · have h1 : ep1 (((e1, e2), true) : IEdge) = (e1 + 1, e2) := by
        show (e1, e2) + edir true = (e1 + 1, e2)
        rw [show edir true = ((1 : ℤ), (0 : ℤ)) from rfl]
        show (e1 + 1, e2 + 0) = (e1 + 1, e2)
        rw [add_zero]
      rw [h1] at this
      show e2 < Y
      simp at this
      omega

open Classical in
/-- Interior membership for a sub-volume edge set is constant along
off-volume walks. -/
theorem insideP_const_offVol {C : Finset IEdge}
    (hCV : C ⊆ eVol Λ)
    (hev : ∀ v, cornerDegF C v % 2 = 0) {w z : V2} (hw : w ∉ Λ)
    (h : Relation.ReflTransGen
      (fun a b => IAdj a b ∧ b ∉ Λ) w z) :
    (InsideP C w ↔ InsideP C z) := by
  induction h with
  | refl => exact Iff.rfl
  | tail hab hbc ih =>
      rename_i b c
      have hbΛ : b ∉ Λ := reach_offVol hw hab
      refine ih.trans (insideP_const_step C hev hbc.1 ?_)
      intro e hcase heC
      have heV := hCV heC
      rcases (mem_eVol Λ).mp heV with h1 | h1
      · rcases hcase with ⟨h2, -⟩ | ⟨h2, -⟩
        · exact hbΛ (by rw [← h2]; exact h1)
        · exact hbc.2 (by rw [← h2]; exact h1)
      · rcases hcase with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact hbc.2 (by rw [← h2]; exact h1)
        · exact hbΛ (by rw [← h2]; exact h1)

open Classical in
/-- Interior membership for an even-corner subset of the contour is
constant along the filled cluster. -/
theorem insideP_const_fillCl {σ : PlusBC Λ} {C : Finset IEdge}
    (hsub : C ⊆ contour σ)
    (hev : ∀ v, cornerDegF C v % 2 = 0) {a b : V2}
    (h : Relation.ReflTransGen (FillStep σ) a b) :
    (InsideP C a ↔ InsideP C b) := by
  induction h with
  | refl => exact Iff.rfl
  | tail hab hbc ih =>
      rename_i b c
      refine ih.trans (insideP_const_step C hev hbc.1 ?_)
      intro e hcase heC
      have hbd : e ∈ obdry (fillCl σ) :=
        (Finset.mem_filter.mp (hsub heC)).2
      rcases hbd with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact h2 (by rw [e2]; exact hbc.2.2)
        · exact h2 (by rw [e2]; exact hbc.2.1)
      · rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact h1 (by rw [e1]; exact hbc.2.1)
        · exact h1 (by rw [e1]; exact hbc.2.2)

open Classical in
/-- **The pocket lemma**: an even-corner subset of the contour whose
interior misses the origin is empty.  The hypothesis `hcompl` says
the complement of the volume escapes upward — the volumes of the
manuscript (boxes) satisfy it; "Swiss-cheese" volumes genuinely
violate the circuit count. -/
theorem even_subset_eq_empty {σ : PlusBC Λ} (h0 : σ.1 0 = false)
    (hcompl : ∀ w : V2, w ∉ Λ → ∃ z : V2,
      (∀ v ∈ Λ, v.2 < z.2) ∧
      Relation.ReflTransGen (fun a b => IAdj a b ∧ b ∉ Λ) w z)
    {C : Finset IEdge} (hsub : C ⊆ contour σ)
    (hev : ∀ v, cornerDegF C v % 2 = 0)
    (hzero : ¬ InsideP C 0) :
    C = ∅ := by
  -- the interior misses the whole filled cluster
  have hfill : ∀ x, x ∈ fillCl σ → ¬ InsideP C x := by
    intro x hx hIx
    exact hzero ((insideP_const_fillCl hsub hev
      (fillCl_connected hx)).mpr hIx)
  have hCV : C ⊆ eVol Λ :=
    fun e he => (Finset.mem_filter.mp (hsub he)).1
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e heC
  have hbd : e ∈ obdry (fillCl σ) :=
    (Finset.mem_filter.mp (hsub heC)).2
  have hflip := (insideP_boundary C hev e).mpr heC
  -- the outside endpoint of the edge lies in the pocket
  obtain ⟨q, hqI, hqf⟩ : ∃ q, InsideP C q ∧ q ∉ fillCl σ := by
    rcases hbd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨ep1 e, ?_, h2⟩
      by_contra hq
      exact (hfill _ h1) (hflip.mpr hq)
    · exact ⟨ep0 e, hflip.mpr (hfill _ h2), h1⟩
  -- pocket sites escape the minus cluster
  have hq' : q ∉ minusCl σ ∧ escV σ q := by
    by_cases hm : q ∈ minusCl σ
    · exact absurd (Or.inl hm : q ∈ fillCl σ) hqf
    · refine ⟨hm, ?_⟩
      by_contra hne
      exact hqf (Or.inr hne)
  obtain ⟨hqm, w, hwΛ, hqw⟩ := hq'
  by_cases hwP : InsideP C w
  · -- the escape endpoint is still in the pocket: walk it upward
    obtain ⟨z, hzY, hzpath⟩ := hcompl w hwΛ
    have hzI : InsideP C z :=
      (insideP_const_offVol hCV hev hwΛ hzpath).mp hwP
    have hz0 : colCount C z = 0 :=
      colCount_far C z.1 fun e' he' =>
        eVol_base_lt hzY e' (hCV he')
    unfold InsideP at hzI
    omega
  · -- the escape path exits the pocket: the crossing edge is a
    -- contour edge whose cluster endpoint both escapes and cannot
    obtain ⟨x, y, hPx, hPy, hxy, hsuf⟩ :=
      first_crossing' hqw hqI hwP
    obtain ⟨e', hcase⟩ := hxy.1
    have he'C : e' ∈ C := by
      by_contra he'
      have hconst := insideP_const_of_notMem C hev he'
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hconst
        exact hPy (hconst.mp hPx)
      · rw [h1, h2] at hconst
        exact hPy (hconst.mpr hPx)
    have hbd' : e' ∈ obdry (fillCl σ) :=
      (Finset.mem_filter.mp (hsub he'C)).2
    have hxout : x ∉ fillCl σ := fun hx => hfill x hx hPx
    have hyfill : y ∈ fillCl σ := by
      rcases hbd' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact absurd (show x ∈ fillCl σ by
            rw [← e1]; exact h1) hxout
        · rw [← e1]; exact h1
      · rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [← e2]; exact h2
        · exact absurd (show x ∈ fillCl σ by
            rw [← e2]; exact h2) hxout
    have hyesc : escV σ y := ⟨w, hwΛ, hsuf⟩
    rcases hyfill with hm | hne
    · exact hxy.2 hm
    · exact hne hyesc

open Classical in
/-- **C1 — no proper even decomposition**: an even-corner subset of
the contour is empty or the whole contour.  This is the discrete
Jordan engine: it forces the contour to be a single circuit. -/
theorem contour_even_split {σ : PlusBC Λ} (h0 : σ.1 0 = false)
    (hcompl : ∀ w : V2, w ∉ Λ → ∃ z : V2,
      (∀ v ∈ Λ, v.2 < z.2) ∧
      Relation.ReflTransGen (fun a b => IAdj a b ∧ b ∉ Λ) w z)
    {C : Finset IEdge} (hsub : C ⊆ contour σ)
    (hev : ∀ v, cornerDegF C v % 2 = 0) :
    C = ∅ ∨ C = contour σ := by
  have hevγ : ∀ v, cornerDegF (contour σ) v % 2 = 0 :=
    fun v => cornerDegF_contour_even h0 v
  have hev' : ∀ v, cornerDegF (contour σ \ C) v % 2 = 0 := by
    intro v
    have hadd := cornerDegF_sdiff C (contour σ) hsub v
    have h1 := hev v
    have h2 := hevγ v
    omega
  have h0in : InsideP (contour σ) 0 :=
    (insideP_contour h0 0).mpr (zero_mem_fillCl σ)
  have hadd := colCount_sdiff C (contour σ) hsub 0
  by_cases hz : InsideP C 0
  · right
    have hz' : ¬ InsideP (contour σ \ C) 0 := by
      unfold InsideP at h0in hz ⊢
      omega
    have hempty := even_subset_eq_empty h0 hcompl
      Finset.sdiff_subset hev' hz'
    refine Finset.Subset.antisymm hsub fun e he => ?_
    by_contra hne
    have hmem : e ∈ contour σ \ C := Finset.mem_sdiff.mpr ⟨he, hne⟩
    rw [hempty] at hmem
    simp at hmem
  · left
    exact even_subset_eq_empty h0 hcompl hsub hev hz

/-! ## Layer D: the Euler listing

A maximal dual trail through the contour must close up (walk parity)
and must exhaust the contour (`contour_even_split`): the contour is
traceable as a single circuit. -/

/-- The corner across an edge. -/
def otherCorner (e : IEdge) (v : V2) : V2 :=
  if v = corner0 e then corner1 e else corner0 e

/-- A dual walk: successive edges pivot through shared corners. -/
def Walk : V2 → List IEdge → Prop
  | _, [] => True
  | v, e :: l => (v = corner0 e ∨ v = corner1 e)
      ∧ Walk (otherCorner e v) l

/-- The final corner of a walk. -/
def walkEnd (v : V2) (L : List IEdge) : V2 :=
  L.foldl (fun w e => otherCorner e w) v

theorem walkEnd_nil (v : V2) : walkEnd v [] = v := rfl

theorem walkEnd_cons (v : V2) (e : IEdge) (l : List IEdge) :
    walkEnd v (e :: l) = walkEnd (otherCorner e v) l := rfl

theorem walkEnd_append (e : IEdge) :
    ∀ (L : List IEdge) (v : V2),
    walkEnd v (L ++ [e]) = otherCorner e (walkEnd v L)
  | [], v => rfl
  | a :: l, v => by
      rw [List.cons_append, walkEnd_cons, walkEnd_cons,
        walkEnd_append e l]

/-- The two corners of an edge are distinct. -/
theorem corner0_ne_corner1 (e : IEdge) : corner0 e ≠ corner1 e := by
  obtain ⟨⟨x, y⟩, β⟩ := e
  cases β <;> simp [corner0, corner1, Prod.ext_iff] <;> omega

/-- Pivoting exchanges the two corners. -/
theorem otherCorner_cases {e : IEdge} {v : V2}
    (hv : v = corner0 e ∨ v = corner1 e) :
    (v = corner0 e ∧ otherCorner e v = corner1 e)
      ∨ (v = corner1 e ∧ otherCorner e v = corner0 e) := by
  rcases hv with h | h
  · refine Or.inl ⟨h, ?_⟩
    unfold otherCorner
    rw [if_pos h]
  · refine Or.inr ⟨h, ?_⟩
    have h' : ¬ (v = corner0 e) := fun hc =>
      corner0_ne_corner1 e (hc.symm.trans h)
    unfold otherCorner
    rw [if_neg h']

/-- The four corner edges are pairwise distinct. -/
theorem cornerEdges_nodup (v : V2) : (cornerEdges v).Nodup := by
  obtain ⟨x, y⟩ := v
  simp [cornerEdges, Prod.ext_iff]

/-- Counting a single element in a duplicate-free list. -/
theorem countP_single_of_nodup :
    ∀ (l : List IEdge), l.Nodup → ∀ (a : IEdge),
    l.countP (fun x => decide (x = a)) = if a ∈ l then 1 else 0
  | [], _, a => by simp
  | b :: l, hl, a => by
      rw [List.nodup_cons] at hl
      rw [List.countP_cons, countP_single_of_nodup l hl.2 a]
      by_cases hb : b = a
      · subst hb
        simp [hl.1]
      · simp [hb, List.mem_cons, Ne.symm hb]

/-- Membership counts split across an insertion. -/
theorem countP_mem_insert :
    ∀ (l : List IEdge) {T : Finset IEdge} {e : IEdge}, e ∉ T →
    l.countP (fun x => decide (x ∈ insert e T))
      = l.countP (fun x => decide (x ∈ T))
        + l.countP (fun x => decide (x = e))
  | [], T, e, _ => by simp
  | a :: l, T, e, he => by
      rw [List.countP_cons, List.countP_cons, List.countP_cons,
        countP_mem_insert l he]
      by_cases ha : a = e
      · subst ha
        have h1 : a ∈ insert a T := Finset.mem_insert_self a T
        simp only [h1, he, eq_self_iff_true, decide_true,
          decide_false, if_true, if_false, Bool.false_eq_true,
          ite_true, ite_false]
        omega
      · have h1 : (a ∈ insert e T) ↔ (a ∈ T) := by
          rw [Finset.mem_insert]
          exact ⟨fun h => h.resolve_left ha, Or.inr⟩
        simp only [h1, ha, decide_false, Bool.false_eq_true,
          if_false, ite_false]
        omega

open Classical in
/-- Corner degrees grow by dual incidence across an insertion. -/
theorem cornerDegF_insert {T : Finset IEdge} {e : IEdge}
    (he : e ∉ T) (u : V2) :
    cornerDegF (insert e T) u = cornerDegF T u
      + (if u = corner0 e ∨ u = corner1 e then 1 else 0) := by
  unfold cornerDegF
  rw [countP_mem_insert _ he,
    countP_single_of_nodup _ (cornerEdges_nodup u) e]
  simp only [mem_cornerEdges_iff]

open Classical in
/-- **Walk parity**: the trail degree is even away from the two
endpoints of the walk. -/
theorem walk_parity :
    ∀ {L : List IEdge} {v₀ : V2}, Walk v₀ L → L.Nodup →
    ∀ u : V2,
    (cornerDegF L.toFinset u + (if u = v₀ then 1 else 0)
      + (if u = walkEnd v₀ L then 1 else 0)) % 2 = 0
  | [], v₀, _, _, u => by
      have h0 : cornerDegF (([] : List IEdge)).toFinset u = 0 := by
        rw [List.toFinset_nil]
        unfold cornerDegF
        simp
      rw [h0, walkEnd_nil]
      by_cases h : u = v₀
      · rw [if_pos h]
      · rw [if_neg h]
  | e :: l, v₀, hW, hnd, u => by
      obtain ⟨hv, hW'⟩ := hW
      rw [List.nodup_cons] at hnd
      have hIH := walk_parity hW' hnd.2 u
      have hdeg : cornerDegF (e :: l).toFinset u
          = cornerDegF l.toFinset u
            + (if u = corner0 e ∨ u = corner1 e then 1 else 0) := by
        rw [List.toFinset_cons]
        exact cornerDegF_insert
          (by rw [List.mem_toFinset]; exact hnd.1) u
      rw [hdeg, walkEnd_cons]
      rcases otherCorner_cases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hne : v₀ ≠ otherCorner e v₀ := by
          rw [h2, h1]
          exact corner0_ne_corner1 e
        rw [← h1, ← h2]
        by_cases hu0 : u = v₀ <;> by_cases hu1 : u = otherCorner e v₀
        · exact absurd (hu0.symm.trans hu1) hne
        · rw [if_pos (Or.inl hu0), if_pos hu0]
          rw [if_neg hu1] at hIH
          omega
        · rw [if_pos (Or.inr hu1), if_neg hu0]
          rw [if_pos hu1] at hIH
          omega
        · have hor : ¬ (u = v₀ ∨ u = otherCorner e v₀) := by
            rintro (h | h)
            · exact hu0 h
            · exact hu1 h
          rw [if_neg hor, if_neg hu0]
          rw [if_neg hu1] at hIH
          omega
      · have hne : v₀ ≠ otherCorner e v₀ := by
          rw [h2, h1]
          exact (corner0_ne_corner1 e).symm
        rw [← h1, ← h2]
        by_cases hu0 : u = v₀ <;> by_cases hu1 : u = otherCorner e v₀
        · exact absurd (hu0.symm.trans hu1) hne
        · rw [if_pos (Or.inr hu0), if_pos hu0]
          rw [if_neg hu1] at hIH
          omega
        · rw [if_pos (Or.inl hu1), if_neg hu0]
          rw [if_pos hu1] at hIH
          omega
        · have hor : ¬ (u = otherCorner e v₀ ∨ u = v₀) := by
            rintro (h | h)
            · exact hu1 h
            · exact hu0 h
          rw [if_neg hor, if_neg hu0]
          rw [if_neg hu1] at hIH
          omega

/-- Appending a fresh element preserves freedom from duplicates. -/
theorem nodup_append_single :
    ∀ {L : List IEdge} {e : IEdge}, L.Nodup → e ∉ L →
    (L ++ [e]).Nodup
  | [], e, _, _ => by simp
  | a :: l, e, h, he => by
      rw [List.nodup_cons] at h
      rw [List.cons_append, List.nodup_cons]
      refine ⟨?_, nodup_append_single h.2
        (fun hm => he (List.mem_cons_of_mem a hm))⟩
      intro hm
      rcases List.mem_append.mp hm with h1 | h1
      · exact h.1 h1
      · rw [List.mem_singleton] at h1
        subst h1
        exact he List.mem_cons_self

/-- Walks extend across an incident edge. -/
theorem walk_append {e : IEdge} :
    ∀ (L : List IEdge) (v₀ : V2), Walk v₀ L →
    (walkEnd v₀ L = corner0 e ∨ walkEnd v₀ L = corner1 e) →
    Walk v₀ (L ++ [e])
  | [], v₀, _, he => by
      show (v₀ = corner0 e ∨ v₀ = corner1 e)
        ∧ Walk (otherCorner e v₀) []
      exact ⟨he, trivial⟩
  | a :: l, v₀, hW, he => by
      obtain ⟨h1, h2⟩ := hW
      show (v₀ = corner0 a ∨ v₀ = corner1 a)
        ∧ Walk (otherCorner a v₀) (l ++ [e])
      exact ⟨h1, walk_append l _ h2 he⟩

open Classical in
/-- **Greedy maximal trails**: every trail extends to one that can no
longer be extended. -/
theorem exists_max_trail (γ : Finset IEdge) (v₀ : V2) :
    ∀ (fuel : ℕ) (L : List IEdge), Walk v₀ L → L.Nodup →
      (∀ e ∈ L, e ∈ γ) → γ.card ≤ L.length + fuel →
      ∃ M, Walk v₀ (L ++ M) ∧ (L ++ M).Nodup ∧
        (∀ e ∈ L ++ M, e ∈ γ) ∧
        ∀ e, e ∈ γ → e ∉ L ++ M →
          ¬ (walkEnd v₀ (L ++ M) = corner0 e ∨
            walkEnd v₀ (L ++ M) = corner1 e) := by
  intro fuel
  induction fuel with
  | zero =>
      intro L hW hnd hsub hlen
      refine ⟨[], ?_, ?_, ?_, ?_⟩
      · rw [List.append_nil]; exact hW
      · rw [List.append_nil]; exact hnd
      · rw [List.append_nil]; exact hsub
      · rw [List.append_nil]
        intro e heγ heL hinc
        have hnd' : (L ++ [e]).Nodup := nodup_append_single hnd heL
        have hsub' : (L ++ [e]).toFinset ⊆ γ := by
          intro x hx
          rw [List.mem_toFinset] at hx
          rcases List.mem_append.mp hx with h | h
          · exact hsub x h
          · rw [List.mem_singleton] at h
            subst h
            exact heγ
        have hcard := Finset.card_le_card hsub'
        rw [List.toFinset_card_of_nodup hnd'] at hcard
        rw [List.length_append, List.length_singleton] at hcard
        omega
  | succ n ih =>
      intro L hW hnd hsub hlen
      by_cases hext : ∃ e, e ∈ γ ∧ e ∉ L ∧
          (walkEnd v₀ L = corner0 e ∨ walkEnd v₀ L = corner1 e)
      · obtain ⟨e, heγ, heL, hinc⟩ := hext
        have hsub' : ∀ x ∈ L ++ [e], x ∈ γ := by
          intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hsub x h
          · rw [List.mem_singleton] at h
            subst h
            exact heγ
        obtain ⟨M, h1, h2, h3, h4⟩ := ih (L ++ [e])
          (walk_append L v₀ hW hinc)
          (nodup_append_single hnd heL) hsub'
          (by rw [List.length_append, List.length_singleton]; omega)
        refine ⟨[e] ++ M, ?_, ?_, ?_, ?_⟩
        · rw [← List.append_assoc]; exact h1
        · rw [← List.append_assoc]; exact h2
        · rw [← List.append_assoc]; exact h3
        · rw [← List.append_assoc]; exact h4
      · refine ⟨[], ?_, ?_, ?_, ?_⟩
        · rw [List.append_nil]; exact hW
        · rw [List.append_nil]; exact hnd
        · rw [List.append_nil]; exact hsub
        · rw [List.append_nil]
          intro e heγ heL hinc
          exact hext ⟨e, heγ, heL, hinc⟩

open Classical in
/-- **Layer D: the Euler listing** — the contour is traceable as a
single dual trail from any of its edges, in either direction. -/
theorem euler_listing {σ : PlusBC Λ} (h0 : σ.1 0 = false)
    (hcompl : ∀ w : V2, w ∉ Λ → ∃ z : V2,
      (∀ v ∈ Λ, v.2 < z.2) ∧
      Relation.ReflTransGen (fun a b => IAdj a b ∧ b ∉ Λ) w z)
    {s : IEdge} (hs : s ∈ contour σ) {v₀ : V2}
    (hv : v₀ = corner0 s ∨ v₀ = corner1 s) :
    ∃ L : List IEdge, Walk v₀ L ∧ L.Nodup ∧
      L.toFinset = contour σ ∧ L.head? = some s := by
  have hW1 : Walk v₀ [s] := by
    show (v₀ = corner0 s ∨ v₀ = corner1 s)
      ∧ Walk (otherCorner s v₀) []
    exact ⟨hv, trivial⟩
  have hsub1 : ∀ e ∈ [s], e ∈ contour σ := by
    intro e he
    rw [List.mem_singleton] at he
    subst he
    exact hs
  obtain ⟨M, hW, hnd, hsub, hmax⟩ :=
    exists_max_trail (contour σ) v₀ (contour σ).card [s] hW1
      (List.nodup_singleton s) hsub1
      (by rw [List.length_singleton]; omega)
  have hTsub : ([s] ++ M).toFinset ⊆ contour σ := by
    intro e he
    rw [List.mem_toFinset] at he
    exact hsub e he
  have hclosed : walkEnd v₀ ([s] ++ M) = v₀ := by
    by_contra hne
    have h1 := walk_parity hW hnd (walkEnd v₀ ([s] ++ M))
    rw [if_neg hne, if_pos rfl] at h1
    have hall : cornerDegF ([s] ++ M).toFinset
        (walkEnd v₀ ([s] ++ M))
        = cornerDegF (contour σ) (walkEnd v₀ ([s] ++ M)) := by
      unfold cornerDegF
      refine List.countP_congr ?_
      intro e he
      have hinc := (mem_cornerEdges_iff e _).mp he
      show decide (e ∈ ([s] ++ M).toFinset) = true
        ↔ decide (e ∈ contour σ) = true
      by_cases heT : e ∈ ([s] ++ M).toFinset
      · exact iff_of_true (decide_eq_true heT)
          (decide_eq_true (hTsub heT))
      · have heγ : e ∉ contour σ := by
          intro hg
          exact hmax e hg
            (fun hm => heT (List.mem_toFinset.mpr hm)) hinc
        exact iff_of_false
          (by rw [decide_eq_false heT]; exact Bool.false_ne_true)
          (by rw [decide_eq_false heγ]; exact Bool.false_ne_true)
    rw [hall] at h1
    have h2 := cornerDegF_contour_even h0 (walkEnd v₀ ([s] ++ M))
    omega
  have hTev : ∀ u, cornerDegF ([s] ++ M).toFinset u % 2 = 0 := by
    intro u
    have h1 := walk_parity hW hnd u
    rw [hclosed] at h1
    by_cases hu : u = v₀
    · rw [if_pos hu] at h1
      omega
    · rw [if_neg hu] at h1
      omega
  rcases contour_even_split h0 hcompl hTsub hTev with hemp | hfull
  · exfalso
    have hsmem : s ∈ ([s] ++ M).toFinset := by
      rw [List.mem_toFinset]
      exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
    rw [hemp] at hsmem
    exact absurd hsmem (Finset.notMem_empty s)
  · exact ⟨[s] ++ M, hW, hnd, hfull, rfl⟩

/-! ## Layer E1: the canonical start edge and its height bound

The contour crosses the column above the origin at some minimal
height `k`; every row up to `k` then meets the filled cluster, and
each such row donates a horizontal contour edge (the leftmost exit),
bounding `k + 1` by the contour length. -/

open Classical in
/-- The contour contains a lowest vertical edge in the column above
the origin. -/
theorem exists_start_edge {σ : PlusBC Λ} (h0 : σ.1 0 = false) :
    ∃ k : ℤ, 0 ≤ k ∧ ((((0 : ℤ), k), false) : IEdge) ∈ contour σ ∧
      ∀ j : ℤ, 0 ≤ j → j < k →
        ((((0 : ℤ), j), false) : IEdge) ∉ contour σ := by
  have h0in : InsideP (contour σ) 0 :=
    (insideP_contour h0 0).mpr (zero_mem_fillCl σ)
  have hex : ∃ e ∈ contour σ,
      e.2 = false ∧ e.1.1 = (0 : ℤ) ∧ (0 : ℤ) ≤ e.1.2 := by
    unfold InsideP colCount at h0in
    have hpos : 0 < ((contour σ).filter (fun e =>
        e.2 = false ∧ e.1.1 = (0 : V2).1
          ∧ (0 : V2).2 ≤ e.1.2)).card := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at he
    exact ⟨e, he.1, he.2⟩
  obtain ⟨e₀, he₀, hb₀, hx₀, hy₀⟩ := hex
  have hKne : (((contour σ).filter (fun e =>
      e.2 = false ∧ e.1.1 = (0 : ℤ) ∧ (0 : ℤ) ≤ e.1.2)).image
        (fun e => e.1.2)).Nonempty :=
    ⟨e₀.1.2, Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨he₀, hb₀, hx₀, hy₀⟩)⟩
  refine ⟨Finset.min' _ hKne, ?_, ?_, ?_⟩
  · have hmem := Finset.min'_mem _ hKne
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_filter] at he
    rw [← heq]
    exact he.2.2.2
  · have hmem := Finset.min'_mem _ hKne
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_filter] at he
    obtain ⟨⟨x, y⟩, b⟩ := e
    obtain ⟨hmem', hb, hx, hy⟩ := he
    have hb' : b = false := hb
    have hx' : x = (0 : ℤ) := hx
    have hy' : y = Finset.min' _ hKne := heq
    subst hb'
    subst hx'
    rw [← hy']
    exact hmem'
  · intro j hj0 hjlt hmem
    have hjK : j ∈ ((contour σ).filter (fun e =>
        e.2 = false ∧ e.1.1 = (0 : ℤ) ∧ (0 : ℤ) ≤ e.1.2)).image
          (fun e => e.1.2) :=
      Finset.mem_image.mpr ⟨(((0 : ℤ), j), false),
        Finset.mem_filter.mpr ⟨hmem, rfl, rfl, hj0⟩, rfl⟩
    have := Finset.min'_le _ j hjK
    omega

open Classical in
/-- Below the lowest crossing, the column stays in the filled
cluster. -/
theorem sites_below_start {σ : PlusBC Λ} (h0 : σ.1 0 = false)
    {k : ℤ}
    (hmin : ∀ j : ℤ, 0 ≤ j → j < k →
      ((((0 : ℤ), j), false) : IEdge) ∉ contour σ) :
    ∀ j : ℤ, 0 ≤ j → j ≤ k → (((0 : ℤ), j) : V2) ∈ fillCl σ := by
  intro j hj0 hjk
  rw [← insideP_contour h0]
  have h0in : InsideP (contour σ) 0 :=
    (insideP_contour h0 0).mpr (zero_mem_fillCl σ)
  have hcol : colCount (contour σ) ((0 : ℤ), j)
      = colCount (contour σ) (0 : V2) := by
    unfold colCount
    congr 1
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, h1, h2, h3⟩
      refine ⟨he, h1, h2, ?_⟩
      show (0 : V2).2 ≤ e.1.2
      have hz : (0 : V2).2 = (0 : ℤ) := rfl
      rw [hz]
      omega
    · rintro ⟨he, h1, h2, h3⟩
      refine ⟨he, h1, h2, ?_⟩
      by_contra hlt
      obtain ⟨⟨x, y⟩, b⟩ := e
      have hb' : b = false := h1
      have hx'' : x = (0 : ℤ) := h2
      subst hb'
      subst hx''
      have hy0 : (0 : ℤ) ≤ y := h3
      have hyj : ¬ (j ≤ y) := hlt
      exact hmin y hy0 (by omega) he
  unfold InsideP at h0in ⊢
  rw [hcol]
  omega

open Classical in
/-- **The height bound**: each row below the start donates a
horizontal contour edge, so the start height is below the contour
length. -/
theorem start_height_bound {σ : PlusBC Λ} (h0 : σ.1 0 = false)
    {k : ℤ} (hk0 : 0 ≤ k)
    (hsites : ∀ j : ℤ, 0 ≤ j → j ≤ k →
      (((0 : ℤ), j) : V2) ∈ fillCl σ) :
    k + 1 ≤ ((contour σ).card : ℤ) := by
  have hedge : ∀ j : ℤ, 0 ≤ j → j ≤ k → ∃ x : ℤ,
      (((x, j), true) : IEdge) ∈ contour σ := by
    intro j h1 h2
    have hRne : (Λ.filter (fun v =>
        v ∈ fillCl σ ∧ v.2 = j)).Nonempty := by
      refine ⟨((0 : ℤ), j), ?_⟩
      rw [Finset.mem_filter]
      exact ⟨fillCl_subset h0 (hsites j h1 h2),
        hsites j h1 h2, rfl⟩
    set R := Λ.filter (fun v => v ∈ fillCl σ ∧ v.2 = j) with hR
    have hRne' : (R.image Prod.fst).Nonempty := hRne.image _
    set xm := (R.image Prod.fst).min' hRne' with hxm
    have hxmem : ((xm, j) : V2) ∈ fillCl σ := by
      have hmm := (R.image Prod.fst).min'_mem hRne'
      obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hmm
      rw [hR, Finset.mem_filter] at hv
      have hveq2 : v = ((xm, j) : V2) := by
        obtain ⟨a, b⟩ := v
        simp only [Prod.mk.injEq]
        exact ⟨hveq, hv.2.2⟩
      rw [← hveq2]
      exact hv.2.1
    have hleft : ((xm - 1, j) : V2) ∉ fillCl σ := by
      intro hmem
      have hΛ : ((xm - 1, j) : V2) ∈ Λ := fillCl_subset h0 hmem
      have hmR : ((xm - 1, j) : V2) ∈ R := by
        rw [hR, Finset.mem_filter]
        exact ⟨hΛ, hmem, rfl⟩
      have := (R.image Prod.fst).min'_le (xm - 1)
        (Finset.mem_image_of_mem _ hmR)
      rw [← hxm] at this
      omega
    have hep : ep1 ((((xm - 1 : ℤ), j), true) : IEdge)
        = ((xm, j) : V2) := by
      show ((xm - 1, j) : V2) + edir true = ((xm, j) : V2)
      rw [show edir true = ((1 : ℤ), (0 : ℤ)) from rfl]
      show ((xm - 1 + 1 : ℤ), (j + 0 : ℤ)) = ((xm, j) : V2)
      rw [add_zero]
      norm_num
    refine ⟨xm - 1, ?_⟩
    rw [contour, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_eVol]
      right
      rw [hep]
      exact fillCl_subset h0 hxmem
    · show (ep0 ((((xm - 1 : ℤ), j), true) : IEdge) ∈ fillCl σ
          ∧ ep1 ((((xm - 1 : ℤ), j), true) : IEdge) ∉ fillCl σ)
        ∨ (ep0 ((((xm - 1 : ℤ), j), true) : IEdge) ∉ fillCl σ
          ∧ ep1 ((((xm - 1 : ℤ), j), true) : IEdge) ∈ fillCl σ)
      right
      constructor
      · show ((xm - 1, j) : V2) ∉ fillCl σ
        exact hleft
      · rw [hep]
        exact hxmem
  -- inject the rows into the contour
  classical
  have hf : ∀ j ∈ Finset.Icc (0 : ℤ) k,
      (if h : 0 ≤ j ∧ j ≤ k then
        (((Classical.choose (hedge j h.1 h.2), j), true) : IEdge)
      else default) ∈ contour σ := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [dif_pos hj]
    exact Classical.choose_spec (hedge j hj.1 hj.2)
  have hinj : Set.InjOn (fun j => if h : 0 ≤ j ∧ j ≤ k then
      (((Classical.choose (hedge j h.1 h.2), j), true) : IEdge)
    else default) ↑(Finset.Icc (0 : ℤ) k) := by
    intro j₁ h₁ j₂ h₂ heq
    rw [Finset.mem_coe, Finset.mem_Icc] at h₁ h₂
    have e1 : ((if h : 0 ≤ j₁ ∧ j₁ ≤ k then
        (((Classical.choose (hedge j₁ h.1 h.2), j₁), true) : IEdge)
      else default)).1.2 = j₁ := by
      rw [dif_pos h₁]
    have e2 : ((if h : 0 ≤ j₂ ∧ j₂ ≤ k then
        (((Classical.choose (hedge j₂ h.1 h.2), j₂), true) : IEdge)
      else default)).1.2 = j₂ := by
      rw [dif_pos h₂]
    have h12 : ((if h : 0 ≤ j₁ ∧ j₁ ≤ k then
        (((Classical.choose (hedge j₁ h.1 h.2), j₁), true) : IEdge)
      else default)).1.2 = ((if h : 0 ≤ j₂ ∧ j₂ ≤ k then
        (((Classical.choose (hedge j₂ h.1 h.2), j₂), true) : IEdge)
      else default)).1.2 := congrArg (fun e : IEdge => e.1.2) heq
    rw [e1, e2] at h12
    exact h12
  have hcard := Finset.card_le_card_of_injOn _ hf hinj
  rw [Int.card_Icc] at hcard
  have htn : (k + 1 - 0).toNat ≤ (contour σ).card := hcard
  rw [Int.toNat_le] at htn
  omega

/-! ## Layer E2: walk codes and the circuit count

Every Euler listing is reconstructible from its start height and a
turn code in `{1,2,3}` per step: contours of length `n` inject into
`n · 3^(n-1)` codes. -/

/-- The decoder: at each pivot, take the `t`-th of the three
continuations. -/
def decodeWalk : IEdge → V2 → List (Fin 3) → List IEdge
  | _, _, [] => []
  | e, v, t :: ts =>
      ((cornerEdges v).erase e).getD (t : ℕ) e
        :: decodeWalk (((cornerEdges v).erase e).getD (t : ℕ) e)
          (otherCorner (((cornerEdges v).erase e).getD (t : ℕ) e) v)
          ts

theorem decodeWalk_cons (e : IEdge) (v : V2) (t : Fin 3)
    (ts : List (Fin 3)) :
    decodeWalk e v (t :: ts)
      = ((cornerEdges v).erase e).getD (t : ℕ) e
        :: decodeWalk (((cornerEdges v).erase e).getD (t : ℕ) e)
          (otherCorner (((cornerEdges v).erase e).getD (t : ℕ) e) v)
          ts := rfl

/-- The full decoder from a start height and turn codes. -/
def decode (k : ℤ) (ts : List (Fin 3)) : List IEdge :=
  ((((0 : ℤ), k), false) : IEdge)
    :: decodeWalk ((((0 : ℤ), k), false) : IEdge)
      (corner1 ((((0 : ℤ), k), false) : IEdge)) ts

/-- Every continuation at a pivot is one of the three codes. -/
theorem code_step {v : V2} {e e' : IEdge} (hne : e' ≠ e)
    (he : e ∈ cornerEdges v) (he' : e' ∈ cornerEdges v) :
    ∃ t : Fin 3, ((cornerEdges v).erase e).getD (t : ℕ) e = e' := by
  have hlen4 : (cornerEdges v).length = 4 := rfl
  have hlen : ((cornerEdges v).erase e).length = 3 := by
    rw [List.length_erase_of_mem he, hlen4]
  have hmem : e' ∈ (cornerEdges v).erase e :=
    (List.mem_erase_of_ne hne).mpr he'
  obtain ⟨a, b, c, habc⟩ := List.length_eq_three.mp hlen
  rw [habc] at hmem
  rw [habc]
  rcases List.mem_cons.mp hmem with h | hmem2
  · exact ⟨⟨0, by norm_num⟩, h.symm⟩
  · rcases List.mem_cons.mp hmem2 with h | hmem3
    · exact ⟨⟨1, by norm_num⟩, h.symm⟩
    · rw [List.mem_singleton] at hmem3
      exact ⟨⟨2, by norm_num⟩, hmem3.symm⟩

/-- **Roundtrip**: every trail is reproduced by some turn code. -/
theorem exists_decodeWalk :
    ∀ (L : List IEdge) (e : IEdge) (v : V2), Walk v L →
    (e :: L).Nodup → e ∈ cornerEdges v →
    ∃ ts : List (Fin 3), ts.length = L.length
      ∧ decodeWalk e v ts = L
  | [], _, _, _, _, _ => ⟨[], rfl, rfl⟩
  | e' :: l, e, v, hW, hnd, hev => by
      obtain ⟨hv', hW'⟩ := hW
      have hev' : e' ∈ cornerEdges v :=
        (mem_cornerEdges_iff e' v).mpr hv'
      have hne : e' ≠ e := by
        intro h
        rw [List.nodup_cons] at hnd
        subst h
        exact hnd.1 List.mem_cons_self
      have hnd' : (e' :: l).Nodup := by
        rw [List.nodup_cons] at hnd
        exact hnd.2
      have hpivot' : e' ∈ cornerEdges (otherCorner e' v) := by
        rcases otherCorner_cases hv' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h2]
          exact (mem_cornerEdges_iff e' _).mpr (Or.inr rfl)
        · rw [h2]
          exact (mem_cornerEdges_iff e' _).mpr (Or.inl rfl)
      obtain ⟨t, ht⟩ := code_step hne hev hev'
      obtain ⟨ts, hlen, hts⟩ :=
        exists_decodeWalk l e' (otherCorner e' v) hW' hnd' hpivot'
      refine ⟨t :: ts, ?_, ?_⟩
      · rw [List.length_cons, List.length_cons, hlen]
      · rw [decodeWalk_cons, ht, hts]

open Classical in
/-- **The full code**: every realizable contour is decoded from a
start height below its length and one turn code per remaining
edge. -/
theorem exists_code {σ : PlusBC Λ} (h0 : σ.1 0 = false)
    (hcompl : ∀ w : V2, w ∉ Λ → ∃ z : V2,
      (∀ v ∈ Λ, v.2 < z.2) ∧
      Relation.ReflTransGen (fun a b => IAdj a b ∧ b ∉ Λ) w z) :
    ∃ (k : ℕ) (ts : List (Fin 3)),
      (k : ℤ) + 1 ≤ ((contour σ).card : ℤ) ∧
      ts.length = (contour σ).card - 1 ∧
      contour σ = (decode (k : ℤ) ts).toFinset := by
  obtain ⟨k, hk0, hkmem, hkmin⟩ := exists_start_edge h0
  have hsites := sites_below_start h0 hkmin
  have hbound := start_height_bound h0 hk0 hsites
  set s : IEdge := (((0 : ℤ), k), false) with hs
  obtain ⟨L, hW, hnd, hcov, hhead⟩ :=
    euler_listing h0 hcompl hkmem (Or.inl rfl)
  obtain ⟨rest, hrest⟩ : ∃ rest, L = s :: rest := by
    cases L with
    | nil => simp at hhead
    | cons a l =>
        rw [List.head?_cons, Option.some.injEq] at hhead
        exact ⟨l, by rw [hhead]⟩
  subst hrest
  have hoc : otherCorner s (corner0 s) = corner1 s := by
    rcases otherCorner_cases
      (Or.inl rfl : corner0 s = corner0 s ∨ corner0 s = corner1 s)
      with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd h1 (corner0_ne_corner1 s)
  obtain ⟨-, hW2⟩ := hW
  have hW2' : Walk (corner1 s) rest := hoc ▸ hW2
  have hpiv : s ∈ cornerEdges (corner1 s) :=
    (mem_cornerEdges_iff s _).mpr (Or.inr rfl)
  obtain ⟨ts, hlen, hts⟩ :=
    exists_decodeWalk rest s (corner1 s) hW2' hnd hpiv
  refine ⟨k.toNat, ts, ?_, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg hk0]
    exact hbound
  · have hcard : (contour σ).card = rest.length + 1 := by
      rw [← hcov, List.toFinset_card_of_nodup hnd, List.length_cons]
    rw [hlen, hcard]
    omega
  · have hkk : ((k.toNat : ℤ)) = k := Int.toNat_of_nonneg hk0
    rw [← hcov]
    unfold decode
    rw [hkk, ← hs, hts]

open Classical in
/-- **The planar circuit count** (`4n·3^{n-1}`), for volumes whose
complement escapes upward: the `hcount` hypothesis of
`isingContourDatum` is a theorem. -/
theorem circuit_count
    (hcompl : ∀ w : V2, w ∉ Λ → ∃ z : V2,
      (∀ v ∈ Λ, v.2 < z.2) ∧
      Relation.ReflTransGen (fun a b => IAdj a b ∧ b ∉ Λ) w z)
    (n : ℕ) :
    ((contours Λ).filter (fun γ => γ.card = n)).card
      ≤ 4 * n * 3 ^ (n - 1) := by
  have hsurj : ∀ γ ∈ (contours Λ).filter (fun γ => γ.card = n),
      ∃ c : Fin n × (Fin (n - 1) → Fin 3),
        (decode ((c.1 : ℕ) : ℤ) (List.ofFn c.2)).toFinset = γ := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    obtain ⟨hγc, hcard⟩ := hγ
    rw [contours, Finset.mem_filter] at hγc
    obtain ⟨-, σ, h0, hσγ⟩ := hγc
    obtain ⟨k, ts, hk, hlen, hdec⟩ := exists_code h0 hcompl
    rw [hσγ] at hk hlen hdec
    rw [hcard] at hk hlen
    have hkn : k < n := by omega
    refine ⟨⟨⟨k, hkn⟩,
      fun i => ts.getD (i : ℕ) (⟨0, by norm_num⟩ : Fin 3)⟩, ?_⟩
    have hofn : List.ofFn (fun i : Fin (n - 1) =>
        ts.getD (i : ℕ) (⟨0, by norm_num⟩ : Fin 3)) = ts := by
      refine List.ext_getElem ?_ ?_
      · rw [List.length_ofFn, hlen]
      · intro i h1 h2
        rw [List.getElem_ofFn]
        exact List.getD_eq_getElem _ _ h2
    show (decode ((⟨k, hkn⟩ : Fin n) : ℕ) (List.ofFn fun i =>
      ts.getD (i : ℕ) (⟨0, by norm_num⟩ : Fin 3))).toFinset = γ
    rw [hofn, ← hdec]
  have hbound : ((contours Λ).filter (fun γ => γ.card = n)).card
      ≤ Fintype.card (Fin n × (Fin (n - 1) → Fin 3)) := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_surjOn
      (fun c : Fin n × (Fin (n - 1) → Fin 3) =>
        (decode ((c.1 : ℕ) : ℤ) (List.ofFn c.2)).toFinset) ?_
    intro γ hγ
    obtain ⟨c, hc⟩ := hsurj γ (Finset.mem_coe.mp hγ)
    exact ⟨c, Finset.mem_coe.mpr (Finset.mem_univ c), hc⟩
  have hcards : Fintype.card (Fin n × (Fin (n - 1) → Fin 3))
      = n * 3 ^ (n - 1) := by
    rw [Fintype.card_prod, Fintype.card_fun]
    simp [Fintype.card_fin]
  rw [hcards] at hbound
  refine hbound.trans ?_
  have h1 : n * 3 ^ (n - 1) ≤ 4 * (n * 3 ^ (n - 1)) :=
    Nat.le_mul_of_pos_left _ (by norm_num)
  calc n * 3 ^ (n - 1) ≤ 4 * (n * 3 ^ (n - 1)) := h1
    _ = 4 * n * 3 ^ (n - 1) := by ring

/-! ## Box volumes satisfy the escape hypothesis

The complement of a rectangle escapes upward: walk sideways out of
the column range if needed, then straight up.  (For "Swiss-cheese"
volumes with enclosed holes the hypothesis — and the circuit count
itself — genuinely fails.) -/

/-- Walking straight up through clear sites. -/
theorem ray_up {Λ : Finset V2} {x y : ℤ}
    (h : ∀ y' : ℤ, y ≤ y' → ((x, y') : V2) ∉ Λ) :
    ∀ m : ℕ, Relation.ReflTransGen
      (fun p q => IAdj p q ∧ q ∉ Λ)
      ((x, y) : V2) ((x, y + (m : ℤ)) : V2)
  | 0 => by
      have h0 : y + ((0 : ℕ) : ℤ) = y := by norm_num
      rw [h0]
  | m + 1 => by
      refine (ray_up h m).tail ?_
      have hep : ep1 (((x, y + (m : ℤ)), false) : IEdge)
          = ((x, y + ((m + 1 : ℕ) : ℤ)) : V2) := by
        show ((x, y + (m : ℤ)) : V2) + edir false
          = ((x, y + ((m + 1 : ℕ) : ℤ)) : V2)
        rw [show edir false = ((0 : ℤ), (1 : ℤ)) from rfl]
        show ((x + 0, y + (m : ℤ) + 1) : V2)
          = ((x, y + ((m + 1 : ℕ) : ℤ)) : V2)
        rw [Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
      constructor
      · exact ⟨((x, y + (m : ℤ)), false), Or.inl ⟨rfl, hep⟩⟩
      · exact h _ (by omega)

/-- Walking left through a clear row. -/
theorem ray_left {Λ : Finset V2} {x y : ℤ}
    (h : ∀ x' : ℤ, ((x', y) : V2) ∉ Λ) :
    ∀ m : ℕ, Relation.ReflTransGen
      (fun p q => IAdj p q ∧ q ∉ Λ)
      ((x, y) : V2) ((x - (m : ℤ), y) : V2)
  | 0 => by
      have h0 : x - ((0 : ℕ) : ℤ) = x := by norm_num
      rw [h0]
  | m + 1 => by
      refine (ray_left h m).tail ?_
      constructor
      · refine ⟨((x - (m : ℤ) - 1, y), true), Or.inr ⟨?_, ?_⟩⟩
        · show ((x - (m : ℤ) - 1, y) : V2)
            = ((x - ((m + 1 : ℕ) : ℤ), y) : V2)
          rw [Prod.mk.injEq]
          exact ⟨by omega, by omega⟩
        · show ((x - (m : ℤ) - 1, y) : V2) + edir true
            = ((x - (m : ℤ), y) : V2)
          rw [show edir true = ((1 : ℤ), (0 : ℤ)) from rfl]
          show ((x - (m : ℤ) - 1 + 1, y + 0) : V2)
            = ((x - (m : ℤ), y) : V2)
          rw [Prod.mk.injEq]
          exact ⟨by omega, by omega⟩
      · exact h _

open Classical in
/-- **Boxes escape upward**: the complement of a rectangle satisfies
the escape hypothesis of the circuit count. -/
theorem box_hcompl (a b c d : ℤ) :
    ∀ w : V2, w ∉ Finset.Icc a b ×ˢ Finset.Icc c d → ∃ z : V2,
      (∀ v ∈ Finset.Icc a b ×ˢ Finset.Icc c d, v.2 < z.2) ∧
      Relation.ReflTransGen (fun p q => IAdj p q ∧
        q ∉ Finset.Icc a b ×ˢ Finset.Icc c d) w z := by
  intro w hw
  obtain ⟨wx, wy⟩ := w
  have hmem : ∀ p q : ℤ, (((p, q) : V2) ∈
      Finset.Icc a b ×ˢ Finset.Icc c d)
        ↔ (a ≤ p ∧ p ≤ b) ∧ (c ≤ q ∧ q ≤ d) := by
    intro p q
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  rw [hmem] at hw
  by_cases hx : wx < a ∨ b < wx
  · refine ⟨((wx, wy + ((d + 1 - wy).toNat : ℤ)) : V2), ?_,
      ray_up ?_ (d + 1 - wy).toNat⟩
    · intro v hv
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hv
      show v.2 < wy + ((d + 1 - wy).toNat : ℤ)
      omega
    · intro y' hy'
      rw [hmem]
      rintro ⟨⟨h1, h2⟩, -⟩
      omega
  · by_cases hyd : d < wy
    · refine ⟨((wx, wy + ((d + 1 - wy).toNat : ℤ)) : V2), ?_,
        ray_up ?_ (d + 1 - wy).toNat⟩
      · intro v hv
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hv
        show v.2 < wy + ((d + 1 - wy).toNat : ℤ)
        omega
      · intro y' hy'
        rw [hmem]
        rintro ⟨-, ⟨h3, h4⟩⟩
        omega
    · have hyc : wy < c := by
        by_contra hcon
        exact hw ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
      have hrow : ∀ x' : ℤ, ((x', wy) : V2) ∉
          Finset.Icc a b ×ˢ Finset.Icc c d := by
        intro x'
        rw [hmem]
        rintro ⟨-, ⟨h3, -⟩⟩
        omega
      have hcol : ∀ y' : ℤ, wy ≤ y' →
          ((wx - ((wx - (a - 1)).toNat : ℤ), y') : V2) ∉
            Finset.Icc a b ×ˢ Finset.Icc c d := by
        intro y' hy2
        rw [hmem]
        rintro ⟨⟨h1, -⟩, -⟩
        omega
      refine ⟨((wx - ((wx - (a - 1)).toNat : ℤ),
          wy + ((d + 1 - wy).toNat : ℤ)) : V2), ?_,
        (ray_left hrow (wx - (a - 1)).toNat).trans
          (ray_up hcol (d + 1 - wy).toNat)⟩
      intro v hv
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hv
      show v.2 < wy + ((d + 1 - wy).toNat : ℤ)
      omega

open Classical in
/-- **The circuit count for box volumes** — unconditional. -/
theorem box_circuit_count (a b c d : ℤ) (n : ℕ) :
    ((contours (Finset.Icc a b ×ˢ Finset.Icc c d)).filter
      (fun γ => γ.card = n)).card ≤ 4 * n * 3 ^ (n - 1) :=
  circuit_count (box_hcompl a b c d) n

open Classical in
/-- **The magnetization bound with the circuit count discharged**:
for every volume whose complement escapes upward — in particular
every box — the scoped `hcount` hypothesis of `isingContourDatum`
is now a theorem. -/
theorem ising_magnetization_of_escape (θ : ℝ)
    (hθ : (1 / 2) * Real.log 12 ≤ θ)
    (hcompl : ∀ w : V2, w ∉ Λ → ∃ z : V2,
      (∀ v ∈ Λ, v.2 < z.2) ∧
      Relation.ReflTransGen (fun p q => IAdj p q ∧ q ∉ Λ) w z) :
    (203 / 216) * ∑ σ : PlusBC Λ, wt Λ θ σ
      ≤ ∑ σ : PlusBC Λ, wt Λ θ σ * spin (σ.1 0) :=
  ising_magnetization Λ θ hθ (circuit_count hcompl)

open Classical in
/-- **The box magnetization bound** — every hypothesis discharged:
low-temperature symmetry breaking on rectangles with the planar
circuit count proved, not assumed. -/
theorem box_magnetization (a b c d : ℤ) (θ : ℝ)
    (hθ : (1 / 2) * Real.log 12 ≤ θ) :
    (203 / 216) * ∑ σ : PlusBC (Finset.Icc a b ×ˢ Finset.Icc c d),
        wt (Finset.Icc a b ×ˢ Finset.Icc c d) θ σ
      ≤ ∑ σ : PlusBC (Finset.Icc a b ×ˢ Finset.Icc c d),
        wt (Finset.Icc a b ×ˢ Finset.Icc c d) θ σ * spin (σ.1 0) :=
  ising_magnetization _ θ hθ
    (circuit_count (box_hcompl a b c d))

end NCG.Upstream.Ising
