/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Even/odd triplet splitting on the two-cell graph
  (`thm:two-cell-splitting`, SM manuscript)

Let `G₂` be the union of the complete graphs on `{0,1,2,3}` and
`{0,1,4,5}`, sharing the edge `01`: six vertices and eleven edges
(ordered `01,02,03,12,13,23,04,05,14,15,45`).  With the coboundary
`d : C⁰ → C¹`, `H¹(G₂;ℂ) = C¹/im d` has

  `dim H¹ = 11 - 6 + 1 = 6`

(`finrank_twoCellH1`; `ker d` is the constants).  The cell-exchange
involution `2↔4, 3↔5` acts on edges without orientation flips,
intertwines `d`, and descends to an involution `T̄` of `H¹`.  Its
even and odd eigenspaces satisfy the boxed splitting

  `H¹ = H¹₊ ⊕ H¹₋`, `dim H¹₊ = dim H¹₋ = 3`

(`two_cell_splitting`).  The even dimension is computed by the
surjection from the even edge subspace (dimension `6`) with kernel
`im d ∩ C¹₊ = d(C⁰₊)` of dimension `3`; the odd dimension follows
from complementarity.  (The manuscript's equivariant-trace argument
is replaced by this equivalent direct dimension count.)
-/

open Module

namespace NCG

/-- The eleven oriented edges of the two-cell graph, as ordered
endpoint pairs. -/
def cellEnds : Fin 11 → Fin 6 × Fin 6 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3),
    (0,4), (0,5), (1,4), (1,5), (4,5)]

/-- The coboundary `C⁰ → C¹` of the two-cell graph. -/
noncomputable def cellD : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 11 → ℂ) where
  toFun f := fun e => f (cellEnds e).2 - f (cellEnds e).1
  map_add' f g := by
    funext e
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The cell-exchange involution on vertices: `2↔4`, `3↔5`. -/
def sigmaV : Fin 6 → Fin 6 := ![0, 1, 4, 5, 2, 3]

/-- The cell-exchange involution on edges. -/
def sigmaE : Fin 11 → Fin 11 := ![0, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5]

/-- The edge action of the cell exchange on one-cochains. -/
noncomputable def cellT : (Fin 11 → ℂ) →ₗ[ℂ] (Fin 11 → ℂ) where
  toFun g := fun e => g (sigmaE e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The vertex action of the cell exchange on zero-cochains. -/
noncomputable def cellT0 : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun f := fun v => f (sigmaV v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The edge exchange is an involution. -/
lemma sigmaE_invol : ∀ e, sigmaE (sigmaE e) = e := by decide

/-- The vertex exchange is an involution. -/
lemma sigmaV_invol : ∀ v, sigmaV (sigmaV v) = v := by decide

/-- The exchange preserves the oriented endpoint structure: no
orientation flips occur. -/
lemma cellEnds_sigmaE : ∀ e, cellEnds (sigmaE e)
    = (sigmaV (cellEnds e).1, sigmaV (cellEnds e).2) := by decide

/-- `T` is an involution on cochains. -/
lemma cellT_invol (g : Fin 11 → ℂ) : cellT (cellT g) = g := by
  funext e
  exact congrArg g (sigmaE_invol e)

/-- `T₀` is an involution on zero-cochains. -/
lemma cellT0_invol (f : Fin 6 → ℂ) : cellT0 (cellT0 f) = f := by
  funext v
  exact congrArg f (sigmaV_invol v)

/-- The exchange intertwines the coboundary: `T ∘ d = d ∘ T₀`. -/
lemma cellT_cellD (f : Fin 6 → ℂ) :
    cellT (cellD f) = cellD (cellT0 f) := by
  funext e
  change f (cellEnds (sigmaE e)).2 - f (cellEnds (sigmaE e)).1
    = f (sigmaV (cellEnds e).2) - f (sigmaV (cellEnds e).1)
  rw [cellEnds_sigmaE e]

/-- The kernel of the coboundary is the constants: the graph is
connected. -/
lemma ker_cellD :
    LinearMap.ker cellD
      = Submodule.span ℂ {(fun _ => 1 : Fin 6 → ℂ)} := by
  apply le_antisymm
  · intro f hf
    rw [LinearMap.mem_ker] at hf
    have h0 : f 1 - f 0 = 0 := congrFun hf 0
    have h1 : f 2 - f 0 = 0 := congrFun hf 1
    have h2 : f 3 - f 0 = 0 := congrFun hf 2
    have h6 : f 4 - f 0 = 0 := congrFun hf 6
    have h7 : f 5 - f 0 = 0 := congrFun hf 7
    rw [Submodule.mem_span_singleton]
    refine ⟨f 0, ?_⟩
    funext v
    rw [Pi.smul_apply, smul_eq_mul, mul_one]
    fin_cases v
    · rfl
    · exact (sub_eq_zero.mp h0).symm
    · exact (sub_eq_zero.mp h1).symm
    · exact (sub_eq_zero.mp h2).symm
    · exact (sub_eq_zero.mp h6).symm
    · exact (sub_eq_zero.mp h7).symm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext e
    change (1 : ℂ) - 1 = 0
    ring

/-- The constant function is nonzero. -/
lemma const_one_ne_zero : (fun _ => 1 : Fin 6 → ℂ) ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num at this

/-- The coboundary has rank `5`. -/
lemma finrank_range_cellD :
    finrank ℂ (LinearMap.range cellD) = 5 := by
  have h := LinearMap.finrank_range_add_finrank_ker cellD
  rw [ker_cellD, finrank_span_singleton const_one_ne_zero] at h
  have h6 : finrank ℂ (Fin 6 → ℂ) = 6 := Module.finrank_fin_fun ℂ
  omega

/-- `H¹(G₂;ℂ)`: one-cochains modulo coboundaries. -/
abbrev TwoCellH1 : Type :=
  (Fin 11 → ℂ) ⧸ LinearMap.range cellD

/-- `dim H¹(G₂;ℂ) = 11 - 6 + 1 = 6`. -/
lemma finrank_twoCellH1 : finrank ℂ TwoCellH1 = 6 := by
  have h : finrank ℂ TwoCellH1
      + finrank ℂ ↥(LinearMap.range cellD) = 11 := by
    have h0 := Submodule.finrank_quotient_add_finrank
      (LinearMap.range cellD)
    have h11 : finrank ℂ (Fin 11 → ℂ) = 11 := Module.finrank_fin_fun ℂ
    rw [h11] at h0
    exact h0
  rw [finrank_range_cellD] at h
  omega

/-- The exchange preserves the coboundary subspace. -/
lemma range_le_comap :
    LinearMap.range cellD
      ≤ Submodule.comap cellT (LinearMap.range cellD) := by
  rintro x ⟨f, rfl⟩
  exact ⟨cellT0 f, (cellT_cellD f).symm⟩

/-- The induced involution `T̄` on `H¹`. -/
noncomputable def cellTbar : TwoCellH1 →ₗ[ℂ] TwoCellH1 :=
  Submodule.mapQ (LinearMap.range cellD) (LinearMap.range cellD)
    cellT range_le_comap

lemma cellTbar_mk (x : Fin 11 → ℂ) :
    cellTbar ((LinearMap.range cellD).mkQ x)
      = (LinearMap.range cellD).mkQ (cellT x) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, cellTbar,
    Submodule.mapQ_apply]

/-- `T̄` is an involution. -/
lemma cellTbar_invol (x : TwoCellH1) : cellTbar (cellTbar x) = x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [cellTbar_mk, cellTbar_mk, cellT_invol]

/-- The even part of `H¹`. -/
noncomputable def H1even : Submodule ℂ TwoCellH1 :=
  LinearMap.ker (cellTbar - LinearMap.id)

/-- The odd part of `H¹`. -/
noncomputable def H1odd : Submodule ℂ TwoCellH1 :=
  LinearMap.ker (cellTbar + LinearMap.id)

/-- The even/odd eigenspaces are complementary (characteristic
zero). -/
lemma isCompl_H1 : IsCompl H1even H1odd := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxp hxm
    rw [H1even, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hxp
    rw [H1odd, LinearMap.mem_ker, LinearMap.add_apply,
      LinearMap.id_apply] at hxm
    have h2 : (2 : ℂ) • x = 0 := by
      rw [two_smul]
      calc x + x = cellTbar x + x := by rw [hxp]
        _ = 0 := hxm
    simpa using smul_eq_zero.mp h2
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (1/2 : ℂ) • (x + cellTbar x)
        + (1/2 : ℂ) • (x - cellTbar x) := by
      rw [smul_add, smul_sub]
      module
    rw [hx]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [H1even, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, map_smul, map_add, cellTbar_invol,
        sub_eq_zero]
      module
    · rw [H1odd, LinearMap.mem_ker, LinearMap.add_apply,
        LinearMap.id_apply, map_smul, map_sub, cellTbar_invol]
      module

/-! ### Dimension of the even part -/

/-- Even edge subspace upstairs. -/
noncomputable def evenEdges : Submodule ℂ (Fin 11 → ℂ) :=
  LinearMap.ker (cellT - LinearMap.id)

/-- Even vertex subspace upstairs. -/
noncomputable def evenVerts : Submodule ℂ (Fin 6 → ℂ) :=
  LinearMap.ker (cellT0 - LinearMap.id)

/-- Edge-orbit representatives of the exchange. -/
def orbitRep : Fin 11 → Fin 6 := ![0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5]

/-- Embedding of orbit representatives. -/
def edgeEmb : Fin 6 → Fin 11 := ![0, 1, 2, 3, 4, 5]

lemma orbitRep_sigmaE : ∀ e, orbitRep (sigmaE e) = orbitRep e := by
  decide

lemma orbitRep_edgeEmb : ∀ i, orbitRep (edgeEmb i) = i := by decide

lemma edgeEmb_orbitRep :
    ∀ e, edgeEmb (orbitRep e) = e ∨ edgeEmb (orbitRep e) = sigmaE e := by
  decide

/-- Members of the even edge subspace are `σ`-invariant
componentwise. -/
lemma evenEdges_apply {g : Fin 11 → ℂ} (hg : g ∈ evenEdges) (e : Fin 11) :
    g (sigmaE e) = g e := by
  rw [evenEdges, LinearMap.mem_ker] at hg
  have h := congrFun hg e
  rw [LinearMap.sub_apply, LinearMap.id_apply] at h
  exact sub_eq_zero.mp h

/-- The even edge subspace has dimension `6`: one coordinate per
edge orbit. -/
noncomputable def evenEdgesEquiv : evenEdges ≃ₗ[ℂ] (Fin 6 → ℂ) where
  toFun g := fun i => g.1 (edgeEmb i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun h := ⟨fun e => h (orbitRep e), by
    rw [evenEdges, LinearMap.mem_ker]
    funext e
    change h (orbitRep (sigmaE e)) - h (orbitRep e) = 0
    rw [orbitRep_sigmaE e, sub_self]⟩
  left_inv g := by
    apply Subtype.ext
    funext e
    change g.1 (edgeEmb (orbitRep e)) = g.1 e
    rcases edgeEmb_orbitRep e with h | h
    · rw [h]
    · rw [h, evenEdges_apply g.2 e]
  right_inv h := by
    funext i
    change h (orbitRep (edgeEmb i)) = h i
    rw [orbitRep_edgeEmb i]

lemma finrank_evenEdges : finrank ℂ evenEdges = 6 := by
  rw [evenEdgesEquiv.finrank_eq]
  exact Module.finrank_fin_fun ℂ

/-- Vertex-orbit representatives of the exchange. -/
def vertRep : Fin 6 → Fin 4 := ![0, 1, 2, 3, 2, 3]

/-- Embedding of vertex-orbit representatives. -/
def vertEmb : Fin 4 → Fin 6 := ![0, 1, 2, 3]

lemma vertRep_sigmaV : ∀ v, vertRep (sigmaV v) = vertRep v := by decide

lemma vertRep_vertEmb : ∀ i, vertRep (vertEmb i) = i := by decide

lemma vertEmb_vertRep :
    ∀ v, vertEmb (vertRep v) = v ∨ vertEmb (vertRep v) = sigmaV v := by
  decide

/-- Members of the even vertex subspace are `σ`-invariant
componentwise. -/
lemma evenVerts_apply {f : Fin 6 → ℂ} (hf : f ∈ evenVerts) (v : Fin 6) :
    f (sigmaV v) = f v := by
  rw [evenVerts, LinearMap.mem_ker] at hf
  have h := congrFun hf v
  rw [LinearMap.sub_apply, LinearMap.id_apply] at h
  exact sub_eq_zero.mp h

/-- The even vertex subspace has dimension `4`. -/
noncomputable def evenVertsEquiv : evenVerts ≃ₗ[ℂ] (Fin 4 → ℂ) where
  toFun f := fun i => f.1 (vertEmb i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun h := ⟨fun v => h (vertRep v), by
    rw [evenVerts, LinearMap.mem_ker]
    funext v
    change h (vertRep (sigmaV v)) - h (vertRep v) = 0
    rw [vertRep_sigmaV v, sub_self]⟩
  left_inv f := by
    apply Subtype.ext
    funext v
    change f.1 (vertEmb (vertRep v)) = f.1 v
    rcases vertEmb_vertRep v with h | h
    · rw [h]
    · rw [h, evenVerts_apply f.2 v]
  right_inv h := by
    funext i
    change h (vertRep (vertEmb i)) = h i
    rw [vertRep_vertEmb i]

lemma finrank_evenVerts : finrank ℂ evenVerts = 4 := by
  rw [evenVertsEquiv.finrank_eq]
  exact Module.finrank_fin_fun ℂ

/-- The even coboundaries are exactly the coboundaries of even
vertex functions. -/
lemma range_inf_even :
    LinearMap.range cellD ⊓ evenEdges
      = Submodule.map cellD evenVerts := by
  apply le_antisymm
  · rintro x hx
    obtain ⟨⟨f, rfl⟩, hev⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_map.mpr
      ⟨(1/2 : ℂ) • (f + cellT0 f), ?_, ?_⟩
    · rw [evenVerts, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, map_smul, map_add, cellT0_invol]
      module
    · have hTd : cellT (cellD f) = cellD f := by
        funext e
        exact evenEdges_apply hev e
      rw [map_smul, map_add, ← cellT_cellD, hTd]
      module
  · rintro x ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe] at hf
    have hf' : cellT0 f = f := funext fun v => evenVerts_apply hf v
    refine Submodule.mem_inf.mpr ⟨⟨f, rfl⟩, ?_⟩
    rw [evenEdges, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, cellT_cellD, hf', sub_self]

/-- The constants are even. -/
lemma ker_le_evenVerts : LinearMap.ker cellD ≤ evenVerts := by
  rw [ker_cellD, Submodule.span_le, Set.singleton_subset_iff]
  rw [SetLike.mem_coe, evenVerts, LinearMap.mem_ker]
  funext v
  change (1 : ℂ) - 1 = 0
  ring

/-- The even coboundary space has dimension `3`. -/
lemma finrank_range_inf_even :
    finrank ℂ ↥(LinearMap.range cellD ⊓ evenEdges) = 3 := by
  rw [range_inf_even]
  -- rank-nullity for `d` restricted to the even vertex functions
  have hmap : Submodule.map cellD evenVerts
      = LinearMap.range (cellD ∘ₗ evenVerts.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have h := LinearMap.finrank_range_add_finrank_ker
    (cellD ∘ₗ evenVerts.subtype)
  have hker : LinearMap.ker (cellD ∘ₗ evenVerts.subtype)
      = Submodule.comap evenVerts.subtype (LinearMap.ker cellD) :=
    LinearMap.ker_comp _ _
  have hkerdim : finrank ℂ
      ↥(LinearMap.ker (cellD ∘ₗ evenVerts.subtype)) = 1 := by
    rw [hker,
      (Submodule.comapSubtypeEquivOfLe ker_le_evenVerts).finrank_eq,
      ker_cellD, finrank_span_singleton const_one_ne_zero]
  rw [hkerdim, finrank_evenVerts] at h
  rw [hmap]
  omega

/-- The projection of the even edge subspace to `H¹` with the
quotient map. -/
noncomputable def psiEven : evenEdges →ₗ[ℂ] TwoCellH1 :=
  (LinearMap.range cellD).mkQ ∘ₗ evenEdges.subtype

/-- `ψ` lands in the even part and surjects onto it. -/
lemma range_psiEven : LinearMap.range psiEven = H1even := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    rw [H1even, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    change cellTbar ((LinearMap.range cellD).mkQ g)
      = (LinearMap.range cellD).mkQ g
    rw [cellTbar_mk]
    congr 1
    funext e
    exact evenEdges_apply hg e
  · intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [H1even, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero, cellTbar_mk] at hx
    refine ⟨⟨(1/2 : ℂ) • (y + cellT y), ?_⟩, ?_⟩
    · rw [evenEdges, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, map_smul, map_add, cellT_invol]
      module
    · change (LinearMap.range cellD).mkQ ((1/2 : ℂ) • (y + cellT y))
        = (LinearMap.range cellD).mkQ y
      rw [map_smul, map_add, hx]
      module

/-- The kernel of `ψ` is the even coboundary space. -/
lemma ker_psiEven :
    finrank ℂ ↥(LinearMap.ker psiEven) = 3 := by
  have hker : LinearMap.ker psiEven
      = Submodule.comap evenEdges.subtype (LinearMap.range cellD) := by
    rw [psiEven, LinearMap.ker_comp, Submodule.ker_mkQ]
  have hcomap : Submodule.comap evenEdges.subtype (LinearMap.range cellD)
      = Submodule.comap evenEdges.subtype
          (LinearMap.range cellD ⊓ evenEdges) := by
    ext ⟨g, hg⟩
    simp [Submodule.mem_comap]
  rw [hker, hcomap,
    (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq]
  exact finrank_range_inf_even

/-- `dim H¹₊ = 3`. -/
lemma finrank_H1even : finrank ℂ H1even = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker psiEven
  rw [range_psiEven, ker_psiEven, finrank_evenEdges] at h
  omega

/-- `dim H¹₋ = 3`. -/
lemma finrank_H1odd : finrank ℂ H1odd = 3 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq H1even H1odd
  rw [isCompl_H1.sup_eq_top, isCompl_H1.inf_eq_bot, finrank_top,
    finrank_twoCellH1, finrank_H1even, finrank_bot] at h
  omega

/-- `thm:two-cell-splitting`: the two-cell graph has
`dim H¹ = 11 - 6 + 1 = 6`, and the cell-exchange involution splits
it into three-dimensional even and odd eigenspaces. -/
theorem two_cell_splitting :
    finrank ℂ TwoCellH1 = 6
    ∧ IsCompl H1even H1odd
    ∧ finrank ℂ H1even = 3 ∧ finrank ℂ H1odd = 3 :=
  ⟨finrank_twoCellH1, isCompl_H1, finrank_H1even, finrank_H1odd⟩

end NCG
