/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Operator.Diagonal
import NCG.Graph.Multigraph

/-!
# The graded path clock and its modular eigenoperators

Covers `thm:pressure-path-clock` from `manuscripts/renewal_emergence/renewal_emergence.tex`: on the
graded path cover `ℓ²(P_fin(G))` the modular weight `Δ_β = e^{βN}`
(with `N` the depth-weighted grading operator) makes every
path-creation operator `S_e` a modular eigenoperator,

`Δ_β^{it} S_e Δ_β^{-it} = e^{itβℓ_e} S_e`.

The construction is carried on the finitely-supported core:

* `GradedPathSystem` — a path space with weighted depth and partial
  edge creation raising the depth by `ℓ_e`;
* `creationOp` — the path-creation operator on `P →₀ ℂ`;
* `creation_grading` — the grading commutator `[N, S_e] = ℓ_e S_e`
  (the hypothesis shape consumed by the affine-clock rigidity theorem
  `upstream_affine_clock_weighted`);
* `creation_modular_conj` — the conjugation identity
  `e^{zN} S_e e^{-zN} = e^{zℓ_e} S_e` for every complex scale `z`;
  `z = itβ` is the boxed modular-flow identity, `z = β` the
  weight form;
* `pathClock` — the concrete instance on the directed finite paths
  `PathIn G` of a multigraph, with depth `Σ ℓ_e` along the path and
  creation by prepending a composable edge.
-/

namespace NCG.Upstream

open NCG

/-- A **graded path system**: a path space `P` with weighted depth,
edge depths `ℓ`, and partial edge creation raising depth by exactly
`ℓ e`.  `P_fin(G)` with prepend-creation is the intended instance
(`pathClock`). -/
structure GradedPathSystem (P : Type*) (E : Type*) where
  /-- The weighted renewal depth `L(w)`. -/
  depth : P → ℝ
  /-- Edge depths `ℓ_e`. -/
  ℓ : E → ℝ
  /-- Partial path creation `w ↦ e·w`. -/
  create : E → P → Option P
  /-- Creation raises the depth by exactly `ℓ e`. -/
  depth_create : ∀ e w w', create e w = some w' →
    depth w' = depth w + ℓ e

variable {P E : Type*} (S : GradedPathSystem P E)

/-- The **path-creation operator** `S_e` on the finitely supported
core: `S_e e_w = e_{e·w}` when the creation composes, `0`
otherwise. -/
noncomputable def creationOp (e : E) : (P →₀ ℂ) →ₗ[ℂ] (P →₀ ℂ) :=
  Finsupp.lsum ℂ fun w =>
    match S.create e w with
    | some w' => Finsupp.lsingle w'
    | none => 0

theorem creationOp_single_some {e : E} {w w' : P}
    (h : S.create e w = some w') (c : ℂ) :
    creationOp S e (Finsupp.single w c) = Finsupp.single w' c := by
  unfold creationOp
  rw [Finsupp.lsum_single]
  rw [h]
  rfl

theorem creationOp_single_none {e : E} {w : P}
    (h : S.create e w = none) (c : ℂ) :
    creationOp S e (Finsupp.single w c) = 0 := by
  unfold creationOp
  rw [Finsupp.lsum_single]
  rw [h]
  rfl

/-- **Theorem `thm:pressure-path-clock` (grading)**: the depth
operator grades the creations, `[N, S_e] = ℓ_e S_e` — exactly the
weighted-grading hypothesis of the affine-clock rigidity theorem. -/
theorem creation_grading (e : E) :
    diagOp (fun w => (S.depth w : ℂ)) ∘ₗ creationOp S e
      - creationOp S e ∘ₗ diagOp (fun w => (S.depth w : ℂ))
    = ((S.ℓ e : ℝ) : ℂ) • creationOp S e := by
  apply Finsupp.lhom_ext
  intro w c
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, diagOp_single]
  cases h : S.create e w with
  | some w' =>
      rw [creationOp_single_some S h, creationOp_single_some S h,
        diagOp_single, Finsupp.smul_single, smul_eq_mul,
        S.depth_create e w w' h]
      rw [← Finsupp.single_sub]
      congr 1
      push_cast
      ring
  | none =>
      rw [creationOp_single_none S h, creationOp_single_none S h,
        smul_zero, sub_zero]
      exact map_zero _

/-- **Theorem `thm:pressure-path-clock` (boxed identity)**: for every
complex scale `z`, conjugation by the diagonal weight `e^{zN}` scales
each creation operator by `e^{zℓ_e}`:

`e^{zN} ∘ S_e ∘ e^{-zN} = e^{zℓ_e} • S_e`.

With `z = itβ` this is the modular-flow eigenoperator identity
`Δ_β^{it} S_e Δ_β^{-it} = e^{itβℓ_e} S_e`; with `z = β` it is the
multiplicative weight form. -/
theorem creation_modular_conj (e : E) (z : ℂ) :
    diagOp (fun w => Complex.exp (z * S.depth w)) ∘ₗ creationOp S e
        ∘ₗ diagOp (fun w => Complex.exp (-(z * S.depth w)))
      = Complex.exp (z * S.ℓ e) • creationOp S e := by
  apply Finsupp.lhom_ext
  intro w c
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    diagOp_single]
  cases h : S.create e w with
  | some w' =>
      rw [creationOp_single_some S h, creationOp_single_some S h,
        diagOp_single, Finsupp.smul_single, smul_eq_mul,
        S.depth_create e w w' h]
      congr 1
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
  | none =>
      rw [creationOp_single_none S h, creationOp_single_none S h,
        smul_zero]
      exact map_zero _

/-! ## The concrete path cover of a multigraph -/

/-- Composability of an edge list read head-first from a vertex. -/
def Multigraph.pathFrom (G : Multigraph) : G.V → List G.E → Prop
  | _, [] => True
  | v, e :: l => G.src e = v ∧ Multigraph.pathFrom G (G.tgt e) l

/-- A **finite directed path** of `G`: a start vertex together with a
composable edge list — the point set of the graded path cover
`P_fin(G)`. -/
abbrev Multigraph.PathIn (G : Multigraph) : Type _ :=
  Σ v : G.V, {l : List G.E // Multigraph.pathFrom G v l}

/-- **Theorem `thm:pressure-path-clock` (the concrete cover)**: the
directed finite paths of a multigraph with depth `Σ ℓ_e` and
prepend-creation form a graded path system — instantiating the
grading and modular-conjugation identities on the actual path cover
`ℓ²(P_fin(G))`. -/
noncomputable def pathClock (G : Multigraph) [DecidableEq G.V]
    (ℓ : G.E → ℝ) : GradedPathSystem (Multigraph.PathIn G) G.E where
  depth := fun p => (p.2.1.map ℓ).sum
  ℓ := ℓ
  create := fun e p =>
    if h : G.tgt e = p.1 then
      some ⟨G.src e, e :: p.2.1,
        ⟨rfl, by rw [h]; exact p.2.2⟩⟩
    else none
  depth_create := by
    intro e p p' h
    obtain ⟨v, l, hl⟩ := p
    dsimp only at h
    by_cases hc : G.tgt e = v
    · rw [dif_pos hc, Option.some.injEq] at h
      subst h
      show ((e :: l).map ℓ).sum = (l.map ℓ).sum + ℓ e
      rw [List.map_cons, List.sum_cons]
      ring
    · rw [dif_neg hc] at h
      simp at h

end NCG.Upstream
