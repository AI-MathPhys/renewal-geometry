/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.PolarHolonomy
import RenewalGeometry.Commutant.SupportPolarEdgeBank

/-!
# Polar metric–holonomy commutant along a spanning tree (`thm:polar-holonomy`)

Covers `thm:polar-holonomy` of the spacetime–gauge duality paper.

**Data.**  A finite vertex set `Λ`, a finite edge bank `E` with `src tgt : E → Λ` (multi-edges
allowed), a common multiplicity space `ℂ^g` at every vertex, and invertible edge maps
`F_e = U_e P_e` with `U_e` unitary and `P_e ≻ 0`.  The typed multiplicity algebra `M_type` is
`SupportPolarBank.bankTypedMultiplicityAlgebra` (families `(R_λ)` with `R_{t(e)} F_e = F_e R_{s(e)}`
and `R_{s(e)} F_e^* = F_e^* R_{t(e)}`).

**Spanning tree.**  A spanning tree is a `SimpleGraph` `T` on `Λ` whose adjacencies are labelled
by bank edges with matching endpoints (`TreeLabel`); a tree step `u → v` transports by `U_e`
when it follows the orientation of its edge and by `U_e^*` otherwise (`stepUnitary`).  For a
root `o` and walks `p_λ : o → λ` (the tree paths, `p_o = nil`), `Q_λ` is the ordered product of
the steps along `p_λ` (`treeTransport`); `IsTree` produces the canonical choice
(`treePathTransport`).

**Results.**
* `typed_family_eq_transport`: every `(R_λ) ∈ M_type` satisfies `R_λ = Q_λ R_o Q_λ^*`
  (induction on `SimpleGraph.Walk`, `walk_transport_conj`).
* `rootResidual_eq_matCommutant` — **`eq:root-holonomy-duality`**:
  `M_type^{(o)} = {R_o : (R_λ) ∈ M_type} = 𝒪_F'` with
  `𝒪_F = C^*(K_e, W_e : e ∈ E)`, `K_e = Q_{s(e)}^* P_e² Q_{s(e)}`, `W_e = Q_{t(e)}^* U_e Q_{s(e)}`;
  and `rootHolonomyAlgebra_eq_matCommutant`: `𝒪_F = (M_type^{(o)})'`.
* `transport_family_mem`: the family associated with `R ∈ 𝒪_F'` is `R_λ = Q_λ R Q_λ^*`.
* `polar_holonomy` packages these; `polar_holonomy_tree` is the spanning-tree form.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace RenewalGeometry

namespace PolarHolonomyTree

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {g : Type*} [Fintype g] [DecidableEq g]
variable {E : Type*} {src tgt : E → Λ}

/-- A labelled tree inside the bank: every adjacency `u ~ v` of the simple graph `T` is carried
by a bank edge with endpoints `{u, v}`. -/
structure TreeLabel (T : SimpleGraph Λ) (src tgt : E → Λ) where
  /-- the bank edge carrying the tree adjacency -/
  edge : ∀ ⦃u v⦄, T.Adj u v → E
  /-- its endpoints, in one of the two orientations -/
  ends : ∀ ⦃u v⦄ (h : T.Adj u v),
    (src (edge h) = u ∧ tgt (edge h) = v) ∨ (src (edge h) = v ∧ tgt (edge h) = u)

variable {T : SimpleGraph Λ} (L : TreeLabel T src tgt) (U : E → Matrix g g ℂ)

/-- The transport of one tree step `u → v`: `U_e` along the orientation of `e`, `U_e^*`
against it. -/
noncomputable def stepUnitary {u v : Λ} (h : T.Adj u v) : Matrix g g ℂ :=
  if src (L.edge h) = u then U (L.edge h) else (U (L.edge h))ᴴ

/-- The ordered product of the step transports along a walk (the last step acts on the left). -/
noncomputable def treeTransport : ∀ {u v : Λ}, T.Walk u v → Matrix g g ℂ
  | _, _, .nil => 1
  | _, _, .cons h p => treeTransport p * stepUnitary L U h

variable {L U}

theorem stepUnitary_unitary (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {u v : Λ} (h : T.Adj u v) :
    stepUnitary L U h * (stepUnitary L U h)ᴴ = 1 ∧ (stepUnitary L U h)ᴴ * stepUnitary L U h = 1 := by
  unfold stepUnitary
  split_ifs
  · exact hU _
  · rw [conjTranspose_conjTranspose]
    exact ⟨(hU _).2, (hU _).1⟩

theorem treeTransport_unitary (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1) :
    ∀ {u v : Λ} (p : T.Walk u v),
      treeTransport L U p * (treeTransport L U p)ᴴ = 1 ∧
        (treeTransport L U p)ᴴ * treeTransport L U p = 1 := by
  intro u v p
  induction p with
  | nil => simp [treeTransport]
  | @cons u v w h p ih =>
      obtain ⟨hs1, hs2⟩ := stepUnitary_unitary (L := L) hU h
      simp only [treeTransport, conjTranspose_mul]
      constructor
      · calc treeTransport L U p * stepUnitary L U h *
              ((stepUnitary L U h)ᴴ * (treeTransport L U p)ᴴ)
            = treeTransport L U p * (stepUnitary L U h * (stepUnitary L U h)ᴴ) *
                (treeTransport L U p)ᴴ := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hs1, Matrix.mul_one, ih.1]
      · calc (stepUnitary L U h)ᴴ * (treeTransport L U p)ᴴ *
              (treeTransport L U p * stepUnitary L U h)
            = (stepUnitary L U h)ᴴ * ((treeTransport L U p)ᴴ * treeTransport L U p) *
                stepUnitary L U h := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [ih.2, Matrix.mul_one, hs2]

/-- One tree step: the conjugation relation `R_{t(e)} = U_e R_{s(e)} U_e^*` on the bank edge
carrying the step gives `R_v = S R_u S^*` for the step transport `S`. -/
theorem step_conj (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    (R : Λ → Matrix g g ℂ) (hR : ∀ e, R (tgt e) = U e * R (src e) * (U e)ᴴ)
    {u v : Λ} (h : T.Adj u v) :
    R v = stepUnitary L U h * R u * (stepUnitary L U h)ᴴ := by
  unfold stepUnitary
  rcases L.ends h with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [if_pos hs]
    have := hR (L.edge h)
    rw [hs, ht] at this
    exact this
  · have huv : u ≠ v := h.ne
    rw [if_neg (by rw [hs]; exact huv.symm), conjTranspose_conjTranspose]
    have := hR (L.edge h)
    rw [hs, ht] at this
    rw [this]
    obtain ⟨h1, h2⟩ := hU (L.edge h)
    calc R v = ((U (L.edge h))ᴴ * U (L.edge h)) * R v * ((U (L.edge h))ᴴ * U (L.edge h)) := by
          rw [h2, Matrix.one_mul, Matrix.mul_one]
      _ = (U (L.edge h))ᴴ * (U (L.edge h) * R v * (U (L.edge h))ᴴ) * U (L.edge h) := by
          simp only [Matrix.mul_assoc]

/-- **Walk induction.**  If every bank edge satisfies `R_{t(e)} = U_e R_{s(e)} U_e^*`, then along
any tree walk `p : u → v`, `R_v = Q_p R_u Q_p^*`. -/
theorem walk_transport_conj (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    (R : Λ → Matrix g g ℂ) (hR : ∀ e, R (tgt e) = U e * R (src e) * (U e)ᴴ) :
    ∀ {u v : Λ} (p : T.Walk u v),
      R v = treeTransport L U p * R u * (treeTransport L U p)ᴴ := by
  intro u v p
  induction p with
  | nil => simp [treeTransport]
  | @cons u w v h p ih =>
      rw [ih, step_conj (L := L) hU R hR h]
      simp only [treeTransport, conjTranspose_mul, Matrix.mul_assoc]

/-! ### The root-fibre data -/

variable (L U)

/-- The root transports `Q_λ` along chosen walks `p_λ : o → λ`. -/
noncomputable def rootTransport {o : Λ} (p : ∀ v, T.Walk o v) (v : Λ) : Matrix g g ℂ :=
  treeTransport L U (p v)

/-- The transported polar metric `K_e = Q_{s(e)}^* P_e² Q_{s(e)}`. -/
noncomputable def rootMetric {o : Λ} (p : ∀ v, T.Walk o v) (P : E → Matrix g g ℂ) (e : E) :
    Matrix g g ℂ :=
  (rootTransport L U p (src e))ᴴ * (P e * P e) * rootTransport L U p (src e)

/-- The relative holonomy `W_e = Q_{t(e)}^* U_e Q_{s(e)}`. -/
noncomputable def rootHolonomy {o : Λ} (p : ∀ v, T.Walk o v) (e : E) : Matrix g g ℂ :=
  (rootTransport L U p (tgt e))ᴴ * U e * rootTransport L U p (src e)

/-- The generators `{K_e, W_e}`. -/
noncomputable def rootGenerators {o : Λ} (p : ∀ v, T.Walk o v) (P : E → Matrix g g ℂ) :
    Set (Matrix g g ℂ) :=
  Set.range (rootMetric L U p P) ∪ Set.range (rootHolonomy L U p)

/-- **`eq:root-holonomy-algebra`**: `𝒪_F = C^*(K_e, W_e : e ∈ E) ⊆ M_g(ℂ)`. -/
noncomputable def rootHolonomyAlgebra {o : Λ} (p : ∀ v, T.Walk o v) (P : E → Matrix g g ℂ) :
    StarSubalgebra ℂ (Matrix g g ℂ) :=
  StarAlgebra.adjoin ℂ (rootGenerators L U p P)

/-- The edge maps `F_e = U_e P_e`. -/
def polarEdgeMap (src tgt : E → Λ) (U P : E → Matrix g g ℂ) (e : E) :
    Matrix ((fun _ : Λ => g) (tgt e)) ((fun _ : Λ => g) (src e)) ℂ :=
  U e * P e

/-- The root restriction `M_type^{(o)} = {R_o : (R_λ) ∈ M_type}` of the typed multiplicity
algebra. -/
def rootResidual (src tgt : E → Λ) (U' : E → Matrix g g ℂ) (o : Λ) (P : E → Matrix g g ℂ) :
    Set (Matrix g g ℂ) :=
  (fun R : ∀ _ : Λ, Matrix g g ℂ => R o) ''
    (SupportPolarBank.bankTypedMultiplicityAlgebra (src := src) (tgt := tgt) (fun _ : Λ => g)
      (polarEdgeMap src tgt U' P) : Set (∀ _ : Λ, Matrix g g ℂ))

variable {L U}

/-! ### The reduction -/

/-- On an invertible polar edge the typed equations are `[R_{s(e)}, P_e²] = 0` and
`R_{t(e)} = U_e R_{s(e)} U_e^*` (`polar_edge_of_posDef`). -/
theorem typed_iff_polar (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) (R : Λ → Matrix g g ℂ) :
    SupportPolarBank.IsBankTypedMultiplicity (src := src) (tgt := tgt) (fun _ : Λ => g) (polarEdgeMap src tgt U P) R ↔
      ∀ e, R (src e) * (P e * P e) = (P e * P e) * R (src e) ∧
        R (tgt e) = U e * R (src e) * (U e)ᴴ := by
  constructor
  · intro h e
    exact (polar_edge_of_posDef (U e) (P e) (R (src e)) (R (tgt e)) (hU e).1 (hU e).2
      (hP e)).mp (h e)
  · intro h e
    exact (polar_edge_of_posDef (U e) (P e) (R (src e)) (R (tgt e)) (hU e).1 (hU e).2
      (hP e)).mpr (h e)

/-- **Every residual family is transported from its root value**: `R_λ = Q_λ R_o Q_λ^*`. -/
theorem typed_family_eq_transport (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) {o : Λ} (p : ∀ v, T.Walk o v)
    (R : Λ → Matrix g g ℂ)
    (hR : SupportPolarBank.IsBankTypedMultiplicity (src := src) (tgt := tgt) (fun _ : Λ => g) (polarEdgeMap src tgt U P) R)
    (v : Λ) :
    R v = rootTransport L U p v * R o * (rootTransport L U p v)ᴴ :=
  walk_transport_conj hU R (fun e => ((typed_iff_polar hU hP R).mp hR e).2) (p v)

/-- Transported families satisfy the typed equations iff the root operator commutes with every
`K_e` and `W_e` (`smst_polar_holonomy`, clause (A), with `Q_s = Q_{s(e)}`, `Q_t = Q_{t(e)}`). -/
theorem transport_typed_iff (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) {o : Λ} (p : ∀ v, T.Walk o v)
    (R : Matrix g g ℂ) :
    SupportPolarBank.IsBankTypedMultiplicity (src := src) (tgt := tgt) (fun _ : Λ => g) (polarEdgeMap src tgt U P)
        (fun v => rootTransport L U p v * R * (rootTransport L U p v)ᴴ) ↔
      R ∈ matCommutant (rootGenerators L U p P) := by
  have hQ := fun v => treeTransport_unitary (L := L) hU (p v)
  have hedge : ∀ e, ((rootTransport L U p (tgt e) * R * (rootTransport L U p (tgt e))ᴴ) *
        (U e * P e) = (U e * P e) * (rootTransport L U p (src e) * R *
          (rootTransport L U p (src e))ᴴ) ∧
      (rootTransport L U p (src e) * R * (rootTransport L U p (src e))ᴴ) * (U e * P e)ᴴ =
        (U e * P e)ᴴ * (rootTransport L U p (tgt e) * R * (rootTransport L U p (tgt e))ᴴ)) ↔
      (R * rootMetric L U p P e = rootMetric L U p P e * R ∧
        R * rootHolonomy L U p e = rootHolonomy L U p e * R) := fun e =>
    (smst_polar_holonomy (g := g)).1 (U e) (P e) R (rootTransport L U p (src e))
      (rootTransport L U p (tgt e)) (hU e).1 (hU e).2 (hP e) (hQ _).1 (hQ _).2 (hQ _).1 (hQ _).2
  constructor
  · intro h
    rintro A (⟨e, rfl⟩ | ⟨e, rfl⟩)
    · exact ((hedge e).mp (h e)).1
    · exact ((hedge e).mp (h e)).2
  · intro h e
    exact (hedge e).mpr ⟨h _ (Or.inl ⟨e, rfl⟩), h _ (Or.inr ⟨e, rfl⟩)⟩

/-- **The family associated with `R ∈ 𝒪_F'`** is `R_λ = Q_λ R Q_λ^*`; it lies in `M_type`. -/
theorem transport_family_mem (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) {o : Λ} (p : ∀ v, T.Walk o v)
    {R : Matrix g g ℂ} (hR : R ∈ matCommutant (rootGenerators L U p P)) :
    (fun v => rootTransport L U p v * R * (rootTransport L U p v)ᴴ) ∈
      SupportPolarBank.bankTypedMultiplicityAlgebra (src := src) (tgt := tgt) (fun _ : Λ => g) (polarEdgeMap src tgt U P) :=
  (transport_typed_iff hU hP p R).mpr hR

/-- The commutant of `{K_e, W_e}` equals the commutant of `C^*(K_e, W_e)`: `K_e` is Hermitian and
`W_e` is unitary. -/
theorem matCommutant_rootHolonomyAlgebra (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) {o : Λ} (p : ∀ v, T.Walk o v) :
    matCommutant (SetLike.coe (rootHolonomyAlgebra L U p P)) =
      matCommutant (rootGenerators L U p P) := by
  have hQ : ∀ v, rootTransport L U p v * (rootTransport L U p v)ᴴ = 1 ∧
      (rootTransport L U p v)ᴴ * rootTransport L U p v = 1 :=
    fun v => treeTransport_unitary (L := L) hU (p v)
  set S := rootGenerators L U p P
  let S' : Set (Matrix g g ℂ) := S ∪ Set.range fun e => (rootHolonomy L U p e)ᴴ
  have hS' : ∀ x ∈ S', xᴴ ∈ S' := by
    rintro x ((⟨e, rfl⟩ | ⟨e, rfl⟩) | ⟨e, rfl⟩)
    · have hK : (rootMetric L U p P e)ᴴ = rootMetric L U p P e := by
        have hPH : (P e)ᴴ = P e := (hP e).isHermitian
        simp only [rootMetric, conjTranspose_mul, conjTranspose_conjTranspose, hPH,
          Matrix.mul_assoc]
      rw [hK]
      exact Or.inl (Or.inl ⟨e, rfl⟩)
    · exact Or.inr ⟨e, rfl⟩
    · rw [conjTranspose_conjTranspose]
      exact Or.inl (Or.inr ⟨e, rfl⟩)
  have hWu : ∀ e, rootHolonomy L U p e * (rootHolonomy L U p e)ᴴ = 1 := by
    intro e
    simp only [rootHolonomy, conjTranspose_mul, conjTranspose_conjTranspose]
    calc (rootTransport L U p (tgt e))ᴴ * U e * rootTransport L U p (src e) *
          ((rootTransport L U p (src e))ᴴ * ((U e)ᴴ * rootTransport L U p (tgt e)))
        = (rootTransport L U p (tgt e))ᴴ * (U e * (rootTransport L U p (src e) *
            (rootTransport L U p (src e))ᴴ) * (U e)ᴴ) * rootTransport L U p (tgt e) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [(hQ (src e)).1, Matrix.mul_one, (hU e).1, Matrix.mul_one]
          exact (hQ (tgt e)).2
  have hWu' : ∀ e, (rootHolonomy L U p e)ᴴ * rootHolonomy L U p e = 1 := by
    intro e
    simp only [rootHolonomy, conjTranspose_mul, conjTranspose_conjTranspose]
    calc (rootTransport L U p (src e))ᴴ * ((U e)ᴴ * rootTransport L U p (tgt e)) *
          ((rootTransport L U p (tgt e))ᴴ * U e * rootTransport L U p (src e))
        = (rootTransport L U p (src e))ᴴ * ((U e)ᴴ * (rootTransport L U p (tgt e) *
            (rootTransport L U p (tgt e))ᴴ) * U e) * rootTransport L U p (src e) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [(hQ (tgt e)).1, Matrix.mul_one, (hU e).2, Matrix.mul_one]
          exact (hQ (src e)).2
  have hadj : rootHolonomyAlgebra L U p P = StarAlgebra.adjoin ℂ S' := by
    apply le_antisymm
    · exact StarAlgebra.adjoin_mono Set.subset_union_left
    · rw [StarAlgebra.adjoin_le_iff]
      rintro x (hx | ⟨e, rfl⟩)
      · exact StarAlgebra.subset_adjoin ℂ _ hx
      · show (rootHolonomy L U p e)ᴴ ∈ rootHolonomyAlgebra L U p P
        rw [← Matrix.star_eq_conjTranspose]
        exact star_mem (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨e, rfl⟩))
  rw [hadj, matCommutant_starAlgebra_adjoin _ hS']
  apply le_antisymm
  · exact fun R hR A hA => hR A (Or.inl hA)
  · intro R hR A hA
    rcases hA with hA | ⟨e, rfl⟩
    · exact hR A hA
    · have hW := hR _ (Or.inr ⟨e, rfl⟩)
      set W := rootHolonomy L U p e
      calc R * Wᴴ = Wᴴ * (W * R) * Wᴴ := by
            rw [← Matrix.mul_assoc, hWu', Matrix.one_mul]
        _ = Wᴴ * (R * W) * Wᴴ := by rw [hW]
        _ = Wᴴ * R := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hWu, Matrix.mul_one]

/-- **`eq:root-holonomy-duality`, first identity**: `M_type^{(o)} = 𝒪_F'`. -/
theorem rootResidual_eq_matCommutant (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) {o : Λ} (p : ∀ v, T.Walk o v)
    (hpo : p o = SimpleGraph.Walk.nil) :
    rootResidual src tgt U o P = matCommutant (SetLike.coe (rootHolonomyAlgebra L U p P)) := by
  rw [matCommutant_rootHolonomyAlgebra hU hP p]
  have hQo : rootTransport L U p o = 1 := by
    simp [rootTransport, hpo, treeTransport]
  ext R
  constructor
  · rintro ⟨Rf, hRf, rfl⟩
    have hfam : Rf = fun v => rootTransport L U p v * Rf o * (rootTransport L U p v)ᴴ :=
      funext fun v => typed_family_eq_transport hU hP p Rf hRf v
    have hmem := hRf
    rw [SetLike.mem_coe, SupportPolarBank.mem_bankTypedMultiplicityAlgebra, hfam] at hmem
    exact (transport_typed_iff hU hP p (Rf o)).mp hmem
  · intro hR
    refine ⟨_, transport_family_mem hU hP p hR, ?_⟩
    simp only [hQo, Matrix.one_mul, conjTranspose_one, Matrix.mul_one]

/-- **`eq:root-holonomy-duality`, second identity**: `𝒪_F = (M_type^{(o)})'`. -/
theorem rootHolonomyAlgebra_eq_matCommutant (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) {o : Λ} (p : ∀ v, T.Walk o v)
    (hpo : p o = SimpleGraph.Walk.nil) :
    SetLike.coe (rootHolonomyAlgebra L U p P) = matCommutant (rootResidual src tgt U o P) := by
  rw [rootResidual_eq_matCommutant hU hP p hpo, matCommutant_matCommutant_starSubalgebra]

/-- **`thm:polar-holonomy`** (root walks `p_λ : o → λ` in a labelled tree, `p_o = nil`):
`M_type^{(o)} = 𝒪_F'`, `𝒪_F = (M_type^{(o)})'`, every `(R_λ) ∈ M_type` is `R_λ = Q_λ R_o Q_λ^*`,
and every `R ∈ 𝒪_F'` gives the residual family `R_λ = Q_λ R Q_λ^*` with root value `R`. -/
theorem polar_holonomy (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) {o : Λ} (p : ∀ v, T.Walk o v)
    (hpo : p o = SimpleGraph.Walk.nil) :
    rootResidual src tgt U o P = matCommutant (SetLike.coe (rootHolonomyAlgebra L U p P)) ∧
      SetLike.coe (rootHolonomyAlgebra L U p P) = matCommutant (rootResidual src tgt U o P) ∧
      (∀ R ∈ SupportPolarBank.bankTypedMultiplicityAlgebra (src := src) (tgt := tgt) (fun _ : Λ => g) (polarEdgeMap src tgt U P),
        ∀ v, R v = rootTransport L U p v * R o * (rootTransport L U p v)ᴴ) ∧
      (∀ R ∈ matCommutant (SetLike.coe (rootHolonomyAlgebra L U p P)),
        (fun v => rootTransport L U p v * R * (rootTransport L U p v)ᴴ) ∈
          SupportPolarBank.bankTypedMultiplicityAlgebra (src := src) (tgt := tgt) (fun _ : Λ => g) (polarEdgeMap src tgt U P)) := by
  refine ⟨rootResidual_eq_matCommutant hU hP p hpo,
    rootHolonomyAlgebra_eq_matCommutant hU hP p hpo,
    fun R hR v => typed_family_eq_transport hU hP p R hR v, fun R hR => ?_⟩
  rw [matCommutant_rootHolonomyAlgebra hU hP p] at hR
  exact transport_family_mem hU hP p hR

/-! ### The spanning-tree form -/

/-- The tree path `o → v` of a tree `T` (unique by `IsTree.existsUnique_path`). -/
noncomputable def treePath (hT : T.IsTree) (o v : Λ) : T.Walk o v :=
  (hT.existsUnique_path o v).exists.choose

theorem treePath_self (hT : T.IsTree) (o : Λ) : treePath hT o o = SimpleGraph.Walk.nil :=
  SimpleGraph.Walk.isPath_iff_eq_nil.mp (hT.existsUnique_path o o).exists.choose_spec

/-- **`thm:polar-holonomy`, spanning-tree form.**  For a spanning tree `T` of the bank (a
labelled `IsTree` simple graph on all of `Λ`, so `Γ` is connected) and a root `o`, with
`Q_λ` the ordered product of the `U_e` (inverted against the orientation) along the tree path
`o → λ`, `K_e = Q_{s(e)}^* P_e² Q_{s(e)}` and `W_e = Q_{t(e)}^* U_e Q_{s(e)}`:
`M_type^{(o)} = C^*(K_e, W_e)'` and `C^*(K_e, W_e) = (M_type^{(o)})'`; the residual family of
`R` is `R_λ = Q_λ R Q_λ^*`. -/
theorem polar_holonomy_tree (hT : T.IsTree) (o : Λ)
    (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) :
    rootResidual src tgt U o P =
        matCommutant (SetLike.coe (rootHolonomyAlgebra L U (treePath hT o) P)) ∧
      SetLike.coe (rootHolonomyAlgebra L U (treePath hT o) P) =
        matCommutant (rootResidual src tgt U o P) ∧
      (∀ R ∈ SupportPolarBank.bankTypedMultiplicityAlgebra (src := src) (tgt := tgt) (fun _ : Λ => g) (polarEdgeMap src tgt U P),
        ∀ v, R v = rootTransport L U (treePath hT o) v * R o *
          (rootTransport L U (treePath hT o) v)ᴴ) ∧
      (∀ R ∈ matCommutant (SetLike.coe (rootHolonomyAlgebra L U (treePath hT o) P)),
        (fun v => rootTransport L U (treePath hT o) v * R *
            (rootTransport L U (treePath hT o) v)ᴴ) ∈
          SupportPolarBank.bankTypedMultiplicityAlgebra (src := src) (tgt := tgt) (fun _ : Λ => g) (polarEdgeMap src tgt U P)) :=
  polar_holonomy hU hP (treePath hT o) (treePath_self hT o)

/-! ### Connected banks: existence of a labelled spanning tree -/

variable (src tgt) in
/-- The underlying simple graph `Γ` of the bank: `u ~ v` iff `u ≠ v` and some bank edge joins
them (in either orientation). -/
def bankGraph : SimpleGraph Λ :=
  SimpleGraph.fromRel fun u v => ∃ e, src e = u ∧ tgt e = v

theorem bankGraph_adj_exists {u v : Λ} (h : (bankGraph src tgt).Adj u v) :
    ∃ e, (src e = u ∧ tgt e = v) ∨ (src e = v ∧ tgt e = u) := by
  rcases (SimpleGraph.fromRel_adj _ u v).mp h with ⟨-, ⟨e, hs, ht⟩ | ⟨e, hs, ht⟩⟩
  · exact ⟨e, Or.inl ⟨hs, ht⟩⟩
  · exact ⟨e, Or.inr ⟨hs, ht⟩⟩

/-- Every subgraph of the bank graph (e.g. a spanning tree of `Γ`) carries a bank labelling. -/
noncomputable def treeLabelOfLE {T : SimpleGraph Λ} (hle : T ≤ bankGraph src tgt) :
    TreeLabel T src tgt where
  edge _ _ h := Classical.choose (bankGraph_adj_exists (hle h))
  ends _ _ h := Classical.choose_spec (bankGraph_adj_exists (hle h))

/-- **`thm:polar-holonomy` for a connected bank.**  If `Γ` is connected, there is a spanning tree
`T ≤ Γ`; with the root `o`, the tree-path transports `Q_λ`, `K_e = Q_{s(e)}^* P_e² Q_{s(e)}` and
`W_e = Q_{t(e)}^* U_e Q_{s(e)}`, `M_type^{(o)} = C^*(K_e, W_e)'` and
`C^*(K_e, W_e) = (M_type^{(o)})'`. -/
theorem polar_holonomy_connected (hconn : (bankGraph src tgt).Connected) (o : Λ)
    (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) :
    ∃ (T : SimpleGraph Λ) (hT : T.IsTree) (hle : T ≤ bankGraph src tgt),
      rootResidual src tgt U o P =
          matCommutant (SetLike.coe
            (rootHolonomyAlgebra (treeLabelOfLE hle) U (treePath hT o) P)) ∧
        SetLike.coe (rootHolonomyAlgebra (treeLabelOfLE hle) U (treePath hT o) P) =
          matCommutant (rootResidual src tgt U o P) := by
  obtain ⟨T, hle, hT⟩ := hconn.exists_isTree_le
  exact ⟨T, hT, hle, (polar_holonomy_tree (L := treeLabelOfLE hle) hT o hU hP).1,
    (polar_holonomy_tree (L := treeLabelOfLE hle) hT o hU hP).2.1⟩

end PolarHolonomyTree

end RenewalGeometry
