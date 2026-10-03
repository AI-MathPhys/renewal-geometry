/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.PolarHolonomyTreeTransport
import RenewalGeometry.Commutant.PolarFlatIrreducibleLimits

/-!
# Flat and irreducible extremes of the root residual algebra (`cor:polar-extremes`)

Covers `cor:polar-extremes` of the spacetime–gauge duality paper, stated on the root residual
multiplicity algebra `M_type^{(o)} = rootResidual` of `thm:polar-holonomy`
(`PolarHolonomyTreeTransport.lean`, where `M_type^{(o)} = 𝒪_F'` is proved):

* (i)  `polar_extremes_flat`: `M_type^{(o)} = M_g(ℂ)` iff every `K_e` and every `W_e` is scalar;
* (ii) `polar_extremes_irreducible`: `M_type^{(o)} = ℂ I` iff `𝒪_F = M_g(ℂ)`;
* (iii) `polar_extremes_unitary`: if every `F_e` is unitary then `K_e = I` and
  `M_type^{(o)} = {W_e}'` (only the relative cycle holonomy obstructs);
* (iv) `polar_extremes_tree_reduction`: on the two-vertex tree with one edge `F = U P`,
  `U = I`, `P = diag(2, 1) ≻ 0` (non-scalar), the residual algebra is a proper subalgebra of
  `M_2(ℂ)`; this explicit packet is also a non-vacuity witness for `thm:polar-holonomy`.
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
variable {T : SimpleGraph Λ} {L : TreeLabel T src tgt} {U : E → Matrix g g ℂ}

/-- **(i) Flat extreme.**  `M_type^{(o)} = M_g(ℂ)` iff every `K_e` and `W_e` is scalar. -/
theorem polar_extremes_flat (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) {o : Λ} (p : ∀ v, T.Walk o v)
    (hpo : p o = SimpleGraph.Walk.nil) :
    rootResidual src tgt U o P = Set.univ ↔
      ∀ e, (∃ α : ℂ, rootMetric L U p P e = α • 1) ∧
        (∃ α : ℂ, rootHolonomy L U p e = α • 1) := by
  rw [rootResidual_eq_matCommutant (L := L) hU hP p hpo, matCommutant_rootHolonomyAlgebra hU hP p,
    matCommutant_eq_univ_iff_generators_scalar]
  constructor
  · intro h e
    exact ⟨h _ (Or.inl ⟨e, rfl⟩), h _ (Or.inr ⟨e, rfl⟩)⟩
  · rintro h A (⟨e, rfl⟩ | ⟨e, rfl⟩)
    · exact (h e).1
    · exact (h e).2

/-- **(ii) Irreducible extreme.**  `M_type^{(o)} = ℂ I` iff `𝒪_F = C^*(K_e, W_e) = M_g(ℂ)`. -/
theorem polar_extremes_irreducible (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) {o : Λ} (p : ∀ v, T.Walk o v)
    (hpo : p o = SimpleGraph.Walk.nil) :
    rootResidual src tgt U o P = Set.range (fun α : ℂ => α • (1 : Matrix g g ℂ)) ↔
      rootHolonomyAlgebra L U p P = ⊤ := by
  rw [rootResidual_eq_matCommutant (L := L) hU hP p hpo]
  have hstar : ∀ A ∈ (rootHolonomyAlgebra L U p P).toSubalgebra,
      Aᴴ ∈ (rootHolonomyAlgebra L U p P).toSubalgebra := fun A hA => by
    rw [← Matrix.star_eq_conjTranspose]
    exact (rootHolonomyAlgebra L U p P).star_mem' hA
  have h := matCommutant_eq_scalars_iff_eq_top (rootHolonomyAlgebra L U p P).toSubalgebra hstar
  have htop : (rootHolonomyAlgebra L U p P).toSubalgebra = ⊤ ↔ rootHolonomyAlgebra L U p P = ⊤ :=
    ⟨fun h' => StarSubalgebra.toSubalgebra_injective (by rw [h', StarSubalgebra.top_toSubalgebra]),
      fun h' => by rw [h', StarSubalgebra.top_toSubalgebra]⟩
  rw [← htop]
  exact h

/-- **(iii) Unitary edges.**  If every `F_e = U_e P_e` is unitary then every `K_e = I`, and the
residual algebra is the commutant of the relative cycle holonomies `W_e` alone. -/
theorem polar_extremes_unitary (hU : ∀ e, U e * (U e)ᴴ = 1 ∧ (U e)ᴴ * U e = 1)
    {P : E → Matrix g g ℂ} (hP : ∀ e, (P e).PosDef) {o : Λ} (p : ∀ v, T.Walk o v)
    (hpo : p o = SimpleGraph.Walk.nil)
    (hF : ∀ e, (U e * P e)ᴴ * (U e * P e) = 1) :
    (∀ e, rootMetric L U p P e = 1) ∧
      rootResidual src tgt U o P = matCommutant (Set.range (rootHolonomy L U p)) := by
  have hK : ∀ e, rootMetric L U p P e = 1 := by
    intro e
    have hPH : (P e)ᴴ = P e := (hP e).isHermitian
    have hPP : P e * P e = 1 := by
      have := hF e
      rw [conjTranspose_mul, hPH, Matrix.mul_assoc, ← Matrix.mul_assoc (U e)ᴴ, (hU e).2,
        Matrix.one_mul] at this
      exact this
    simp only [rootMetric, hPP, Matrix.mul_one]
    exact (treeTransport_unitary (L := L) hU (p (src e))).2
  refine ⟨hK, ?_⟩
  rw [rootResidual_eq_matCommutant (L := L) hU hP p hpo, matCommutant_rootHolonomyAlgebra hU hP p]
  ext R
  constructor
  · intro hR A hA
    exact hR A (Or.inr hA)
  · rintro hR A (⟨e, rfl⟩ | hA)
    · rw [hK e, Matrix.mul_one, Matrix.one_mul]
    · exact hR A hA

/-! ### (iv) A non-scalar positive metric on a tree -/

/-- The two-vertex tree `⊤` on `Fin 2`, every adjacency carried by the single bank edge
`0 → 1`. -/
def twoVertexLabel :
    TreeLabel (⊤ : SimpleGraph (Fin 2)) (fun _ : Unit => (0 : Fin 2)) (fun _ : Unit => 1) where
  edge _ _ _ := ()
  ends u v h := by
    have huv : u ≠ v := h
    fin_cases u <;> fin_cases v <;> simp_all

theorem isTree_top_fin_two : (⊤ : SimpleGraph (Fin 2)).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨SimpleGraph.connected_top, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

/-- The positive non-scalar polar metric `P = diag(2, 1)`. -/
def treeMetric : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![2, 1]

theorem treeMetric_posDef : treeMetric.PosDef := by
  rw [treeMetric, Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> simp

theorem treeMetric_sq_not_scalar : ¬ ∃ α : ℂ, treeMetric * treeMetric = α • 1 := by
  rintro ⟨α, hα⟩
  have h0 := congrFun (congrFun hα 0) 0
  have h1 := congrFun (congrFun hα 1) 1
  simp [treeMetric] at h0 h1
  rw [← h0] at h1
  norm_num at h1

/-- **(iv)** Even on a tree, a non-scalar positive polar metric reduces the residual multiplicity
algebra: for the two-vertex tree with `F = U P`, `U = I`, `P = diag(2,1) ≻ 0`, the root residual
algebra `M_type^{(o)}` is a proper subset of `M_2(ℂ)`; it is the commutant of
`K = Q_0^* P² Q_0 = diag(4, 1)`. -/
theorem polar_extremes_tree_reduction :
    treeMetric.PosDef ∧ (¬ ∃ α : ℂ, treeMetric * treeMetric = α • 1) ∧
      rootResidual (fun _ : Unit => (0 : Fin 2)) (fun _ : Unit => 1) (fun _ => 1) 0
          (fun _ => treeMetric) ≠ Set.univ := by
  refine ⟨treeMetric_posDef, treeMetric_sq_not_scalar, ?_⟩
  intro hfull
  have hU : ∀ _ : Unit, (1 : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 ∧
      (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * 1 = 1 := fun _ => by simp
  have h := (polar_extremes_flat (L := twoVertexLabel) hU (fun _ => treeMetric_posDef)
    (treePath isTree_top_fin_two 0) (treePath_self isTree_top_fin_two 0)).mp hfull ()
  obtain ⟨α, hα⟩ := h.1
  apply treeMetric_sq_not_scalar
  refine ⟨α, ?_⟩
  have hQ := (treeTransport_unitary (L := twoVertexLabel) hU
    (treePath isTree_top_fin_two 0 0))
  simp only [rootMetric, rootTransport] at hα
  rw [treePath_self isTree_top_fin_two 0] at hα
  simpa [treeTransport] using hα

/-- Non-vacuity of `thm:polar-holonomy`: the theorem instantiated on the explicit tree packet. -/
example :
    rootResidual (fun _ : Unit => (0 : Fin 2)) (fun _ : Unit => 1) (fun _ => 1) 0
        (fun _ => treeMetric) =
      matCommutant (SetLike.coe (rootHolonomyAlgebra twoVertexLabel (fun _ => 1)
        (treePath isTree_top_fin_two 0) (fun _ => treeMetric))) :=
  (polar_holonomy_tree (L := twoVertexLabel) isTree_top_fin_two 0 (fun _ => by simp)
    (fun _ => treeMetric_posDef)).1

end PolarHolonomyTree

end RenewalGeometry
