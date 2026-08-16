/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteUnitaryBlockCarrier
import NCG.Grand.FiniteGaugeInvariantBasis
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Vertex intertwiner spaces and spin-network contractions

An edge block label determines incoming defining factors and outgoing dual
factors at every vertex. Their fixed subspace has a finite orthonormal basis.
A spin label is one edge irreducible label plus one invariant-basis label at
each vertex; `contractedSpinFunction` performs the full index contraction.
-/

namespace NCG.FiniteSpinNetwork

open NCG.FinitePeterWeyl
open scoped PiTensorProduct

variable {G V E : Type*} [Group G] [Fintype G] [Fintype V]
  [Fintype E] [DecidableEq V] [DecidableEq E]

abbrev EdgeRepresentationLabel
    (D : MatrixBlockDecomposition G) (E : Type*) := E → Fin D.count

abbrev IncomingIndex (D : MatrixBlockDecomposition G)
    (t : E → V) (π : EdgeRepresentationLabel D E) (v : V) :=
  (e : {e : E // t e = v}) → Fin (D.dimension (π e.1))

abbrev OutgoingIndex (D : MatrixBlockDecomposition G)
    (s : E → V) (π : EdgeRepresentationLabel D E) (v : V) :=
  (e : {e : E // s e = v}) → Fin (D.dimension (π e.1))

/-- Coordinate index of `(⊗ incoming V_π) ⊗ (⊗ outgoing V_π*)`. -/
abbrev VertexTensorIndex (D : MatrixBlockDecomposition G)
    (t s : E → V) (π : EdgeRepresentationLabel D E) (v : V) :=
  IncomingIndex D t π v × OutgoingIndex D s π v

abbrev VertexTensorSpace (D : MatrixBlockDecomposition G)
    (t s : E → V) (π : EdgeRepresentationLabel D E) (v : V) :=
  EuclideanSpace ℂ (VertexTensorIndex D t s π v)

/-- Regroup global row indices by their target vertices. -/
def rowVertexEquiv (D : MatrixBlockDecomposition G)
    (t : E → V) (π : EdgeRepresentationLabel D E) :
    ((e : E) → Fin (D.dimension (π e))) ≃
      ((v : V) → IncomingIndex D t π v) where
  toFun row v e := row e.1
  invFun family e := family (t e) ⟨e, rfl⟩
  left_inv row := by
    funext e
    rfl
  right_inv family := by
    funext v e
    obtain ⟨e, he⟩ := e
    subst v
    rfl

@[simp] theorem rowVertexEquiv_apply (D : MatrixBlockDecomposition G)
    (t : E → V) (π : EdgeRepresentationLabel D E)
    (row : (e : E) → Fin (D.dimension (π e))) (v : V)
    (e : {e : E // t e = v}) :
    (rowVertexEquiv D t π row v) e = row e.1 := rfl

/-- Regroup global column indices by their source vertices. -/
def colVertexEquiv (D : MatrixBlockDecomposition G)
    (s : E → V) (π : EdgeRepresentationLabel D E) :
    ((e : E) → Fin (D.dimension (π e))) ≃
      ((v : V) → OutgoingIndex D s π v) where
  toFun col v e := col e.1
  invFun family e := family (s e) ⟨e, rfl⟩
  left_inv col := by
    funext e
    rfl
  right_inv family := by
    funext v e
    obtain ⟨e, he⟩ := e
    subst v
    rfl
@[simp] theorem colVertexEquiv_apply (D : MatrixBlockDecomposition G)
    (s : E → V) (π : EdgeRepresentationLabel D E)
    (col : (e : E) → Fin (D.dimension (π e))) (v : V)
    (e : {e : E // s e = v}) :
    (colVertexEquiv D s π col v) e = col e.1 := rfl

/-- Incoming half-edges, grouped by target, are exactly the edge set. -/
def targetHalfEdgeEquiv (t : E → V) :
    (Σ v : V, {e : E // t e = v}) ≃ E where
  toFun x := x.2.1
  invFun e := ⟨t e, ⟨e, rfl⟩⟩
  left_inv x := by
    obtain ⟨v, e, he⟩ := x
    subst v
    rfl
  right_inv e := rfl

/-- Outgoing half-edges, grouped by source, are exactly the edge set. -/
def sourceHalfEdgeEquiv (s : E → V) :
    (Σ v : V, {e : E // s e = v}) ≃ E where
  toFun x := x.2.1
  invFun e := ⟨s e, ⟨e, rfl⟩⟩
  left_inv x := by
    obtain ⟨v, e, he⟩ := x
    subst v
    rfl
  right_inv e := rfl

theorem prod_edges_eq_prod_incoming_vertices
    (t : E → V) (f : E → ℂ) :
    (∏ e : E, f e) =
      ∏ v : V, ∏ e : {e : E // t e = v}, f e.1 := by
  calc
    (∏ e : E, f e) =
        ∏ x : Σ v : V, {e : E // t e = v},
          f ((targetHalfEdgeEquiv t) x) :=
      ((targetHalfEdgeEquiv t).prod_comp f).symm
    _ = ∏ v : V, ∏ e : {e : E // t e = v}, f e.1 :=
      Fintype.prod_sigma _

theorem prod_edges_eq_prod_outgoing_vertices
    (s : E → V) (f : E → ℂ) :
    (∏ e : E, f e) =
      ∏ v : V, ∏ e : {e : E // s e = v}, f e.1 := by
  calc
    (∏ e : E, f e) =
        ∏ x : Σ v : V, {e : E // s e = v},
          f ((sourceHalfEdgeEquiv s) x) :=
      ((sourceHalfEdgeEquiv s).prod_comp f).symm
    _ = ∏ v : V, ∏ e : {e : E // s e = v}, f e.1 :=
      Fintype.prod_sigma _
/-- Tensor-product matrix kernel on all incoming defining factors. -/
noncomputable def incomingKernel (D : MatrixBlockDecomposition G)
    (t : E → V) (π : EdgeRepresentationLabel D E) (v : V)
    (h : G) (x y : IncomingIndex D t π v) : ℂ :=
  ∏ e : {e : E // t e = v}, normalizedBlockMatrix D (π e.1) h (x e) (y e)

/-- A finite double sum of a vertexwise product factors into independent
vertex sums. -/
theorem sum_pi_pair_prod {A B : V → Type*}
    [∀ v, Fintype (A v)] [∀ v, Fintype (B v)]
    (f : ∀ v, A v → B v → ℂ) :
    (∑ a : (v : V) → A v, ∑ b : (v : V) → B v,
      ∏ v : V, f v (a v) (b v)) =
      ∏ v : V, ∑ x : A v, ∑ y : B v, f v x y := by
  classical
  symm
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.prod_sum]


/-- Cyclically move the last two indices of a finite fourfold sum to the
front. -/
theorem sum_four_rotate {A B C D₀ : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D₀]
    (f : A → B → C → D₀ → ℂ) :
    (∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D₀, f a b c d) =
      ∑ d : D₀, ∑ c : C, ∑ a : A, ∑ b : B, f a b c d := by
  classical
  calc
    _ = ∑ a : A, ∑ b : B, ∑ d : D₀, ∑ c : C, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ a : A, ∑ d : D₀, ∑ b : B, ∑ c : C, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ d : D₀, ∑ a : A, ∑ b : B, ∑ c : C, f a b c d := by
      exact Finset.sum_comm
    _ = ∑ d : D₀, ∑ a : A, ∑ c : C, ∑ b : B, f a b c d := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ d : D₀, ∑ c : C, ∑ a : A, ∑ b : B, f a b c d := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm

/-- Tensor-product matrix kernel on all outgoing dual factors. -/
noncomputable def outgoingDualKernel (D : MatrixBlockDecomposition G)
    (s : E → V) (π : EdgeRepresentationLabel D E) (v : V)
    (h : G) (x y : OutgoingIndex D s π v) : ℂ :=
  ∏ e : {e : E // s e = v}, normalizedBlockMatrix D (π e.1) h⁻¹ (y e) (x e)

@[simp]
theorem star_incomingKernel_inv (D : MatrixBlockDecomposition G)
    (t : E → V) (π : EdgeRepresentationLabel D E) (v : V)
    (h : G) (x y : IncomingIndex D t π v) :
    star (incomingKernel D t π v h⁻¹ x y) =
      incomingKernel D t π v h y x := by
  classical
  simp [incomingKernel, normalizedBlockMatrix_inv_eq_star]

@[simp]
theorem star_outgoingDualKernel_inv (D : MatrixBlockDecomposition G)
    (s : E → V) (π : EdgeRepresentationLabel D E) (v : V)
    (h : G) (x y : OutgoingIndex D s π v) :
    star (outgoingDualKernel D s π v h⁻¹ x y) =
      outgoingDualKernel D s π v h y x := by
  classical
  simp [outgoingDualKernel, normalizedBlockMatrix_inv_eq_star]
noncomputable def vertexActionValue (D : MatrixBlockDecomposition G)
    (t s : E → V) (π : EdgeRepresentationLabel D E) (v : V)
    (h : G) (F : VertexTensorSpace D t s π v)
    (x : VertexTensorIndex D t s π v) : ℂ :=
  ∑ y : VertexTensorIndex D t s π v,
    incomingKernel D t π v h x.1 y.1 *
      outgoingDualKernel D s π v h x.2 y.2 * F.ofLp y

/-- Fixed vectors of the incoming-defining/outgoing-dual vertex action. -/
def VertexInvariantSubspace (D : MatrixBlockDecomposition G)
    (t s : E → V) (π : EdgeRepresentationLabel D E) (v : V) :
    Submodule ℂ (VertexTensorSpace D t s π v) where
  carrier := {F | ∀ (h : G) (x : VertexTensorIndex D t s π v),
    vertexActionValue D t s π v h F x = F.ofLp x}
  zero_mem' := by
    intro h x
    simp [vertexActionValue]
  add_mem' := by
    intro F K hF hK h x
    change vertexActionValue D t s π v h (F + K) x = (F + K).ofLp x
    calc
      vertexActionValue D t s π v h (F + K) x
          = vertexActionValue D t s π v h F x +
            vertexActionValue D t s π v h K x := by
              simp [vertexActionValue, mul_add, Finset.sum_add_distrib]
      _ = F.ofLp x + K.ofLp x := by rw [hF h x, hK h x]
      _ = (F + K).ofLp x := rfl
  smul_mem' := by
    intro c F hF h x
    change vertexActionValue D t s π v h (c • F) x = (c • F).ofLp x
    calc
      vertexActionValue D t s π v h (c • F) x
          = c * vertexActionValue D t s π v h F x := by
              simp only [vertexActionValue, WithLp.ofLp_smul, Pi.smul_apply,
                smul_eq_mul]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = c * F.ofLp x := by rw [hF h x]
      _ = (c • F).ofLp x := rfl

abbrev IntertwinerIndex (D : MatrixBlockDecomposition G)
    (t s : E → V) (π : EdgeRepresentationLabel D E) (v : V) :=
  Fin (Module.finrank ℂ (VertexInvariantSubspace D t s π v))

/-- Orthonormal basis of the local invariant tensor space. -/
noncomputable def vertexIntertwinerBasis
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) :
    OrthonormalBasis (IntertwinerIndex D t s π v) ℂ
      (VertexInvariantSubspace D t s π v) :=
  stdOrthonormalBasis ℂ (VertexInvariantSubspace D t s π v)

theorem vertexIntertwiner_invariant
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V)
    (a : IntertwinerIndex D t s π v) (h : G)
    (x : VertexTensorIndex D t s π v) :
    vertexActionValue D t s π v h
        (vertexIntertwinerBasis D t s π v a).1 x =
      (vertexIntertwinerBasis D t s π v a).1.ofLp x :=
  (vertexIntertwinerBasis D t s π v a).property h x

/-- The conjugated coordinates of an invariant vertex tensor form an
invariant bra.  This is the local identity used when contracting transformed
edge matrix coefficients. -/
theorem vertexIntertwiner_bra_invariant
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V)
    (a : IntertwinerIndex D t s π v) (h : G)
    (x : VertexTensorIndex D t s π v) :
    (∑ y : VertexTensorIndex D t s π v,
      star ((vertexIntertwinerBasis D t s π v a).1.ofLp y) *
        incomingKernel D t π v h y.1 x.1 *
        outgoingDualKernel D s π v h y.2 x.2) =
      star ((vertexIntertwinerBasis D t s π v a).1.ofLp x) := by
  have hinv := vertexIntertwiner_invariant D t s π v a h⁻¹ x
  have hstar := congrArg star hinv
  simpa [vertexActionValue, map_sum, map_mul, mul_comm, mul_left_comm,
    mul_assoc] using hstar
/-- One irreducible representation per edge and one intertwiner per vertex. -/
structure Label (D : MatrixBlockDecomposition G) (t s : E → V) where
  edgeRepresentation : EdgeRepresentationLabel D E
  vertexIntertwiner :
    (v : V) → IntertwinerIndex D t s edgeRepresentation v

def vertexTensorIndexOf (D : MatrixBlockDecomposition G)
    (t s : E → V) (π : EdgeRepresentationLabel D E)
    (row col : (e : E) → Fin (D.dimension (π e))) (v : V) :
    VertexTensorIndex D t s π v :=
  ⟨fun e => row e.1, fun e => col e.1⟩


@[simp] theorem vertexTensorIndexOf_regroup (D : MatrixBlockDecomposition G)
    (t s : E → V) (π : EdgeRepresentationLabel D E)
    (row col : (e : E) → Fin (D.dimension (π e))) (v : V) :
    vertexTensorIndexOf D t s π row col v =
      ((rowVertexEquiv D t π) row v, (colVertexEquiv D s π) col v) := rfl

/-- Product of all chosen vertex-intertwiner coordinates. -/
noncomputable def vertexContraction (D : MatrixBlockDecomposition G)
    (t s : E → V) (L : Label D t s)
    (row col : (e : E) → Fin (D.dimension (L.edgeRepresentation e))) : ℂ :=
  ∏ v : V, star ((vertexIntertwinerBasis D t s L.edgeRepresentation v
    (L.vertexIntertwiner v)).1.ofLp
      (vertexTensorIndexOf D t s L.edgeRepresentation row col v))

/-- Product of normalized unitary matrix coefficients over all edges. -/
noncomputable def normalizedEdgeCoefficient
    (D : MatrixBlockDecomposition G) (π : EdgeRepresentationLabel D E)
    (row col : (e : E) → Fin (D.dimension (π e)))
    (g : E → G) : ℂ :=
  ∏ e : E, normalizedBlockMatrix D (π e) (g e) (row e) (col e)

theorem normalizedEdgeCoefficient_gauge_expand
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E)
    (row col : (e : E) → Fin (D.dimension (π e)))
    (h : V → G) (g : E → G) :
    normalizedEdgeCoefficient D π row col (NCG.gaugeAct t s h g) =
      ∑ q : (e : E) → Fin (D.dimension (π e)),
        ∑ p : (e : E) → Fin (D.dimension (π e)),
          ∏ e : E,
            normalizedBlockMatrix D (π e) (h (t e)) (row e) (p e) *
              normalizedBlockMatrix D (π e) (g e) (p e) (q e) *
              normalizedBlockMatrix D (π e) (h (s e))⁻¹ (q e) (col e) := by
  classical
  unfold normalizedEdgeCoefficient NCG.gaugeAct
  simp_rw [normalizedBlockMatrix_endpoint_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fintype.prod_sum]
theorem edge_transport_product_factor
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E)
    (row col p q : (e : E) → Fin (D.dimension (π e)))
    (h : V → G) (g : E → G) :
    (∏ e : E,
      normalizedBlockMatrix D (π e) (h (t e)) (row e) (p e) *
        normalizedBlockMatrix D (π e) (g e) (p e) (q e) *
        normalizedBlockMatrix D (π e) (h (s e))⁻¹ (q e) (col e)) =
      (∏ v : V,
        incomingKernel D t π v (h v)
            ((rowVertexEquiv D t π) row v) ((rowVertexEquiv D t π) p v) *
          outgoingDualKernel D s π v (h v)
            ((colVertexEquiv D s π) col v) ((colVertexEquiv D s π) q v)) *
        normalizedEdgeCoefficient D π p q g := by
  have hIncoming :
      (∏ v : V, ∏ e : {e : E // t e = v},
        normalizedBlockMatrix D (π e.1) (h (t e.1))
          (row e.1) (p e.1)) =
        ∏ v : V,
          incomingKernel D t π v (h v)
            ((rowVertexEquiv D t π) row v)
            ((rowVertexEquiv D t π) p v) := by
    unfold incomingKernel
    apply Finset.prod_congr rfl
    intro v _
    apply Finset.prod_congr rfl
    intro e _
    rw [e.property]
    rfl
  have hOutgoing :
      (∏ v : V, ∏ e : {e : E // s e = v},
        normalizedBlockMatrix D (π e.1) (h (s e.1))⁻¹
          (q e.1) (col e.1)) =
        ∏ v : V,
          outgoingDualKernel D s π v (h v)
            ((colVertexEquiv D s π) col v)
            ((colVertexEquiv D s π) q v) := by
    unfold outgoingDualKernel
    apply Finset.prod_congr rfl
    intro v _
    apply Finset.prod_congr rfl
    intro e _
    rw [e.property]
    rfl
  classical
  unfold normalizedEdgeCoefficient
  calc
    (∏ e : E,
      normalizedBlockMatrix D (π e) (h (t e)) (row e) (p e) *
        normalizedBlockMatrix D (π e) (g e) (p e) (q e) *
        normalizedBlockMatrix D (π e) (h (s e))⁻¹ (q e) (col e)) =
      (∏ e : E, normalizedBlockMatrix D (π e) (h (t e)) (row e) (p e)) *
      (∏ e : E, normalizedBlockMatrix D (π e) (h (s e))⁻¹ (q e) (col e)) *
      (∏ e : E, normalizedBlockMatrix D (π e) (g e) (p e) (q e)) := by
        simp only [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro e _
        ring
    _ = (∏ v : V,
        incomingKernel D t π v (h v)
            ((rowVertexEquiv D t π) row v) ((rowVertexEquiv D t π) p v)) *
      (∏ v : V,
        outgoingDualKernel D s π v (h v)
            ((colVertexEquiv D s π) col v) ((colVertexEquiv D s π) q v)) *
      (∏ e : E, normalizedBlockMatrix D (π e) (g e) (p e) (q e)) := by
        rw [prod_edges_eq_prod_incoming_vertices t
            (fun e => normalizedBlockMatrix D (π e) (h (t e))
              (row e) (p e)),
          prod_edges_eq_prod_outgoing_vertices s
            (fun e => normalizedBlockMatrix D (π e) (h (s e))⁻¹
              (q e) (col e))]
        rw [hIncoming, hOutgoing]
    _ = (∏ v : V,
        incomingKernel D t π v (h v)
            ((rowVertexEquiv D t π) row v) ((rowVertexEquiv D t π) p v) *
          outgoingDualKernel D s π v (h v)
            ((colVertexEquiv D s π) col v) ((colVertexEquiv D s π) q v)) *
      (∏ e : E, normalizedBlockMatrix D (π e) (g e) (p e) (q e)) := by
        rw [Finset.prod_mul_distrib]

/-- Summing the transformed endpoint indices against invariant vertex bras
returns the original contraction coefficient. -/
theorem vertexContraction_transport_sum
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (L : Label D t s)
    (p q : (e : E) → Fin (D.dimension (L.edgeRepresentation e)))
    (h : V → G) :
    (∑ row : (e : E) → Fin (D.dimension (L.edgeRepresentation e)),
      ∑ col : (e : E) → Fin (D.dimension (L.edgeRepresentation e)),
        vertexContraction D t s L row col *
          ∏ v : V,
            incomingKernel D t L.edgeRepresentation v (h v)
                ((rowVertexEquiv D t L.edgeRepresentation) row v)
                ((rowVertexEquiv D t L.edgeRepresentation) p v) *
              outgoingDualKernel D s L.edgeRepresentation v (h v)
                ((colVertexEquiv D s L.edgeRepresentation) col v)
                ((colVertexEquiv D s L.edgeRepresentation) q v)) =
      vertexContraction D t s L p q := by
  classical
  calc
    _ = ∑ rowFamily : (v : V) → IncomingIndex D t L.edgeRepresentation v,
        ∑ colFamily : (v : V) → OutgoingIndex D s L.edgeRepresentation v,
          ∏ v : V,
            star ((vertexIntertwinerBasis D t s L.edgeRepresentation v
              (L.vertexIntertwiner v)).1.ofLp (rowFamily v, colFamily v)) *
              incomingKernel D t L.edgeRepresentation v (h v)
                (rowFamily v)
                ((rowVertexEquiv D t L.edgeRepresentation) p v) *
              outgoingDualKernel D s L.edgeRepresentation v (h v)
                (colFamily v)
                ((colVertexEquiv D s L.edgeRepresentation) q v) := by
          rw [← (rowVertexEquiv D t L.edgeRepresentation).symm.sum_comp]
          simp_rw [← (colVertexEquiv D s L.edgeRepresentation).symm.sum_comp]
          simp only [vertexContraction, vertexTensorIndexOf_regroup,
            Equiv.apply_symm_apply, ← Finset.prod_mul_distrib, mul_assoc]
    _ = ∏ v : V,
        ∑ rowIndex : IncomingIndex D t L.edgeRepresentation v,
          ∑ colIndex : OutgoingIndex D s L.edgeRepresentation v,
            star ((vertexIntertwinerBasis D t s L.edgeRepresentation v
              (L.vertexIntertwiner v)).1.ofLp (rowIndex, colIndex)) *
              incomingKernel D t L.edgeRepresentation v (h v)
                rowIndex ((rowVertexEquiv D t L.edgeRepresentation) p v) *
              outgoingDualKernel D s L.edgeRepresentation v (h v)
                colIndex ((colVertexEquiv D s L.edgeRepresentation) q v) := by
          exact sum_pi_pair_prod (V := V)
            (A := fun v => IncomingIndex D t L.edgeRepresentation v)
            (B := fun v => OutgoingIndex D s L.edgeRepresentation v)
            (fun v rowIndex colIndex =>
              star ((vertexIntertwinerBasis D t s
                L.edgeRepresentation v (L.vertexIntertwiner v)).1.ofLp
                  (rowIndex, colIndex)) *
                incomingKernel D t L.edgeRepresentation v (h v)
                  rowIndex
                  ((rowVertexEquiv D t L.edgeRepresentation) p v) *
                outgoingDualKernel D s L.edgeRepresentation v (h v)
                  colIndex
                  ((colVertexEquiv D s L.edgeRepresentation) q v))
    _ = ∏ v : V,
        star ((vertexIntertwinerBasis D t s L.edgeRepresentation v
          (L.vertexIntertwiner v)).1.ofLp
            ((rowVertexEquiv D t L.edgeRepresentation) p v,
              (colVertexEquiv D s L.edgeRepresentation) q v)) := by
          apply Finset.prod_congr rfl
          intro v _
          simpa only [Fintype.sum_prod_type] using
            (vertexIntertwiner_bra_invariant D t s L.edgeRepresentation v
              (L.vertexIntertwiner v) (h v)
              ((rowVertexEquiv D t L.edgeRepresentation) p v,
                (colVertexEquiv D s L.edgeRepresentation) q v))
    _ = vertexContraction D t s L p q := by
          rfl

/-- Full contraction of vertex intertwiners with the normalized unitary edge
matrix coefficients. -/
noncomputable def contractedSpinFunction (D : MatrixBlockDecomposition G)
    (t s : E → V) (L : Label D t s) : (E → G) → ℂ := fun g =>
  ∑ row : (e : E) → Fin (D.dimension (L.edgeRepresentation e)),
    ∑ col : (e : E) → Fin (D.dimension (L.edgeRepresentation e)),
      vertexContraction D t s L row col *
        normalizedEdgeCoefficient D L.edgeRepresentation row col g


/-- The explicitly contracted normalized spin function is invariant under
the finite vertex gauge action. -/
theorem contractedSpinFunction_gaugeInvariant
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (L : Label D t s) (h : V → G) (g : E → G) :
    contractedSpinFunction D t s L (NCG.gaugeAct t s h g) =
      contractedSpinFunction D t s L g := by
  classical
  unfold contractedSpinFunction
  simp_rw [normalizedEdgeCoefficient_gauge_expand, Finset.mul_sum,
    edge_transport_product_factor]
  rw [sum_four_rotate]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  calc
    (∑ row, ∑ col,
      vertexContraction D t s L row col *
        ((∏ v,
          incomingKernel D t L.edgeRepresentation v (h v)
              ((rowVertexEquiv D t L.edgeRepresentation) row v)
              ((rowVertexEquiv D t L.edgeRepresentation) p v) *
            outgoingDualKernel D s L.edgeRepresentation v (h v)
              ((colVertexEquiv D s L.edgeRepresentation) col v)
              ((colVertexEquiv D s L.edgeRepresentation) q v)) *
          normalizedEdgeCoefficient D L.edgeRepresentation p q g)) =
        normalizedEdgeCoefficient D L.edgeRepresentation p q g *
          (∑ row, ∑ col,
            vertexContraction D t s L row col *
              ∏ v,
                incomingKernel D t L.edgeRepresentation v (h v)
                    ((rowVertexEquiv D t L.edgeRepresentation) row v)
                    ((rowVertexEquiv D t L.edgeRepresentation) p v) *
                  outgoingDualKernel D s L.edgeRepresentation v (h v)
                    ((colVertexEquiv D s L.edgeRepresentation) col v)
                    ((colVertexEquiv D s L.edgeRepresentation) q v)) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro row _
          apply Finset.sum_congr rfl
          intro col _
          ring
    _ = normalizedEdgeCoefficient D L.edgeRepresentation p q g *
        vertexContraction D t s L p q := by
          rw [vertexContraction_transport_sum]
    _ = vertexContraction D t s L p q *
        normalizedEdgeCoefficient D L.edgeRepresentation p q g := by
          ring


/-- The contracted function bundled as an element of the gauge-invariant
Hilbert subspace. -/
noncomputable def contractedSpinVector
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (L : Label D t s) : GaugeInvariantSubspace (G := G) t s :=
  ⟨WithLp.toLp 2 (contractedSpinFunction D t s L),
    contractedSpinFunction_gaugeInvariant D t s L⟩

@[simp] theorem contractedSpinVector_apply
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (L : Label D t s) (g : E → G) :
    (contractedSpinVector D t s L).1.ofLp g =
      contractedSpinFunction D t s L g := rfl

/-- Every local tensor used by the contraction is invariant. -/
theorem contractedSpinFunction_uses_invariant_intertwiners
    (D : MatrixBlockDecomposition G) (t s : E → V) (L : Label D t s) :
    ∀ v : V, ∀ h : G, ∀ x : VertexTensorIndex D t s L.edgeRepresentation v,
      vertexActionValue D t s L.edgeRepresentation v h
          (vertexIntertwinerBasis D t s L.edgeRepresentation v
            (L.vertexIntertwiner v)).1 x =
        (vertexIntertwinerBasis D t s L.edgeRepresentation v
          (L.vertexIntertwiner v)).1.ofLp x := by
  intro v h x
  exact vertexIntertwiner_invariant D t s L.edgeRepresentation v
    (L.vertexIntertwiner v) h x

end NCG.FiniteSpinNetwork
