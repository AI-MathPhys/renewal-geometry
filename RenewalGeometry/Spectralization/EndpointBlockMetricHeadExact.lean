/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact finite metric head: endpoint blocks and the graph shortest-path metric

Paper `predictive_spectral_geometry`, label `thm:supp-global-metric`, finite
clauses.  A finite edge-weighted graph (`EdgeGraph`: source, terminal and edge
length) carries the direct sum of endpoint blocks
`D_h^met = ⊕_e [[0, 1/ℓ_e], [1/ℓ_e, 0]]` (`metricDirac`) on which a vertex
function acts by its two endpoint values (`endpointRepresentation`).

* `eq:supp-edge-lip` (`norm_commutator_eq_edgeLipschitz`,
  `edgeLipschitz_eq_sup'`): the commutator operator norm is the maximal edge
  Lipschitz quotient `max_e |f(x_e) - f(y_e)| / ℓ_e`.
* Second clause (`edgeConnesDistance_eq_graphDistance`): the pure-state Connes
  distance of this finite triple, the supremum of `|f x - f y|` over the
  commutator unit ball, is exactly the weighted shortest-path metric
  `graphDistance` (an infimum over walks).  Connectedness of the graph and
  strict positivity of the edge lengths are assumed, as in the paper.

The continuum clauses (uniform convergence to the Riemannian distance along
mesoscopic meshes and the smooth seminorm limit) are not treated here.
-/

open Matrix Set
open scoped Matrix.Norms.L2Operator

namespace RenewalGeometry.EndpointBlockMetricHead

/-- A finite edge-weighted graph: every edge `e` has a source `src e`, a
terminal `tgt e` and a length `len e` (`ℓ_h(x,y)` in the paper). -/
structure EdgeGraph (V E : Type*) where
  /-- source vertex of an edge -/
  src : E → V
  /-- terminal vertex of an edge -/
  tgt : E → V
  /-- length of an edge -/
  len : E → ℝ

variable {V E : Type*}

/-! ### Walks and the weighted shortest-path metric -/

/-- `IsWalk Γ x w y`: the edge list `w` is a walk from `x` to `y`, each edge
traversed in either orientation. -/
inductive IsWalk (Γ : EdgeGraph V E) : V → List E → V → Prop
  | nil (x : V) : IsWalk Γ x [] x
  | forward {x y : V} {e : E} {w : List E} (h : Γ.src e = x)
      (hw : IsWalk Γ (Γ.tgt e) w y) : IsWalk Γ x (e :: w) y
  | backward {x y : V} {e : E} {w : List E} (h : Γ.tgt e = x)
      (hw : IsWalk Γ (Γ.src e) w y) : IsWalk Γ x (e :: w) y

/-- Total length of an edge list. -/
def walkLength (Γ : EdgeGraph V E) (w : List E) : ℝ := (w.map Γ.len).sum

/-- The set of lengths of walks from `x` to `y`. -/
def walkLengths (Γ : EdgeGraph V E) (x y : V) : Set ℝ :=
  {r | ∃ w, IsWalk Γ x w y ∧ r = walkLength Γ w}

/-- The weighted graph shortest-path distance: the infimum of walk lengths. -/
noncomputable def graphDistance (Γ : EdgeGraph V E) (x y : V) : ℝ :=
  sInf (walkLengths Γ x y)

/-- Connectedness: every pair of vertices is joined by a walk. -/
def Connected (Γ : EdgeGraph V E) : Prop := ∀ x y, ∃ w, IsWalk Γ x w y

theorem walkLength_nil (Γ : EdgeGraph V E) : walkLength Γ [] = 0 := by
  simp [walkLength]

theorem walkLength_cons (Γ : EdgeGraph V E) (e : E) (w : List E) :
    walkLength Γ (e :: w) = Γ.len e + walkLength Γ w := by
  simp [walkLength]

theorem walkLength_append (Γ : EdgeGraph V E) (w w' : List E) :
    walkLength Γ (w ++ w') = walkLength Γ w + walkLength Γ w' := by
  simp [walkLength]

theorem walkLength_nonneg (Γ : EdgeGraph V E) (hlen : ∀ e, 0 ≤ Γ.len e) (w : List E) :
    0 ≤ walkLength Γ w := by
  induction w with
  | nil => simp [walkLength_nil]
  | cons e w ih => rw [walkLength_cons]; exact add_nonneg (hlen e) ih

theorem IsWalk.append {Γ : EdgeGraph V E} {x y z : V} {w w' : List E}
    (h : IsWalk Γ x w y) (h' : IsWalk Γ y w' z) : IsWalk Γ x (w ++ w') z := by
  induction h with
  | nil x => simpa using h'
  | forward he _ ih => exact IsWalk.forward he (ih h')
  | backward he _ ih => exact IsWalk.backward he (ih h')

/-- The one-edge walk along `e` in the forward orientation. -/
theorem IsWalk.single_forward (Γ : EdgeGraph V E) (e : E) :
    IsWalk Γ (Γ.src e) [e] (Γ.tgt e) :=
  IsWalk.forward rfl (IsWalk.nil _)

/-- The one-edge walk along `e` in the backward orientation. -/
theorem IsWalk.single_backward (Γ : EdgeGraph V E) (e : E) :
    IsWalk Γ (Γ.tgt e) [e] (Γ.src e) :=
  IsWalk.backward rfl (IsWalk.nil _)

/-- Telescoping along a walk: an edgewise Lipschitz function changes by at
most the walk length. -/
theorem abs_sub_le_walkLength {Γ : EdgeGraph V E} (f : V → ℝ)
    (hf : ∀ e, |f (Γ.tgt e) - f (Γ.src e)| ≤ Γ.len e)
    {x y : V} {w : List E} (hw : IsWalk Γ x w y) :
    |f x - f y| ≤ walkLength Γ w := by
  induction hw with
  | nil x => simp [walkLength_nil]
  | @forward x y e w he _ ih =>
    rw [walkLength_cons]
    calc |f x - f y| ≤ |f x - f (Γ.tgt e)| + |f (Γ.tgt e) - f y| := abs_sub_le _ _ _
      _ ≤ Γ.len e + walkLength Γ w := by
        refine add_le_add ?_ ih
        rw [← he, abs_sub_comm]
        exact hf e
  | @backward x y e w he _ ih =>
    rw [walkLength_cons]
    calc |f x - f y| ≤ |f x - f (Γ.src e)| + |f (Γ.src e) - f y| := abs_sub_le _ _ _
      _ ≤ Γ.len e + walkLength Γ w := by
        refine add_le_add ?_ ih
        rw [← he]
        exact hf e

theorem walkLengths_nonempty {Γ : EdgeGraph V E} (hconn : Connected Γ) (x y : V) :
    (walkLengths Γ x y).Nonempty := by
  obtain ⟨w, hw⟩ := hconn x y
  exact ⟨walkLength Γ w, w, hw, rfl⟩

theorem walkLengths_bddBelow {Γ : EdgeGraph V E} (hlen : ∀ e, 0 ≤ Γ.len e) (x y : V) :
    BddBelow (walkLengths Γ x y) := by
  refine ⟨0, ?_⟩
  rintro r ⟨w, _, rfl⟩
  exact walkLength_nonneg Γ hlen w

theorem graphDistance_le_walkLength {Γ : EdgeGraph V E} (hlen : ∀ e, 0 ≤ Γ.len e)
    {x y : V} {w : List E} (hw : IsWalk Γ x w y) :
    graphDistance Γ x y ≤ walkLength Γ w :=
  csInf_le (walkLengths_bddBelow hlen x y) ⟨w, hw, rfl⟩

theorem graphDistance_nonneg {Γ : EdgeGraph V E} (hlen : ∀ e, 0 ≤ Γ.len e)
    (hconn : Connected Γ) (x y : V) : 0 ≤ graphDistance Γ x y := by
  refine le_csInf (walkLengths_nonempty hconn x y) ?_
  rintro r ⟨w, _, rfl⟩
  exact walkLength_nonneg Γ hlen w

theorem graphDistance_self {Γ : EdgeGraph V E} (hlen : ∀ e, 0 ≤ Γ.len e)
    (hconn : Connected Γ) (x : V) : graphDistance Γ x x = 0 := by
  refine le_antisymm ?_ (graphDistance_nonneg hlen hconn x x)
  simpa [walkLength_nil] using graphDistance_le_walkLength hlen (IsWalk.nil (Γ := Γ) x)

/-- Extending a walk by one edge: the distance to the terminal is at most the
distance to the source plus the edge length. -/
theorem graphDistance_tgt_le {Γ : EdgeGraph V E} (hlen : ∀ e, 0 ≤ Γ.len e)
    (hconn : Connected Γ) (x : V) (e : E) :
    graphDistance Γ x (Γ.tgt e) ≤ graphDistance Γ x (Γ.src e) + Γ.len e := by
  have h : graphDistance Γ x (Γ.tgt e) - Γ.len e ≤ graphDistance Γ x (Γ.src e) := by
    refine le_csInf (walkLengths_nonempty hconn x _) ?_
    rintro r ⟨w, hw, rfl⟩
    have := graphDistance_le_walkLength hlen (hw.append (IsWalk.single_forward Γ e))
    rw [walkLength_append, walkLength_cons, walkLength_nil] at this
    linarith
  linarith

theorem graphDistance_src_le {Γ : EdgeGraph V E} (hlen : ∀ e, 0 ≤ Γ.len e)
    (hconn : Connected Γ) (x : V) (e : E) :
    graphDistance Γ x (Γ.src e) ≤ graphDistance Γ x (Γ.tgt e) + Γ.len e := by
  have h : graphDistance Γ x (Γ.src e) - Γ.len e ≤ graphDistance Γ x (Γ.tgt e) := by
    refine le_csInf (walkLengths_nonempty hconn x _) ?_
    rintro r ⟨w, hw, rfl⟩
    have := graphDistance_le_walkLength hlen (hw.append (IsWalk.single_backward Γ e))
    rw [walkLength_append, walkLength_cons, walkLength_nil] at this
    linarith
  linarith

/-- The distance to a fixed vertex is edgewise Lipschitz with constant one. -/
theorem abs_graphDistance_sub_le_len {Γ : EdgeGraph V E} (hlen : ∀ e, 0 ≤ Γ.len e)
    (hconn : Connected Γ) (x : V) (e : E) :
    |graphDistance Γ x (Γ.tgt e) - graphDistance Γ x (Γ.src e)| ≤ Γ.len e := by
  rw [abs_le]
  constructor
  · linarith [graphDistance_src_le hlen hconn x e]
  · linarith [graphDistance_tgt_le hlen hconn x e]

/-- Any edgewise `1`-Lipschitz function is dominated by the graph distance. -/
theorem abs_sub_le_graphDistance {Γ : EdgeGraph V E} (hconn : Connected Γ) (f : V → ℝ)
    (hf : ∀ e, |f (Γ.tgt e) - f (Γ.src e)| ≤ Γ.len e) (x y : V) :
    |f x - f y| ≤ graphDistance Γ x y := by
  refine le_csInf (walkLengths_nonempty hconn x y) ?_
  rintro r ⟨w, hw, rfl⟩
  exact abs_sub_le_walkLength f hf hw

/-! ### The endpoint-block Dirac operator and its commutator norm -/

variable [Fintype E]

/-- The direct sum of endpoint blocks `[[0, 1/ℓ_e], [1/ℓ_e, 0]]`, acting on
`ℝ^{E ⊕ E}` (source copy `inl`, terminal copy `inr`). -/
noncomputable def metricDirac [DecidableEq E] (Γ : EdgeGraph V E) : Matrix (E ⊕ E) (E ⊕ E) ℝ :=
  Matrix.fromBlocks 0 (Matrix.diagonal fun e => (Γ.len e)⁻¹)
    (Matrix.diagonal fun e => (Γ.len e)⁻¹) 0

/-- A vertex function acts on each endpoint block by its two endpoint values. -/
def endpointRepresentation [DecidableEq E] (Γ : EdgeGraph V E) (f : V → ℝ) : Matrix (E ⊕ E) (E ⊕ E) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal fun e => f (Γ.src e)) 0 0
    (Matrix.diagonal fun e => f (Γ.tgt e))

/-- The edge Lipschitz quotient `(f(y_e) - f(x_e)) / ℓ_e`. -/
noncomputable def edgeQuotient (Γ : EdgeGraph V E) (f : V → ℝ) (e : E) : ℝ :=
  (f (Γ.tgt e) - f (Γ.src e)) / Γ.len e

/-- The edge Lipschitz seminorm `L_h^met(f)`: the sup norm of the edge quotients. -/
noncomputable def edgeLipschitz (Γ : EdgeGraph V E) (f : V → ℝ) : ℝ :=
  ‖fun e => edgeQuotient Γ f e‖

/-- The commutator `[D_h^met, π_h(f)]` is the direct sum of the blocks
`[[0, q_e], [-q_e, 0]]` with `q_e = (f(y_e) - f(x_e)) / ℓ_e`. -/
theorem metricDirac_commutator [DecidableEq E] (Γ : EdgeGraph V E) (f : V → ℝ) :
    metricDirac Γ * endpointRepresentation Γ f - endpointRepresentation Γ f * metricDirac Γ =
      Matrix.fromBlocks 0 (Matrix.diagonal (edgeQuotient Γ f))
        (Matrix.diagonal fun e => -edgeQuotient Γ f e) 0 := by
  rw [sub_eq_add_neg]
  simp only [metricDirac, endpointRepresentation, Matrix.fromBlocks_multiply,
    Matrix.diagonal_mul_diagonal, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.fromBlocks_neg, Matrix.fromBlocks_add, neg_zero, ← Matrix.diagonal_neg]
  congr 2
  all_goals
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [edgeQuotient]
      ring
    · simp [hij]

theorem edgeLipschitz_nonneg (Γ : EdgeGraph V E) (f : V → ℝ) : 0 ≤ edgeLipschitz Γ f :=
  norm_nonneg _

theorem abs_edgeQuotient_le_edgeLipschitz (Γ : EdgeGraph V E) (f : V → ℝ) (e : E) :
    |edgeQuotient Γ f e| ≤ edgeLipschitz Γ f := by
  unfold edgeLipschitz
  have := norm_le_pi_norm (fun e => edgeQuotient Γ f e) e
  simpa [Real.norm_eq_abs] using this

theorem edgeLipschitz_le_iff (Γ : EdgeGraph V E) (f : V → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    edgeLipschitz Γ f ≤ c ↔ ∀ e, |edgeQuotient Γ f e| ≤ c := by
  unfold edgeLipschitz
  rw [pi_norm_le_iff_of_nonneg hc]
  simp [Real.norm_eq_abs]

/-- `eq:supp-edge-lip`, maximum form: on a nonempty edge set the seminorm is
the maximum of the edge quotients `|f(x) - f(y)| / ℓ_h(x,y)`. -/
theorem edgeLipschitz_eq_sup' (Γ : EdgeGraph V E) [Nonempty E] (f : V → ℝ) :
    edgeLipschitz Γ f =
      Finset.univ.sup' Finset.univ_nonempty (fun e => |edgeQuotient Γ f e|) := by
  apply le_antisymm
  · have h0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun e => |edgeQuotient Γ f e|) :=
      (abs_nonneg _).trans (Finset.le_sup' (fun e => |edgeQuotient Γ f e|)
        (Finset.mem_univ (Classical.arbitrary E)))
    rw [edgeLipschitz_le_iff Γ f h0]
    intro e
    exact Finset.le_sup' (fun e => |edgeQuotient Γ f e|) (Finset.mem_univ e)
  · exact Finset.sup'_le _ _ fun e _ => abs_edgeQuotient_le_edgeLipschitz Γ f e

theorem norm_sum_elim_self (v : E → ℝ) : ‖(Sum.elim v v : E ⊕ E → ℝ)‖ = ‖v‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    rintro (e | e) <;> exact norm_le_pi_norm v e
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro e
    exact norm_le_pi_norm (Sum.elim v v : E ⊕ E → ℝ) (Sum.inl e)

theorem norm_sq_fun_eq (v : E → ℝ) : ‖fun e => v e ^ 2‖ = ‖v‖ ^ 2 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (sq_nonneg _)]
    intro e
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v e) 2
  · have h : ‖v‖ ≤ Real.sqrt ‖fun e => v e ^ 2‖ := by
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro e
      rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      have := norm_le_pi_norm (fun e => v e ^ 2) e
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (v e))] using this
    calc ‖v‖ ^ 2 ≤ Real.sqrt ‖fun e => v e ^ 2‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = ‖fun e => v e ^ 2‖ := Real.sq_sqrt (norm_nonneg _)

/-- **`eq:supp-edge-lip`.** The commutator operator norm of the endpoint-block
Dirac operator is exactly the edge Lipschitz seminorm. -/
theorem norm_commutator_eq_edgeLipschitz [DecidableEq E] (Γ : EdgeGraph V E) (f : V → ℝ) :
    ‖metricDirac Γ * endpointRepresentation Γ f - endpointRepresentation Γ f * metricDirac Γ‖ =
      edgeLipschitz Γ f := by
  rw [metricDirac_commutator]
  set C := Matrix.fromBlocks (0 : Matrix E E ℝ) (Matrix.diagonal (edgeQuotient Γ f))
    (Matrix.diagonal fun e => -edgeQuotient Γ f e) 0 with hC
  have hgram : Cᴴ * C = Matrix.diagonal (Sum.elim (fun e => edgeQuotient Γ f e ^ 2)
      (fun e => edgeQuotient Γ f e ^ 2)) := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hC, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_diagonal]
    simp only [Matrix.transpose_zero, Matrix.diagonal_transpose, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.diagonal_mul_diagonal, add_zero, zero_add]
    congr 2 <;> ext e <;> ring
  have hsq : ‖C‖ ^ 2 = edgeLipschitz Γ f ^ 2 := by
    calc ‖C‖ ^ 2 = ‖C‖ * ‖C‖ := by ring
      _ = ‖Cᴴ * C‖ := (Matrix.l2_opNorm_conjTranspose_mul_self C).symm
      _ = ‖fun e => edgeQuotient Γ f e ^ 2‖ := by
        rw [hgram, Matrix.l2_opNorm_diagonal, norm_sum_elim_self]
      _ = edgeLipschitz Γ f ^ 2 := norm_sq_fun_eq _
  exact (pow_left_inj₀ (norm_nonneg _) (edgeLipschitz_nonneg Γ f) two_ne_zero).mp hsq

/-! ### The pure-state Connes distance is the shortest-path metric -/

/-- Values `|f x - f y|` over the commutator unit ball of the metric head. -/
def edgeDistanceValues (Γ : EdgeGraph V E) (x y : V) : Set ℝ :=
  {r | ∃ f : V → ℝ, edgeLipschitz Γ f ≤ 1 ∧ r = |f x - f y|}

/-- The pure-state Connes distance of the finite endpoint-block triple. -/
noncomputable def edgeConnesDistance (Γ : EdgeGraph V E) (x y : V) : ℝ :=
  sSup (edgeDistanceValues Γ x y)

theorem edgeLipschitz_le_one_iff (Γ : EdgeGraph V E) (hlen : ∀ e, 0 < Γ.len e) (f : V → ℝ) :
    edgeLipschitz Γ f ≤ 1 ↔ ∀ e, |f (Γ.tgt e) - f (Γ.src e)| ≤ Γ.len e := by
  rw [edgeLipschitz_le_iff Γ f zero_le_one]
  apply forall_congr'
  intro e
  rw [edgeQuotient, abs_div, abs_of_pos (hlen e), div_le_one (hlen e)]

/-- The distance to a fixed vertex lies in the commutator unit ball. -/
theorem edgeLipschitz_graphDistance_le_one (Γ : EdgeGraph V E) (hlen : ∀ e, 0 < Γ.len e)
    (hconn : Connected Γ) (x : V) :
    edgeLipschitz Γ (graphDistance Γ x) ≤ 1 := by
  rw [edgeLipschitz_le_one_iff Γ hlen]
  exact fun e => abs_graphDistance_sub_le_len (fun e => (hlen e).le) hconn x e

theorem graphDistance_isGreatest (Γ : EdgeGraph V E) (hlen : ∀ e, 0 < Γ.len e)
    (hconn : Connected Γ) (x y : V) :
    IsGreatest (edgeDistanceValues Γ x y) (graphDistance Γ x y) := by
  have hlen' : ∀ e, 0 ≤ Γ.len e := fun e => (hlen e).le
  constructor
  · refine ⟨graphDistance Γ x, edgeLipschitz_graphDistance_le_one Γ hlen hconn x, ?_⟩
    rw [graphDistance_self hlen' hconn x, zero_sub, abs_neg,
      abs_of_nonneg (graphDistance_nonneg hlen' hconn x y)]
  · rintro r ⟨f, hf, rfl⟩
    exact abs_sub_le_graphDistance hconn f ((edgeLipschitz_le_one_iff Γ hlen f).mp hf) x y

/-- **`thm:supp-global-metric`, second clause.** The pure-state Connes distance
of the endpoint-block metric head is exactly the weighted graph shortest-path
metric (connected graph, positive edge lengths). -/
theorem edgeConnesDistance_eq_graphDistance (Γ : EdgeGraph V E) (hlen : ∀ e, 0 < Γ.len e)
    (hconn : Connected Γ) (x y : V) :
    edgeConnesDistance Γ x y = graphDistance Γ x y :=
  (graphDistance_isGreatest Γ hlen hconn x y).csSup_eq

/-- The same identity phrased with the actual commutator norm as the constraint. -/
theorem sSup_commutator_unit_ball_eq_graphDistance [DecidableEq E] (Γ : EdgeGraph V E)
    (hlen : ∀ e, 0 < Γ.len e) (hconn : Connected Γ) (x y : V) :
    sSup {r | ∃ f : V → ℝ,
        ‖metricDirac Γ * endpointRepresentation Γ f -
          endpointRepresentation Γ f * metricDirac Γ‖ ≤ 1 ∧ r = |f x - f y|} =
      graphDistance Γ x y := by
  have : {r | ∃ f : V → ℝ,
      ‖metricDirac Γ * endpointRepresentation Γ f -
        endpointRepresentation Γ f * metricDirac Γ‖ ≤ 1 ∧ r = |f x - f y|} =
      edgeDistanceValues Γ x y := by
    ext r
    simp only [edgeDistanceValues, mem_ofPred_eq, norm_commutator_eq_edgeLipschitz]
  rw [this]
  exact edgeConnesDistance_eq_graphDistance Γ hlen hconn x y

end RenewalGeometry.EndpointBlockMetricHead
