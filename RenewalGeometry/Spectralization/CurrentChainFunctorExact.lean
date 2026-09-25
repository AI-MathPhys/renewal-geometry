/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.FiniteGraphSpectralUniversalityFibreExact
import RenewalGeometry.MarkovChains.CoarseAndHiddenEntropyProduction

/-!
# The current-chain functor of a vertex quotient

Paper `predictive_spectral_geometry`, label `thm:supp-current-chain`.

An oriented finite graph is given by `tail head : E → V` with real oriented
incidence `∂_G : ℝ^E → ℝ^V` (`incidence`), cycle space `𝒵(G) = ker ∂_G`
(`cycleSpace`) and current polytope `Curr(G, c)` (`currentPolytope`).  A
vertex quotient `q : V ↠ V̄` together with the induced coarse graph
`(tail', head') : E' → V'` is a `VertexQuotient`: every fine edge is either
sent to a coarse edge with the quotient endpoints, or is *internal* (both
endpoints in one fibre) and dropped.  `Q_V` and `Q_E` sum vertex and edge
coefficients over fibres (`vertexMatrix`, `edgeMatrix`).

* `eq:supp-current-chain` — `incidence_mul_edgeMatrix`:
  `∂_{Ḡ} Q_E = Q_V ∂_G`; hence `Q_E 𝒵(G) ⊆ 𝒵(Ḡ)` (`edgeSum_mem_cycleSpace`).
* the polytope map `Q_E Curr(G,c) ⊆ Curr(Ḡ, c̄)` with `c̄ = Q_E c`
  (`edgeSum_mem_currentPolytope`), for a coarse graph that retains every
  inter-fibre edge class (every coarse edge has a nonempty fibre).
* `eq:supp-cycle-exact` — `edgeSum_cycleSpace_surjective`: with connected
  vertex fibres and every inter-fibre class retained, `Q_E : 𝒵(G) → 𝒵(Ḡ)` is
  onto, so `0 → ker → 𝒵(G) → 𝒵(Ḡ) → 0` is exact.
* `eq:supp-cycle-kernel-dim` — `finrank_ker_cycleMap`:
  `dim ker (Q_E|_{𝒵(G)}) = b₁(G) - b₁(Ḡ)`, with `b₁ = |E| - |V| + 1` for the
  connected graphs (`cycleSpace_finrank_of_connected`).
* `eq:supp-entropy-contraction` — `entropyProduction_edgeSum_le`:
  `σ_{Ḡ}(Q_E j) ≤ σ_G(j)`, by the log-sum inequality for the aggregated
  forward and reverse fluxes on every coarse edge.
-/

open Finset Matrix

namespace RenewalGeometry
namespace CurrentChain

open FiniteGraphSpectralUniversalityFibre CoarseAndHiddenEntropyProduction

variable {V E V' E' : Type*} [Fintype V] [Fintype E] [Fintype V'] [Fintype E']
  [DecidableEq V] [DecidableEq V'] [DecidableEq E] [DecidableEq E']

/-! ### Oriented graphs, incidence, cycle space, current polytope -/

/-- The real oriented incidence matrix `∂_G`, `(∂_G)_{x e} = [tail e = x] - [head e = x]`. -/
def incidence (tail head : E → V) : Matrix V E ℝ :=
  fun x e => (if tail e = x then 1 else 0) - (if head e = x then 1 else 0)

theorem incidence_mulVec_apply (tail head : E → V) (j : E → ℝ) (x : V) :
    (incidence tail head *ᵥ j) x =
      ∑ e, ((if tail e = x then j e else 0) - (if head e = x then j e else 0)) := by
  simp [incidence, Matrix.mulVec, dotProduct, sub_mul, ite_mul]

/-- The cycle space `𝒵(G) = ker ∂_G`. -/
def cycleSpace (tail head : E → V) : Submodule ℝ (E → ℝ) :=
  LinearMap.ker (incidence tail head).mulVecLin

theorem mem_cycleSpace_iff (tail head : E → V) (j : E → ℝ) :
    j ∈ cycleSpace tail head ↔ incidence tail head *ᵥ j = 0 := by
  simp [cycleSpace]

/-- The current polytope `Curr(G, c) = {j ∈ 𝒵(G) : |j_e| < c_e}`. -/
def currentPolytope (tail head : E → V) (c : E → ℝ) : Set (E → ℝ) :=
  {j | incidence tail head *ᵥ j = 0 ∧ ∀ e, |j e| < c e}

/-- Undirected adjacency of the oriented graph. -/
def Adj (tail head : E → V) (x y : V) : Prop :=
  ∃ e, (tail e = x ∧ head e = y) ∨ (tail e = y ∧ head e = x)

/-- Connectedness of the oriented graph. -/
def Connected (tail head : E → V) : Prop :=
  ∀ x y, Relation.ReflTransGen (Adj tail head) x y

/-! ### Vertex quotients -/

/-- **A vertex quotient with its coarse graph.**  `vmap : V ↠ V̄` is the vertex
quotient; a fine edge is either mapped to a coarse edge with the quotient
endpoints (`emap e = some e'`) or is internal to a fibre and dropped
(`emap e = none`). -/
structure VertexQuotient (tail head : E → V) (tail' head' : E' → V') where
  vmap : V → V'
  emap : E → Option E'
  tail_comm : ∀ e e', emap e = some e' → tail' e' = vmap (tail e)
  head_comm : ∀ e e', emap e = some e' → head' e' = vmap (head e)
  internal : ∀ e, emap e = none → vmap (tail e) = vmap (head e)

namespace VertexQuotient

variable {tail head : E → V} {tail' head' : E' → V'}
  (q : VertexQuotient tail head tail' head')

/-- `Q_V`: summation of vertex coefficients over fibres, as a matrix. -/
def vertexMatrix : Matrix V' V ℝ := fun x' x => if q.vmap x = x' then 1 else 0

/-- `Q_E`: summation of oriented edge coefficients over edge fibres, as a matrix. -/
def edgeMatrix : Matrix E' E ℝ := fun e' e => if q.emap e = some e' then 1 else 0

/-- `Q_V f`. -/
def vertexSum (f : V → ℝ) : V' → ℝ := q.vertexMatrix *ᵥ f

/-- `Q_E j`. -/
def edgeSum (j : E → ℝ) : E' → ℝ := q.edgeMatrix *ᵥ j

theorem vertexSum_apply (f : V → ℝ) (x' : V') :
    q.vertexSum f x' = ∑ x, if q.vmap x = x' then f x else 0 := by
  simp [vertexSum, vertexMatrix, Matrix.mulVec, dotProduct, ite_mul]

theorem edgeSum_apply (j : E → ℝ) (e' : E') :
    q.edgeSum j e' = ∑ e, if q.emap e = some e' then j e else 0 := by
  simp [edgeSum, edgeMatrix, Matrix.mulVec, dotProduct, ite_mul]

/-- The coarse conductance `c̄_{ē} = ∑_{e ↦ ē} c_e`. -/
def coarseConductance (c : E → ℝ) : E' → ℝ := q.edgeSum c

/-- **`eq:supp-current-chain`.**  The chain identity `∂_{Ḡ} Q_E = Q_V ∂_G`:
internal fine edges cancel in pairs, inter-fibre edges are counted once. -/
theorem incidence_mul_edgeMatrix :
    incidence tail' head' * q.edgeMatrix = q.vertexMatrix * incidence tail head := by
  ext x' e
  simp only [Matrix.mul_apply, incidence, edgeMatrix, vertexMatrix]
  have hR : (∑ x, (if q.vmap x = x' then (1 : ℝ) else 0) *
      ((if tail e = x then 1 else 0) - (if head e = x then 1 else 0))) =
      (if q.vmap (tail e) = x' then 1 else 0) - (if q.vmap (head e) = x' then 1 else 0) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp
  rw [hR]
  rcases he : q.emap e with _ | e₀
  · simp only [reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero]
    rw [q.internal e he]
    simp
  · simp only [Option.some.injEq, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    rw [q.tail_comm e e₀ he, q.head_comm e e₀ he]

/-- The chain identity applied to a current. -/
theorem incidence_edgeSum (j : E → ℝ) :
    incidence tail' head' *ᵥ q.edgeSum j = q.vertexSum (incidence tail head *ᵥ j) := by
  simp only [edgeSum, vertexSum, Matrix.mulVec_mulVec, incidence_mul_edgeMatrix]

/-- `Q_E 𝒵(G) ⊆ 𝒵(Ḡ)`. -/
theorem edgeSum_mem_cycleSpace {j : E → ℝ} (hj : j ∈ cycleSpace tail head) :
    q.edgeSum j ∈ cycleSpace tail' head' := by
  rw [mem_cycleSpace_iff] at hj ⊢
  rw [incidence_edgeSum, hj]
  simp [vertexSum]

/-- The coarse graph retains every inter-fibre edge class: every coarse edge
is the image of a fine edge. -/
def RetainsInterFibreEdges : Prop := ∀ e', ∃ e, q.emap e = some e'

/-- **Polytope map.**  `Q_E Curr(G, c) ⊆ Curr(Ḡ, c̄)` with `c̄ = Q_E c`, by the
triangle inequality `|(Q_E j)_{ē}| ≤ ∑_{e ↦ ē} |j_e| < c̄_{ē}` (strict because
the fibre of `ē` is nonempty). -/
theorem edgeSum_mem_currentPolytope (hret : q.RetainsInterFibreEdges) (c : E → ℝ)
    {j : E → ℝ} (hj : j ∈ currentPolytope tail head c) :
    q.edgeSum j ∈ currentPolytope tail' head' (q.coarseConductance c) := by
  refine ⟨?_, fun e' => ?_⟩
  · rw [incidence_edgeSum, hj.1]
    simp [vertexSum]
  · rw [edgeSum_apply, coarseConductance, edgeSum_apply]
    refine lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) ?_
    obtain ⟨e₀, he₀⟩ := hret e'
    apply Finset.sum_lt_sum
    · intro e _
      split_ifs
      · exact (hj.2 e).le
      · simp
    · refine ⟨e₀, Finset.mem_univ _, ?_⟩
      simp [he₀, hj.2 e₀]

/-! ### Entropy contraction -/

/-- The edge entropy is the symmetrised rate divergence of the forward and
reverse fluxes: `2 j log((c+j)/(c-j)) = Φ(c+j, c-j) + Φ(c-j, c+j)`. -/
theorem entropyEdge_eq_rateDivergence {c j : ℝ} (hpos : 0 < c + j) (hneg : 0 < c - j) :
    entropyEdge c j = rateDivergence (c + j) (c - j) + rateDivergence (c - j) (c + j) := by
  unfold entropyEdge rateDivergence
  have hlog : Real.log ((c - j) / (c + j)) = -Real.log ((c + j) / (c - j)) := by
    rw [← Real.log_inv, inv_div]
  rw [hlog]
  ring

/-- Log-sum inequality on a nonempty finset. -/
theorem rateDivergence_sum_le_sum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ i ∈ s, 0 < b i) :
    rateDivergence (∑ i ∈ s, a i) (∑ i ∈ s, b i) ≤ ∑ i ∈ s, rateDivergence (a i) (b i) := by
  have : Nonempty s := hs.to_subtype
  have h := sum_rateDivergence_ge_total (I := s) (fun i => a i) (fun i => b i)
    (fun i => ha i i.2) (fun i => hb i i.2)
  rw [← Finset.sum_coe_sort s a, ← Finset.sum_coe_sort s b,
    ← Finset.sum_coe_sort s (fun i => rateDivergence (a i) (b i))]
  exact h

/-- Entropy contraction on one coarse edge: the aggregated forward and reverse
fluxes have at most the summed fine edge entropies. -/
theorem entropyEdge_coarse_le (c j : E → ℝ) (hc : ∀ e, 0 < c e) (hj : ∀ e, |j e| < c e)
    (e' : E') :
    entropyEdge (q.coarseConductance c e') (q.edgeSum j e') ≤
      ∑ e, if q.emap e = some e' then entropyEdge (c e) (j e) else 0 := by
  have hfwd : ∀ e, 0 < c e + j e := fun e => by linarith [(abs_lt.mp (hj e)).1]
  have hrev : ∀ e, 0 < c e - j e := fun e => by linarith [(abs_lt.mp (hj e)).2]
  set s : Finset E := Finset.univ.filter fun e => q.emap e = some e' with hs
  have hcs : q.coarseConductance c e' = ∑ e ∈ s, c e := by
    rw [coarseConductance, edgeSum_apply, Finset.sum_filter]
  have hjs : q.edgeSum j e' = ∑ e ∈ s, j e := by
    rw [edgeSum_apply, Finset.sum_filter]
  rw [← Finset.sum_filter, ← hs, hcs, hjs]
  rcases s.eq_empty_or_nonempty with hemp | hne
  · simp [hemp, entropyEdge]
  · have hpos : 0 < ∑ e ∈ s, c e + ∑ e ∈ s, j e := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_pos (fun e _ => hfwd e) hne
    have hneg : 0 < ∑ e ∈ s, c e - ∑ e ∈ s, j e := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_pos (fun e _ => hrev e) hne
    rw [entropyEdge_eq_rateDivergence hpos hneg]
    have h1 := rateDivergence_sum_le_sum s hne (fun e => c e + j e) (fun e => c e - j e)
      (fun e _ => hfwd e) (fun e _ => hrev e)
    have h2 := rateDivergence_sum_le_sum s hne (fun e => c e - j e) (fun e => c e + j e)
      (fun e _ => hrev e) (fun e _ => hfwd e)
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1 h2
    calc rateDivergence (∑ e ∈ s, c e + ∑ e ∈ s, j e) (∑ e ∈ s, c e - ∑ e ∈ s, j e) +
          rateDivergence (∑ e ∈ s, c e - ∑ e ∈ s, j e) (∑ e ∈ s, c e + ∑ e ∈ s, j e)
        ≤ (∑ e ∈ s, rateDivergence (c e + j e) (c e - j e)) +
          ∑ e ∈ s, rateDivergence (c e - j e) (c e + j e) := add_le_add h1 h2
      _ = ∑ e ∈ s, entropyEdge (c e) (j e) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e _
        rw [entropyEdge_eq_rateDivergence (hfwd e) (hrev e)]

/-- **`eq:supp-entropy-contraction`.**  The stationary entropy production
contracts under coarse graining: `σ_{Ḡ}(Q_E j) ≤ σ_G(j)`. -/
theorem entropyProduction_edgeSum_le (c j : E → ℝ) (hc : ∀ e, 0 < c e)
    (hj : ∀ e, |j e| < c e) :
    entropyProduction (q.coarseConductance c) (q.edgeSum j) ≤ entropyProduction c j := by
  unfold entropyProduction
  calc (∑ e', entropyEdge (q.coarseConductance c e') (q.edgeSum j e'))
      ≤ ∑ e', ∑ e, if q.emap e = some e' then entropyEdge (c e) (j e) else 0 :=
        Finset.sum_le_sum fun e' _ => q.entropyEdge_coarse_le c j hc hj e'
    _ = ∑ e, ∑ e', if q.emap e = some e' then entropyEdge (c e) (j e) else 0 :=
        Finset.sum_comm
    _ ≤ ∑ e, entropyEdge (c e) (j e) := by
        apply Finset.sum_le_sum
        intro e _
        rcases he : q.emap e with _ | e₀
        · simp only [reduceCtorEq, if_false, Finset.sum_const_zero]
          exact entropyEdge_nonneg (hc e) (hj e)
        · simp only [Option.some.injEq]
          rw [Finset.sum_ite_eq]
          simp

/-! ### Surjectivity on cycle spaces and the kernel dimension -/

/-- Adjacency through internal (dropped, intra-fibre) edges. -/
def InternalAdj (x y : V) : Prop :=
  ∃ e, q.emap e = none ∧ ((tail e = x ∧ head e = y) ∨ (tail e = y ∧ head e = x))

/-- The vertex fibres are connected through internal edges. -/
def FibresConnected : Prop :=
  ∀ x y, q.vmap x = q.vmap y → Relation.ReflTransGen q.InternalAdj x y

/-- A path flow along a chain of internal edges: a current supported on
internal edges with divergence `δ_x - δ_y`. -/
theorem exists_internal_pathFlow {x y : V} (h : Relation.ReflTransGen q.InternalAdj x y) :
    ∃ p : E → ℝ, (∀ e, q.emap e ≠ none → p e = 0) ∧
      incidence tail head *ᵥ p = Pi.single x 1 - Pi.single y 1 := by
  induction h with
  | refl => exact ⟨0, fun _ _ => rfl, by simp⟩
  | tail _ hbc ih =>
      obtain ⟨p, hp, hdiv⟩ := ih
      obtain ⟨e, he, hor⟩ := hbc
      have hsingle : incidence tail head *ᵥ Pi.single e (1 : ℝ) =
          Pi.single (tail e) 1 - Pi.single (head e) 1 := by
        funext z
        rw [incidence_mulVec_apply]
        simp only [Pi.single_apply, Pi.sub_apply]
        rw [Finset.sum_eq_single e]
        · by_cases h1 : tail e = z <;> by_cases h2 : head e = z <;>
            simp [h1, h2, @eq_comm _ z]
        · intro e₁ _ hne
          simp [hne]
        · simp
      rcases hor with ⟨hte, hhe⟩ | ⟨hte, hhe⟩
      · refine ⟨p + Pi.single e 1, ?_, ?_⟩
        · intro e₁ h₁
          have hne : e₁ ≠ e := fun h => h₁ (h ▸ he)
          simp [hp e₁ h₁, hne]
        · rw [Matrix.mulVec_add, hdiv, hsingle, hte, hhe]
          abel
      · refine ⟨p - Pi.single e 1, ?_, ?_⟩
        · intro e₁ h₁
          have hne : e₁ ≠ e := fun h => h₁ (h ▸ he)
          simp [hp e₁ h₁, hne]
        · rw [Matrix.mulVec_sub, hdiv, hsingle, hte, hhe]
          abel

/-- Inside a connected fibre, every zero-sum divergence is realised by an
internal current. -/
theorem exists_internal_fibreFlow (hconn : q.FibresConnected) (g : V → ℝ) (x' : V')
    (hzero : q.vertexSum g x' = 0) :
    ∃ p : E → ℝ, (∀ e, q.emap e ≠ none → p e = 0) ∧
      incidence tail head *ᵥ p = fun x => if q.vmap x = x' then g x else 0 := by
  classical
  by_cases hex : ∃ x₀, q.vmap x₀ = x'
  · obtain ⟨x₀, hx₀⟩ := hex
    choose P hP using fun x (hx : q.vmap x = x') =>
      q.exists_internal_pathFlow (hconn x₀ x (hx₀.trans hx.symm))
    let P' : V → E → ℝ := fun x => if hx : q.vmap x = x' then P x hx else 0
    refine ⟨∑ x, g x • (-P' x), ?_, ?_⟩
    · intro e he
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : q.vmap x = x'
      · simp [P', hx, (hP x hx).1 e he]
      · simp [P', hx]
    · rw [Matrix.mulVec_sum]
      funext z
      simp only [Finset.sum_apply, Matrix.mulVec_smul, Matrix.mulVec_neg, Pi.smul_apply,
        Pi.neg_apply, smul_eq_mul]
      have hterm : ∀ x, g x * -((incidence tail head *ᵥ P' x) z) =
          (if z = x then (if q.vmap x = x' then g x else 0) else 0) -
            (if z = x₀ then 1 else 0) * (if q.vmap x = x' then g x else 0) := by
        intro x
        by_cases hx : q.vmap x = x'
        · simp only [P', hx, dif_pos, if_true]
          rw [(hP x hx).2]
          simp only [Pi.sub_apply, Pi.single_apply]
          split_ifs <;> ring
        · simp [P', hx]
      simp_rw [hterm]
      have hz : q.vertexSum g x' = ∑ x, if q.vmap x = x' then g x else 0 :=
        q.vertexSum_apply g x'
      rw [hz] at hzero
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, ← Finset.mul_sum, hzero, mul_zero,
        sub_zero]
      simp
  · refine ⟨0, fun _ _ => rfl, ?_⟩
    funext x
    have : q.vmap x ≠ x' := fun h => hex ⟨x, h⟩
    simp [this]

/-- The column of `Q_E` at a fine edge lying over `e'` is the coarse unit vector. -/
theorem edgeSum_single_of_emap {e : E} {e' : E'} (he : q.emap e = some e') :
    q.edgeSum (Pi.single e (1 : ℝ)) = Pi.single e' 1 := by
  funext e''
  rw [edgeSum_apply, Finset.sum_eq_single e]
  · simp only [Pi.single_apply, if_true, he, Option.some.injEq]
    by_cases h : e' = e''
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro e₁ _ hne
    simp [hne]
  · simp

/-- **Surjectivity on cycle spaces (`eq:supp-cycle-exact`).**  With connected
fibres and every inter-fibre edge class retained, every coarse cycle lifts to
a fine cycle: choose one representative fine edge per coarse edge, and
complete the resulting divergence inside the connected fibres. -/
theorem edgeSum_cycleSpace_surjective (hconn : q.FibresConnected)
    (hret : q.RetainsInterFibreEdges) {z' : E' → ℝ} (hz' : z' ∈ cycleSpace tail' head') :
    ∃ z ∈ cycleSpace tail head, q.edgeSum z = z' := by
  classical
  choose s hs using hret
  let j₀ : E → ℝ := ∑ e', z' e' • (Pi.single (s e') (1 : ℝ) : E → ℝ)
  have hQj₀ : q.edgeSum j₀ = z' := by
    simp only [j₀, edgeSum, Matrix.mulVec_sum, Matrix.mulVec_smul]
    funext e''
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have : ∀ e', (q.edgeMatrix *ᵥ Pi.single (s e') (1 : ℝ)) = Pi.single e' 1 :=
      fun e' => q.edgeSum_single_of_emap (hs e')
    simp_rw [this]
    simp [Pi.single_apply]
  set g : V → ℝ := -(incidence tail head *ᵥ j₀) with hg
  have hgzero : ∀ x', q.vertexSum g x' = 0 := by
    intro x'
    have h := congrFun (q.incidence_edgeSum j₀) x'
    rw [hQj₀, (mem_cycleSpace_iff _ _ _).mp hz'] at h
    simp only [Pi.zero_apply] at h
    rw [hg, vertexSum, Matrix.mulVec_neg, Pi.neg_apply]
    change -(q.vertexSum (incidence tail head *ᵥ j₀) x') = 0
    rw [← h, neg_zero]
  choose F hF using fun x' => q.exists_internal_fibreFlow hconn g x' (hgzero x')
  let j₁ : E → ℝ := ∑ x', F x'
  have hBj₁ : incidence tail head *ᵥ j₁ = g := by
    simp only [j₁, Matrix.mulVec_sum]
    funext x
    simp only [Finset.sum_apply]
    simp_rw [fun x' => (hF x').2]
    simp
  have hQj₁ : q.edgeSum j₁ = 0 := by
    funext e'
    rw [edgeSum_apply]
    apply Finset.sum_eq_zero
    intro e _
    split_ifs with he
    · simp only [j₁, Finset.sum_apply]
      exact Finset.sum_eq_zero fun x' _ => (hF x').1 e (by simp [he])
    · rfl
  refine ⟨j₀ + j₁, ?_, ?_⟩
  · rw [mem_cycleSpace_iff, Matrix.mulVec_add, hBj₁, hg]
    simp
  · simp only [edgeSum, Matrix.mulVec_add]
    change q.edgeSum j₀ + q.edgeSum j₁ = z'
    rw [hQj₀, hQj₁, add_zero]

/-- `Q_E` restricted to the cycle spaces, `𝒵(G) → 𝒵(Ḡ)`. -/
def cycleMap : cycleSpace tail head →ₗ[ℝ] cycleSpace tail' head' :=
  (q.edgeMatrix.mulVecLin.domRestrict (cycleSpace tail head)).codRestrict
    (cycleSpace tail' head') (fun j => q.edgeSum_mem_cycleSpace j.2)

theorem cycleMap_apply (j : cycleSpace tail head) :
    (q.cycleMap j : E' → ℝ) = q.edgeSum j := rfl

theorem cycleMap_surjective (hconn : q.FibresConnected) (hret : q.RetainsInterFibreEdges) :
    Function.Surjective q.cycleMap := by
  intro z'
  obtain ⟨z, hz, hQ⟩ := q.edgeSum_cycleSpace_surjective hconn hret z'.2
  exact ⟨⟨z, hz⟩, Subtype.ext hQ⟩

/-- **`eq:supp-cycle-exact`.**  The sequence
`0 → ker(Q_E|𝒵(G)) → 𝒵(G) → 𝒵(Ḡ) → 0` is exact: the range of `Q_E|𝒵(G)` is all
of `𝒵(Ḡ)` (the other exactness conditions hold by definition of the kernel and
of the inclusion). -/
theorem range_cycleMap_eq_top (hconn : q.FibresConnected) (hret : q.RetainsInterFibreEdges) :
    LinearMap.range q.cycleMap = ⊤ :=
  LinearMap.range_eq_top.mpr (q.cycleMap_surjective hconn hret)

/-- **`eq:supp-cycle-kernel-dim`** (rank–nullity form):
`dim ker(Q_E|𝒵(G)) = dim 𝒵(G) - dim 𝒵(Ḡ)`. -/
theorem finrank_ker_cycleMap (hconn : q.FibresConnected) (hret : q.RetainsInterFibreEdges) :
    Module.finrank ℝ (LinearMap.ker q.cycleMap) =
      Module.finrank ℝ (cycleSpace tail head) - Module.finrank ℝ (cycleSpace tail' head') := by
  have h := LinearMap.finrank_range_add_finrank_ker q.cycleMap
  rw [q.range_cycleMap_eq_top hconn hret, finrank_top] at h
  omega

end VertexQuotient

/-! ### The Betti number of a connected oriented graph over `ℝ` -/

theorem transpose_incidence_mulVec_apply (tail head : E → V) (f : V → ℝ) (e : E) :
    ((incidence tail head)ᵀ *ᵥ f) e = f (tail e) - f (head e) := by
  simp [incidence, Matrix.mulVec, dotProduct, Matrix.transpose_apply, sub_mul, ite_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq]

/-- On a connected graph the kernel of the transposed incidence is the
constant-potential line. -/
theorem ker_transpose_incidence_eq_span_one (tail head : E → V) (hG : Connected tail head) :
    LinearMap.ker (incidence tail head)ᵀ.mulVecLin = ℝ ∙ (fun _ : V => (1 : ℝ)) := by
  ext f
  constructor
  · intro hf
    have hf' : (incidence tail head)ᵀ *ᵥ f = 0 := LinearMap.mem_ker.mp hf
    have hedge : ∀ e, f (tail e) = f (head e) := by
      intro e
      have h := congrFun hf' e
      rw [transpose_incidence_mulVec_apply] at h
      exact sub_eq_zero.mp h
    have hadj : ∀ a b, Adj tail head a b → f a = f b := by
      rintro a b ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact hedge e
      · exact (hedge e).symm
    have hconst : ∀ a b, Relation.ReflTransGen (Adj tail head) a b → f a = f b := by
      intro a b h
      induction h with
      | refl => rfl
      | tail _ hbc ih => exact ih.trans (hadj _ _ hbc)
    rcases isEmpty_or_nonempty V with hV | hV
    · exact Submodule.mem_span_singleton.mpr ⟨0, funext fun v => (hV.false v).elim⟩
    · obtain ⟨v₀⟩ := hV
      refine Submodule.mem_span_singleton.mpr ⟨f v₀, funext fun v => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      exact hconst v₀ v (hG v₀ v)
  · intro hf
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
    apply LinearMap.mem_ker.mpr
    funext e
    change ((incidence tail head)ᵀ *ᵥ (c • fun _ : V => (1 : ℝ))) e = 0
    rw [transpose_incidence_mulVec_apply]
    simp

/-- A connected oriented graph on a nonempty vertex set has incidence rank `|V| - 1`. -/
theorem incidence_rank_of_connected [Nonempty V] (tail head : E → V)
    (hG : Connected tail head) :
    (incidence tail head).rank = Fintype.card V - 1 := by
  have hone : (fun _ : V => (1 : ℝ)) ≠ 0 := by
    intro h
    obtain ⟨v⟩ := ‹Nonempty V›
    have := congrFun h v
    simp at this
  have hker : Module.finrank ℝ (LinearMap.ker (incidence tail head)ᵀ.mulVecLin) = 1 := by
    rw [ker_transpose_incidence_eq_span_one tail head hG, finrank_span_singleton hone]
  have hrn := LinearMap.finrank_range_add_finrank_ker (incidence tail head)ᵀ.mulVecLin
  rw [hker, Module.finrank_pi] at hrn
  have hT : (incidence tail head)ᵀ.rank =
      Module.finrank ℝ (LinearMap.range (incidence tail head)ᵀ.mulVecLin) := rfl
  rw [← Matrix.rank_transpose, hT]
  omega

/-- **`b₁(G) = |E| - |V| + 1`** over `ℝ` for a connected oriented graph. -/
theorem cycleSpace_finrank_of_connected [Nonempty V] (tail head : E → V)
    (hG : Connected tail head) :
    Module.finrank ℝ (cycleSpace tail head) = Fintype.card E + 1 - Fintype.card V := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (incidence tail head).mulVecLin
  rw [Module.finrank_pi] at hrn
  have hrank := incidence_rank_of_connected tail head hG
  have hrk : (incidence tail head).rank =
      Module.finrank ℝ (LinearMap.range (incidence tail head).mulVecLin) := rfl
  have hle : (incidence tail head).rank ≤ Fintype.card E := Matrix.rank_le_card_width _
  rw [hrk] at hrank hle
  have hV : 1 ≤ Fintype.card V := Fintype.card_pos
  unfold cycleSpace
  omega

namespace VertexQuotient

variable {tail head : E → V} {tail' head' : E' → V'}
  (q : VertexQuotient tail head tail' head')

/-- **`eq:supp-cycle-kernel-dim`.**  For connected `G` and `Ḡ`,
`dim ker(Q_E|𝒵(G)) = b₁(G) - b₁(Ḡ)` with `b₁ = |E| - |V| + 1`. -/
theorem finrank_ker_cycleMap_eq_betti [Nonempty V] [Nonempty V']
    (hconn : q.FibresConnected) (hret : q.RetainsInterFibreEdges)
    (hG : Connected tail head) (hG' : Connected tail' head') :
    Module.finrank ℝ (LinearMap.ker q.cycleMap) =
      (Fintype.card E + 1 - Fintype.card V) - (Fintype.card E' + 1 - Fintype.card V') := by
  rw [q.finrank_ker_cycleMap hconn hret, cycleSpace_finrank_of_connected tail head hG,
    cycleSpace_finrank_of_connected tail' head' hG']

/-- **`thm:supp-current-chain` (assembled).**  The chain identity, the cycle
and polytope maps, surjectivity on cycle spaces with the kernel dimension
`b₁(G) - b₁(Ḡ)`, and entropy contraction. -/
theorem current_chain_functor [Nonempty V] [Nonempty V']
    (hconn : q.FibresConnected) (hret : q.RetainsInterFibreEdges)
    (hG : Connected tail head) (hG' : Connected tail' head') (c : E → ℝ)
    (hc : ∀ e, 0 < c e) :
    incidence tail' head' * q.edgeMatrix = q.vertexMatrix * incidence tail head ∧
      (∀ j ∈ cycleSpace tail head, q.edgeSum j ∈ cycleSpace tail' head') ∧
      (∀ j ∈ currentPolytope tail head c,
        q.edgeSum j ∈ currentPolytope tail' head' (q.coarseConductance c)) ∧
      LinearMap.range q.cycleMap = ⊤ ∧
      Module.finrank ℝ (LinearMap.ker q.cycleMap) =
        (Fintype.card E + 1 - Fintype.card V) - (Fintype.card E' + 1 - Fintype.card V') ∧
      (∀ j ∈ currentPolytope tail head c,
        entropyProduction (q.coarseConductance c) (q.edgeSum j) ≤ entropyProduction c j) :=
  ⟨q.incidence_mul_edgeMatrix, fun _ hj => q.edgeSum_mem_cycleSpace hj,
    fun _ hj => q.edgeSum_mem_currentPolytope hret c hj,
    q.range_cycleMap_eq_top hconn hret,
    q.finrank_ker_cycleMap_eq_betti hconn hret hG hG',
    fun _ hj => q.entropyProduction_edgeSum_le c _ hc hj.2⟩

end VertexQuotient

end CurrentChain
end RenewalGeometry
