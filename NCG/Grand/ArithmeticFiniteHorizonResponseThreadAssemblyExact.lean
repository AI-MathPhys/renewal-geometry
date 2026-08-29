/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResponseThreadCompletionExact
import NCG.Grand.ThreadCutoffCompactnessExact
import NCG.Grand.RelationValuedLimitExact
import NCG.Grand.ArithmeticResponseThreadExact

/-!
# Arithmetic finite-horizon response-thread assembly

This file closes `thm:arithmetic-response-thread` by assembling the already proved
finite-query completion, scalar master-defect, cutoff compactness, relation-valued limit,
and writer-identifiability results.  It also supplies the previously missing R4 passage:
convergence of all bounded writer truncations plus a uniform tail certificate implies
convergence of the original (possibly unbounded) writer.

The relation-valued conclusion is deliberately kept distinct from a probability or path-law
conclusion: compact compatible cylinders produce a compact relation.  The existing theorem
turns that relation into a continuous graph only under equicontinuity of its fibres.
-/

open Filter Topology Set
open scoped BoundedContinuousFunction

namespace NCG
namespace ArithmeticFiniteHorizonResponseThread

/-! ## R4: passage from bounded truncations to an unbounded writer -/

variable {A E : Type*} [MetricSpace E]

/-- A usable uniform-integrability/tail certificate for a writer along a response thread.
Every bounded truncation converges, while the original writer and the truncation are uniformly
close along the whole thread and at its proposed limit. -/
structure UniformTailCertificate (g : A → E) (truncate : ℕ → A → E)
    (x : ℕ → A) (xlim : A) : Prop where
  truncation_tendsto : ∀ M, Tendsto (fun n => truncate M (x n)) atTop (𝓝 (truncate M xlim))
  uniform_tail : ∀ ε : ℝ, 0 < ε → ∃ M,
    (∀ n, dist (g (x n)) (truncate M (x n)) < ε) ∧
      dist (g xlim) (truncate M xlim) < ε

/-- **R4 passage.** A uniform tail certificate promotes convergence of every bounded
truncation to convergence of the original writer. -/
theorem writer_tendsto_of_uniform_tail_certificate
    {g : A → E} {truncate : ℕ → A → E} {x : ℕ → A} {xlim : A}
    (h : UniformTailCertificate g truncate x xlim) :
    Tendsto (fun n => g (x n)) atTop (𝓝 (g xlim)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hthread, hlimit⟩ := h.uniform_tail (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp (h.truncation_tendsto M)) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hthread' := hthread n
  have htruncation := hN n hn
  have hlimit' : dist (truncate M xlim) (g xlim) < ε / 3 := by
    simpa [dist_comm] using hlimit
  calc
    dist (g (x n)) (g xlim)
        ≤ dist (g (x n)) (truncate M (x n)) +
            dist (truncate M (x n)) (truncate M xlim) +
            dist (truncate M xlim) (g xlim) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-! ## R1--R3: one completed response and the countable core -/

variable {K : Type*} [MetricSpace K] [CompleteSpace K]

/-- The R1--R3 response packet: the completed trace is continuous, retains the common
modulus, stays within the projective defect at every finite query, and satisfies every
member of the countable defect core certified by the scalar master defect. -/
theorem completed_response_and_master_core
    (Y : ResponseThreadCompletion.Thread K)
    {k : ℕ → ℕ} (d : ∀ j, (Fin (k j) → K) → ℝ)
    (hd : ∀ j, Continuous (d j)) (hd0 : ∀ j v, 0 ≤ d j v)
    (q : ∀ j, Fin (k j) → ℝ) (depth : ℕ → ℕ)
    (hq : ∀ j i, q j i ∈ Y.D (depth j))
    (hmaster : Tendsto (ResponseThreadCompletion.masterDefect Y d q) atTop (𝓝 0)) :
    ContinuousOn (ResponseThreadCompletion.limitTrace Y) (Icc 0 Y.T) ∧
      (∀ t s, t ∈ Icc 0 Y.T → s ∈ Icc 0 Y.T →
        dist (ResponseThreadCompletion.limitTrace Y t)
          (ResponseThreadCompletion.limitTrace Y s) ≤ Y.ω (|t - s|)) ∧
      (∀ m t, t ∈ Y.D m →
        dist (ResponseThreadCompletion.limitTrace Y t) (Y.y m t) ≤ Y.η m) ∧
      (∀ j, d j (fun i => ResponseThreadCompletion.limitTrace Y (q j i)) = 0) := by
  refine ⟨ResponseThreadCompletion.limitTrace_continuousOn Y, ?_, ?_, ?_⟩
  · exact fun _t _s ht hs => ResponseThreadCompletion.limitTrace_modulus Y ht hs
  · exact fun _m _t ht => ResponseThreadCompletion.limitTrace_defect Y ht
  · exact fun j =>
      ResponseThreadCompletion.master_defect_closure Y d hd hd0 q depth hq hmaster j

/-! ## Compactness across regulators -/

variable {C : Type*} [MetricSpace C] [CompactSpace C] {T : ℝ}

/-- Across regulators, a common continuation modulus gives relative compactness and a
convergent subsequence; continuous defects close on every subsequential limit.  The same
packet proves full convergence under uniqueness or a summable Cauchy estimate. -/
theorem regulator_compactness_and_full_convergence_alternatives
    {ω : ℝ → ℝ} {y : ℕ → C(Icc (0 : ℝ) T, C)}
    (hω : ThreadCutoff.IsCommonModulus ω y) {ι : Type*}
    (d : ι → C(Icc (0 : ℝ) T, C) → ℝ)
    (hcont : ∀ j, Continuous (d j))
    (hvan : ∀ j, Tendsto (fun N => d j (y N)) atTop (𝓝 0)) :
    IsCompact (closure (Set.range y)) ∧
      (∃ z : C(Icc (0 : ℝ) T, C), ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 z)) ∧
      (∀ (z : C(Icc (0 : ℝ) T, C)) (φ : ℕ → ℕ),
        StrictMono φ → Tendsto (y ∘ φ) atTop (𝓝 z) → ∀ j, d j z = 0) ∧
      (∀ z : C(Icc (0 : ℝ) T, C),
        (∀ z', MapClusterPt z' atTop y → z' = z) → Tendsto y atTop (𝓝 z)) ∧
      ((Summable fun N => dist (y N) (y (N + 1))) →
        ∃ z : C(Icc (0 : ℝ) T, C), Tendsto y atTop (𝓝 z)) :=
  ThreadCutoff.thread_cutoff_compactness hω d hcont hvan

/-! ## Compact compatible cylinders and the graph threshold -/

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Compact compatible response cylinders close to a compact relation.  All continuous
defects vanish on that relation; equicontinuous fibres are precisely the extra packet used
here to obtain a single continuous response graph. -/
theorem compact_cylinders_give_relation_and_graph_under_equicontinuity
    {Γ : ℕ → Set (X × Y)} {Γlim : Set (X × Y)}
    (hΓ : RelationValued.HausdorffLimit Γ Γlim)
    {ι : Type*} {d : ι → ℕ → X × Y → ℝ} {dlim : ι → X × Y → ℝ}
    (hcont : ∀ j n, Continuous (d j n)) (hnonneg : ∀ j n p, 0 ≤ d j n p)
    (hunif : ∀ j, TendstoUniformly (d j) (dlim j) atTop)
    (hvan : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ p ∈ Γ n, d j n p < ε) :
    (∀ p ∈ Γlim, ∀ j, dlim j p = 0) ∧
      (RelationValued.EquicontinuousFibres Γ →
        ∃ f : X → Y, ContinuousOn f (Prod.fst '' Γlim) ∧
          Γlim = {p : X × Y | p.1 ∈ Prod.fst '' Γlim ∧ p.2 = f p.1}) :=
  RelationValued.relation_valued_limit hΓ hcont hnonneg hunif hvan

/-! ## Writer identifiability on the completed response quotient -/

variable {History Response Writer : Type*} [EMetricSpace Writer]

/-- The writer is reconstructible from the completed response exactly when its oscillation
on every response fibre is zero. -/
theorem writer_reconstructs_iff_zero_fibre_oscillation
    (g : History → Writer) (r : History → Response) [Nonempty Writer] :
    (∃ decode : Response → Writer, ∀ a, g a = decode (r a)) ↔
      ∀ b, ArithmeticThread.fibreOscillation g r b = 0 :=
  ArithmeticThread.writer_reconstruction_iff g r

end ArithmeticFiniteHorizonResponseThread
end NCG
