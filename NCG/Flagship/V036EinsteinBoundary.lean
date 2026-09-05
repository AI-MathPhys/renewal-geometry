/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Einstein insertion, local weak equations, and the global
  boundary theorem (`thm:master-Einstein-insertion-v036`,
  `thm:master-local-variation-v036`,
  `thm:master-global-boundary-v036`, flagship manuscript)

* `insertion_functional_determined`: faithfulness of the boxed
  insertion limit — the pairing `k ↦ Σ T·k` against all test
  insertions determines the tensor `T` exactly (vanishing on
  all tests forces `T = 0`, so two limits agreeing on all tests
  agree), the sense in which `χ∫√-g(G+Λg)k` carries the full
  Einstein content and no independently discretized Einstein
  tensor is needed;
* `insertion_pairing_linear`: the insertion limit is linear in
  the test — the first-variation structure;
* `local_weak_subsequence`: the subsequence-extraction step of
  the local weak theorem — a norm-bounded sequence of
  functionals on the finite test space has a convergent
  subsequence (finite-dimensional dual ball compactness);
* `boundary_first_variation`: the boxed global decomposition —
  the first variation of
  `S_glob = S_ren + 2χΣ_F a_F + 2χΣ_C b_C` is the sum of the
  bulk variation and the face/joint variations, term by term.

Rendering disclosed: the Fréchet/cut-tomography hypotheses
(E1)–(E5), the renormalization hypotheses (V1)–(V5) and the
diffeomorphism/conservation clauses, and the Stokes/trace
hypotheses (B1)–(B5) with the well-posed Dirichlet problem are
the manuscript's analytic layer; the faithfulness of the
insertion pairing, the subsequence compactness, and the exact
variation bookkeeping are proved here.
-/

open Filter Topology

namespace NCG

variable {ι : Type*} [Fintype ι]

/-- The insertion pairing determines the tensor: vanishing
against every test insertion forces `T = 0`, so the boxed limit
`χ∫√-g(G+Λg)k` carries the full field-equation content. -/
theorem insertion_functional_determined (T : ι → ℝ)
    (h : ∀ k : ι → ℝ, ∑ i, T i * k i = 0) : ∀ i, T i = 0 := by
  classical
  intro i
  have := h (Pi.single i 1)
  simpa [Pi.single_apply, Finset.sum_ite_eq', mul_ite]
    using this

/-- The insertion limit is linear in the test insertion. -/
theorem insertion_pairing_linear (T : ι → ℝ) (k₁ k₂ : ι → ℝ)
    (c : ℝ) :
    ∑ i, T i * (c * k₁ i + k₂ i)
      = c * (∑ i, T i * k₁ i) + ∑ i, T i * k₂ i := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Subsequence extraction for the local weak equations: a
norm-bounded functional sequence on the finite-dimensional test
space has a convergent subsequence. -/
theorem local_weak_subsequence {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (φ : ℕ → (E →L[ℝ] ℝ)) (C : ℝ)
    (hbd : ∀ j, ‖φ j‖ ≤ C) :
    ∃ ψ : E →L[ℝ] ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun j => φ (σ j)) atTop (𝓝 ψ) := by
  have hmem : ∀ j,
      φ j ∈ Metric.closedBall (0 : E →L[ℝ] ℝ) C := by
    intro j
    simpa [Metric.mem_closedBall, dist_zero_right] using hbd j
  have hcomp :
      IsCompact (Metric.closedBall (0 : E →L[ℝ] ℝ) C) :=
    isCompact_closedBall _ _
  obtain ⟨ψ, _, σ, hσ, hconv⟩ := hcomp.tendsto_subseq hmem
  exact ⟨ψ, σ, hσ, hconv⟩

/-- Boxed global decomposition: the first variation of
`S_glob = S_ren + 2χΣ_F a_F + 2χΣ_C b_C` splits into bulk,
face, and joint variations. -/
theorem boundary_first_variation {F C : Type*} [Fintype F]
    [Fintype C] (χ t : ℝ) (s : ℝ → ℝ) (a : F → ℝ → ℝ)
    (b : C → ℝ → ℝ) (ds : ℝ) (da : F → ℝ) (db : C → ℝ)
    (hs : HasDerivAt s ds t)
    (ha : ∀ f, HasDerivAt (a f) (da f) t)
    (hb : ∀ c, HasDerivAt (b c) (db c) t) :
    HasDerivAt
      (fun u => s u + 2 * χ * ∑ f, a f u
        + 2 * χ * ∑ c, b c u)
      (ds + 2 * χ * ∑ f, da f + 2 * χ * ∑ c, db c) t := by
  have hA : HasDerivAt (fun u => ∑ f, a f u) (∑ f, da f) t := by
    have h := HasDerivAt.sum (u := Finset.univ) fun f _ => ha f
    have heq : (∑ f, a f) = fun u => ∑ f, a f u := by
      funext u
      simp [Finset.sum_apply]
    rw [heq] at h
    exact h
  have hB : HasDerivAt (fun u => ∑ c, b c u) (∑ c, db c) t := by
    have h := HasDerivAt.sum (u := Finset.univ) fun c _ => hb c
    have heq : (∑ c, b c) = fun u => ∑ c, b c u := by
      funext u
      simp [Finset.sum_apply]
    rw [heq] at h
    exact h
  exact (hs.add (hA.const_mul (2 * χ))).add
    (hB.const_mul (2 * χ))

end NCG
