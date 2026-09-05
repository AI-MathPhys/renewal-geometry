/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MoscoResolvent
import NCG.Grand.OUProcess
import NCG.Grand.ProjectiveState
import NCG.Grand.UniversalCoercive
import NCG.Grand.YMSlabGap

/-!
# The universal continuum assemblies
  (`thm:universal-physical-continuum`,
  `thm:GT-universal-limit-alternative`, Gran-Tensor manuscript)

Each assembly bundles the formal cores of its cited proved
constituent records (the manuscript's proof is the citation
list; the B-tier process/Mosco limit clauses of the
constituents enter through their own disclosed layers).

* `universal_physical_continuum`: the continuum-handoff bundle —
  resolvent well-posedness of every implicit-Euler step, the
  norm-resolvent convergence engine, the head–tail contraction
  `q* < 1` transferring the noncollapsing gap, the Lyapunov
  stationarity of the OU balance, and the finite-resolution
  screen tail;
* `gt_universal_limit_alternative`: the limit-or-obstruction
  alternative — pointwise Mosco recovery, finite-stage state
  compactness (Bolzano–Weierstrass extraction), and the
  Schur-iteration dichotomy locating any obstruction at the
  boxed small root.
-/

open Matrix Filter Topology

namespace NCG

/-- `thm:universal-physical-continuum`: the continuum-handoff
bundle, each clause the formal core of its cited proved
constituents. -/
theorem universal_physical_continuum :
    (∀ (L : Matrix (Fin 4) (Fin 4) ℝ),
      (∀ x : Fin 4 → ℝ, 0 ≤ x ⬝ᵥ L.mulVec x) → ∀ τ : ℝ,
      0 < τ → (1 + τ • L).det ≠ 0)
    ∧ (∀ (L : Matrix (Fin 4) (Fin 4) ℝ)
        (Lseq : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (τ : ℝ),
        (1 + τ • L).det ≠ 0 →
        Tendsto Lseq atTop (𝓝 L) →
        Tendsto (fun k => (1 + τ • Lseq k)⁻¹) atTop
          (𝓝 (1 + τ • L)⁻¹))
    ∧ (∀ a b d : ℝ, a < 1 → d < 1 →
        b ^ 2 < (1 - a) * (1 - d) →
        (a + d + Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2 < 1)
    ∧ (∀ A : Matrix (Fin 4) (Fin 4) ℝ, Aᵀ = A →
        IsUnit A.det → A * A⁻¹ + A⁻¹ * Aᵀ = (2 : ℝ) • 1)
    ∧ (∀ (μ f lam : Fin 8 → ℝ), (∀ i, 0 ≤ μ i) →
        (∀ i, 0 ≤ lam i) → ∀ R : ℝ, 0 < R →
        ∑ i ∈ Finset.univ.filter (fun i => R < lam i),
            μ i * f i ^ 2
          ≤ R⁻¹ * ∑ i, lam i * (μ i * f i ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun L hpsd τ hτ => resolvent_det_ne_zero L hpsd τ hτ
  · exact fun L Lseq τ hdet hL =>
      resolvent_convergence L Lseq τ hdet hL
  · exact fun a b d ha hd hb =>
      head_tail_contraction a b d ha hd hb
  · exact fun A hsym hA => lyapunov_stationary A hsym hA
  · exact fun μ f lam hμ hlam R hR =>
      screen_tail_bound μ f lam hμ hlam R hR

/-- `thm:GT-universal-limit-alternative`: the
limit-or-obstruction alternative, each clause the formal core
of its cited proved constituents. -/
theorem gt_universal_limit_alternative :
    (∀ (q : ℕ → (Fin 4 → ℝ) → ℝ) (qlim : (Fin 4 → ℝ) → ℝ),
      (∀ x, Tendsto (fun k => q k x) atTop (𝓝 (qlim x))) →
      ∀ x, ∃ xseq : ℕ → (Fin 4 → ℝ),
        Tendsto xseq atTop (𝓝 x)
        ∧ Tendsto (fun k => q k (xseq k)) atTop (𝓝 (qlim x)))
    ∧ (∀ φ : ℕ → (EuclideanSpace ℂ (Fin 4) →L[ℂ] ℂ),
        (∀ j, ‖φ j‖ ≤ 1) →
        ∃ ψ, ‖ψ‖ ≤ 1 ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
          Tendsto (fun j => φ (σ j)) atTop (𝓝 ψ))
    ∧ (∀ ε b x : ℝ, 0 < ε → 2 * ε < b →
        0 ≤ ε * x ^ 2 - b * x + ε →
        x < (b + Real.sqrt (b ^ 2 - 4 * ε ^ 2)) / (2 * ε) →
        x ≤ (b - Real.sqrt (b ^ 2 - 4 * ε ^ 2)) / (2 * ε)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun q qlim hconv x =>
      mosco_pointwise_recovery q qlim hconv x
  · exact fun φ hbd => finite_stage_state_compactness φ hbd
  · exact fun ε b x hε hsmall hself hbelow =>
      quadratic_gap_dichotomy ε b x hε hsmall hself hbelow

end NCG
