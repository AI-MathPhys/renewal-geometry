/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertWeakStrongPairing
import NCG.Grand.VaryingHilbertWeakCompactnessUpgrade
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Resolvent variational objectives on varying Hilbert spaces

This file formalizes the quadratic functional minimized by a resolvent vector.  Along strongly
convergent recovery and source sequences, convergence of the form energies implies convergence
of the complete objective, including its norm and source-pairing terms.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]

/-- The real quadratic objective whose unique minimizer is the shifted resolvent vector. -/
def resolventObjective (q : H → ℝ) (lam : ℝ) (f x : H) : ℝ :=
  q x + lam * ‖x‖ ^ 2 - 2 * RCLike.re (inner K x f)

namespace System

universe w

variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- The whole resolvent objective converges along a strong recovery sequence and a strongly
convergent moving source family. -/
theorem resolventObjective_tendsto_of_recovery
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (lam : ℝ) (f x : ∀ n, Hn n) (flim xlim : H)
    (hx : J.StronglyConverges x xlim)
    (hf : J.StronglyConverges f flim)
    (hq : Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim))) :
    Tendsto
      (fun n ↦ resolventObjective (K := K) (q n) lam (f n) (x n)) atTop
      (𝓝 (resolventObjective (K := K) qlim lam flim xlim)) := by
  have hnorm : Tendsto (fun n ↦ ‖x n‖) atTop (𝓝 ‖xlim‖) := by
    simpa [StronglyConverges] using hx.norm
  have hinner :
      Tendsto (fun n ↦ inner K (J.embedding n (x n)) (J.embedding n (f n))) atTop
        (𝓝 (inner K xlim flim)) :=
    hx.inner hf
  have hinnerRe :
      Tendsto (fun n ↦ RCLike.re (inner K (x n) (f n))) atTop
        (𝓝 (RCLike.re (inner K xlim flim))) := by
    have := RCLike.reCLM.continuous.continuousAt.tendsto.comp hinner
    simpa only [Function.comp_def, LinearIsometry.inner_map_map,
      RCLike.reCLM_apply] using this
  simpa [resolventObjective] using
    (hq.add (tendsto_const_nhds.mul (hnorm.pow 2))).sub
      (hinnerRe.const_mul 2)

/-- If the total quadratic objectives and the form energies converge along a weakly convergent,
uniformly bounded minimizer family, then the norms converge.  The moving source term is handled
by the weak--strong pairing theorem; positivity of the resolvent parameter isolates the norm
square. -/
theorem norm_tendsto_of_resolventObjective_tendsto
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (f x : ∀ n, Hn n) (flim xlim : H)
    (hx : J.WeaklyConverges x xlim)
    (hf : J.StronglyConverges f flim)
    (C : ℝ) (hbound : ∀ n, ‖x n‖ ≤ C)
    (hq : Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim)))
    (hobj : Tendsto
      (fun n ↦ resolventObjective (K := K) (q n) lam (f n) (x n)) atTop
      (𝓝 (resolventObjective (K := K) qlim lam flim xlim))) :
    Tendsto (fun n ↦ ‖x n‖) atTop (𝓝 ‖xlim‖) := by
  have hpair := hx.inner_strong J hf C hbound
  have hinnerRe :
      Tendsto (fun n ↦ RCLike.re (inner K (x n) (f n))) atTop
        (𝓝 (RCLike.re (inner K xlim flim))) := by
    have hre := RCLike.reCLM.continuous.continuousAt.tendsto.comp hpair
    simpa only [Function.comp_def, LinearIsometry.inner_map_map,
      RCLike.reCLM_apply] using hre
  have hscaled :
      Tendsto (fun n ↦ lam * ‖x n‖ ^ 2) atTop (𝓝 (lam * ‖xlim‖ ^ 2)) := by
    have hraw := (hobj.sub hq).add (hinnerRe.const_mul 2)
    convert hraw using 1
    · funext n
      simp only [resolventObjective]
      ring_nf
    · simp only [resolventObjective]
      ring_nf
  have hsquare :
      Tendsto (fun n ↦ ‖x n‖ ^ 2) atTop (𝓝 (‖xlim‖ ^ 2)) := by
    have hraw := hscaled.const_mul lam⁻¹
    convert hraw using 1
    · funext n
      field_simp
    · field_simp
  have hsqrt := hsquare.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using hsqrt


/-- Abstract Mosco minimizer convergence engine.  Weak subsequential compactness and variational
uniqueness give full weak convergence; convergence of the objective and energy isolates the
norm term; Radon--Riesz then yields strong convergence. -/
theorem stronglyConverges_of_resolventObjective
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (f x : ∀ n, Hn n) (flim xlim : H)
    (hcompact : J.IsSequentiallyWeaklyPrecompact x)
    (hunique : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        y = xlim)
    (hf : J.StronglyConverges f flim)
    (C : ℝ) (hbound : ∀ n, ‖x n‖ ≤ C)
    (hq : Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim)))
    (hobj : Tendsto
      (fun n ↦ resolventObjective (K := K) (q n) lam (f n) (x n)) atTop
      (𝓝 (resolventObjective (K := K) qlim lam flim xlim))) :
    J.StronglyConverges x xlim := by
  have hweak :=
    weaklyConverges_of_weakPrecompact_of_unique J hcompact hunique
  have hnorm := norm_tendsto_of_resolventObjective_tendsto J q qlim
    lam hlam f x flim xlim hweak hf C hbound hq hobj
  exact stronglyConverges_of_weakPrecompact_of_unique_of_norm
    J hcompact hunique hnorm

/-- The concrete variational obligations needed for one moving source and its resolvent
minimizers.  Model-specific closed-form theory can construct this record without depending on the
subsequence proof that consumes it. -/
structure ResolventMinimizerConvergenceData
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ) (lam : ℝ)
    (f x : ∀ n, Hn n) (flim xlim : H) : Prop where
  weakPrecompact : J.IsSequentiallyWeaklyPrecompact x
  weakCluster_unique : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
    (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
    (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
      y = xlim
  uniformlyBounded : ∃ C : ℝ, ∀ n, ‖x n‖ ≤ C
  energy_tendsto :
    Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim))
  objective_tendsto :
    Tendsto
      (fun n ↦ resolventObjective (K := K) (q n) lam (f n) (x n)) atTop
      (𝓝 (resolventObjective (K := K) qlim lam flim xlim))

/-- Per-source variational convergence data imply strong convergence of a whole family of
resolvent operators on varying Hilbert spaces. -/
theorem strongOperatorConverges_of_resolventMinimizerData
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (hdata : ∀ (f : ∀ n, Hn n) (flim : H),
      J.StronglyConverges f flim →
        ResolventMinimizerConvergenceData J q qlim lam f
          (fun n ↦ Tn n (f n)) flim (T flim)) :
    J.StrongOperatorConverges J Tn T := by
  intro f flim hf
  let data := hdata f flim hf
  obtain ⟨C, hbound⟩ := data.uniformlyBounded
  exact stronglyConverges_of_resolventObjective J q qlim lam hlam
    f (fun n ↦ Tn n (f n)) flim (T flim)
      data.weakPrecompact data.weakCluster_unique hf C hbound
        data.energy_tendsto data.objective_tendsto

end System

end NCG.VaryingHilbert
