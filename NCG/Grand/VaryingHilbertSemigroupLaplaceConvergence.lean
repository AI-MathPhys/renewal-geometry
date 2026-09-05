/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniformSemigroupApproximation
import NCG.Grand.VaryingHilbertStrongBoundedness
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Laplace transforms of convergent varying-Hilbert semigroups

Uniform strong convergence on every compact positive-time set, together with
contractivity, passes to Laplace transforms on the whole positive half-line.
The proof is a varying-space dominated-convergence argument in the common
carrier Hilbert space.  It is the analytic reverse bridge from semigroup
convergence to strong resolvent convergence.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [NormedSpace ℝ H] [IsScalarTower ℝ K H] [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)]
  [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, NormedSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ K (Hn n)]

/-- Compact-uniform strong convergence of contraction semigroups implies
convergence of their positive-half-line Laplace transforms after embedding
all stage vectors into the common carrier. -/
theorem StrongOperatorConvergesUniformlyOn.tendsto_laplace_integrals
    (J : System (K := K) (H := H) (Hn := Hn))
    (Sn : ∀ n, ℝ → Hn n →L[K] Hn n)
    (S : ℝ → H →L[K] H)
    (hpositive : ∀ s : Set ℝ, IsCompact s → (∀ t ∈ s, 0 < t) →
      J.StrongOperatorConvergesUniformlyOn Sn S s)
    (hSnContinuous : ∀ n (x : Hn n), Continuous (fun t ↦ Sn n t x))
    (hSnContraction : ∀ n t, 0 ≤ t → ‖Sn n t‖ ≤ 1)
    (x : ∀ n, Hn n) (xlim : H) (hx : J.StronglyConverges x xlim)
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto
      (fun n ↦ ∫ t : ℝ in Ioi 0,
        ((Real.exp (-lam * t) : ℝ) : K) •
          J.embedding n (Sn n t (x n)))
      atTop
      (𝓝 (∫ t : ℝ in Ioi 0,
        ((Real.exp (-lam * t) : ℝ) : K) • S t xlim)) := by
  obtain ⟨C, hCpos, hCbound⟩ := hx.exists_pos_uniform_norm_bound J
  apply tendsto_integral_of_dominated_convergence
    (fun t : ℝ ↦ C * Real.exp (-lam * t))
  · intro n
    apply Continuous.aestronglyMeasurable
    have horbit : Continuous
        (fun t ↦ J.embedding n (Sn n t (x n))) :=
      (J.embedding n).continuous.comp (hSnContinuous n (x n))
    have hweight : Continuous
        (fun t : ℝ ↦ ((Real.exp (-lam * t) : ℝ) : K)) := by
      fun_prop
    exact hweight.smul horbit
  · have hexp :
        IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t)) (Ioi 0) := by
      convert integrableOn_exp_mul_Ioi (a := -lam) (by linarith) 0 using 1
    exact hexp.const_mul C
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [norm_smul, RCLike.norm_ofReal, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    rw [show ‖J.embedding n (Sn n t (x n))‖ = ‖Sn n t (x n)‖ by
      exact LinearIsometry.norm_map (J.embedding n) _]
    calc
      Real.exp (-lam * t) * ‖Sn n t (x n)‖
          ≤ Real.exp (-lam * t) * (‖Sn n t‖ * ‖x n‖) := by
            gcongr
            exact (Sn n t).le_opNorm (x n)
      _ ≤ Real.exp (-lam * t) * (1 * C) := by
            gcongr
            · exact hSnContraction n t (le_of_lt ht)
            · exact hCbound n
      _ = C * Real.exp (-lam * t) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htPos : 0 < t := ht
    have hpoint :=
      (hpositive ({t} : Set ℝ) isCompact_singleton (by
        intro u hu
        simp only [Set.mem_singleton_iff] at hu
        subst u
        exact htPos) x xlim hx).tendsto_at
        (show t ∈ ({t} : Set ℝ) by simp)
    exact tendsto_const_nhds.smul hpoint

end NCG.VaryingHilbert.System
