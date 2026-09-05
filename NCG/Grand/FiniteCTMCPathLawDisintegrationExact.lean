/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCJumpSequenceLawExact
import NCG.Grand.FiniteCTMCNonexplosionExact
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Exact disintegration of the finite-CTMC infinite jump law

The genuine Ionescu--Tulcea law is recovered by sampling any finite prefix
and continuing it with the actual trajectory kernel. This is an equality of
full infinite-path measures, not just a one-step conditional-distribution
statement. It supplies the law-level integral decomposition needed for the
first-jump Feynman--Kac argument.

The continuation still retains its original prefix. Identifying a shifted,
dummy-coordinate-reset continuation with a freshly started CTMC law is a
separate restart assertion and is not assumed here.
-/

open MeasureTheory ProbabilityTheory Preorder
open ProbabilityTheory.Kernel

namespace NCG.FiniteCTMCPathLawDisintegration

open FiniteCTMCJumpSequenceLaw DrivenProcess DrivenProcess.FinitePath

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable (L : Matrix S S ℝ) (hL : IsGenerator L)
variable (hescape : ∀ x, 0 < escapeRate L x)

/-- Genuine infinite continuation of the given finite CTMC prefix. -/
def continuationKernel (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, ℝ × S) (ℕ → ℝ × S) := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  exact Kernel.traj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) n

instance continuationKernel_isMarkov (n : ℕ) :
    IsMarkovKernel (continuationKernel L hL hescape n) := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  unfold continuationKernel
  infer_instance

/-- Sampling a finite prefix and then continuing it recovers the full path law. -/
theorem jumpSequenceLaw_eq_continuation_comp_prefix (p : S → ℝ) (n : ℕ) :
    jumpSequenceLaw p L hL hescape =
      continuationKernel L hL hescape n ∘ₘ jumpPrefixLaw p L hL hescape n := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  unfold jumpPrefixLaw jumpSequenceLaw continuationKernel Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_frestrictLe n),
    Kernel.traj_map_frestrictLe, Measure.comp_assoc,
    Kernel.traj_comp_partialTraj (Nat.zero_le n)]

/-- The stronger joint identity retains the sampled prefix alongside the
full continuation, so integrands may depend on both without an independence
assumption. -/
theorem prefix_compProd_continuation_eq_joint_law
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (n : ℕ) :
    jumpPrefixLaw p L hL hescape n ⊗ₘ continuationKernel L hL hescape n =
      (jumpSequenceLaw p L hL hescape).map (fun z => (frestrictLe n z, z)) := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  letI : IsProbabilityMeasure (initialHoldingStateMeasure p) :=
    initialHoldingStateMeasure_isProbabilityMeasure p hp hp1
  unfold jumpPrefixLaw jumpSequenceLaw continuationKernel Kernel.trajMeasure
  rw [Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ (measurable_frestrictLe n),
    Kernel.traj_map_frestrictLe, Measure.comp_assoc,
    Measure.map_comp _ _ (by fun_prop)]
  congr 1
  ext history : 1
  rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod,
    Kernel.map_apply _ (by fun_prop)]
  exact Kernel.partialTraj_compProd_traj (X := fun _ : ℕ => ℝ × S)
    (κ := historyJumpKernel L) (Nat.zero_le n) history

variable (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)

include hp hp1 in
/-- For almost every sampled prefix, its continuation is concentrated on
the genuine nonexplosive positive-holding-time path carrier. -/
theorem ae_continuation_admissible [Nonempty S] (n : ℕ) :
    ∀ᵐ history ∂jumpPrefixLaw p L hL hescape n,
      ∀ᵐ z ∂continuationKernel L hL hescape n history,
        z ∈ FiniteCTMCPathCarrierMeasurability.admissibleJumpSequenceSet (S := S) := by
  letI : IsProbabilityMeasure (jumpSequenceLaw p L hL hescape) :=
    jumpSequenceLaw_isProbabilityMeasure p hp hp1 L hL hescape
  have hadm : ∀ᵐ z ∂jumpSequenceLaw p L hL hescape,
      z ∈ FiniteCTMCPathCarrierMeasurability.admissibleJumpSequenceSet (S := S) := by
    apply (ae_mem_iff_measure_eq
      (FiniteCTMCPathCarrierMeasurability.measurableSet_admissibleJumpSequenceSet
        (S := S)).nullMeasurableSet).mpr
    simpa using FiniteCTMCNonexplosion.jumpSequenceLaw_admissibleJumpSequenceSet_eq_one
      p hp hp1 L hL hescape
  rw [jumpSequenceLaw_eq_continuation_comp_prefix L hL hescape p n] at hadm
  exact Measure.ae_ae_of_ae_comp hadm

/-- Integrability on the full law implies integrability of almost every
conditional infinite continuation, at every finite jump index. -/
theorem ae_integrable_continuation {B : Type*} [NormedAddCommGroup B]
    {f : (ℕ → ℝ × S) → B} (hf : Integrable f (jumpSequenceLaw p L hL hescape))
    (n : ℕ) :
    ∀ᵐ history ∂jumpPrefixLaw p L hL hescape n,
      Integrable f (continuationKernel L hL hescape n history) := by
  rw [jumpSequenceLaw_eq_continuation_comp_prefix L hL hescape p n] at hf
  exact Measure.ae_integrable_of_integrable_comp hf

include hp hp1 in
/-- Exact iterated Bochner integral on the full CTMC path space. -/
theorem integral_jumpSequenceLaw_eq_prefix_continuation
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {f : (ℕ → ℝ × S) → B} (hf : Integrable f (jumpSequenceLaw p L hL hescape))
    (n : ℕ) :
    ∫ z, f z ∂jumpSequenceLaw p L hL hescape =
      ∫ history, ∫ z, f z ∂continuationKernel L hL hescape n history
        ∂jumpPrefixLaw p L hL hescape n := by
  letI : IsProbabilityMeasure (jumpPrefixLaw p L hL hescape n) :=
    jumpPrefixLaw_isProbabilityMeasure p hp hp1 L hL hescape n
  rw [jumpSequenceLaw_eq_continuation_comp_prefix L hL hescape p n,
    Measure.comp_eq_comp_const_apply] at hf ⊢
  simpa only [Kernel.const_apply] using Kernel.integral_comp hf

end

end NCG.FiniteCTMCPathLawDisintegration
