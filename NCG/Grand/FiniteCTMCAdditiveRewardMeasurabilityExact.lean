/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCPathEvaluationMeasurabilityExact

/-!
# Measurability of finite-CTMC additive rewards

The reward accumulated up to a finite horizon consists of the complete
holding and jump contributions before the occupied interval, followed by the
residual occupation contribution in that interval.  The fixed-jump-count
formula is measurable, and measurable selection by the random jump index
makes the full finite-horizon reward measurable.
-/

open MeasureTheory Finset Set
open scoped BigOperators

noncomputable section

namespace NCG.FiniteCTMCAdditiveRewardMeasurability

open NCG.FiniteCTMCPathCarrierMeasurability
open NCG.FiniteCTMCPathEvaluationMeasurability

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Measurable evaluation of a countable family at a measurable natural
index. -/
theorem measurable_natIndexedEvaluation
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (index : α → ℕ) (f : ℕ → α → β)
    (hindex : Measurable index) (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => f (index x) x) := by
  intro s hs
  have hpreimage :
      (fun x => f (index x) x) ⁻¹' s =
        ⋃ n : ℕ, (index ⁻¹' ({n} : Set ℕ)) ∩ (f n ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨index x, rfl, hx⟩
    · rintro ⟨n, hn, hx⟩
      simpa [hn] using hx
  rw [hpreimage]
  exact MeasurableSet.iUnion fun n =>
    (hindex (measurableSet_singleton n)).inter (hf n hs)

/-- Reward accumulated up to `T` when exactly `n` jumps occur before the
horizon.  Indices `i<n` contribute a full holding reward and the directed
jump reward; the final occupied interval contributes its residual holding
time. -/
def fixedJumpCountAdditiveReward
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (n : ℕ)
    (z : AdmissibleJumpSequence (S := S)) : ℝ :=
  (Finset.range n).sum (fun i =>
      physicalHold z.1 i * v (z.1 i).2 +
        g (z.1 i).2 (z.1 (i + 1)).2) +
    (T - cumulativeJumpTime z.1 n) * v (z.1 n).2

/-- The fixed-jump-count reward is measurable in the underlying admissible
jump sequence. -/
theorem measurable_fixedJumpCountAdditiveReward
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (n : ℕ) :
    Measurable (fixedJumpCountAdditiveReward v g T n) := by
  have hcoord : ∀ i : ℕ, Measurable
      (fun z : AdmissibleJumpSequence (S := S) => z.1 i) :=
    fun i => (measurable_pi_apply i).comp measurable_subtype_coe
  have hhold : ∀ i : ℕ, Measurable
      (fun z : AdmissibleJumpSequence (S := S) => physicalHold z.1 i) :=
    fun i => by
      change Measurable (Prod.fst ∘
        fun z : AdmissibleJumpSequence (S := S) => z.1 (i + 1))
      exact measurable_fst.comp (hcoord (i + 1))
  have hstate : ∀ i : ℕ, Measurable
      (fun z : AdmissibleJumpSequence (S := S) => (z.1 i).2) :=
    fun i => measurable_snd.comp (hcoord i)
  have hv : Measurable v := measurable_of_countable v
  have hg : Measurable (Function.uncurry g) :=
    measurable_of_countable (Function.uncurry g)
  have hsum : Measurable (fun z : AdmissibleJumpSequence (S := S) =>
      (Finset.range n).sum (fun i =>
        physicalHold z.1 i * v (z.1 i).2 +
          g (z.1 i).2 (z.1 (i + 1)).2)) := by
    apply Finset.measurable_sum
    intro i _hi
    exact ((hhold i).mul (hv.comp (hstate i))).add
      (hg.comp ((hstate i).prodMk (hstate (i + 1))))
  have hcum : Measurable (fun z : AdmissibleJumpSequence (S := S) =>
      cumulativeJumpTime z.1 n) :=
    (measurable_cumulativeJumpTime (S := S) n).comp measurable_subtype_coe
  unfold fixedJumpCountAdditiveReward
  exact hsum.add ((measurable_const.sub hcum).mul (hv.comp (hstate n)))

/-- Exact protected additive reward accumulated by an admissible CTMC path
up to the nonnegative horizon `T`. -/
def finiteHorizonAdditiveReward
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ)
    (z : AdmissibleJumpSequence (S := S)) : ℝ :=
  fixedJumpCountAdditiveReward v g T (admissibleJumpIndex z T) z

/-- The full occupation-plus-jump reward from the manuscript is measurable
on the probability-one admissible path carrier. -/
theorem measurable_finiteHorizonAdditiveReward
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    Measurable (finiteHorizonAdditiveReward v g T) := by
  exact measurable_natIndexedEvaluation
    (fun z : AdmissibleJumpSequence (S := S) => admissibleJumpIndex z T)
    (fun n z => fixedJumpCountAdditiveReward v g T n z)
    (measurable_admissibleJumpIndex T hT)
    (fun n => measurable_fixedJumpCountAdditiveReward v g T n)

/-- The normalized empirical reward is measurable at every positive
horizon. -/
theorem measurable_normalizedFiniteHorizonAdditiveReward
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (hT : 0 < T) :
    Measurable (fun z : AdmissibleJumpSequence (S := S) =>
      finiteHorizonAdditiveReward v g T z / T) :=
  (measurable_finiteHorizonAdditiveReward v g T hT.le).div_const T

end NCG.FiniteCTMCAdditiveRewardMeasurability
