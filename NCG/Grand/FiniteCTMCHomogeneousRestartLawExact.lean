/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCRestartPrefixLawExact
import NCG.Grand.FiniteCTMCPathLawDisintegrationExact
import NCG.Grand.FiniteCTMCCanonicalRestartExact

/-!
# Homogeneous restart of the genuine infinite CTMC trajectory law

Dropping a finite past and resetting the dummy holding coordinate transports
the actual continuation law to a fresh trajectory started at its current
state. This is proved from concrete one-step kernel compatibility, finite
prefix induction, and uniqueness of finite measures from their marginals.
-/

open MeasureTheory ProbabilityTheory Preorder
open ProbabilityTheory.Kernel

namespace NCG.FiniteCTMCHomogeneousRestartLaw

open FiniteCTMCJumpSequenceLaw FiniteCTMCRestartPrefixLaw
open FiniteCTMCPathLawDisintegration DrivenProcess DrivenProcess.FinitePath
open FiniteCTMCFeynmanKacPathMoment

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Drop the first `a` pairs, retaining their terminal state but resetting
the new nonphysical initial holding coordinate to zero. -/
def resetShift (a : ℕ) (z : ℕ → ℝ × S) (n : ℕ) : ℝ × S :=
  (if n = 0 then 0 else (z (a + n)).1, (z (a + n)).2)

theorem measurable_resetShift (a : ℕ) : Measurable (resetShift (S := S) a) := by
  apply measurable_pi_lambda
  intro n
  by_cases hn : n = 0
  · simp only [resetShift, hn, ite_true]
    fun_prop
  · simp only [resetShift, hn, ite_false]
    fun_prop

theorem restrict_resetShift (a n : ℕ) :
    frestrictLe n ∘ resetShift (S := S) a =
      resetShiftPrefix a n ∘ frestrictLe (a + n) := rfl

/-- At the first jump this is exactly the normalized admissible restart,
not merely the raw tail with a nonzero dummy holding time. -/
theorem resetShift_one_eq_canonicalRestart
    (z : FiniteCTMCPathCarrierMeasurability.AdmissibleJumpSequence (S := S)) :
    resetShift 1 z.1 = (FiniteCTMCCanonicalRestart.canonicalRestart z).1 := by
  funext n
  simp [resetShift, FiniteCTMCCanonicalRestart.canonicalRestart,
    FiniteCTMCCanonicalRestart.resetDummy, FiniteCTMCAdmissiblePathRestart.tailJumpSequence,
    Nat.add_comm]

variable (L : Matrix S S ℝ) (hL : IsGenerator L)
variable (hescape : ∀ x, 0 < escapeRate L x)

/-- The canonical deterministic initial prefix for a process started at `x`. -/
def pointInitialPrefix (x : S) : Finset.Iic 0 → ℝ × S := fun _ => (0, x)

theorem discrete_pointMass (x : S) :
    QuantumCylinderInverseLimit.discrete (pointMass x) = Measure.dirac x := by
  simp [QuantumCylinderInverseLimit.discrete, pointMass, apply_ite, ite_smul]

theorem initialHoldingStateMeasure_pointMass (x : S) :
    initialHoldingStateMeasure (pointMass x) = Measure.dirac (0, x) := by
  rw [initialHoldingStateMeasure, discrete_pointMass, Measure.dirac_prod_dirac]

/-- The freshly started trajectory is exactly the repository's point-start
jump-sequence probability law, with its canonical zero dummy coordinate. -/
theorem jumpSequenceLaw_pointMass_eq_continuation (x : S) :
    jumpSequenceLaw (pointMass x) L hL hescape =
      continuationKernel L hL hescape 0 (pointInitialPrefix x) := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  unfold jumpSequenceLaw Kernel.trajMeasure continuationKernel
  rw [initialHoldingStateMeasure_pointMass,
    Measure.map_dirac' (MeasurableEquiv.piUnique _).symm.measurable,
    Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- The full infinite continuation resets to the genuine fresh trajectory
whose initial state is the last state of the supplied prefix. -/
theorem map_continuation_resetShift (a : ℕ) (h : Finset.Iic a → ℝ × S) :
    (continuationKernel L hL hescape a h).map (resetShift a) =
      continuationKernel L hL hescape 0 (resetShiftPrefix a 0 h) := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  apply TrajectoryPrefixTransport.measure_eq_of_prefix_marginals
  intro n
  rw [Measure.map_map (measurable_frestrictLe n) (measurable_resetShift a),
    restrict_resetShift,
    ← Measure.map_map (measurable_resetShiftPrefix a n) (measurable_frestrictLe (a + n))]
  have hleft : (continuationKernel L hL hescape a h).map (frestrictLe (a + n)) =
      partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) a (a + n) h :=
    Kernel.traj_map_frestrictLe_apply (X := fun _ : ℕ => ℝ × S)
      (κ := historyJumpKernel L) a (a + n) h
  have hright : (continuationKernel L hL hescape 0 (resetShiftPrefix a 0 h)).map
      (frestrictLe n) =
      partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L)
        0 n (resetShiftPrefix a 0 h) :=
    Kernel.traj_map_frestrictLe_apply (X := fun _ : ℕ => ℝ × S)
      (κ := historyJumpKernel L) 0 n (resetShiftPrefix a 0 h)
  rw [hleft, hright]
  have hp := congrArg
    (fun K : Kernel (Finset.Iic a → ℝ × S) (Finset.Iic n → ℝ × S) => K h)
    (map_partialTraj_resetShiftPrefix L hL hescape a n)
  simpa only [Kernel.map_apply _ (measurable_resetShiftPrefix a n),
    Kernel.comp_deterministic_eq_comap, Kernel.comap_apply] using hp

/-- Full homogeneous restart, expressed directly using the concrete
point-start Ionescu--Tulcea law used by the Feynman--Kac path moment. -/
theorem map_continuation_resetShift_eq_jumpSequenceLaw
    (a : ℕ) (h : Finset.Iic a → ℝ × S) :
    (continuationKernel L hL hescape a h).map (resetShift a) =
      jumpSequenceLaw (pointMass (currentState a h)) L hL hescape := by
  rw [map_continuation_resetShift]
  have hinit : resetShiftPrefix a 0 h = pointInitialPrefix (currentState a h) := by
    funext i
    have hi : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ :=
      Subtype.ext (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2))
    subst i
    rfl
  rw [hinit, ← jumpSequenceLaw_pointMass_eq_continuation]

end

end NCG.FiniteCTMCHomogeneousRestartLaw
