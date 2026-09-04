/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCJumpSequenceLawExact
import NCG.Grand.TrajectoryPrefixTransportExact

/-!
# Concrete finite-prefix laws of a canonically restarted CTMC

The prefix reset drops the past and resets the new dummy holding time to
zero. It preserves the current state, commutes with adjoining a sampled
jump, and therefore intertwines the actual CTMC one-step kernel. The
finite-prefix transport theorem then identifies every restarted prefix law.
-/

open MeasureTheory ProbabilityTheory Preorder
open ProbabilityTheory.Kernel

namespace NCG.FiniteCTMCRestartPrefixLaw

open FiniteCTMCJumpSequenceLaw DrivenProcess DrivenProcess.FinitePath

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Append one sampled holding-time/state pair to a finite history. -/
def appendHistory (n : ℕ) (h : Finset.Iic n → ℝ × S) (q : ℝ × S) :
    Finset.Iic (n + 1) → ℝ × S :=
  IicProdIoc (X := fun _ : ℕ => ℝ × S) n (n + 1)
    (h, MeasurableEquiv.piSingleton (X := fun _ : ℕ => ℝ × S) n q)

theorem measurable_appendHistory (n : ℕ) (h : Finset.Iic n → ℝ × S) :
    Measurable (appendHistory n h) := by
  unfold appendHistory
  exact (measurable_IicProdIoc (X := fun _ : ℕ => ℝ × S)).comp
    (measurable_const.prodMk (MeasurableEquiv.piSingleton
      (X := fun _ : ℕ => ℝ × S) n).measurable)

theorem appendHistory_apply_le (n : ℕ) (h : Finset.Iic n → ℝ × S) (q : ℝ × S)
    (i : Finset.Iic (n + 1)) (hi : i.1 ≤ n) :
    appendHistory n h q i = h ⟨i.1, Finset.mem_Iic.mpr hi⟩ := by
  simp [appendHistory, IicProdIoc, hi]

@[simp] theorem appendHistory_apply_last (n : ℕ) (h : Finset.Iic n → ℝ × S)
    (q : ℝ × S) :
    appendHistory n h q ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ = q := by
  simp [appendHistory, IicProdIoc, MeasurableEquiv.piSingleton]

/-- Restart a finite prefix at jump index `a`, including canonical dummy reset. -/
def resetShiftPrefix (a n : ℕ) (h : Finset.Iic (a + n) → ℝ × S)
    (i : Finset.Iic n) : ℝ × S :=
  let q := h ⟨a + i.1, Finset.mem_Iic.mpr
    (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) a)⟩
  (if i.1 = 0 then 0 else q.1, q.2)

theorem measurable_resetShiftPrefix (a n : ℕ) :
    Measurable (resetShiftPrefix (S := S) a n) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i.1 = 0
  · simp only [resetShiftPrefix, hi, ite_true]
    fun_prop
  · simp only [resetShiftPrefix, hi, ite_false]
    fun_prop

@[simp] theorem currentState_resetShiftPrefix (a n : ℕ)
    (h : Finset.Iic (a + n) → ℝ × S) :
    currentState n (resetShiftPrefix a n h) = currentState (a + n) h := rfl

/-- Resetting commutes with adjoining the next physical jump. -/
theorem resetShiftPrefix_appendHistory (a n : ℕ)
    (h : Finset.Iic (a + n) → ℝ × S) (q : ℝ × S) :
    resetShiftPrefix a (n + 1) (appendHistory (a + n) h q) =
      appendHistory n (resetShiftPrefix a n h) q := by
  funext i
  by_cases hi : i.1 ≤ n
  · have hai : a + i.1 ≤ a + n := Nat.add_le_add_left hi a
    simp [resetShiftPrefix, appendHistory, IicProdIoc, hi, hai]
  · have hilast : i.1 = n + 1 := by
      have := Finset.mem_Iic.mp i.2
      omega
    have hieq : i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hilast
    subst i
    simp [resetShiftPrefix, appendHistory, IicProdIoc, MeasurableEquiv.piSingleton]

variable (L : Matrix S S ℝ) (hL : IsGenerator L)
variable (hescape : ∀ x, 0 < escapeRate L x)

include hL hescape in
/-- The actual one-step prefix kernel samples the CTMC jump and appends it. -/
theorem partialTraj_step_apply (n : ℕ) (h : Finset.Iic n → ℝ × S) :
    partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) n (n + 1) h =
      (historyJumpKernel L n h).map (appendHistory n h) := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  rw [partialTraj_succ_self, Kernel.map_apply _
      (measurable_IicProdIoc (X := fun _ : ℕ => ℝ × S) (m := n) (n := n + 1)),
    Kernel.prod_apply, Kernel.id_apply,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ℝ × S) n).measurable,
    Measure.dirac_prod,
    Measure.map_map (measurable_IicProdIoc (X := fun _ : ℕ => ℝ × S)
      (m := n) (n := n + 1)) (measurable_prodMk_left (x := h)),
    Measure.map_map ((measurable_IicProdIoc (X := fun _ : ℕ => ℝ × S)
      (m := n) (n := n + 1)).comp (measurable_prodMk_left (x := h)))
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ℝ × S) n).measurable]
  rfl

include hL hescape in
/-- One-step compatibility is derived from the actual current-state kernel,
not supplied as an input to the CTMC restart theorem. -/
theorem map_step_resetShiftPrefix (a n : ℕ) (h : Finset.Iic (a + n) → ℝ × S) :
    (partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L)
      (a + n) (a + n + 1) h).map (resetShiftPrefix a (n + 1)) =
      partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L)
        n (n + 1) (resetShiftPrefix a n h) := by
  rw [partialTraj_step_apply L hL hescape, partialTraj_step_apply L hL hescape,
    Measure.map_map (measurable_resetShiftPrefix a (n + 1))
      (measurable_appendHistory (a + n) h)]
  have hkernel : historyJumpKernel L n (resetShiftPrefix a n h) =
      historyJumpKernel L (a + n) h := rfl
  rw [hkernel]
  congr 1
  funext q
  exact resetShiftPrefix_appendHistory a n h q

include hL hescape in
/-- The concrete reset intertwines one-step prefix kernels. -/
theorem resetShiftPrefix_step_kernel (a n : ℕ) :
    (partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L)
      (a + n) (a + (n + 1))).map (resetShiftPrefix a (n + 1)) =
      partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) n (n + 1) ∘ₖ
        Kernel.deterministic (resetShiftPrefix a n) (measurable_resetShiftPrefix a n) := by
  rw [Kernel.comp_deterministic_eq_comap]
  ext h : 1
  rw [Kernel.map_apply _ (measurable_resetShiftPrefix a (n + 1)), Kernel.comap_apply]
  exact map_step_resetShiftPrefix L hL hescape a n h

include hL hescape in
/-- Every restarted finite-prefix law equals the freshly started prefix law;
the compatibility input is proved from the CTMC kernel above. -/
theorem map_partialTraj_resetShiftPrefix (a n : ℕ) :
    (partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L)
      a (a + n)).map (resetShiftPrefix a n) =
      partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) 0 n ∘ₖ
        Kernel.deterministic (resetShiftPrefix a 0) (measurable_resetShiftPrefix a 0) := by
  exact TrajectoryPrefixTransport.map_partialTraj_eq_of_step_compatibility
    (X := fun _ : ℕ => ℝ × S) (Y := fun _ : ℕ => ℝ × S)
    (historyJumpKernel L) (historyJumpKernel L) a (resetShiftPrefix a)
    (measurable_resetShiftPrefix a) (resetShiftPrefix_step_kernel L hL hescape a) n

end

end NCG.FiniteCTMCRestartPrefixLaw
