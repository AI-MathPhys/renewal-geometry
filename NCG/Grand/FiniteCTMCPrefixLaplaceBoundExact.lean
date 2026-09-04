/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCHoldingLaplaceExact
import NCG.Grand.FiniteCTMCRestartPrefixLawExact
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Geometric Laplace bounds for finite CTMC jump prefixes

The estimate is derived by iterating the actual one-step kernel. No
independence of successive holding times is assumed: their rates may depend
on the current state at every jump.
-/

open MeasureTheory ProbabilityTheory Preorder
open ProbabilityTheory.Kernel

namespace NCG.FiniteCTMCPrefixLaplaceBound

open DrivenProcess DrivenProcess.FinitePath FiniteCTMCJumpSequenceLaw
open FiniteCTMCHoldingLaplace FiniteCTMCRestartPrefixLaw

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Remove the last pair of a finite history. -/
def previousPrefix (n : ℕ) (h : Finset.Iic (n+1) → ℝ × S) : Finset.Iic n → ℝ × S :=
  fun i => h ⟨i.1, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp i.2).trans (Nat.le_succ n))⟩

theorem measurable_previousPrefix (n : ℕ) : Measurable (previousPrefix (S := S) n) := by
  unfold previousPrefix
  fun_prop

@[simp] theorem previousPrefix_appendHistory (n : ℕ)
    (h : Finset.Iic n → ℝ × S) (q : ℝ × S) :
    previousPrefix n (appendHistory n h q) = h := by
  funext i
  exact appendHistory_apply_le n h q _ (Finset.mem_Iic.mp i.2)

/-- Product of the physical holding discounts, excluding the dummy pair. -/
def prefixDiscount (s : ℝ) : (n : ℕ) → (Finset.Iic n → ℝ × S) → ℝ
  | 0, _ => 1
  | n+1, h => prefixDiscount s n (previousPrefix n h) *
      holdingDiscount s (h ⟨n+1, Finset.mem_Iic.mpr le_rfl⟩).1

theorem measurable_prefixDiscount (s : ℝ) (n : ℕ) :
    Measurable (prefixDiscount (S := S) s n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp (measurable_previousPrefix n)).mul
      ((measurable_holdingDiscount s).comp (measurable_fst.comp (measurable_pi_apply _)))

theorem prefixDiscount_nonneg (s : ℝ) (n : ℕ) (h : Finset.Iic n → ℝ × S) :
    0 ≤ prefixDiscount s n h := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (ih _) (holdingDiscount_pos _ _).le

theorem prefixDiscount_le_one (s : ℝ) (hs : 0 ≤ s) (n : ℕ)
    (h : Finset.Iic n → ℝ × S) : prefixDiscount s n h ≤ 1 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact mul_le_one₀ (ih _) (holdingDiscount_pos _ _).le (holdingDiscount_le_one _ _ hs)

theorem integrable_prefixDiscount (s : ℝ) (hs : 0 ≤ s) (n : ℕ)
    (μ : Measure (Finset.Iic n → ℝ × S)) [IsFiniteMeasure μ] :
    Integrable (prefixDiscount s n) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_prefixDiscount s n).aestronglyMeasurable
  exact ae_of_all _ fun h => by
    rw [Real.norm_eq_abs, abs_of_nonneg (prefixDiscount_nonneg s n h)]
    exact prefixDiscount_le_one s hs n h

@[simp] theorem prefixDiscount_appendHistory (s : ℝ) (n : ℕ)
    (h : Finset.Iic n → ℝ × S) (q : ℝ × S) :
    prefixDiscount s (n+1) (appendHistory n h q) =
      prefixDiscount s n h * holdingDiscount s q.1 := by
  simp only [prefixDiscount, previousPrefix_appendHistory, appendHistory_apply_last]

variable (L : Matrix S S ℝ) (hL : IsGenerator L)
  (hescape : ∀ x, 0 < escapeRate L x)

include hL hescape in
/-- Exact one-step integral of the discount product. -/
theorem integral_prefixDiscount_step (s : ℝ) (hs : 0 ≤ s) (n : ℕ)
    (h : Finset.Iic n → ℝ × S) :
    (∫ z, prefixDiscount s (n+1) z
      ∂partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) n (n+1) h) =
      prefixDiscount s n h *
        (escapeRate L (currentState n h) / (escapeRate L (currentState n h) + s)) := by
  rw [partialTraj_step_apply L hL hescape]
  rw [integral_map (measurable_appendHistory n h).aemeasurable
    (measurable_prefixDiscount s (n+1)).aestronglyMeasurable]
  simp_rw [prefixDiscount_appendHistory]
  rw [integral_const_mul]
  congr 1
  exact integral_holdingDestination_discount L hL hescape (currentState n h) s hs

include hL hescape in
/-- Iterating the true history-dependent kernel gives a geometric bound. -/
theorem integral_prefixDiscount_le_pow (s R : ℝ) (hs : 0 ≤ s) (hRpos : 0 < R)
    (hR : ∀ x, escapeRate L x ≤ R) (n : ℕ) (h : Finset.Iic 0 → ℝ × S) :
    (∫ z, prefixDiscount s n z ∂partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) 0 n h) ≤
      (R / (R+s)) ^ n := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  induction n with
  | zero => simp [partialTraj_self, Kernel.id_apply, prefixDiscount]
  | succ n ih =>
    rw [partialTraj_succ_eq_comp (Nat.zero_le n)]
    rw [Kernel.integral_comp (integrable_prefixDiscount s hs (n+1) _)]
    have hinner : ∀ z : Finset.Iic n → ℝ × S,
        (∫ w, prefixDiscount s (n+1) w ∂partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) n (n+1) z) ≤
          prefixDiscount s n z * (R / (R+s)) := by
      intro z
      rw [integral_prefixDiscount_step L hL hescape s hs]
      apply mul_le_mul_of_nonneg_left _ (prefixDiscount_nonneg s n z)
      rw [← integral_holdingDestination_discount L hL hescape (currentState n z) s hs]
      exact integral_holdingDestination_discount_le L hL hescape (currentState n z) s R hs (hR _)
    have hi := (integrable_prefixDiscount (S := S) s hs (n+1)
      ((partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) n (n+1) ∘ₖ
        partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) 0 n) h)).integral_comp
    calc
      _ ≤ ∫ z, prefixDiscount s n z * (R / (R+s))
          ∂partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) 0 n h :=
        integral_mono hi ((integrable_prefixDiscount s hs n _).mul_const _) hinner
      _ = (∫ z, prefixDiscount s n z ∂partialTraj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) 0 n h) *
          (R / (R+s)) := integral_mul_const _ _
      _ ≤ (R / (R+s)) ^ n * (R / (R+s)) :=
        mul_le_mul_of_nonneg_right ih (div_nonneg hRpos.le (add_nonneg hRpos.le hs))
      _ = (R / (R+s)) ^ (n+1) := (pow_succ _ _).symm

end

end NCG.FiniteCTMCPrefixLaplaceBound
