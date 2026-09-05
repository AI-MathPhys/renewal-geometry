/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SummableCorrections
import NCG.Grand.AFInductiveLimitState

/-!
# Summable correction of states on a C-star inductive system

This is the dependent-stage completion of
'thm:summable-state-correction'.  Later states are pulled back to each fixed
stage.  Their consecutive differences are controlled by the original
one-step defects, so the abstract Banach telescoping theorem produces a
norm-convergent corrected functional at every stage.  Positivity,
normalization, and exact compatibility are then recovered from norm limits.
-/

open Filter
open scoped ComplexOrder

noncomputable section

namespace NCG.SummableInductiveStateCorrection

universe v

variable {A : ℕ → Type v} [∀ n, CStarAlgebra (A n)]
variable (f : ∀ m n, m ≤ n → A m →⋆ₐ[ℂ] A n)
variable [DirectedSystem A (fun m n hmn => f m n hmn)]
variable [NCG.PreCStarDirectLimit.IsometricSystem f]

/-- Two pre-C-star states are equal once their continuous functionals are
equal; the remaining structure fields are propositions. -/
theorem preCStarState_ext {B : Type*} [CStarAlgebra B]
    {phi psi : NCG.PreCStarState B}
    (h : phi.toContinuousLinearMap = psi.toContinuousLinearMap) : phi = psi := by
  cases phi with
  | mk phi hone hpos hnorm =>
      cases psi with
      | mk psi kone kpos knorm =>
          dsimp only at h
          subst psi
          rfl

/-- A connecting map as a continuous linear contraction. -/
def embeddingCLM {m n : ℕ} (hmn : m ≤ n) : A m →L[ℂ] A n :=
  (f m n hmn).toLinearMap.mkContinuous 1 fun a => by
    change ‖f m n hmn a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le (f m n hmn) a

@[simp] theorem embeddingCLM_apply {m n : ℕ} (hmn : m ≤ n) (a : A m) :
    embeddingCLM f hmn a = f m n hmn a := rfl

/-- The state at cutoff 'm+k', restricted to the fixed old stage 'm'. -/
def pulledStateCLM (omega : ∀ n, NCG.PreCStarState (A n)) (m k : ℕ) :
    A m →L[ℂ] ℂ :=
  (omega (m + k)).toContinuousLinearMap.comp
    (embeddingCLM f (Nat.le_add_right m k))

@[simp] theorem pulledStateCLM_apply
    (omega : ∀ n, NCG.PreCStarState (A n)) (m k : ℕ) (a : A m) :
    pulledStateCLM f omega m k a =
      omega (m + k) (f m (m + k) (Nat.le_add_right m k) a) := rfl

@[simp] theorem pulledStateCLM_zero
    (omega : ∀ n, NCG.PreCStarState (A n)) (m : ℕ) :
    pulledStateCLM f omega m 0 = (omega m).toContinuousLinearMap := by
  ext a
  change omega m (f m m (Nat.le_add_right m 0) a) = omega m a
  congr 1
  exact DirectedSystem.map_self (f := fun i j h => f i j h) a

/-- Pullback preserves the norm-one state bound. -/
theorem norm_pulledStateCLM_le_one
    (omega : ∀ n, NCG.PreCStarState (A n)) (m k : ℕ) :
    ‖pulledStateCLM f omega m k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  calc
    ‖pulledStateCLM f omega m k a‖
        ≤ ‖(omega (m + k)).toContinuousLinearMap‖ *
            ‖f m (m + k) (Nat.le_add_right m k) a‖ :=
      (omega (m + k)).toContinuousLinearMap.le_opNorm _
    _ = ‖f m (m + k) (Nat.le_add_right m k) a‖ := by
      rw [(omega (m + k)).norm_eq_one, one_mul]
    _ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le _ _
    _ = 1 * ‖a‖ := (one_mul _).symm

/-- The fixed-stage pulled-back sequence inherits the one-step defect bound. -/
theorem pulledStateCLM_step_bound
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n)
    (m k : ℕ) :
    ‖pulledStateCLM f omega m (k + 1) - pulledStateCLM f omega m k‖
      ≤ delta (m + k) := by
  let defect : A (m + k) →L[ℂ] ℂ :=
    (omega (m + k + 1)).toContinuousLinearMap.comp
        (embeddingCLM f (Nat.le_succ (m + k))) -
      (omega (m + k)).toContinuousLinearMap
  have hdelta : 0 ≤ delta (m + k) :=
    (norm_nonneg defect).trans (hdef (m + k))
  apply ContinuousLinearMap.opNorm_le_bound _ hdelta
  intro a
  have hpoint :
      (pulledStateCLM f omega m (k + 1) -
          pulledStateCLM f omega m k) a =
        defect (f m (m + k) (Nat.le_add_right m k) a) := by
    simp only [ContinuousLinearMap.sub_apply, pulledStateCLM_apply, defect,
      ContinuousLinearMap.comp_apply, embeddingCLM_apply]
    congr 2
    exact (DirectedSystem.map_map' f (Nat.le_add_right m k)
      (Nat.le_succ (m + k)) a).symm
  rw [hpoint]
  calc
    ‖defect (f m (m + k) (Nat.le_add_right m k) a)‖
        ≤ ‖defect‖ * ‖f m (m + k) (Nat.le_add_right m k) a‖ :=
      defect.le_opNorm _
    _ ≤ delta (m + k) * ‖f m (m + k) (Nat.le_add_right m k) a‖ :=
      mul_le_mul_of_nonneg_right (hdef (m + k)) (norm_nonneg _)
    _ ≤ delta (m + k) * ‖a‖ :=
      mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le _ _) hdelta

/-- At every fixed stage the pulled-back states have a canonical norm limit
with the exact defect-tail estimate. -/
theorem fixedStage_limit
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n)
    (m : ℕ) :
    ∃ psi : A m →L[ℂ] ℂ,
      Tendsto (pulledStateCLM f omega m) atTop (nhds psi) ∧
      ‖psi - (omega m).toContinuousLinearMap‖ ≤
        ∑' k : ℕ, delta (k + m) := by
  obtain ⟨psi, hpsi, htail⟩ :=
    summable_defect_limit (pulledStateCLM f omega m)
      (fun k => delta (m + k)) (by
        simpa [add_comm] using (summable_nat_add_iff m).mpr hdelta)
      (pulledStateCLM_step_bound f omega delta hdef m)
  refine ⟨psi, hpsi, ?_⟩
  simpa [pulledStateCLM_zero, add_comm] using htail 0

/-- The canonical corrected continuous functional at stage 'm'. -/
def correctedCLM
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n)
    (m : ℕ) : A m →L[ℂ] ℂ :=
  Classical.choose (fixedStage_limit f omega delta hdelta hdef m)

theorem correctedCLM_tendsto
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n)
    (m : ℕ) :
    Tendsto (pulledStateCLM f omega m) atTop
      (nhds (correctedCLM f omega delta hdelta hdef m)) :=
  (Classical.choose_spec (fixedStage_limit f omega delta hdelta hdef m)).1

theorem correctedCLM_tail
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n)
    (m : ℕ) :
    ‖correctedCLM f omega delta hdelta hdef m -
        (omega m).toContinuousLinearMap‖ ≤ ∑' k : ℕ, delta (k + m) :=
  (Classical.choose_spec (fixedStage_limit f omega delta hdelta hdef m)).2

theorem norm_correctedCLM_le_one
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n)
    (m : ℕ) :
    ‖correctedCLM f omega delta hdelta hdef m‖ ≤ 1 := by
  have hmem : correctedCLM f omega delta hdelta hdef m ∈
      Metric.closedBall (0 : A m →L[ℂ] ℂ) 1 := by
    apply Metric.isClosed_closedBall.mem_of_tendsto
      (correctedCLM_tendsto f omega delta hdelta hdef m)
    exact Eventually.of_forall fun k => by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        norm_pulledStateCLM_le_one f omega m k
  simpa [Metric.mem_closedBall, dist_zero_right] using hmem

theorem correctedCLM_one
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n)
    (m : ℕ) :
    correctedCLM f omega delta hdelta hdef m 1 = 1 := by
  have ht := ((ContinuousLinearMap.apply ℂ ℂ (1 : A m)).continuous.tendsto _).comp
    (correctedCLM_tendsto f omega delta hdelta hdef m)
  change Tendsto (fun k => pulledStateCLM f omega m k 1) atTop
    (nhds (correctedCLM f omega delta hdelta hdef m 1)) at ht
  have ht' : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop
      (nhds (correctedCLM f omega delta hdelta hdef m 1)) := by
    convert ht using 1
    funext k
    simp [pulledStateCLM]
  exact tendsto_nhds_unique ht' tendsto_const_nhds

/-- Norm limits of the pulled-back states remain positive normalized states. -/
def correctedState
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n)
    (m : ℕ) : NCG.PreCStarState (A m) where
  toContinuousLinearMap := correctedCLM f omega delta hdelta hdef m
  map_one := correctedCLM_one f omega delta hdelta hdef m
  map_star_mul_self_nonneg := by
    intro a
    have ht := ((ContinuousLinearMap.apply ℂ ℂ (star a * a)).continuous.tendsto _).comp
      (correctedCLM_tendsto f omega delta hdelta hdef m)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    exact Eventually.of_forall fun k => by
      change 0 ≤ omega (m + k)
        (f m (m + k) (Nat.le_add_right m k) (star a * a))
      rw [map_mul, map_star]
      exact (omega (m + k)).map_star_mul_self_nonneg
        (f m (m + k) (Nat.le_add_right m k) a)
  norm_eq_one := by
    letI : Nontrivial (A m) := ⟨⟨0, 1, fun hzero => by
      have hz := congrArg (correctedCLM f omega delta hdelta hdef m) hzero
      rw [map_zero, correctedCLM_one f omega delta hdelta hdef m] at hz
      exact zero_ne_one hz⟩⟩
    apply le_antisymm
    · exact norm_correctedCLM_le_one f omega delta hdelta hdef m
    · calc
        1 = ‖correctedCLM f omega delta hdelta hdef m 1‖ := by
          rw [correctedCLM_one f omega delta hdelta hdef m, norm_one]
        _ ≤ ‖correctedCLM f omega delta hdelta hdef m‖ * ‖(1 : A m)‖ :=
          (correctedCLM f omega delta hdelta hdef m).le_opNorm 1
        _ = ‖correctedCLM f omega delta hdelta hdef m‖ := by
          rw [CStarRing.norm_one, mul_one]

/-- Pulling the next old stage back one step gives the one-step shift of the
current fixed-stage sequence. -/
theorem directedMap_heq_of_index_eq {i p q : ℕ}
    (hip : i ≤ p) (hiq : i ≤ q) (hpq : p = q) (a : A i) :
    HEq (f i p hip a) (f i q hiq a) := by
  subst q
  rfl

theorem state_apply_eq_of_heq
    (omega : ∀ n, NCG.PreCStarState (A n)) {p q : ℕ}
    (hpq : p = q) {x : A p} {y : A q} (hxy : HEq x y) :
    omega p x = omega q y := by
  subst q
  exact congrArg (omega p) (eq_of_heq hxy)

theorem pulledStateCLM_succ_relation
    (omega : ∀ n, NCG.PreCStarState (A n)) (m k : ℕ) (a : A m) :
    pulledStateCLM f omega m (k + 1) a =
      pulledStateCLM f omega (m + 1) k (f m (m + 1) (Nat.le_succ m) a) := by
  simp only [pulledStateCLM_apply]
  have hidx : m + (k + 1) = m + 1 + k := by omega
  apply state_apply_eq_of_heq omega hidx
  have hdirect : HEq
      (f m (m + (k + 1)) (Nat.le_add_right m (k + 1)) a)
      (f m (m + 1 + k) ((Nat.le_succ m).trans
        (Nat.le_add_right (m + 1) k)) a) :=
    directedMap_heq_of_index_eq f _ _ hidx a
  have hcomp :
      f m (m + 1 + k) ((Nat.le_succ m).trans
          (Nat.le_add_right (m + 1) k)) a =
        f (m + 1) (m + 1 + k) (Nat.le_add_right (m + 1) k)
          (f m (m + 1) (Nat.le_succ m) a) :=
    (DirectedSystem.map_map' f (Nat.le_succ m)
      (Nat.le_add_right (m + 1) k) a).symm
  exact hdirect.trans (heq_of_eq hcomp)

/-- The corrected states are exactly compatible with every one-step
connecting map. -/
theorem correctedState_succ_compatible
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n)
    (m : ℕ) (a : A m) :
    correctedState f omega delta hdelta hdef (m + 1)
        (f m (m + 1) (Nat.le_succ m) a) =
      correctedState f omega delta hdelta hdef m a := by
  have hnext := ((ContinuousLinearMap.apply ℂ ℂ
      (f m (m + 1) (Nat.le_succ m) a)).continuous.tendsto _).comp
    (correctedCLM_tendsto f omega delta hdelta hdef (m + 1))
  change Tendsto
    (fun k => pulledStateCLM f omega (m + 1) k
      (f m (m + 1) (Nat.le_succ m) a)) atTop
    (nhds (correctedState f omega delta hdelta hdef (m + 1)
      (f m (m + 1) (Nat.le_succ m) a))) at hnext
  have hcurrent := ((ContinuousLinearMap.apply ℂ ℂ a).continuous.tendsto _).comp
    (correctedCLM_tendsto f omega delta hdelta hdef m)
  change Tendsto (fun k => pulledStateCLM f omega m k a) atTop
    (nhds (correctedState f omega delta hdelta hdef m a)) at hcurrent
  have hshift := hcurrent.comp (Filter.tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique
    (hnext.congr' (Eventually.of_forall fun k =>
      (pulledStateCLM_succ_relation f omega m k a).symm))
    hshift

/-- The corrected family as a compatible state on the complete directed
system. -/
def compatibleCorrectedState
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n) :
    NCG.PreCStarDirectLimit.CompatibleState f where
  state := correctedState f omega delta hdelta hdef
  compatible i j hij a := by
    induction j, hij using Nat.le_induction with
    | base =>
        change correctedState f omega delta hdelta hdef i (f i i le_rfl a) =
          correctedState f omega delta hdelta hdef i a
        congr 1
        exact DirectedSystem.map_self (f := fun p q h => f p q h) a
    | succ j hij ih =>
        rw [← ih]
        rw [← DirectedSystem.map_map' f hij (Nat.le_succ j) a]
        exact correctedState_succ_compatible f omega delta hdelta hdef j
          (f i j hij a)

/-- Restricting an exactly compatible comparison family to an old stage
cannot enlarge its discrepancy from the original state. -/
theorem pulledStateCLM_sub_compatible_norm_le
    (omega : ∀ n, NCG.PreCStarState (A n))
    (omegaTilde : NCG.PreCStarDirectLimit.CompatibleState f)
    (m k : ℕ) :
    ‖pulledStateCLM f omega m k -
        (omegaTilde.state m).toContinuousLinearMap‖ ≤
      ‖(omega (m + k)).toContinuousLinearMap -
        (omegaTilde.state (m + k)).toContinuousLinearMap‖ := by
  let discrepancy : A (m + k) →L[ℂ] ℂ :=
    (omega (m + k)).toContinuousLinearMap -
      (omegaTilde.state (m + k)).toContinuousLinearMap
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg discrepancy)
  intro a
  have hpoint :
      (pulledStateCLM f omega m k -
          (omegaTilde.state m).toContinuousLinearMap) a =
        discrepancy (f m (m + k) (Nat.le_add_right m k) a) := by
    simp only [sub_apply, pulledStateCLM_apply, discrepancy]
    rw [omegaTilde.compatible m (m + k) (Nat.le_add_right m k) a]
  rw [hpoint]
  calc
    ‖discrepancy (f m (m + k) (Nat.le_add_right m k) a)‖
        ≤ ‖discrepancy‖ * ‖f m (m + k) (Nat.le_add_right m k) a‖ :=
      discrepancy.le_opNorm _
    _ ≤ ‖discrepancy‖ * ‖a‖ :=
      mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le _ _)
        (norm_nonneg discrepancy)

/-- Uniqueness of the correction among exactly compatible families which
track the original states asymptotically in operator norm. -/
theorem compatibleState_eq_corrected_of_tracking
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n)
    (omegaTilde : NCG.PreCStarDirectLimit.CompatibleState f)
    (htrack : Tendsto
      (fun n => ‖(omega n).toContinuousLinearMap -
        (omegaTilde.state n).toContinuousLinearMap‖)
      atTop (nhds 0)) :
    omegaTilde = compatibleCorrectedState f omega delta hdelta hdef := by
  have hstate : ∀ m,
      (omegaTilde.state m).toContinuousLinearMap =
        correctedCLM f omega delta hdelta hdef m := by
    intro m
    have htrackShift : Tendsto
        (fun k => ‖(omega (m + k)).toContinuousLinearMap -
          (omegaTilde.state (m + k)).toContinuousLinearMap‖)
        atTop (nhds 0) := by
      simpa [Function.comp_def, add_comm] using
        htrack.comp (Filter.tendsto_add_atTop_nat m)
    have hnorm : Tendsto
        (fun k => ‖pulledStateCLM f omega m k -
          (omegaTilde.state m).toContinuousLinearMap‖)
        atTop (nhds 0) :=
      squeeze_zero (fun k => norm_nonneg _)
        (fun k => pulledStateCLM_sub_compatible_norm_le f omega omegaTilde m k)
        htrackShift
    have htilde : Tendsto (pulledStateCLM f omega m) atTop
        (nhds (omegaTilde.state m).toContinuousLinearMap) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
    exact tendsto_nhds_unique htilde
      (correctedCLM_tendsto f omega delta hdelta hdef m)
  cases omegaTilde with
  | mk state compatible =>
      have hstates : state = correctedState f omega delta hdelta hdef := by
        funext m
        exact preCStarState_ext (hstate m)
      subst state
      rfl

/-- Full state and AF-limit existence package, including the exact
defect-tail estimate at every finite stage and uniqueness of the completed
extension of the corrected compatible family. -/
theorem summableInductiveStateCorrection
    (omega : ∀ n, NCG.PreCStarState (A n)) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hdef : ∀ n,
      ‖(omega (n + 1)).toContinuousLinearMap.comp
          (embeddingCLM f (Nat.le_succ n)) -
        (omega n).toContinuousLinearMap‖ ≤ delta n) :
    ∃ omegaHat : NCG.PreCStarDirectLimit.CompatibleState f,
      (∀ m,
        ‖(omegaHat.state m).toContinuousLinearMap -
            (omega m).toContinuousLinearMap‖ ≤
          ∑' k : ℕ, delta (k + m)) ∧
      ∃! Omega : NCG.PreCStarDirectLimit.Completion f →ₚ[ℂ] ℂ,
        ∀ m (a : A m),
          Omega (NCG.PreCStarDirectLimit.completionOf f m a) =
            omegaHat.state m a := by
  let omegaHat := compatibleCorrectedState f omega delta hdelta hdef
  refine ⟨omegaHat, ?_, ?_⟩
  · intro m
    exact correctedCLM_tail f omega delta hdelta hdef m
  · refine ⟨omegaHat.completionPositiveLinearMap,
      fun m a => omegaHat.completionPositiveLinearMap_of m a, ?_⟩
    intro Omega hOmega
    exact omegaHat.completionPositiveLinearMap_unique Omega hOmega

end NCG.SummableInductiveStateCorrection
