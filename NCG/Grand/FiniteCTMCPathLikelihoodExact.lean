/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DrivenProcessExact

/-!
# Exact finite continuous-time Markov path likelihoods

This file supplies the pathwise analytic layer used by the accepted-process
theorems.  A finite trajectory consists of an initial state, a list of
holding-time/next-state pairs, and a final holding time.  Its logarithmic
cylinder density is the integrated diagonal rate plus the logarithms of the
jump rates.  For the Perron--Doob transform we prove the exact likelihood
identity, including the endpoint coboundary.

The formulation is zero-safe at the interface: ValidFor records precisely
that each traversed edge has positive reference rate.  No global
all-to-all-positivity hypothesis is imposed.
-/

open Matrix Finset

namespace NCG
namespace DrivenProcess
namespace FinitePath

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A jump is a holding time at the current state followed by the next state. -/
abbrev Jump (S : Type*) := ℝ × S

/-- The endpoint reached after following a finite jump list. -/
def endpoint (x : S) : List (Jump S) → S
  | [] => x
  | (_, y) :: rest => endpoint y rest

/-- Total elapsed time, including the last holding interval. -/
def duration (terminalHold : ℝ) : List (Jump S) → ℝ
  | [] => terminalHold
  | (hold, _) :: rest => hold + duration terminalHold rest

/-- The protected additive reward on a finite path. -/
def additiveReward (v : S → ℝ) (g : S → S → ℝ)
    (terminalHold : ℝ) (x : S) : List (Jump S) → ℝ
  | [] => terminalHold * v x
  | (hold, y) :: rest =>
      hold * v x + g x y + additiveReward v g terminalHold y rest

/-- Conditional log-density of the path after fixing its initial state. -/
noncomputable def conditionalLogLikelihood (L : Matrix S S ℝ)
    (terminalHold : ℝ) (x : S) : List (Jump S) → ℝ
  | [] => terminalHold * L x x
  | (hold, y) :: rest =>
      hold * L x x + Real.log (L x y) +
        conditionalLogLikelihood L terminalHold y rest

/-- Full logarithmic cylinder density, including the initial distribution. -/
noncomputable def logLikelihood (p : S → ℝ) (L : Matrix S S ℝ)
    (terminalHold : ℝ) (x : S) (path : List (Jump S)) : ℝ :=
  Real.log (p x) + conditionalLogLikelihood L terminalHold x path

/-- Positive cylinder density represented by its exact log-density. -/
noncomputable def likelihood (p : S → ℝ) (L : Matrix S S ℝ)
    (terminalHold : ℝ) (x : S) (path : List (Jump S)) : ℝ :=
  Real.exp (logLikelihood p L terminalHold x path)

/-- Path-specific absolute continuity: every traversed edge is a genuine
positive reference jump, and consecutive states differ. -/
def ValidFor (L : Matrix S S ℝ) (x : S) : List (Jump S) → Prop
  | [] => True
  | (_, y) :: rest => x ≠ y ∧ 0 < L x y ∧ ValidFor L y rest

/-- Total rate of leaving a state. -/
noncomputable def escapeRate (L : Matrix S S ℝ) (u : S) : ℝ :=
  ∑ w ∈ univ.erase u, L u w

theorem diagonal_eq_neg_escapeRate {L : Matrix S S ℝ}
    (hL : IsGenerator L) (u : S) :
    L u u = -escapeRate L u := by
  have hrow := hL.row_sum u
  rw [← Finset.add_sum_erase _ _ (mem_univ u)] at hrow
  unfold escapeRate
  linarith

/-- Jump-count part of the log-likelihood ratio, accumulated pathwise. -/
noncomputable def jumpLogRatio (L Ltilde : Matrix S S ℝ)
    (x : S) : List (Jump S) → ℝ
  | [] => 0
  | (_, y) :: rest =>
      Real.log (L x y / Ltilde x y) + jumpLogRatio L Ltilde y rest

/-- Integrated difference of escape rates along a resolved path. -/
noncomputable def integratedEscapeDifference
    (L Ltilde : Matrix S S ℝ) (terminalHold : ℝ)
    (x : S) : List (Jump S) → ℝ
  | [] => terminalHold * (escapeRate L x - escapeRate Ltilde x)
  | (hold, y) :: rest =>
      hold * (escapeRate L x - escapeRate Ltilde x) +
        integratedEscapeDifference L Ltilde terminalHold y rest

/-- Occupation time of a state in a resolved finite path. -/
def occupationTime (terminalHold : ℝ) (x : S)
    (path : List (Jump S)) (u : S) : ℝ :=
  match path with
  | [] => if x = u then terminalHold else 0
  | (hold, y) :: rest =>
      (if x = u then hold else 0) + occupationTime terminalHold y rest u

/-- Number of directed jumps between two states in a resolved finite path. -/
def directedJumpCount (x : S) (path : List (Jump S))
    (u w : S) : ℕ :=
  match path with
  | [] => 0
  | (_, y) :: rest =>
      (if x = u ∧ y = w then 1 else 0) +
        directedJumpCount y rest u w

/-- The finite sufficient record for a continuous-time trajectory. -/
structure TrajectoryRecord (S : Type*) where
  initial : S
  occupation : S → ℝ
  jumps : S → S → ℕ

/-- Extract the sufficient record from a resolved path. -/
def trajectoryRecord (terminalHold : ℝ) (x : S)
    (path : List (Jump S)) : TrajectoryRecord S where
  initial := x
  occupation := occupationTime terminalHold x path
  jumps := directedJumpCount x path

theorem integratedEscapeDifference_eq_occupation_sum
    (L Ltilde : Matrix S S ℝ) (terminalHold : ℝ)
    (x : S) (path : List (Jump S)) :
    integratedEscapeDifference L Ltilde terminalHold x path =
      ∑ u, occupationTime terminalHold x path u *
        (escapeRate L u - escapeRate Ltilde u) := by
  classical
  induction path generalizing x with
  | nil =>
      simp [integratedEscapeDifference, occupationTime]
  | cons step rest ih =>
      rcases step with ⟨hold, y⟩
      simp only [integratedEscapeDifference, occupationTime,
        add_mul, Finset.sum_add_distrib]
      rw [ih y]
      simp

theorem jumpLogRatio_eq_count_sum
    (L Ltilde : Matrix S S ℝ) (x : S) (path : List (Jump S)) :
    jumpLogRatio L Ltilde x path =
      ∑ u, ∑ w, (directedJumpCount x path u w : ℝ) *
        Real.log (L u w / Ltilde u w) := by
  classical
  induction path generalizing x with
  | nil => simp [jumpLogRatio, directedJumpCount]
  | cons step rest ih =>
      rcases step with ⟨hold, y⟩
      simp only [jumpLogRatio, directedJumpCount, Nat.cast_add,
        add_mul, Finset.sum_add_distrib]
      rw [ih y]
      congr 1
      symm
      calc
        (∑ u, ∑ w,
            ((if x = u ∧ y = w then 1 else 0 : ℕ) : ℝ) *
              Real.log (L u w / Ltilde u w)) =
            ∑ u, ∑ w,
            if x = u ∧ y = w then
              Real.log (L u w / Ltilde u w) else 0 := by
                apply Finset.sum_congr rfl
                intro u _
                apply Finset.sum_congr rfl
                intro w _
                split <;> simp_all
        _ =
            ∑ u, if x = u then
              Real.log (L u y / Ltilde u y) else 0 := by
                apply Finset.sum_congr rfl
                intro u _
                by_cases hxu : x = u
                · subst u
                  simp
                · simp [hxu]
        _ = Real.log (L x y / Ltilde x y) := by simp

/-- Conditional path-likelihood identity after fixing the initial state. -/
theorem conditionalLogLikelihood_sub
    (L Ltilde : Matrix S S ℝ)
    (hL : IsGenerator L) (hLtilde : IsGenerator Ltilde)
    (terminalHold : ℝ) (x : S) (path : List (Jump S))
    (hpath : ValidFor L x path)
    (hpathTilde : ValidFor Ltilde x path) :
    conditionalLogLikelihood L terminalHold x path -
      conditionalLogLikelihood Ltilde terminalHold x path =
        jumpLogRatio L Ltilde x path -
          integratedEscapeDifference L Ltilde terminalHold x path := by
  induction path generalizing x with
  | nil =>
      simp only [conditionalLogLikelihood, jumpLogRatio,
        integratedEscapeDifference]
      rw [diagonal_eq_neg_escapeRate hL,
        diagonal_eq_neg_escapeRate hLtilde]
      ring
  | cons step rest ih =>
      rcases step with ⟨hold, y⟩
      rcases hpath with ⟨hxy, hLxy, hrest⟩
      rcases hpathTilde with ⟨_, hLtildeXY, hrestTilde⟩
      simp only [conditionalLogLikelihood, jumpLogRatio,
        integratedEscapeDifference]
      have hih := ih y hrest hrestTilde
      have hdiag := diagonal_eq_neg_escapeRate hL x
      have hdiagTilde := diagonal_eq_neg_escapeRate hLtilde x
      have hlog := Real.log_div hLxy.ne' hLtildeXY.ne'
      calc
        hold * L x x + Real.log (L x y) +
              conditionalLogLikelihood L terminalHold y rest -
            (hold * Ltilde x x + Real.log (Ltilde x y) +
              conditionalLogLikelihood Ltilde terminalHold y rest) =
            (Real.log (L x y) - Real.log (Ltilde x y)) +
              (conditionalLogLikelihood L terminalHold y rest -
                conditionalLogLikelihood Ltilde terminalHold y rest) -
              hold * (escapeRate L x - escapeRate Ltilde x) := by
                rw [hdiag, hdiagTilde]
                ring
        _ = Real.log (L x y / Ltilde x y) +
              jumpLogRatio L Ltilde y rest -
            (hold * (escapeRate L x - escapeRate Ltilde x) +
              integratedEscapeDifference L Ltilde terminalHold y rest) := by
                rw [hlog, hih]
                ring

/-- General finite continuous-time path-likelihood identity for two
absolutely continuous finite generators. -/
theorem logLikelihood_sub
    (p ptilde : S → ℝ) (L Ltilde : Matrix S S ℝ)
    (hL : IsGenerator L) (hLtilde : IsGenerator Ltilde)
    (terminalHold : ℝ) (x : S) (path : List (Jump S))
    (hp : 0 < p x) (hptilde : 0 < ptilde x)
    (hpath : ValidFor L x path)
    (hpathTilde : ValidFor Ltilde x path) :
    logLikelihood p L terminalHold x path -
      logLikelihood ptilde Ltilde terminalHold x path =
        Real.log (p x / ptilde x) +
          jumpLogRatio L Ltilde x path -
          integratedEscapeDifference L Ltilde terminalHold x path := by
  unfold logLikelihood
  have hc := conditionalLogLikelihood_sub L Ltilde hL hLtilde
    terminalHold x path hpath hpathTilde
  rw [Real.log_div hp.ne' hptilde.ne']
  calc
    Real.log (p x) + conditionalLogLikelihood L terminalHold x path -
        (Real.log (ptilde x) +
          conditionalLogLikelihood Ltilde terminalHold x path) =
      (Real.log (p x) - Real.log (ptilde x)) +
        (conditionalLogLikelihood L terminalHold x path -
          conditionalLogLikelihood Ltilde terminalHold x path) := by ring
    _ = _ := by rw [hc]; ring

/-- Displayed sufficient-statistics form: the likelihood ratio depends only
on the initial state, occupation times, and directed jump counts. -/
theorem logLikelihood_sub_sufficient_record
    (p ptilde : S → ℝ) (L Ltilde : Matrix S S ℝ)
    (hL : IsGenerator L) (hLtilde : IsGenerator Ltilde)
    (terminalHold : ℝ) (x : S) (path : List (Jump S))
    (hp : 0 < p x) (hptilde : 0 < ptilde x)
    (hpath : ValidFor L x path)
    (hpathTilde : ValidFor Ltilde x path) :
    logLikelihood p L terminalHold x path -
      logLikelihood ptilde Ltilde terminalHold x path =
        Real.log (p x / ptilde x) +
          (∑ u, ∑ w,
            (directedJumpCount x path u w : ℝ) *
              Real.log (L u w / Ltilde u w)) -
          ∑ u, occupationTime terminalHold x path u *
            (escapeRate L u - escapeRate Ltilde u) := by
  rw [logLikelihood_sub p ptilde L Ltilde hL hLtilde terminalHold
      x path hp hptilde hpath hpathTilde,
    jumpLogRatio_eq_count_sum,
    integratedEscapeDifference_eq_occupation_sum]

/-- KL divergence of two finite initial distributions, in the positive-support
form used by the path theorem. -/
noncomputable def initialKL (p ptilde : S → ℝ) : ℝ :=
  ∑ u, p u * Real.log (p u / ptilde u)

/-- Instantaneous generator-relative-entropy density at one state. -/
noncomputable def generatorKLDensity
    (L Ltilde : Matrix S S ℝ) (u : S) : ℝ :=
  ∑ w ∈ univ.erase u, Phi (L u w) (Ltilde u w)

/-- Algebraic compensator identity behind the finite-horizon path-space KL
formula.  Here theta is the vector of expected occupation times; the expected
directed jump count is theta(u) times L(u,w). -/
theorem compensated_path_KL
    (p ptilde : S → ℝ) (L Ltilde : Matrix S S ℝ)
    (theta : S → ℝ) :
    initialKL p ptilde +
        (∑ u, theta u *
          ∑ w ∈ univ.erase u,
            L u w * Real.log (L u w / Ltilde u w)) -
        ∑ u, theta u * (escapeRate L u - escapeRate Ltilde u) =
      initialKL p ptilde +
        ∑ u, theta u * generatorKLDensity L Ltilde u := by
  have hpoint : ∀ u,
      theta u *
          (∑ w ∈ univ.erase u,
            L u w * Real.log (L u w / Ltilde u w)) -
        theta u * (escapeRate L u - escapeRate Ltilde u) =
      theta u * generatorKLDensity L Ltilde u := by
    intro u
    unfold generatorKLDensity escapeRate Phi
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      mul_sub, Finset.mul_sum]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  calc
    initialKL p ptilde +
          (∑ u, theta u *
            ∑ w ∈ univ.erase u,
              L u w * Real.log (L u w / Ltilde u w)) -
          ∑ u, theta u * (escapeRate L u - escapeRate Ltilde u) =
        initialKL p ptilde +
          ∑ u, (theta u *
              ∑ w ∈ univ.erase u,
                L u w * Real.log (L u w / Ltilde u w) -
            theta u * (escapeRate L u - escapeRate Ltilde u)) := by
              rw [Finset.sum_sub_distrib]
              ring
    _ = initialKL p ptilde +
        ∑ u, theta u * generatorKLDensity L Ltilde u := by
          apply congrArg (fun z => initialKL p ptilde + z)
          apply Finset.sum_congr rfl
          intro u _
          exact hpoint u

/-- Nonnegativity of the dynamic KL contribution under absolute continuity. -/
theorem generatorKLDensity_nonneg
    (L Ltilde : Matrix S S ℝ) (u : S)
    (hL : ∀ w, w ≠ u → 0 ≤ L u w)
    (hLtilde : ∀ w, w ≠ u → 0 ≤ Ltilde u w)
    (hAC : ∀ w, w ≠ u → Ltilde u w = 0 → L u w = 0) :
    0 ≤ generatorKLDensity L Ltilde u := by
  unfold generatorKLDensity
  exact Finset.sum_nonneg fun w hw =>
    Phi_nonneg
      (hL w (Finset.ne_of_mem_erase hw))
      (hLtilde w (Finset.ne_of_mem_erase hw))
      (hAC w (Finset.ne_of_mem_erase hw))

/-- The finite-horizon path KL term is nonnegative when occupation times are
nonnegative and the reference generator dominates the path support. -/
theorem integrated_generator_KL_nonneg
    (L Ltilde : Matrix S S ℝ) (theta : S → ℝ)
    (htheta : ∀ u, 0 ≤ theta u)
    (hL : IsGenerator L) (hLtilde : IsGenerator Ltilde)
    (hAC : ∀ u w, u ≠ w → Ltilde u w = 0 → L u w = 0) :
    0 ≤ ∑ u, theta u * generatorKLDensity L Ltilde u :=
  Finset.sum_nonneg fun u _ =>
    mul_nonneg (htheta u)
      (generatorKLDensity_nonneg L Ltilde u
        (fun w hwu => hL.offDiag_nonneg u w hwu.symm)
        (fun w hwu => hLtilde.offDiag_nonneg u w hwu.symm)
        (fun w hwu => hAC u w hwu.symm))

/-- Coherent two-generator certificate for finite continuous-time trajectory
likelihoods and their compensated KL divergence. -/
structure FiniteCTMCPathLikelihoodCertificate
    (L Ltilde : Matrix S S ℝ)
    (hL : IsGenerator L) (hLtilde : IsGenerator Ltilde) : Prop where
  pathLogRadonNikodym :
    ∀ (p ptilde : S → ℝ) (terminalHold : ℝ) (x : S)
      (path : List (Jump S)),
      0 < p x → 0 < ptilde x →
      ValidFor L x path → ValidFor Ltilde x path →
      logLikelihood p L terminalHold x path -
        logLikelihood ptilde Ltilde terminalHold x path =
          Real.log (p x / ptilde x) +
            (∑ u, ∑ w,
              (directedJumpCount x path u w : ℝ) *
                Real.log (L u w / Ltilde u w)) -
            ∑ u, occupationTime terminalHold x path u *
              (escapeRate L u - escapeRate Ltilde u)
  compensatedKL :
    ∀ (p ptilde theta : S → ℝ),
      initialKL p ptilde +
          (∑ u, theta u *
            ∑ w ∈ univ.erase u,
              L u w * Real.log (L u w / Ltilde u w)) -
          ∑ u, theta u * (escapeRate L u - escapeRate Ltilde u) =
        initialKL p ptilde +
          ∑ u, theta u * generatorKLDensity L Ltilde u
  dynamicKLNonnegative :
    ∀ (theta : S → ℝ), (∀ u, 0 ≤ theta u) →
      (∀ u w, u ≠ w → Ltilde u w = 0 → L u w = 0) →
      0 ≤ ∑ u, theta u * generatorKLDensity L Ltilde u

/-- Finite continuous-time path likelihood and KL compiler. -/
theorem finite_continuous_time_path_likelihood
    (L Ltilde : Matrix S S ℝ)
    (hL : IsGenerator L) (hLtilde : IsGenerator Ltilde) :
    FiniteCTMCPathLikelihoodCertificate L Ltilde hL hLtilde where
  pathLogRadonNikodym :=
    fun p ptilde terminalHold x path hp hptilde hpath hpathTilde =>
      logLikelihood_sub_sufficient_record p ptilde L Ltilde hL hLtilde
        terminalHold x path hp hptilde hpath hpathTilde
  compensatedKL := fun p ptilde theta =>
    compensated_path_KL p ptilde L Ltilde theta
  dynamicKLNonnegative := fun theta htheta hAC =>
    integrated_generator_KL_nonneg L Ltilde theta htheta hL hLtilde hAC

theorem driven_diagonal
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (k : ℝ) (r : S → ℝ) (psi : ℝ) (hr : ∀ u, 0 < r u) (u : S) :
    drivenGen L v g k r psi u u = L u u + k * v u - psi := by
  rw [drivenGen, driven_apply_self, tilt_apply_self]
  field_simp [(hr u).ne']

theorem log_driven_jump
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (k : ℝ) (r : S → ℝ) (psi : ℝ) (hr : ∀ u, 0 < r u)
    {u w : S} (huw : u ≠ w) (hL : 0 < L u w) :
    Real.log (drivenGen L v g k r psi u w) - Real.log (L u w) =
      k * g u w + Real.log (r w) - Real.log (r u) := by
  rw [drivenGen, driven_apply_ne _ _ _ huw, tilt_apply_ne _ _ _ _ huw]
  have hru : (r u)⁻¹ ≠ 0 := inv_ne_zero (hr u).ne'
  have hLexp : L u w * Real.exp (k * g u w) ≠ 0 :=
    mul_ne_zero hL.ne' (Real.exp_ne_zero _)
  rw [Real.log_mul (mul_ne_zero hru hLexp) (hr w).ne',
    Real.log_mul hru hLexp, Real.log_mul hL.ne' (Real.exp_ne_zero _),
    Real.log_exp, Real.log_inv]
  ring

/-- Exact pathwise log Radon--Nikodym identity for the Perron--Doob
transform.  The terminal logarithm is the telescoping endpoint coboundary. -/
theorem conditionalLogLikelihood_driven_sub
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (k : ℝ) (r : S → ℝ) (psi terminalHold : ℝ)
    (hr : ∀ u, 0 < r u) (x : S) (path : List (Jump S))
    (hpath : ValidFor L x path) :
    conditionalLogLikelihood (drivenGen L v g k r psi)
        terminalHold x path -
      conditionalLogLikelihood L terminalHold x path =
        k * additiveReward v g terminalHold x path -
          psi * duration terminalHold path +
          Real.log (r (endpoint x path)) - Real.log (r x) := by
  induction path generalizing x with
  | nil =>
      simp only [conditionalLogLikelihood, additiveReward, duration, endpoint]
      rw [driven_diagonal L v g k r psi hr x]
      ring
  | cons step rest ih =>
      rcases step with ⟨hold, y⟩
      rcases hpath with ⟨hxy, hLxy, hrest⟩
      simp only [conditionalLogLikelihood, additiveReward, duration, endpoint]
      have hih := ih y hrest
      have hdiag := driven_diagonal L v g k r psi hr x
      have hjump := log_driven_jump L v g k r psi hr hxy hLxy
      calc
        hold * drivenGen L v g k r psi x x +
              Real.log (drivenGen L v g k r psi x y) +
              conditionalLogLikelihood (drivenGen L v g k r psi)
                terminalHold y rest -
            (hold * L x x + Real.log (L x y) +
              conditionalLogLikelihood L terminalHold y rest) =
            hold * (k * v x - psi) +
              (Real.log (drivenGen L v g k r psi x y) - Real.log (L x y)) +
              (conditionalLogLikelihood (drivenGen L v g k r psi)
                terminalHold y rest -
                conditionalLogLikelihood L terminalHold y rest) := by
                  rw [hdiag]
                  ring
        _ = k * (hold * v x + g x y +
              additiveReward v g terminalHold y rest) -
            psi * (hold + duration terminalHold rest) +
            Real.log (r (endpoint y rest)) - Real.log (r x) := by
              rw [hjump, hih]
              ring

/-- Full log-likelihood identity.  The common initial distribution cancels. -/
theorem logLikelihood_driven_sub
    (p : S → ℝ) (L : Matrix S S ℝ) (v : S → ℝ)
    (g : S → S → ℝ) (k : ℝ) (r : S → ℝ) (psi terminalHold : ℝ)
    (hr : ∀ u, 0 < r u) (x : S) (path : List (Jump S))
    (hpath : ValidFor L x path) :
    logLikelihood p (drivenGen L v g k r psi) terminalHold x path -
      logLikelihood p L terminalHold x path =
        k * additiveReward v g terminalHold x path -
          psi * duration terminalHold path +
          Real.log (r (endpoint x path)) - Real.log (r x) := by
  unfold logLikelihood
  have h := conditionalLogLikelihood_driven_sub
    L v g k r psi terminalHold hr x path hpath
  calc
    Real.log (p x) +
          conditionalLogLikelihood (drivenGen L v g k r psi)
            terminalHold x path -
        (Real.log (p x) + conditionalLogLikelihood L terminalHold x path) =
      conditionalLogLikelihood (drivenGen L v g k r psi)
          terminalHold x path -
        conditionalLogLikelihood L terminalHold x path := by ring
    _ = _ := h

/-- Exact likelihood-ratio form of the finite-path
Radon--Nikodym derivative. -/
theorem likelihood_driven_div
    (p : S → ℝ) (L : Matrix S S ℝ) (v : S → ℝ)
    (g : S → S → ℝ) (k : ℝ) (r : S → ℝ) (psi terminalHold : ℝ)
    (hr : ∀ u, 0 < r u) (x : S) (path : List (Jump S))
    (hpath : ValidFor L x path) :
    likelihood p (drivenGen L v g k r psi) terminalHold x path /
      likelihood p L terminalHold x path =
        Real.exp
          (k * additiveReward v g terminalHold x path -
            psi * duration terminalHold path) *
          (r (endpoint x path) / r x) := by
  unfold likelihood
  rw [← Real.exp_sub,
    logLikelihood_driven_sub p L v g k r psi terminalHold hr x path hpath]
  rw [show
      k * additiveReward v g terminalHold x path -
          psi * duration terminalHold path +
          Real.log (r (endpoint x path)) - Real.log (r x) =
        (k * additiveReward v g terminalHold x path -
          psi * duration terminalHold path) +
          (Real.log (r (endpoint x path)) - Real.log (r x)) by ring,
    Real.exp_add]
  congr 1
  rw [Real.exp_sub, Real.exp_log (hr (endpoint x path)),
    Real.exp_log (hr x)]

end FinitePath

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Coherent certificate for the finite Perron--Doob process.  Unlike the
earlier algebraic bundle, this certificate contains the exact cylinder-density
Radon--Nikodym identity on every admissible finite trajectory. -/
structure AcceptedDrivenPathCertificate
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (k : ℝ) (r ell : S → ℝ) (psi : ℝ) : Prop where
  generator : IsGenerator (drivenGen L v g k r psi)
  sameSupport :
    ∀ u w, u ≠ w →
      (0 < drivenGen L v g k r psi u w ↔ 0 < L u w)
  stationarity :
    (stationary r ell) ᵥ* drivenGen L v g k r psi = 0
  stationaryPositive : ∀ u, 0 < stationary r ell u
  stationaryNormalized : ∑ u, stationary r ell u = 1
  finitePathRadonNikodym :
    ∀ (p : S → ℝ) (terminalHold : ℝ) (x : S)
      (path : List (FinitePath.Jump S)),
      FinitePath.ValidFor L x path →
      FinitePath.likelihood p (drivenGen L v g k r psi)
          terminalHold x path /
        FinitePath.likelihood p L terminalHold x path =
          Real.exp
            (k * FinitePath.additiveReward v g terminalHold x path -
              psi * FinitePath.duration terminalHold path) *
            (r (FinitePath.endpoint x path) / r x)
  shiftedTilt :
    ∀ q, tilt (drivenGen L v g k r psi) v g q =
      driven (tilt L v g (k + q)) r psi
  shiftedPerron :
    ∀ q (r' ell' : S → ℝ) (psi' : ℝ),
      (tilt L v g (k + q)) *ᵥ r' = psi' • r' →
      ell' ᵥ* (tilt L v g (k + q)) = psi' • ell' →
      (tilt (drivenGen L v g k r psi) v g q) *ᵥ
          (fun u => (r u)⁻¹ * r' u) =
            (psi' - psi) • (fun u => (r u)⁻¹ * r' u) ∧
        (fun u => ell' u * r u) ᵥ*
            tilt (drivenGen L v g k r psi) v g q =
          (psi' - psi) • (fun u => ell' u * r u)
  entropyOptimal :
    ∀ (K : Matrix S S ℝ), IsGenerator K →
      (∀ u w, u ≠ w → L u w = 0 → K u w = 0) →
      ∀ nu : S → ℝ, (∀ u, 0 ≤ nu u) → ∑ u, nu u = 1 →
        nu ᵥ* K = 0 →
        entropyRate nu K L - k * rewardRate nu K v g + psi =
            entropyRate nu K (drivenGen L v g k r psi) ∧
          0 ≤ entropyRate nu K (drivenGen L v g k r psi)

/-- Perron--Doob driven process with exact finite-path likelihood and
entropy-optimal control. -/
theorem accepted_driven_process_with_path_likelihood
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (k : ℝ) (r ell : S → ℝ) (psi : ℝ)
    (hL : IsGenerator L) (hr : ∀ u, 0 < r u)
    (hell : ∀ u, 0 < ell u)
    (hright : (tilt L v g k) *ᵥ r = psi • r)
    (hleft : ell ᵥ* (tilt L v g k) = psi • ell)
    (hnorm : ∑ u, ell u * r u = 1) :
    AcceptedDrivenPathCertificate L v g k r ell psi := by
  rcases accepted_driven_process L v g k r psi hL ell hr hell
      hright hleft hnorm with
    ⟨hgen, hsupp, hstat, hpositive, hnormalized, hshift,
      hshiftedPerron, hcontrol⟩
  exact {
    generator := hgen
    sameSupport := hsupp
    stationarity := hstat
    stationaryPositive := hpositive
    stationaryNormalized := hnormalized
    finitePathRadonNikodym := fun p terminalHold x path hpath =>
      FinitePath.likelihood_driven_div p L v g k r psi terminalHold
        hr x path hpath
    shiftedTilt := hshift
    shiftedPerron := hshiftedPerron
    entropyOptimal := hcontrol }

end DrivenProcess
end NCG
