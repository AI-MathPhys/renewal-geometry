/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CovariantFourierStackResolventConvergence
import NCG.Grand.FiniteTorusCenteredFrequencyWindow
import NCG.Grand.FiniteConnectionExponentialBound
import NCG.Grand.L2BlockDiagonalScreenConvergence

/-!
# Finite-torus covariant resolvents on the integer coefficient carrier

The centered finite-torus modes are extended by zero to the common carrier
`ℓ²(d → ℤ, E)`.  The resulting finite-stage covariant resolvents converge in
operator norm to the continuum Fourier multiplier.  This is the complete
low-frequency plus coercive-tail assembly on coefficient space.
-/

open Filter Topology
open scoped InnerProduct lp

noncomputable section

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Nontrivial E]

/-- The finite-stage resolver block, extended by zero away from the centered
frequency window. -/
def finiteTorusCovariantResolverBlock
    (N : ℕ) (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam)
    (k : d → ℤ) : E →L[ℂ] E :=
  if k ∈ finiteTorusCenteredFrequencyWindow (d := d) N then
    VaryingHilbert.boundedOperatorNormalResolvent
      (meshCovariantFourierOperatorStack (finiteTorusCutoffMesh N) k B)
      lam hlam
  else 0

/-- The continuum covariant resolver block at one integer Fourier mode. -/
def continuumCovariantResolverBlock
    (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam)
    (k : d → ℤ) : E →L[ℂ] E :=
  VaryingHilbert.boundedOperatorNormalResolvent
    (continuumCovariantFourierOperatorStack k B) lam hlam

theorem finiteTorusCovariantResolverBlock_opNorm_le_inv
    (N : ℕ) (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam)
    (k : d → ℤ) :
    ‖finiteTorusCovariantResolverBlock N B lam hlam k‖ ≤ 1 / lam := by
  by_cases hk : k ∈ finiteTorusCenteredFrequencyWindow (d := d) N
  · rw [finiteTorusCovariantResolverBlock, if_pos hk]
    exact VaryingHilbert.boundedOperatorNormalResolvent_opNorm_le_inv _ lam hlam
  · rw [finiteTorusCovariantResolverBlock, if_neg hk, norm_zero]
    positivity

theorem continuumCovariantResolverBlock_opNorm_le_inv
    (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam)
    (k : d → ℤ) :
    ‖continuumCovariantResolverBlock B lam hlam k‖ ≤ 1 / lam :=
  VaryingHilbert.boundedOperatorNormalResolvent_opNorm_le_inv _ lam hlam

theorem finiteTorusCovariantResolverBlock_norm_apply_le_inv
    (N : ℕ) (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam)
    (k : d → ℤ) (x : E) :
    ‖finiteTorusCovariantResolverBlock N B lam hlam k x‖ ≤
      (1 / lam) * ‖x‖ :=
  (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right
      (finiteTorusCovariantResolverBlock_opNorm_le_inv N B lam hlam k)
      (norm_nonneg x))

theorem continuumCovariantResolverBlock_norm_apply_le_inv
    (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam)
    (k : d → ℤ) (x : E) :
    ‖continuumCovariantResolverBlock B lam hlam k x‖ ≤
      (1 / lam) * ‖x‖ :=
  (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right
      (continuumCovariantResolverBlock_opNorm_le_inv B lam hlam k)
      (norm_nonneg x))

/-- Finite-stage covariant resolver on the common integer coefficient
carrier. -/
def finiteTorusCovariantCoefficientResolver
    (N : ℕ) (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam) :
    ℓ²(d → ℤ, E) →L[ℂ] ℓ²(d → ℤ, E) :=
  l2BlockDiagonal
    (finiteTorusCovariantResolverBlock N B lam hlam)
    (1 / lam) (by positivity)
    (finiteTorusCovariantResolverBlock_norm_apply_le_inv N B lam hlam)

/-- Continuum covariant resolver on the integer coefficient carrier. -/
def continuumCovariantCoefficientResolver
    (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam) :
    ℓ²(d → ℤ, E) →L[ℂ] ℓ²(d → ℤ, E) :=
  l2BlockDiagonal
    (continuumCovariantResolverBlock B lam hlam)
    (1 / lam) (by positivity)
    (continuumCovariantResolverBlock_norm_apply_le_inv B lam hlam)

theorem finiteTorusCovariantCoefficientResolver_isL2BlockDiagonal
    (N : ℕ) (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam) :
    IsL2BlockDiagonal
      (finiteTorusCovariantCoefficientResolver N B lam hlam)
      (finiteTorusCovariantResolverBlock N B lam hlam) := by
  intro f k
  rfl

theorem continuumCovariantCoefficientResolver_isL2BlockDiagonal
    (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam) :
    IsL2BlockDiagonal
      (continuumCovariantCoefficientResolver B lam hlam)
      (continuumCovariantResolverBlock B lam hlam) := by
  intro f k
  rfl

/-- A single integer radius can meet both connection thresholds and make the
canonical radius-squared resolver tail arbitrarily small. -/
theorem exists_covariantResolverTailRadius
    (lam M ε : ℝ) (hlam : 0 < lam) (hε : 0 < ε) :
    ∃ R : ℕ,
      M ≤ 3 * (R : ℝ) ∧ M ≤ 5 * (R : ℝ) ∧
      1 / (lam + integerFourierCoercivityFloor R) < ε := by
  have hthree : Tendsto (fun R : ℕ ↦ 3 * (R : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hfive : Tendsto (fun R : ℕ ↦ 5 * (R : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hdenom :
      Tendsto (fun R : ℕ ↦ lam + integerFourierCoercivityFloor R)
        atTop atTop :=
    Filter.tendsto_atTop_add_const_left atTop lam
      tendsto_integerFourierCoercivityFloor_atTop
  have hinv :
      Tendsto (fun R : ℕ ↦ 1 / (lam + integerFourierCoercivityFloor R))
        atTop (𝓝 0) := by
    have hinv' : Tendsto (fun R : ℕ ↦
        (lam + integerFourierCoercivityFloor R)⁻¹) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp hdenom).congr'
        (Eventually.of_forall fun _ ↦ rfl)
    exact hinv'.congr'
      (Eventually.of_forall fun R ↦ by simp only [one_div])
  obtain ⟨R, h3, h5, hsmall⟩ :=
    ((hthree.eventually_ge_atTop M).and
      ((hfive.eventually_ge_atTop M).and
        (hinv.eventually (Iio_mem_nhds hε)))).exists
  exact ⟨R, h3, h5, hsmall⟩

/-- Full coefficient-space norm-resolvent convergence.  The finite-stage
connection bound is stated in the exact form needed by the phase-chord
estimate; for a fixed finite family `B` it follows automatically from
`h_N → 0` after choosing `M` strictly above `max_j ‖B_j‖`. -/
theorem finiteTorusCovariantCoefficientResolver_tendsto_of_connectionBounds
    (B : d → E →L[ℂ] E) (lam M : ℝ) (hlam : 0 < lam)
    (hreal : ∀ (r : ℝ) (T : E →L[ℂ] E), r • T = (r : ℂ) • T)
    (hlimitConnection : ∀ j, ‖B j‖ ≤ M)
    (hstageConnection : ∀ᶠ N : ℕ in atTop, ∀ j,
      ‖B j‖ * Real.exp (finiteTorusCutoffMesh N * ‖B j‖) ≤ M) :
    Tendsto
      (fun N ↦ finiteTorusCovariantCoefficientResolver N B lam hlam)
      atTop
      (𝓝 (continuumCovariantCoefficientResolver B lam hlam)) := by
  apply tendsto_l2BlockDiagonal_of_finiteScreens_eventualTails
    (fun N ↦ finiteTorusCovariantCoefficientResolver N B lam hlam)
    (continuumCovariantCoefficientResolver B lam hlam)
    (fun N ↦ finiteTorusCovariantResolverBlock N B lam hlam)
    (continuumCovariantResolverBlock B lam hlam)
    (integerFourierBox (d := d))
  · intro N
    exact finiteTorusCovariantCoefficientResolver_isL2BlockDiagonal
      (N := N) (B := B) (lam := lam) hlam
  · exact continuumCovariantCoefficientResolver_isL2BlockDiagonal
      (B := B) (lam := lam) hlam
  · intro R ε hε
    filter_upwards
        [eventually_integerFourierBox_subset_finiteTorusCenteredFrequencyWindow
          (d := d) R,
          eventually_forall_mem_finset_meshStack_resolvents_close
            (integerFourierBox (d := d) R) B lam hlam hε]
        with N hwindow hclose k hk
    rw [finiteTorusCovariantResolverBlock,
      if_pos (hwindow hk), continuumCovariantResolverBlock]
    exact hclose k hk
  · intro ε hε
    obtain ⟨R, hthreshold3, hthreshold5, hsmall⟩ :=
      exists_covariantResolverTailRadius lam M ε hlam hε
    refine ⟨R, ?_, ?_⟩
    · filter_upwards [hstageConnection] with N hconnection k hk
      by_cases hwindow :
          k ∈ finiteTorusCenteredFrequencyWindow (d := d) N
      · rw [finiteTorusCovariantResolverBlock, if_pos hwindow]
        exact (meshCovariantFourierOperatorStack_resolvent_opNorm_le
          (finiteTorusCutoffMesh N) R M k B lam
          (by unfold finiteTorusCutoffMesh; positivity) hk hlam
          (mem_finiteTorusCenteredFrequencyWindow_nyquist N hwindow)
          hconnection hthreshold3 hreal).trans_lt hsmall
      · rw [finiteTorusCovariantResolverBlock, if_neg hwindow, norm_zero]
        exact hε
    · intro k hk
      exact (continuumCovariantFourierOperatorStack_resolvent_opNorm_le
        R M k B lam hk hlam hlimitConnection hthreshold5).trans_lt hsmall

/-- Unconditional coefficient-space norm-resolvent convergence for every
fixed finite family of bounded connection operators. -/
theorem finiteTorusCovariantCoefficientResolver_tendsto
    (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam) :
    Tendsto
      (fun N ↦ finiteTorusCovariantCoefficientResolver N B lam hlam)
      atTop
      (𝓝 (continuumCovariantCoefficientResolver B lam hlam)) := by
  apply finiteTorusCovariantCoefficientResolver_tendsto_of_connectionBounds
    B lam (finiteConnectionNormEnvelope B) hlam
  · intro r T
    rfl
  · exact norm_le_finiteConnectionNormEnvelope B
  · exact eventually_connectionExp_le_finiteConnectionNormEnvelope B


end NCG
