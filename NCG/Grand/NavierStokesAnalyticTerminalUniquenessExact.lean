/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Analytic terminal-zero uniqueness

This is the analytic-continuation end of the terminal Navier--Stokes argument.
Once repeated differentiation of the evolution equation has certified that
the Taylor series at the zero terminal trace is the zero formal multilinear
series, local vanishing follows from the power-series representation and the
analytic identity principle propagates it throughout the connected ancient
time interval.
-/

open Set Filter Topology

noncomputable section

namespace NCG.NavierStokesAnalyticTerminalUniqueness

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A recurrence which sends a zero initial jet and zero lower jets to a zero
next jet forces every Taylor coefficient to vanish. -/
theorem all_timeJets_zero
    (jet : ℕ → H) (hzero : jet 0 = 0)
    (hrecurrence : ∀ n, (∀ k ≤ n, jet k = 0) → jet (n + 1) = 0) :
    ∀ n, jet n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => exact hzero
      | succ n =>
          exact hrecurrence n fun k hk ↦ ih k (Nat.lt_succ_iff.mpr hk)

/-- Concrete repeated differentiation for a quadratic evolution
`u' = A u + B(u,u)`.  The displayed binomial recurrence is the Taylor-jet
form of Navier--Stokes; a zero terminal trace forces every jet to vanish. -/
theorem quadratic_evolution_timeJets_zero
    (A : H →ₗ[ℝ] H) (B : H →ₗ[ℝ] (H →ₗ[ℝ] H)) (jet : ℕ → H)
    (hzero : jet 0 = 0)
    (hjet : ∀ n,
      jet (n + 1) = A (jet n) +
        ∑ k ∈ Finset.range (n + 1),
          Nat.choose n k • B (jet k) (jet (n - k))) :
    ∀ n, jet n = 0 := by
  apply all_timeJets_zero jet hzero
  intro n hall
  rw [hjet n, hall n le_rfl]
  simp only [map_zero, zero_add]
  apply Finset.sum_eq_zero
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [hall k hkn, hall (n - k) (Nat.sub_le n k)]
  simp

/-- Banach-valued real analyticity plus a zero Taylor series at the terminal
time forces vanishing on the entire connected time domain. -/
theorem eqOn_zero_of_zero_terminal_powerSeries
    (U : ℝ → H) (timeDomain : Set ℝ)
    (hanalytic : AnalyticOnNhd ℝ U timeDomain)
    (hconnected : IsPreconnected timeDomain) (hterminal : 0 ∈ timeDomain)
    (hzeroSeries : HasFPowerSeriesAt U
      (0 : FormalMultilinearSeries ℝ ℝ H) 0) :
    EqOn U 0 timeDomain :=
  hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hconnected hterminal hzeroSeries.eventually_eq_zero

/-- The global-space specialization: a terminal zero formal series determines
an identically zero analytic ancient profile on all of real time. -/
theorem eq_zero_of_zero_terminal_powerSeries
    (U : ℝ → H) (hanalytic : AnalyticOnNhd ℝ U Set.univ)
    (hzeroSeries : HasFPowerSeriesAt U
      (0 : FormalMultilinearSeries ℝ ℝ H) 0) :
    U = 0 := by
  funext t
  exact eqOn_zero_of_zero_terminal_powerSeries U Set.univ hanalytic
    isPreconnected_univ (mem_univ 0) hzeroSeries (mem_univ t)

end NCG.NavierStokesAnalyticTerminalUniqueness
