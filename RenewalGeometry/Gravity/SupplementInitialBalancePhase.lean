/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.SupplementInitialBalanceExact
import RenewalGeometry.DiscreteAnalysis.OddPhaseDerivativeReal

/-!
# The four-mode mean calibration with the actual odd phase derivative
  (`lem:supp-initial-balance`, `eq:supp-initial-phase-derivative`, `eq:supp-initial-seed`,
  `eq:supp-initial-quadratic-mean`; emergent-spacetime manuscript)

`Gravity/SupplementInitialBalanceExact.lean` computes the mean jet `Q_h(ϑ)` of the displayed
quadratic Hamiltonian `ℋ_h^{[2]}` on the seed `u_* = Σ_i T_i cos(2π x_i)` *under the hypothesis*
`δ_i u_* = -ω sin(2π x_i) T_i` with `ω` a free real.  Here the hypothesis is discharged for the
paper's odd phase derivative (`eq:supp-initial-phase-derivative`, encoded as the real Fourier
multiplier `OddPhaseDerivativeReal.pd`, equal to the complex encoding
`InitialConstraintLinearRange.delta`), with `ω = ω_h = 2h⁻¹ sin(πh)` (`OddPhaseDerivativeReal.omega`):

* `phaseDerivFin`: `δ_i` transported to the `Fin N`-indexed grid of the balance file;
* `phaseDerivFin_uStar`: `δ_i u_* = -ω_h sin(2π x_i) T_i` (odd `N ≥ 3`);
* `meanJet_seed_phase`: `eq:supp-initial-quadratic-mean` for the actual `δ_i`:
  `Q_h(ϑ) = (⅔κ² - ½Σ_i b_i² - ⅜ω_h², -½ω_h b_1, -½ω_h b_2, -½ω_h b_3)`.
-/

open Finset Real

noncomputable section

namespace RenewalGeometry.InitialBalancePhase

open InitialBalance OddPhaseDerivativeReal

variable {N : ℕ} [NeZero N]

/-- The `ZMod N`-grid point of a `Fin N`-grid point. -/
def toZ (x : InitialBalance.Grid N) : PeriodicGridSobolev.Grid N := fun j => ZMod.finEquiv N (x j)

/-- The `Fin N`-grid point of a `ZMod N`-grid point. -/
def toF (z : PeriodicGridSobolev.Grid N) : InitialBalance.Grid N :=
  fun j => (ZMod.finEquiv N).symm (z j)

theorem val_finEquiv (a : Fin N) : (ZMod.finEquiv N a).val = (a : ℕ) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := NeZero.pos N; omega⟩
  rfl

theorem coe_finEquiv_symm (z : ZMod N) : (((ZMod.finEquiv N).symm z : Fin N) : ℕ) = z.val := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := NeZero.pos N; omega⟩
  rfl

/-- The odd phase derivative `δ_i` (`eq:supp-initial-phase-derivative`) acting on the
`Fin N`-indexed `Sym₃`-valued fields of the balance file. -/
def phaseDerivFin (i : Fin 3) (u : InitialBalance.Grid N → Matrix (Fin 3) (Fin 3) ℝ) :
    InitialBalance.Grid N → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x => pd i (fun z => u (toF z)) (toZ x)

/-- `δ_i u_* = -ω_h sin(2π x_i) T_i` for the actual odd phase derivative (odd `N ≥ 3`). -/
theorem phaseDerivFin_uStar (hN : Odd N) (h3 : 3 ≤ N) (i : Fin 3) :
    phaseDerivFin i (uStar N) = fun x => (-(omega N * sinMode N i x)) • T i := by
  funext x
  have hcos : ∀ k (z : PeriodicGridSobolev.Grid N),
      cosMode N k (toF z) = Real.cos (2 * π * (z k).val / N) := by
    intro k z; simp [cosMode, toF, coe_finEquiv_symm]
  have hu : (fun z => uStar N (toF z)) =
      ∑ k, fun z => Real.cos (2 * π * (z k).val / N) • T k := by
    funext z; simp [uStar, hcos, Finset.sum_apply]
  have hk : ∀ k, pd i (fun z : PeriodicGridSobolev.Grid N =>
      Real.cos (2 * π * (z k).val / N) • T k) =
      fun z => pd i (fun z : PeriodicGridSobolev.Grid N => Real.cos (2 * π * (z k).val / N)) z •
        T k := by
    intro k
    exact pd_map i ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (T k)) _
  unfold phaseDerivFin
  rw [hu, map_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · rw [hk, pd_cos hN h3]
    simp [sinMode, toZ, val_finEquiv]
  · intro k _ hki
    rw [hk]
    have h0 := pd_of_ne (N := N) (Ne.symm hki) (fun a : ZMod N => Real.cos (2 * π * a.val / N))
    beta_reduce at h0
    rw [h0]
    simp only [Pi.zero_apply, zero_smul]
  · simp

/-- **`eq:supp-initial-quadratic-mean` for the actual odd phase derivative**: on the seed
`(u_*, p(ϑ))`, the mean jet of `ℋ_h^{[2]}` with `δ_i` the paper's odd phase derivative is
`Q_h(ϑ) = (⅔κ² - ½Σb_i² - ⅜ω_h², -½ω_h b)`, `ω_h = 2h⁻¹ sin(πh)`. -/
theorem meanJet_seed_phase (hN : Odd N) (h3 : 3 ≤ N) (κ : ℝ) (b : Fin 3 → ℝ) :
    meanJet N phaseDerivFin (uStar N) (pSeed N κ b) =
      (2 / 3 * κ ^ 2 - 1 / 2 * ∑ i, b i ^ 2 - 3 / 8 * omega N ^ 2,
        fun i => -(omega N / 2) * b i) :=
  meanJet_seed N κ (omega N) b h3 phaseDerivFin (phaseDerivFin_uStar hN h3)

end RenewalGeometry.InitialBalancePhase
