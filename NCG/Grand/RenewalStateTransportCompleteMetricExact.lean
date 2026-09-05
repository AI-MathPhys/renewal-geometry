/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StateTransport
import NCG.Grand.SummableCorrections
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Complete-metric renewal state transport

Banach fixed-point form of `thm:renewal-state-transport`, valid on the
complete state space of any finite unital C*-algebra.
-/

open Filter Function
open scoped NNReal Topology

namespace NCG
namespace RenewalStateTransportCompleteMetric

variable {X Y : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
  [MetricSpace Y] [CompleteSpace Y] [Nonempty Y]

noncomputable def stationaryState (T : X → X) (K : ℝ≥0)
    (hT : ContractingWith K T) : X :=
  hT.fixedPoint T

theorem stationaryState_isFixed (T : X → X) (K : ℝ≥0)
    (hT : ContractingWith K T) :
    T (stationaryState T K hT) = stationaryState T K hT :=
  hT.fixedPoint_isFixedPt

theorem stationaryState_unique (T : X → X) (K : ℝ≥0)
    (hT : ContractingWith K T) {x : X} (hx : T x = x) :
    x = stationaryState T K hT :=
  hT.fixedPoint_unique hx

theorem stationaryState_cutoff_bound
    (TX : X → X) (TY : Y → Y) (J : Y → X)
    (KX KY : ℝ≥0) (hTX : ContractingWith KX TX)
    (hTY : ContractingWith KY TY) (delta : ℝ)
    (hdefect : ∀ y : Y, dist (J (TY y)) (TX (J y)) ≤ delta) :
    dist (J (stationaryState TY KY hTY))
        (stationaryState TX KX hTX)
      ≤ delta / (1 - (KX : ℝ)) := by
  let ystar := stationaryState TY KY hTY
  have hy : TY ystar = ystar := stationaryState_isFixed TY KY hTY
  calc
    dist (J ystar) (stationaryState TX KX hTX)
        ≤ dist (J ystar) (TX (J ystar)) / (1 - (KX : ℝ)) :=
      hTX.dist_le_of_fixedPoint (J ystar) hTX.fixedPoint_isFixedPt
    _ ≤ delta / (1 - (KX : ℝ)) := by
      apply (div_le_div_iff_of_pos_right hTX.one_sub_K_pos).2
      simpa [hy] using hdefect ystar

theorem stationaryState_cutoff_exact
    (TX : X → X) (TY : Y → Y) (J : Y → X)
    (KX KY : ℝ≥0) (hTX : ContractingWith KX TX)
    (hTY : ContractingWith KY TY)
    (hintertwine : ∀ y : Y, J (TY y) = TX (J y)) :
    J (stationaryState TY KY hTY) = stationaryState TX KX hTX := by
  have hbound := stationaryState_cutoff_bound TX TY J KX KY hTX hTY 0
    (fun y => by rw [hintertwine y, dist_self])
  exact dist_eq_zero.mp (le_antisymm (by simpa using hbound) dist_nonneg)

variable {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]

theorem stationaryChain_limit
    (T : ℕ → V → V) (K : ℕ → ℝ≥0) (omega : ℕ → V)
    (delta : ℕ → ℝ)
    (hT : ∀ n, ContractingWith (K n) (T n))
    (hfix : ∀ n, T n (omega n) = omega n)
    (hdefect : ∀ n, dist (omega (n + 1)) (T n (omega (n + 1))) ≤ delta n)
    (hsum : Summable fun n => delta n / (1 - (K n : ℝ))) :
    ∃ omegaInf : V, Tendsto omega atTop (𝓝 omegaInf)
      ∧ ∀ m : ℕ, ‖omegaInf - omega m‖ ≤
        ∑' n : ℕ, delta (n + m) / (1 - (K (n + m) : ℝ)) := by
  apply summable_state_correction omega
    (fun n => delta n / (1 - (K n : ℝ))) hsum
  intro n
  rw [← dist_eq_norm]
  exact ((hT n).dist_le_of_fixedPoint (omega (n + 1)) (hfix n)).trans
    ((div_le_div_iff_of_pos_right (hT n).one_sub_K_pos).2 (hdefect n))

/-- A quantitative dense-cycle form of
`1 - exp (-x) = x + O(x^2)`: on `0 ≤ x ≤ 1`, the gap is at least `x/2`. -/
theorem half_le_one_sub_exp_neg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hbase : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hden : 0 < 1 + x := by linarith
  have hinv : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) hden).mpr hbase
  have hfrac : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    calc
      x / (1 + x) = 1 - (1 + x)⁻¹ := by
        field_simp
        ring
      _ ≤ 1 - (Real.exp x)⁻¹ := sub_le_sub_left hinv 1
      _ = 1 - Real.exp (-x) := by rw [Real.exp_neg]
  calc
    x / 2 ≤ x / (1 + x) :=
      div_le_div_of_nonneg_left hx0 hden (by linarith)
    _ ≤ 1 - Real.exp (-x) := hfrac

/-- In the dense branch `K ≤ exp (-lambda*tau)`, the sharp stationary
transport error is bounded by `(2/lambda) * (delta/tau)`. -/
theorem denseBranch_stationaryError_le
    (K : ℝ≥0) (lambda tau delta : ℝ)
    (hK : (K : ℝ) ≤ Real.exp (-lambda * tau))
    (hlambda : 0 < lambda) (htau : 0 < tau)
    (hsmall : lambda * tau ≤ 1) (hdelta : 0 ≤ delta) :
    delta / (1 - (K : ℝ)) ≤
      (2 / lambda) * (delta / tau) := by
  have hx0 : 0 ≤ lambda * tau := mul_nonneg hlambda.le htau.le
  have hgap : lambda * tau / 2 ≤ 1 - Real.exp (-lambda * tau) :=
    by simpa only [neg_mul] using half_le_one_sub_exp_neg hx0 hsmall
  have hden : lambda * tau / 2 ≤ 1 - (K : ℝ) := by linarith
  have hhalf : 0 < lambda * tau / 2 := by positivity
  calc
    delta / (1 - (K : ℝ)) ≤ delta / (lambda * tau / 2) :=
      div_le_div_of_nonneg_left hdelta hhalf hden
    _ = (2 / lambda) * (delta / tau) := by field_simp

/-- The manuscript's summability criterion
`sum delta/tau < infinity` implies summability of the actual stationary
transport errors in the dense branch. -/
theorem denseBranch_stationaryErrors_summable
    (K : ℕ → ℝ≥0) (lambda : ℝ) (tau delta : ℕ → ℝ)
    (hKcontract : ∀ n, K n < 1)
    (hKexp : ∀ n, (K n : ℝ) ≤ Real.exp (-lambda * tau n))
    (hlambda : 0 < lambda) (htau : ∀ n, 0 < tau n)
    (hsmall : ∀ n, lambda * tau n ≤ 1)
    (hdelta : ∀ n, 0 ≤ delta n)
    (hsum : Summable fun n => delta n / tau n) :
    Summable fun n => delta n / (1 - (K n : ℝ)) := by
  apply Summable.of_nonneg_of_le
  · intro n
    exact div_nonneg (hdelta n) (sub_nonneg.mpr (hKcontract n).le)
  · intro n
    exact denseBranch_stationaryError_le (K n) lambda (tau n) (delta n)
      (hKexp n) hlambda (htau n) (hsmall n) (hdelta n)
  · exact hsum.mul_left (2 / lambda)

theorem renewal_state_transport_completeMetric
    (TX : X → X) (TY : Y → Y) (J : Y → X)
    (KX KY : ℝ≥0) (hTX : ContractingWith KX TX)
    (hTY : ContractingWith KY TY) (delta : ℝ)
    (hdefect : ∀ y : Y, dist (J (TY y)) (TX (J y)) ≤ delta) :
    (∃! x : X, TX x = x) ∧ (∃! y : Y, TY y = y)
      ∧ dist (J (stationaryState TY KY hTY))
          (stationaryState TX KX hTX)
        ≤ delta / (1 - (KX : ℝ))
      ∧ (delta = 0 →
          J (stationaryState TY KY hTY) = stationaryState TX KX hTX) := by
  refine ⟨⟨stationaryState TX KX hTX, stationaryState_isFixed TX KX hTX,
      fun x hx => stationaryState_unique TX KX hTX hx⟩,
    ⟨stationaryState TY KY hTY, stationaryState_isFixed TY KY hTY,
      fun y hy => stationaryState_unique TY KY hTY hy⟩,
    stationaryState_cutoff_bound TX TY J KX KY hTX hTY delta hdefect, ?_⟩
  intro hdelta
  subst delta
  have hbound := stationaryState_cutoff_bound TX TY J KX KY hTX hTY 0 hdefect
  exact dist_eq_zero.mp (le_antisymm (by simpa using hbound) dist_nonneg)

end RenewalStateTransportCompleteMetric
end NCG
