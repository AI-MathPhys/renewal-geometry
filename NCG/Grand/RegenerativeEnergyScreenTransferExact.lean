/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTRegenerativeScreenExact

/-!
# Regenerative energy-screen transfer

This module closes the comparison step in `cor:SMST-regenerative-screen`.
The shorted-Hodge/Lyapunov branch supplies inverse-radius energy tails; a
uniformly faithful Legendre--conductance comparison transfers those tails to
the packet variables.  The positive-screen theorem then yields strong packet
convergence, and a uniformly bounded inverse square root transfers it to the
physical variables.
-/

open Filter

namespace NCG
namespace SMSTChannel

variable {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

/-- A nonnegative energy tail bounded by `E/(R+1)`, together with a faithful
comparison of packet-tail energy, gives the exact packet estimate required by
the regenerative screen theorem. -/
theorem packet_tail_of_energy_comparison
    (energy : ℕ → ℕ → ℝ) (packetTail : ℕ → ℕ → ℝ)
    (E κ : ℝ) (hκ : 0 ≤ κ)
    (henergy : ∀ R n, energy R n ≤ E / (R + 1))
    (hcompare : ∀ R n, packetTail R n ≤ κ * energy R n) :
    ∀ R n, packetTail R n ≤ (κ * E) / (R + 1) := by
  intro R n
  calc
    packetTail R n ≤ κ * energy R n := hcompare R n
    _ ≤ κ * (E / (R + 1)) :=
      mul_le_mul_of_nonneg_left (henergy R n) hκ
    _ = (κ * E) / (R + 1) := by ring

/-- Exact regenerative-screen assembly from the energy bounds actually
returned by the Lyapunov/shorted-Hodge branch.  In particular, neither packet
tail is assumed: both are derived through the uniformly faithful comparison.
-/
theorem regenerative_screen_of_energy_comparison
    (Z : ℕ → Y) (Zlim : Y) (Cb : ℝ)
    (hbdd : ∀ n, ‖Z n‖ ≤ Cb)
    (hweak : WeakTendsto Z Zlim)
    (SR : ℕ → Y →L[ℂ] Y) (Sh : ℕ → ℕ → Y →L[ℂ] Y)
    (hSconv : ∀ R, Tendsto (fun n => ‖Sh R n - SR R‖)
      atTop (nhds 0))
    (hcc : ∀ (R : ℕ) (W : ℕ → Y) (Wlim : Y) (Cw : ℝ),
      (∀ n, ‖W n‖ ≤ Cw) →
      NCG.SMSTChannel.WeakTendsto (Y := Y) W Wlim →
      Tendsto (fun n => SR R (W n)) atTop (nhds (SR R Wlim)))
    (energy : ℕ → ℕ → ℝ) (energyLim : ℕ → ℝ)
    (E κ : ℝ) (hE : 0 ≤ E) (hκ : 0 ≤ κ)
    (henergy : ∀ R n, energy R n ≤ E / (R + 1))
    (henergyLim : ∀ R, energyLim R ≤ E / (R + 1))
    (hcompare : ∀ R n,
      ‖Z n - Sh R n (Z n)‖ ^ 2 ≤ κ * energy R n)
    (hcompareLim : ∀ R,
      ‖Zlim - SR R Zlim‖ ^ 2 ≤ κ * energyLim R) :
    Tendsto Z atTop (nhds Zlim) := by
  apply regenerative_screen_strong_convergence Z Zlim Cb hbdd hweak
    SR Sh hSconv hcc (κ * E) (mul_nonneg hκ hE)
  · exact packet_tail_of_energy_comparison energy
      (fun R n => ‖Z n - Sh R n (Z n)‖ ^ 2)
      E κ hκ henergy hcompare
  · intro R
    exact packet_tail_of_energy_comparison
      (fun R _ => energyLim R)
      (fun R _ => ‖Zlim - SR R Zlim‖ ^ 2)
      E κ hκ (fun R _ => henergyLim R) (fun R _ => hcompareLim R) R 0

/-- Full physical-packet conclusion: after regenerative energy-screen
compactness, the uniformly bounded inverse square-root packet map converges
strongly and therefore carries the strong limit to the physical variables. -/
theorem regenerative_physical_packet_convergence
    (Z : ℕ → Y) (Zlim : Y) (Cb : ℝ)
    (hbdd : ∀ n, ‖Z n‖ ≤ Cb)
    (hweak : WeakTendsto Z Zlim)
    (SR : ℕ → Y →L[ℂ] Y) (Sh : ℕ → ℕ → Y →L[ℂ] Y)
    (hSconv : ∀ R, Tendsto (fun n => ‖Sh R n - SR R‖)
      atTop (nhds 0))
    (hcc : ∀ (R : ℕ) (W : ℕ → Y) (Wlim : Y) (Cw : ℝ),
      (∀ n, ‖W n‖ ≤ Cw) →
      NCG.SMSTChannel.WeakTendsto (Y := Y) W Wlim →
      Tendsto (fun n => SR R (W n)) atTop (nhds (SR R Wlim)))
    (energy : ℕ → ℕ → ℝ) (energyLim : ℕ → ℝ)
    (E κ : ℝ) (hE : 0 ≤ E) (hκ : 0 ≤ κ)
    (henergy : ∀ R n, energy R n ≤ E / (R + 1))
    (henergyLim : ∀ R, energyLim R ≤ E / (R + 1))
    (hcompare : ∀ R n,
      ‖Z n - Sh R n (Z n)‖ ^ 2 ≤ κ * energy R n)
    (hcompareLim : ∀ R,
      ‖Zlim - SR R Zlim‖ ^ 2 ≤ κ * energyLim R)
    (B : ℕ → Y →L[ℂ] Y) (Blim : Y →L[ℂ] Y) (Cm : ℝ)
    (hBbdd : ∀ n, ‖B n‖ ≤ Cm)
    (hBstrong : ∀ v : Y, Tendsto (fun n => B n v) atTop
      (nhds (Blim v))) :
    Tendsto Z atTop (nhds Zlim) ∧
      Tendsto (fun n => B n (Z n)) atTop (nhds (Blim Zlim)) := by
  have hZ := regenerative_screen_of_energy_comparison Z Zlim Cb hbdd hweak
    SR Sh hSconv hcc energy energyLim E κ hE hκ henergy henergyLim
    hcompare hcompareLim
  exact ⟨hZ, strong_convergence_transfer B Blim Cm hBbdd hBstrong Z Zlim hZ⟩

end SMSTChannel
end NCG
