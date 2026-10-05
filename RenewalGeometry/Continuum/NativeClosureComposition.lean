/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The composition step of `thm:native-closure`

Einstein–Standard-Model action-closure manuscript, proof of `thm:native-closure`
("Apply the one-sided coupled actual-jet stability estimate `prop:coupled-bootstrap` with
`d = i_{h,k} + γ_{h,k} + 𝒴_k(z_h)` … yields `eq:native-geometry`").

`native_closure_composition` is the bookkeeping that composes
* the output of `thm:native-source`, `𝒴_k(z_h) ≤ C₁ F_{h,k}` (`eq:native-strong-source`), and
* the conclusion of `prop:coupled-bootstrap`, `d ≤ d_*` ⇒ (state + curvature + stress
  difference) `≤ C_* d`,
into `eq:native-geometry`: if `D^{full}_{h,k} = i_{h,k} + γ_{h,k} + F_{h,k} → 0`, then eventually
the comparison quantity is `≤ C_* max(1, C₁) D^{full}_{h,k}`.  Both inputs are hypotheses here:
`thm:native-source` and `prop:coupled-bootstrap` are open in the ledger, so this file does not
close `thm:native-closure`; it isolates the exact dependency.
-/

open Filter Topology

namespace RenewalGeometry.NativeClosure

/-- **Composition of `thm:native-source` with `prop:coupled-bootstrap`** (proof of
`thm:native-closure`).  Along any filter, if `D_h = i_h + γ_h + F_h → 0` (all nonnegative), the
source bound `Y_h ≤ C₁F_h` holds, and the bootstrap gives `S_h ≤ C_*(i_h + γ_h + Y_h)` whenever
`i_h + γ_h + Y_h ≤ d_*` (`d_* > 0`), then eventually `S_h ≤ C_* max(1, C₁) D_h`. -/
theorem native_closure_composition {ι : Type*} {l : Filter ι} {i γ Y F S : ι → ℝ}
    {C₁ Cst dst : ℝ} (hdst : 0 < dst) (hCst : 0 ≤ Cst)
    (hi : ∀ h, 0 ≤ i h) (hγ : ∀ h, 0 ≤ γ h) (hF : ∀ h, 0 ≤ F h)
    (hD : Tendsto (fun h => i h + γ h + F h) l (𝓝 0))
    (hY : ∀ h, Y h ≤ C₁ * F h)
    (hboot : ∀ h, i h + γ h + Y h ≤ dst → S h ≤ Cst * (i h + γ h + Y h)) :
    ∀ᶠ h in l, S h ≤ Cst * max 1 C₁ * (i h + γ h + F h) := by
  set K := max 1 C₁ with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hev : ∀ᶠ h in l, i h + γ h + F h < dst / K :=
    hD.eventually (gt_mem_nhds (div_pos hdst hK0))
  filter_upwards [hev] with h hh
  have hdY : i h + γ h + Y h ≤ K * (i h + γ h + F h) := by
    have h1 : C₁ * F h ≤ K * F h := mul_le_mul_of_nonneg_right (le_max_right _ _) (hF h)
    have h2 : i h + γ h ≤ K * (i h + γ h) := by
      have := hi h; have := hγ h
      nlinarith
    nlinarith [hY h]
  have hsmall : i h + γ h + Y h ≤ dst := by
    calc i h + γ h + Y h ≤ K * (i h + γ h + F h) := hdY
      _ ≤ K * (dst / K) := mul_le_mul_of_nonneg_left hh.le hK0.le
      _ = dst := by field_simp
  calc S h ≤ Cst * (i h + γ h + Y h) := hboot h hsmall
    _ ≤ Cst * (K * (i h + γ h + F h)) := mul_le_mul_of_nonneg_left hdY hCst
    _ = Cst * K * (i h + γ h + F h) := by ring

end RenewalGeometry.NativeClosure
