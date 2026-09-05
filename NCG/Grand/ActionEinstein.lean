/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Common-action Ward, BRST, stress, and the finite Einstein
  residual (`thm:SMST-finite-action-Einstein`, Gran-Tensor
  manuscript)

* `total_stress_split`: the boxed total equation of motion —
  `ℰ_q^tot = 2D_q𝒮_tot = 2D_q𝒮_g - 𝖳` with
  `𝖳 = -2D_q𝒮_mat` (linearity of the derivative on the joint
  carrier);
* `invariance_derivative_zero` / `gauge_ward_identity`: clause
  (F1) — exact finite gauge invariance makes the action constant
  along every gauge flow, so the flow derivative vanishes, and
  when that derivative is the displayed pairing
  `Div_U J + ℛ*E_Φ` the boxed Ward identity holds;
* `relabeling_stress_identity`: clause (F3) — common tangential
  relabeling invariance makes the flow derivative
  `⟨ℒ*𝖳⟩ - 2⟨ℒ*E_Φ⟩` vanish, giving the boxed stress-transfer
  identity;
* `einstein_residual_psd`: clause (F4) — for a positive-definite
  metric on geometric variations,
  `Δ_Ein = ⟨ℰ, G⁻¹ℰ⟩ ≥ 0` with equality exactly at metric
  stationarity `ℰ = 0`, i.e. `2D_q𝒮_g = 𝖳`.

Rendering disclosed: the BRST clause (F2) (ghost complex and
nilpotency on the covariant finite-Dirac carriers) and the
identification of the flow derivatives with the displayed
divergence/pairing expressions are the manuscript's variational
layer; the derivative splitting, both invariance-to-identity
steps, and the residual positivity/stationarity are proved
here.
-/

open Matrix

namespace NCG

/-- Boxed total equation of motion: with `𝖳 = -2D_q𝒮_mat`,
`2D_q(𝒮_g + 𝒮_mat) = 2D_q𝒮_g - 𝖳`. -/
theorem total_stress_split {Q : Type*} [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] (Sg Sm : Q → ℝ) (q : Q)
    (Dg Dm : Q →L[ℝ] ℝ) (hg : HasFDerivAt Sg Dg q)
    (hm : HasFDerivAt Sm Dm q) :
    HasFDerivAt (fun x => Sg x + Sm x) (Dg + Dm) q
      ∧ (2 : ℝ) • (Dg + Dm)
        = (2 : ℝ) • Dg - (-(2 : ℝ) • Dm) := by
  refine ⟨hg.add hm, ?_⟩
  module

/-- Invariance kills the flow derivative: a function constant
along a flow has derivative zero at every time. -/
theorem invariance_derivative_zero (F : ℝ → ℝ)
    (hconst : ∀ t, F t = F 0) (d t₀ : ℝ)
    (hd : HasDerivAt F d t₀) : d = 0 := by
  have hF : F = fun _ => F 0 := funext hconst
  have hzero : HasDerivAt F 0 t₀ := by
    rw [hF]
    exact hasDerivAt_const t₀ (F 0)
  exact hd.unique hzero

/-- Clause (F1), boxed Ward identity: if the gauge-flow
derivative of the invariant action is the pairing
`Div_U J + ⟨ℛ*, E_Φ⟩`, that pairing vanishes. -/
theorem gauge_ward_identity (F : ℝ → ℝ)
    (hconst : ∀ t, F t = F 0) (divJ pairing t₀ : ℝ)
    (hd : HasDerivAt F (divJ + pairing) t₀) :
    divJ + pairing = 0 :=
  invariance_derivative_zero F hconst _ t₀ hd

/-- Clause (F3), boxed stress transfer: if the relabeling-flow
derivative is `⟨ℒ*𝖳⟩ - 2⟨ℒ*E_Φ⟩` and the action is relabeling
invariant, then `⟨ℒ*𝖳⟩ = 2⟨ℒ*E_Φ⟩`. -/
theorem relabeling_stress_identity (F : ℝ → ℝ)
    (hconst : ∀ t, F t = F 0) (pairT pairE t₀ : ℝ)
    (hd : HasDerivAt F (pairT - 2 * pairE) t₀) :
    pairT = 2 * pairE := by
  have h := invariance_derivative_zero F hconst _ t₀ hd
  linarith

open scoped ComplexOrder in
/-- Clause (F4), boxed finite Einstein residual: for a
positive-definite variation metric,
`Δ_Ein = ⟨ℰ, G⁻¹ℰ⟩ ≥ 0` with equality exactly at metric
stationarity `ℰ = 0`. -/
theorem einstein_residual_psd {n : Type*} [Fintype n]
    [DecidableEq n] (G : Matrix n n ℂ) (hG : G.PosDef)
    (E : n → ℂ) :
    0 ≤ (star E ⬝ᵥ G⁻¹.mulVec E).re
      ∧ (star E ⬝ᵥ G⁻¹.mulVec E = 0 ↔ E = 0) := by
  have hGinv : (G⁻¹).PosDef := hG.inv
  constructor
  · rcases eq_or_ne E 0 with rfl | hE
    · simp
    · exact (hGinv.re_dotProduct_pos hE).le
  · constructor
    · intro h0
      by_contra hE
      have hpos := hGinv.re_dotProduct_pos hE
      rw [h0] at hpos
      simp at hpos
    · rintro rfl
      simp

end NCG
