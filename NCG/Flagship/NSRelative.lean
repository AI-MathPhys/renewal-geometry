/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Conditional Navier–Stokes continuation
  (`thm:NS-relative-master`, flagship manuscript)

`ns_relative_energy`: the boxed weighted energy estimate — from
the `H^s` energy identity `E' + νD = -Re⟨A^{s/2}B(u,u), A^{s/2}u⟩`
and the relative bound
`|⟨A^{s/2}B(u,u), A^{s/2}u⟩| ≤ (1-θ)νD + kE` (combined into the
displayed differential inequality `hineq`), the integrating
factor `e^{-K}` gives

`e^{-K(t)}E(t) + θν∫₀ᵗ e^{-K}D ≤ E(0)` :

the auxiliary function `F = e^{-K}E + θν∫e^{-K}D` has nonpositive
derivative and `F(0) = E(0)`.

Rendering disclosed: the `H^s` energy identity itself, the local
continuation criterion for `s > 5/2` (global smoothness once the
estimate is global), and the observation that generic positive
Schur shorting cannot manufacture the relative bound are the
manuscript's PDE layer; the Grönwall/integrating-factor content
is proved here.  `K` and `G` enter through their FTC data
(`K' = k`, `G' = e^{-K}D`, `K(0) = G(0) = 0`), the standard
rendering of the locally integrable time weights.
-/

namespace NCG

/-- `thm:NS-relative-master`, boxed estimate: the integrating
factor turns the relative bound into a monotone energy. -/
theorem ns_relative_energy (E E' D k K G : ℝ → ℝ)
    (ν θ t : ℝ) (_hθν : 0 ≤ θ * ν)
    (hE : ∀ s, HasDerivAt E (E' s) s)
    (hK : ∀ s, HasDerivAt K (k s) s) (hK0 : K 0 = 0)
    (hG : ∀ s, HasDerivAt G (Real.exp (-K s) * D s) s)
    (hG0 : G 0 = 0)
    (hineq : ∀ s, E' s ≤ -(θ * ν) * D s + k s * E s)
    (ht : 0 ≤ t) :
    Real.exp (-K t) * E t + θ * ν * G t ≤ E 0 := by
  let F : ℝ → ℝ :=
    fun s => Real.exp (-K s) * E s + θ * ν * G s
  have hFd : ∀ s, HasDerivAt F
      (Real.exp (-K s) * (-k s) * E s
        + Real.exp (-K s) * E' s
        + θ * ν * (Real.exp (-K s) * D s)) s := by
    intro s
    have hexp : HasDerivAt (fun u => Real.exp (-K u))
        (Real.exp (-K s) * (-k s)) s := by
      have hneg : HasDerivAt (fun u => -K u) (-k s) s :=
        (hK s).neg
      exact (Real.hasDerivAt_exp (-K s)).comp s hneg
    have hprod := hexp.mul (hE s)
    have hlin := (hG s).const_mul (θ * ν)
    exact (hprod.add hlin).congr_deriv (by ring)
  have hF0 : F 0 = E 0 := by
    simp [F, hK0, hG0]
  have hante : AntitoneOn F (Set.Icc 0 t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (convex_Icc 0 t)
      (fun s _ => (hFd s).continuousAt.continuousWithinAt)
      (fun s _ => ((hFd s).hasDerivWithinAt)) ?_
    intro s _
    have h1 := hineq s
    have h2 : (0:ℝ) < Real.exp (-K s) := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_left h1 h2.le]
  have hFt : F t ≤ F 0 :=
    hante (Set.mem_Icc.mpr ⟨le_refl 0, ht⟩)
      (Set.mem_Icc.mpr ⟨ht, le_refl t⟩) ht
  calc Real.exp (-K t) * E t + θ * ν * G t = F t := rfl
    _ ≤ F 0 := hFt
    _ = E 0 := hF0

end NCG
