/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.HurwitzRH

/-!
# Prolate–Hurwitz chain, completed packet, and the parity firewall
  (`thm:v002-pswf-chain`, `prop:v002-completed-packet`,
   `corollary:parity-firewall`, arithmetic manuscript)

* `pswf_chain`: the conditional prolate route to RH — once the
  cluster, simple-even, and leakage estimates (displayed as the
  locally uniform determinant convergence `hconv`) and
  real-rootedness of the regularized determinants (`hzeros`) are
  supplied, the Hurwitz record concludes that every zero of `Ξ`
  is real;
* `completed_packet_cancellation`: the parity-forced trivial-zero
  poles cancel — with the displayed principal-part expansions of
  the digamma and `L'/L` terms near a trivial zero, their sum is
  bounded, so only nontrivial zeros contribute poles in the open
  strip;
* `parity_firewall_identity`: the exact Möbius conversion on a
  squarefree carrier — the temperature-difference product equals
  the sign `(-1)^k` (the Möbius value) times the damped positive
  product, so every shifted or fixed-sum estimate of it carries
  the weighted Möbius current linearly.

Rendering disclosed: `hconv` bundles chain hypotheses (i)–(iii)
of the manuscript (cluster decomposition, simple even ground
vector, and leakage-norm convergence — their per-record contents
are separate ledger items); the digamma and `L'/L` principal
parts are the displayed classical expansions; the Möbius value
`μ(n) = (-1)^k` for squarefree `n` names the sign factor.
-/

open Metric Set Filter

namespace NCG

/-- `thm:v002-pswf-chain`: the conditional prolate cluster route
to RH, discharged through the Hurwitz record. -/
theorem pswf_chain (Ξ : ℂ → ℂ) (D : ℕ → ℂ → ℂ)
    (hΞdiff : Differentiable ℂ Ξ)
    (hΞne : ∃ w, Ξ w ≠ 0)
    (hconv : TendstoLocallyUniformly D Ξ atTop)
    (hzeros : ∀ n z, D n z = 0 → z.im = 0)
    (hHurwitz : ∀ (z₀ : ℂ) (r : ℝ), 0 < r →
      TendstoLocallyUniformly D Ξ atTop →
      (∀ n, ∀ z ∈ closedBall z₀ r, D n z ≠ 0) →
      (∀ z ∈ ball z₀ r, Ξ z ≠ 0) ∨ (∀ z ∈ ball z₀ r, Ξ z = 0)) :
    ∀ z, Ξ z = 0 → z.im = 0 :=
  hurwitz_real_rooted_rh Ξ D hΞdiff hzeros hconv hΞne hHurwitz

/-- `prop:v002-completed-packet`, trivial-zero cancellation: the
displayed principal parts of the digamma and `L'/L` terms cancel
exactly, leaving a bounded remainder near each parity-forced
trivial zero. -/
theorem completed_packet_cancellation
    (ψhalf Ldiv B1 B2 : ℂ → ℂ) (wm : ℂ) (C1 C2 : ℝ)
    (S : Set ℂ)
    (hψ : ∀ w ∈ S, ψhalf w = -(w - wm)⁻¹ + B1 w)
    (hL : ∀ w ∈ S, Ldiv w = (w - wm)⁻¹ + B2 w)
    (hB1 : ∀ w ∈ S, ‖B1 w‖ ≤ C1)
    (hB2 : ∀ w ∈ S, ‖B2 w‖ ≤ C2) :
    ∀ w ∈ S, ‖ψhalf w + Ldiv w‖ ≤ C1 + C2 := by
  intro w hw
  rw [hψ w hw, hL w hw]
  have h1 : -(w - wm)⁻¹ + B1 w + ((w - wm)⁻¹ + B2 w)
      = B1 w + B2 w := by ring
  rw [h1]
  exact le_trans (norm_add_le _ _)
    (add_le_add (hB1 w hw) (hB2 w hw))

/-- `corollary:parity-firewall`, exact Möbius conversion: on a
squarefree carrier the temperature-difference product equals the
sign `(-1)^k` times the damped positive product. -/
theorem parity_firewall_identity (ps : Finset ℕ)
    (hps : ∀ p ∈ ps, 1 ≤ p) (a L : ℝ) :
    ∏ p ∈ ps, (Real.exp (-a * (Real.log p / L)) - 1)
      = (-1) ^ ps.card
        * Real.exp (-(a / L) * Real.log (∏ p ∈ ps, (p : ℝ)))
        * ∏ p ∈ ps, (Real.exp (a * (Real.log p / L)) - 1) := by
  classical
  -- per-factor conversion e^{-x} - 1 = (-1)·e^{-x}·(e^x - 1)
  have hfac : ∀ p ∈ ps,
      Real.exp (-a * (Real.log p / L)) - 1
      = (-1) * Real.exp (-(a * (Real.log p / L)))
        * (Real.exp (a * (Real.log p / L)) - 1) := by
    intro p _
    have h1 : Real.exp (-(a * (Real.log p / L)))
        * Real.exp (a * (Real.log p / L)) = 1 := by
      rw [← Real.exp_add]
      simp
    have h2 : -a * (Real.log p / L)
        = -(a * (Real.log p / L)) := by ring
    rw [h2]
    nlinarith [h1]
  rw [Finset.prod_congr rfl hfac]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_const]
  congr 1
  congr 1
  -- product of dampings is the damped log of the product
  rw [← Real.exp_sum]
  congr 1
  have hne : ∀ p ∈ ps, ((p : ℝ)) ≠ 0 := fun p hp => by
    have := hps p hp
    positivity
  rw [Real.log_prod hne, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  ring

end NCG
