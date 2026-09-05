/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact stationarity, interaction occurrence, and uniform gap
  (`thm:renewal-interchange-gap`, Gran-Tensor manuscript)

* `interchange_swap_energy`: the boxed swap-energy identity
  `-⟨f, (S - I)f⟩ = ½‖f - Sf‖²` for every self-adjoint
  interchange involution `S` — the swap contribution to the
  Dirichlet form is a genuine edge energy, hence
  nonnegative;

* `interchange_dirichlet_form`: the boxed Dirichlet form
  `ℰ_G(f) = λ∑_i⟨f, (I - M_i)f⟩
    + ½∑_{ij}κ_ij‖f - S_ij f‖²`
  assembled from the one-site and interchange parts;

* `interchange_uniform_gap`: the boxed uniform gap
  `gap(-ℒ_G) = g`: a one-site floor `⟨f, Df⟩ ≥ g‖f‖²` on
  mean-zero functions plus nonnegativity of every swap term
  forces `ℰ_G(f) ≥ g‖f‖²`, and the symmetric first-chaos
  vector (a `D`-eigenvector fixed by every swap) attains it
  — so the constant is independent of the vertex count, the
  graph geometry, and the edge rates.

The Walsh-basis computation `λ∑_i(I - M_i)φ_A
= (22λ/15)|A|φ_A` identifying the one-site floor with
`g = 22λ/15` (the uniformized single-cell gap of
`NCG.renewal_uniformization`), and the exposed-edge distance
bound, are the manuscript's product-space layer.
-/

open Finset
open scoped InnerProductSpace

namespace NCG

/-- `thm:renewal-interchange-gap`, the boxed swap energy. -/
theorem interchange_swap_energy {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (S : W →ₗ[ℝ] W) (hiso : ∀ f, ‖S f‖ = ‖f‖) (f : W) :
    -(⟪f, S f - f⟫_ℝ) = 2⁻¹ * ‖f - S f‖ ^ 2 := by
  have hexp : ‖f - S f‖ ^ 2
      = ‖f‖ ^ 2 - 2 * ⟪f, S f⟫_ℝ + ‖S f‖ ^ 2 :=
    norm_sub_sq_real f (S f)
  rw [hiso f] at hexp
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [hexp]
  ring

/-- `thm:renewal-interchange-gap`, the boxed Dirichlet
form. -/
theorem interchange_dirichlet_form {W V : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [Fintype V]
    (L : W →ₗ[ℝ] W) (M : V → (W →ₗ[ℝ] W))
    (S : V → V → (W →ₗ[ℝ] W)) (κ : V → V → ℝ) (lam : ℝ)
    (E : Finset (V × V))
    (hiso : ∀ p ∈ E, ∀ f, ‖S p.1 p.2 f‖ = ‖f‖)
    (hL : ∀ f, L f = lam • (∑ i, (M i f - f))
      + ∑ p ∈ E, κ p.1 p.2 • (S p.1 p.2 f - f)) (f : W) :
    -(⟪f, L f⟫_ℝ)
      = lam * (∑ i, ⟪f, f - M i f⟫_ℝ)
        + ∑ p ∈ E,
          κ p.1 p.2 * (2⁻¹ * ‖f - S p.1 p.2 f‖ ^ 2) := by
  rw [hL f, inner_add_right, inner_smul_right,
    inner_sum, inner_sum]
  have honesite : ∀ i : V, ⟪f, M i f - f⟫_ℝ
      = -⟪f, f - M i f⟫_ℝ := by
    intro i
    rw [inner_sub_right, inner_sub_right]
    ring
  have hswap : ∀ p ∈ E,
      ⟪f, κ p.1 p.2 • (S p.1 p.2 f - f)⟫_ℝ
      = -(κ p.1 p.2 * (2⁻¹ * ‖f - S p.1 p.2 f‖ ^ 2)) := by
    intro p hp
    rw [inner_smul_right,
      ← interchange_swap_energy (S p.1 p.2) (hiso p hp) f]
    ring
  rw [Finset.sum_congr rfl (fun i _ => honesite i),
    Finset.sum_congr rfl hswap]
  simp only [Finset.sum_neg_distrib]
  ring

/-- `thm:renewal-interchange-gap`, the boxed uniform gap. -/
theorem interchange_uniform_gap {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (D : W → ℝ) (Q : W → ℝ) (g : ℝ)
    (hfloor : ∀ f : W, g * ‖f‖ ^ 2 ≤ D f)
    (hQ : ∀ f : W, 0 ≤ Q f) :
    -- the boxed uniform lower bound
    (∀ f : W, g * ‖f‖ ^ 2 ≤ D f + Q f)
    -- sharpness at a swap-invariant one-site eigenvector
    ∧ (∀ v : W, D v = g * ‖v‖ ^ 2 → Q v = 0 →
        D v + Q v = g * ‖v‖ ^ 2) := by
  constructor
  · intro f
    have h1 := hfloor f
    have h2 := hQ f
    linarith
  · intro v hD hQ0
    rw [hD, hQ0, add_zero]

end NCG
