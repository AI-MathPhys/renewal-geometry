/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.CoordinateCurvature

/-!
# Coordinate curvature as a Lipschitz function of the metric 2-jet
  (infrastructure for `thm:supp-gowdy-full-curvature`, `eq:supp-gowdy-full-curvature`:
  "`Γ = g⁻¹ * Dg`, … substitution in `Riem = DΓ + Γ*Γ`"; emergent-spacetime supplement)

In coordinates on `Fin 4`, with the inverse metric `g^{ab}`, the first derivatives
`dg i e j = ∂_i g_{ej}` and the second derivatives `ddg d i e j = ∂_d ∂_i g_{ej}`:

* `christoffel` (`CoordinateCurvature`) gives `Γ^c_{ij} = ½ g^{ce}(∂_i g_{ej} + ∂_j g_{ei} - ∂_e g_{ij})`;
* `dInvMetric ginv dg d c e = -g^{cf} ∂_d g_{fk} g^{ke}` is the derivative of the inverse metric
  (the entries of `-g⁻¹ (∂_d g) g⁻¹`), and `dChristoffel` is `∂_d Γ^c_{ij}` by the product rule;
* `riemJet ginv dg ddg = riemann (christoffel ginv dg) (dChristoffel ginv dg ddg)` and `ricciJet`
  are polynomial in the jet `(g⁻¹, ∂g, ∂²g)`.

`riemJet_lipschitz`, `ricciJet_lipschitz`: on every closed ball of jets there is a Lipschitz
constant `L` with `‖Riem(J) - Riem(J')‖ ≤ L ‖J - J'‖` (sup norms).  `inv_sub_inv_entry_le`
controls the inverse metric: `|(g⁻¹ - g'⁻¹)_{ij}| ≤ 16 B² δ` when the inverses are entrywise
bounded by `B` and `|g - g'| ≤ δ` entrywise (inverses taken at type `Matrix`).  Hence pointwise jet errors `O(h²)` in `(g, ∂g)` and `O(h)` in `∂²g`
with bounded jets and bounded inverses give `‖Riem(g_h) - Riem(g_*)‖ = O(h)`
(`riemJet_sub_le`).
-/

open Finset
open scoped BigOperators

namespace RenewalGeometry.CoordinateCurvatureJet

noncomputable section

/-- Index arrays. -/
abbrev Arr2 := Fin 4 → Fin 4 → ℝ
abbrev Arr3 := Fin 4 → Fin 4 → Fin 4 → ℝ
abbrev Arr4 := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- The metric 2-jet `(g⁻¹, ∂g, ∂²g)`. -/
abbrev Jet := Arr2 × Arr3 × Arr4

/-- `∂_d g^{ce} = -Σ_{f,k} g^{cf} ∂_d g_{fk} g^{ke}`. -/
def dInvMetric (ginv : Arr2) (dg : Arr3) : Arr3 :=
  fun d c e => -∑ f, ∑ k, ginv c f * dg d f k * ginv k e

/-- `∂_d Γ^c_{ij}` from the 2-jet (product rule applied to `christoffel`). -/
def dChristoffel (ginv : Arr2) (dg : Arr3) (ddg : Arr4) : Arr4 :=
  fun d c i j => (1 / 2) * ∑ e, (dInvMetric ginv dg d c e * (dg i e j + dg j e i - dg e i j) +
    ginv c e * (ddg d i e j + ddg d j e i - ddg d e i j))

/-- The Riemann tensor `R^a_{bcd}` of the 2-jet. -/
def riemJet (J : Jet) : Arr4 :=
  riemann (christoffel J.1 J.2.1) (dChristoffel J.1 J.2.1 J.2.2)

/-- The Ricci tensor of the 2-jet. -/
def ricciJet (J : Jet) : Arr2 :=
  ricci (christoffel J.1 J.2.1) (dChristoffel J.1 J.2.1 J.2.2)

theorem contDiff_riemJet : ContDiff ℝ ⊤ riemJet := by
  unfold riemJet riemann christoffel dChristoffel dInvMetric
  fun_prop

theorem contDiff_ricciJet : ContDiff ℝ ⊤ ricciJet := by
  unfold ricciJet ricci riemann christoffel dChristoffel dInvMetric
  fun_prop

/-- **The Riemann tensor is Lipschitz in the metric 2-jet** on every closed ball of jets. -/
theorem riemJet_lipschitz (B : ℝ) : ∃ L : ℝ, 0 ≤ L ∧
    ∀ J ∈ Metric.closedBall (0 : Jet) B, ∀ J' ∈ Metric.closedBall (0 : Jet) B,
      ‖riemJet J - riemJet J'‖ ≤ L * ‖J - J'‖ := by
  obtain ⟨K, hK⟩ := contDiff_riemJet.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall 0 B) (isCompact_closedBall 0 B)
  refine ⟨K, K.2, fun J hJ J' hJ' => ?_⟩
  have := hK.dist_le_mul J hJ J' hJ'
  rwa [dist_eq_norm, dist_eq_norm] at this

/-- **The Ricci tensor is Lipschitz in the metric 2-jet** on every closed ball of jets. -/
theorem ricciJet_lipschitz (B : ℝ) : ∃ L : ℝ, 0 ≤ L ∧
    ∀ J ∈ Metric.closedBall (0 : Jet) B, ∀ J' ∈ Metric.closedBall (0 : Jet) B,
      ‖ricciJet J - ricciJet J'‖ ≤ L * ‖J - J'‖ := by
  obtain ⟨K, hK⟩ := contDiff_ricciJet.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall 0 B) (isCompact_closedBall 0 B)
  refine ⟨K, K.2, fun J hJ J' hJ' => ?_⟩
  have := hK.dist_le_mul J hJ J' hJ'
  rwa [dist_eq_norm, dist_eq_norm] at this

/-- The jet distance is at most the sum of the component distances. -/
theorem norm_jet_sub_le (J J' : Jet) :
    ‖J - J'‖ ≤ ‖J.1 - J'.1‖ + ‖J.2.1 - J'.2.1‖ + ‖J.2.2 - J'.2.2‖ := by
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · simp only [Prod.fst_sub]; linarith [norm_nonneg (J.2.1 - J'.2.1), norm_nonneg (J.2.2 - J'.2.2)]
  · simp only [Prod.snd_sub, Prod.fst_sub]
    linarith [norm_nonneg (J.1 - J'.1), norm_nonneg (J.2.2 - J'.2.2)]
  · simp only [Prod.snd_sub]
    linarith [norm_nonneg (J.1 - J'.1), norm_nonneg (J.2.1 - J'.2.1)]

/-- **Curvature error from jet errors** (`eq:supp-gowdy-full-curvature`, pointwise): with jets
in the ball of radius `B`, `‖g_h⁻¹ - g_*⁻¹‖ ≤ ε₀`, `‖∂g_h - ∂g_*‖ ≤ ε₁`, `‖∂²g_h - ∂²g_*‖ ≤ ε₂`,
the Riemann tensors differ by at most `L (ε₀ + ε₁ + ε₂)`, `L` depending only on `B`. -/
theorem riemJet_sub_le (B : ℝ) : ∃ L : ℝ, 0 ≤ L ∧
    ∀ J ∈ Metric.closedBall (0 : Jet) B, ∀ J' ∈ Metric.closedBall (0 : Jet) B,
      ∀ ε₀ ε₁ ε₂ : ℝ, ‖J.1 - J'.1‖ ≤ ε₀ → ‖J.2.1 - J'.2.1‖ ≤ ε₁ → ‖J.2.2 - J'.2.2‖ ≤ ε₂ →
        ‖riemJet J - riemJet J'‖ ≤ L * (ε₀ + ε₁ + ε₂) := by
  obtain ⟨L, hL, hlip⟩ := riemJet_lipschitz B
  refine ⟨L, hL, fun J hJ J' hJ' ε₀ ε₁ ε₂ h0 h1 h2 => (hlip J hJ J' hJ').trans ?_⟩
  exact mul_le_mul_of_nonneg_left ((norm_jet_sub_le J J').trans (by linarith)) hL

/-- **The inverse metric is Lipschitz where it is bounded**: for invertible `4 × 4` matrices
(inverted at type `Matrix`), entrywise
`|(g⁻¹ - g'⁻¹)_{ij}| ≤ 16 B² δ` when `|g⁻¹|, |g'⁻¹| ≤ B` and `|g - g'| ≤ δ` entrywise. -/
theorem inv_sub_inv_entry_le (g g' : Matrix (Fin 4) (Fin 4) ℝ) (hg : IsUnit g.det)
    (hg' : IsUnit g'.det) {B δ : ℝ} (hB : ∀ i j, |g⁻¹ i j| ≤ B) (hB' : ∀ i j, |g'⁻¹ i j| ≤ B)
    (hδ : ∀ i j, |g i j - g' i j| ≤ δ) (i j : Fin 4) :
    |g⁻¹ i j - g'⁻¹ i j| ≤ 16 * B ^ 2 * δ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0 0)
  have key : g⁻¹ - g'⁻¹ = g⁻¹ * (g' - g) * g'⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg', Matrix.mul_one]
  have e : g⁻¹ i j - g'⁻¹ i j = (g⁻¹ * (g' - g) * g'⁻¹) i j := by
    rw [← key]; rfl
  rw [e, Matrix.mul_apply]
  simp only [Matrix.mul_apply]
  have hterm : ∀ k l : Fin 4, |g⁻¹ i l * (g' - g) l k * g'⁻¹ k j| ≤ B * δ * B := by
    intro k l
    rw [abs_mul, abs_mul]
    have h1 : |(g' - g) l k| ≤ δ := by
      rw [Matrix.sub_apply, abs_sub_comm]; exact hδ l k
    exact mul_le_mul (mul_le_mul (hB i l) h1 (abs_nonneg _) hB0) (hB' k j) (abs_nonneg _)
      (mul_nonneg hB0 hδ0)
  calc |∑ k, (∑ l, g⁻¹ i l * (g' - g) l k) * g'⁻¹ k j|
      = |∑ k, ∑ l, g⁻¹ i l * (g' - g) l k * g'⁻¹ k j| := by
        congr 1; refine Finset.sum_congr rfl fun k _ => ?_; rw [Finset.sum_mul]
    _ ≤ ∑ k : Fin 4, ∑ l : Fin 4, |g⁻¹ i l * (g' - g) l k * g'⁻¹ k j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ k : Fin 4, ∑ l : Fin 4, B * δ * B :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l
    _ = 16 * B ^ 2 * δ := by simp; ring

/-- Non-vacuity: the Minkowski jet `(η⁻¹, 0, 0)` has vanishing curvature. -/
example : riemJet (fun i j => if i = j then (if i = 0 then -1 else 1) else 0, 0, 0) = 0 := by
  funext a b c d
  simp [riemJet, riemann, christoffel, dChristoffel, dInvMetric]

end

end RenewalGeometry.CoordinateCurvatureJet
