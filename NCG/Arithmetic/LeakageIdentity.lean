/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact leakage identity
  (`thm:v002-leakage`, arithmetic monograph)

Let `QW` be a form (only first-slot additivity is used), let `F` be
in its radical against the Galerkin range, decomposed as
`F = φ + s + r` with `φ = P_N P_win F` the Galerkin-window part,
`s` the Galerkin leakage and `r` the window leakage.  If `Q_N`
represents `QW` on the Galerkin range (`⟪h, Q_Nφ⟫ = QW(φ,h)`), then

  `⟪h, Q_Nφ⟫ = −QW(r,h) − QW(s,h)`  for every Galerkin `h`,

and consequently `‖Q_Nφ‖` is bounded by the supremum of
`|QW(r,h) + QW(s,h)|` over unit Galerkin vectors.

* `leakage_identity` — the boxed identity;
* `leakage_bound` — the norm consequence.
-/

open scoped InnerProductSpace

namespace NCG

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `thm:v002-leakage` (identity): for a radical vector
`F = φ + s + r` and any Galerkin vector `h` on which `Q_N`
represents the form, `⟪h, Q_Nφ⟫ = −QW(r,h) − QW(s,h)`. -/
theorem leakage_identity (QW : H → H → ℂ)
    (hadd : ∀ x y h : H, QW (x + y) h = QW x h + QW y h)
    {F g r φ s QNφ h : H}
    (hg : F = g + r) (hφ : g = φ + s)
    (hrad : QW F h = 0)
    (hrep : ⟪h, QNφ⟫_ℂ = QW φ h) :
    ⟪h, QNφ⟫_ℂ = -QW r h - QW s h := by
  have hsplit : QW F h = QW φ h + QW s h + QW r h := by
    rw [hg, hφ, hadd, hadd]
  rw [hrad] at hsplit
  rw [hrep]
  linear_combination -hsplit

/-- `thm:v002-leakage` (norm bound): the Galerkin residual of a
radical packet is controlled by the window and Galerkin leakage
tested against unit Galerkin vectors. -/
theorem leakage_bound (QW : H → H → ℂ)
    (hadd : ∀ x y h : H, QW (x + y) h = QW x h + QW y h)
    (V : Submodule ℂ H) {F g r φ s QNφ : H}
    (hg : F = g + r) (hφ : g = φ + s)
    (hQN : QNφ ∈ V)
    (hrad : ∀ h ∈ V, QW F h = 0)
    (hrep : ∀ h ∈ V, ⟪h, QNφ⟫_ℂ = QW φ h)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ h ∈ V, ‖h‖ = 1 → ‖QW r h + QW s h‖ ≤ M) :
    ‖QNφ‖ ≤ M := by
  by_cases hz : QNφ = 0
  · rw [hz, norm_zero]
    exact hM0
  · have hnz : ‖QNφ‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    set h₀ : H := ((‖QNφ‖ : ℂ))⁻¹ • QNφ with hh₀
    have hmem : h₀ ∈ V := V.smul_mem _ hQN
    have hnorm : ‖h₀‖ = 1 := by
      rw [hh₀, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnz]
    have hid := leakage_identity QW hadd hg hφ (hrad h₀ hmem)
      (hrep h₀ hmem)
    have hval : ⟪h₀, QNφ⟫_ℂ = (‖QNφ‖ : ℂ) := by
      rw [hh₀, inner_smul_left, inner_self_eq_norm_sq_to_K,
        ← RCLike.ofReal_eq_complex_ofReal]
      rw [map_inv₀, RCLike.conj_ofReal]
      have hne : (RCLike.ofReal ‖QNφ‖ : ℂ) ≠ 0 :=
        RCLike.ofReal_ne_zero.mpr hnz
      rw [sq, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    have hfinal : (‖QNφ‖ : ℂ) = -QW r h₀ - QW s h₀ := by
      rw [← hval]
      exact hid
    have hnormeq : ‖QNφ‖ = ‖QW r h₀ + QW s h₀‖ := by
      have h1 : ‖((‖QNφ‖ : ℝ) : ℂ)‖ = ‖QNφ‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      rw [← h1, hfinal]
      rw [show -QW r h₀ - QW s h₀ = -(QW r h₀ + QW s h₀) from by
        ring]
      rw [norm_neg]
    rw [hnormeq]
    exact hM h₀ hmem hnorm

end NCG
