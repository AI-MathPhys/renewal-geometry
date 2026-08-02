/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Sharp one-dwell cluster centre and polar Gram–resource law
  (`lem:cluster-common-dwell-master`,
   `cor:polar-Gram-resource-master`, flagship manuscript)

* `cluster_common_dwell`: for a positive Store-frequency cluster
  `[μ⁻, μ⁺]`, the boxed minimax identity for the polar angle
  `π/4`: at the centre `t* = π/(2(μ⁻+μ⁺))` every cluster
  frequency has phase error at most
  `(π/4)(μ⁺-μ⁻)/(μ⁺+μ⁻)`, and no dwell time does better (the
  lower bound already holds for the endpoint pair, hence for the
  full cluster maximum).
* `polar_gram_resource`: the two-axis Bloch Gram
  `[[1, cosθ],[cosθ, 1]]` has certified eigenpairs
  `(1-cosθ, (1,-1))`, `(1+cosθ, (1,1))`, the boxed floor identity
  `λ_min = 1 - cosθ = 2sin²(θ/2)`, and the boxed count identity
  `⌈π/(4θ)⌉ = ⌈π/(8 arcsin √(λ_min/2))⌉` for `0 < θ ≤ π`.  The
  pulse-count semantics `k_pol = k_*(exp(-iπσ_y/4), θ)` and
  `L_pol ≤ 2k_pol + 1` live in
  `thm:optimal-transverse-pulse-master` (prose here).
-/

open Matrix

namespace NCG

/-- `lem:cluster-common-dwell-master`, boxed minimax: the centre
`t* = π/(2(μ⁻+μ⁺))` achieves phase error
`(π/4)(μ⁺-μ⁻)/(μ⁺+μ⁻)` uniformly on the cluster, and every dwell
time incurs at least this error at one endpoint. -/
theorem cluster_common_dwell (μm μp : ℝ) (h0 : 0 < μm)
    (hle : μm ≤ μp) :
    (∀ μ ∈ Set.Icc μm μp,
      |Real.pi / (2 * (μm + μp)) * μ - Real.pi / 4|
        ≤ Real.pi / 4 * ((μp - μm) / (μp + μm)))
    ∧ ∀ t : ℝ,
      Real.pi / 4 * ((μp - μm) / (μp + μm))
        ≤ max |t * μm - Real.pi / 4| |t * μp - Real.pi / 4| := by
  have hs : (0 : ℝ) < μp + μm := by linarith
  have hs2 : (0 : ℝ) < μm + μp := by linarith
  constructor
  · rintro μ ⟨h1, h2⟩
    have key : Real.pi / (2 * (μm + μp)) * μ - Real.pi / 4
        = Real.pi / 4 * ((2 * μ - (μm + μp)) / (μp + μm)) := by
      field_simp
      ring
    rw [key, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 4),
      abs_div, abs_of_pos hs]
    gcongr
    rw [abs_le]
    constructor <;> linarith
  · intro t
    have h1 := abs_le.mp (le_max_left
      |t * μm - Real.pi / 4| |t * μp - Real.pi / 4|)
    have h2 := abs_le.mp (le_max_right
      |t * μm - Real.pi / 4| |t * μp - Real.pi / 4|)
    have hkey : Real.pi / 4 * (μp - μm)
        ≤ max |t * μm - Real.pi / 4| |t * μp - Real.pi / 4|
            * (μp + μm) := by
      nlinarith [h1.1, h1.2, h2.1, h2.2, h0, hle]
    rw [← mul_div_assoc, div_le_iff₀ hs]
    linarith

/-- The two-axis Bloch Gram of the polar quarter-root problem. -/
noncomputable def blochGram (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, Real.cos θ; Real.cos θ, 1]

/-- `cor:polar-Gram-resource-master`, boxed law: certified
eigenpairs of the two-axis Gram, the floor identity
`λ_min = 1 - cosθ = 2sin²(θ/2)`, and the count identity
`⌈π/(4θ)⌉ = ⌈π/(8 arcsin √(λ_min/2))⌉`. -/
theorem polar_gram_resource (θ : ℝ) (h0 : 0 < θ)
    (hπ : θ ≤ Real.pi) :
    blochGram θ *ᵥ ![1, -1] = (1 - Real.cos θ) • ![1, -1]
    ∧ blochGram θ *ᵥ ![1, 1] = (1 + Real.cos θ) • ![1, 1]
    ∧ 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2
    ∧ (⌈Real.pi / (4 * θ)⌉ : ℤ)
        = ⌈Real.pi / (8 * Real.arcsin
            (Real.sqrt ((1 - Real.cos θ) / 2)))⌉ := by
  have hsin : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
    have h := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    rw [h, Real.cos_sq' (θ / 2)]
    ring
  have hsinpos : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith [Real.pi_pos])
  have harc : Real.arcsin (Real.sqrt ((1 - Real.cos θ) / 2))
      = θ / 2 := by
    rw [← hsin, Real.sqrt_sq hsinpos,
      Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext j
    fin_cases j <;>
      (simp [blochGram, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]; ring)
  · funext j
    fin_cases j <;>
      simp [blochGram, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, add_comm]
  · rw [hsin]
    ring
  · rw [harc, show 8 * (θ / 2) = 4 * θ by ring]

end NCG
