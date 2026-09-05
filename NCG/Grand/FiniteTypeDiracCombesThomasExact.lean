/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTypeWeightedInverseClosure

/-!
# Coercive finite Dirac inverse and Combes--Thomas corner identity

This file removes the two interfaces formerly left in the finite-type closure:
the inverse and its norm are constructed from the finite square-gap inequality,
and the exponentially weighted corner identity is derived algebraically from
the conjugated inverse and the endpoint weight relations.
-/

open scoped BigOperators

noncomputable section

namespace NCG
namespace FiniteTypeDiracCombesThomas

/-- A finite-dimensional operator satisfying the norm-square form of
`D² ⪰ σ² I` is invertible, and its inverse has norm at most `1/σ`. -/
theorem inverse_of_square_gap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (D : H →L[ℂ] H) (σ : ℝ) (hσ : 0 < σ)
    (hgap : ∀ x : H, σ ^ 2 * ‖x‖ ^ 2 ≤ ‖D x‖ ^ 2) :
    ∃ Di : H →L[ℂ] H,
      D * Di = 1 ∧ Di * D = 1 ∧ ‖Di‖ ≤ 1 / σ := by
  have hinj : Function.Injective D := by
    intro x y hxy
    have hzero : D (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hg := hgap (x - y)
    rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hg
    have hxynorm : ‖x - y‖ = 0 := by
      have hσsq : 0 < σ ^ 2 := sq_pos_of_pos hσ
      have hprod : σ ^ 2 * ‖x - y‖ ^ 2 = 0 :=
        le_antisymm hg (mul_nonneg hσsq.le (sq_nonneg _))
      have hsquare : ‖x - y‖ ^ 2 = 0 :=
        (mul_eq_zero.mp hprod).resolve_left hσsq.ne'
      exact (sq_eq_zero_iff).mp hsquare
    exact sub_eq_zero.mp (norm_eq_zero.mp hxynorm)
  have hsurj : Function.Surjective D :=
    LinearMap.injective_iff_surjective.mp hinj
  let e : H ≃L[ℂ] H := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  let Di : H →L[ℂ] H := e.symm.toContinuousLinearMap
  have hDDi : D * Di = 1 := by
    ext x
    exact e.apply_symm_apply x
  have hDiD : Di * D = 1 := by
    ext x
    exact e.symm_apply_apply x
  refine ⟨Di, hDDi, hDiD, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hDx : D (Di x) = x := by
    have h := congrArg (fun T : H →L[ℂ] H => T x) hDDi
    simpa using h
  have hg := hgap (Di x)
  rw [hDx] at hg
  have hsquare : (σ * ‖Di x‖) ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa [mul_pow] using hg
  have hlinear : σ * ‖Di x‖ ≤ ‖x‖ :=
    (sq_le_sq₀ (mul_nonneg hσ.le (norm_nonneg _)) (norm_nonneg _)).mp hsquare
  calc
    ‖Di x‖ ≤ ‖x‖ / σ := (le_div_iff₀ hσ).2 (by simpa [mul_comm] using hlinear)
    _ = (1 / σ) * ‖x‖ := by ring

/-- Algebraic exponential-corner identity.  If `W,Wi` are inverse weights,
`Dφ=W D Wi`, and the endpoint localizers are weight eigenprojections, then
the unweighted inverse corner is the expected scalar multiple of the
conjugated inverse corner. -/
theorem conjugated_inverse_corner_identity
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (D Di Dφ Dφi W Wi Px Py : A) (wx wy : ℝ)
    (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hDDi : D * Di = 1) (hDiD : Di * D = 1)
    (hconj : Dφ = W * D * Wi)
    (hφinv1 : Dφ * Dφi = 1) (hφinv2 : Dφi * Dφ = 1)
    (hPx : Px * Wi = wx • Px) (hPy : W * Py = wy • Py) :
    Px * Di * Py = (wx * wy) • (Px * Dφi * Py) := by
  have hcandidate1 : Dφ * (W * Di * Wi) = 1 := by
    calc
      Dφ * (W * Di * Wi) = W * D * (Wi * W) * Di * Wi := by
        rw [hconj]
        noncomm_ring
      _ = W * D * Di * Wi := by rw [hWiW, mul_one]
      _ = W * Wi := by rw [mul_assoc W D Di, hDDi, mul_one]
      _ = 1 := hWWi
  have hcandidate2 : (W * Di * Wi) * Dφ = 1 := by
    calc
      (W * Di * Wi) * Dφ = W * Di * (Wi * W) * D * Wi := by
        rw [hconj]
        noncomm_ring
      _ = W * Di * D * Wi := by rw [hWiW, mul_one]
      _ = W * Wi := by rw [mul_assoc W Di D, hDiD, mul_one]
      _ = 1 := hWWi
  have hφi : Dφi = W * Di * Wi := by
    calc
      Dφi = Dφi * 1 := (mul_one _).symm
      _ = Dφi * (Dφ * (W * Di * Wi)) := by rw [hcandidate1]
      _ = (Dφi * Dφ) * (W * Di * Wi) :=
        (mul_assoc Dφi Dφ (W * Di * Wi)).symm
      _ = W * Di * Wi := by rw [hφinv2, one_mul]
  have hDi : Di = Wi * Dφi * W := by
    calc
      Di = 1 * Di * 1 := by simp
      _ = (Wi * W) * Di * (Wi * W) := by rw [hWiW]
      _ = Wi * (W * Di * Wi) * W := by noncomm_ring
      _ = Wi * Dφi * W := by rw [← hφi]
  calc
    Px * Di * Py = (Px * Wi) * Dφi * (W * Py) := by
      rw [hDi]
      noncomm_ring
    _ = (wx • Px) * Dφi * (wy • Py) := by rw [hPx, hPy]
    _ = (wx * wy) • (Px * Dφi * Py) := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm wy wx]

/-- The actual exponential specialization of the corner identity. -/
theorem exponential_corner_identity
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (D Di Dφ Dφi W Wi Px Py : A) (μ φx φy : ℝ)
    (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hDDi : D * Di = 1) (hDiD : Di * D = 1)
    (hconj : Dφ = W * D * Wi)
    (hφinv1 : Dφ * Dφi = 1) (hφinv2 : Dφi * Dφ = 1)
    (hPx : Px * Wi = Real.exp (-μ * φx) • Px)
    (hPy : W * Py = Real.exp (μ * φy) • Py) :
    Px * Di * Py =
      Real.exp (-μ * (φx - φy)) • (Px * Dφi * Py) := by
  rw [conjugated_inverse_corner_identity D Di Dφ Dφi W Wi Px Py
    (Real.exp (-μ * φx)) (Real.exp (μ * φy)) hWWi hWiW hDDi hDiD
    hconj hφinv1 hφinv2 hPx hPy]
  congr 1
  rw [← Real.exp_add]
  congr 1
  ring

/-- Complete finite Combes--Thomas compiler from the primary square-gap and
conjugation data.  Both inverses are constructed, and the localized inverse
corner receives the manuscript's exponential bound. -/
theorem finite_dirac_combes_thomas
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (D Dφ E W Wi Px Py : H →L[ℂ] H)
    (σ b μ φx φy δ : ℝ)
    (hσ : 0 < σ) (hb : 0 ≤ b) (hbσ : b < σ)
    (hgap : ∀ x : H, σ ^ 2 * ‖x‖ ^ 2 ≤ ‖D x‖ ^ 2)
    (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hconj : Dφ = W * D * Wi) (hperturb : Dφ = D + E)
    (hE : ‖E‖ ≤ b) (hPxNorm : ‖Px‖ ≤ 1) (hPyNorm : ‖Py‖ ≤ 1)
    (hμ : 0 ≤ μ) (hδ : 0 ≤ δ) (hφ : φx - φy = δ)
    (hPx : Px * Wi = Real.exp (-μ * φx) • Px)
    (hPy : W * Py = Real.exp (μ * φy) • Py) :
    ∃ Di Dφi : H →L[ℂ] H,
      D * Di = 1 ∧ Di * D = 1 ∧ ‖Di‖ ≤ 1 / σ ∧
      Dφ * Dφi = 1 ∧ Dφi * Dφ = 1 ∧
      ‖Px * Di * Py‖ ≤ Real.exp (-μ * δ) / (σ - b) := by
  obtain ⟨Di, hDDi, hDiD, hDiNorm⟩ := inverse_of_square_gap D σ hσ hgap
  let Dφi : H →L[ℂ] H := W * Di * Wi
  have hDφi1 : Dφ * Dφi = 1 := by
    calc
      Dφ * Dφi = W * D * (Wi * W) * Di * Wi := by
        simp only [Dφi]
        rw [hconj]
        noncomm_ring
      _ = W * D * Di * Wi := by rw [hWiW, mul_one]
      _ = W * Wi := by rw [mul_assoc W D Di, hDDi, mul_one]
      _ = 1 := hWWi
  have hDφi2 : Dφi * Dφ = 1 := by
    calc
      Dφi * Dφ = W * Di * (Wi * W) * D * Wi := by
        simp only [Dφi]
        rw [hconj]
        noncomm_ring
      _ = W * Di * D * Wi := by rw [hWiW, mul_one]
      _ = W * Wi := by rw [mul_assoc W Di D, hDiD, mul_one]
      _ = 1 := hWWi
  have hcorner : Px * Di * Py =
      Real.exp (-μ * δ) • (Px * Dφi * Py) := by
    have h := exponential_corner_identity D Di Dφ Dφi W Wi Px Py
      μ φx φy hWWi hWiW hDDi hDiD hconj hDφi1 hDφi2 hPx hPy
    rwa [hφ] at h
  have hsum1 : (D + E) * Dφi = 1 := by
    rw [← hperturb]
    exact hDφi1
  have hsum2 : Dφi * (D + E) = 1 := by
    rw [← hperturb]
    exact hDφi2
  have hbound : ‖Px * Di * Py‖ ≤
      Real.exp (-μ * δ) / (σ - b) :=
    exponential_conjugation_corner_decay D E Di Dφi Px Py σ b μ δ
      hσ hb hbσ hDDi hDiD hDiNorm hE
      hsum1 hsum2
      hPxNorm hPyNorm hμ hδ hcorner
  exact ⟨Di, Dφi, hDDi, hDiD, hDiNorm, hDφi1, hDφi2, hbound⟩

end FiniteTypeDiracCombesThomas
end NCG
