/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Vacuum Doob transfer as a Koopman compression, and the
  invariant/fixed-free arm
  (`thm:YM-Doob-Koopman` and `cor:YM-no-character-arm`,
  Gran-Tensor manuscript)

* `ym_doob_koopman_dirichlet`: the boxed Dirichlet-form
  identity — for a Koopman dilation packet
  (`J` isometry, `U` unitary, compression `J*UJ = 𝒫` with
  `𝒫` self-adjoint), the augmentation energy compresses
  exactly to twice the transfer Dirichlet form:
  `J*(U-1)*(U-1)J = 2(1-𝒫)`.

* `ym_no_character_arm`: a positive self-adjoint
  contraction has no unit-circle spectral value other
  than `1` — a real eigenvalue `c` of modulus one of a map
  with `0 ≤ ⟨x,𝒫x⟩ ≤ ‖x‖²` is `c = 1` — so a positive
  Yang–Mills transfer cannot supply a nontrivial
  predictive character; its protected decomposition is the
  vacuum fixed sector plus the fixed-free complement
  (`NCG.gt_fixed_coboundary`).

The construction of the packet — the Doob transform
`𝒫f = Ω⁻¹T(Ωf)` being a self-adjoint Markov contraction
on `L²(μ)`, the stationary two-sided path law, and the
full `n`-step compression `J*UⁿJ = 𝒫ⁿ` — is the
manuscript's probabilistic dilation layer.
-/

open Matrix
open scoped InnerProductSpace

namespace NCG

set_option linter.unusedFintypeInType false in
/-- `thm:YM-Doob-Koopman` (the boxed augmentation-energy
identity from the dilation packet). -/
theorem ym_doob_koopman_dirichlet {N M : Type} [Fintype N]
    [Fintype M] [DecidableEq N] [DecidableEq M]
    (J : Matrix N M ℂ) (U : Matrix N N ℂ)
    (P : Matrix M M ℂ)
    (hJ : Jᴴ * J = 1) (hU : Uᴴ * U = 1)
    (hP : Jᴴ * (U * J) = P) (hPH : Pᴴ = P) :
    Jᴴ * ((U - 1)ᴴ * ((U - 1) * J)) = (2 : ℂ) • (1 - P)
    := by
  have hUJ : Jᴴ * (Uᴴ * J) = P := by
    have h := congrArg conjTranspose hP
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hPH] at h
    rw [← h, Matrix.mul_assoc]
  have hexp : (U - 1)ᴴ * ((U - 1) * J)
      = (2 : ℂ) • J - U * J - Uᴴ * J := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    simp only [Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul]
    rw [← Matrix.mul_assoc, hU]
    simp only [Matrix.one_mul]
    rw [two_smul]
    abel
  rw [hexp]
  simp only [Matrix.mul_sub, Matrix.mul_smul]
  rw [hJ, hP, hUJ, smul_sub, two_smul, two_smul]
  abel

/-- `cor:YM-no-character-arm`: a positive self-adjoint
contraction has no unit-circle value except `1`. -/
theorem ym_no_character_arm {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →ₗ[ℝ] V)
    (hpsd : ∀ x, 0 ≤ ⟪x, P x⟫_ℝ)
    (hcontr : ∀ x, ⟪x, P x⟫_ℝ ≤ ‖x‖ ^ 2)
    (c : ℝ) (x : V) (hx : x ≠ 0)
    (heig : P x = c • x) (habs : |c| = 1) :
    c = 1 := by
  have hnx : 0 < ‖x‖ ^ 2 := by
    have := norm_pos_iff.mpr hx
    positivity
  have hval : ⟪x, P x⟫_ℝ = c * ‖x‖ ^ 2 := by
    rw [heig, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  have h0 : 0 ≤ c * ‖x‖ ^ 2 := hval ▸ hpsd x
  have h1 : c * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 := hval ▸ hcontr x
  have hc0 : 0 ≤ c := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hc1 : c ≤ 1 := by
    by_contra hgt
    push Not at hgt
    nlinarith
  rcases abs_cases c with ⟨he, _⟩ | ⟨he, hneg⟩
  · rw [← he, habs]
  · linarith [habs ▸ he, hc0]

end NCG
