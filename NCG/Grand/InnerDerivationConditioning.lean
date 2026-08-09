/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.NaimarkPhaseSharpness

/-!
# conditioning of inner derivations

This file expands the commutator on every matrix unit, proves the exact
superoperator Hilbert--Schmidt identity, and derives the traceless
`sqrt (2d)` scaling and injectivity clauses.
-/

open Matrix Finset

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]

def adSuperHSSq (H : Matrix d d ℂ) : ℝ :=
  ∑ a, ∑ b, hsFrobSq
    (H * Matrix.single a b 1 - Matrix.single a b 1 * H)

lemma ad_matrix_unit_hs (H : Matrix d d ℂ) (hH : Hᴴ = H) (a b : d) :
    hsFrobSq (H * Matrix.single a b 1 - Matrix.single a b 1 * H)
      = ((H * H) a a).re + ((H * H) b b).re
          - 2 * (H a a * H b b).re := by
  let Eab : Matrix d d ℂ := Matrix.single a b 1
  let Eba : Matrix d d ℂ := Matrix.single b a 1
  have hEstar : Eabᴴ = Eba := by
    simp [Eab, Eba, Matrix.conjTranspose_single]
  have h1 : Matrix.trace (Eba * H * H * Eab) = (H * H) a a := by
    calc
      Matrix.trace (Eba * H * H * Eab)
          = Matrix.trace (Eba * (H * H) * Eab) := by
              congr 1
              simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Matrix.single b b ((H * H) a a)) := by
              simp only [Eba, Eab]
              rw [Matrix.single_mul_mul_single]
              simp
      _ = (H * H) a a := by simp
  have h2 : Matrix.trace (Eba * H * Eab * H) = H a a * H b b := by
    calc
      Matrix.trace (Eba * H * Eab * H)
          = Matrix.trace ((Eba * H * Eab) * H) := by rfl
      _ = Matrix.trace (Matrix.single b b (H a a) * H) := by
              simp only [Eba, Eab]
              rw [Matrix.single_mul_mul_single]
              simp
      _ = H a a * H b b := by
              rw [Matrix.trace_single_mul]
              simp
  have h3 : Matrix.trace (H * Eba * H * Eab) = H a a * H b b := by
    calc
      Matrix.trace (H * Eba * H * Eab)
          = Matrix.trace (H * (Eba * H * Eab)) := by
              congr 1
              simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Eba * H * Eab) * H) := Matrix.trace_mul_comm _ _
      _ = H a a * H b b := h2
  have h4 : Matrix.trace (H * Eba * Eab * H) = (H * H) b b := by
    calc
      Matrix.trace (H * Eba * Eab * H)
          = Matrix.trace (H * (Eba * Eab * H)) := by
              congr 1
              simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Eba * Eab * H) * H) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Matrix.single b b 1 * (H * H)) := by
              congr 1
              simp [Eba, Eab, Matrix.mul_assoc]
      _ = (H * H) b b := by
              rw [Matrix.trace_single_mul]
              simp
  rw [hsFrobSq_eq_re_trace]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hEstar, hH]
  change (Matrix.trace ((Eba * H - H * Eba) * (H * Eab - Eab * H))).re = _
  rw [show (Eba * H - H * Eba) * (H * Eab - Eab * H)
      = Eba * H * H * Eab - Eba * H * Eab * H
          - H * Eba * H * Eab + H * Eba * Eab * H by noncomm_ring]
  rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, Complex.sub_re, h1, h2, h3, h4]
  ring

theorem adSuperHSSq_expansion (H : Matrix d d ℂ) (hH : Hᴴ = H) :
    adSuperHSSq H =
      2 * Fintype.card d * hsFrobSq H - 2 * Complex.normSq (Matrix.trace H) := by
  have hdiag : ∑ a, ((H * H) a a).re = hsFrobSq H := by
    rw [hsFrobSq_eq_re_trace, hH]
    simp [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  have htrstar : star (Matrix.trace H) = Matrix.trace H := by
    rw [← Matrix.trace_conjTranspose, hH]
  have hmix : ∑ a, ∑ b, (H a a * H b b).re
      = Complex.normSq (Matrix.trace H) := by
    calc
      ∑ a, ∑ b, (H a a * H b b).re
          = (∑ a, ∑ b, H a a * H b b).re := by
              simp only [Complex.re_sum]
      _ = (Matrix.trace H * Matrix.trace H).re := by
              congr 1
              simp only [← Finset.mul_sum, ← Finset.sum_mul]
              rfl
      _ = (Matrix.trace H * star (Matrix.trace H)).re := by rw [htrstar]
      _ = Complex.normSq (Matrix.trace H) := by
              rw [Complex.star_def, Complex.mul_conj]
              simp
  rw [adSuperHSSq]
  simp_rw [ad_matrix_unit_hs H hH]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, hdiag, hmix,
    nsmul_eq_mul]
  ring

theorem hsFrobSq_center_trace [Nonempty d]
    (H : Matrix d d ℂ) (hH : Hᴴ = H) :
    hsFrobSq (H - ((Matrix.trace H / (Fintype.card d : ℂ)) • 1))
      = hsFrobSq H - Complex.normSq (Matrix.trace H) / Fintype.card d := by
  let t : ℂ := Matrix.trace H
  let n : ℝ := Fintype.card d
  let α : ℂ := t / (n : ℂ)
  have hn0 : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast Fintype.card_ne_zero
  have htstar : star t = t := by
    calc
      star t = star (Matrix.trace H) := rfl
      _ = Matrix.trace Hᴴ := (Matrix.trace_conjTranspose H).symm
      _ = Matrix.trace H := congrArg Matrix.trace hH
      _ = t := rfl
  have hαstar : star α = α := by
    simp [α, htstar]
  have hKstar : (H - α • (1 : Matrix d d ℂ))ᴴ = H - α • 1 := by
    rw [Matrix.conjTranspose_sub, hH, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hαstar]
  change hsFrobSq (H - α • 1) = hsFrobSq H - Complex.normSq t / n
  rw [hsFrobSq_eq_re_trace, hKstar, hsFrobSq_eq_re_trace, hH]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, smul_eq_mul]
  rw [Matrix.trace_one]
  change (Matrix.trace (H * H)).re - (α * t).re
      - (α * (t - α * (n : ℂ))).re
      = (Matrix.trace (H * H)).re - Complex.normSq t / n
  have htIm : t.im = 0 := by
    have him := congrArg Complex.im htstar
    simp at him
    linarith
  have htNorm : Complex.normSq t = t.re ^ 2 := by
    rw [Complex.normSq_apply, htIm]
    ring
  have htEq : t = (t.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using htIm
  rw [htNorm]
  dsimp [α]
  rw [htEq]
  simp
  field_simp

theorem inner_derivation_norm_exact [Nonempty d]
    (H : Matrix d d ℂ) (hH : Hᴴ = H) :
    adSuperHSSq H =
      2 * Fintype.card d *
        hsFrobSq (H - ((Matrix.trace H / (Fintype.card d : ℂ)) • 1)) := by
  rw [adSuperHSSq_expansion H hH, hsFrobSq_center_trace H hH]
  have hn0 : (Fintype.card d : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

noncomputable def matrixHSNorm (H : Matrix d d ℂ) : ℝ := Real.sqrt (hsFrobSq H)

noncomputable def adSuperHSNorm (H : Matrix d d ℂ) : ℝ := Real.sqrt (adSuperHSSq H)

theorem inner_derivation_traceless_scaling [Nonempty d]
    (H : Matrix d d ℂ) (hH : Hᴴ = H) (htr : Matrix.trace H = 0) :
    adSuperHSSq H = 2 * Fintype.card d * hsFrobSq H := by
  rw [inner_derivation_norm_exact H hH, htr]
  simp

theorem inner_derivation_traceless_norm [Nonempty d]
    (H : Matrix d d ℂ) (hH : Hᴴ = H) (htr : Matrix.trace H = 0) :
    adSuperHSNorm H = Real.sqrt (2 * Fintype.card d) * matrixHSNorm H := by
  rw [adSuperHSNorm, matrixHSNorm, inner_derivation_traceless_scaling H hH htr]
  rw [Real.sqrt_mul (by positivity)]

theorem inner_derivation_injective_on_traceless [Nonempty d]
    (H K : Matrix d d ℂ) (hH : Hᴴ = H) (hK : Kᴴ = K)
    (htrH : Matrix.trace H = 0) (htrK : Matrix.trace K = 0)
    (had : ∀ a b,
      H * Matrix.single a b 1 - Matrix.single a b 1 * H
        = K * Matrix.single a b 1 - Matrix.single a b 1 * K) :
    H = K := by
  let B : Matrix d d ℂ := H - K
  have hBstar : Bᴴ = B := by
    simp [B, Matrix.conjTranspose_sub, hH, hK]
  have hBtr : Matrix.trace B = 0 := by
    simp [B, Matrix.trace_sub, htrH, htrK]
  have hunit : ∀ a b,
      B * Matrix.single a b 1 - Matrix.single a b 1 * B = 0 := by
    intro a b
    calc
      B * Matrix.single a b 1 - Matrix.single a b 1 * B
          = (H * Matrix.single a b 1 - Matrix.single a b 1 * H)
              - (K * Matrix.single a b 1 - Matrix.single a b 1 * K) := by
                dsimp [B]
                noncomm_ring
      _ = 0 := sub_eq_zero.mpr (had a b)
  have had0 : adSuperHSSq B = 0 := by
    rw [adSuperHSSq]
    simp_rw [hunit]
    simp [hsFrobSq]
  have hscale := inner_derivation_traceless_scaling B hBstar hBtr
  rw [had0] at hscale
  have hcard : (0 : ℝ) < Fintype.card d := by
    exact_mod_cast Fintype.card_pos
  have hhs : hsFrobSq B = 0 := by
    nlinarith [hsFrobSq_nonneg B]
  have hB0 : B = 0 := (hsFrobSq_eq_zero_iff B).mp hhs
  exact sub_eq_zero.mp hB0

end NCG
