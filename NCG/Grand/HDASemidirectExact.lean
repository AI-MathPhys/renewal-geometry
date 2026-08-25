/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite HDA: the `DH` bracket from semidirect naturality

Analysis layer for `thm:finite-HDA` (H5): differentiating the exponentiated
semidirect naturality law
`R_h(e^{sv}) U_h(N,t) R_h(e^{sv})^{-1} = U_h(ρ_h(e^{sv})N, t)`
yields the `DH` bracket with unit amplitude.

* `generator_ext`: two one-parameter groups with the same orbit have the same
  generator — differentiation at `t = 0`;
* `exp_smul_neg_mul`: `e^{sX} e^{-sX} = 1`;
* `conj_of_naturality`: for every `s`, the naturality law forces the exact
  conjugation identity
  `e^{-isD_v} (−iH_N) e^{isD_v} = −i H_{ρ_s N}` of the generators;
* `dh_bracket`: **the `DH` identity** — differentiating the conjugation
  identity at `s = 0` gives `−i[D_v, H_N] = H_{ℓ(v)N}`, where `H_{ℓ(v)N}` is
  the derivative of the lapse flow `s ↦ H_{ρ_s N}` at `s = 0`.

Stated on a complex Banach algebra; the finite physical carrier (a matrix
algebra with any of its equivalent norms) is an instance.
-/

open NormedSpace

namespace NCG
namespace HDASemidirect

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]
  [SMulCommClass ℝ ℂ 𝔸] [CompleteSpace 𝔸]

/-- The rational Banach-algebra structure obtained by restriction, driving the
norm-free exponential lemmas (the same device as Mathlib's `CStarAlgebra`
exponential files). -/
@[instance_reducible]
noncomputable def ratAlgebra : NormedAlgebra ℚ 𝔸 :=
  NormedAlgebra.restrictScalars ℚ ℂ 𝔸

attribute [local instance] ratAlgebra

omit [SMulCommClass ℝ ℂ 𝔸] in
/-- Two one-parameter groups with the same orbit have the same generator. -/
theorem generator_ext {A B : 𝔸} (h : ∀ t : ℝ, exp (t • A) = exp (t • B)) :
    A = B := by
  have hA : HasDerivAt (fun t : ℝ => exp (t • A))
      (exp ((0 : ℝ) • A) * A) 0 := hasDerivAt_exp_smul_const A (0 : ℝ)
  have hB : HasDerivAt (fun t : ℝ => exp (t • B))
      (exp ((0 : ℝ) • B) * B) 0 := hasDerivAt_exp_smul_const B (0 : ℝ)
  have hfun : (fun t : ℝ => exp (t • A)) = fun t : ℝ => exp (t • B) :=
    funext h
  rw [hfun] at hA
  have huni := hA.unique hB
  simpa [zero_smul, exp_zero, one_mul] using huni

omit [SMulCommClass ℝ ℂ 𝔸] in
/-- `e^{sX} e^{-sX} = 1`. -/
theorem exp_smul_neg_mul (X : 𝔸) (s : ℝ) :
    exp (s • X) * exp (s • (-X)) = 1 := by
  have hcomm : Commute (s • X) (s • (-X)) :=
    (((Commute.refl X).neg_right).smul_left s).smul_right s
  rw [← exp_add_of_commute hcomm, smul_neg, add_neg_cancel, exp_zero]

omit [SMulCommClass ℝ ℂ 𝔸] in
/-- **The conjugation identity of generators**: the exponentiated semidirect
naturality law forces, for every flow time `s`, the exact conjugation
`e^{-isD_v} (−iH_N) e^{isD_v} = −i H_{ρ_s N}`. -/
theorem conj_of_naturality (Dv HN : 𝔸) (Hρ : ℝ → 𝔸)
    (hnat : ∀ s t : ℝ,
      exp (s • (-Complex.I • Dv)) * exp (t • (-Complex.I • HN))
          * exp (s • (Complex.I • Dv))
        = exp (t • (-Complex.I • Hρ s))) (s : ℝ) :
    exp (s • (-Complex.I • Dv)) * (-Complex.I • HN)
        * exp (s • (Complex.I • Dv))
      = -Complex.I • Hρ s := by
  have hXX : exp (s • (-Complex.I • Dv)) * exp (s • (Complex.I • Dv)) = 1 := by
    have h := exp_smul_neg_mul (-Complex.I • Dv) s
    simpa [neg_smul, neg_neg] using h
  have hXX' : exp (s • (Complex.I • Dv)) * exp (s • (-Complex.I • Dv)) = 1 := by
    have h := exp_smul_neg_mul (Complex.I • Dv) s
    simpa [neg_smul] using h
  apply generator_ext
  intro t
  calc exp (t • (exp (s • (-Complex.I • Dv)) * (-Complex.I • HN)
        * exp (s • (Complex.I • Dv))))
      = exp (exp (s • (-Complex.I • Dv)) * (t • (-Complex.I • HN))
          * exp (s • (Complex.I • Dv))) := by
        congr 1
        simp only [mul_smul_comm, smul_mul_assoc]
    _ = exp (s • (-Complex.I • Dv)) * exp (t • (-Complex.I • HN))
          * exp (s • (Complex.I • Dv)) :=
        exp_units_conj
          ⟨exp (s • (-Complex.I • Dv)), exp (s • (Complex.I • Dv)), hXX, hXX'⟩
          (t • (-Complex.I • HN))
    _ = exp (t • (-Complex.I • Hρ s)) := hnat s t

/-- **The `DH` bracket (H5)**: differentiating the conjugation identity at
`s = 0` gives `−i[D_v, H_N] = H_{ℓ(v)N}`, where `H_{ℓ(v)N}` is the derivative
of the lapse flow `s ↦ H_{ρ_s N}` at `s = 0`. -/
theorem dh_bracket (Dv HN HℓN : 𝔸) (Hρ : ℝ → 𝔸)
    (hnat : ∀ s t : ℝ,
      exp (s • (-Complex.I • Dv)) * exp (t • (-Complex.I • HN))
          * exp (s • (Complex.I • Dv))
        = exp (t • (-Complex.I • Hρ s)))
    (hρderiv : HasDerivAt Hρ HℓN 0) :
    -Complex.I • (Dv * HN - HN * Dv) = HℓN := by
  have hconj := conj_of_naturality Dv HN Hρ hnat
  have hd1 : HasDerivAt (fun s : ℝ => exp (s • (-Complex.I • Dv)))
      (exp ((0 : ℝ) • (-Complex.I • Dv)) * (-Complex.I • Dv)) 0 :=
    hasDerivAt_exp_smul_const (-Complex.I • Dv) (0 : ℝ)
  have hd2 : HasDerivAt (fun s : ℝ => exp (s • (Complex.I • Dv)))
      (exp ((0 : ℝ) • (Complex.I • Dv)) * (Complex.I • Dv)) 0 :=
    hasDerivAt_exp_smul_const (Complex.I • Dv) (0 : ℝ)
  simp only [zero_smul, exp_zero, one_mul] at hd1 hd2
  have hd3 : HasDerivAt
      (fun s : ℝ => (-Complex.I • HN) * exp (s • (Complex.I • Dv)))
      ((-Complex.I • HN) * (Complex.I • Dv)) 0 :=
    hd2.const_mul (-Complex.I • HN)
  have hmul := hd1.mul hd3
  simp only [zero_smul, exp_zero, mul_one, one_mul] at hmul
  have hfun : ((fun s : ℝ => exp (s • (-Complex.I • Dv)))
      * fun s : ℝ => (-Complex.I • HN) * exp (s • (Complex.I • Dv)))
      = fun s : ℝ => -Complex.I • Hρ s := by
    funext s
    simp only [Pi.mul_apply]
    rw [← mul_assoc, hconj s]
  rw [hfun] at hmul
  have hdG : HasDerivAt (fun s : ℝ => -Complex.I • Hρ s)
      (-Complex.I • HℓN) 0 := hρderiv.const_smul (-Complex.I)
  have hval := hmul.unique hdG
  have hsimp : (-Complex.I • Dv) * (-Complex.I • HN)
      + (-Complex.I • HN) * (Complex.I • Dv)
      = -(Dv * HN) + HN * Dv := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, neg_mul, mul_neg,
      Complex.I_mul_I, neg_neg, one_smul, neg_one_smul]
  rw [hsimp] at hval
  have hI := congrArg (fun M : 𝔸 => Complex.I • M) hval
  simp only [smul_add, smul_neg, smul_smul, mul_neg, Complex.I_mul_I,
    neg_neg, one_smul] at hI
  rw [← hI, smul_sub]
  module

end HDASemidirect
end NCG
