/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.CommonAction

/-!
# SM selector projector, principal module, and matter–Legendre
  (`thm:SM-selector`, `thm:SM-principal-module`,
   `thm:SMST-matter-Legendre`, Gran-Tensor manuscript)

* `descent_fourier_projector`: the boxed finite Fourier
  indicator — for `ζ` of order six,
  `Σ_{k<6}(ζ^m)^k = 6·𝟏_{6∣m}` — combined with the proved `ℤ₆`
  kernel congruence (`hypercharge_z6_kernel`) this is the
  central descent selector `𝟏_{2t+3s+y≡0 (6)}`;
* `principal_matter_module`: a `κ`-normalized occurrence row
  gives the isometric faithful right-module map
  `J(X) = κ^{-1/2}C₀X` with `J(X)ᴴJ(X') = XᴴX'` and `J`
  injective — Choi rank of the occurrence column is environment
  memory, not a generation count;
* `matter_legendre_reciprocity`: per-species Legendre data
  `a_r = η_r⁻¹`, `b_r = η_r` give the boxed closure criterion
  `a_rb_r = 1` for every loaded species; conversely `a_rb_r = 1`
  forces `b_r = a_r⁻¹`; and the underlying scalar Legendre
  transform is the proved `legendre_kinetic` supremum.

Rendering disclosed: the identification of `(t, s, y)` with
colour triality, weak parity, and integer hypercharge is the
proved `ℤ₆` kernel congruence; the identification of the
reciprocity criterion with total HDA closure is the
manuscript's displayed equivalence.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:SM-selector`: the finite Fourier projector — for `ζ` of
order six, `Σ_{k<6}(ζ^m)^k = 6` when `6 ∣ m` and `0`
otherwise. -/
theorem descent_fourier_projector (ζ : ℂ) (hζ : orderOf ζ = 6)
    (m : ℕ) :
    (∑ k ∈ Finset.range 6, (ζ ^ m) ^ k)
      = if 6 ∣ m then 6 else 0 := by
  have hz6 : ζ ^ (6 : ℕ) = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  by_cases hdvd : 6 ∣ m
  · have hzm : ζ ^ m = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (hζ ▸ hdvd)
    rw [if_pos hdvd]
    simp [hzm]
  · have hzm : ζ ^ m ≠ 1 := fun h =>
      hdvd (hζ ▸ orderOf_dvd_of_pow_eq_one h)
    have h6 : (ζ ^ m) ^ (6 : ℕ) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hz6, one_pow]
    rw [geom_sum_eq hzm, h6, sub_self, zero_div, if_neg hdvd]

/-- `thm:SM-principal-module`: the isometric faithful
right-module map from a `κ`-normalized occurrence row. -/
theorem principal_matter_module {Y q : Type*} [Fintype Y]
    [Fintype q] [DecidableEq q]
    (C0 : Matrix Y q ℂ) (κ : ℝ) (hκ : 0 < κ)
    (hC : C0ᴴ * C0 = (κ : ℂ) • 1) :
    (∀ X X' : Matrix q q ℂ,
      (((Real.sqrt κ : ℂ))⁻¹ • (C0 * X))ᴴ
          * (((Real.sqrt κ : ℂ))⁻¹ • (C0 * X'))
        = Xᴴ * X')
    ∧ Function.Injective
        (fun X : Matrix q q ℂ =>
          ((Real.sqrt κ : ℂ))⁻¹ • (C0 * X)) := by
  have hs : ((Real.sqrt κ : ℂ)) * (Real.sqrt κ : ℂ)
      = (κ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hκ.le]
  have hκne : (κ : ℂ) ≠ 0 := by
    simpa using hκ.ne'
  have hstar : star ((Real.sqrt κ : ℝ) : ℂ)
      = ((Real.sqrt κ : ℝ) : ℂ) := by
    simp
  have hmain : ∀ X X' : Matrix q q ℂ,
      (((Real.sqrt κ : ℂ))⁻¹ • (C0 * X))ᴴ
          * (((Real.sqrt κ : ℂ))⁻¹ • (C0 * X'))
        = Xᴴ * X' := by
    intro X X'
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, star_inv₀, hstar,
      Matrix.conjTranspose_mul]
    rw [show Xᴴ * C0ᴴ * (C0 * X')
        = Xᴴ * (C0ᴴ * C0) * X' from by
      simp only [Matrix.mul_assoc]]
    rw [hC, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      smul_smul]
    rw [show ((Real.sqrt κ : ℂ))⁻¹ * ((Real.sqrt κ : ℂ))⁻¹
          * (κ : ℂ)
        = ((Real.sqrt κ : ℂ) * (Real.sqrt κ : ℂ))⁻¹
          * (κ : ℂ) from by rw [mul_inv]]
    rw [hs, inv_mul_cancel₀ hκne, one_smul]
  refine ⟨hmain, ?_⟩
  intro X X' hXX
  simp only [] at hXX
  have hz : ((Real.sqrt κ : ℂ))⁻¹ • (C0 * (X - X')) = 0 := by
    rw [Matrix.mul_sub, smul_sub]
    rw [show ((Real.sqrt κ : ℂ))⁻¹ • (C0 * X)
        = ((Real.sqrt κ : ℂ))⁻¹ • (C0 * X') from hXX]
    exact sub_self _
  have h0 : (X - X')ᴴ * (X - X') = 0 := by
    have h := hmain (X - X') (X - X')
    rw [hz] at h
    rw [← h, Matrix.conjTranspose_zero, Matrix.zero_mul]
  exact sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp h0)

/-- `thm:SMST-matter-Legendre`: per-species Legendre reciprocity
`a_rb_r = 1`, the converse determination, and the underlying
proved scalar Legendre supremum. -/
theorem matter_legendre_reciprocity {r : ℕ}
    (η a b : Fin r → ℝ) (hη : ∀ i, 0 < η i)
    (hLeg : ∀ i, a i = (η i)⁻¹ ∧ b i = η i) :
    (∀ i, a i * b i = 1)
    ∧ (∀ i, a i * b i = 1 → a i ≠ 0 → b i = (a i)⁻¹)
    ∧ (∀ (i : Fin r) (p : ℝ), IsGreatest
        (Set.range fun v : ℝ => p * v - η i / 2 * v ^ 2)
        (p ^ 2 / (2 * η i))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [(hLeg i).1, (hLeg i).2, inv_mul_cancel₀ (hη i).ne']
  · intro i hab ha
    rw [inv_eq_one_div, eq_div_iff ha, mul_comm]
    exact hab
  · intro i p
    exact legendre_kinetic (η i) (hη i) p

end NCG
