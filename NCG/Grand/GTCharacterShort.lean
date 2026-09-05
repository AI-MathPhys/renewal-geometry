/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Character projection commutes with invariant shorting
  (`thm:GT-character-short`, Gran-Tensor manuscript)

* `gt_character_short`: for a unitary action `U` of a
  finite abelian group commuting with the invertible
  action `L`, and unimodular characters `χ ≠ ψ`, the
  character projections
  `P_χ = |G|⁻¹ ∑ χ(g)* U(g)` satisfy:
  (i) `L⁻¹` commutes with every `P_χ` (so every
      action-dressed Gram is block diagonal by character);
  (ii) the covariance `U(g)P_ψ = ψ(g)P_ψ`;
  (iii) distinct character projections annihilate,
      `P_χ P_ψ = 0` (character orthogonality, proved from
      the shift trick);
  (iv) `P_χ` is hermitian; and
  (v) the boxed `A*L†Z = 0` — a trivial-χ-character source
      and a ψ-character source have zero dressed overlap.

The pseudoinverse formulation (`L†` on `Ran L`), the
nuisance-shorted action, and the identification of the
character sources inside `Ran L` are the manuscript's
range bookkeeping; with invertible `L` the boxed overlap
is exact.
-/

open Matrix Finset

namespace NCG

/-- `thm:GT-character-short`. -/
theorem gt_character_short {G : Type} [Fintype G]
    [CommGroup G] {n : Type} [Fintype n] [DecidableEq n]
    (U : G → Matrix n n ℂ)
    (hU : ∀ g h, U (g * h) = U g * U h)
    (hUH : ∀ g, (U g)ᴴ = U g⁻¹)
    (χ ψ : G → ℂ)
    (hχ : ∀ g h, χ (g * h) = χ g * χ h)
    (hψ : ∀ g h, ψ (g * h) = ψ g * ψ h)
    (hχu : ∀ g, star (χ g) * χ g = 1)
    (hψu : ∀ g, star (ψ g) * ψ g = 1)
    (L : Matrix n n ℂ) [Invertible L]
    (hLU : ∀ g, L * U g = U g * L)
    (hne : ∃ g₀, χ g₀ ≠ ψ g₀) :
    -- (i) L⁻¹ commutes with the character projection
    (L⁻¹ * ((Fintype.card G : ℂ)⁻¹
        • ∑ g, star (χ g) • U g)
      = ((Fintype.card G : ℂ)⁻¹
        • ∑ g, star (χ g) • U g) * L⁻¹)
    -- (ii) the character covariance of the action
    ∧ (∀ g, U g * ((Fintype.card G : ℂ)⁻¹
        • ∑ h, star (ψ h) • U h)
      = ψ g • ((Fintype.card G : ℂ)⁻¹
        • ∑ h, star (ψ h) • U h))
    -- (iii) distinct character projections annihilate
    ∧ (((Fintype.card G : ℂ)⁻¹
        • ∑ g, star (χ g) • U g)
      * ((Fintype.card G : ℂ)⁻¹
        • ∑ h, star (ψ h) • U h) = 0)
    -- (iv) the character projection is hermitian
    ∧ (((Fintype.card G : ℂ)⁻¹
        • ∑ g, star (χ g) • U g)ᴴ
      = (Fintype.card G : ℂ)⁻¹
        • ∑ g, star (χ g) • U g)
    -- (v) the boxed A* L† Z = 0
    ∧ (∀ {k m : Type} [Fintype k] [Fintype m]
        (A : Matrix n k ℂ) (Z : Matrix n m ℂ),
        ((Fintype.card G : ℂ)⁻¹
          • ∑ g, star (χ g) • U g) * A = A →
        ((Fintype.card G : ℂ)⁻¹
          • ∑ h, star (ψ h) • U h) * Z = Z →
        Aᴴ * (L⁻¹ * Z) = 0) := by
  set c : ℂ := (Fintype.card G : ℂ)⁻¹ with hc
  set Pχ := c • ∑ g, star (χ g) • U g with hPχ
  set Pψ := c • ∑ h, star (ψ h) • U h with hPψ
  -- unimodular characters invert by conjugation
  have hχinv : ∀ g, star (χ g) = (χ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_left (hχu g)
  have hψinv : ∀ g, star (ψ g) = (ψ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_left (hψu g)
  have hχ0 : ∀ g, χ g ≠ 0 := by
    intro g hg
    have h := hχu g
    rw [hg, mul_zero] at h
    exact one_ne_zero h.symm
  have hψ0 : ∀ g, ψ g ≠ 0 := by
    intro g hg
    have h := hψu g
    rw [hg, mul_zero] at h
    exact one_ne_zero h.symm
  have hψ1 : ψ 1 = 1 := by
    have h := hψ 1 1
    rw [one_mul] at h
    exact (mul_left_cancel₀ (hψ0 1)
      (by rw [mul_one, ← h])).symm
  have hψginv : ∀ g, ψ g⁻¹ = (ψ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_right
      (by rw [← hψ, mul_inv_cancel, hψ1])
  have hχ1 : χ 1 = 1 := by
    have h := hχ 1 1
    rw [one_mul] at h
    exact (mul_left_cancel₀ (hχ0 1)
      (by rw [mul_one, ← h])).symm
  have hχginv : ∀ g, χ g⁻¹ = (χ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_right
      (by rw [← hχ, mul_inv_cancel, hχ1])
  -- (ii) covariance
  have hcov : ∀ g, U g * Pψ = ψ g • Pψ := by
    intro g
    rw [hPψ, Matrix.mul_smul, Matrix.mul_sum]
    rw [smul_comm]
    congr 1
    calc ∑ h, U g * (star (ψ h) • U h)
        = ∑ h, star (ψ h) • U (g * h) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Matrix.mul_smul, hU]
      _ = ∑ x, star (ψ (g⁻¹ * x)) • U x := by
          refine Fintype.sum_equiv (Equiv.mulLeft g)
            _ _ fun x => ?_
          simp only [Equiv.coe_mulLeft]
          rw [show g⁻¹ * (g * x) = x by group]
      _ = ψ g • ∑ h, star (ψ h) • U h := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hψ, star_mul', smul_smul]
          congr 1
          rw [hψginv, star_inv₀, hψinv, inv_inv]
  -- character orthogonality
  have horth : ∑ g, star (χ g) * ψ g = 0 := by
    obtain ⟨g₀, hg₀⟩ := hne
    set φ : G → ℂ := fun g => star (χ g) * ψ g with hφ
    have hφmul : ∀ g h, φ (g * h) = φ g * φ h := by
      intro g h
      simp only [φ, hχ, hψ, star_mul']
      ring
    have hφne : φ g₀ ≠ 1 := by
      intro hcontra
      have hs : star (χ g₀) ≠ 0 := by
        intro hz
        have h2 := hχu g₀
        rw [hz, zero_mul] at h2
        exact one_ne_zero h2.symm
      have hkey : star (χ g₀) * χ g₀
          = star (χ g₀) * ψ g₀ :=
        (hχu g₀).trans hcontra.symm
      exact hg₀ (mul_left_cancel₀ hs hkey)
    have hshift : ∑ g, φ (g₀ * g) = ∑ g, φ g :=
      Fintype.sum_equiv (Equiv.mulLeft g₀) _ _
        fun g => rfl
    have hfac : ∑ g, φ (g₀ * g) = φ g₀ * ∑ g, φ g := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => hφmul g₀ g
    have := hshift.symm.trans hfac
    have hzero : (φ g₀ - 1) * ∑ g, φ g = 0 := by
      linear_combination -this
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (by linear_combination h) hφne
    · exact h
  -- (iii) annihilation
  have hPP : Pχ * Pψ = 0 := by
    rw [hPχ, Matrix.smul_mul, Matrix.sum_mul]
    rw [show ∑ g, star (χ g) • U g * Pψ
        = ∑ g, (star (χ g) * ψ g) • Pψ from
      Finset.sum_congr rfl fun g _ => by
        rw [Matrix.smul_mul, hcov g, smul_smul]]
    rw [← Finset.sum_smul, horth, zero_smul, smul_zero]
  -- (i) commutation with L⁻¹
  have hLinvU : ∀ g, L⁻¹ * U g = U g * L⁻¹ := by
    intro g
    have h := hLU g
    calc L⁻¹ * U g
        = L⁻¹ * (U g * (L * L⁻¹)) := by
          rw [Matrix.mul_inv_of_invertible,
            Matrix.mul_one]
      _ = L⁻¹ * ((U g * L) * L⁻¹) := by
          rw [Matrix.mul_assoc]
      _ = L⁻¹ * ((L * U g) * L⁻¹) := by rw [h]
      _ = L⁻¹ * (L * (U g * L⁻¹)) := by
          rw [Matrix.mul_assoc]
      _ = U g * L⁻¹ :=
          Matrix.inv_mul_cancel_left_of_invertible _ _
  have hcomm : L⁻¹ * Pχ = Pχ * L⁻¹ := by
    rw [hPχ, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sum, Matrix.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, hLinvU]
  have hcommψ : L⁻¹ * Pψ = Pψ * L⁻¹ := by
    rw [hPψ, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sum, Matrix.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, hLinvU]
  -- (iv) hermitian
  have hherm : Pχᴴ = Pχ := by
    rw [hPχ, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_sum]
    have hcstar : star c = c := by
      rw [hc, star_inv₀]
      congr 1
      rw [Complex.star_def, Complex.conj_natCast]
    rw [hcstar]
    congr 1
    calc ∑ g, (star (χ g) • U g)ᴴ
        = ∑ g, χ g • U g⁻¹ := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Matrix.conjTranspose_smul, star_star,
            hUH]
      _ = ∑ g, χ g⁻¹ • U g := by
          refine Fintype.sum_equiv (Equiv.inv G) _ _
            fun g => ?_
          simp only [Equiv.inv_apply]
          rw [inv_inv]
      _ = ∑ g, star (χ g) • U g := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [hχginv, ← hχinv]
  refine ⟨hcomm, hcov, hPP, hherm, ?_⟩
  intro k m _ _ A Z hA hZ
  calc Aᴴ * (L⁻¹ * Z)
      = (Pχ * A)ᴴ * (L⁻¹ * (Pψ * Z)) := by rw [hA, hZ]
    _ = (Aᴴ * Pχ) * (Pψ * (L⁻¹ * Z)) := by
        rw [Matrix.conjTranspose_mul, hherm,
          ← Matrix.mul_assoc L⁻¹ Pψ Z, hcommψ,
          Matrix.mul_assoc]
        simp only [Matrix.mul_assoc]
    _ = Aᴴ * ((Pχ * Pψ) * (L⁻¹ * Z)) := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by
        rw [hPP, Matrix.zero_mul, Matrix.mul_zero]

end NCG
