/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact clock–geometry action audit
  (`thm:ADM-action-audit-master`, flagship manuscript)

For the clock and geometry source maps `S_clk, S_geo` with Grams
`A = S_clk*S_clk`, `B = S_clk*S_geo`, `D = S_geo*S_geo` and the
clock-range projection `P = S_clk A⁻¹ S_clk*` (the clock Gram `A`
invertible — minimality of the retained clock module, displayed
as `hA`):

* `admP_hermitian` / `admP_idem` / `admP_fix`: `P` is the
  orthogonal projection onto the clock source range
  (`P* = P`, `P² = P`, `P·S_clk = S_clk`);
* `adm_gram_identity`: the first box —
  `𝔾_{geo|clk} = D - B*A⁻¹B = S_geo*(I - P)S_geo`;
* `adm_gram_posSemidef`: `𝔾_{geo|clk} ⪰ 0` (it is the Gram of
  `(I - P)S_geo`);
* `adm_gram_zero_iff`: the second box — `𝔾_{geo|clk} = 0` exactly
  when the geometry source factors through the clock source
  (`∃ C, S_geo = S_clk·C`, the range inclusion
  `Ran S_geo ⊆ Ran S_clk` in factored form).

Rendering disclosed: the pseudoinverse form (`A†` for singular
`A`), the rank bookkeeping
`rank [A B; B* D] - rank A = rank 𝔾`, and the principal-cosine
contraction `D^{-1/2} 𝔾 D^{-1/2} = I - 𝒞*𝒞` are the manuscript's
remaining clauses on top of the identities proved here.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {n m m' : Type*}

/-- The clock Gram is Hermitian. -/
theorem admA_hermitian [Fintype n] (Sclk : Matrix n m ℂ) :
    (Sclkᴴ * Sclk)ᴴ = Sclkᴴ * Sclk := by
  rw [conjTranspose_mul, conjTranspose_conjTranspose]

/-- The clock-range projector is Hermitian. -/
theorem admP_hermitian [Fintype n] [Fintype m] [DecidableEq m]
    (Sclk : Matrix n m ℂ) :
    (Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)ᴴ
      = Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ := by
  rw [conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, conjTranspose_nonsing_inv,
    admA_hermitian, Matrix.mul_assoc]

/-- The projector fixes the clock source: `P·S_clk = S_clk`. -/
theorem admP_fix [Fintype n] [Fintype m] [DecidableEq m]
    (Sclk : Matrix n m ℂ)
    (hA : IsUnit (Sclkᴴ * Sclk).det) :
    Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ * Sclk = Sclk := by
  rw [Matrix.mul_assoc (Sclk * (Sclkᴴ * Sclk)⁻¹) Sclkᴴ Sclk,
    Matrix.mul_assoc Sclk ((Sclkᴴ * Sclk)⁻¹) (Sclkᴴ * Sclk),
    Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]

/-- The projector is idempotent. -/
theorem admP_idem [Fintype n] [Fintype m] [DecidableEq m]
    (Sclk : Matrix n m ℂ)
    (hA : IsUnit (Sclkᴴ * Sclk).det) :
    (Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)
      * (Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)
    = Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ := by
  calc (Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)
        * (Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)
      = (Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ * Sclk)
        * ((Sclkᴴ * Sclk)⁻¹ * Sclkᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ := by
        rw [admP_fix Sclk hA, Matrix.mul_assoc]

variable [Fintype n] [Fintype m] [Fintype m'] [DecidableEq n]
  [DecidableEq m]

omit [Fintype m'] in
/-- `thm:ADM-action-audit-master`, first box:
`D - B*A⁻¹B = S_geo*(I - P)S_geo`. -/
theorem adm_gram_identity (Sclk : Matrix n m ℂ)
    (Sgeo : Matrix n m' ℂ) :
    Sgeoᴴ * Sgeo
      - (Sclkᴴ * Sgeo)ᴴ * (Sclkᴴ * Sclk)⁻¹ * (Sclkᴴ * Sgeo)
    = Sgeoᴴ * (1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ) * Sgeo := by
  rw [conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  congr 1
  simp only [Matrix.mul_assoc]

/-- The one-complement of the projector is idempotent. -/
theorem admQ_idem (Sclk : Matrix n m ℂ)
    (hA : IsUnit (Sclkᴴ * Sclk).det) :
    ((1 : Matrix n n ℂ) - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)
      * (1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)
    = 1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ := by
  have h1 : ((1 : Matrix n n ℂ)
        - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)
      * (1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)
      = 1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ
        - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ
        + (Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)
          * (Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ) := by
    noncomm_ring
  rw [h1, admP_idem Sclk hA]
  abel

omit [Fintype m'] in
/-- The audit Gram in factored form. -/
theorem adm_gram_factored (Sclk : Matrix n m ℂ)
    (Sgeo : Matrix n m' ℂ)
    (hA : IsUnit (Sclkᴴ * Sclk).det) :
    Sgeoᴴ * (1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ) * Sgeo
      = ((1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ) * Sgeo)ᴴ
        * ((1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ) * Sgeo) := by
  have hsub : ((1 : Matrix n n ℂ)
        - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)ᴴ
      = 1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ := by
    rw [conjTranspose_sub, conjTranspose_one, admP_hermitian]
  rw [conjTranspose_mul, hsub, ← Matrix.mul_assoc,
    Matrix.mul_assoc Sgeoᴴ
      ((1 : Matrix n n ℂ) - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)
      ((1 : Matrix n n ℂ) - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ),
    admQ_idem Sclk hA]

omit [Fintype m'] in
/-- `𝔾_{geo|clk} ⪰ 0`: it is the Gram of `(I - P)S_geo`. -/
theorem adm_gram_posSemidef [Finite m'] (Sclk : Matrix n m ℂ)
    (Sgeo : Matrix n m' ℂ)
    (hA : IsUnit (Sclkᴴ * Sclk).det) :
    (Sgeoᴴ * (1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ)
      * Sgeo).PosSemidef := by
  cases nonempty_fintype m'
  rw [adm_gram_factored Sclk Sgeo hA]
  exact posSemidef_conjTranspose_mul_self _

omit [Fintype m'] in
/-- `thm:ADM-action-audit-master`, second box: the audit Gram
vanishes exactly when the geometry source factors through the
clock source. -/
theorem adm_gram_zero_iff (Sclk : Matrix n m ℂ)
    (Sgeo : Matrix n m' ℂ)
    (hA : IsUnit (Sclkᴴ * Sclk).det) :
    Sgeoᴴ * (1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ) * Sgeo = 0
      ↔ ∃ C : Matrix m m' ℂ, Sgeo = Sclk * C := by
  rw [adm_gram_factored Sclk Sgeo hA,
    conjTranspose_mul_self_eq_zero]
  constructor
  · intro h
    refine ⟨(Sclkᴴ * Sclk)⁻¹ * Sclkᴴ * Sgeo, ?_⟩
    have h2 : Sgeo
        - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ * Sgeo = 0 := by
      calc Sgeo - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ * Sgeo
          = (1 - Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ) * Sgeo := by
            rw [Matrix.sub_mul, Matrix.one_mul]
        _ = 0 := h
    have h3 := sub_eq_zero.mp h2
    calc Sgeo = Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ * Sgeo := h3
      _ = Sclk * ((Sclkᴴ * Sclk)⁻¹ * Sclkᴴ * Sgeo) := by
          simp only [Matrix.mul_assoc]
  · rintro ⟨C, rfl⟩
    rw [Matrix.sub_mul, Matrix.one_mul,
      ← Matrix.mul_assoc (Sclk * (Sclkᴴ * Sclk)⁻¹ * Sclkᴴ),
      admP_fix Sclk hA, sub_self]

end NCG
