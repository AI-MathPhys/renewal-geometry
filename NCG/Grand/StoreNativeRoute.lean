/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Protected-sign odd shorting and matter-route theorem
  (`thm:SMST-store-native-route`, Gran-Tensor manuscript)

With a protected binary record involution `Z` (`Zᴴ = Z`,
`Z² = 1`) and hermitian generator `G`, write `C = (1−Z)G(1+Z)`
(`= 4B` for the corner `B = P_L G P_R`), `D = G − ZGZ`
(`= 2G_odd`), `E = G + ZGZ` (`= 2G_ev`).

* `store_native_route`:
  (R2) `C + Cᴴ = D + D` (the boxed `G_odd = B + Bᴴ`),
  `C·C = 0` (corner nilpotency), and
  `Tr(CᴴC) = 2·Tr(DᴴD)` (the boxed `‖G_odd‖² = 2‖B‖²` after
  the `1/4, 1/2` scalings);
  (R3) `[Z,G] = Z·D` and `Tr([Z,G]ᴴ[Z,G]) = Tr(DᴴD)` (the
  boxed `‖B‖² = ⅛‖[Z,G]‖²`), and `{Z,G} = Z·E` with
  `Tr({Z,G}ᴴ{Z,G}) = Tr(EᴴE)` (the boxed
  `‖{Z,G}‖² = 4‖G_ev‖²`);
  (R4) on the faithful route support the normalized route
  `B(√(BᴴB))⁻¹` is an isometry, `ρ ↦ BρBᴴ` preserves
  positivity, and it is nonzero exactly when `B ≠ 0`.

Rendering disclosed: (R1) — `G = (i/t)Log U_t` in the
principal-logarithm domain — and (R5) — the exponential
Taylor-remainder bound and diamond-norm limit — are the
manuscript's functional-calculus and analytic clauses,
declared context for the proved algebra; the pseudo-inverse
`(BᴴB)^{†/2}` is rendered by positive definiteness on the
route support (the manuscript's support reduction).
-/

open Matrix
open scoped ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:SMST-store-native-route`. -/
theorem store_native_route {n : Type*} [Fintype n]
    [DecidableEq n] (Z G : Matrix n n ℂ) (hZH : Zᴴ = Z)
    (hZ2 : Z * Z = 1) (hGH : Gᴴ = G) :
    -- (R2) odd shorting, nilpotency, HS identity
    (((1 : Matrix n n ℂ) - Z) * G * ((1 : Matrix n n ℂ) + Z)
        + (((1 : Matrix n n ℂ) - Z) * G
            * ((1 : Matrix n n ℂ) + Z))ᴴ
      = (G - Z * G * Z) + (G - Z * G * Z))
    ∧ (((1 : Matrix n n ℂ) - Z) * G * ((1 : Matrix n n ℂ) + Z))
        * (((1 : Matrix n n ℂ) - Z) * G
          * ((1 : Matrix n n ℂ) + Z)) = 0
    ∧ ((((1 : Matrix n n ℂ) - Z) * G
          * ((1 : Matrix n n ℂ) + Z))ᴴ
        * (((1 : Matrix n n ℂ) - Z) * G
          * ((1 : Matrix n n ℂ) + Z))).trace
      = 2 * ((G - Z * G * Z)ᴴ * (G - Z * G * Z)).trace
    -- (R3) matter margin and even identity
    ∧ Z * G - G * Z = Z * (G - Z * G * Z)
    ∧ ((Z * G - G * Z)ᴴ * (Z * G - G * Z)).trace
      = ((G - Z * G * Z)ᴴ * (G - Z * G * Z)).trace
    ∧ Z * G + G * Z = Z * (G + Z * G * Z)
    ∧ ((Z * G + G * Z)ᴴ * (Z * G + G * Z)).trace
      = ((G + Z * G * Z)ᴴ * (G + Z * G * Z)).trace
    -- (R4) normalized route, positivity, nonvanishing
    ∧ (∀ B : Matrix n n ℂ, (Bᴴ * B).PosDef →
        (B * (CFC.sqrt (Bᴴ * B))⁻¹)ᴴ
          * (B * (CFC.sqrt (Bᴴ * B))⁻¹) = 1)
    ∧ (∀ (B ρ : Matrix n n ℂ), ρ.PosSemidef →
        (B * ρ * Bᴴ).PosSemidef)
    ∧ (∀ B : Matrix n n ℂ,
        B * (1 : Matrix n n ℂ) * Bᴴ = 0 ↔ B = 0) := by
  have hCH : (((1 : Matrix n n ℂ) - Z) * G
        * ((1 : Matrix n n ℂ) + Z))ᴴ
      = ((1 : Matrix n n ℂ) + Z) * G
        * ((1 : Matrix n n ℂ) - Z) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hZH, hGH]
    simp only [Matrix.mul_assoc]
  have hDH : (G - Z * G * Z)ᴴ = G - Z * G * Z := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hZH, hGH]
    simp only [Matrix.mul_assoc]
  have hEH : (G + Z * G * Z)ᴴ = G + Z * G * Z := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hZH, hGH]
    simp only [Matrix.mul_assoc]
  have hmid : ((1 : Matrix n n ℂ) + Z)
      * ((1 : Matrix n n ℂ) - Z) = 0 := by
    have h : ((1 : Matrix n n ℂ) + Z)
        * ((1 : Matrix n n ℂ) - Z) = 1 - Z * Z := by
      noncomm_ring
    rw [h, hZ2, sub_self]
  have hsum : ((1 : Matrix n n ℂ) - Z) * G
        * ((1 : Matrix n n ℂ) + Z)
        + (((1 : Matrix n n ℂ) - Z) * G
            * ((1 : Matrix n n ℂ) + Z))ᴴ
      = (G - Z * G * Z) + (G - Z * G * Z) := by
    rw [hCH]
    noncomm_ring
  have hnil : (((1 : Matrix n n ℂ) - Z) * G
        * ((1 : Matrix n n ℂ) + Z))
      * (((1 : Matrix n n ℂ) - Z) * G
        * ((1 : Matrix n n ℂ) + Z)) = 0 := by
    rw [show ((1 : Matrix n n ℂ) - Z) * G
          * ((1 : Matrix n n ℂ) + Z)
          * (((1 : Matrix n n ℂ) - Z) * G
            * ((1 : Matrix n n ℂ) + Z))
        = ((1 : Matrix n n ℂ) - Z) * G
          * ((((1 : Matrix n n ℂ) + Z)
            * ((1 : Matrix n n ℂ) - Z))
            * (G * ((1 : Matrix n n ℂ) + Z))) from by
      simp only [Matrix.mul_assoc]]
    rw [hmid, Matrix.zero_mul, Matrix.mul_zero]
  have hnilH : (((1 : Matrix n n ℂ) - Z) * G
        * ((1 : Matrix n n ℂ) + Z))ᴴ
      * (((1 : Matrix n n ℂ) - Z) * G
        * ((1 : Matrix n n ℂ) + Z))ᴴ = 0 := by
    rw [← Matrix.conjTranspose_mul, hnil,
      Matrix.conjTranspose_zero]
  have hZD : Z * G - G * Z = Z * (G - Z * G * Z) := by
    have h : Z * (G - Z * G * Z)
        = Z * G - (Z * Z) * G * Z := by noncomm_ring
    rw [h, hZ2, Matrix.one_mul]
  have hZE : Z * G + G * Z = Z * (G + Z * G * Z) := by
    have h : Z * (G + Z * G * Z)
        = Z * G + (Z * Z) * G * Z := by noncomm_ring
    rw [h, hZ2, Matrix.one_mul]
  -- sandwich: (Z·M)ᴴ(Z·M) = Mᴴ M for the involution Z
  have hsand : ∀ M : Matrix n n ℂ,
      ((Z * M)ᴴ * (Z * M)).trace = (Mᴴ * M).trace := by
    intro M
    rw [Matrix.conjTranspose_mul, hZH,
      show Mᴴ * Z * (Z * M) = Mᴴ * ((Z * Z) * M) from by
        simp only [Matrix.mul_assoc],
      hZ2, Matrix.one_mul]
  refine ⟨hsum, hnil, ?_, hZD, ?_, hZE, ?_, ?_, ?_, ?_⟩
  · -- Tr(CᴴC) = 2 Tr(DᴴD) from the sum + nilpotency
    have h1 : ((((1 : Matrix n n ℂ) - Z) * G
            * ((1 : Matrix n n ℂ) + Z)
          + (((1 : Matrix n n ℂ) - Z) * G
            * ((1 : Matrix n n ℂ) + Z))ᴴ)ᴴ
        * (((1 : Matrix n n ℂ) - Z) * G
            * ((1 : Matrix n n ℂ) + Z)
          + (((1 : Matrix n n ℂ) - Z) * G
            * ((1 : Matrix n n ℂ) + Z))ᴴ)).trace
        = 4 * ((G - Z * G * Z) * (G - Z * G * Z)).trace := by
      rw [hsum, Matrix.conjTranspose_add, hDH,
        Matrix.add_mul, Matrix.mul_add]
      simp only [Matrix.trace_add]
      ring
    have h2 : ((((1 : Matrix n n ℂ) - Z) * G
            * ((1 : Matrix n n ℂ) + Z)
          + (((1 : Matrix n n ℂ) - Z) * G
            * ((1 : Matrix n n ℂ) + Z))ᴴ)ᴴ
        * (((1 : Matrix n n ℂ) - Z) * G
            * ((1 : Matrix n n ℂ) + Z)
          + (((1 : Matrix n n ℂ) - Z) * G
            * ((1 : Matrix n n ℂ) + Z))ᴴ)).trace
        = 2 * ((((1 : Matrix n n ℂ) - Z) * G
              * ((1 : Matrix n n ℂ) + Z))ᴴ
            * (((1 : Matrix n n ℂ) - Z) * G
              * ((1 : Matrix n n ℂ) + Z))).trace := by
      generalize hCg : ((1 : Matrix n n ℂ) - Z) * G
        * ((1 : Matrix n n ℂ) + Z) = Cm at hnil hnilH ⊢
      rw [Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose, Matrix.add_mul,
        Matrix.mul_add, Matrix.mul_add, hnil, hnilH]
      simp only [Matrix.trace_add, Matrix.trace_zero]
      rw [Matrix.trace_mul_comm Cm]
      ring
    rw [hDH]
    linear_combination (h1 - h2) / 2
  · rw [hZD, hsand]
  · rw [hZE, hsand]
  · intro B hB
    haveI := (sqrt_isUnit hB).invertible
    rw [Matrix.conjTranspose_mul, sqrt_inv_isHermitian]
    calc (CFC.sqrt (Bᴴ * B))⁻¹ * Bᴴ
        * (B * (CFC.sqrt (Bᴴ * B))⁻¹)
        = (CFC.sqrt (Bᴴ * B))⁻¹ * (Bᴴ * B)
          * (CFC.sqrt (Bᴴ * B))⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (CFC.sqrt (Bᴴ * B))⁻¹
          * (CFC.sqrt (Bᴴ * B) * CFC.sqrt (Bᴴ * B))
          * (CFC.sqrt (Bᴴ * B))⁻¹ := by
          rw [sqrt_mul_self_eq _ hB.posSemidef]
      _ = 1 := by
          rw [← Matrix.mul_assoc,
            Matrix.inv_mul_of_invertible, Matrix.one_mul,
            Matrix.mul_inv_of_invertible]
  · intro B ρ hρ
    exact hρ.mul_mul_conjTranspose_same B
  · intro B
    rw [Matrix.mul_one]
    constructor
    · intro h0
      have := Matrix.conjTranspose_mul_self_eq_zero
        (A := Bᴴ)
      rw [Matrix.conjTranspose_conjTranspose] at this
      have hB := this.mp h0
      rw [← Matrix.conjTranspose_conjTranspose (M := B), hB,
        Matrix.conjTranspose_zero]
    · intro h0
      rw [h0, Matrix.zero_mul]

end NCG
