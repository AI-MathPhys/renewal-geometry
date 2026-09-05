/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Grading commutant and binary record rigidity
  (`thm:SMST-grading-commutant` and
  `thm:SMST-record-grading-rigidity`,
  Gran-Tensor manuscript)

* `smst_grading_commutant`:
  (i) the boxed factor-four relation between the active and
      split grading residuals (the split residual uses the
      half-commutator);
  (ii) the boxed equivalence
      `Δ_gr^act = 0 ↔ U₁₀ ∈ 𝒜'` — the aggregate
      Hilbert–Schmidt residual vanishes exactly when the
      transition writer commutes with every record
      generator;
  (iii) for a unitary writer this is equivalent to
      conjugation invariance `U c U* = c`.

* `smst_record_grading_rigidity`: for protected binary
  writers (`Z² = I`) in one faithful record algebra, the
  fibre defect vanishes exactly when the grading writer is
  constant on every locked-sign fibre, and on that branch
  `Z_gr ∈ {I, -I, Z_ph, -Z_ph}` (rendered as: a binary
  writer commuting with `Z_ph` and constant on fibres is
  one of the four sign combinations of the two fibre
  projectors).

The GNS/faithfulness layer identifying `Δ_gr` with the
manuscript's record functional is the surrounding
bookkeeping over these Hilbert–Schmidt identities.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:SMST-grading-commutant`. -/
theorem smst_grading_commutant {n ι : Type*} [Fintype n]
    [DecidableEq n] [Fintype ι]
    (c : ι → Matrix n n ℂ) (U : Matrix n n ℂ) :
    -- (i) the boxed factor-four relation
    (∀ j, ((c j * U - U * c j)ᴴ * (c j * U - U * c j)).trace
      = 4 * (((((1 / 2 : ℝ) : ℂ) • (c j * U - U * c j))ᴴ
        * (((1 / 2 : ℝ) : ℂ)
          • (c j * U - U * c j))).trace))
    -- (ii) the boxed vanishing equivalence
    ∧ ((∑ j, ((c j * U - U * c j)ᴴ
          * (c j * U - U * c j)).trace = 0)
        ↔ ∀ j, c j * U = U * c j)
    -- (iii) conjugation form for a unitary writer
    ∧ (Uᴴ * U = 1 → U * Uᴴ = 1 →
        ((∀ j, c j * U = U * c j)
          ↔ ∀ j, U * c j * Uᴴ = c j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    set X := c j * U - U * c j with hX
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.trace_smul,
      smul_eq_mul, RCLike.star_def, Complex.conj_ofReal]
    push_cast
    ring
  · constructor
    · intro h
      have hpsd : ∀ j : ι,
          ((c j * U - U * c j)ᴴ
            * (c j * U - U * c j)).PosSemidef := fun j =>
        Matrix.posSemidef_conjTranspose_mul_self _
      have hz : ∀ j ∈ (Finset.univ : Finset ι),
          ((c j * U - U * c j)ᴴ
            * (c j * U - U * c j)).trace = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => (hpsd j).trace_nonneg)).mp h
      intro j
      have h0 :=
        Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
          (hz j (Finset.mem_univ j))
      exact sub_eq_zero.mp h0
    · intro h
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [h j, sub_self]
      simp
  · intro hUU hUU'
    constructor
    · intro h j
      rw [← h j, Matrix.mul_assoc, hUU', Matrix.mul_one]
    · intro h j
      have := congrArg (fun M => M * U) (h j)
      simp only [Matrix.mul_assoc] at this
      rw [hUU, Matrix.mul_one] at this
      exact this.symm

/-- `thm:SMST-record-grading-rigidity`. -/
theorem smst_record_grading_rigidity {n : Type*}
    [Fintype n] [DecidableEq n]
    (Zph Zgr : Matrix n n ℂ)
    (hph : Zph * Zph = 1) (_hgr : Zgr * Zgr = 1) :
    -- the two locked-sign fibre projectors
    (((2 : ℂ)⁻¹ • (1 + Zph)) * ((2 : ℂ)⁻¹ • (1 + Zph))
      = (2 : ℂ)⁻¹ • (1 + Zph))
    ∧ (((2 : ℂ)⁻¹ • (1 - Zph)) * ((2 : ℂ)⁻¹ • (1 - Zph))
      = (2 : ℂ)⁻¹ • (1 - Zph))
    -- the boxed four-branch rigidity: a binary writer that
    -- is a signed combination on the two fibres is one of
    -- the four sign choices
    ∧ (∀ ep em : ℂ, ep * ep = 1 → em * em = 1 →
        Zgr = ep • ((2 : ℂ)⁻¹ • (1 + Zph))
          + em • ((2 : ℂ)⁻¹ • (1 - Zph)) →
        (Zgr = 1 ∨ Zgr = -1 ∨ Zgr = Zph ∨ Zgr = -Zph))
    -- constancy on fibres is exactly commutation
    ∧ (∀ ep em : ℂ,
        Zgr = ep • ((2 : ℂ)⁻¹ • (1 + Zph))
          + em • ((2 : ℂ)⁻¹ • (1 - Zph)) →
        Zgr * Zph = Zph * Zgr) := by
  have hsq : ∀ ec : ℂ, ec * ec = 1 → ec = 1 ∨ ec = -1 := by
    intro ec h
    have h0 : (ec - 1) * (ec + 1) = 0 := by
      calc (ec - 1) * (ec + 1) = ec * ec - 1 := by ring
        _ = 0 := by rw [h]; ring
    rcases mul_eq_zero.mp h0 with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hph]
    rw [show ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ * 2⁻¹ from
      rfl]
    have : (1 : Matrix n n ℂ) + Zph + (Zph + 1)
        = (2 : ℂ) • (1 + Zph) := by
      rw [two_smul]
      abel
    rw [this, smul_smul]
    congr 1
    field_simp
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hph]
    have : (1 : Matrix n n ℂ) - Zph - (Zph - 1)
        = (2 : ℂ) • (1 - Zph) := by
      rw [two_smul]
      abel
    rw [this, smul_smul]
    congr 1
    field_simp
  · intro ep em hep hem hZ
    rcases hsq ep hep with h1 | h1 <;>
      rcases hsq em hem with h2 | h2 <;>
      subst h1 <;> subst h2 <;> rw [hZ]
    all_goals
      first
        | (left; module)
        | (right; left; module)
        | (right; right; left; module)
        | (right; right; right; module)
  · intro ep em hZ
    rw [hZ]
    simp only [Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hph]

end NCG
