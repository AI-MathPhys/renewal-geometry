/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ScoreExport
import NCG.Grand.NuisanceShort
import NCG.Grand.GrandEntangler
import NCG.Flagship.CrossTomography

/-!
# operational score and phase identities
-/

open Matrix Kronecker
open scoped ComplexOrder

namespace NCG

/-! ## Score centering and export -/

/-- Differentiating a finite normalized probability distribution
centres its logarithmic score. -/
theorem finite_score_centering {Om idx : Type*} [Fintype Om]
    (p : Om → ℝ) (dp : idx → Om → ℝ)
    (hp : ∀ x, p x ≠ 0) (hnorm : ∀ i, ∑ x, dp i x = 0) :
    ∀ i, ∑ x, (p x : ℂ) * ((dp i x : ℂ) / (p x : ℂ)) = 0 := by
  intro i
  calc
    ∑ x, (p x : ℂ) * ((dp i x : ℂ) / (p x : ℂ))
        = ∑ x, (dp i x : ℂ) := by
            apply Finset.sum_congr rfl
            intro x _
            have hpx : (p x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hp x)
            field_simp
    _ = ((∑ x, dp i x : ℝ) : ℂ) := by simp
    _ = 0 := by rw [hnorm i]; simp

/-- `thm:operational-score-export` with score centering derived
from finite-sum normalization rather than assumed.  The final
nuisance-projection clause is `simultaneous_nuisance_short`. -/
theorem operational_score_export_exact {Om Omc idx : Type*}
    [Fintype Om] [Fintype Omc] [DecidableEq Omc] [Finite idx]
    (p : Om → ℝ) (hp : ∀ x, 0 ≤ p x) (hp0 : ∀ x, p x ≠ 0)
    (dp : idx → Om → ℝ) (hnorm : ∀ i, ∑ x, dp i x = 0)
    (s : idx → Om → ℂ)
    (hscore : ∀ i x, s i x = (dp i x : ℂ) / (p x : ℂ))
    (c : Om → Omc) (pc : Omc → ℝ)
    (hpc : ∀ y, pc y
      = ∑ x ∈ Finset.univ.filter (fun x => c x = y), p x)
    (hpcpos : ∀ y, pc y ≠ 0) (sc : idx → Omc → ℂ)
    (hsc : ∀ i y, sc i y = (pc y : ℂ)⁻¹
      * ∑ x ∈ Finset.univ.filter (fun x => c x = y),
          (p x : ℂ) * s i x) :
    (∀ i, ∑ x, (p x : ℂ) * s i x = 0)
    ∧ (fisherBlock p s).PosSemidef
    ∧ (fisherBlock pc sc).PosSemidef
    ∧ (fisherBlock p s = fisherBlock pc sc
        + fisherBlock p (fun i x => s i x - sc i (c x)))
    ∧ (fisherBlock p (fun i x => s i x - sc i (c x))).PosSemidef
    ∧ ((∀ i x, s i x = sc i (c x)) →
        fisherBlock p s = fisherBlock pc sc) := by
  have hcenter := finite_score_centering p dp hp0 hnorm
  have hexport := operational_score_export p hp s c pc hpc hpcpos sc hsc
  refine ⟨?_, hexport.1, hexport.2.1, hexport.2.2.1,
    hexport.2.2.2.1, hexport.2.2.2.2⟩
  intro i
  simpa only [hscore] using hcenter i

/-! ## Two-phase ordered-kernel reconstruction -/

/-- `cor:canonical-two-phase-history`: the two measured phase
Grams and the known marginal Gram determine the ordered cross
kernel. -/
theorem canonical_two_phase_history {h e : Type*}
    [Fintype h] [Fintype e] [DecidableEq h]
    (A B : Matrix h e ℂ) :
    let D := Aᴴ * A + Bᴴ * B
    let G₁ := (A + B)ᴴ * (A + B)
    let Gᵢ := (A + Complex.I • B)ᴴ * (A + Complex.I • B)
    Aᴴ * B = (1 / 2 : ℂ) •
      ((G₁ - D) - Complex.I • (Gᵢ - D)) := by
  dsimp
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.conjTranspose_apply, star_add, star_mul, star_smul,
    Complex.conj_I, smul_eq_mul]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  rw [show star Complex.I = -Complex.I from Complex.conj_I]
  have hsumBA :
      (∑ x, -(Complex.I * star (B x i) * A x j)) =
        -Complex.I * ∑ x, star (B x i) * A x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hsumAB :
      (∑ x, Complex.I * star (A x i) * B x j) =
        Complex.I * ∑ x, star (A x i) * B x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  ring_nf
  rw [hsumBA, hsumAB]
  rw [Complex.I_sq]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-! ## Score-bus circuit contraction -/

/-- The common `|+⟩` preparation coefficient. -/
noncomputable def plusCoeff (_q : Fin 2) : ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ)

/-- Coefficients of `|y_m⟩=(|0⟩+im|1⟩)/√2`. -/
noncomputable def scoreYCoeff (m : ℤ) (q : Fin 2) : ℂ :=
  if q = 0 then ((1 / Real.sqrt 2 : ℝ) : ℂ)
  else ((m : ℂ) * Complex.I) * ((1 / Real.sqrt 2 : ℝ) : ℂ)

/-- Contracting the score qubit after the two controlled-Z gates.
The `q=0` target block is `I` and the `q=1` block is `Z_A Z_B`. -/
noncomputable def scoreBusCircuitK (m : ℤ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ q : Fin 2, ((starRingEnd ℂ) (scoreYCoeff m q) * plusCoeff q) •
    (if q = 0 then
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) else zzWord)

/-- The literal circuit contraction is the Kraus operator used by
the entangler theorem. -/
theorem scoreBusCircuitK_eq (m : ℤ) :
    scoreBusCircuitK m = entanglerK m := by
  let c : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  have hc : (((1 / Real.sqrt 2 : ℝ) : ℂ)
      * ((1 / Real.sqrt 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by
    norm_cast
    field_simp
    rw [Real.sq_sqrt] <;> norm_num
  rw [scoreBusCircuitK, Fin.sum_univ_two, entanglerK]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [show scoreYCoeff m 0 = c by simp [scoreYCoeff, c],
    show plusCoeff 0 = c by rfl,
    show scoreYCoeff m 1 = (m : ℂ) * Complex.I * c by
      simp [scoreYCoeff, h10, c],
    show plusCoeff 1 = c by rfl]
  simp only [if_pos rfl, if_neg h10]
  simp only [starRingEnd_apply, if_true]
  have hstarc : star c = c := by simp [c]
  rw [hstarc]
  have hstarprod : star ((m : ℂ) * Complex.I * c) =
      -(m : ℂ) * Complex.I * c := by
    rw [star_mul, star_mul, hstarc,
      show star Complex.I = -Complex.I from Complex.conj_I]
    simp
    ring
  have hcc : c * c = (1 / 2 : ℂ) := by simpa [c] using hc
  rw [hstarprod, hcc]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply]
  rw [show -(m : ℂ) * Complex.I * c * c =
      (-(m : ℂ) * Complex.I) * (c * c) by ring, hcc]
  ring

/-- `lem:score-bus-entangler`, packaged from the circuit
contraction and all branch/POVM/unitarity/quarter-rotation clauses. -/
theorem score_bus_entangler_exact :
    (∀ m : ℤ, scoreBusCircuitK m = entanglerK m)
    ∧ (∀ m : ℤ, m = 1 ∨ m = -1 →
        (entanglerK m)ᴴ * entanglerK m =
          (1 / 2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    ∧ ((entanglerK 1)ᴴ * entanglerK 1
        + (entanglerK (-1))ᴴ * entanglerK (-1) = 1)
    ∧ (∀ m : ℤ, m = 1 ∨ m = -1 →
        (((Real.sqrt 2 : ℂ) • entanglerK m)ᴴ
          * ((Real.sqrt 2 : ℂ) • entanglerK m) = 1)
        ∧ (((Real.sqrt 2 : ℂ) • entanglerK m)ᴴ
          = (Real.sqrt 2 : ℂ) • entanglerK (-m)))
    ∧ (∀ m : ℤ, m = 1 ∨ m = -1 →
        ((Real.sqrt 2 : ℂ) • entanglerK m)
          * ((Real.sqrt 2 : ℂ) • entanglerK m)
        = (-(m : ℂ) * Complex.I) • zzWord) := by
  refine ⟨scoreBusCircuitK_eq, ?_, entangler_povm, ?_, ?_⟩
  · exact entangler_kraus_prob
  · exact entangler_unitary
  · exact entangler_quarter

end NCG
