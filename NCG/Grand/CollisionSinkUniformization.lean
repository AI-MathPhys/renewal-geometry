/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperationalScorePhases
import NCG.Grand.GrandScoreCollision
import NCG.Grand.GrandNullIdeal
import NCG.Grand.DiscreteClock

/-!
# collision, sink, and uniformization
-/

open Matrix NormedSpace

namespace NCG

/-! ## One-clock score collision -/

/-- Literal contraction of the prepared score qubit after a
single controlled-Z gate. -/
noncomputable def scoreCollisionCircuitK (m : ℤ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ q : Fin 2, ((starRingEnd ℂ) (scoreYCoeff m q) * plusCoeff q) •
    (if q = 0 then (1 : Matrix (Fin 2) (Fin 2) ℂ) else clockZ)

/-- The controlled-Z circuit contraction equals the collision
Kraus operator. -/
theorem scoreCollisionCircuitK_eq (m : ℤ) :
    scoreCollisionCircuitK m = collideK m := by
  let c : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  have hc : (((1 / Real.sqrt 2 : ℝ) : ℂ)
      * ((1 / Real.sqrt 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by
    norm_cast
    field_simp
    rw [Real.sq_sqrt] <;> norm_num
  rw [scoreCollisionCircuitK, Fin.sum_univ_two, collideK]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [show scoreYCoeff m 0 = c by simp [scoreYCoeff, c],
    show plusCoeff 0 = c by rfl,
    show scoreYCoeff m 1 = (m : ℂ) * Complex.I * c by
      simp [scoreYCoeff, h10, c],
    show plusCoeff 1 = c by rfl]
  simp only [if_neg h10, starRingEnd_apply, if_true]
  have hstarc : star c = c := by simp [c]
  rw [hstarc]
  have hstarprod : star ((m : ℂ) * Complex.I * c) =
      -(m : ℂ) * Complex.I * c := by
    rw [star_mul, star_mul, hstarc,
      show star Complex.I = -Complex.I from Complex.conj_I]
    simp
    ring
  rw [hstarprod]
  have hcc : c * c = (1 / 2 : ℂ) := by simpa [c] using hc
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply]
  rw [show -(m : ℂ) * Complex.I * c * c =
      (-(m : ℂ) * Complex.I) * (c * c) by ring, hcc]
  ring

/-- `lem:one-clock-score-collision`, now including its circuit
derivation as well as the fair effect, quarter rotation, and
forgotten-score dephasing channel. -/
theorem one_clock_score_collision_exact :
    (∀ m : ℤ, scoreCollisionCircuitK m = collideK m)
    ∧ (∀ (m : ℤ), m = 1 ∨ m = -1 →
      ∀ Xm : Matrix (Fin 2) (Fin 2) ℂ,
        ((collideK m)ᴴ * collideK m = (1 / 2 : ℂ) • 1)
        ∧ ((2 : ℂ) • (collideK m * collideK m)
          = (-((m : ℂ) * Complex.I)) • clockZ)
        ∧ (collideK 1 * Xm * (collideK 1)ᴴ
            + collideK (-1) * Xm * (collideK (-1))ᴴ
          = (1 / 2 : ℂ) • (Xm + clockZ * Xm * clockZ))) := by
  refine ⟨scoreCollisionCircuitK_eq, ?_⟩
  intro m hm Xm
  exact score_collision m hm Xm

/-! ## Transient record sink -/

/-- A projection-factorized future map has a unique factor among
maps already supported on the retained projection. -/
theorem record_sink_factor_unique {t h : Type*} [Fintype t]
    [DecidableEq t] [Fintype h]
    (C : Matrix h t ℂ) (P Q : Matrix t t ℂ)
    (hP : P * P = P) (hPQ : P + Q = 1) (hCQ : C * Q = 0) :
    ∃! Cbar : Matrix h t ℂ,
      Cbar = Cbar * P ∧ C = Cbar * P := by
  have hCP : C = C * P := by
    calc
      C = C * (1 : Matrix t t ℂ) := (Matrix.mul_one C).symm
      _ = C * (P + Q) := by rw [hPQ]
      _ = C * P + C * Q := by rw [Matrix.mul_add]
      _ = C * P := by rw [hCQ, add_zero]
  refine ⟨C, ⟨hCP, hCP⟩, ?_⟩
  intro D hD
  calc
    D = D * P := hD.1
    _ = C := hD.2.symm

/-- `thm:record-sink-nullity`, including uniqueness of the
factor through the retained projection. -/
theorem record_sink_nullity_exact {t h e : Type*} [Fintype t]
    [DecidableEq t] [Fintype h]
    (C : Matrix h t ℂ) (P Q : Matrix t t ℂ) (J : Matrix t e ℂ)
    (hP : P * P = P) (hPQ : P + Q = 1)
    (hCQ : C * Q = 0) (hQJ : Q * J = J) :
    (∃! Cbar : Matrix h t ℂ,
      Cbar = Cbar * P ∧ C = Cbar * P)
    ∧ C * J = 0
    ∧ Jᴴ * (Cᴴ * C) * J = 0 := by
  have hbase := record_sink_nullity C P Q J hPQ hCQ hQJ
  exact ⟨record_sink_factor_unique C P Q hP hPQ hCQ,
    hbase.2.1, hbase.2.2⟩

/-! ## Uniformization gauge -/

/-- Equality of uniformized generators gives equality of their
continuous semigroups at every time. -/
theorem uniformization_semigroup_gauge (Λ : ℝ) (hΛ : Λ ≠ 0)
    (L : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    exp (t • (Λ • (((1 : Matrix (Fin 2) (Fin 2) ℝ)
      + Λ⁻¹ • L) - 1))) = exp (t • L) := by
  have hgauge : Λ • (((1 : Matrix (Fin 2) (Fin 2) ℝ)
      + Λ⁻¹ • L) - 1) = L := by
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hΛ, one_smul]
  rw [hgauge]

/-- `thm:renewal-uniformization-gauge`, with the actual matrix
exponential equality appended to the stochasticity and generator
identities. -/
theorem renewal_uniformization_gauge_exact (α β Λ : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hΛmax : max α β ≤ Λ)
    (hΛ0 : 0 < Λ) :
    ((0 ≤ 1 - α / Λ ∧ 0 ≤ α / Λ)
      ∧ (0 ≤ β / Λ ∧ 0 ≤ 1 - β / Λ)
      ∧ (1 - α / Λ) + α / Λ = 1
      ∧ β / Λ + (1 - β / Λ) = 1)
    ∧ (∀ L : Matrix (Fin 2) (Fin 2) ℝ,
        Λ • (((1 : Matrix (Fin 2) (Fin 2) ℝ) + Λ⁻¹ • L) - 1) = L)
    ∧ (∀ (L : Matrix (Fin 2) (Fin 2) ℝ) (Λ' : ℝ), Λ' ≠ 0 →
        Λ • (((1 : Matrix (Fin 2) (Fin 2) ℝ) + Λ⁻¹ • L) - 1)
        = Λ' • (((1 : Matrix (Fin 2) (Fin 2) ℝ) + Λ'⁻¹ • L) - 1))
    ∧ (∀ (L : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ),
        exp (t • (Λ • (((1 : Matrix (Fin 2) (Fin 2) ℝ)
          + Λ⁻¹ • L) - 1))) = exp (t • L)) := by
  have hbase := renewal_uniformization_gauge α β Λ hα hβ hΛmax hΛ0
  exact ⟨hbase.1, hbase.2.1, hbase.2.2, fun L t =>
    uniformization_semigroup_gauge Λ hΛ0.ne' L t⟩

end NCG
