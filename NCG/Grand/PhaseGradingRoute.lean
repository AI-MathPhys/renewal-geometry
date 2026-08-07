/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointSourceUniversality

/-!
# Locked sign reuse exports the selected Store phase as matter
  (`thm:SMST-phase-grading-route`, Gran-Tensor manuscript)

* `phase_grading_route`: the faithful-trace identification
  criterion (`Δ_id = 0 ⟺ Z_gr = εZ_ph`, as weighted signature
  residual on the record points); grading transfer of the
  anticommutation relation; a nonzero odd coefficient has a
  nonzero cross-support corner; the multiplicity-one route
  normalization; and Kossakowski positivity (a vanishing branch
  sum kills every branch).

Rendering disclosed: the record involutions are rendered by
their ±1 record-point values with faithful weights; the polar
normalization `κ^{-1/2}B` is rendered by the Schur identity
`(1/κ)BᴴB = P` (the square-root gauge is the invisible Kraus
phase); the selection hypotheses `γ_odd > 0`, `Δ_phase = 0`
cite `thm:primitive-phase-selection` (blocked tier).
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:SMST-phase-grading-route`. -/
theorem phase_grading_route :
    -- (1) faithful-trace identification of the two signs
    (∀ {R : Type} [Fintype R] (w : R → ℝ) (zgr zph : R → ℝ)
      (ε : ℝ), (∀ r, 0 < w r) →
      ((∑ r, w r * (zgr r - ε * zph r) ^ 2 = 0)
        ↔ ∀ r, zgr r = ε * zph r))
    -- (2) grading transfer of anticommutation
    ∧ (∀ {n : Type} [Fintype n] (Zph C : Matrix n n ℂ)
        (ε : ℂ),
        Zph * C + C * Zph = 0 →
        (ε • Zph) * C + C * (ε • Zph) = 0)
    -- (3) a nonzero odd coefficient has a nonzero corner
    ∧ (∀ {n : Type} [Fintype n] [DecidableEq n]
        (PL PR C : Matrix n n ℂ),
        PL + PR = 1 →
        PL * C * PL = 0 → PR * C * PR = 0 →
        PL * C * PR = 0 → PR * C * PL = 0 → C = 0)
    -- (4) the multiplicity-one route normalization
    ∧ (∀ {n e : Type} [Fintype n] [Fintype e]
        (B : Matrix n e ℂ) (P : Matrix e e ℂ) (κ : ℂ),
        κ ≠ 0 → Bᴴ * B = κ • P → κ⁻¹ • (Bᴴ * B) = P)
    -- (5) Kossakowski positivity: vanishing branch sums kill
    --     every branch
    ∧ (∀ {n e J : Type} [Fintype n] [Fintype e] [DecidableEq e]
        [Fintype J] (B : J → Matrix n e ℂ),
        (∑ j, (B j)ᴴ * B j) = 0 → ∀ j, B j = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro R _ w zgr zph ε hw
    constructor
    · intro hsum r
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun s _ => mul_nonneg (hw s).le (sq_nonneg _))).mp
        hsum r (Finset.mem_univ r)
      have h2 : (zgr r - ε * zph r) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hterm with h | h
        · exact absurd h (ne_of_gt (hw r))
        · exact h
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      linarith [sub_eq_zero.mp this]
    · intro hall
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [hall r]
      ring
  · intro n _ Zph C ε hanti
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hanti,
      smul_zero]
  · intro n _ _ PL PR C hsum hLL hRR hLR hRL
    calc C = 1 * C * 1 := by
          rw [Matrix.one_mul, Matrix.mul_one]
      _ = (PL + PR) * C * (PL + PR) := by rw [hsum]
      _ = PL * C * PL + PL * C * PR + PR * C * PL
          + PR * C * PR := by
          simp only [Matrix.add_mul, Matrix.mul_add]
          abel
      _ = 0 := by
          rw [hLL, hRR, hLR, hRL]
          simp
  · intro n e _ _ B P κ hκ hB
    rw [hB, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  · intro n e J _ _ _ _ B hsum j
    -- each branch Gram is PSD; a vanishing PSD sum kills each
    have hcol : ∀ v : e → ℂ, B j *ᵥ v = 0 := by
      intro v
      have hterms : ∀ i : J,
          (0 : ℝ) ≤ (star v ⬝ᵥ (((B i)ᴴ * B i) *ᵥ v)).re := by
        intro i
        rw [← gram_realization_inner]
        -- re of star w ⬝ w is a sum of normSq
        have hre : (star (B i *ᵥ v) ⬝ᵥ (B i *ᵥ v)).re
            = ∑ x, Complex.normSq ((B i *ᵥ v) x) := by
          rw [dotProduct]
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Pi.star_apply, RCLike.star_def, mul_comm,
            Complex.mul_conj]
          simp
        rw [hre]
        exact Finset.sum_nonneg fun x _ =>
          Complex.normSq_nonneg _
      have hzero : (star v ⬝ᵥ (((B j)ᴴ * B j) *ᵥ v)).re
          = 0 := by
        have htot : ∑ i, (star v ⬝ᵥ (((B i)ᴴ * B i) *ᵥ v)).re
            = 0 := by
          have h1 : star v ⬝ᵥ ((∑ i, (B i)ᴴ * B i) *ᵥ v)
              = 0 := by
            rw [hsum, Matrix.zero_mulVec, dotProduct_zero]
          rw [Matrix.sum_mulVec, dotProduct_sum] at h1
          rw [← Complex.re_sum, h1, Complex.zero_re]
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => hterms i)).mp htot j (Finset.mem_univ j)
      have hnorm : ∑ x, Complex.normSq ((B j *ᵥ v) x) = 0 := by
        have hre : (star (B j *ᵥ v) ⬝ᵥ (B j *ᵥ v)).re
            = ∑ x, Complex.normSq ((B j *ᵥ v) x) := by
          rw [dotProduct, Complex.re_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Pi.star_apply, RCLike.star_def, mul_comm,
            Complex.mul_conj]
          simp
        rw [← hre, gram_realization_inner]
        exact hzero
      funext x
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => Complex.normSq_nonneg _)).mp hnorm x
        (Finset.mem_univ x)
      exact Complex.normSq_eq_zero.mp this
    ext i k
    have h := congrFun (hcol (Pi.single k 1)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq'] using h

end NCG
