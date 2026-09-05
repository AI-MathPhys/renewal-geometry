/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Saturated full-cell generator and finite-Dirac provenance
  (`thm:SMST-generator-projections`, Gran-Tensor manuscript)

* `smst_generator_projections`:
  (1) the boxed saturation criterion: with the Krylov head
      spanned by an isometry `W` (`WᴴW = 1`, `P_sat = WWᴴ`),
      the reduction `(I−P_sat)·G·P_sat = 0` holds exactly when
      the head is `G`-invariant (`(I−P_sat)GW = 0`) — a
      positive innovation Gram before stabilization is exactly
      the failure of this criterion;
  (2) the grading split: `G = G_ev + G_odd` with
      `ΓG_evΓ = G_ev` and `ΓG_oddΓ = −G_odd` for the finite
      grading `Γ² = 1`;
  (3) the boxed provenance Pythagoras: for any orthogonal
      splitting `X = D + R` with vanishing Hilbert–Schmidt
      cross terms, `‖X‖²_HS = ‖D‖²_HS + ‖R‖²_HS` — the exact
      `η_F^D` versus `Δ_F,odd^extra` budget of the canonical
      finite-Dirac projection.

Rendering disclosed: the relation space `𝔇_F` (type, carrier,
record, grading, reality, order-one, neutral, Majorana
relations) and its orthogonal projector `Π_F^D` are the
declared derived inputs; clause (3) is exactly their
Pythagorean budget once `D = Π_F^D X` and `R = (I−Π_F^D)X`
are HS-orthogonal (the defining property of an orthogonal
projector).
-/

open Matrix

namespace NCG

/-- `thm:SMST-generator-projections`. -/
theorem smst_generator_projections {h : Type*} [Fintype h]
    [DecidableEq h] :
    -- (1) the boxed saturation criterion
    (∀ {k : Type} [Fintype k] [DecidableEq k]
      (W : Matrix h k ℂ)
      (G : Matrix h h ℂ), Wᴴ * W = 1 →
      (((1 : Matrix h h ℂ) - W * Wᴴ) * G * (W * Wᴴ) = 0
        ↔ ((1 : Matrix h h ℂ) - W * Wᴴ) * G * W = 0))
    -- (2) the grading split
    ∧ (∀ G Γ : Matrix h h ℂ, Γ * Γ = 1 →
        ((2 : ℂ)⁻¹ • (G + Γ * G * Γ)
            + (2 : ℂ)⁻¹ • (G - Γ * G * Γ) = G)
        ∧ Γ * ((2 : ℂ)⁻¹ • (G + Γ * G * Γ)) * Γ
            = (2 : ℂ)⁻¹ • (G + Γ * G * Γ)
        ∧ Γ * ((2 : ℂ)⁻¹ • (G - Γ * G * Γ)) * Γ
            = -((2 : ℂ)⁻¹ • (G - Γ * G * Γ)))
    -- (3) the provenance Pythagoras
    ∧ (∀ D R : Matrix h h ℂ,
        (Dᴴ * R).trace = 0 → (Rᴴ * D).trace = 0 →
        ((D + R)ᴴ * (D + R)).trace
          = (Dᴴ * D).trace + (Rᴴ * R).trace) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k _ _ W G hW
    constructor
    · intro h0
      have hh := congrArg (fun M => M * W) h0
      simp only [Matrix.zero_mul] at hh
      rw [show ((1 : Matrix h h ℂ) - W * Wᴴ) * G * (W * Wᴴ)
            * W
          = ((1 : Matrix h h ℂ) - W * Wᴴ) * G
            * (W * (Wᴴ * W)) from by
        simp only [Matrix.mul_assoc], hW, Matrix.mul_one] at hh
      exact hh
    · intro h0
      rw [show ((1 : Matrix h h ℂ) - W * Wᴴ) * G * (W * Wᴴ)
          = (((1 : Matrix h h ℂ) - W * Wᴴ) * G * W) * Wᴴ from
        by simp only [Matrix.mul_assoc], h0, Matrix.zero_mul]
  · intro G Γ hΓ
    refine ⟨?_, ?_, ?_⟩
    · rw [← smul_add]
      rw [show G + Γ * G * Γ + (G - Γ * G * Γ)
          = (2 : ℂ) • G from by
        rw [two_smul]
        abel]
      rw [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    · rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [Matrix.mul_add, Matrix.add_mul]
      rw [show Γ * (Γ * G * Γ) * Γ
          = (Γ * Γ) * G * (Γ * Γ) from by
        simp only [Matrix.mul_assoc], hΓ, Matrix.one_mul,
        Matrix.mul_one]
      abel
    · rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]
      congr 1
      rw [Matrix.mul_sub, Matrix.sub_mul]
      rw [show Γ * (Γ * G * Γ) * Γ
          = (Γ * Γ) * G * (Γ * Γ) from by
        simp only [Matrix.mul_assoc], hΓ, Matrix.one_mul,
        Matrix.mul_one]
      abel
  · intro D R hDR hRD
    rw [Matrix.conjTranspose_add, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.trace_add]
    rw [hDR, hRD]
    ring

end NCG
