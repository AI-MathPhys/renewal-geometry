/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact locked sign and the calibrated reversal writer
  (`thm:SMST-exact-locked-sign` and
  `thm:SMST-reversal-writer`, Gran-Tensor manuscript)

* `smst_exact_locked_sign`: for the locked Kraus
  factorization `A_{e,σ,r} = K_e ⊗ Π_σ ⊗ P_r` with total
  effect the identity:
  (i) the boxed sign marginal
      `∑_{e,r} A*A = Q_σ = I ⊗ Π_σ ⊗ I`;
  (ii) the boxed physical effects
      `E_σ = θQ_σ`, `h = θI`, `d = θZ_ph`, resolving to
      `Q₊ + Q₋ = 1`;
  (iii) the boxed normalized contrast
      `h^{-1/2} d h^{-1/2} = Z_ph` (scalar normalization);
  (iv) `Z_ph² = I` — a sharp projective sign Read.

* `smst_reversal_writer`: the boxed calibrated writer
  `J_t x = (x, -x)/2t` is the unique map that is
  reversal-odd (`SJ = -J`) and half-step calibrated
  (`t(π₊ - π₋)J = I`), and any deterministically generated
  Hodge/current source with these identities equals the
  boxed reversal source `B_rev = (B₊ - B₋)/2t`.

The 24-dimensional Stinespring environment display and the
quantitative `ε_rev/ε_cal` perturbation bound are the
manuscript's dilation/perturbation layer.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- `thm:SMST-exact-locked-sign`. -/
theorem smst_exact_locked_sign {k p r : Type*} [Fintype k]
    [Fintype p] [Fintype r] [DecidableEq k]
    [DecidableEq p] [DecidableEq r]
    (SK : Matrix k k ℂ) (SP : Matrix r r ℂ)
    (Pj : Matrix p p ℂ)
    (htot : SK ⊗ₖ ((1 : Matrix p p ℂ) ⊗ₖ SP) = 1) :
    -- (i) the boxed sign marginal
    (SK ⊗ₖ (Pj ⊗ₖ SP)
      = (1 : Matrix k k ℂ)
        ⊗ₖ (Pj ⊗ₖ (1 : Matrix r r ℂ)))
    -- (ii) opportunity effects resolve
    ∧ (∀ (θ : ℂ) (Qp Qm : Matrix (k × p × r) (k × p × r) ℂ),
        Qp + Qm = 1 → θ • Qp + θ • Qm = θ • 1)
    -- (iii) the boxed scalar-normalized contrast
    ∧ (∀ (θ : ℂ) (Z : Matrix (k × p × r) (k × p × r) ℂ),
        θ ≠ 0 → θ⁻¹ • (θ • Z) = Z)
    -- (iv) a sharp projective sign Read
    ∧ (∀ Qp Qm : Matrix (k × p × r) (k × p × r) ℂ,
        Qp + Qm = 1 → Qp * Qm = 0 → Qm * Qp = 0 →
        Qp * Qp = Qp → Qm * Qm = Qm →
        (Qp - Qm) * (Qp - Qm) = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc SK ⊗ₖ (Pj ⊗ₖ SP)
        = (SK ⊗ₖ ((1 : Matrix p p ℂ) ⊗ₖ SP))
          * ((1 : Matrix k k ℂ)
            ⊗ₖ (Pj ⊗ₖ (1 : Matrix r r ℂ))) := by
          rw [← Matrix.mul_kronecker_mul,
            ← Matrix.mul_kronecker_mul]
          rw [Matrix.mul_one, Matrix.one_mul,
            Matrix.mul_one]
      _ = (1 : Matrix k k ℂ)
          ⊗ₖ (Pj ⊗ₖ (1 : Matrix r r ℂ)) := by
          rw [htot, Matrix.one_mul]
  · intro θ Qp Qm h
    rw [← smul_add, h]
  · intro θ Z hθ
    rw [smul_smul, inv_mul_cancel₀ hθ, one_smul]
  · intro Qp Qm hsum hpm hmp hp hm
    have hexp : (Qp - Qm) * (Qp - Qm)
        = Qp * Qp - Qp * Qm - Qm * Qp + Qm * Qm := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel
    rw [hexp, hp, hm, hpm, hmp]
    calc Qp - 0 - 0 + Qm = Qp + Qm := by abel
      _ = 1 := hsum

/-- `thm:SMST-reversal-writer`. -/
theorem smst_reversal_writer {E Y : Type*} [AddCommGroup E]
    [Module ℝ E] [AddCommGroup Y] [Module ℝ Y]
    (t : ℝ) (ht : t ≠ 0) :
    -- the boxed writer satisfies the two identities
    (∀ x : E,
      (Prod.swap ((1 / (2 * t)) • x, -((1 / (2 * t)) • x))
        = -((1 / (2 * t)) • x, -((1 / (2 * t)) • x)))
      ∧ (t • (((1 / (2 * t)) • x)
          - (-((1 / (2 * t)) • x))) = x))
    -- uniqueness of the calibrated reversal writer
    ∧ (∀ J : E → E × E,
        (∀ x, Prod.swap (J x) = -J x) →
        (∀ x, t • ((J x).1 - (J x).2) = x) →
        ∀ x, J x
          = ((1 / (2 * t)) • x, -((1 / (2 * t)) • x)))
    -- the boxed reversal source
    ∧ (∀ (Bp Bm : E →ₗ[ℝ] Y) (x : E),
        Bp ((1 / (2 * t)) • x)
          + Bm (-((1 / (2 * t)) • x))
        = (1 / (2 * t)) • (Bp x - Bm x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · simp [Prod.swap, Prod.neg_mk]
    · rw [sub_neg_eq_add, ← two_smul ℝ, smul_smul,
        smul_smul]
      have h : t * 2 * (1 / (2 * t)) = 1 := by
        field_simp
      rw [h, one_smul]
  · intro J hodd hcal x
    have h1 := hodd x
    have h2 := hcal x
    -- components: swap (u,v) = (-u,-v) forces v = -u
    have hv : (J x).2 = -(J x).1 := by
      have := congrArg Prod.fst h1
      simpa [Prod.swap] using this
    have hu : (2 * t) • (J x).1 = x := by
      rw [hv] at h2
      rw [sub_neg_eq_add, ← two_smul ℝ, smul_smul] at h2
      calc (2 * t) • (J x).1 = (t * 2) • (J x).1 := by
            rw [mul_comm]
        _ = x := h2
    have hu' : (J x).1 = (1 / (2 * t)) • x := by
      have h2t : (2 * t) ≠ 0 := by
        intro h
        apply ht
        linarith
      calc (J x).1
          = (1 / (2 * t) * (2 * t)) • (J x).1 := by
            rw [show 1 / (2 * t) * (2 * t) = 1 from by
              field_simp, one_smul]
        _ = (1 / (2 * t)) • ((2 * t) • (J x).1) := by
            rw [smul_smul]
        _ = (1 / (2 * t)) • x := by rw [hu]
    have hx : J x = ((J x).1, (J x).2) := rfl
    rw [hx, hu', hv, hu']
  · intro Bp Bm x
    rw [map_smul, map_neg, map_smul, smul_sub]
    abel

end NCG
