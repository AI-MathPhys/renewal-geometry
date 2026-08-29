/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTAtlasMarginExact
import NCG.Grand.BrandNewEasy03
import NCG.Grand.ProtectedObservableRieszPseudoinverseExact

/-!
# Exact two-margin source-complete coercivity

This file implements all three clauses of thm:GT-two-margin-closure.
The moment Gram and shifted localizer are the actual compressions to the
finite multi-column Krylov synthesis. Its Moore--Penrose range projection is
then tested by the physical atlas. The strict atlas margin forces that
projection to be the identity, so every physical vector is a polynomial
source history.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG
namespace GTTwoMarginFull

open ProtectedObservableRiesz

set_option maxHeartbeats 800000

variable {h f e : Type} [Fintype h] [Fintype f] [Fintype e]
  [DecidableEq h] [DecidableEq f] [DecidableEq e]

/-- The depth-N multi-column Krylov/source synthesis. -/
def krylovSynthesis (T : Matrix h h ℂ) (J : Matrix h f ℂ) (N : ℕ) :
    Matrix h (Fin N × f) ℂ :=
  fun i ja => (T ^ (ja.1 : ℕ) * J) i ja.2

/-- The block Hankel Gram of the finite source histories. -/
def hankelGram (T : Matrix h h ℂ) (J : Matrix h f ℂ) (N : ℕ) :
    Matrix (Fin N × f) (Fin N × f) ℂ :=
  (krylovSynthesis T J N)ᴴ * krylovSynthesis T J N

/-- The shifted block Hankel localizer for the upper threshold θ. -/
def hankelLocalizer (T : Matrix h h ℂ) (J : Matrix h f ℂ)
    (N : ℕ) (θ : ℝ) : Matrix (Fin N × f) (Fin N × f) ℂ :=
  (krylovSynthesis T J N)ᴴ *
    ((θ : ℂ) • (1 : Matrix h h ℂ) - T) *
      krylovSynthesis T J N

/-- The orthogonal projection onto the finite source-generated carrier. -/
noncomputable def reachedProj (T : Matrix h h ℂ) (J : Matrix h f ℂ)
    (N : ℕ) : Matrix h h ℂ :=
  smosTraceRangeProj (krylovSynthesis T J N)

private noncomputable def eNorm {i : Type} [Fintype i] (x : i → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℂ i)‖

/-- The compression Gram has exactly the manuscript's moment-Hankel
entries V_{i+j} = J* T^{i+j} J. -/
theorem hankelGram_apply
    (T : Matrix h h ℂ) (hTH : Tᴴ = T)
    (J : Matrix h f ℂ) (N : ℕ) (ia jb : Fin N × f) :
    hankelGram T J N ia jb =
      (Jᴴ * T ^ ((ia.1 : ℕ) + (jb.1 : ℕ)) * J) ia.2 jb.2 := by
  have hblock :
      (T ^ (ia.1 : ℕ) * J)ᴴ * (T ^ (jb.1 : ℕ) * J) =
        Jᴴ * T ^ ((ia.1 : ℕ) + (jb.1 : ℕ)) * J := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hTH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (T ^ (ia.1 : ℕ)) (T ^ (jb.1 : ℕ)) J,
      ← pow_add]
  simpa only [hankelGram, krylovSynthesis, Matrix.mul_apply,
    Matrix.conjTranspose_apply] using
    congrArg (fun M : Matrix f f ℂ => M ia.2 jb.2) hblock

/-- The one-step compressed form has the shifted moment V_{i+j+1}. -/
theorem shiftedCompression_apply
    (T : Matrix h h ℂ) (hTH : Tᴴ = T)
    (J : Matrix h f ℂ) (N : ℕ) (ia jb : Fin N × f) :
    ((krylovSynthesis T J N)ᴴ * T * krylovSynthesis T J N) ia jb =
      (Jᴴ * T ^ ((ia.1 : ℕ) + (jb.1 : ℕ) + 1) * J) ia.2 jb.2 := by
  have hblock :
      (T ^ (ia.1 : ℕ) * J)ᴴ * T *
          (T ^ (jb.1 : ℕ) * J) =
        Jᴴ * T ^ ((ia.1 : ℕ) + (jb.1 : ℕ) + 1) * J := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hTH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T (T ^ (jb.1 : ℕ)) J, ← pow_succ']
    rw [← Matrix.mul_assoc (T ^ (ia.1 : ℕ))
      (T ^ ((jb.1 : ℕ) + 1)) J, ← pow_add]
    congr 3
  simpa only [krylovSynthesis, Matrix.mul_apply,
    Matrix.conjTranspose_apply] using
    congrArg (fun M : Matrix f f ℂ => M ia.2 jb.2) hblock

/-- Entrywise SA.9: the compressed localizer is literally
θ V_{i+j} - V_{i+j+1}. -/
theorem hankelLocalizer_apply
    (T : Matrix h h ℂ) (hTH : Tᴴ = T)
    (J : Matrix h f ℂ) (N : ℕ) (θ : ℝ) (ia jb : Fin N × f) :
    hankelLocalizer T J N θ ia jb =
      (θ : ℂ) * (Jᴴ * T ^ ((ia.1 : ℕ) + (jb.1 : ℕ)) * J) ia.2 jb.2 -
        (Jᴴ * T ^ ((ia.1 : ℕ) + (jb.1 : ℕ) + 1) * J) ia.2 jb.2 := by
  have hdecomp :
      hankelLocalizer T J N θ =
        (θ : ℂ) • hankelGram T J N -
          (krylovSynthesis T J N)ᴴ * T * krylovSynthesis T J N := by
    unfold hankelLocalizer hankelGram
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one]
  rw [hdecomp, Matrix.sub_apply, Matrix.smul_apply,
    hankelGram_apply T hTH J N ia jb,
    shiftedCompression_apply T hTH J N ia jb]
  rfl

/-- A compression quadratic form is the corresponding physical quadratic
form of the synthesized history. -/
theorem compression_form
    (K : Matrix h (Fin N × f) ℂ) (A : Matrix h h ℂ)
    (c : Fin N × f → ℂ) :
    star c ⬝ᵥ ((Kᴴ * A * K) *ᵥ c) =
      star (K *ᵥ c) ⬝ᵥ (A *ᵥ (K *ᵥ c)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec]

/-- SA.10 makes the actual Krylov range projection equal to the identity. -/
theorem atlas_margin_completes_krylov
    (T : Matrix h h ℂ) (J : Matrix h f ℂ) (N : ℕ)
    (U : Matrix h e ℂ) (m : ℝ) (hm : 0 < m)
    (hUsurj : Function.Surjective U.mulVecLin)
    (hUfloor : ∀ x : e → ℂ, m * eNorm x ^ 2 ≤ eNorm (U *ᵥ x) ^ 2)
    (hmargin : ‖Uᴴ * (1 - reachedProj T J N) * U‖ < m) :
    reachedProj T J N = 1 := by
  apply GTAtlasMargin.atlas_margin_forces_identity
    (reachedProj T J N)
    (smosTraceRangeProj_idem (krylovSynthesis T J N))
    (smosTraceRangeProj_conjTranspose (krylovSynthesis T J N))
    U m hm hUsurj hUfloor hmargin

/-- Failure of SA.10 returns the canonical source-minimal missing bank with
its exact Gram, reconstruction, support-isometry, and rank-minimality
certificates. -/
theorem atlas_failure_returns_exact_missing_bank
    {nh ne : ℕ} {f : Type} [Fintype f] [DecidableEq f]
    (T : Matrix (Fin nh) (Fin nh) ℂ)
    (J : Matrix (Fin nh) f ℂ) (N : ℕ)
    (U : Matrix (Fin nh) (Fin ne) ℂ) (m : ℝ)
    (_hfail : ¬ ‖Uᴴ * (1 - reachedProj T J N) * U‖ < m) :
    let P := reachedProj T J N
    let A := AtlasMissingBank.missingSynthesis P U
    let C := AtlasMissingBank.completenessKernel P U
    let Jmiss := AtlasMissingBank.missingBank P U
    C = Aᴴ * A
      ∧ Jmissᴴ * Jmiss =
          SourceCoercivityInfluence.supportProj
            (ThreeCylinderActionResponse.gramPsd A).1
      ∧ Jmiss *
          ThreeCylinderActionResponse.sqrtM
            (ThreeCylinderActionResponse.gramPsd A).1 = A
      ∧ Jmiss.rank = A.rank
      ∧ (∀ {p : ℕ} (B : Matrix (Fin p) (Fin ne) ℂ),
          Bᴴ * B = C → B.rank = A.rank) := by
  dsimp only
  exact AtlasMissingBank.atlas_missing_bank_exact
    (reachedProj T J N)
    (smosTraceRangeProj_conjTranspose (krylovSynthesis T J N))
    (smosTraceRangeProj_idem (krylovSynthesis T J N)) U

/-- SA.10 + SA.11 imply SA.12 on the complete physical carrier.

The localizer premise is the literal matrix inequality
L_{J,N}^{≤θ} ⪰ β G_{J,N}. -/
theorem gt_two_margin_full_coercivity
    (T : Matrix h h ℂ) (hTH : Tᴴ = T)
    (J : Matrix h f ℂ) (N : ℕ) (θ β : ℝ) (hβ : 0 < β)
    (U : Matrix h e ℂ) (m : ℝ) (hm : 0 < m)
    (hUsurj : Function.Surjective U.mulVecLin)
    (hUfloor : ∀ x : e → ℂ, m * eNorm x ^ 2 ≤ eNorm (U *ᵥ x) ^ 2)
    (hmargin : ‖Uᴴ * (1 - reachedProj T J N) * U‖ < m)
    (hlocalizer :
      (hankelLocalizer T J N θ - (β : ℂ) • hankelGram T J N).PosSemidef) :
    ∀ v : h → ℂ,
      (star v ⬝ᵥ (T *ᵥ v)).re ≤ (θ - β) * eNorm v ^ 2 := by
  intro v
  have hPone := atlas_margin_completes_krylov
    T J N U m hm hUsurj hUfloor hmargin
  have hmem := smosTraceRangeProj_mulVec_mem
    (krylovSynthesis T J N) v
  rw [show smosTraceRangeProj (krylovSynthesis T J N) =
      reachedProj T J N from rfl, hPone, Matrix.one_mulVec] at hmem
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hmem
  rw [Matrix.mulVecLin_apply] at hc
  have hq := hlocalizer.dotProduct_mulVec_nonneg c
  have hformL := compression_form
    (krylovSynthesis T J N)
    ((θ : ℂ) • (1 : Matrix h h ℂ) - T) c
  have hformLoc :
      star c ⬝ᵥ (hankelLocalizer T J N θ *ᵥ c) =
      star (krylovSynthesis T J N *ᵥ c) ⬝ᵥ
        (((θ : ℂ) • (1 : Matrix h h ℂ) - T) *ᵥ
          (krylovSynthesis T J N *ᵥ c)) := by
    simpa only [hankelLocalizer] using hformL
  have hformG := compression_form
    (krylovSynthesis T J N) (1 : Matrix h h ℂ) c
  have hformG' :
      star c ⬝ᵥ (((krylovSynthesis T J N)ᴴ *
        krylovSynthesis T J N) *ᵥ c) =
      star (krylovSynthesis T J N *ᵥ c) ⬝ᵥ
        (krylovSynthesis T J N *ᵥ c) := by
    simpa using hformG
  have hformScaled :
      star c ⬝ᵥ (((β : ℂ) • ((krylovSynthesis T J N)ᴴ *
        krylovSynthesis T J N)) *ᵥ c) =
      (β : ℂ) * (star (krylovSynthesis T J N *ᵥ c) ⬝ᵥ
        (krylovSynthesis T J N *ᵥ c)) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hformG']
  have hformScaledH :
      star c ⬝ᵥ (((β : ℂ) • hankelGram T J N) *ᵥ c) =
      (β : ℂ) * (star (krylovSynthesis T J N *ᵥ c) ⬝ᵥ
        (krylovSynthesis T J N *ᵥ c)) := by
    simpa only [hankelGram] using hformScaled
  rw [Matrix.sub_mulVec, dotProduct_sub, hformLoc, hformScaledH,
    hc] at hq
  have hself := star_dot_self_eq_norm_sq v
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hself,
    Complex.nonneg_iff] at hq
  have hre := hq.1
  norm_num [Complex.sub_re, Complex.mul_re] at hre
  have hnorm_re :
      ((↑‖(WithLp.toLp 2 v : EuclideanSpace ℂ h)‖ : ℂ) ^ 2).re =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ h)‖ ^ 2 := by
    norm_num [pow_two, Complex.mul_re]
  rw [hnorm_re] at hre
  dsimp [eNorm]
  linarith

/-- Failure of SA.11 is constructive: a coefficient vector gives a nonzero
visible history violating the claimed physical floor. -/
theorem localizer_failure_returns_soft_history
    (T : Matrix h h ℂ) (hTH : Tᴴ = T)
    (J : Matrix h f ℂ) (N : ℕ)
    (θ β : ℝ) (hβ : 0 < β)
    (hfail :
      ¬(hankelLocalizer T J N θ - (β : ℂ) •
        hankelGram T J N).PosSemidef) :
    ∃ c : Fin N × f → ℂ,
      let v := krylovSynthesis T J N *ᵥ c
      v ≠ 0 ∧
        (θ - β) * eNorm v ^ 2 <
          (star v ⬝ᵥ (T *ᵥ v)).re := by
  have hA : ((θ : ℂ) • (1 : Matrix h h ℂ) - T).IsHermitian := by
    change ((θ : ℂ) • (1 : Matrix h h ℂ) - T)ᴴ =
      (θ : ℂ) • (1 : Matrix h h ℂ) - T
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hTH, Complex.star_def,
      Complex.conj_ofReal]
  have hL : (hankelLocalizer T J N θ).IsHermitian := by
    change (((krylovSynthesis T J N)ᴴ *
      ((θ : ℂ) • (1 : Matrix h h ℂ) - T) *
        krylovSynthesis T J N)ᴴ) =
      (krylovSynthesis T J N)ᴴ *
        ((θ : ℂ) • (1 : Matrix h h ℂ) - T) *
          krylovSynthesis T J N
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hA]
    simp only [Matrix.mul_assoc]
  have hG : (hankelGram T J N).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self (krylovSynthesis T J N)
  have hM : (hankelLocalizer T J N θ - (β : ℂ) •
      hankelGram T J N).IsHermitian := by
    change (hankelLocalizer T J N θ - (β : ℂ) •
      hankelGram T J N)ᴴ =
      hankelLocalizer T J N θ - (β : ℂ) • hankelGram T J N
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      hL.eq, hG.eq, Complex.star_def, Complex.conj_ofReal]
  have hnotall : ¬ ∀ c : Fin N × f → ℂ,
      0 ≤ star c ⬝ᵥ
        ((hankelLocalizer T J N θ - (β : ℂ) •
          hankelGram T J N) *ᵥ c) := by
    intro hall
    apply hfail
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    exact ⟨hM, hall⟩
  push Not at hnotall
  obtain ⟨c, hc⟩ := hnotall
  have him :
      (star c ⬝ᵥ
        ((hankelLocalizer T J N θ - (β : ℂ) •
          hankelGram T J N) *ᵥ c)).im = 0 :=
    hM.im_star_dotProduct_mulVec_self c
  have hcRe :
      (star c ⬝ᵥ
        ((hankelLocalizer T J N θ - (β : ℂ) •
          hankelGram T J N) *ᵥ c)).re < 0 := by
    have hnre : ¬ 0 ≤
        (star c ⬝ᵥ
          ((hankelLocalizer T J N θ - (β : ℂ) •
            hankelGram T J N) *ᵥ c)).re := by
      intro hre
      apply hc
      exact Complex.nonneg_iff.mpr ⟨hre, him.symm⟩
    exact lt_of_not_ge hnre
  refine ⟨c, ?_⟩
  dsimp only
  have hformL := compression_form
    (krylovSynthesis T J N)
    ((θ : ℂ) • (1 : Matrix h h ℂ) - T) c
  have hformLoc :
      star c ⬝ᵥ (hankelLocalizer T J N θ *ᵥ c) =
      star (krylovSynthesis T J N *ᵥ c) ⬝ᵥ
        (((θ : ℂ) • (1 : Matrix h h ℂ) - T) *ᵥ
          (krylovSynthesis T J N *ᵥ c)) := by
    simpa only [hankelLocalizer] using hformL
  have hformG := compression_form
    (krylovSynthesis T J N) (1 : Matrix h h ℂ) c
  have hformG' :
      star c ⬝ᵥ (((krylovSynthesis T J N)ᴴ *
        krylovSynthesis T J N) *ᵥ c) =
      star (krylovSynthesis T J N *ᵥ c) ⬝ᵥ
        (krylovSynthesis T J N *ᵥ c) := by
    simpa using hformG
  have hformScaled :
      star c ⬝ᵥ (((β : ℂ) • ((krylovSynthesis T J N)ᴴ *
        krylovSynthesis T J N)) *ᵥ c) =
      (β : ℂ) * (star (krylovSynthesis T J N *ᵥ c) ⬝ᵥ
        (krylovSynthesis T J N *ᵥ c)) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hformG']
  have hformScaledH :
      star c ⬝ᵥ (((β : ℂ) • hankelGram T J N) *ᵥ c) =
      (β : ℂ) * (star (krylovSynthesis T J N *ᵥ c) ⬝ᵥ
        (krylovSynthesis T J N *ᵥ c)) := by
    simpa only [hankelGram] using hformScaled
  rw [Matrix.sub_mulVec, dotProduct_sub, hformLoc, hformScaledH] at hcRe
  have hvne : krylovSynthesis T J N *ᵥ c ≠ 0 := by
    intro hv
    simp [hv] at hcRe
  refine ⟨hvne, ?_⟩
  have hself := star_dot_self_eq_norm_sq
    (krylovSynthesis T J N *ᵥ c)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hself] at hcRe
  have hre := hcRe
  norm_num [Complex.sub_re, Complex.mul_re] at hre
  have hnorm_re :
      ((↑‖(WithLp.toLp 2 (krylovSynthesis T J N *ᵥ c) :
          EuclideanSpace ℂ h)‖ : ℂ) ^ 2).re =
        ‖(WithLp.toLp 2 (krylovSynthesis T J N *ᵥ c) :
          EuclideanSpace ℂ h)‖ ^ 2 := by
    norm_num [pow_two, Complex.mul_re]
  rw [hnorm_re] at hre
  rw [← Matrix.mulVec_mulVec] at hre
  dsimp [eNorm]
  linarith

end GTTwoMarginFull
end NCG
